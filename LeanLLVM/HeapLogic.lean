/-
String extents as the unit of ownership.

`LeanLLVM/Permissions.lean` states the byte as a resource: `PointsTo a b` is one
byte's value, and `Star` composes two claims by splitting a *memory* into two
`MemApart` parts.  That atom is smaller than the connective: a claim about one
byte is a claim about one address, while `MemApart` asks two whole memories to
share no address, so a read cannot migrate into a composition without the record
being restated about a part of the memory rather than about the memory itself.

This module makes the extent the unit.  `BytesAt a bs mem` is a *read*: the
memory answers the byte list `bs` at `a`.  A claim carries its own footprint —
`atomExtent a bs` is `a … a + bs.length`, computed from the claim — so composition
asks only that two footprints share no address.  That is a fact about the two
claims, and nothing about the memories they were read from.

* `BytesAt` is the read, definitionally (`bytesAt_iff_readBytes`), and it
  determines the bytes it names (`BytesAt.agree`, `BytesAt.agree_prefix`): two
  atoms at one address cannot disagree.
* `star (bytes a bs) (bytes a' bs')` holds exactly when the two extents are apart
  and both reads succeed (`star_bytes_iff`).  Both reads are recovered unchanged
  (`star_bytes_reads`), so nothing is weakened to fit the connective.  The side
  condition is a hypothesis where a caller has it (`star_bytes_of_apart`), it is the
  interval order a record writes (`atomApart_iff_extent_before`), and the
  composition is inhabited by a memory a caller can write (`bytesAt_star_inhabited`,
  with `star_bytes_inhabited` as its concrete instance).
* The memory-splitting `Star` of `LeanLLVM/Permissions.lean`, read at two atoms,
  derives the extent disjointness (`star_memApart_apart`) and both atoms on the
  composed memory (`star_memApart_reads`), so a record migrates from the split form
  without loss.  What the extent form removes is the requirement to exhibit the two
  memories: the atoms and their disjointness are the whole hypothesis.
* `star` is a commutative monoid with `emp` as its unit (`star_comm`,
  `star_assoc`, `star_emp`, `emp_star`); the composed footprint is the union of the
  parts' (`star_foot_comm`, `star_foot_assoc`, `star_foot_emp`).
* The frame rule is derived, not assumed: a property of one atom's extent
  transfers across a change confined to the composition's other footprint
  (`frame_rule_of_star`), and a write into the other claim's footprint leaves the
  atom in place (`star_frame_atom`).
* `Owns`, `Rights`, `Carries` and `PointsTo` of `LeanLLVM/Permissions.lean`, and the
  `UnchangedOn`/`DependsOutside` frame rule of `LeanLLVM/FramePredicate.lean`, are
  projections of the atom (`BytesAt.owns`, `BytesAt.rights`, `bytesAt_toOwns`,
  `BytesAt.carries`, `BytesAt.singleton_pointsTo`, `pointsTo_bytesAt`,
  `bytesAt_dependsOutside`, `frame_rule_atom`), so nothing stated in those
  vocabularies regresses.

### What this does not buy

`DecodeNoAlias`'s fourth clause is `xj`/`dst`: two extents one run writes.  The
extent logic composes claims; it does not separate two claims about overlapping
bytes, because a run legitimately owns both regions it writes.  `self_overlap`
exhibits an atom that never excludes a second claim at its own extent, and
`decodeXjDst_notDerived` exhibits one memory carrying the destination window's
bytes and the cursor slot's with the cursor inside the window.

The clause is not made derivable, and it is not weakened either: at the run's two
extents the record's disjunction *is* the composition's side condition
(`decodeXjDst_clause_iff_atomApart`).  So the fourth clause stays a hypothesis,
exactly as under `Rights`: the number of disjointness facts a staging must supply
does not fall, because four regions that are pairwise apart are four facts however
they are spelled.  What changes is where they sit — the side condition of one
composition over the run's own writes, rather than clauses written beside a region
claim.  The logic buys composition, not separation.
-/
import LeanLLVM.Permissions

namespace LeanLLVM

/-! ### The atom: a byte run read out of the memory -/

/-- The atom: `bs` are the bytes the memory answers at `a`.  This is a read, not a
presence claim, so it says what the memory holds rather than that it holds
something; and it names an extent rather than a memory, so its footprint is the
bytes it is about. -/
def BytesAt (a : Nat) (bs : List UInt8) (mem : Mem) : Prop :=
  readBytes mem a bs.length = some bs

/-- The atom is the range read, with no proposition former between them. -/
theorem bytesAt_iff_readBytes {a : Nat} {bs : List UInt8} {mem : Mem} :
    BytesAt a bs mem ↔ readBytes mem a bs.length = some bs :=
  Iff.rfl

/-- The atom implies its read definitionally: this is the statement a consumer
uses, and it is the atom's own body. -/
theorem BytesAt.read {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem) :
    readBytes mem a bs.length = some bs :=
  h

/-- An interval of addresses as a region predicate. -/
def extent (a n : Nat) : Nat → Prop :=
  inRegion (a, n)

/-- Membership in an interval. -/
theorem extent_iff {a n x : Nat} : extent a n x ↔ a ≤ x ∧ x < a + n :=
  Iff.rfl

/-- The footprint of an atom: the addresses its read touches.  It is computed from
the claim, so no author can declare a region narrower or wider than what the claim
is about. -/
def atomExtent (a : Nat) (bs : List UInt8) : Nat → Prop :=
  extent a bs.length

/-- Membership in an atom's footprint. -/
theorem atomExtent_iff {a : Nat} {bs : List UInt8} {x : Nat} :
    atomExtent a bs x ↔ a ≤ x ∧ x < a + bs.length :=
  Iff.rfl

/-- A region is either exhausting an address or entirely above it: the case split a
disjointness hypothesis supplies. -/
theorem not_extent {a n x : Nat} (h : ¬ (a ≤ x ∧ x < a + n)) :
    x < a ∨ a + n ≤ x := by
  rcases Nat.lt_or_ge x a with hlt | hge
  · exact Or.inl hlt
  · rcases Nat.lt_or_ge x (a + n) with hlt' | hge'
    · exact absurd ⟨hge, hlt'⟩ h
    · exact Or.inr hge'

/-! ### The atom determines its bytes -/

/-- A shorter read is a prefix of a longer one at the same address. -/
theorem readBytes_take_of_le {mem : Mem} {a n m : Nat} {bs bs' : List UInt8}
    (hnm : n ≤ m) (h : readBytes mem a n = some bs) (h' : readBytes mem a m = some bs') :
    bs'.take n = bs := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  obtain ⟨h1, -⟩ := readBytes_split mem a n k h'
  rw [h1] at h
  exact Option.some.inj h

/-- **Two atoms at one address agree on their common prefix.**  The memory is a
function of the address, so the shorter read bounds the longer; nothing is assumed
about either claim. -/
theorem BytesAt.agree_prefix {a : Nat} {bs bs' : List UInt8} {mem : Mem}
    (h : BytesAt a bs mem) (h' : BytesAt a bs' mem) :
    bs'.take (Nat.min bs.length bs'.length) = bs.take (Nat.min bs.length bs'.length) := by
  have h1 : readBytes mem a (Nat.min bs.length bs'.length) =
      some (bs.take (Nat.min bs.length bs'.length)) := by
    refine (readBytes_split mem a (Nat.min bs.length bs'.length)
      (bs.length - Nat.min bs.length bs'.length) ?_).1
    rw [Nat.add_sub_of_le (Nat.min_le_left _ _)]
    exact h
  have h2 : readBytes mem a (Nat.min bs.length bs'.length) =
      some (bs'.take (Nat.min bs.length bs'.length)) := by
    refine (readBytes_split mem a (Nat.min bs.length bs'.length)
      (bs'.length - Nat.min bs.length bs'.length) ?_).1
    rw [Nat.add_sub_of_le (Nat.min_le_right _ _)]
    exact h'
  rw [h1] at h2
  exact (Option.some.inj h2).symm

/-- **Two atoms at one address with one length are one atom.**  The bytes are
determined, not merely present. -/
theorem BytesAt.agree {a : Nat} {bs bs' : List UInt8} {mem : Mem}
    (h : BytesAt a bs mem) (h' : BytesAt a bs' mem) (hlen : bs.length = bs'.length) :
    bs = bs' := by
  have h1 : bs'.take bs.length = bs := readBytes_take_of_le (Nat.le_of_eq hlen) h h'
  rw [hlen, List.take_length] at h1
  exact h1.symm

/-- The atom, byte by byte: the read answers at every offset of its extent. -/
theorem BytesAt.byte {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem)
    {k : Nat} (hk : k < bs.length) : readByte mem (a + k) = some (bs.getD k 0) :=
  readByte_of_readBytes (m := mem) (addr := a) (n := bs.length) (bs := bs) h hk

/-! ### The atom in the presence vocabulary -/

/-- Every address of an atom's extent is present. -/
theorem BytesAt.presentAt {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem)
    {x : Nat} (hx : atomExtent a bs x) : present mem x := by
  obtain ⟨hlo, hhi⟩ := atomExtent_iff.mp hx
  have hk1 : a + (x - a) < a + bs.length := by
    rw [Nat.add_sub_of_le hlo]
    exact hhi
  have hk : x - a < bs.length := Nat.lt_of_add_lt_add_left hk1
  have hb := h.byte hk
  rw [Nat.add_sub_of_le hlo] at hb
  exact ⟨bs.getD (x - a) 0, hb⟩

/-- The atom is a present range, in `LeanLLVM/FramePredicate.lean`'s per-location
vocabulary. -/
theorem BytesAt.hasBytes {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem) :
    HasBytes mem a bs.length :=
  readBytes_some_present mem a bs.length bs h

/-- The atom carries its footprint in `LeanLLVM/Permissions.lean`'s set-valued
vocabulary. -/
theorem BytesAt.carries {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem) :
    Carries (atomExtent a bs) mem := by
  intro x hx
  obtain ⟨b, hb⟩ := h.presentAt hx
  rw [hb]
  intro hc
  cases hc

/-- **`Owns` recovered.**  An atom names a present region, so with the frame
relation of the run that produced it the atom is the old region claim at its own
extent — the projection a record that states `Owns` reads. -/
theorem BytesAt.owns {a : Nat} {bs : List UInt8} {mem m : Mem} (h : BytesAt a bs m)
    (hu : UnchangedOn (atomExtent a bs) mem m) : Owns (atomExtent a bs) mem m :=
  ⟨hu, fun _ hx => h.presentAt hx⟩

/-- **`Rights` recovered.**  The atom at its own extent, keeping nothing and
declaring that extent writable, is a rights claim; `Rights.toOwns` then returns
`Owns`, so the rights vocabulary is a projection of the atom rather than a second
assumption. -/
theorem BytesAt.rights {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem) :
    Rights (atomExtent a bs) emptyRegion (atomExtent a bs) mem mem where
  present := fun _ hx => h.presentAt hx
  writes := UnchangedOn.refl _ _
  within := fun _ hx => hx
  apart := fun _ hk _ => hk

/-- The old region claim at an atom's own extent. -/
theorem bytesAt_toOwns {a : Nat} {bs : List UInt8} {mem : Mem} (h : BytesAt a bs mem) :
    Owns (atomExtent a bs) mem mem :=
  h.rights.toOwns

/-- **`PointsTo` is the one-byte atom.**  The byte atom of
`LeanLLVM/Permissions.lean` is this atom read at length one, so the two
vocabularies state the same claim rather than one weakening the other. -/
theorem BytesAt.singleton_pointsTo {a : Nat} {b : UInt8} {mem : Mem}
    (h : BytesAt a [b] mem) : PointsTo a b mem := by
  have hb := readByte_of_readBytes (m := mem) (addr := a) (n := 1) (bs := [b]) h
    (k := 0) (by decide)
  simpa [PointsTo] using hb

/-- The byte atom is the one-byte extent atom. -/
theorem pointsTo_bytesAt {a : Nat} {b : UInt8} {mem : Mem} (h : PointsTo a b mem) :
    BytesAt a [b] mem := by
  unfold PointsTo at h
  show readBytes mem a 1 = some [b]
  simp only [readBytes]
  rw [h]

/-! ### A window's read depends on the window -/

/-- A window's read is determined by the bytes in that window: two memories that
answer the same there read the same.  This is what makes the extent, rather than the
memory, the unit of separation. -/
theorem readBytes_eq_of_agree (mem m : Mem) :
    ∀ (a n : Nat), (∀ k, k < n → readByte m (a + k) = readByte mem (a + k)) →
      readBytes m a n = readBytes mem a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
      have hhead : readByte m a = readByte mem a := by
        simpa using h 0 (Nat.succ_pos n)
      have htail : readBytes m (a + 1) n = readBytes mem (a + 1) n :=
        readBytes_eq_of_agree mem m (a + 1) n (fun k hk => by
          rw [show a + 1 + k = a + (k + 1) from by rw [Nat.add_assoc, Nat.add_comm 1 k]]
          exact h (k + 1) (Nat.succ_lt_succ hk))
      cases hb : readByte mem a with
      | none => simp only [readBytes, hhead, hb]
      | some b => simp only [readBytes, hhead, hb, htail]

/-- A property of a footprint: two memories that answer the same on `F` agree on the
property.  `DependsOutside` in `LeanLLVM/FramePredicate.lean` is this read at the
complement of the region a run may change. -/
def DependsOn (F : Nat → Prop) (R : Mem → Prop) : Prop :=
  ∀ {m1 m2 : Mem}, (∀ a, F a → readByte m1 a = readByte m2 a) → (R m1 ↔ R m2)

/-- **An atom depends only on its extent.** -/
theorem bytesAt_dependsOn (a : Nat) (bs : List UInt8) :
    DependsOn (atomExtent a bs) (BytesAt a bs) := by
  intro m1 m2 hag
  have hread : readBytes m1 a bs.length = readBytes m2 a bs.length :=
    readBytes_eq_of_agree m2 m1 a bs.length (fun k hk => by
      have hin : atomExtent a bs (a + k) :=
        atomExtent_iff.mpr ⟨Nat.le_add_right a k, Nat.add_lt_add_left hk a⟩
      exact hag (a + k) hin)
  constructor
  · intro h
    show readBytes m2 a bs.length = some bs
    rw [← hread]
    exact h
  · intro h
    show readBytes m1 a bs.length = some bs
    rw [hread]
    exact h

/-- **The atom as a `DependsOutside` property.**  Read at the complement of the
atom's extent, the atom is a property of that complement, so the frame rule of
`LeanLLVM/FramePredicate.lean` applies to it verbatim. -/
theorem bytesAt_dependsOutside (a : Nat) (bs : List UInt8) :
    DependsOutside (fun x => ¬ atomExtent a bs x) (BytesAt a bs) := by
  intro mem m hu
  refine (bytesAt_dependsOn a bs) ?_
  intro x hx
  exact (hu x (fun hc => hc hx)).symm

/-- **The frame rule of `LeanLLVM/FramePredicate.lean`, recovered at an atom.**  A
run that leaves the extent alone leaves the atom alone: the old rule, unchanged,
with the atom as its property. -/
theorem frame_rule_atom {a : Nat} {bs : List UInt8} {mem m : Mem}
    (hu : UnchangedOn (fun x => ¬ atomExtent a bs x) mem m) :
    BytesAt a bs mem ↔ BytesAt a bs m :=
  frame_rule hu (bytesAt_dependsOutside a bs)

/-- **The atom's frame.**  A property of the atom's own extent transfers to any
memory agreeing with it there. -/
theorem BytesAt.frame {a : Nat} {bs : List UInt8} {mem m : Mem} (h : BytesAt a bs mem)
    (hag : ∀ x, atomExtent a bs x → readByte mem x = readByte m x) : BytesAt a bs m := by
  have hread : readBytes m a bs.length = readBytes mem a bs.length :=
    readBytes_eq_of_agree mem m a bs.length (fun k hk => by
      have hin : atomExtent a bs (a + k) :=
        atomExtent_iff.mpr ⟨Nat.le_add_right a k, Nat.add_lt_add_left hk a⟩
      exact (hag (a + k) hin).symm)
  show readBytes m a bs.length = some bs
  rw [hread]
  exact h

/-- **A write outside the extent leaves the atom.**  The atom is about the bytes in
its extent, so a store at an unclaimed address is not a change to it. -/
theorem BytesAt.writeByte {a : Nat} {bs : List UInt8} {mem : Mem} {c : Nat} {v : UInt8}
    (h : BytesAt a bs mem) (hout : ¬ atomExtent a bs c) : BytesAt a bs (writeByte mem c v) := by
  refine h.frame ?_
  intro x hx
  have hxc : c ≠ x := by
    rintro rfl
    exact hout hx
  exact (readByte_writeByte_other mem v hxc).symm

/-! ### Claims and `*` over extents -/

/-- A claim with an explicit footprint.  The footprint is part of the claim, so
composition asks for two footprints to share no address rather than for two
memories to: the atom is smaller than the memory it is read from. -/
structure Claim where
  /-- What the claim asserts of a memory. -/
  holds : Mem → Prop
  /-- The addresses the claim is about. -/
  foot : Nat → Prop

/-- **The atom as a claim**, with the footprint computed from the bytes it names. -/
def bytes (a : Nat) (bs : List UInt8) : Claim where
  holds := BytesAt a bs
  foot := atomExtent a bs

/-- The claim that asserts nothing and owns nothing: the unit of `*`. -/
def emp : Claim where
  holds := fun _ => True
  foot := emptyRegion

/-- **`*` over extents.**  Two claims compose when their footprints share no
address, and the composed claim's footprint is the union.  The side condition names
the claims' own addresses, so it is a fact about what each claim reads and nothing
about how either was read. -/
def star (P Q : Claim) : Claim where
  holds := fun mem => Disjoint P.foot Q.foot ∧ P.holds mem ∧ Q.holds mem
  foot := fun a => P.foot a ∨ Q.foot a

/-- The composed footprint is the union, at an address. -/
theorem star_foot_apply (P Q : Claim) (a : Nat) :
    (star P Q).foot a ↔ P.foot a ∨ Q.foot a :=
  Iff.rfl

/-- The composed footprint does not care which side is written first. -/
theorem star_foot_comm (P Q : Claim) (a : Nat) :
    (star P Q).foot a ↔ (star Q P).foot a :=
  or_comm

/-- The composed footprint groups. -/
theorem star_foot_assoc (P Q R : Claim) (a : Nat) :
    (star (star P Q) R).foot a ↔ (star P (star Q R)).foot a :=
  or_assoc

/-- The empty footprint is the unit of the union. -/
theorem star_foot_emp (P : Claim) (a : Nat) :
    (star P emp).foot a ↔ P.foot a := by
  constructor
  · intro h
    rcases h with hp | he
    · exact hp
    · exact absurd he (fun hc => hc)
  · exact Or.inl

/-! ### The monoid laws -/

/-- `*` is commutative: the disjointness is symmetric and the two claims conjoin. -/
theorem star_comm (P Q : Claim) (mem : Mem) :
    (star P Q).holds mem ↔ (star Q P).holds mem := by
  constructor <;> rintro ⟨hd, hp, hq⟩
  · exact ⟨hd.symm, hq, hp⟩
  · exact ⟨hd.symm, hq, hp⟩

/-- `*` is associative: the same three pairwise disjointness facts are read in a
different grouping, and the grouped claim's footprint is the union on both sides. -/
theorem star_assoc (P Q R : Claim) (mem : Mem) :
    (star (star P Q) R).holds mem ↔ (star P (star Q R)).holds mem := by
  constructor
  · rintro ⟨hd, ⟨hpq, hp, hq⟩, hr⟩
    refine ⟨?_, hp, ⟨?_, hq, hr⟩⟩
    · intro a ha hqr
      rcases hqr with hq' | hr'
      · exact hpq a ha hq'
      · exact hd a (Or.inl ha) hr'
    · intro a hq' hr'
      exact hd a (Or.inr hq') hr'
  · rintro ⟨hpr, hp, ⟨hqr, hq, hr⟩⟩
    refine ⟨?_, ⟨?_, hp, hq⟩, hr⟩
    · intro a hab hr'
      rcases hab with hp' | hq'
      · exact hpr a hp' (Or.inr hr')
      · exact hqr a hq' hr'
    · intro a hp' hq'
      exact hpr a hp' (Or.inl hq')

/-- `emp` is the unit on the right: the empty footprint is disjoint from everything,
and the other claim is the whole content. -/
theorem star_emp (P : Claim) (mem : Mem) : (star P emp).holds mem ↔ P.holds mem := by
  constructor
  · rintro ⟨-, hp, -⟩
    exact hp
  · intro hp
    exact ⟨fun _ _ hq => hq, hp, trivial⟩

/-- `emp` is the unit on the left. -/
theorem emp_star (P : Claim) (mem : Mem) : (star emp P).holds mem ↔ P.holds mem := by
  constructor
  · rintro ⟨-, -, hp⟩
    exact hp
  · intro hp
    exact ⟨fun _ he _ => he, trivial, hp⟩

/-! ### Composition of two extents -/

/-- Two atoms are extent-apart when their footprints share no address.  This is the
whole side condition composition needs — not `MemApart` on two memories, because an
atom's claim is about its extent. -/
def AtomApart (a : Nat) (bs : List UInt8) (a' : Nat) (bs' : List UInt8) : Prop :=
  Disjoint (atomExtent a bs) (atomExtent a' bs')

/-- Extent-apartness is symmetric. -/
theorem AtomApart.symm {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    (h : AtomApart a bs a' bs') : AtomApart a' bs' a bs :=
  fun x hx' hx => h x hx hx'

/-- **Two non-empty extents are apart exactly when one ends before the other
begins.**  This is the form a record writes: `DecodeNoAlias`'s clauses are all
disjunctions of this shape.  Composition therefore asks for the record's own
interval order, at the two claims' extents. -/
theorem atomApart_iff_extent_before {a : Nat} {bs : List UInt8} {a' : Nat}
    {bs' : List UInt8} (hbs : bs ≠ []) (hbs' : bs' ≠ []) :
    AtomApart a bs a' bs' ↔ a + bs.length ≤ a' ∨ a' + bs'.length ≤ a := by
  have hn : 0 < bs.length := by
    cases bs with
    | nil => exact absurd rfl hbs
    | cons b rest => exact Nat.succ_pos rest.length
  have hm : 0 < bs'.length := by
    cases bs' with
    | nil => exact absurd rfl hbs'
    | cons b rest => exact Nat.succ_pos rest.length
  constructor
  · intro hd
    by_cases h1 : a + bs.length ≤ a'
    · exact Or.inl h1
    · by_cases h2 : a' + bs'.length ≤ a
      · exact Or.inr h2
      · exfalso
        have hlt1 : a' < a + bs.length := Nat.not_le.mp h1
        have hlt2 : a < a' + bs'.length := Nat.not_le.mp h2
        have hx1 : a < a + bs.length := Nat.lt_add_of_pos_right hn
        have hx2 : a' < a' + bs'.length := Nat.lt_add_of_pos_right hm
        rcases Nat.le_total a a' with hle | hle
        · exact hd a' (atomExtent_iff.mpr ⟨hle, hlt1⟩)
            (atomExtent_iff.mpr ⟨Nat.le_refl a', hx2⟩)
        · exact hd a (atomExtent_iff.mpr ⟨Nat.le_refl a, hx1⟩)
            (atomExtent_iff.mpr ⟨hle, hlt2⟩)
  · rintro (h | h)
    · intro x hx hx'
      exact absurd (Nat.lt_of_lt_of_le (atomExtent_iff.mp hx).2 h)
        (Nat.not_lt.mpr (atomExtent_iff.mp hx').1)
    · intro x hx hx'
      exact absurd (Nat.lt_of_lt_of_le (atomExtent_iff.mp hx').2 h)
        (Nat.not_lt.mpr (atomExtent_iff.mp hx).1)

/-- **The composition, with the disjointness supplied as a hypothesis.**  Both
atoms are claims about the same memory, so composing them consumes no part of it. -/
theorem star_bytes_of_apart {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    {mem : Mem} (hd : AtomApart a bs a' bs') (h : BytesAt a bs mem) (h' : BytesAt a' bs' mem) :
    (star (bytes a bs) (bytes a' bs')).holds mem :=
  ⟨hd, h, h'⟩

/-- **The composition's content, exactly.**  The composed claim is the disjointness
conjoined with both reads: nothing is weakened to fit the connective. -/
theorem star_bytes_iff {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8} {mem : Mem} :
    (star (bytes a bs) (bytes a' bs')).holds mem ↔
      AtomApart a bs a' bs' ∧ BytesAt a bs mem ∧ BytesAt a' bs' mem :=
  Iff.rfl

/-- **The composition still reads — both atoms, unchanged.**  A composition implies
the reads its parts asserted; this is the test the memory-splitting atom could not
pass, because it recovered the claim about a part rather than about the memory. -/
theorem star_bytes_reads {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8} {mem : Mem}
    (h : (star (bytes a bs) (bytes a' bs')).holds mem) :
    readBytes mem a bs.length = some bs ∧ readBytes mem a' bs'.length = some bs' :=
  ⟨h.2.1, h.2.2⟩

/-- The first atom of a composition, unchanged. -/
theorem star_bytes_left {a : Nat} {bs : List UInt8} {Q : Claim} {mem : Mem}
    (h : (star (bytes a bs) Q).holds mem) : BytesAt a bs mem :=
  h.2.1

/-- The second atom of a composition, unchanged. -/
theorem star_bytes_right {a' : Nat} {bs' : List UInt8} {P : Claim} {mem : Mem}
    (h : (star P (bytes a' bs')).holds mem) : BytesAt a' bs' mem :=
  h.2.2

/-- With the disjointness fixed, the composition is exactly the two claims: the
round trip a record makes when it states its writes as atoms. -/
theorem star_bytes_roundtrip {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    {mem : Mem} (hd : AtomApart a bs a' bs') :
    (star (bytes a bs) (bytes a' bs')).holds mem ↔ BytesAt a bs mem ∧ BytesAt a' bs' mem :=
  ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => star_bytes_of_apart hd h.1 h.2⟩

/-- **The composition inhabits a memory.**  Writing the first atom's bytes and then
the second's, at extents that share no address, gives a memory that answers both: the
second write leaves every byte of the first extent alone.  This is the split a
caller can produce, and it needs only the two extents to be apart. -/
theorem bytesAt_star_inhabited {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    (hd : AtomApart a bs a' bs') :
    ∃ mem : Mem, (star (bytes a bs) (bytes a' bs')).holds mem := by
  refine ⟨writeBytes (writeBytes [] a bs) a' bs', hd, ?_, ?_⟩
  · have hag : ∀ k, k < bs.length →
        readByte (writeBytes (writeBytes [] a bs) a' bs') (a + k) =
          readByte (writeBytes [] a bs) (a + k) := by
      intro k hk
      have hin : atomExtent a bs (a + k) :=
        atomExtent_iff.mpr ⟨Nat.le_add_right a k, Nat.add_lt_add_left hk a⟩
      have hout : ¬ (a' ≤ a + k ∧ a + k < a' + bs'.length) :=
        fun hc => hd (a + k) hin (atomExtent_iff.mpr hc)
      rcases not_extent hout with hlt | hge
      · exact readByte_writeBytes_below (writeBytes [] a bs) bs' hlt
      · exact readByte_writeBytes_above (writeBytes [] a bs) bs' hge
    have hread := readBytes_eq_of_agree (writeBytes [] a bs)
      (writeBytes (writeBytes [] a bs) a' bs') a bs.length hag
    show readBytes (writeBytes (writeBytes [] a bs) a' bs') a bs.length = some bs
    rw [hread]
    exact readBytes_writeBytes_same [] bs
  · exact readBytes_writeBytes_same (writeBytes [] a bs) bs'

/-- The control for `bytesAt_star_inhabited`: two extents that are apart satisfy the
side condition, so the inhabitation theorem is not vacuous. -/
theorem atomApart_inhabited : AtomApart 0 [1, 2] 5 [3, 4] := by
  intro x hx hx'
  obtain ⟨-, h2⟩ := atomExtent_iff.mp hx
  obtain ⟨h3, -⟩ := atomExtent_iff.mp hx'
  exact absurd (Nat.lt_of_lt_of_le h2 (by decide : 2 ≤ 5)) (Nat.not_lt.mpr h3)

/-- The composition at a concrete memory: two extents, one memory, both reads.  The
control for `star_bytes_reads` and `bytesAt_star_inhabited`, so neither is a claim
about an empty composition. -/
theorem star_bytes_inhabited :
    (star (bytes 0 [1, 2]) (bytes 5 [3, 4])).holds [(0, 1), (1, 2), (5, 3), (6, 4)] := by
  refine star_bytes_of_apart atomApart_inhabited ?_ ?_
  · show readBytes [(0, 1), (1, 2), (5, 3), (6, 4)] 0 2 = some [1, 2]
    decide
  · show readBytes [(0, 1), (1, 2), (5, 3), (6, 4)] 5 2 = some [3, 4]
    decide

/-- **Overlapping extents do not compose.**  A shared address refutes the composed
claim at every memory; the refusal is the disjointness conjunct, not a weakened
atom. -/
theorem star_bytes_uninhabited_of_overlap {a : Nat} {bs : List UInt8} {a' : Nat}
    {bs' : List UInt8} {x : Nat} (hx : atomExtent a bs x) (hx' : atomExtent a' bs' x)
    (mem : Mem) : ¬ (star (bytes a bs) (bytes a' bs')).holds mem :=
  fun h => h.1 x hx hx'

/-- **The memory-splitting `*` implies the extent composition's side condition.**  A
split into two `MemApart` parts that carry the two byte runs puts the two extents
apart — derived from the split rather than assumed.  The split is the stronger
hypothesis, which is why the extent form composes where the split form could not. -/
theorem star_memApart_apart {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    {mem : Mem} (h : Star (BytesAt a bs) (BytesAt a' bs') mem) : AtomApart a bs a' bs' := by
  obtain ⟨m1, m2, hap, h1, h2, -⟩ := h
  intro x hx hx'
  obtain ⟨hlo, hhi⟩ := atomExtent_iff.mp hx
  obtain ⟨hlo', hhi'⟩ := atomExtent_iff.mp hx'
  have hk : x - a < bs.length :=
    Nat.lt_of_add_lt_add_left (by rw [Nat.add_sub_of_le hlo]; exact hhi)
  have hk' : x - a' < bs'.length :=
    Nat.lt_of_add_lt_add_left (by rw [Nat.add_sub_of_le hlo']; exact hhi')
  have hb1 := h1.byte hk
  rw [Nat.add_sub_of_le hlo] at hb1
  have hb2 := h2.byte hk'
  rw [Nat.add_sub_of_le hlo'] at hb2
  have hne : readByte m1 x ≠ none := by
    rw [hb1]
    intro hc
    cases hc
  rw [hap x hne] at hb2
  cases hb2

/-- **The memory split still reads on the composed memory.**  An instance of
`LeanLLVM/Permissions.lean`'s `Star` gives both atoms on `mem` itself, so moving a
record from the split form to the extent form loses nothing.  The converse fails
only because the split asks for more than the atoms say (`self_overlap`). -/
theorem star_memApart_reads {a : Nat} {bs : List UInt8} {a' : Nat} {bs' : List UInt8}
    {mem : Mem} (h : Star (BytesAt a bs) (BytesAt a' bs') mem) :
    BytesAt a bs mem ∧ BytesAt a' bs' mem := by
  obtain ⟨m1, m2, hap, h1, h2, hag⟩ := h
  have hmem : ∀ (addr n : Nat), readBytes mem addr n = readBytes (m1 ++ m2) addr n :=
    fun addr n => readBytes_eq_of_agree (m1 ++ m2) mem addr n (fun k _ => hag (addr + k))
  have hleft : readBytes (m1 ++ m2) a bs.length = readBytes m1 a bs.length := by
    refine readBytes_eq_of_agree m1 (m1 ++ m2) a bs.length (fun k hk => ?_)
    simp only [readByte_append, h1.byte hk]
  have hright : readBytes (m1 ++ m2) a' bs'.length = readBytes m2 a' bs'.length := by
    refine readBytes_eq_of_agree m2 (m1 ++ m2) a' bs'.length (fun k hk => ?_)
    have hb := h2.byte hk
    have hne : readByte m2 (a' + k) ≠ none := by
      rw [hb]
      intro hc
      cases hc
    simp only [readByte_append, hap.symm (a' + k) hne]
  constructor
  · show readBytes mem a bs.length = some bs
    rw [hmem a bs.length, hleft]
    exact h1
  · show readBytes mem a' bs'.length = some bs'
    rw [hmem a' bs'.length, hright]
    exact h2

/-! ### The frame rule, derived -/

/-- **The frame rule.**  A composition carries the atom, and the other claim's
footprint is apart from it, so a change confined to that footprint leaves the atom
in place.  The disjointness comes from the composition rather than from a
hand-written hypothesis, which is what makes this a rule of `*`. -/
theorem frame_rule_of_star {a : Nat} {bs : List UInt8} {Q : Claim} {mem m : Mem}
    (h : (star (bytes a bs) Q).holds mem) (hu : UnchangedOn Q.foot mem m) :
    BytesAt a bs m := by
  refine ((bytesAt_dependsOn a bs) ?_).1 h.2.1
  intro x hx
  exact (hu x (fun hq => h.1 x hx hq)).symm

/-- A write into the other claim's footprint leaves the atom: the frame rule at a
single store, derived from the composition's disjointness. -/
theorem star_frame_atom {a : Nat} {bs : List UInt8} {Q : Claim} {mem : Mem} {c : Nat}
    {v : UInt8} (h : (star (bytes a bs) Q).holds mem) (hc : Q.foot c) :
    BytesAt a bs (writeByte mem c v) :=
  h.2.1.writeByte (fun hin => h.1 c hin hc)

/-! ### The fourth clause of `DecodeNoAlias` -/

/-- **An atom never excludes a second claim at its own extent.**  A read says what
the memory answers; it says nothing about what else is read there, so a second atom
at the same address is compatible with the first.  Composition is where disjointness
is required, and it is required as a hypothesis (`star_bytes_of_apart`), not derived
from the atoms. -/
theorem self_overlap (a : Nat) (bs : List UInt8) (hne : bs ≠ []) :
    ∃ mem : Mem, BytesAt a bs mem ∧ ¬ AtomApart a bs a bs := by
  refine ⟨writeBytes [] a bs, readBytes_writeBytes_same [] bs, ?_⟩
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b rest => exact Nat.succ_pos rest.length
  intro hd
  exact hd a (atomExtent_iff.mpr ⟨Nat.le_refl a, Nat.lt_add_of_pos_right hpos⟩)
    (atomExtent_iff.mpr ⟨Nat.le_refl a, Nat.lt_add_of_pos_right hpos⟩)

/-- **`DecodeNoAlias`'s fourth clause *is* the composition's side condition.**  The
record writes `xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj`; at the run's two extents that
disjunction is `AtomApart`, the hypothesis `*` asks for.  So the logic neither
derives the clause from the reads nor weakens it: the record already states exactly
what composition requires, and composition still requires it. -/
theorem decodeXjDst_clause_iff_atomApart (n dst xj : Nat) :
    (xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj) ↔
      AtomApart dst (List.replicate (n + 64) 0) xj (List.replicate 8 0) := by
  have hpos : 0 < n + 64 :=
    Nat.lt_of_lt_of_le (by decide : 0 < 64) (Nat.le_add_left 64 n)
  have hbs : List.replicate (n + 64) (0 : UInt8) ≠ [] := by
    intro h
    have hlen : (List.replicate (n + 64) (0 : UInt8)).length = 0 := by rw [h]; rfl
    rw [List.length_replicate] at hlen
    exact absurd hlen (Nat.ne_of_gt hpos)
  have hbs' : List.replicate 8 (0 : UInt8) ≠ [] := by
    intro h
    have hlen : (List.replicate 8 (0 : UInt8)).length = 0 := by rw [h]; rfl
    rw [List.length_replicate] at hlen
    exact absurd hlen (by decide)
  rw [atomApart_iff_extent_before hbs hbs', List.length_replicate, List.length_replicate,
    Nat.add_assoc]
  exact or_comm

/-- **`DecodeNoAlias`'s `xj`/`dst` pair, on one memory.**  The record states the
fourth clause as `xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj`.  Here the cursor slot sits
inside the destination window — the destination is 72 bytes at `0`, the cursor eight
bytes at `4` — and one memory answers both reads: the window's bytes, and the eight
bytes four bytes into that window.  So the pair is not a consequence of the extent
claims; a run writes both regions, and the composition refuses rather than derives
(`star_bytes_uninhabited_of_overlap`).  The clause stays a hypothesis. -/
theorem decodeXjDst_notDerived :
    ∃ (mem : Mem) (window cursor : List UInt8),
      window.length = 72 ∧ cursor.length = 8 ∧
      BytesAt 0 window mem ∧ BytesAt 4 cursor mem ∧
      ¬ AtomApart 0 window 4 cursor ∧
      ¬ Disjoint (destinationWindow 8 0) (cursorSlot 4) := by
  refine ⟨writeBytes [] 0 (List.replicate 72 0), List.replicate 72 0,
    List.replicate 8 0, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact readBytes_writeBytes_same [] (List.replicate 72 0)
  · have hwin : readBytes (writeBytes [] 0 (List.replicate 72 0)) 0 72 =
        some (List.replicate 72 0) := readBytes_writeBytes_same [] _
    have h1 : readBytes (writeBytes [] 0 (List.replicate 72 0)) 4 68 =
        some ((List.replicate 72 0).drop 4) := by
      have h :=
        (readBytes_split (writeBytes [] 0 (List.replicate 72 0)) 0 4 68 (by simpa using hwin)).2
      simpa using h
    have h2 : readBytes (writeBytes [] 0 (List.replicate 72 0)) 4 8 =
        some (((List.replicate 72 0).drop 4).take 8) := by
      have h :=
        (readBytes_split (writeBytes [] 0 (List.replicate 72 0)) 4 8 60 (by simpa using h1)).1
      simpa using h
    rw [show ((List.replicate 72 (0 : UInt8)).drop 4).take 8 =
      List.replicate 8 0 from rfl] at h2
    exact h2
  · intro hd
    refine hd 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  · intro hd
    exact hd 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-! ### Axiom footprints

Every declaration reports its footprint.  The expected ceiling is
`[propext, Quot.sound]`; a `Classical.choice` would name a carrier this vocabulary
does not need. -/

#print axioms BytesAt
#print axioms bytesAt_iff_readBytes
#print axioms BytesAt.read
#print axioms extent
#print axioms extent_iff
#print axioms atomExtent
#print axioms atomExtent_iff
#print axioms not_extent
#print axioms readBytes_take_of_le
#print axioms BytesAt.agree_prefix
#print axioms BytesAt.agree
#print axioms BytesAt.byte
#print axioms BytesAt.presentAt
#print axioms BytesAt.hasBytes
#print axioms BytesAt.carries
#print axioms BytesAt.owns
#print axioms BytesAt.rights
#print axioms bytesAt_toOwns
#print axioms BytesAt.singleton_pointsTo
#print axioms pointsTo_bytesAt
#print axioms readBytes_eq_of_agree
#print axioms DependsOn
#print axioms bytesAt_dependsOn
#print axioms bytesAt_dependsOutside
#print axioms frame_rule_atom
#print axioms BytesAt.frame
#print axioms BytesAt.writeByte
#print axioms Claim
#print axioms bytes
#print axioms emp
#print axioms star
#print axioms star_foot_apply
#print axioms star_foot_comm
#print axioms star_foot_assoc
#print axioms star_foot_emp
#print axioms star_comm
#print axioms star_assoc
#print axioms star_emp
#print axioms emp_star
#print axioms AtomApart
#print axioms AtomApart.symm
#print axioms atomApart_iff_extent_before
#print axioms star_bytes_of_apart
#print axioms star_bytes_iff
#print axioms star_bytes_reads
#print axioms star_bytes_left
#print axioms star_bytes_right
#print axioms star_bytes_roundtrip
#print axioms bytesAt_star_inhabited
#print axioms atomApart_inhabited
#print axioms star_bytes_inhabited
#print axioms star_bytes_uninhabited_of_overlap
#print axioms star_memApart_apart
#print axioms star_memApart_reads
#print axioms frame_rule_of_star
#print axioms star_frame_atom
#print axioms self_overlap
#print axioms decodeXjDst_clause_iff_atomApart
#print axioms decodeXjDst_notDerived

end LeanLLVM
