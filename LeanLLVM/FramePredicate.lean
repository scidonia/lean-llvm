/-
The frame vocabulary as a predicate on locations, beside the region-list form.

`LeanLLVM/Refinement/JsonEscapeSteps.lean` and `JsonPipelineContract.lean` describe a
run's memory effect with three loose predicates: `UnchangedOutside` over a
`List (Nat × Nat)`, `HasBytes` as a successful `readBytes`, and `DisjointRegions`
as a pairwise separation of a list.  Those forms name a region as a value and a
run as a list of intervals, so the frame a record excludes from unchanged, the
region a record promises present, and the region a run writes are three separate
objects that can drift.  The record defects this module is meant to make
unstatable are of one class: **a record names a region, the run writes part of
it, and no predicate owns the rest.**

This module states the same vocabulary with a predicate on locations as the
region, after CompCert's `Mem.unchanged_on`:

* `UnchangedOn P mem m` says every location *outside* `P` is unchanged, so `P` is
  the region the run may change.  This polarity is what makes the bridge to the
  list form exact: a list denotes the predicate `inRegions rs` of the locations
  inside one of its intervals, and `UnchangedOutside mem m rs` is
  `UnchangedOn (inRegions rs) mem m` with no complement to construct.  (The
  inside-of-`P` reading would need a complement predicate, and a complement is
  another object that can be got wrong.)
* `present mem a` is per-location presence, and `HasBytes mem a n` is *defined*
  as `∀ k < n, present mem (a + k)`, not as a parallel predicate over
  `readBytes`.  `hasBytes_iff` shows the definition is the same proposition as
  the list vocabulary's `∃ vs, readBytes mem a n = some vs`, in both directions.
  The model has no separate read or write permission — a read returns the cell
  and a write replaces it — so presence is its only permission predicate.
* `Owns P mem m` is the region claim a post uses, and it is a *structure*: a
  footprint `P`, a proof that only `P` may change (`UnchangedOn P`), and a proof
  that every location of `P` is present.  The constructor has the presence field,
  so the region cannot be named with its presence left out; `UnchangedOn P` is
  the frame relation the first field projects, not a region claim.  The presence
  field is the predicate-indexed form of the `HasBytes` definition, `∀ a, P a →
  present m a`, so the reserve window's presence follows from the region claim
  rather than from a second range predicate.
* The frame rule is stated once: `UnchangedOn W` composes with any property
  `DependsOutside W`, and two `UnchangedOn` claims compose.  The algebra needs no
  disjointness side condition, which is why no predicate form of
  `DisjointRegions` appears here.

Nothing in this module changes the existing definitions; it is the same
statements beside them.  The bridges are the migration path: a record can be
restated in the predicate form one clause at a time, and the list form remains
the source of truth until it is.

### The historical defects

The defects below are the ones the region lists carried.  What the predicate does
to each is stated exactly, because the boundary matters:

* **The escape positions post's reserve, excluded from unchanged and promised by
  nothing.**  Unstatable as the region claim `Owns`: the constructor's presence
  field is over the *same* predicate, so there is no `Owns` that names the escape
  frame and leaves the reserve's presence out.  `omission_not_owns` is that
  non-inhabitant, and `escapeFrame_owns_reserve` reads the reserve's presence off
  the region claim.  The weaker `UnchangedOn` alone is still a proposition —
  `omission_writesOnly` is its witness — but it names no region: it is the frame
  relation, not a post's memory clause.  A post that stops at it has not made the
  region claim, and the record's clause is `Owns`; there is no second clause to
  omit.  The obligation is therefore in the type, where the prover refuses it,
  rather than in a reviewer's comparison of two clause lists.
* **An extent narrower than the writes.**  Refuted at the byte the run wrote
  (`narrowExtent_refuted`): the unchanged claim and the change are about the same
  location, with no list-complement proof in between.
* **Presence without room to write.**  Refuted at the first byte past the
  capacity (`presenceWithoutRoom_refuted`): `Owns` ties the present region and
  the written region to the same predicate, so presence alone is not a state it
  admits.
* **A region whose base is a computed address.**  The predicate expresses it:
  `blockIndexed_zero_universal` is the universal region, every address lying in
  the block window at its own computed index, and a finite list (a finite union
  of bounded intervals) cannot denote it; `blockIndexed_contains` gives the
  per-member containment, and `blockWindow_iff_inRegion` the single computed
  base, which a list can also name once the term is in scope.  The predicate is
  strictly stronger for the computed-by-member shape, not weaker than the list.
-/
import LeanLLVM.Memory
import LeanLLVM.Refinement.JsonEscapeSteps

namespace LeanLLVM

/-! ### Per-location presence -/

/-- A byte is present at `a` when the memory answers a read there.  In this
model a present byte is also writable: `writeByte` replaces a cell or adds one,
so presence is the only permission the representation has. -/
def present (mem : Mem) (a : Nat) : Prop := ∃ b, readByte mem a = some b

/-- A write preserves every byte that was present, at whatever address.  A store
either replaces an existing cell or appends a fresh one, so the only effect on
presence is to add. -/
theorem present_writeByte (mem : Mem) (addr : Nat) (c : UInt8) {a : Nat}
    (h : present mem a) : present (writeByte mem addr c) a := by
  obtain ⟨b, hb⟩ := h
  by_cases hae : a = addr
  · subst hae
    exact ⟨c, readByte_writeByte_same mem a c⟩
  · exact ⟨b, by rw [readByte_writeByte_other mem c (Ne.symm hae)]; exact hb⟩

/-- Presence survives a byte sequence. -/
theorem present_writeBytes (mem : Mem) (start : Nat) (bs : List UInt8) {a : Nat}
    (h : present mem a) : present (writeBytes mem start bs) a := by
  induction bs generalizing mem start with
  | nil => exact h
  | cons c cs ih =>
      exact ih (writeByte mem start c) (start + 1) (present_writeByte mem start c h)

/-- The bytes at `a … a + n` are present, stated per location.  This is the
region form the list vocabulary spells `∃ vs, readBytes mem a n = some vs`. -/
def HasBytes (mem : Mem) (a n : Nat) : Prop := ∀ k, k < n → present mem (a + k)

/-- A successful range read supplies a present byte at every offset below its
length. -/
theorem readBytes_some_present :
    ∀ (mem : Mem) (a n : Nat) (vs : List UInt8),
      readBytes mem a n = some vs → ∀ j, j < n → present mem (a + j)
  | _, _, 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | mem, a, n + 1, vs, h, j, hj => by
      cases hb : readByte mem a with
      | none =>
          simp only [readBytes, hb] at h
          cases h
      | some b =>
          cases hbs : readBytes mem (a + 1) n with
          | none =>
              simp only [readBytes, hb, hbs] at h
              cases h
          | some bs =>
              have hvs : vs = b :: bs := by
                simp only [readBytes, hb, hbs, Option.some.injEq] at h
                exact h.symm
              subst hvs
              cases j with
              | zero => exact ⟨b, by simpa using hb⟩
              | succ j =>
                  have hj' : j < n := by omega
                  have hp := readBytes_some_present mem (a + 1) n bs hbs j hj'
                  have heq : (a + 1) + j = a + (j + 1) := by omega
                  rwa [heq] at hp

/-- A present range reads back as some byte sequence. -/
theorem readBytes_of_hasBytes :
    ∀ (mem : Mem) (a n : Nat), HasBytes mem a n → ∃ vs, readBytes mem a n = some vs
  | _, _, 0, _ => ⟨[], rfl⟩
  | mem, a, n + 1, h => by
      obtain ⟨b, hb⟩ := h 0 (Nat.succ_pos n)
      have hb' : readByte mem a = some b := by simpa using hb
      have htail : HasBytes mem (a + 1) n := by
        intro k hk
        have hk' : k + 1 < n + 1 := by omega
        have hp := h (k + 1) hk'
        have heq : a + (k + 1) = a + 1 + k := by omega
        rwa [heq] at hp
      obtain ⟨bs, hbs⟩ := readBytes_of_hasBytes mem (a + 1) n htail
      exact ⟨b :: bs, by simp only [readBytes, hb', hbs]⟩

/-- The per-location form and the list vocabulary's `HasBytes` are the same
proposition.  This is the presence bridge: a record can be restated one clause
at a time. -/
theorem hasBytes_iff (mem : Mem) (a n : Nat) :
    Refinement.HasBytes mem a n ↔ HasBytes mem a n := by
  constructor
  · rintro ⟨vs, hvs⟩
    exact readBytes_some_present mem a n vs hvs
  · intro h
    exact readBytes_of_hasBytes mem a n h

/-- A shorter range is present. -/
theorem HasBytes.mono {mem : Mem} {a n m : Nat} (h : HasBytes mem a n)
    (hmn : m ≤ n) : HasBytes mem a m :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hmn)

/-- A subrange of a present range is present. -/
theorem HasBytes.sub {mem : Mem} {a n b m : Nat} (h : HasBytes mem a n)
    (hlo : a ≤ b) (hhi : b + m ≤ a + n) : HasBytes mem b m := by
  intro k hk
  have hlt : b + k - a < n := by omega
  have hp := h (b + k - a) hlt
  have heq : a + (b + k - a) = b + k := by omega
  rwa [heq] at hp

/-- Two adjacent present ranges concatenate. -/
theorem HasBytes.append {mem : Mem} {a n b m : Nat} (h1 : HasBytes mem a n)
    (h2 : HasBytes mem b m) (hadj : b = a + n) : HasBytes mem a (n + m) := by
  subst hadj
  intro k hk
  rcases Nat.lt_or_ge k n with hkn | hkn
  · exact h1 k hkn
  · have hk' : k - n < m := by omega
    have hp := h2 (k - n) hk'
    have heq : a + n + (k - n) = a + k := by omega
    rwa [heq] at hp

/-- A present range stays present under any write. -/
theorem HasBytes.writeBytes {mem : Mem} {a n : Nat} (h : HasBytes mem a n)
    (start : Nat) (bs : List UInt8) : HasBytes (writeBytes mem start bs) a n :=
  fun k hk => present_writeBytes mem start bs (h k hk)

/-! ### Unchanged outside a predicate -/

/-- Every location outside `P` is unchanged; `P` is the region the run may
change.  This is CompCert's `Mem.unchanged_on` reading of a footprint, and it is
the predicate form of `UnchangedOutside`. -/
def UnchangedOn (P : Nat → Prop) (mem m : Mem) : Prop :=
  ∀ a, ¬ P a → readByte m a = readByte mem a

/-- A memory is unchanged outside a predicate from itself. -/
theorem UnchangedOn.refl (P : Nat → Prop) (m : Mem) : UnchangedOn P m m :=
  fun _ _ => rfl

/-- Two steps that leave the same region alone compose. -/
theorem UnchangedOn.comp {P : Nat → Prop} {m0 m1 m2 : Mem}
    (h01 : UnchangedOn P m0 m1) (h12 : UnchangedOn P m1 m2) :
    UnchangedOn P m0 m2 :=
  fun a ha => (h12 a ha).trans (h01 a ha)

/-- The second step's region may be smaller than the first's: a byte outside the
smaller region is outside the larger one too. -/
theorem UnchangedOn.comp_sub {P P' : Nat → Prop} {m0 m1 m2 : Mem}
    (h01 : UnchangedOn P m0 m1) (h12 : UnchangedOn P' m1 m2)
    (hsub : ∀ a, P' a → P a) : UnchangedOn P m0 m2 :=
  fun a ha => (h12 a (fun hp' => ha (hsub a hp'))).trans (h01 a ha)

/-- A smaller region is a stronger claim: unchanged outside a smaller region
implies unchanged outside a larger one. -/
theorem UnchangedOn.mono {P P' : Nat → Prop} {mem m : Mem}
    (h : UnchangedOn P mem m) (hsub : ∀ a, P a → P' a) : UnchangedOn P' mem m :=
  fun a ha => h a (fun hp => ha (hsub a hp))

/-- Two claims about the same region conjoin: outside their intersection neither
region may change, and both claims therefore hold there.

The case split is on the *equality the goal asks for*, which is decidable for
`Option UInt8`; the intersection itself is never decided, so the proof stays
constructive. -/
theorem UnchangedOn.conj {P Q : Nat → Prop} {mem m : Mem}
    (hP : UnchangedOn P mem m) (hQ : UnchangedOn Q mem m) :
    UnchangedOn (fun a => P a ∧ Q a) mem m := by
  intro a ha
  by_cases hxy : readByte m a = readByte mem a
  · exact hxy
  · have hnp : ¬ P a := fun hp => hxy (hQ a (fun hq => ha ⟨hp, hq⟩))
    exact absurd (hP a hnp) hxy

/-- The union of two write sets is one region: a byte outside both is outside
each, so either claim gives the equality.  No disjointness side condition is
needed, which is what a list merge cannot avoid. -/
theorem UnchangedOn.union {P Q : Nat → Prop} {mem m : Mem}
    (hP : UnchangedOn P mem m) (_hQ : UnchangedOn Q mem m) :
    UnchangedOn (fun a => P a ∨ Q a) mem m :=
  fun a ha => hP a (fun hp => ha (Or.inl hp))

/-- A read wholly inside the unchanged complement is the same read on both
memories. -/
theorem readBytes_eq_of_UnchangedOn {P : Nat → Prop} {mem m : Mem}
    (h : UnchangedOn P mem m) :
    ∀ {a n : Nat}, (∀ k, k < n → ¬ P (a + k)) → readBytes m a n = readBytes mem a n
  | _, 0, _ => rfl
  | a, n + 1, hP => by
      have hhead : readByte m a = readByte mem a := h a (hP 0 (Nat.succ_pos n))
      have htail : readBytes m (a + 1) n = readBytes mem (a + 1) n :=
        readBytes_eq_of_UnchangedOn h (a := a + 1) (n := n) (fun k hk => by
          have hp := hP (k + 1) (by omega)
          have heq : a + (k + 1) = a + 1 + k := by omega
          rwa [heq] at hp)
      simp only [readBytes, hhead, htail]

/-! ### Lists as predicates -/

/-- The predicate a region list denotes: the locations inside one of its
intervals. -/
def inRegions (regions : List (Nat × Nat)) : Nat → Prop :=
  fun a => ∃ r ∈ regions, r.1 ≤ a ∧ a < r.1 + r.2

/-- One listed interval as a predicate. -/
def inRegion (r : Nat × Nat) : Nat → Prop :=
  fun a => r.1 ≤ a ∧ a < r.1 + r.2

/-- A singleton list denotes its one interval. -/
theorem inRegion_iff_inRegions_singleton (r : Nat × Nat) (a : Nat) :
    inRegion r a ↔ inRegions [r] a := by
  simp [inRegion, inRegions]

/-- **The list bridge.**  `UnchangedOutside` over a region list is exactly
`UnchangedOn` over the predicate the list denotes.  The direction from the list
is `not_exists`, and the direction to the list is the same step read backwards;
both are kept because migration reads the bridge in both directions. -/
theorem unchangedOutside_iff_inRegions {mem m : Mem} {regions : List (Nat × Nat)} :
    Refinement.UnchangedOutside mem m regions ↔ UnchangedOn (inRegions regions) mem m := by
  constructor
  · intro h a ha
    exact h a (fun r hr hi => ha ⟨r, hr, hi⟩)
  · intro h a hout
    exact h a (fun ⟨r, hr, hi⟩ => hout r hr hi)

/-! ### The region claim and the frame rule -/

/-- A run owns the region `P`: it changes only inside `P`, and every location of
`P` is present afterwards.  The claim is a structure, not a conjunction an author
can prune: the constructor has the presence field, so there is no inhabitant of
`Owns P` with the reserve window named and its presence left out.  The weaker
`UnchangedOn P` is the frame relation the `unchanged` field projects, not a
region claim; a post that stops at it has not named a region at all. -/
structure Owns (P : Nat → Prop) (mem m : Mem) : Prop where
  /-- The run changes only inside `P`. -/
  unchanged : UnchangedOn P mem m
  /-- Every location of `P` is present afterwards. -/
  present : ∀ a, P a → present m a

/-- A memory property `Q` is about the complement of `W` when agreement outside
`W` determines it. -/
def DependsOutside (W : Nat → Prop) (Q : Mem → Prop) : Prop :=
  ∀ {mem m : Mem}, UnchangedOn W mem m → (Q mem ↔ Q m)

/-- The region claim is exactly its two fields.  The structure's constructor is
the only introduction rule, so the presence field is not optional: an author
proving `Owns P` has both goals, and the half that the old records omitted is one
of them. -/
theorem owns_iff {P : Nat → Prop} {mem m : Mem} :
    Owns P mem m ↔ UnchangedOn P mem m ∧ ∀ a, P a → present m a :=
  ⟨fun h => ⟨h.unchanged, h.present⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The frame rule's shape.  A run that changes only inside `W` composes with
any property that depends only on the complement of `W`. -/
theorem frame_rule {W : Nat → Prop} {mem m : Mem} (h : UnchangedOn W mem m)
    {Q : Mem → Prop} (hQ : DependsOutside W Q) : Q mem ↔ Q m :=
  hQ h

/-! ### The historical defects -/

/-- The **capacity** window of the escape positions stream: `xp` to
`xp + 4 * blockMax xn0`, which includes the batch's eight-entry reserve.  It is the
window the record's frame named *before* that frame was corrected: the record now
names the run's touched extent (`Refinement.touchedPositions`, the counted positions
plus the reserve), which is this window's prefix and shorter whenever the block
counts fewer than its maximum.  The theorems below are about the capacity-wide
shape, which is why this definition keeps `blockMax`. -/
def reserveWindow (xp xn0 : Nat) : Nat → Prop :=
  fun a => xp ≤ a ∧ a < xp + 4 * Refinement.blockMax xn0

/-- The capacity-wide frame predicate: the stream's capacity (the reserve
included), the count's slot and the carry's sixteen bytes.  An earlier shape of the
escape positions post named exactly this; the record names the touched extent now,
so this is the wider frame those theorems are about. -/
def escapeFrame (xp xn carry xn0 : Nat) : Nat → Prop :=
  inRegions [(xp, 4 * Refinement.blockMax xn0), (xn, 8), (carry, 16)]

/-- The reserve window is inside the frame predicate. -/
theorem reserveWindow_mem_escapeFrame (xp xn carry xn0 a : Nat)
    (h : reserveWindow xp xn0 a) : escapeFrame xp xn carry xn0 a :=
  ⟨(xp, 4 * Refinement.blockMax xn0), by simp, h⟩

/-- **The reserve cannot be excluded and left unowned.**  If a post owns the
capacity-wide frame predicate, every location of the reserve window is present.
This is the half the escape positions post initially omitted: its exclusion named
the whole capacity, but no predicate promised the reserve's presence, so the run's
own successor had no capacity to stand on.  The record states that presence as a
clause of its own now, at the capacity, beside a frame at the touched extent. -/
theorem escapeFrame_owns_reserve {xp xn carry xn0 : Nat} {mem m : Mem}
    (h : Owns (escapeFrame xp xn carry xn0) mem m) :
    ∀ a, reserveWindow xp xn0 a → present m a :=
  fun a ha => h.present a (reserveWindow_mem_escapeFrame xp xn carry xn0 a ha)

/-- The witness memory: one byte written at address zero. -/
def omissionMem : Mem := [(0, 7)]

/-- The capacity-wide frame predicate, at a stream base of zero, a capacity of
`4 * blockMax 0`, and the two slots at 100 and 200 (both inside the capacity). -/
theorem omission_writesOnly :
    UnchangedOn (escapeFrame 0 100 200 0) [] omissionMem := by
  intro a ha
  have h0 : a ≠ 0 := by
    intro h
    subst h
    apply ha
    apply reserveWindow_mem_escapeFrame 0 100 200 0 0
    show 0 ≤ 0 ∧ 0 < 0 + 4 * Refinement.blockMax 0
    unfold Refinement.blockMax Refinement.batchReserve
    decide
  have hne : ¬ (0 = a) := fun h => h0 h.symm
  show (if (0 = a) then some 7 else readByte [] a) = readByte [] a
  rw [if_neg hne]

/-- Address one is inside the reserve window at these numbers, and it is not
present in the witness memory. -/
theorem omission_not_present_one : ¬ present omissionMem 1 := by
  intro hp
  obtain ⟨b, hb⟩ := hp
  have hne : ¬ (0 = 1) := by decide
  have hnone : readByte omissionMem 1 = none := by
    show (if (0 = 1) then some 7 else readByte [] 1) = none
    rw [if_neg hne]
    rfl
  rw [hnone] at hb
  cases hb

/-- **The earlier post's omission, stated directly.**  The capacity-wide frame
clause holds — the run changes only inside that frame — and the reserve window's
presence does not.  That conjunction is the gap that shape carried: the exclusion
is satisfied without the presence half, so it alone does not hand its successor a
capacity. -/
theorem reserve_omission_witness :
    UnchangedOn (escapeFrame 0 100 200 0) [] omissionMem ∧
      ¬ (∀ a, reserveWindow 0 0 a → present omissionMem a) := by
  constructor
  · exact omission_writesOnly
  · intro hp
    apply omission_not_present_one
    apply hp 1
    show 0 ≤ 1 ∧ 1 < 0 + 4 * Refinement.blockMax 0
    unfold Refinement.blockMax Refinement.batchReserve
    decide

/-- **The earlier post's omission is not an owned region.**  The run changes only
inside the capacity-wide frame predicate, but the reserve window is not present, so
that shape cannot claim `Owns`; the omission is exactly the weaker `UnchangedOn`
half.  `Owns` could not have omitted the presence clause, because it is one
predicate with both halves; the old list vocabulary had a second object in which
the reserve could be named and then promised by nothing. -/
theorem omission_not_owns :
    ¬ Owns (escapeFrame 0 100 200 0) [] omissionMem := by
  intro h
  apply omission_not_present_one
  apply h.present 1
  apply reserveWindow_mem_escapeFrame 0 100 200 0 1
  show 0 ≤ 1 ∧ 1 < 0 + 4 * Refinement.blockMax 0
  unfold Refinement.blockMax Refinement.batchReserve
  decide

/-- **An extent narrower than the writes is unstatable.**  If the run changed a
byte outside the region it names, the unchanged claim is false there.  With the
predicate form the single fact `¬ W a` refutes it; the list form has to prove the
narrow list does not contain the changed address. -/
theorem not_unchangedOn_of_changed {W : Nat → Prop} {mem m : Mem} {a : Nat}
    (ha : ¬ W a) (hchange : readByte m a ≠ readByte mem a) :
    ¬ UnchangedOn W mem m :=
  fun h => hchange (h a ha)

/-- **Presence without room to write is unstatable as an owned region.**  If the
run changed a byte outside the present region `P`, it does not own `P`, whatever
`P` contains.  The staging defect — presence of the event buffer with no bound
tying the appended stream to its capacity — is this refutation at the first byte
past `evcap`. -/
theorem not_owns_of_changed_outside {P : Nat → Prop} {mem m : Mem} {a : Nat}
    (ha : ¬ P a) (hchange : readByte m a ≠ readByte mem a) :
    ¬ Owns P mem m :=
  fun h => not_unchangedOn_of_changed ha hchange h.unchanged

/-- **Presence without room is refuted constructively.**  `Owns P` says every
changed byte lies in `P`; the double negation is what remains without deciding
an arbitrary `P`. -/
theorem owns_changed_not_not {P : Nat → Prop} {mem m : Mem} {a : Nat}
    (h : Owns P mem m) (hchange : readByte m a ≠ readByte mem a) : ¬ ¬ P a :=
  fun ha => hchange (h.unchanged a ha)

/-- A caller's four-byte capacity at address zero, all present. -/
def stagedCapacity : Mem := [(0, 0), (1, 0), (2, 0), (3, 0)]

/-- The staged capacity is present before the reserve write. -/
theorem stagedCapacity_present : HasBytes stagedCapacity 0 4 := by
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl <;>
    exact ⟨0, by simp [stagedCapacity, readByte]⟩

/-- **The narrow-extent defect, at the escape batch's first reserve byte.**  The
counted prefix is `(0, 4)`; the batch writes its first reserve byte at address
four, outside the narrow frame.  The run refutes the narrow claim at the byte it
wrote, which is the omission the pipeline post carried: an extent narrower than the
writes leaves a moved byte outside every region the post names.  This is why the
corrected record's frame stops at the *touched* extent — the counted positions plus
the reserve — and not at the counted prefix. -/
theorem narrowExtent_refuted :
    ¬ UnchangedOn (inRegion (0, 4)) [] (writeBytes [] 4 [0]) := by
  apply not_unchangedOn_of_changed (W := inRegion (0, 4)) (a := 4)
  · simp [inRegion]
  · rw [show writeBytes ([] : Mem) 4 [0] = writeByte [] 4 0 from rfl,
      readByte_writeByte_same]
    simp [readByte]

/-- **The presence-without-room defect, at the same reserve byte.**  The caller
staged the whole four-byte capacity and the run writes at four, outside it.  The
staging defect was presence of a buffer with no bound tying the appended stream
to its capacity; `Owns` refuses the state at the byte past the capacity, because
the presence region and the written region are the same predicate. -/
theorem presenceWithoutRoom_refuted :
    ¬ Owns (inRegion (0, 4)) stagedCapacity (writeBytes stagedCapacity 4 [0]) := by
  apply not_owns_of_changed_outside (P := inRegion (0, 4)) (a := 4)
  · simp [inRegion]
  · rw [show writeBytes stagedCapacity 4 [0] = writeByte stagedCapacity 4 0 from rfl,
      readByte_writeByte_same]
    simp [stagedCapacity, readByte]

/-- **Presence without room, with the presence side proved.**  The capacity is
still present after the reserve write, so the `Owns` failure above is the missing
write room alone, not a lost byte.  This is the staging defect stated in full:
presence holds and the written region is not the present one. -/
theorem presenceWithoutRoom_witness :
    HasBytes (writeBytes stagedCapacity 4 [0]) 0 4 ∧
      ¬ Owns (inRegion (0, 4)) stagedCapacity (writeBytes stagedCapacity 4 [0]) :=
  ⟨HasBytes.writeBytes stagedCapacity_present 4 [0], presenceWithoutRoom_refuted⟩

/-- A block-indexed region: the sixty-four-byte block at `base + 64 * b`, for
every block index `b`.  Its base is computed from the index and the family is
not a finite literal list, so a predicate is what expresses it; the list form
would have to enumerate every block up front. -/
def blockIndexed (base : Nat) : Nat → Prop :=
  fun a => ∃ b, base + 64 * b ≤ a ∧ a < base + 64 * b + 64

/-- Every block's window is contained in the block-indexed region, at its
computed base.  This is the fourth shape: a region whose base is computed from
the location's block, which a list would have to name one entry at a time. -/
theorem blockIndexed_contains (base b k : Nat) (hk : k < 64) :
    blockIndexed base (base + 64 * b + k) :=
  ⟨b, by omega, by omega⟩

/-- `blockIndexed 0` is the universal region: every address lies in some block's
window, and the base is computed from the address's block index.  A finite list
of intervals denotes only a finite union of bounded intervals, so no list
denotes this region; the predicate is strictly stronger for the computed-by-member
shape, not weaker than the list it replaces. -/
theorem blockIndexed_zero_universal (a : Nat) : blockIndexed 0 a := by
  apply Exists.intro (a / 64)
  constructor
  · have h := Nat.div_mul_le_self a 64
    omega
  · have hmod : a % 64 < 64 := Nat.mod_lt a (by decide)
    have hdiv : a % 64 + 64 * (a / 64) = a := Nat.mod_add_div a 64
    omega

/-- A single computed base is expressible as one list entry too, once the term is
in scope; the record that needed it added the base as a parameter for exactly
that reason.  The strictly stronger shape is the family above, whose bases are
computed by the member rather than fixed before the list is written. -/
theorem blockWindow_iff_inRegion (base : Nat) (blk0 : BitVec 64) (a : Nat) :
    (base + Refinement.blockAddr blk0 ≤ a ∧
        a < base + Refinement.blockAddr blk0 + 64) ↔
      inRegion (base + Refinement.blockAddr blk0, 64) a :=
  Iff.rfl

/-! ### Axiom footprints

Every declaration above reports its footprint.  The expected ceiling is
`[propext, Quot.sound]`; any `Classical.choice` would name a carrier this
vocabulary does not need. -/

#print axioms present
#print axioms present_writeByte
#print axioms present_writeBytes
#print axioms HasBytes
#print axioms readBytes_some_present
#print axioms readBytes_of_hasBytes
#print axioms hasBytes_iff
#print axioms HasBytes.mono
#print axioms HasBytes.sub
#print axioms HasBytes.append
#print axioms HasBytes.writeBytes
#print axioms UnchangedOn
#print axioms UnchangedOn.refl
#print axioms UnchangedOn.comp
#print axioms UnchangedOn.comp_sub
#print axioms UnchangedOn.mono
#print axioms UnchangedOn.conj
#print axioms UnchangedOn.union
#print axioms readBytes_eq_of_UnchangedOn
#print axioms inRegions
#print axioms inRegion
#print axioms inRegion_iff_inRegions_singleton
#print axioms unchangedOutside_iff_inRegions
#print axioms Owns
#print axioms owns_iff
#print axioms DependsOutside
#print axioms frame_rule
#print axioms reserveWindow
#print axioms escapeFrame
#print axioms reserveWindow_mem_escapeFrame
#print axioms escapeFrame_owns_reserve
#print axioms omissionMem
#print axioms omission_writesOnly
#print axioms omission_not_present_one
#print axioms reserve_omission_witness
#print axioms omission_not_owns
#print axioms not_unchangedOn_of_changed
#print axioms not_owns_of_changed_outside
#print axioms owns_changed_not_not
#print axioms stagedCapacity
#print axioms stagedCapacity_present
#print axioms narrowExtent_refuted
#print axioms presenceWithoutRoom_refuted
#print axioms presenceWithoutRoom_witness
#print axioms blockIndexed
#print axioms blockIndexed_contains
#print axioms blockIndexed_zero_universal
#print axioms blockWindow_iff_inRegion

end LeanLLVM
