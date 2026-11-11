/-
Rights on the region claim, stated beside it.

`LeanLLVM/FramePredicate.lean` states the region claim `Owns P` as two facts about
one predicate: nothing outside `P` changes, and every location of `P` is present.
One predicate for both questions is why `LeanLLVM/Refinement/JsonEscapeDecodeRun.lean`
carries four hand-written disjointness clauses — `tab`/`dst`, `err`/`dst`,
`err`/`xj`, `xj`/`dst` — each found by executing a staging that broke the post.
The model cannot say "this unit may not write here": it can only say that two
regions do not overlap, pairwise, by hand, and nothing ties a hand-written region
to what the run actually writes.

This module adds a claim beside `Owns`, so nothing already stated is invalidated
and a record migrates on its own:

* `Disjoint P Q` is disjointness as a *hypothesis* — the shape the composition
  lemma takes for its side condition — not a connective added to the vocabulary.
* `Rights P K W mem m` is the region claim with rights: the named region `P` is
  present, the declared writable set `W` bounds the change (nothing outside it
  changes) and lies inside `P` (a writable location is a present one), and the
  kept set `K` shares no location with `W`.  `Owns` is the case `K` empty and
  `W = P`, so `rights_empty_iff_owns` recovers the old claim exactly.
* `sep` is `*`: two claims, the first's region apart from the second's declared
  writable set, compose into the claim on their unions.  `owns_sep` is the same
  lemma at the old claim, derived from `sep` rather than stated again for it.
* `frame_rule_derived` reads the frame rule off `sep`'s conclusion instead of
  assuming it: the composition's frame is on the union of the declared sets.
* `decodeTableInsideWindow_unstatable` and `decodeCursorOverOffset_unstatable`
  state two of the record's four escaped aliasings in this vocabulary and refute
  them structurally — no memory, no executed row — because the claim's `apart`
  field is refuted at the shared byte.  Those are the stagings the record's `pre`
  admitted and whose post then failed.

### Derived or restated

`decodeClaim_yields_four` reads the record's `tab`/`dst`, `err`/`dst` and
`err`/`xj` clauses off **one** field of one claim: the consumer names the kept set
and the writable set once, and the three pairs follow.  The fourth, `xj`/`dst`, is
between two regions the same run writes, so the claim cannot separate them, and
`cursorWindowNotDerived` exhibits two inhabited claims whose declared sets meet —
no rule derives the separation from the claims.  That clause therefore stays a
hypothesis, of `sep` at the run's own two writers.

So three of the four are derived and the fourth is restated: the consumer still
writes that one pair.  What the rights component changes is the rest — the three
cannot be dropped (dropping one leaves no claim rather than a weaker pre), and the
one that remains is a hypothesis between two claims' own declared sets rather than
a disjunction of hand-computed extents in a record's `pre`.  It is not a
separation logic: four clauses stay four where four writers meet four regions.

### Ownership, and what it changes

The region claim above is a *permission*: it says what a unit may change and what
it promises present, and the disjointness it needs is a predicate an author writes
and a lemma takes as an argument.  The rest of this module states the byte as a
*resource*:

* `PointsTo a b mem` is one byte's value.  Its footprint is the address it names,
  so a claim's owned set is computed from the claim rather than declared beside it
  — that is the difference between ownership and presence.
* `Star P Q` is `*`: two claims on heaps that share no address compose into the
  claim on their union.  The split is part of the composed claim, so
  `PointsTo a v * PointsTo a w` is *uninhabited*, for every memory and every pair
  of values (`star_pointsTo_uninhabited`); `*` is commutative and associative, and
  `EmptyHeap` is the unit at a points-to claim (`pointsTo_star_empty_iff`).  `sep`
  took the separation as an argument; here there is no composition to state without
  it.
* Exclusivity has two readings, and they are kept apart.  The structural one is
  `pointsTo_exclusive`: two claims about one memory's byte agree, because the
  memory is a function — no hypothesis and no composition.  The standard one is
  `star_pointsTo_agree`: `PointsTo a v * PointsTo a w` gives `v = w`, because the
  composed claim has no inhabitant rather than because the caller said the sets are
  apart.  `star_pointsTo_apart_inhabited` is the control: at two addresses the same
  composition is inhabited, so the refutation is the shared byte.
* A write at an owned byte yields the claim at the new value
  (`pointsTo_writeByte`, `star_pointsTo_write`); a write at another byte leaves the
  claim (`PointsTo.writeByte`); a write at a byte the claim does not own yields no
  claim about that byte — `unowned_byte_not_claimed` exhibits two memories carrying
  the same claim and disagreeing there.  The store's byte is a fresh claim on the
  new memory, not an update of the composed one, and the composed claim's footprint
  excludes the write.
* The frame rule is read off `*` rather than assumed: `star_pointsTo_write` updates
  the first part's owned byte and leaves the second claim in place.  Its memory
  effect is the `UnchangedOn` the property-based rule consumes
  (`pointsTo_write_unchangedOn`), so the old rule is that write read through
  `DependsOutside` (`frame_rule_of_write`); `frame_rule_of_claim` and
  `frame_rule_sep` keep their statements unchanged.
* `Carries W mem` is the set-valued claim, and its composition *derives* the
  separation: `star_carries_disjoint` takes `Carries W * Carries V` to
  `Disjoint W V`, and `Carries W * Carries W` has no inhabitant wherever `W` names
  a byte.

### What this does not buy

The separation inside `*` is a conjunct of the composed claim, not a message from
nowhere: over a total memory there is no other way to say that two claims are about
different bytes.  What changes is who writes it.  The footprint now comes from the
claim's own addresses, so nothing can declare a region narrower or wider than what
the claim is about, and `Carries W * Carries V` yields the disjointness rather than
requiring it.

It does not derive the fourth clause.  `xj`/`dst` is a pair of writes by one run,
and a run legitimately owns both regions it writes: a byte written twice is one
byte holding the second value.  `runOwned_meeting_regions_inhabited` exhibits the
run's claim over the union of the two regions at a staging where they meet, and
`cursorWindow_carries_notStar` shows the two-claim composition refused there — a
refusal, which is not a separation.  So `xj`/`dst` stays a staging hypothesis under
ownership exactly as it did under `Rights`, and the count of derived clauses is
unchanged.
-/
import LeanLLVM.FramePredicate

namespace LeanLLVM

/-! ### Disjointness as a hypothesis -/

/-- Two regions share no location.  This is the shape the composition lemma takes
for its side condition: `sep` is handed the disjointness it needs instead of
building a new proposition former, which is what keeps the rights component
additive over the claims the records already state. -/
def Disjoint (P Q : Nat → Prop) : Prop := ∀ a, P a → Q a → False

/-- A smaller region is easier to separate. -/
theorem Disjoint.sub_left {P P' Q : Nat → Prop} (h : Disjoint P' Q)
    (hsub : ∀ a, P a → P' a) : Disjoint P Q :=
  fun a hp hq => h a (hsub a hp) hq

/-- A smaller region is easier to separate, on the other side. -/
theorem Disjoint.sub_right {P Q Q' : Nat → Prop} (h : Disjoint P Q')
    (hsub : ∀ a, Q a → Q' a) : Disjoint P Q :=
  fun a hp hq => h a hp (hsub a hq)

/-- Disjointness is symmetric. -/
theorem Disjoint.symm {P Q : Nat → Prop} (h : Disjoint P Q) : Disjoint Q P :=
  fun a hq hp => h a hp hq

/-- The region that names nothing: the kept set of a claim that keeps nothing. -/
def emptyRegion : Nat → Prop := fun _ => False

/-! ### The region claim with rights -/

/-- A region claim with rights.  `Owns P` asks two questions of one predicate — is
this the frame the run may change, and is this the region the run promises
present — so a record states them together and can narrow neither.  This claim
states them apart:

* `present` — every location of the named region `P` is present afterwards;
* `writes` — nothing outside the declared writable set `W` changes;
* `within` — the writable set is inside the named region, so every location the
  run may write is one the claim promises present (`writeByte` replaces a cell or
  appends one, so presence is the only permission a byte has in this model);
* `apart` — the kept set `K` and the writable set `W` share no location.

`apart` is the component no list of pairwise clauses can state: a unit may not
write where it keeps, so a record cannot name one slot both as the caller's and as
the run's output.  The kept set is what a record's post reads about a region it
does not own — the bytes the run's result depends on and must not touch. -/
structure Rights (P K W : Nat → Prop) (mem m : Mem) : Prop where
  present : ∀ a, P a → present m a
  writes : UnchangedOn W mem m
  within : ∀ a, W a → P a
  apart : Disjoint K W

/-- Every location the run may write is present: the declared right is a right
over bytes the claim already promises. -/
theorem rights_writable_present {P K W : Nat → Prop} {mem m : Mem}
    (h : Rights P K W mem m) : ∀ a, W a → present m a :=
  fun a hw => h.present a (h.within a hw)

/-- The kept region is the caller's after the run: `apart` and `writes` supply the
equality.  This is the fact a record's post reads about a slot it does not own. -/
theorem Rights.kept {P K W : Nat → Prop} {mem m : Mem}
    (h : Rights P K W mem m) : ∀ a, K a → readByte m a = readByte mem a :=
  fun a hk => h.writes a (fun hw => h.apart a hk hw)

/-- **The projection back to the region claim.**  `within` makes the declared set's
frame a frame on the named region, so a righted claim is an `Owns`.  A consumer that
wants only the old statement reads it from here, which is what keeps the migration
per record. -/
theorem Rights.toOwns {P K W : Nat → Prop} {mem m : Mem}
    (h : Rights P K W mem m) : Owns P mem m :=
  ⟨h.writes.mono h.within, h.present⟩

/-- **The old claim is the new one with nothing kept and its own region as the
writable set.**  This is where a record starts: it narrows `W` and widens `K` to
what its run does, one clause at a time, and the old statement stays available
through `Rights.toOwns` throughout. -/
theorem ofOwns {P : Nat → Prop} {mem m : Mem} (h : Owns P mem m) :
    Rights P emptyRegion P mem m where
  present := h.present
  writes := h.unchanged
  within := fun _ hp => hp
  apart := fun _ hk _ => hk

/-- The rights component is additive: at the old claim's own sets it is exactly
`Owns`, so no record that states `Owns` is invalidated and none has to migrate. -/
theorem rights_empty_iff_owns {P : Nat → Prop} {mem m : Mem} :
    Rights P emptyRegion P mem m ↔ Owns P mem m :=
  ⟨fun h => h.toOwns, fun h => ofOwns h⟩

/-! ### The forms rights make unstatable -/

/-- **A claim cannot have changed a byte outside its declared writable set.**  The
changed byte refutes `writes` at that address, so a record that under-declares what
its run writes has no claim rather than a claim with a weak clause. -/
theorem not_rights_of_changed_outside {P K W : Nat → Prop} {mem m : Mem} {a : Nat}
    (ha : ¬ W a) (hchange : readByte m a ≠ readByte mem a) :
    ¬ Rights P K W mem m :=
  fun h => hchange (h.writes a ha)

/-- **A unit may not write where it keeps.**  One location in both the kept set and
the writable set refutes every claim with those sets: the refutation is the `apart`
field, so it needs no memory and no executed row. -/
theorem rights_apart_unstatable {P K W : Nat → Prop} {mem m : Mem} {a : Nat}
    (hk : K a) (hw : W a) : ¬ Rights P K W mem m :=
  fun h => h.apart a hk hw

/-- A one-byte write changes nothing outside the single location it writes. -/
theorem unchangedOn_writeByte (mem : Mem) (addr : Nat) (c : UInt8) :
    UnchangedOn (inRegion (addr, 1)) mem (writeByte mem addr c) := by
  intro a ha
  have hin : inRegion (addr, 1) addr :=
    ⟨Nat.le_refl addr, Nat.lt_add_of_pos_right (by decide : 0 < 1)⟩
  have hne : a ≠ addr := by
    intro heq
    apply ha
    rw [heq]
    exact hin
  show readByte (writeByte mem addr c) a = readByte mem a
  exact readByte_writeByte_other mem c (fun h => hne h.symm)

/-- The witness memory of the control: one byte at address zero. -/
def oneByteMem : Mem := writeByte [] 0 0

/-- The control for `rights_apart_unstatable`: with the kept set and the writable
set apart, a claim of the same shape is inhabited, so the refutation above is the
aliasing and not the shape.  It is also the control for
`not_rights_of_changed_outside`: the run changed address zero, which lies inside its
declared writable set, and the claim stands. -/
theorem rights_apart_inhabited :
    Rights (inRegion (0, 1)) (inRegion (100, 8)) (inRegion (0, 1)) [] oneByteMem where
  present := by
    intro a ha
    have hzero : a = 0 := Nat.lt_one_iff.mp ha.2
    subst hzero
    exact ⟨0, readByte_writeByte_same [] 0 0⟩
  writes := unchangedOn_writeByte [] 0 0
  within := fun _ h => h
  apart := by
    intro a ha hw
    have h1 : a < 1 := hw.2
    have h2 : 100 ≤ a := ha.1
    exact absurd h1 (Nat.not_lt.mpr (Nat.le_trans (by decide : 1 ≤ 100) h2))

/-! ### `*` as a lemma -/

/-- **`*`.**  Two claims compose into the claim on their unions when the first's
named region is apart from the second's declared writable set — which is what the
presence half needs, since `P` may extend past `W` — and both claims' kept sets are
apart from both declared sets.  The disjointness is an argument, not a connective,
so the lemma adds no proposition former to the records: a caller holding the facts
hands them over.  At the old claim `P` is the written set, so the first hypothesis
is the ticket's "`P` and `Q` disjoint". -/
theorem sep {P K W Q J V : Nat → Prop} {mem m1 m2 : Mem}
    (h1 : Rights P K W mem m1) (h2 : Rights Q J V m1 m2)
    (hpv : Disjoint P V) (hk : Disjoint (fun a => K a ∨ J a) (fun a => W a ∨ V a)) :
    Rights (fun a => P a ∨ Q a) (fun a => K a ∨ J a) (fun a => W a ∨ V a) mem m2 where
  present := by
    intro a ha
    rcases ha with hp | hq
    · obtain ⟨b, hb⟩ := h1.present a hp
      exact ⟨b, by
        rw [h2.writes a (fun hv => hpv a hp hv)]
        exact hb⟩
    · exact h2.present a hq
  writes := by
    intro a ha
    have hfirst : readByte m1 a = readByte mem a :=
      h1.writes a (fun hw1 => ha (Or.inl hw1))
    have hsecond : readByte m2 a = readByte m1 a :=
      h2.writes a (fun hv => ha (Or.inr hv))
    rw [hsecond, hfirst]
  within := fun a ha => by
    rcases ha with hw1 | hv
    · exact Or.inl (h1.within a hw1)
    · exact Or.inr (h2.within a hv)
  apart := hk

/-- **`*` at the old claim**, which this module leaves intact: two owned regions
with no location in common compose into the claim on their union.  Derived from
`sep` at the empty kept set, so the two forms share one algebra rather than two. -/
theorem owns_sep {P Q : Nat → Prop} {mem m1 m2 : Mem}
    (h1 : Owns P mem m1) (h2 : Owns Q m1 m2) (hd : Disjoint P Q) :
    Owns (fun a => P a ∨ Q a) mem m2 :=
  (sep (ofOwns h1) (ofOwns h2) hd
    (fun _ ha _ => ha.elim (fun h => h) (fun h => h))).toOwns

/-! ### The frame rule, derived -/

/-- A region's bytes are the caller's: nothing in it changed. -/
def Keeps (K : Nat → Prop) (mem m : Mem) : Prop :=
  ∀ a, K a → readByte m a = readByte mem a

/-- A sub-region of a kept region is kept: this is what turns one frame clause into
a clause per named region without a second hypothesis. -/
theorem Keeps.sub {K K' : Nat → Prop} {mem m : Mem} (h : Keeps K mem m)
    (hsub : ∀ a, K' a → K a) : Keeps K' mem m :=
  fun a ha => h a (hsub a ha)

/-- **The frame rule.**  A claim's declared writable set is the only region its run
can change, so every region apart from it is kept — the whole region, and each of
its sub-regions by `Keeps.sub`. -/
theorem frame_rule_sep {P K W S : Nat → Prop} {mem m : Mem}
    (h : Rights P K W mem m) (hd : Disjoint W S) : Keeps S mem m :=
  fun a ha => h.writes a (fun hw => hd a hw ha)

/-- **The frame rule, derived from `*`.**  `sep` supplies the composed run's
`UnchangedOn` on the union of the declared sets; a property that depends only on the
complement of that union is preserved, with no per-component frame clause. -/
theorem frame_rule_derived {P K W Q J V : Nat → Prop} {mem m1 m2 : Mem}
    (h1 : Rights P K W mem m1) (h2 : Rights Q J V m1 m2)
    (hpv : Disjoint P V) (hk : Disjoint (fun a => K a ∨ J a) (fun a => W a ∨ V a))
    {R : Mem → Prop} (hR : DependsOutside (fun a => W a ∨ V a) R) :
    R mem ↔ R m2 :=
  hR (sep h1 h2 hpv hk).writes

/-- The `Keeps` form of the same derivation: one region apart from the union of two
claims' declared sets is kept across both. -/
theorem frame_rule_sep_composed {P K W Q J V S : Nat → Prop} {mem m1 m2 : Mem}
    (h1 : Rights P K W mem m1) (h2 : Rights Q J V m1 m2)
    (hpv : Disjoint P V) (hk : Disjoint (fun a => K a ∨ J a) (fun a => W a ∨ V a))
    (hs : Disjoint (fun a => W a ∨ V a) S) : Keeps S mem m2 :=
  fun a ha => (sep h1 h2 hpv hk).writes a (fun h => hs a h ha)

/-- The frame rule of `LeanLLVM/FramePredicate.lean`, recovered from a claim: the
claim's `writes` field is the `UnchangedOn` that rule consumes, so the old rule is a
projection of the new one rather than a second assumption. -/
theorem frame_rule_of_claim {P K W : Nat → Prop} {mem m : Mem}
    (h : Rights P K W mem m) {Q : Mem → Prop} (hQ : DependsOutside W Q) :
    Q mem ↔ Q m :=
  hQ h.writes

/-! ### Ownership: the byte as a resource -/

/-- A claim on one byte's value.  This is the atom the region vocabulary cannot
state: `Rights P K W` says a unit *may* change `W`, while a `PointsTo` claim says a
byte *is* a value, and the value is read out of the memory rather than declared.
Its footprint is the address it names, so a claim's owned set comes from the claim
instead of from an author's region predicate. -/
def PointsTo (a : Nat) (b : UInt8) (mem : Mem) : Prop := readByte mem a = some b

/-- **Value exclusivity, without a hypothesis.**  The memory is a function, so two
claims about one byte are one claim: a second claim at the same address cannot
carry a different value.  Nothing about disjointness is assumed — both claims are
about the same memory, and the read cannot answer twice. -/
theorem pointsTo_exclusive {a : Nat} {v w : UInt8} {mem : Mem}
    (hv : PointsTo a v mem) (hw : PointsTo a w mem) : v = w := by
  unfold PointsTo at hv hw
  rw [hv] at hw
  exact Option.some.inj hw

/-- Two memories share no address: whatever one answers, the other does not.  This
is the disjointness a heap split carries, and it is about the bytes themselves
rather than about a region predicate an author wrote by hand. -/
def MemApart (m1 m2 : Mem) : Prop := ∀ a, readByte m1 a ≠ none → readByte m2 a = none

/-- Two memories answer the same at every address.  Splitting a memory does not fix
a list order: the composed claim is about the bytes, so it names a memory up to
this relation. -/
def Agrees (m1 m2 : Mem) : Prop := ∀ a, readByte m1 a = readByte m2 a

/-- Reading a concatenation is reading the prefix, and falling through to the
suffix when the prefix has nothing at that address. -/
theorem readByte_append (m1 m2 : Mem) (a : Nat) :
    readByte (m1 ++ m2) a =
      (match readByte m1 a with
       | none => readByte m2 a
       | some b => some b) := by
  induction m1 with
  | nil => simp [readByte]
  | cons cell rest ih =>
      obtain ⟨x, y⟩ := cell
      by_cases hx : x = a
      · simp [readByte, hx]
      · simp [readByte, hx, ih]

/-- A byte the prefix answers is the byte the concatenation answers. -/
theorem readByte_append_of_some {m1 m2 : Mem} {a : Nat} {b : UInt8}
    (h : readByte m1 a = some b) : readByte (m1 ++ m2) a = some b := by
  rw [readByte_append, h]

/-- A byte the prefix does not answer is answered by the suffix. -/
theorem readByte_append_of_none {m1 m2 : Mem} {a : Nat}
    (h : readByte m1 a = none) : readByte (m1 ++ m2) a = readByte m2 a := by
  rw [readByte_append, h]

/-- Disjointness is symmetric. -/
theorem MemApart.symm {m1 m2 : Mem} (h : MemApart m1 m2) : MemApart m2 m1 := by
  intro a h2
  by_cases h1 : readByte m1 a = none
  · exact h1
  · exact absurd (h a h1) h2

/-- A split's left part stays apart from the right after a write to a byte the left
part already carried: the write changes a value, not which addresses are read. -/
theorem MemApart.writeByte_left {m1 m2 : Mem} {a : Nat} {b : UInt8}
    (h : MemApart m1 m2) (ha : readByte m1 a ≠ none) :
    MemApart (writeByte m1 a b) m2 := by
  intro x hx
  by_cases hxa : x = a
  · simpa [hxa] using h a ha
  · have hx' : readByte m1 x ≠ none := by
      intro hc
      apply hx
      rw [readByte_writeByte_other m1 b (Ne.symm hxa)]
      exact hc
    exact h x hx'

/-- The left part of a split may stay apart from a concatenated right side. -/
theorem MemApart.append_right {m12 m3 m1 m2 : Mem} (h13 : MemApart m12 m3)
    (h12 : MemApart m1 m2) (hag : Agrees m12 (m1 ++ m2)) :
    MemApart m1 (m2 ++ m3) := by
  intro a ha
  have hm2 : readByte m2 a = none := h12 a ha
  have hm12 : readByte m12 a ≠ none := by
    rw [hag a]
    cases hm : readByte m1 a with
    | none => exact absurd hm ha
    | some b => rw [readByte_append_of_some hm]; intro hc; cases hc
  have hm3 : readByte m3 a = none := h13 a hm12
  rw [readByte_append, hm2, hm3]

/-- The right part of a split is apart from what the left part's side is apart
from, which is how a nested composition's inner split stays a split. -/
theorem MemApart.of_append_left {m12 m3 m1 m2 : Mem} (h13 : MemApart m12 m3)
    (hag : Agrees m12 (m1 ++ m2)) : MemApart m2 m3 := by
  intro a ha
  have h12 : readByte (m1 ++ m2) a ≠ none := by
    cases hm : readByte m1 a with
    | none => rw [readByte_append, hm]; exact ha
    | some b => rw [readByte_append, hm]; intro hc; cases hc
  have hm12 : readByte m12 a ≠ none := by
    rw [hag a]
    exact h12
  exact h13 a hm12

/-- Apartness transfers across an agreeing memory. -/
theorem MemApart.congr_left {m12 m3 n : Mem} (h : MemApart m12 m3) (hag : Agrees m12 n) :
    MemApart n m3 := by
  intro a hn
  have hm12 : readByte m12 a ≠ none := by
    rwa [hag a]
  exact h a hm12

/-- Agreement with itself. -/
theorem Agrees.refl (m : Mem) : Agrees m m := fun _ => rfl

/-- Agreement is symmetric. -/
theorem Agrees.symm {m1 m2 : Mem} (h : Agrees m1 m2) : Agrees m2 m1 := fun a => (h a).symm

/-- Agreement is transitive. -/
theorem Agrees.trans {m1 m2 m3 : Mem} (h1 : Agrees m1 m2) (h2 : Agrees m2 m3) :
    Agrees m1 m3 := fun a => (h1 a).trans (h2 a)

/-- A write to one address reads the same in two agreeing memories: the written
value is the same on both sides, and every other address is the old agreement. -/
theorem Agrees.writeByte {m1 m2 : Mem} (h : Agrees m1 m2) (a : Nat) (b : UInt8) :
    Agrees (writeByte m1 a b) (writeByte m2 a b) := by
  intro x
  by_cases hx : x = a
  · subst hx
    rw [readByte_writeByte_same, readByte_writeByte_same]
  · rw [readByte_writeByte_other m1 b (Ne.symm hx),
        readByte_writeByte_other m2 b (Ne.symm hx)]
    exact h x

/-- Agreement carries into a common suffix. -/
theorem Agrees.append_left {m1 m2 : Mem} (h : Agrees m1 m2) (r : Mem) :
    Agrees (m1 ++ r) (m2 ++ r) := by
  intro a
  rw [readByte_append, readByte_append]
  cases hm : readByte m1 a with
  | none =>
      have hm2 : readByte m2 a = none := by rw [← h a]; exact hm
      rw [hm2]
  | some b =>
      have hm2 : readByte m2 a = some b := by rw [← h a]; exact hm
      rw [hm2]

/-- Reversing two disjoint parts does not change what the union answers, which is
what makes the composition commutative over bytes rather than over lists. -/
theorem agrees_append_swap {m1 m2 : Mem} (h : MemApart m1 m2) :
    Agrees (m1 ++ m2) (m2 ++ m1) := by
  intro a
  rw [readByte_append, readByte_append]
  cases h1 : readByte m1 a with
  | none =>
      cases h2 : readByte m2 a with
      | none => rfl
      | some b => rfl
  | some b =>
      have h2 : readByte m2 a = none := h a (by rw [h1]; intro hc; cases hc)
      rw [h2]

/-- **`*`.**  Two claims on two heaps that share no address compose into the claim
on their union.  The split carries the disjointness as part of the composed claim,
so a composition of two claims that own one address is not a weaker claim: it has
no inhabitant, and no caller is asked to supply a separation before composing. -/
def Star (P Q : Mem → Prop) (mem : Mem) : Prop :=
  ∃ m1 m2, MemApart m1 m2 ∧ P m1 ∧ Q m2 ∧ Agrees mem (m1 ++ m2)

/-- `*` does not care which side is written first. -/
theorem Star.comm {P Q : Mem → Prop} {mem : Mem} (h : Star P Q mem) : Star Q P mem := by
  obtain ⟨m1, m2, hap, hp, hq, hag⟩ := h
  exact ⟨m2, m1, hap.symm, hq, hp, hag.trans (agrees_append_swap hap)⟩

/-- `*` groups.  The split is over bytes, so a nested composition is the flat one. -/
theorem Star.assoc {P Q R : Mem → Prop} {mem : Mem}
    (h : Star (fun m => Star P Q m) R mem) : Star P (fun m => Star Q R m) mem := by
  obtain ⟨m12, m3, hap13, ⟨m1, m2, hap12, hp, hq, hag12⟩, hr, hag⟩ := h
  refine ⟨m1, m2 ++ m3, ?_, hp, ?_, ?_⟩
  · exact MemApart.append_right hap13 hap12 hag12
  · exact ⟨m2, m3, MemApart.of_append_left hap13 hag12, hq, hr, Agrees.refl (m2 ++ m3)⟩
  · have hstep : Agrees (m12 ++ m3) ((m1 ++ m2) ++ m3) := Agrees.append_left hag12 m3
    have hcomp : Agrees mem ((m1 ++ m2) ++ m3) := hag.trans hstep
    rw [List.append_assoc] at hcomp
    exact hcomp

/-- The composition answers with its first part's byte. -/
theorem Star.pointsTo_left {Q : Mem → Prop} {mem : Mem} {a : Nat} {b : UInt8}
    (h : Star (PointsTo a b) Q mem) : PointsTo a b mem := by
  obtain ⟨m1, m2, hap, h1, h2, hag⟩ := h
  unfold PointsTo at h1 ⊢
  rw [hag a]
  exact readByte_append_of_some h1

/-- The composition answers with its second part's byte. -/
theorem Star.pointsTo_right {P : Mem → Prop} {mem : Mem} {a : Nat} {b : UInt8}
    (h : Star P (PointsTo a b) mem) : PointsTo a b mem :=
  h.comm.pointsTo_left

/-- A memory that holds no byte at all: the unit of `*`. -/
def EmptyHeap (mem : Mem) : Prop := ∀ a, readByte mem a = none

/-- A claim on one byte is a composed claim with nothing beside it. -/
theorem pointsTo_star_empty {a : Nat} {b : UInt8} {mem : Mem}
    (h : PointsTo a b mem) : Star (PointsTo a b) EmptyHeap mem := by
  refine ⟨mem, [], ?_, h, ?_, ?_⟩
  · intro x _
    rfl
  · intro x
    rfl
  · rw [List.append_nil]
    exact Agrees.refl mem

/-- The unit law, read at the atom. -/
theorem pointsTo_star_empty_iff {a : Nat} {b : UInt8} {mem : Mem} :
    Star (PointsTo a b) EmptyHeap mem ↔ PointsTo a b mem :=
  ⟨Star.pointsTo_left, pointsTo_star_empty⟩

/-! #### Exclusivity by construction -/

/-- **Two claims on one byte do not compose.**  The composed claim has no
inhabitant at any memory, for any values: each part owns the address, and the
split's parts share no address.  This is the separation `sep` takes as an argument
becoming structure — a record cannot state the composition at all, so there is no
side condition to forget. -/
theorem star_pointsTo_uninhabited (a : Nat) (v w : UInt8) (mem : Mem) :
    ¬ Star (PointsTo a v) (PointsTo a w) mem := by
  rintro ⟨m1, m2, hap, h1, h2, -⟩
  unfold PointsTo at h1 h2
  have h1' : readByte m1 a ≠ none := by rw [h1]; intro hc; cases hc
  have h2' : readByte m2 a = none := hap a h1'
  rw [h2'] at h2
  cases h2

/-- The exclusivity law of the atom: `x ↦ v * x ↦ w` gives `v = w`.  Its content
here is the theorem above — the composed claim is uninhabited, so the equality is
not a premise anyone supplies.  The non-vacuous reading of the same fact is
`pointsTo_exclusive`, which needs no composition: two claims about one memory's
byte cannot disagree. -/
theorem star_pointsTo_agree {a : Nat} {v w : UInt8} {mem : Mem}
    (h : Star (PointsTo a v) (PointsTo a w) mem) : v = w :=
  absurd h (star_pointsTo_uninhabited a v w mem)

/-- Two singleton heaps with different addresses are apart. -/
theorem memApart_singleton {a c : Nat} {v w : UInt8} (h : a ≠ c) :
    MemApart [(a, v)] [(c, w)] := by
  intro x hx
  by_cases hxa : x = a
  · have hcx : ¬ (c = x) := fun hc => h (hxa.symm.trans hc.symm)
    simp [readByte, hcx]
  · have hnone : readByte [(a, v)] x = none := by
      simp [readByte, Ne.symm hxa]
    exact absurd hnone hx

/-- The control for the two theorems above: at two addresses the same composition
is inhabited, so the refutation is the shared address and not the shape of `*`. -/
theorem star_pointsTo_apart_inhabited (a c : Nat) (v w : UInt8) (h : a ≠ c) :
    Star (PointsTo a v) (PointsTo c w) [(a, v), (c, w)] := by
  refine ⟨[(a, v)], [(c, w)], memApart_singleton h, ?_, ?_, ?_⟩
  · simp [PointsTo, readByte]
  · simp [PointsTo, readByte]
  · exact Agrees.refl _

/-! #### Ownership as a set of bytes -/

/-- A claim that a memory carries every byte of `W`, naming no value and saying
nothing about the rest.  `PointsTo` is this plus a value, and `present` is this at
one address: the difference is that `W` is the claim's own footprint. -/
def Carries (W : Nat → Prop) (mem : Mem) : Prop := ∀ a, W a → readByte mem a ≠ none

/-- A points-to claim carries the address it names. -/
theorem PointsTo.carries {a : Nat} {b : UInt8} {mem : Mem} (h : PointsTo a b mem) :
    Carries (fun x => x = a) mem := by
  intro x hx
  subst hx
  unfold PointsTo at h
  rw [h]
  intro hc
  cases hc

/-- A points-to claim is a present byte, in the presence vocabulary. -/
theorem PointsTo.present {a : Nat} {b : UInt8} {mem : Mem} (h : PointsTo a b mem) :
    present mem a :=
  ⟨b, h⟩

/-- A carried set is present. -/
theorem Carries.present {W : Nat → Prop} {mem : Mem} (h : Carries W mem) :
    ∀ a, W a → present mem a := by
  intro a ha
  cases hm : readByte mem a with
  | none => exact absurd hm (h a ha)
  | some b => exact ⟨b, hm⟩

/-- **Exclusivity derived, not assumed.**  Two composed ownership claims are
disjoint: each set's bytes are read out of its own part of the split, and the parts
share no address.  The disjointness is a consequence of `*`, so a record states the
claims and reads the separation off them. -/
theorem star_carries_disjoint {W V : Nat → Prop} {mem : Mem}
    (h : Star (Carries W) (Carries V) mem) : Disjoint W V := by
  obtain ⟨m1, m2, hap, h1, h2, -⟩ := h
  intro a hw hv
  exact absurd (hap a (h1 a hw)) (h2 a hv)

/-- **`Carries W * Carries W` has no inhabitant** where `W` names a byte: each part
would have to own that byte.  Aliasing is impossible rather than excluded. -/
theorem star_carries_self_uninhabited {W : Nat → Prop} {mem : Mem} {a : Nat}
    (ha : W a) : ¬ Star (Carries W) (Carries W) mem :=
  fun h => star_carries_disjoint h a ha ha

/-- The control: at two different sets the composition is inhabited, so the
refutation above is the shared byte. -/
theorem star_carries_inhabited :
    Star (Carries (fun a => a = 0)) (Carries (fun a => a = 1)) [(0, 1), (1, 2)] := by
  refine ⟨[(0, 1)], [(1, 2)], memApart_singleton (by decide), ?_, ?_, ?_⟩
  · intro x hx
    subst hx
    simp [readByte]
  · intro x hx
    subst hx
    simp [readByte]
  · exact Agrees.refl _

/-- The composition carries a set its part carried. -/
theorem Star.carries_left {W : Nat → Prop} {Q : Mem → Prop} {mem : Mem}
    (h : Star (Carries W) Q mem) : Carries W mem := by
  obtain ⟨m1, m2, hap, h1, h2, hag⟩ := h
  intro a ha
  have hx : readByte m1 a ≠ none := h1 a ha
  rw [hag a, readByte_append]
  cases hm : readByte m1 a with
  | none => exact absurd hm hx
  | some b => intro hc; cases hc

/-! #### Write rules -/

/-- **A write at a byte is that byte's claim.**  The store is what puts the bytes
there, so the claim does not need the old one; what the old claim buys is the rest
of the composition (`star_pointsTo_write`). -/
theorem pointsTo_writeByte (mem : Mem) (a : Nat) (b : UInt8) :
    PointsTo a b (writeByte mem a b) :=
  readByte_writeByte_same mem a b

/-- A write at another address leaves the claim: the atom's frame. -/
theorem PointsTo.writeByte {a : Nat} {b : UInt8} {mem : Mem} (c : Nat) (v : UInt8)
    (hne : c ≠ a) (h : PointsTo a b mem) : PointsTo a b (writeByte mem c v) := by
  unfold PointsTo at h ⊢
  rw [readByte_writeByte_other mem v hne]
  exact h

/-- **A write at an unowned byte is not a claim about that byte.**  These two
memories carry the same claim at address zero and disagree at address five, so no
rule reads five out of a claim that does not name it.  What happens instead: the
store makes a *fresh* claim at the written byte on the new memory
(`pointsTo_writeByte`), the old claim's own bytes are unchanged (`PointsTo.writeByte`),
and the composed claim's footprint excludes the write — there is no update of a
claim to a byte it did not own. -/
theorem unowned_byte_not_claimed :
    ∃ (mem₁ mem₂ : Mem), PointsTo 0 1 mem₁ ∧ PointsTo 0 1 mem₂ ∧
      readByte mem₁ 5 ≠ readByte mem₂ 5 := by
  refine ⟨[(0, 1)], [(0, 1), (5, 2)], ?_, ?_, ?_⟩
  · simp [PointsTo, readByte]
  · simp [PointsTo, readByte]
  · decide

/-- Writing inside the first part of a composition leaves the second part alone. -/
theorem star_writeByte_outside {Q : Mem → Prop} {mem : Mem} {a : Nat} {b : UInt8}
    (h : Star (PointsTo a b) Q mem) (c : Nat) {v : UInt8} (hne : c ≠ a) :
    readByte (writeByte mem c v) a = some b :=
  h.pointsTo_left.writeByte c v hne

/-- A write inside the first part is a write inside the prefix of the split, so the
split survives it: the write substitutes the prefix's cell and leaves the suffix
where it was. -/
theorem writeByte_append_left {m1 m2 : Mem} {a : Nat} {b : UInt8}
    (ha : readByte m1 a ≠ none) :
    writeByte (m1 ++ m2) a b = writeByte m1 a b ++ m2 := by
  induction m1 with
  | nil => exact absurd rfl ha
  | cons cell rest ih =>
      obtain ⟨x, y⟩ := cell
      by_cases hx : x = a
      · subst hx
        simp [writeByte]
      · have ha' : readByte rest a ≠ none := by
          intro hc
          apply ha
          simp [readByte, hx, hc]
        simp [writeByte, hx, ih ha']

/-- **The frame rule from the resource.**  A write at a byte the first part owns
updates that claim and leaves the composition otherwise the same: the second claim
is still the same claim about the same bytes.  Nothing is assumed about the memory
as a whole, which is what makes this a rule of the claim rather than a property the
caller supplies. -/
theorem star_pointsTo_write {Q : Mem → Prop} {mem : Mem} {a : Nat} {b b' : UInt8}
    (h : Star (PointsTo a b) Q mem) :
    Star (PointsTo a b') Q (writeByte mem a b') := by
  obtain ⟨m1, m2, hap, h1, h2, hag⟩ := h
  unfold PointsTo at h1
  have hown : readByte m1 a ≠ none := by rw [h1]; intro hc; cases hc
  refine ⟨writeByte m1 a b', m2, hap.writeByte_left hown, ?_, h2, ?_⟩
  · exact readByte_writeByte_same m1 a b'
  · have hstep : Agrees (writeByte mem a b') (writeByte (m1 ++ m2) a b') :=
      hag.writeByte a b'
    rw [writeByte_append_left hown] at hstep
    exact hstep

/-- A write is a change at one address only: the `UnchangedOn` every frame rule in
this module already consumes. -/
theorem pointsTo_write_unchangedOn (mem : Mem) (a : Nat) (b : UInt8) :
    UnchangedOn (fun x => x = a) mem (writeByte mem a b) := by
  intro x hx
  exact readByte_writeByte_other mem b (fun hc : a = x => hx hc.symm)

/-- **The old frame rule, recovered as a projection.**  The write's resource effect
is the `UnchangedOn` the property-based rule takes as its hypothesis, so the rule
that predates this vocabulary is this one read at `DependsOutside`; nothing that
consumed the property form regresses.  `frame_rule_of_claim` and `frame_rule_sep`
are the same projection at a `Rights` claim's own writable set. -/
theorem frame_rule_of_write (mem : Mem) (a : Nat) (b : UInt8) {R : Mem → Prop}
    (hR : DependsOutside (fun x => x = a) R) :
    R mem ↔ R (writeByte mem a b) :=
  frame_rule (pointsTo_write_unchangedOn mem a b) hR

/-! ### The historical defect, in this vocabulary -/

/-- The extent the decoder writes through `dst`: the decoded prefix plus the
sixty-four bytes the stored form reaches.  `DecodeNoAlias` writes this window as
`dst + n + 64 ≤ tab` on the far side of its disjunction. -/
def destinationWindow (n dst : Nat) : Nat → Prop := inRegion (dst, n + 64)

/-- The offset slot the caller keeps: `err`'s eight bytes, which the post reads back
as the caller's value. -/
def offsetSlot (err : Nat) : Nat → Prop := inRegion (err, 8)

/-- The cursor slot the run's trailing store writes: `xj`'s eight bytes. -/
def cursorSlot (xj : Nat) : Nat → Prop := inRegion (xj, 8)

/-- The table entry the decoder's emitter reads while the raw copy is writing:
`tab`'s 256 bytes. -/
def tableWindow (tab : Nat) : Nat → Prop := inRegion (tab, 256)

/-- The decoder's claim as the record states it: it writes the destination window
and the cursor slot, and it keeps the offset slot it reads back and the table entry
its emitter reads. -/
def decodeClaim (n dst xj err tab : Nat) (mem m : Mem) : Prop :=
  Rights (fun a => destinationWindow n dst a ∨ cursorSlot xj a)
    (fun a => offsetSlot err a ∨ tableWindow tab a)
    (fun a => destinationWindow n dst a ∨ cursorSlot xj a) mem m

/-- **Three of the record's four clauses are readings of one field.**  `apart` holds
with the kept set on one side and the writable set on the other, so `tab`/`dst`,
`err`/`dst` and `err`/`xj` are the three readings it has at the record's regions.
The consumer names the two sets once.  The fourth, `xj`/`dst`, is a hypothesis: both
regions are written by the run, so no field of the claim can separate them. -/
theorem decodeClaim_yields_four {n dst xj err tab : Nat} {mem m : Mem}
    (h : decodeClaim n dst xj err tab mem m)
    (hfourth : Disjoint (cursorSlot xj) (destinationWindow n dst)) :
    Disjoint (tableWindow tab) (destinationWindow n dst) ∧
      Disjoint (offsetSlot err) (destinationWindow n dst) ∧
      Disjoint (offsetSlot err) (cursorSlot xj) ∧
      Disjoint (cursorSlot xj) (destinationWindow n dst) :=
  ⟨fun a hk hw => h.apart a (Or.inr hk) (Or.inl hw),
   fun a hk hw => h.apart a (Or.inl hk) (Or.inl hw),
   fun a hk hw => h.apart a (Or.inl hk) (Or.inr hw),
   hfourth⟩

/-- **The historical `tab`/`dst` aliasing is unstatable as a claim.**  The raw copy's
sixty-four-byte write reaches the table entry the emitter reads — the row
`DecodeNoAlias` records as executed — and the record's claim keeps that entry and
writes that window.  `apart` is refuted at the entry's base for every memory: the
aliased staging is not a weaker claim here, it is no claim, so the clause cannot be
dropped the way one conjunct of four can. -/
theorem decodeTableInsideWindow_unstatable (n dst xj err tab : Nat) (mem m : Mem)
    (hlo : dst ≤ tab) (hhi : tab < dst + (n + 64)) :
    ¬ decodeClaim n dst xj err tab mem m :=
  rights_apart_unstatable
    (Or.inr ⟨Nat.le_refl tab, Nat.lt_add_of_pos_right (by decide : 0 < 256)⟩)
    (Or.inl ⟨hlo, hhi⟩)

/-- **The historical `err`/`xj` aliasing is unstatable as a claim**, the other
executed row: the trailing cursor store leaves `1` where the post reads the caller's
`0`.  At a staging where the two are one slot, the kept set and the writable set meet
on all eight bytes, so no claim of the record's shape exists. -/
theorem decodeCursorOverOffset_unstatable (n dst xj err tab : Nat) (mem m : Mem)
    (h : xj = err) : ¬ decodeClaim n dst xj err tab mem m := by
  subst h
  exact rights_apart_unstatable (a := xj)
    (Or.inl ⟨Nat.le_refl xj, Nat.lt_add_of_pos_right (by decide : 0 < 8)⟩)
    (Or.inr ⟨Nat.le_refl xj, Nat.lt_add_of_pos_right (by decide : 0 < 8)⟩)

/-- **The `xj`/`dst` aliasing refutes `sep`'s hypothesis**, and that is the whole of
its exclusion: at overlapping numbers the cursor slot is not apart from the
destination window, so no composition of the run's two writers exists there. -/
theorem cursorInsideWindow_notSep (n dst xj : Nat) (hlo : dst ≤ xj)
    (hhi : xj < dst + (n + 64)) :
    ¬ Disjoint (cursorSlot xj) (destinationWindow n dst) :=
  fun hd => hd xj ⟨Nat.le_refl xj, Nat.lt_add_of_pos_right (by decide : 0 < 8)⟩
    ⟨hlo, hhi⟩

/-- The control for `cursorInsideWindow_notSep`: at separated numbers the same
`Disjoint` is inhabited, so the refutation above is the aliasing and not the shape
of the fourth clause.  Together with `cursorWindowNotDerived` it fixes the pair's
status — statable at a separated staging, and not implied by the claims. -/
theorem cursorWindowSep_inhabited :
    Disjoint (cursorSlot 1000) (destinationWindow 0 0) := by
  intro a ha hw
  have h1 : a < 64 := hw.2
  have h2 : 1000 ≤ a := ha.1
  exact absurd h1 (Nat.not_lt.mpr (Nat.le_trans (by decide : 64 ≤ 1000) h2))

/-! #### Presence for the control

The two unstatability theorems above need a control, or "no claim exists" could be
true of the shape rather than of the aliasing.  These lemmas build a memory whose
window is present, so the claim is exhibited at a staging the record admits. -/

/-- A location of a present range is present. -/
theorem present_of_hasBytes {mem : Mem} {start k a : Nat} (h : HasBytes mem start k)
    (ha : inRegion (start, k) a) : present mem a := by
  have hk : a - start < k := by
    have h1 : start + (a - start) < start + k := by
      rw [Nat.add_sub_of_le ha.1]
      exact ha.2
    exact Nat.lt_of_add_lt_add_left h1
  have hp := h (a - start) hk
  rwa [Nat.add_sub_of_le ha.1] at hp

/-- The bytes a write sequence wrote are present afterwards, whatever memory it
started from. -/
theorem hasBytes_writeBytes_self : ∀ (mem : Mem) (bs : List UInt8) (start : Nat),
    HasBytes (writeBytes mem start bs) start bs.length
  | _, [], _ => by
      intro k hk
      exact absurd hk (Nat.not_lt_zero k)
  | mem, c :: cs, start => by
      intro k hk
      cases k with
      | zero =>
          exact present_writeBytes (writeByte mem start c) (start + 1) cs
            ⟨c, readByte_writeByte_same mem start c⟩
      | succ j =>
          have hj : j < cs.length := Nat.lt_of_succ_lt_succ hk
          have hp := hasBytes_writeBytes_self (writeByte mem start c) cs (start + 1) j hj
          rw [Nat.add_assoc, Nat.add_comm 1 j] at hp
          exact hp

/-- A memory with `k` bytes from `start`. -/
def filled (start k : Nat) : Mem := writeBytes [] start (List.replicate k 0)

/-- The bytes of a filled range are present. -/
theorem hasBytes_filled (start k : Nat) : HasBytes (filled start k) start k := by
  have h := hasBytes_writeBytes_self [] (List.replicate k 0) start
  simpa [filled, List.length_replicate] using h

/-- The staging memory of the control: the cursor slot's eight bytes, then the
destination window's sixty-four. -/
def decodeStagingMem : Mem := writeBytes (filled 1000 8) 0 (List.replicate 64 0)

/-- **The control for the two unstatability theorems.**  At a staging the record
admits — the cursor slot and the destination window apart from the offset slot and
the table entry, all four present — the claim is inhabited.  So the refutations are
the aliasings and not the claim's shape. -/
theorem decodeClaim_staging_inhabited :
    decodeClaim 0 0 1000 2000 3000 decodeStagingMem decodeStagingMem := by
  have hwin : HasBytes decodeStagingMem 0 64 := by
    have h := hasBytes_writeBytes_self (filled 1000 8) (List.replicate 64 0) 0
    simpa [decodeStagingMem, List.length_replicate] using h
  have hcur : HasBytes decodeStagingMem 1000 8 :=
    HasBytes.writeBytes (hasBytes_filled 1000 8) 0 (List.replicate 64 0)
  unfold decodeClaim
  refine ⟨?_, UnchangedOn.refl _ _, fun _ h => h, ?_⟩
  · intro a ha
    rcases ha with hd | hc
    · exact present_of_hasBytes hwin hd
    · exact present_of_hasBytes hcur hc
  · intro a ha hw
    rcases ha with he | ht <;> rcases hw with hd | hc
    · exact absurd (Nat.lt_of_lt_of_le hd.2 (by decide : 64 ≤ 2000))
        (Nat.not_lt.mpr he.1)
    · exact absurd (Nat.lt_of_lt_of_le hc.2 (by decide : 1008 ≤ 2000))
        (Nat.not_lt.mpr he.1)
    · exact absurd (Nat.lt_of_lt_of_le hd.2 (by decide : 64 ≤ 3000))
        (Nat.not_lt.mpr ht.1)
    · exact absurd (Nat.lt_of_lt_of_le hc.2 (by decide : 1008 ≤ 3000))
        (Nat.not_lt.mpr ht.1)

/-! #### The fourth clause is not derived -/

/-- **The `xj`/`dst` pair is a hypothesis, not a consequence.**  Two claims whose
declared writable sets are the same location are both inhabited — a write followed
by another write — so nothing about the claims implies the separation `sep` asks
for.  The pair stays a `Disjoint` the consumer writes, which is why three of the
four clauses are derived and the fourth is restated. -/
theorem cursorWindowNotDerived :
    ∃ (mem m1 m2 : Mem) (P Q : Nat → Prop),
      Rights P emptyRegion P mem m1 ∧ Rights Q emptyRegion Q m1 m2 ∧ ¬ Disjoint P Q := by
  refine ⟨[], writeByte [] 0 1, writeByte (writeByte [] 0 1) 0 2,
    inRegion (0, 1), inRegion (0, 1), ?_, ?_, ?_⟩
  · refine ⟨?_, unchangedOn_writeByte [] 0 1, fun _ h => h, fun _ hk _ => hk⟩
    intro a ha
    have hzero : a = 0 := Nat.lt_one_iff.mp ha.2
    subst hzero
    exact ⟨1, readByte_writeByte_same [] 0 1⟩
  · refine ⟨?_, unchangedOn_writeByte (writeByte [] 0 1) 0 2, fun _ h => h,
      fun _ hk _ => hk⟩
    intro a ha
    have hzero : a = 0 := Nat.lt_one_iff.mp ha.2
    subst hzero
    exact ⟨2, readByte_writeByte_same (writeByte [] 0 1) 0 2⟩
  · intro hd
    exact hd 0 ⟨Nat.le_refl 0, Nat.lt_add_of_pos_right (by decide : 0 < 1)⟩
      ⟨Nat.le_refl 0, Nat.lt_add_of_pos_right (by decide : 0 < 1)⟩

/-! #### Ownership does not separate the run's own writers -/

/-- **A run owns both regions it writes, even where they meet.**  The claim over
the union of the destination window and the cursor slot is inhabited at a staging
where the cursor lies inside the window: ownership is a claim about a byte's value,
and a byte written twice by the same run is one byte holding the second value.  So
nothing in the ownership algebra forces `xj` apart from `dst`. -/
theorem runOwned_meeting_regions_inhabited (n dst xj : Nat)
    (hhi : xj < dst + (n + 64)) :
    ∃ mem : Mem, Carries (fun a => destinationWindow n dst a ∨ cursorSlot xj a) mem := by
  refine ⟨filled 0 (dst + (n + 64) + 8), ?_⟩
  intro a ha
  have hbytes : HasBytes (filled 0 (dst + (n + 64) + 8)) 0 (dst + (n + 64) + 8) :=
    hasBytes_filled 0 (dst + (n + 64) + 8)
  have ha' : a < dst + (n + 64) + 8 := by
    rcases ha with hd | hc
    · exact Nat.lt_trans hd.2 (Nat.lt_add_of_pos_right (by decide : 0 < 8))
    · exact Nat.lt_trans hc.2 (Nat.add_lt_add_right hhi 8)
  obtain ⟨b, hb⟩ := hbytes a ha'
  rw [Nat.zero_add] at hb
  intro hc
  rw [hb] at hc
  cases hc

/-- **The two claims do not compose as `*` where the regions meet**, and that
refusal is not a separation: `*` refuses the composition of a claim with itself as
well (`star_carries_self_uninhabited`).  So `xj`/`dst` stays a staging hypothesis —
the pair is not derived by the region vocabulary (`cursorWindowNotDerived`) and is
not derived by ownership either. -/
theorem cursorWindow_carries_notStar (n dst xj : Nat) (hlo : dst ≤ xj)
    (hhi : xj < dst + (n + 64)) (mem : Mem) :
    ¬ Star (Carries (cursorSlot xj)) (Carries (destinationWindow n dst)) mem :=
  fun h => cursorInsideWindow_notSep n dst xj hlo hhi (star_carries_disjoint h)

/-! ### Axiom footprints

Every declaration above reports its footprint.  The expected ceiling is
`[propext, Quot.sound]`; a `Classical.choice` would name a carrier this vocabulary
does not need. -/

#print axioms Disjoint
#print axioms Disjoint.sub_left
#print axioms Disjoint.sub_right
#print axioms Disjoint.symm
#print axioms emptyRegion
#print axioms Rights
#print axioms rights_writable_present
#print axioms Rights.kept
#print axioms Rights.toOwns
#print axioms ofOwns
#print axioms rights_empty_iff_owns
#print axioms not_rights_of_changed_outside
#print axioms rights_apart_unstatable
#print axioms unchangedOn_writeByte
#print axioms oneByteMem
#print axioms rights_apart_inhabited
#print axioms sep
#print axioms owns_sep
#print axioms Keeps
#print axioms Keeps.sub
#print axioms frame_rule_sep
#print axioms frame_rule_derived
#print axioms frame_rule_sep_composed
#print axioms frame_rule_of_claim
#print axioms PointsTo
#print axioms pointsTo_exclusive
#print axioms MemApart
#print axioms Agrees
#print axioms MemApart.symm
#print axioms MemApart.writeByte_left
#print axioms MemApart.append_right
#print axioms MemApart.of_append_left
#print axioms MemApart.congr_left
#print axioms Agrees.refl
#print axioms Agrees.symm
#print axioms Agrees.trans
#print axioms Agrees.writeByte
#print axioms Agrees.append_left
#print axioms readByte_append
#print axioms readByte_append_of_some
#print axioms readByte_append_of_none
#print axioms agrees_append_swap
#print axioms Star
#print axioms Star.comm
#print axioms Star.assoc
#print axioms Star.pointsTo_left
#print axioms Star.pointsTo_right
#print axioms EmptyHeap
#print axioms pointsTo_star_empty
#print axioms pointsTo_star_empty_iff
#print axioms star_pointsTo_uninhabited
#print axioms star_pointsTo_agree
#print axioms star_pointsTo_apart_inhabited
#print axioms memApart_singleton
#print axioms Carries
#print axioms PointsTo.carries
#print axioms PointsTo.present
#print axioms Carries.present
#print axioms star_carries_disjoint
#print axioms star_carries_self_uninhabited
#print axioms star_carries_inhabited
#print axioms Star.carries_left
#print axioms pointsTo_writeByte
#print axioms PointsTo.writeByte
#print axioms unowned_byte_not_claimed
#print axioms star_writeByte_outside
#print axioms writeByte_append_left
#print axioms star_pointsTo_write
#print axioms pointsTo_write_unchangedOn
#print axioms frame_rule_of_write
#print axioms destinationWindow
#print axioms offsetSlot
#print axioms cursorSlot
#print axioms tableWindow
#print axioms decodeClaim
#print axioms decodeClaim_yields_four
#print axioms decodeTableInsideWindow_unstatable
#print axioms decodeCursorOverOffset_unstatable
#print axioms cursorInsideWindow_notSep
#print axioms cursorWindowSep_inhabited
#print axioms present_of_hasBytes
#print axioms hasBytes_writeBytes_self
#print axioms filled
#print axioms hasBytes_filled
#print axioms decodeStagingMem
#print axioms decodeClaim_staging_inhabited
#print axioms cursorWindowNotDerived
#print axioms runOwned_meeting_regions_inhabited
#print axioms cursorWindow_carries_notStar

end LeanLLVM
