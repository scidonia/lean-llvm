/-
Rights on the region claim, stated beside it.

`LeanLLVM/FramePredicate.lean` states the region claim `Owns P` as two facts about
one predicate: nothing outside `P` changes, and every location of `P` is present.
One predicate for both questions is why `LeanLLVM/Vellum/JsonEscapeDecodeRun.lean`
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

end LeanLLVM
