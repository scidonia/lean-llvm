/-
The tier-2 bridge: the body's `num_el_el1` model and the guard's decision.

`JsonStage2NumFastCalls` supplies `numElEl1` — the callee's model, with the
`EPOW` table as a parameter — while `LeanLLVM.ElGuardRefine.elTier2Code` is the
guard's own decision over the emitted table, and `elGuardRefinesOn` proves that
decision is `roundMag`'s on sixty-four-bit mantissas.  This module closes the
correspondence between the two *models*: the same C text, written twice in two
namespaces (`LeanLLVM.Refinement.EPow` here, `LeanLLVM.ElGuardRefine.EPow`
there), now related on the kernel's domain.

**The model's low-word wrap.**  Reading the correspondence first found a defect
in the model, not only a missing lemma.  `el_exact`'s two additions are
`uint64_t` in the emitted code: `Rlo = Alo + c` wraps and the carry is
`Rlo < Alo` on the wrapped word, and `Rhi` carries it into another sixty-four-bit
word.  The model's `Rlo`/`Rhi` were *unreduced* naturals.  At
`(w, q) = (34, -36)` — one of `ElGuardRefine.witnesses`, the very inputs the
guard's check prints — the unwrapped sum is `18870555535664931523 ≥ 2 ^ 64`, the
unwrapped reading sees `hp = 511 = hh - 1` and rounds down, and the emitted
kernel (and `elTier2Code`) sees `hp = 512 = hh` and rounds up: `…961` against
`…962`.  `JsonStage2NumFastCalls.elExact` now reduces both words modulo
`2 ^ 64`, which is what the C does and what `elTier2Code` computes.

**The bridge, and its domain.**  `guardTable` is the body's table taken from the
guard's rows, and `NumFastElAgrees` says that on every mantissa and exponent the
model's decision is the guard's encoding bits.  The mantissa is the kernel's
`uint64_t` parameter, so the statement carries the same `w < 2 ^ 64` bound as
`ElGuardRefinesOn`.  The bound is not a proof convenience: above it the guard's
in-window test wraps the `2 ^ 64`-wide subtraction of `inWindow`, while the model
tests the three-value window directly, and the two decisions separate at
`(w, q) = (43 · 2 ^ 64, -45)`.  `NumFastElUnbounded` is that false statement and
`not_numFastElUnbounded` records the witness: the model gives `…4512`, the guard
`…0823`.  Within `w < 2 ^ 64` the bridge is `numFastElAgrees`, proved below.

The proof runs on the common normalisation: `64 - Nat.size w = 63 - Nat.log2 w`
(`lz_shift`), the table's rows are below `2 ^ 64` (`epowAt_hi_lt`, a
`decide`-checked sweep of the ninety-one rows), so the product's high word is
below `2 ^ 64` and `ub ∈ {0, 1}`; there `inWindow_iff` turns the emitted wrapped
test into the model's three-value window (`window_equiv`).  The two arms then
coincide through `elExact_bits` and `elPack_bits`, which also carry the encoding
(`codeBits`) across `elPack`.

**Axiom footprints** are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.ElGuardRefine

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement

/-! ### The two tables

The body's `EPow` and the guard's are the same three fields under different
namespaces; `ofGuard` carries a guard row to the model's type, and `guardTable`
is the model's table read from the guard's own rows. -/

/-- A guard row as the model's row. -/
def EPow.ofGuard (t : LeanLLVM.ElGuardRefine.EPow) : EPow :=
  ⟨t.hi, t.lo, t.e⟩

/-- The body's table, taken from the guard's rows. -/
def guardTable : Int → Option EPow :=
  fun q => (LeanLLVM.ElGuardRefine.epowAt q).map EPow.ofGuard

/-- The encoding's bits, as the emitted kernel's `out_u64` carries them. -/
abbrev tier2Bits (c : LeanLLVM.Code) : Nat :=
  LeanLLVM.ElGuardRefine.codeBits c

/-! ### The bridge

The obligation: everywhere the model decides, its word is the guard's encoding.
The statement is the guard's own domain — the emitted kernel's `uint64_t`
mantissa, as `ElGuardRefinesOn` states it. -/

/-- **The tier-2 bridge.**  On every sixty-four-bit mantissa `w` and exponent
`q`, the model's decision is the guard's encoding bits. -/
def NumFastElAgrees : Prop :=
  ∀ (w : Nat) (q : Int), w < 2 ^ 64 →
    numElEl1 guardTable w q = (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits

/-! ### Sharing the model's arithmetic

The model and the guard compute the same `W = w << lz`; `Nat.size w` and
`Nat.log2 w` differ by one on nonzero `w`, which is `lz_shift`.  Everything after
that is the same arithmetic in both texts. -/

/-- `w`'s bit length is one more than its binary logarithm. -/
theorem size_eq_log2_add_one {w : Nat} (h : w ≠ 0) : Nat.size w = Nat.log2 w + 1 := by
  have hb := (Nat.log2_eq_iff h).mp rfl
  have h1 : Nat.log2 w < Nat.size w := Nat.lt_size.mpr hb.1
  have h2 : Nat.size w ≤ Nat.log2 w + 1 := Nat.size_le.mpr hb.2
  omega

/-- The model's normalising shift is the guard's: `64 - size` is `63 - log2`. -/
theorem lz_shift (w : Nat) (h : w ≠ 0) : 64 - Nat.size w = 63 - Nat.log2 w := by
  have hs := size_eq_log2_add_one h
  omega

/-- The normalised word is below `2 ^ 64` for a sixty-four-bit mantissa. -/
theorem wnorm_lt (w : Nat) (h : w < 2 ^ 64) (h0 : w ≠ 0) :
    w * 2 ^ (64 - Nat.size w) < 2 ^ 64 := by
  have hb := (Nat.log2_eq_iff h0).mp rfl
  have hs := size_eq_log2_add_one h0
  have hsle : Nat.size w ≤ 64 := Nat.size_le.mpr h
  calc w * 2 ^ (64 - Nat.size w)
      < 2 ^ (Nat.log2 w + 1) * 2 ^ (64 - Nat.size w) :=
        Nat.mul_lt_mul_of_pos_right hb.2 (Nat.pow_pos (by decide))
    _ = 2 ^ (Nat.log2 w + 1 + (64 - Nat.size w)) := by rw [← Nat.pow_add]
    _ = 2 ^ 64 := by rw [hs]; congr 1; omega

/-! ### The table's rows are sixty-four-bit

`epowAt` indexes the ninety-one-row emitted table.  A `decide`-checked sweep of
`epow.toList` gives every row's `hi` below `2 ^ 64`, and `Array.getElem?_eq_some_iff`
carries that bound to the row `epowAt` returns. -/

/-- Every table row's `hi` is a sixty-four-bit word. -/
theorem epowAt_hi_lt (q : Int) (t : LeanLLVM.ElGuardRefine.EPow)
    (h : LeanLLVM.ElGuardRefine.epowAt q = some t) : t.hi < 2 ^ 64 := by
  have hall : LeanLLVM.ElGuardRefine.epow.toList.all (fun r => r.hi < 2 ^ 64) = true := by
    decide
  unfold LeanLLVM.ElGuardRefine.epowAt at h
  split at h
  · rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨hi, rfl⟩ := h
    have hmem : LeanLLVM.ElGuardRefine.epow[(q + 45).toNat] ∈
        LeanLLVM.ElGuardRefine.epow.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    have hrow := (List.all_eq_true.mp hall) _ hmem
    simpa using hrow
  · simp at h

/-- Inside the range gate the table has a row. -/
theorem epowAt_some_of_range {q : Int} (h : -45 ≤ q ∧ q ≤ 45) :
    ∃ t, LeanLLVM.ElGuardRefine.epowAt q = some t := by
  refine ⟨LeanLLVM.ElGuardRefine.epow[(q + 45).toNat]'(by
    show (q + 45).toNat < LeanLLVM.ElGuardRefine.epow.size
    show (q + 45).toNat < 91
    omega), ?_⟩
  unfold LeanLLVM.ElGuardRefine.epowAt
  rw [ite_eq_left h]
  exact Array.getElem?_eq_getElem _

/-! ### `Option.map` through a branch

`elTier2Code` returns an `Option Code` whose branches `Option.map codeBits`
must cross; this is the one shape needed. -/

/-- `Option.map` distributes over a propositional branch. -/
theorem Omap_ite {α β : Type} (f : α → β) (P : Prop) [Decidable P] (a b : Option α) :
    Option.map f (if P then a else b) = if P then Option.map f a else Option.map f b := by
  by_cases h : P <;> simp [h]

/-! ### `el_pack`, with and without the encoding

The model's `elPack` returns the eight-byte integer; the guard's builds the
`Code` and `codeBits` spells that integer.  The two range gates are complements
over `Int`. -/

/-- The model's `elPack` is the guard's encoding. -/
theorem elPack_bits (m up ub : Nat) (t : EPow) (lz : Nat) :
    elPack m up ub t lz =
      (LeanLLVM.ElGuardRefine.elPack
        { m := m, up := up, ub := ub, e := t.e, lz := lz }).map
        LeanLLVM.ElGuardRefine.codeBits := by
  unfold elPack LeanLLVM.ElGuardRefine.elPack LeanLLVM.ElGuardRefine.codeBits
  by_cases h : -1022 ≤ 180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) ∧
      180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) ≤ 1023
  · have hnot : ¬ (180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) > 1023 ∨
        180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) < -1022) := by omega
    rw [ite_eq_right hnot, ite_eq_left h]
    simp only [Option.map]
    have hne : (180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) + 1023).toNat ≠ 0 := by
      omega
    simp only [hne, ite_false, Nat.add_sub_cancel_left]
  · have hnot : 180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) > 1023 ∨
        180 + ((10 + ub + (m + up) / 2 ^ 53 : Nat) : Int) + t.e - (lz : Int) < -1022 := by omega
    rw [ite_eq_left hnot, ite_eq_right h]
    rfl

/-! ### The exact arm

`elTier2Code`'s in-window arm, factorised so the bridge can compare it with the
model's `elExact`.  `tier2ExactCode` is a faithful copy of that arm; the copy is
tied to the guard by `elTier2Code_eq`, so a change to `ElGuardRefine`'s text
breaks this file rather than drifting from it. -/

/-- The guard's exact arm, as a function of the normalised word and the row. -/
def tier2ExactCode (W hi lo : Nat) (e : Int) (q : Int) (lz : Nat) : Option LeanLLVM.Code :=
  let Ahi := W * hi / 2 ^ 64
  let Alo := W * hi % 2 ^ 64
  let c := W * lo / 2 ^ 64
  let L := W * lo % 2 ^ 64
  let Rlo := (Alo + c) % 2 ^ 64
  let Rhi := (Ahi + (if Rlo < Alo then 1 else 0)) % 2 ^ 64
  let ub := Rhi / 2 ^ 63
  let sh := 10 + ub
  let m := Rhi / 2 ^ sh
  let hp := Rhi % 2 ^ sh
  let hh := 2 ^ (9 + ub)
  let tie := hp = hh
  let close := hp = hh - 1
  let undec := (tie && decide (Rlo ||| L = 0)) || (close && decide (Rlo = 2 ^ 64 - 1))
  if undec && decide (q < 0) then none
  else
    let up : Nat :=
      if hp > hh then 1
      else if tie && decide ((Rlo ||| L) ≠ 0 ∨ m % 2 = 1) then 1 else 0
    LeanLLVM.ElGuardRefine.elPack { m := m, up := up, ub := ub, e := e, lz := lz }

/-- The guard's `undec` test and the model's are the same decision. -/
theorem undec_eq (tie close b1 b2 q0 : Prop)
    [Decidable tie] [Decidable close] [Decidable b1] [Decidable b2] [Decidable q0] :
    (((decide tie && decide b1) || (decide close && decide b2)) && decide q0)
      = decide (((tie ∧ b1) ∨ (close ∧ b2)) ∧ q0) := by
  by_cases ht : tie <;> by_cases hc : close <;> by_cases hb1 : b1 <;>
    by_cases hb2 : b2 <;> by_cases hq : q0 <;> simp [ht, hc, hb1, hb2, hq]

/-- The guard's in-window `up` and the model's are the same round-up.

The guard tests `hp > hh` first and the tie second; the model adds a `tieUp`
term.  When `hp > hh` the tie is false, so the sum is the guard's one; otherwise
the first term is zero. -/
theorem up_eq_generic (hp hh : Nat) (b : Prop) [Decidable b] :
    ((if hp > hh then 1 else 0) + (if hp = hh ∧ b then 1 else 0))
    = (if hp > hh then 1 else if (hp = hh) && decide b then 1 else 0) := by
  by_cases hgt : hp > hh
  · have hne : ¬ (hp = hh) := by omega
    simp [hgt, hne]
  · by_cases hpe : hp = hh
    · by_cases hb : b
      · simp [hpe, hb]
      · simp [hpe, hb]
    · simp [hgt, hpe]

/-- The model's `elExact` is the guard's exact arm's encoding.

The two texts differ only in the branch representation: the guard's `Bool`
condition and its `if hp > hh ... else if tie && ...` are the model's `Prop`
condition and `(if hp > hh then 1 else 0) + tieUp`.  `undec_eq` and
`up_eq_generic` are those two correspondences, and `elPack_bits` carries the
encoding. -/
theorem elExact_bits (W lz : Nat) (t : EPow) (q : Int) :
    elExact W lz t q = (tier2ExactCode W t.hi t.lo t.e q lz).map tier2Bits := by
  unfold elExact tier2ExactCode
  dsimp only
  simp only [elHalf]
  rw [undec_eq]
  split <;> split <;> simp_all [elPack_bits, up_eq_generic, Omap_ite]

/-! ### The guard's decision with the arm factorised

`tier2Code` is `elTier2Code`'s `some` branch, with the exact arm named.  It is a
copy of the guard's text; `elTier2Code_eq` proves the copy is the original by
`rfl`, which is the check that keeps the two in step. -/

/-- `elTier2Code`'s decision at a known row. -/
def tier2Code (w : Nat) (q : Int) (t : LeanLLVM.ElGuardRefine.EPow) : Option LeanLLVM.Code :=
  if w = 0 then some { expField := 0, mant := 0 }
  else
    let W := LeanLLVM.ElGuardRefine.Wnorm w
    let s := LeanLLVM.ElGuardRefine.sliceOf W t.hi
    if LeanLLVM.ElGuardRefine.inWindow s.hp s.hh then
      tier2ExactCode W t.hi t.lo t.e q (LeanLLVM.ElGuardRefine.lz w)
    else
      LeanLLVM.ElGuardRefine.elPack
        { m := s.Ahi / 2 ^ s.sh, up := if s.hp > s.hh then 1 else 0,
          ub := s.ub, e := t.e, lz := LeanLLVM.ElGuardRefine.lz w }

/-- `tier2Code` is the guard's own decision at the row `epowAt` returns. -/
theorem elTier2Code_eq (w : Nat) (q : Int) :
    LeanLLVM.ElGuardRefine.elTier2Code w q =
      (match LeanLLVM.ElGuardRefine.epowAt q with
       | none => none
       | some t => tier2Code w q t) := by
  cases hq : LeanLLVM.ElGuardRefine.epowAt q with
  | none => simp [LeanLLVM.ElGuardRefine.elTier2Code, hq]
  | some t =>
    simp only [LeanLLVM.ElGuardRefine.elTier2Code, hq]
    unfold tier2Code tier2ExactCode
    dsimp only [LeanLLVM.ElGuardRefine.sliceOf, LeanLLVM.ElGuardRefine.hi64,
      LeanLLVM.ElGuardRefine.lo64]
    rfl

/-! ### The window test

The guard's emitted test is `hp + 2 ^ 64 - (hh - 2)` reduced modulo `2 ^ 64`;
`inWindow_iff` says that is the three-value window when `hh ≤ 2 ^ 11` and
`hp < 2 ^ 64`.  For a sixty-four-bit mantissa the high word is below `2 ^ 64`, so
`ub ≤ 1` and both hypotheses hold. -/

/-- The emitted wrapped test is the model's window below `2 ^ 64`. -/
theorem window_equiv (Ahi : Nat) (hA : Ahi < 2 ^ 64) :
    (LeanLLVM.ElGuardRefine.inWindow (Ahi % 2 ^ (10 + Ahi / 2 ^ 63))
        (2 ^ (9 + Ahi / 2 ^ 63)) = true)
      ↔ (2 ^ (9 + Ahi / 2 ^ 63) ≤ Ahi % 2 ^ (10 + Ahi / 2 ^ 63) + 2 ∧
          Ahi % 2 ^ (10 + Ahi / 2 ^ 63) ≤ 2 ^ (9 + Ahi / 2 ^ 63)) := by
  have hub : Ahi / 2 ^ 63 ≤ 1 := by
    have hlt : Ahi / 2 ^ 63 < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)]
      have htwo : (2 : Nat) * 2 ^ 63 = 2 ^ 64 := by decide
      omega
    omega
  have hiff := LeanLLVM.ElGuardRefine.inWindow_iff
    (hp := Ahi % 2 ^ (10 + Ahi / 2 ^ 63)) (hh := 2 ^ (9 + Ahi / 2 ^ 63))
    (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 1 ≤ 9 + Ahi / 2 ^ 63))
    (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 9 + Ahi / 2 ^ 63 ≤ 11))
    (by
      have hmod := Nat.mod_lt Ahi
        (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ (10 + Ahi / 2 ^ 63))
      have hle := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 10 + Ahi / 2 ^ 63 ≤ 11)
      omega)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hiff.mp h
    exact ⟨by omega, h2⟩
  · intro h
    exact hiff.mpr ⟨by omega, h.2⟩

/-! ### The bridge proof -/

/-- **The tier-2 bridge, proved.**  On the kernel's domain the model's decision
is the guard's encoding.  The range gate, the zero mantissa, the normalised word,
the window test and both arms line up; the only table fact used is that the
row's `hi` is a sixty-four-bit word. -/
theorem numElEl1_eq_elTier2Code (w : Nat) (q : Int) (hw : w < 2 ^ 64) :
    numElEl1 guardTable w q =
      (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits := by
  rw [elTier2Code_eq]
  by_cases hgate : q < -45 ∨ 45 < q
  · have hnone : LeanLLVM.ElGuardRefine.epowAt q = none := by
      unfold LeanLLVM.ElGuardRefine.epowAt
      rw [ite_eq_right (by omega)]
    simp [numElEl1, hgate, hnone]
  · have hrange : -45 ≤ q ∧ q ≤ 45 := by omega
    obtain ⟨t, ht⟩ := epowAt_some_of_range hrange
    have ht' : guardTable q = some (EPow.ofGuard t) := by simp [guardTable, ht]
    simp only [ht, ht', numElEl1, hgate, ite_false, EPow.ofGuard]
    by_cases hw0 : w = 0
    · subst w
      simp [tier2Code, LeanLLVM.ElGuardRefine.codeBits]
    · simp only [hw0, ite_false, tier2Code, LeanLLVM.ElGuardRefine.Wnorm,
        LeanLLVM.ElGuardRefine.lz,
        show 63 - Nat.log2 w = 64 - Nat.size w from (lz_shift w hw0).symm,
        LeanLLVM.ElGuardRefine.sliceOf, LeanLLVM.ElGuardRefine.hi64,
        LeanLLVM.ElGuardRefine.lo64, elHalf]
      have hWlt := wnorm_lt w hw hw0
      have hhi := epowAt_hi_lt q t ht
      have hA : (w * 2 ^ (64 - Nat.size w) * t.hi) / 2 ^ 64 < 2 ^ 64 := by
        apply Nat.div_lt_of_lt_mul
        have hle1 : w * 2 ^ (64 - Nat.size w) ≤ 2 ^ 64 - 1 := by omega
        have hle2 : t.hi ≤ 2 ^ 64 - 1 := by omega
        have hmul : w * 2 ^ (64 - Nat.size w) * t.hi ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
          Nat.mul_le_mul hle1 hle2
        have hnum : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 64 * 2 ^ 64 := by decide
        omega
      have hwin := window_equiv ((w * 2 ^ (64 - Nat.size w) * t.hi) / 2 ^ 64) hA
      simp only [hwin]
      split
      · rename_i hP
        rw [elExact_bits]
        simp only [hP]
        rfl
      · rename_i hP
        rw [elPack_bits]
        simp only [hP, ite_false]
        rfl

/-- **The bridge holds.** -/
theorem numFastElAgrees : NumFastElAgrees :=
  fun w q hw => numElEl1_eq_elTier2Code w q hw

/-! ### The bound is load-bearing

Above `2 ^ 64` the guard's wrapped window subtraction is no longer the model's
three-value window.  The witness is `w = 43 · 2 ^ 64`, `q = -45`: the model
decides `4490088828488384512`, the guard's encoding `4221546617189100823`. -/

/-- The unbounded statement: the model at every natural mantissa. -/
def NumFastElUnbounded : Prop :=
  ∀ (w : Nat) (q : Int),
    numElEl1 guardTable w q = (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits

/-- The model's decision at the witness. -/
theorem numElEl1_43_neg45 :
    numElEl1 guardTable (43 * 2 ^ 64) (-45) = some 4490088828488384512 := by
  decide

/-- The guard's encoding at the witness. -/
theorem elTier2Code_43_neg45 :
    (LeanLLVM.ElGuardRefine.elTier2Code (43 * 2 ^ 64) (-45)).map tier2Bits =
      some 4221546617189100823 := by
  decide

/-- **The unbounded statement is false.**  The word bound is the kernel's
domain, as `ElGuardRefinesOn` states it, not a convenience of the proof. -/
theorem not_numFastElUnbounded : ¬ NumFastElUnbounded := by
  intro h
  have hbad := h (43 * 2 ^ 64) (-45)
  rw [numElEl1_43_neg45, elTier2Code_43_neg45] at hbad
  exact absurd hbad (by decide)

/-! ### The check at the guard's witnesses

The guard's own test set is `ElGuardRefine.witnesses`; the model and the guard
decide the same bits at every one of them.  This is a `decide`-checked theorem,
not an evaluation, so a regression in either model fails the build. -/

set_option exponentiation.threshold 2200 in
set_option maxRecDepth 20000 in
/-- **The bridge at the guard's witnesses.**  `numElEl1 guardTable` and
`elTier2Code`'s bits are equal at each of `ElGuardRefine.witnesses`, including
the two 15- and 16-digit rows the guard's window alone would decide the other
way. -/
theorem numElEl1_witnesses :
    (LeanLLVM.ElGuardRefine.witnesses.all (fun (w, q) =>
      decide (numElEl1 guardTable w q
        = (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits))) = true := by
  decide

/-! ### Why the wrap is load-bearing

The pre-fix model is not in the tree, so the record of the defect is a theorem
about its arithmetic: at `(34, -36)` the low sum is at least `2 ^ 64`, so an
unreduced low word is not the emitted word, and the wrapped model is the one
that decides with the guard. -/

/-- The exponent `-45 … 45` table's row for `q`, as the model's row. -/
def rowAt (q : Int) : Option EPow := guardTable q

/-- The emitted row at `-36`, whose low sum overflows at `w = 34`. -/
theorem rowAt_neg36 :
    (rowAt (-36)).map (fun t => (t.hi, t.lo, t.e))
      = some (12259964326927110866, 15989199047912110569, -247) := by
  decide

/-- The low-word sum at `(34, -36)`, before the emitted wrap, is at least
`2 ^ 64`; that is the input where the unwrapped reading rounds down and the
wrapped one rounds up. -/
theorem low_sum_overflows_at_34_neg36 :
    2 ^ 64 ≤
      (34 * 2 ^ (64 - (34 : Nat).size) * 12259964326927110866) % 2 ^ 64 +
        (34 * 2 ^ (64 - (34 : Nat).size) * 15989199047912110569) / 2 ^ 64 := by
  decide

/-- **The wrapped model is the guard's at that input.**  The model and the guard
return the same bits at `(34, -36)`, which the unwrapped reading does not
(the reading is recorded in `JsonStage2NumFastCalls.elExact`'s docstring). -/
theorem numElEl1_34_neg36 :
    numElEl1 guardTable 34 (-36)
      = (LeanLLVM.ElGuardRefine.elTier2Code 34 (-36)).map tier2Bits := by
  decide

/-! ### Axiom footprints -/

#print axioms numFastElAgrees

#print axioms numElEl1_eq_elTier2Code

#print axioms not_numFastElUnbounded

#print axioms numElEl1_witnesses

#print axioms low_sum_overflows_at_34_neg36

#print axioms numElEl1_34_neg36

end LeanLLVM.Refinement
