/-
# The walk's terminal price at the credit boundary

## The defect this module closes

`entryPos` is `G.ent.getD k 0`, and past the last entry the totalisation sends it to
zero.  A terminal price stated as

  `p + 2 ≤ 32·(k2 - C.k) + 8·(entryPos G k2 - entryPos G C.k)`

therefore has a byte term of *zero* at `k2 = G.nep`: the document bytes a final
scalar's trailing-whitespace scan walks are charged to nothing.  The price can still
be met at the terminal index only because the counted terminal path is twenty-two
blocks; the credit the scan actually spent appears nowhere.
`JsonStage2WalkExitProducer` records the same reading from the exit's side.

## Two quantities, and the module that holds them

The position at an index and the credit boundary at an index are two quantities, and
only the first is a stream read.  `boundary`, its bounds and monotonicity, the
agreement with `entryPos` below the stream, and the potential read through it live in
`JsonStage2WalkTraverse`, beside `walkPotential`'s definition.  **They cannot live
here**: this module is downstream of that one
(`JsonStage2WalkCredit → JsonStage2WalkDispatchWitnessHlast → JsonStage2WalkFinishPath
→ JsonStage2WalkAssembly → JsonStage2WalkTraverse`), so a definition written here is
invisible to the potential it restates — a module above a definition cannot re-point
it.  That is why the repair is split: the index and the potential are stated where
the potential is defined, and the terminal *price* is restated here, where the
terminal conjunct is stated and `Hlast`'s facts are in scope.

Below the stream the boundary and the stream's position are the same number
(`boundary_eq_entryPos` in `JsonStage2WalkTraverse`), so every price the walk states
at `k2 < nep` is unchanged — that identity is what makes the substitution safe
rather than a re-pricing.  At `G.nep` the boundary reads the document's *length*: the
terminal index has no entry position, and the credit it consumes is the entry's whole
remaining span, `G.n - entryPos G C.k`.

`entryPos` is not redefined, and `entryPos_nep` is not deleted: it stays the fact
about the stream, and `entryPosPrice_noByteAllowance` — beside the definition in
`JsonStage2WalkTraverse` — reads it as the statement that the old terminal byte term
is zero.

## The price it restates

`terminalPrice_boundary` is the terminal conjunct with `boundary` in place of
`entryPos` at both indices, derived from the `entryPos` form for any `k2`: the
boundary is never below the stream's position, and it agrees with it below the
stream, so the price's right-hand side only loses the vanishing byte term.  At
`k2 = G.nep` the byte term is `8 · (G.n - entryPos G C.k)`
(`terminalPrice_terminal_byteTerm`) — the span a trailing scan may cover — and
`terminalPrice_of_scan` is the charge: a terminal path of the dispatch's per-byte
form `22 + 6b` fits the price for every `b` inside that span, where the old form
held only at `b = 0` (`terminalScan_charge_control`, in `JsonStage2WalkTraverse`).

`hlast_finish_boundary` is the last entry's finish disjunct at the restated price:
`hlast_finish`'s existential with its conjunct replaced, so the callers of the
terminal finish path can read the boundary directly.

## What is not here

The boundary, its laws and the boundary potential — `boundary`,
`boundary_eq_entryPos`, `boundary_le`, `boundary_mono`, `price_eq_of_lt`,
`entryPosPrice_noByteAllowance`, `terminalScan_charge_control`,
`walkPotential_boundary` and its lemmas — are in `JsonStage2WalkTraverse`.  This
module states prices at the index, not the credit that is charged at it.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The price, below the stream and at its end

The index itself is `JsonStage2WalkTraverse`'s.  What is stated here is the terminal
conjunct read through it: the charged span only grows, and at the terminal index it
is the entry's remaining document. -/

/-- **The terminal price on the credit boundary.**  The `entryPos` form with the
boundary at both indices: the entry term is untouched, and the byte term is the
boundary's, which at the terminal index is the document's end rather than the
stream's totalisation.  The hypothesis is the old conjunct, and the conclusion its
replacement — the charged span only grows, by exactly what `entryPos` discards past
the stream. -/
theorem terminalPrice_boundary {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {p k2 : Nat}
    (hk : C.k < G.nep)
    (h : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) :
    p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (boundary G k2 - boundary G C.k) := by
  rw [boundary_eq_entryPos G hk]
  have hb : entryPos G k2 - entryPos G C.k ≤ boundary G k2 - entryPos G C.k :=
    Nat.sub_le_sub_right (boundary_ge_entryPos G k2) _
  exact le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left _ hb) _)

/-- **The restated price's new conjunct, at the terminal index**: an entry's
remaining span, `G.n - entryPos G C.k`.  This is the term the old form read as zero
and the one a trailing scan is charged against. -/
theorem terminalPrice_terminal_byteTerm {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G}
    (hk : C.k < G.nep) :
    stage2ByteAllowance * (boundary G G.nep - boundary G C.k) =
      stage2ByteAllowance * (G.n - entryPos G C.k) := by
  rw [boundary_nep, boundary_eq_entryPos G hk]

/-- **The boundary pays a trailing scan.**  A terminal path of the dispatch's
per-byte form `22 + 6b` — twenty-two blocks on the entry's own path and six per byte
a scan visits (`walkCredit_suffices`' numbers) — fits the restated price for every
`b` inside the entry's remaining span: the entry term pays the twenty-four, and the
boundary's byte term pays every scanned byte.  The same path under the `entryPos`
form is `terminalScan_charge_control`'s second conjunct. -/
theorem terminalPrice_of_scan {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {p b : Nat}
    (hk : C.k < G.nep) (hb : b ≤ G.n - entryPos G C.k) (hp : p ≤ 22 + 6 * b) :
    p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (boundary G G.nep - boundary G C.k) := by
  rw [terminalPrice_terminal_byteTerm G hk]
  have hΔ : 1 ≤ G.nep - C.k := by omega
  have hmul : stage2EntryAllowance * 1 ≤ stage2EntryAllowance * (G.nep - C.k) :=
    Nat.mul_le_mul_left _ hΔ
  have hb' : stage2ByteAllowance * b ≤ stage2ByteAllowance * (G.n - entryPos G C.k) :=
    Nat.mul_le_mul_left _ hb
  simp only [stage2EntryAllowance, stage2ByteAllowance] at hmul hb' ⊢
  omega

/-- **The last entry's finish disjunct at the restated price.**  `hlast_finish`'s
existential with its terminal conjunct read on the boundary: the same segment, the
same merge cells, and a price whose byte term is the entry's remaining span.  The
carry's index is below the stream (`hlastK`), which is the agreement's hypothesis. -/
theorem hlast_finish_boundary {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (prev : String) (kOp : Operand)
      (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧ Cd.block = "cleanup478.i" ∧
      sd.pre = some prev ∧ phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧ k2 = nepv.toNat ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (boundary G k2 - boundary G C.k) := by
  obtain ⟨Cd, sd, p, k2, prev, kOp, nepv,
    hseg, hblk, hpre, hphi, hkOp, hnep, hterm, hprice⟩ :=
    hlast_finish G C s hInv hblock f
  exact ⟨Cd, sd, p, k2, prev, kOp, nepv, hseg, hblk, hpre, hphi, hkOp, hnep, hterm,
    terminalPrice_boundary G (C := C) (p := p) (k2 := k2)
      (by rw [← f.hlastK]; omega) hprice⟩

end WalkScope
end LeanLLVM.Refinement
