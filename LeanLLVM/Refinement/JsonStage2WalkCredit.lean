/-
# The walk's credit boundary

## The defect this module closes

`WalkPotential`'s byte term is `8 · (G.n - entryPos G C.k)`, and the credit a
revolution consumes is priced `p ≤ 32·Δk + 8·ΔA`, where `ΔA` is read off the same
`entryPos`.  Both readings are right below the stream and wrong at its end:
`entryPos` is `G.ent.getD k 0`, and past the last entry the totalisation sends it
to zero (`entryPos_nep`).  A terminal price stated as

  `p + 2 ≤ 32·(k2 - C.k) + 8·(entryPos G k2 - entryPos G C.k)`

therefore has a byte term of *zero* at `k2 = G.nep`: the document bytes a final
scalar's trailing-whitespace scan walks are charged to nothing.  The price can
still be met at the terminal index only because the counted terminal path is
twenty-two blocks; the credit the scan actually spent appears nowhere.
`JsonStage2WalkExitProducer` records the same reading from the exit's side — "the
byte credit the dispatch spent is not recovered here" — and leaves the statement
shape to the layer that owns the potential.

## The boundary

The position at an index and the credit boundary at an index are two quantities,
and only the first is a stream read:

  `boundary G k = if k < G.nep then entryPos G k else G.n`

Below the stream the two are the same number, so every price the walk already
states is unchanged — `price_eq_of_lt` is that identity, and it is what makes the
substitution safe rather than a re-pricing.  At `G.nep` the boundary reads the
document's *length*: the terminal index has no entry position, and the credit it
consumes is the entry's whole remaining span, `G.n - entryPos G C.k`.
Above the stream the boundary saturates at the same length, which is what keeps it
total and monotone there (`boundary_mono`, `boundary_le`) while `entryPos` falls
back to zero.

`entryPos` is not redefined, and `entryPos_nep` is not deleted: it stays the fact
about the stream, and `entryPosPrice_noByteAllowance` reads it as the statement
that the old terminal byte term is zero.  The boundary supersedes `entryPos` at the
terminal *index* only, and does so as a second definition beside it.

## The price it restates

`terminalPrice_boundary` is the terminal conjunct with `boundary` in place of
`entryPos` at both indices, derived from the `entryPos` form for any `k2`: the
boundary is never below the stream's position, and it agrees with it below the
stream, so the price's right-hand side only loses the vanishing byte term.  At
`k2 = G.nep` the byte term is `8 · (G.n - entryPos G C.k)`
(`terminalPrice_terminal_byteTerm`) — the span a trailing scan may cover — and
`terminalPrice_of_scan` is the charge: a terminal path of the dispatch's per-byte
form `22 + 6b` fits the price for every `b` inside that span, where the old form
held only at `b = 0` (`terminalScan_charge_control`).

`hlast_finish_boundary` is the last entry's finish disjunct at the restated price:
`hlast_finish`'s existential with its conjunct replaced, so the callers of the
terminal finish path can read the boundary directly.

## The potential: the word the layer charges against

A price alone charges nothing.  The charge is `walkPotential`'s byte term, and while
that term reads `entryPos` the terminal byte credit is the totalisation: at
`C.k = G.nep` the potential is `8 · G.n` — the whole document still counted as
unreached — while the price at that index spends zero.  `walkPotential_boundary` is
that potential with its byte term read through the boundary, and it is the version
the layer must charge against:

* below the stream it is `walkPotential` word for word
  (`walkPotential_boundary_eq_of_lt`), so no head-state statement changes value;
* at and past the stream it is `0` (`walkPotential_boundary_zero_of_nep_le`) — the
  credit is spent, which is what the terminal index means;
* `walkPotential_boundary_spend` is `walkPotential_spend` with the boundary: `C.k ≤
  C'.k` is the only index hypothesis, because `boundary_mono` is unconditional and
  `boundary_le` bounds both ends inside the document.  `walkPotential_spend` needed
  `entryPos G C.k ≤ entryPos G C'.k` from its caller, which `entryPos_mono` supplies
  only under `C'.k < G.nep` — so the terminal step was *unstatable* in that form;
* `terminalCharge_boundary` is the terminal step: the restated terminal conjunct
  spends its price and leaves the potential at zero.

## What is not here

`JsonStage2WalkTraverse` owns `walkPotential` and its two laws, so the definitions
above are the statement to transplant rather than the re-pointing itself.  What this
module fixes is the index, the price stated at it, and the potential stated at it;
`boundary` is a price index and no theorem here reads it as a stream position.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The index

`entryPos`'s default is `0` because it is a lane read: an index past the stream
selects no lane, and zero is the totalisation.  The price's default cannot be zero
at the same index, because the credit at `nep` is the document the walk has left to
reach.  Two quantities, two definitions. -/

/-- **The credit boundary at an index**: the entry stream's position below the
stream, and the document's length at and past it.

`entryPos` is a stream read and totalises to zero past the stream; `boundary` is a
price index and totalises to the document's length.  Two quantities that agree below
the terminal index and must not agree at it: the terminal index has no entry
position, and the credit there is the document the walk has left to reach.  That is
why `price_eq_of_lt` is an equality rather than an implication, and why re-pointing
a price at this index cannot alter a non-terminal price. -/
def boundary {m0 : Mem} (G : WalkGeom m0) (k : Nat) : Nat :=
  if k < G.nep then entryPos G k else G.n

/-- **Below the stream the boundary is the stream's position.** -/
theorem boundary_eq_entryPos {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    boundary G k = entryPos G k := by
  simp only [boundary, ite_eq_left hk]

/-- **At the terminal index the boundary is the document's length.** -/
theorem boundary_nep {m0 : Mem} (G : WalkGeom m0) : boundary G G.nep = G.n := by
  simp only [boundary, ite_eq_right (lt_irrefl G.nep)]

/-- **The boundary is inside the document**, at every index: a position below the
stream is one the entry stream holds (`entryPos_lt`), and at or past it the boundary
is the length itself. -/
theorem boundary_le {m0 : Mem} (G : WalkGeom m0) (k : Nat) : boundary G k ≤ G.n := by
  by_cases hk : k < G.nep
  · rw [boundary_eq_entryPos G hk]
    exact le_of_lt (entryPos_lt G hk)
  · rw [show boundary G k = G.n from by simp only [boundary, ite_eq_right hk]]

/-- **The stream's position past the stream is zero**, at every index from `nep` on:
`entryPos`'s default is the totalisation, not a position.  `entryPos_nep` is the
instance at `nep`, and this is the form the boundary's comparison needs. -/
theorem entryPos_eq_zero_of_nep_le {m0 : Mem} (G : WalkGeom m0) {k : Nat}
    (hk : G.nep ≤ k) : entryPos G k = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  simp only [entryPos, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- **The boundary is never below the stream's position.**  Below the stream the two
coincide, and at or past it the stream reads zero while the boundary reads the
document's length.  This is the direction the price's substitution rests on: the
right-hand side the boundary form states is the `entryPos` form's plus what the
totalisation discards. -/
theorem boundary_ge_entryPos {m0 : Mem} (G : WalkGeom m0) (k : Nat) :
    entryPos G k ≤ boundary G k := by
  by_cases hk : k < G.nep
  · rw [boundary_eq_entryPos G hk]
  · rw [show boundary G k = G.n from by simp only [boundary, ite_eq_right hk],
      entryPos_eq_zero_of_nep_le G (by omega)]
    exact Nat.zero_le _

/-! ### Monotonicity

The walk's accounting advances the index and reads the boundary at both ends, so the
boundary has to rise with the index across the whole range — below the stream it is
`entryPos`'s monotonicity, and the step across `nep` is `boundary_nep_ge_prev`. -/

/-- **The boundary is monotone in the index.**  Two cases: both indices below the
stream, where it is `entryPos_mono`; or the upper one at or past `nep`, where the
boundary is the document's length and `boundary_le` bounds the lower one. -/
theorem boundary_mono {m0 : Mem} (G : WalkGeom m0) {k k' : Nat} (hkk : k ≤ k') :
    boundary G k ≤ boundary G k' := by
  by_cases hk' : k' < G.nep
  · have hk : k < G.nep := lt_of_le_of_lt hkk hk'
    rw [boundary_eq_entryPos G hk, boundary_eq_entryPos G hk']
    exact entryPos_mono G hkk hk'
  · rw [show boundary G k' = G.n from by simp only [boundary, ite_eq_right hk']]
    exact boundary_le G k

/-- **The last entry's boundary is at most the terminal one.**  The step the terminal
price reads: its byte term is a difference of boundaries, and the terminal index may
not fall below the entry before it. -/
theorem boundary_nep_ge_prev {m0 : Mem} (G : WalkGeom m0) :
    boundary G (G.nep - 1) ≤ boundary G G.nep :=
  boundary_mono G (Nat.sub_le _ _)

/-- **And the step is strict when there is an entry to take it from**, since every
entry's position is inside the document: the terminal boundary is past the last
entry position, not equal to it. -/
theorem boundary_nep_gt_prev {m0 : Mem} (G : WalkGeom m0) (hnep : 0 < G.nep) :
    boundary G (G.nep - 1) < boundary G G.nep := by
  have hprev : G.nep - 1 < G.nep := by omega
  rw [boundary_eq_entryPos G hprev, boundary_nep]
  exact entryPos_lt G hprev

/-! ### The price, below the stream and at its end -/

/-- **Below the stream the price is the price.**  Both indices are stream positions,
so the boundary form and the `entryPos` form are the same number — every price the
walk states at `k2 < nep` is unchanged by the substitution, not merely implied by
it. -/
theorem price_eq_of_lt {m0 : Mem} (G : WalkGeom m0) {k k2 : Nat}
    (hk : k < G.nep) (hk2 : k2 < G.nep) :
    stage2EntryAllowance * (k2 - k) +
        stage2ByteAllowance * (boundary G k2 - boundary G k) =
      stage2EntryAllowance * (k2 - k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G k) := by
  rw [boundary_eq_entryPos G hk, boundary_eq_entryPos G hk2]

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

/-- **The old terminal byte term is zero.**  `entryPos_nep` reads as the accounting
defect: at the terminal index the `entryPos` form charges nothing for the document
bytes the walk has left to reach, whatever the price's block count. -/
theorem entryPosPrice_noByteAllowance {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    stage2ByteAllowance * (entryPos G G.nep - entryPos G C.k) = 0 := by
  rw [entryPos_nep, Nat.zero_sub, Nat.mul_zero]

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

/-- **The charge, both ways at a hundred bytes**: the boundary form pays a
hundred-byte trailing scan and the `entryPos` form — whose byte term is zero — does
not.  The rows are `walkCreditRows`' long-string width at the terminal entry. -/
theorem terminalScan_charge_control :
    (22 + 6 * 100) + 2 ≤ 32 + 8 * 100 ∧ ¬ ((22 + 6 * 100) + 2 ≤ 32 + 0) := by
  decide

/-! ### The potential at the boundary

The word the layer charges against is the potential's byte term, not the price.  The
definitions here are `walkPotential`'s with that term read through `boundary`, so
`JsonStage2WalkTraverse` has the statement to transplant: below the stream nothing
changes, at the terminal index the credit is the entry's remaining span, and the
spend that pays a revolution becomes unconditional in the index. -/

/-- **The walk's remaining credit at the boundary**: `walkPotential`'s two terms with
the byte term read through `boundary`.  Below the stream the two are the same
number; at `G.nep` this is zero where `walkPotential` still counts `8 · G.n`. -/
def walkPotential_boundary {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat :=
  stage2EntryAllowance * (G.nep - C.k) + stage2ByteAllowance * (G.n - boundary G C.k)

/-- **Below the stream the credit is `walkPotential`'s, word for word** — the
agreement that keeps every head-state statement's value: `WalkExit`, `WalkLoopStep`'s
two branches and the completions are all taken at `C.k < G.nep`. -/
theorem walkPotential_boundary_eq_of_lt {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G}
    (hk : C.k < G.nep) : walkPotential_boundary G C = walkPotential G C := by
  simp only [walkPotential_boundary, walkPotential, boundary_eq_entryPos G hk]

/-- **The credit is inside the record's entry and byte terms.**  `walkPotential_le`
with the boundary: the entry term saturates, and the byte term is inside the document
because `boundary_le` is unconditional — so this version needs no invariant. -/
theorem walkPotential_boundary_le {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    walkPotential_boundary G C ≤
      stage2EntryAllowance * G.nep + stage2ByteAllowance * G.n := by
  have h1 : stage2EntryAllowance * (G.nep - C.k) ≤ stage2EntryAllowance * G.nep :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : stage2ByteAllowance * (G.n - boundary G C.k) ≤
      stage2ByteAllowance * G.n :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  simp only [walkPotential_boundary, stage2EntryAllowance, stage2ByteAllowance] at h1 h2 ⊢
  omega

/-- **At and past the stream the credit is exhausted**: no entry left and no document
byte left to reach.  This is the terminal index's reading, and it is what the
`entryPos` form cannot state — there the potential is `8 · G.n` past the stream. -/
theorem walkPotential_boundary_zero_of_nep_le {m0 : Mem} (G : WalkGeom m0)
    {C : WalkCarry G} (hk : G.nep ≤ C.k) : walkPotential_boundary G C = 0 := by
  have h1 : G.nep - C.k = 0 := by omega
  have h2 : boundary G C.k = G.n := by
    simp only [boundary, ite_eq_right (by omega : ¬ C.k < G.nep)]
  simp only [walkPotential_boundary, h1, h2, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- **A revolution's price, in the credit it consumes, at the boundary.**  As
`walkPotential_spend`, and with one hypothesis: the index does not fall.  The three
that `walkPotential_spend` takes beside it — the two positions inside the document
and their monotonicity — are `boundary_le` and `boundary_mono` here, and neither
carries a `k2 < nep` side condition.  That is what admits `C'.k = G.nep`, the step
the terminal dispatch takes and the step the `entryPos` form could not state. -/
theorem walkPotential_boundary_spend {m0 : Mem} (G : WalkGeom m0) {C C' : WalkCarry G}
    {p : Nat} (hk : C.k ≤ C'.k) (hk' : C'.k ≤ G.nep)
    (hall : p ≤ stage2EntryAllowance * (C'.k - C.k) +
      stage2ByteAllowance * (boundary G C'.k - boundary G C.k)) :
    p + walkPotential_boundary G C' ≤ walkPotential_boundary G C := by
  have h1 : G.nep - C.k = (G.nep - C'.k) + (C'.k - C.k) := by omega
  have hmono : boundary G C.k ≤ boundary G C'.k := boundary_mono G hk
  have hb : boundary G C.k ≤ G.n := boundary_le G C.k
  have hb' : boundary G C'.k ≤ G.n := boundary_le G C'.k
  have h2 : G.n - boundary G C.k =
      (G.n - boundary G C'.k) + (boundary G C'.k - boundary G C.k) := by omega
  simp only [walkPotential_boundary, stage2EntryAllowance, stage2ByteAllowance] at hall ⊢
  rw [h1, h2, Nat.mul_add, Nat.mul_add]
  omega

/-- **The terminal dispatch pays into the credit.**  The restated terminal conjunct as
the potential's spend: `p + 2` steps carry the loop from `C.k` to the terminal index,
the price is the entry's remaining span, and the potential at the terminal index is
zero.  This is the sentence the `entryPos` accounting could not state — its
`walkPotential_spend` needs `entryPos G C.k ≤ entryPos G G.nep`, which is false
whenever the entry has a position. -/
theorem terminalCharge_boundary {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {p : Nat}
    (hk : C.k < G.nep)
    (h : p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k)) :
    (p + 2) + walkPotential_boundary G { C with k := G.nep } ≤ walkPotential_boundary G C := by
  have hz : walkPotential_boundary G { C with k := G.nep } = 0 :=
    walkPotential_boundary_zero_of_nep_le G (le_of_eq rfl)
  rw [hz, Nat.add_zero, walkPotential_boundary, boundary_eq_entryPos G hk]
  exact h

/-- **The seed's credit is `walkPotential_seed`'s**, given an entry to dispatch:
`walkSeed`'s index is zero, so the boundary agrees with the stream's position there.
The hypothesis is not decoration — at `G.nep = 0` the boundary reads the document's
length at index zero, the seed's credit is zero, and the loop exits before any
dispatch; `walkCompletes_of_seed_loop` already carries `0 < G.nep`. -/
theorem walkPotential_boundary_seed {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hn : 0 < G.nep) :
    walkPotential_boundary G (walkSeed G S) =
      stage2EntryAllowance * G.nep + stage2ByteAllowance * (G.n - entryPos G 0) := by
  have hk : (walkSeed G S).k = 0 := rfl
  simp only [walkPotential_boundary, hk, boundary_eq_entryPos G hn, Nat.sub_zero]

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
