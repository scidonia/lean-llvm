/-
The page's store word and the peel's word at the exit, from the committed
identities.

`JsonS1BlocksWordIdentities.fb54_or84_eq_entryMask` states the fused body's
store word at the mask unit's `Ctx`, and `JsonS1BlocksPeelWord` packages the
one-step instantiation from the document's windows for both the page
(`fb54_or84_eq_entryMask_docBlock`) and the peel
(`if103_or135_eq_entryMask_docBlock`).  `JsonS1BlocksLoopRun` states the page's
identity as `PageModel`'s `storeW`, quantified over the loop's carry.

This module closes both links:

* **`pageModel`** — `PageModel bs` itself, at a full block whose two loaded
  words are the block's halves and whose carried state is the model's.  The
  entry word's tail clamp is the all-ones word at a full block, so the model's
  `stage1Word` is the identity's `entryMask64`.
* **`peelWordAtModel_of_carry`** — the peel's `%or135` at the exit is
  `PeelWordAtModel`, which `loopExit_peel_slot` reads back as the model's
  `stage1Word` (`loopExit_peel_slot_of_carry`).
* **The exit staging** — `exit_staging_of_loopCarry` and
  `exit_staging_of_fusedEnd` are `loopExit_staging`/`fused_end_staging` at the
  document's own block count, and `hstagePeel_of_staging`/`hsilent_of_arm` feed
  the peel's two exit hypotheses (`hstagePeel_fusedExit`,
  `hsilent_fusedExit_of_gate`) from them.  These are the inputs
  `JsonS1BlocksExitFuel`'s compositions name.

## What remains

The page's windows are the block's halves: `PageModel`'s `storeW` takes
`bs73 = docBlock.take 32` and `bs74 = docBlock.drop 32`, and the tie from the
emitted six offset reads to those windows is the run's (as at the peel).  The
carried state (`PageCarry`: the two state words and the shift register at the
model's carry) is the loop's own residual, held as an hypothesis at every head;
no module derives the DFA state words from the classifier's carry.  The
accumulator's fold and lane count, the escape page's keeps and the run's own
frame are `JsonS1BlocksLoopRun`'s exit obligations, unchanged here.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoopRun
import LeanLLVM.Refinement.JsonS1BlocksPeelWord
import LeanLLVM.Refinement.JsonS1BlocksConv

namespace LeanLLVM.Refinement.JsonS1BlocksPageModel

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksPeelWord
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksPeelStaging
open LeanLLVM.Refinement.JsonS1BlocksConv
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The carried state's odd-run equation

`pageCtx`'s open and parity bits are chosen from its own odd-run bit, so the
docBlock corollaries' `k.st.oddRun = (k.opened && k.ppar)` premise holds at the
model's carry without a further carried-state fact. -/

theorem pageCtx_oddRun (bs : List UInt8) (i : Nat) :
    (pageCtx bs i).st.oddRun = ((pageCtx bs i).opened && (pageCtx bs i).ppar) := by
  simp [pageCtx]

/-! ### The page's store word -/

/-- **`PageModel`.**  At a full block whose windows are the block's halves and
whose carried state is the model's, the fused body's store word is
`stage1Word`.  The docBlock corollary gives the unclamped `entryMask64`; the
block is full, so the model's clamp is the all-ones word. -/
theorem pageModel (bs : List UInt8) : PageModel bs := by
  refine ⟨?storeW⟩
  intro c bs73 bs74 hfull hcarry h73 h74
  have hi : c.i.toNat < blocksOf bs.length := by
    have hle : 64 * (c.i.toNat + 1) ≤ 64 * blocksOf bs.length := by
      have := blocksOf_le bs.length
      omega
    omega
  have hne : 64 ≤ bs.length - 64 * c.i.toNat := by omega
  have h00 : (fusedValues c bs73 bs74).andII =
      escAnd00W (pageCtx bs c.i.toNat) := by
    rw [fb54_andII]
    exact hcarry.and00
  have h13 : c.st15 = seedW (pageCtx bs c.i.toNat) := hcarry.st15
  have hprev : c.prevS = (if stage1PrevS bs c.i.toNat then 1 else 0) :=
    hcarry.prevS
  rw [fb54_or84_eq_entryMask_docBlock bs hi (pageCtx bs c.i.toNat) rfl rfl rfl
    c bs73 bs74 h73 h74 (pageCtx_oddRun bs c.i.toNat) h00 h13 hprev]
  unfold stage1Word
  rw [limMask_eq_allOnes hne]
  rw [show (BitVec.ofInt 64 (-1) : BitVec 64) = BitVec.allOnes 64 from rfl,
    BitVec.and_allOnes]

/-! ### The peel's word at the exit -/

/-- **The peel's `%or135` is the model's entry word at the peel's block.**  The
docBlock corollary at `if.then103`'s registers, with the carried state read from
the loop's carry. -/
theorem peelWordAtModel_of_carry {bs : List UInt8} {c : FusedCarry}
    {env : Env} {n andv : BitVec 64} {bs136 bs137 : List UInt8}
    {conv : BitVec 32}
    (hi : c.i.toNat < blocksOf bs.length)
    (hcarry : PageCarry bs c)
    (h136 : bs136 = (docBlock bs c.i.toNat).take 32)
    (h137 : bs137 = (docBlock bs c.i.toNat).drop 32) :
    PeelWordAtModel
      (fusedPeelValues env c n andv bs136 bs137 conv).or135 bs c.i.toNat :=
  if103_or135_peelWordAtModel bs hi (pageCtx bs c.i.toNat) rfl rfl rfl
    n c.b bs136 bs137 c.ascii c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv
    c.prevAscii h136 h137 (pageCtx_oddRun bs c.i.toNat) hcarry.and00 hcarry.st15
    hcarry.prevS

/-- **The peel's slot is the model's word, from the carried state.**  The
peel's `%or135 &&& limMask %and` store reads back as `stage1Word`; the clamp's
index and the word are the record's own readings. -/
theorem loopExit_peel_slot_of_carry {bs : List UInt8} {c : FusedCarry}
    {env : Env} {n andv w : BitVec 64} {bs136 bs137 : List UInt8}
    {conv : BitVec 32}
    (hi : c.i.toNat < blocksOf bs.length)
    (hcarry : PageCarry bs c)
    (h136 : bs136 = (docBlock bs c.i.toNat).take 32)
    (h137 : bs137 = (docBlock bs c.i.toNat).drop 32)
    (hlim : limMask andv.toNat = limMask (bs.length - 64 * c.i.toNat))
    (hw : w = (fusedPeelValues env c n andv bs136 bs137 conv).or135
      &&& limMask andv.toNat) :
    readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
      (c.ent + 8 * c.i.toNat) 8 = some (wordsOf [stage1Word bs c.i.toNat]) :=
  loopExit_peel_slot (peelWordAtModel_of_carry hi hcarry h136 h137) hlim hw

/-! ### The exit staging

`JsonS1BlocksLoopRun.loopExit_staging` and `JsonS1BlocksEntry.fused_end_staging`
are the loop's two staging routes at `for.end101`: the first reads the carry's
prefix and frame, the second the accumulator's fold.  Both are stated at the
document's own block count here, which is the shape the exit's compositions
(`JsonS1BlocksExitFuel`) and the peel's staging lemmas read. -/

/-- **The staging from the loop's carry.**  `loopExit_staging` at
`n = bs.length` and `nb = blocksOf bs.length`. -/
theorem exit_staging_of_loopCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {env : Env} {s : State} {c : FusedCarry} {gate : Bool}
    (hexit : FusedExit env s c) (hc : LoopCarry mem0 xp xn ps bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hu8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat))
    (haccLen : c.u8k.length = 4)
    (hi : c.i.toNat = blocksOf bs.length)
    (herr : evalICmp .eq (ptestzU8k c.u8k) 0 = 1 ↔
      ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
        (bs.length ≠ 0 ∧ klTailByte (klByte bs (bs.length - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs bs.length (blocksOf bs.length) gate
      (evalICmp .eq (ptestzU8k c.u8k) 0) :=
  loopExit_staging hexit hc hframe hu8k haccLen rfl rfl hi herr

/-- **The staging from the fused exit.**  `fused_end_staging` at the
document's block count. -/
theorem exit_staging_of_fusedEnd {bs : List UInt8} {env : Env} {s : State}
    {c : FusedCarry} {gate : Bool}
    (hexit : FusedExit env s c)
    (hascii_len : c.ascii.length = 4) (hu8k_len : c.u8k.length = 4)
    (hascii : packLanes c.ascii = bytesToNat (asciiAcc bs (blocksOf bs.length)))
    (hacc : packLanes c.u8k = bytesToNat (klAll gate bs))
    (herr : evalICmp .eq (ptestzU8k c.u8k) 0 = 1 ↔
      ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
        (bs.length ≠ 0 ∧ klTailByte (klByte bs (bs.length - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs bs.length (blocksOf bs.length) gate
      (evalICmp .eq (ptestzU8k c.u8k) 0) :=
  fused_end_staging env s c bs bs.length (blocksOf bs.length) gate
    (evalICmp .eq (ptestzU8k c.u8k) 0) hexit rfl rfl hascii_len hu8k_len
    hascii hacc herr

/-- **The peel's staging at the exit.**  `hstagePeel_fusedExit` at
`k = c.shr.toNat`, the block the carry's bound names.  The peel's carried words
are the exit's, so this is the hypothesis `JsonS1BlocksExitFuel` takes. -/
theorem hstagePeel_of_staging {bs : List UInt8} {env : Env} {c : FusedCarry}
    {n andv : BitVec 64} {bs136 bs137 : List UInt8} {conv : BitVec 32}
    {nb : Nat} {gate : Bool}
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hsucc : c.shr.toNat + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs c.shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs c.shr.toNat).drop 32) :
    ∀ (v : IfThen103Values),
      v = fusedPeelValues env c n andv bs136 bs137 conv →
      VerdictStaging v.or279 c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0) :=
  hstagePeel_fusedExit env c n andv bs136 bs137 conv hstage hsucc rfl h136 h137

/-- **The peel's `hsilent` at the exit, gate derived from the arm.**  The
silent-merge bit at a zero gate word and the block's probe, at the bound the
carry names. -/
theorem hsilent_of_arm {bs : List UInt8} {env : Env} {c : FusedCarry}
    {n andv : BitVec 64} {bs136 bs137 : List UInt8} {arm : BitVec 64}
    (hk : c.shr.toNat < blocksOf bs.length)
    (h136 : bs136 = (docBlock bs c.shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs c.shr.toNat).drop 32)
    (h4 : arm &&& 4 = 0)
    (hprobe : ∀ x ∈ blockHalfOr bs c.shr.toNat, x.toNat < 0x80)
    (hprev : c.prevAscii ≠ 0) :
    ∀ (v : IfThen103Values),
      v = fusedPeelValues env c n andv bs136 bs137 (entryGate arm) →
      lookupName (ifThen103Out (forEnd101OutOf env c.prevS c.ascii c.u8k
        c.prevAscii c.st0 c.st9 c.st15 andv) v) "%or.cond191" = some (.int 1 1) :=
  hsilent_fusedExit_of_gate env c n andv bs136 bs137 arm hk rfl h136 h137 h4
    hprobe hprev

/-! ### The loop's run without a `PageModel` hypothesis

`loopRun_carry` takes the page's word identity as an input.  With `pageModel`
proved, the run is available from the carried-state facts and the block bound
alone; this is the form the calling lanes use. -/

/-- **The loop's run from the head, at the proved page model.** -/
theorem loopRun_carry_of_state (sel : Calls) (mem0 : Mem) (xp xn : Nat)
    (ps : List Nat) (bs : List UInt8) (env : Env) (s : State)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : LoopInv mem0 xp xn ps bs env s c gate escBit)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hcallAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
      (∀ j, j < c'.shr.toNat →
        readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
      EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
      StreamPrefix r.mem xp xn ps) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      LoopTerm mem0 xp xn ps bs e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e :=
  loopRun_carry sel mem0 xp xn ps bs (pageModel bs) env s c gate escBit hstate
    hshrBlocks hshr57 hshrLe hblocks64 hinv hb3 hgap hdoc hzero hentXp hcallAll hkeep

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.pageCtx_oddRun
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.pageModel
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.peelWordAtModel_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.loopExit_peel_slot_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.exit_staging_of_loopCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.exit_staging_of_fusedEnd
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.hstagePeel_of_staging
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.hsilent_of_arm
#print axioms LeanLLVM.Refinement.JsonS1BlocksPageModel.loopRun_carry_of_state

end LeanLLVM.Refinement.JsonS1BlocksPageModel
