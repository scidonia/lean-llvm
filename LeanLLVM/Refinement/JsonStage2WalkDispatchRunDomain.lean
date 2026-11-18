/-
The run class's domain, at a staged document.

## What is exhibited

`HcontArm.run` is the default arm's run class at the continuing head: the byte before the
entry's end is whitespace, the whitespace skip runs, the token's end `%ee.1.i` is the run's
stop, the copy call's test is true and the extra-token scan is entered.  Its segment is
`runScanMerge_at`'s — the head chain, the byte's span, the tail's *scan* arm, the landing,
`scanRoundsAt`'s visits at the seam's bound, the exit and the merge.

The document below is the continuing level's, with a letter as its head byte:

| document | head byte | `HcontClass` | level |
|---|---|---|---|
| `"a0"` | `97` (`'a'`) | `defaultValueBracketHigh` | continuing |

The byte is read off the staged document (`WalkGeom.doc`, `WalkGeom.entries`,
`entryByte`/`entryPos`) and the state is the seed's handoff, so the arm's first class
premise — the tag test clear at `97` — is a fact about the input.  The bundle's other
fields are the arm's own premises, exactly as `hHead`/`hTail` are the scan-free arms': the
whitespace run's own bytes, the three callees' staging, the landing's byte and the visits'
totality are the input's, and no `WalkInv` clause fixes them.

## The negative control

A digit's head byte (`48`) has the tag test `1` — it is `HcontClass.value`'s, the
plain-value arm's — so `RunFacts.hbit` fails there and the arm's class does not hold.  The
control is one detector at one byte.

The second control is the class's *continuation*: `.run`'s tail ends at `land.rhs457.i` and
the scan-free arms' at `if.end473.i`, so a document whose byte before the entry's end is not
whitespace cannot inhabit this arm's tail field.  The two names are distinct, which is the
mechanical half of the scan-free/run split.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head byte, at the staged document -/

/-- **`"a0"`'s head byte is `97`.** -/
theorem runHead_a {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((97 : UInt8)).toNat = 97 := by decide
  rw [ht] at hreg
  walk_read using hreg

/-- **`97`'s head class is `defaultValueBracketHigh`**, the default arm's. -/
theorem runClass_a : HcontClass (BitVec.ofNat 8 97) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`97` takes the run class's premise**: the tag test is clear there, so the seam sends
the walk to `if.else387.i` and the byte's span rather than the plain-value path. -/
theorem runPrem_a :
    (evalICmp .eq (BitVec.ofNat 8 97) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 97 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-! ### The arm at the document, and its dispatch -/

/-- **The document fixes the bundle's head byte.**  The bundle's `%8` cell and the
document's are the same read, so its `x` is `97` rather than an unrelated byte. -/
theorem runFacts_byte {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    (f : RunFacts G (walkSeed G S) s) : f.x = BitVec.ofNat 8 97 := by
  have h8d := runHead_a G S s h hInv
  have hinj := Option.some.inj (f.h8.symm.trans h8d)
  exact eq_of_heq (Value.int.inj hinj).2

/-- **`"a0"`'s head takes the continuing run arm.**  The bundle is the arm's own
premises, and `runFacts_byte` says its head byte is the document's. -/
def run_cont_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (f : RunFacts G (walkSeed G S) s) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .run f

/-- **The dispatch at `"a0"`**, through the real `HcontArm.dispatch`: the continuing
guard is the document's `0 + 1 < 2`, and the result is the merge `runScanMerge_at`
composes. -/
theorem run_cont_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (97 : UInt8))
    (f : RunFacts G (walkSeed G S) (openerHead G S args next)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact HcontArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show 0 + 1 < 2; omega)
    (run_cont_arm G S _ f)

/-! ### The negative controls -/

/-- **A digit's head byte is not the run class's**: at `48` the tag test is `1`, so the
walk takes `if.end372.i`'s `if.then413.i` arm — the plain-value path — and `RunFacts.hbit`
fails.  One detector at one byte. -/
theorem digitHead_not_run :
    ¬ ((evalICmp .eq (BitVec.ofNat 8 48) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 48 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) := by
  decide

/-- **The run class's continuation is not the scan-free arms':** the tail's endpoint is
`land.rhs457.i` here and `if.end473.i` there, so the two arms' tail fields cannot be
interchanged.  This is the mechanical half of the split — the copy call's test is `1`
here and `0` there. -/
theorem runTail_ne_cleanupTail : ("land.rhs457.i" : String) ≠ "if.end473.i" := by
  decide

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.runHead_a
#print axioms LeanLLVM.Refinement.WalkScope.runClass_a
#print axioms LeanLLVM.Refinement.WalkScope.runPrem_a
#print axioms LeanLLVM.Refinement.WalkScope.run_cont_arm
#print axioms LeanLLVM.Refinement.WalkScope.run_cont_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.digitHead_not_run
#print axioms LeanLLVM.Refinement.WalkScope.runTail_ne_cleanupTail

end WalkScope
end LeanLLVM.Refinement
