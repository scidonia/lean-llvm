/-
The stage-2 walk's seven appended objects, at the extents its body allocates.

The emitted `s2_walk` takes twenty-one values: `stage2.h`'s thirteen and eight
appended by the flattening (see `JsonStage2IR.stage2StagingArgs`).  Seven of the
eight are written by the body — the cursor record, the two container stacks, the
token, the decoder state, the log and the refusal record — and `%d.i` is written by
neither.  Those seven extents are the ones a *frame* has to name, and both sides of
the call need them: the stage-2 record names them in its frame
(`JsonStage2Contract.stage2WalkFrame`), and its caller's post names them in the
frame it reports for the composite run (`JsonPipelineContract.pipelineUnitsPost`).
They therefore live here, upstream of both, rather than in either.

The numbers are the body's own `llvm.lifetime.start` sizes, read off the pinned
AST by `JsonStage2IR`'s `lifetimeExtents` guards; a fixture that resized one of
them fails those guards at elaboration rather than leaving either record
describing an object the body no longer has.
-/
import LeanLLVM.Basic

set_option autoImplicit false

namespace LeanLLVM.Refinement

/-- The cursor record `%c.i`. -/
def stage2CursorExtent : Nat := 1192

/-- Each container stack `%ctype.i`/`%cst.i`. -/
def stage2StackExtent : Nat := 520

/-- The token `%t352.i`. -/
def stage2TokenExtent : Nat := 24

/-- The decoder state `%s`. -/
def stage2StateExtent : Nat := 120

/-- The log `%z`. -/
def stage2LogExtent : Nat := 64

/-- The error record `%e`. -/
def stage2ErrorExtent : Nat := 24

/-- The seven appended objects the walk writes, at their extents, in the order
`stage2StagingArgs` receives them. -/
def stage2StagedWrites (c ctype cst tok s z e : Nat) : List (Nat × Nat) :=
  [(c, stage2CursorExtent), (ctype, stage2StackExtent), (cst, stage2StackExtent),
   (tok, stage2TokenExtent), (s, stage2StateExtent), (z, stage2LogExtent),
   (e, stage2ErrorExtent)]

end LeanLLVM.Refinement
