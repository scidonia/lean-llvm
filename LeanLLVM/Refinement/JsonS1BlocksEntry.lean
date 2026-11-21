/-
The block unit's entry and exit seals, and the loop's charge.

`JsonS1BlocksLoop` proves the fused loop's pages from the invariant it states at
`for.body54`, and `JsonS1BlocksExit` proves the bound's block at both of its
edges.  Two links between those modules and the rest of the unit are still open,
and this module states them:

## The entry

The preheader `for.body54.lr.ph` writes the DFA gate and the escape bit and
branches to the head.  `for_body54_lr_ph_page` runs the preheader's step and the
first body pass under the continuation the hand-off supplies, ending at
`if.then90`.  The first pass's carried byte is zero, so the decision is clear and
the DFA arm is the one the page takes; its six windows are the first row's.
`entry_first_page_latch` continues from there through `if.then90`, `if.end93`,
the escape record or its skip, and reaches the latch with the successor's carry.
`entry_first_page` composes the latch's own step: the same page reaches
`for.end101`'s exit or the back edge at the successor's `FusedInv`, in at most six
control steps (the loop's own iteration is five from the head; the preheader is
the sixth).

The DFA arm's continuation is stated at the cells the arm reads, not at a
`FusedInv`: the first pass enters the head from `for.body54.lr.ph` and its phi
operands are the hand-off's, so the arm's two pages are re-stated at the same
environments the loop's page uses (`fusedDfaState` and its successors) with the
first pass's carry.  `entryCarry` is that carry and `entryEnv` the preheader's
environment; the body's values are `fb54FirstPassValues` at them.

## The exit

`FusedTerm` is the loop's terminal at `for.end101` with the latch as the
predecessor.  `fused_end_denote` runs the bound's block at the fused edge, so the
seven phis select `%u8k.2`, `%or.i282`, `%75`, `%shr.i.i325`, `%conv13.i.i324`,
`%shr.i348` and `%shr85` — the staging's three words and the peel's four.  The
peel's own run follows at those cells (`fused_end_peel_denote`): `if.then103`'s
`ifThen103Values` carries the fused ASCII word and accumulator and the fused
carried byte, which is what `JsonS1BlocksExit`'s peel tie leaves open at this
edge.  `fused_end_staging` reads the same three words as a `VerdictStaging`, and
`fused_end_out_carries` is the tie from the block's phi destinations to them.

## The charge

The unit's budget is `8 * blocksOf n + 32`.  The ASCII phase charges three per
block and four for its entry and hand-off; the fused loop charges five per
remaining page and five for its exit.  With the entry's `shr = n >>> 6` and the
unaligned exit relation `shr + 1 = blocksOf n`, the sum is below the budget
(`entry_charge`, `entry_run_charge`).

## What remains

`s1_blocks_satisfies` still owes the loop's model carries — that the fused
`%u8k` packs to `klAll` and `%ascii` to `asciiAcc` at the document's blocks — and
the memory conjuncts: the entry array's prefix, the escape stream and count, and
the four-region `UnchangedOutside` (`JsonS1BlocksCompose` and
`JsonS1BlocksRecordFrame` name them).  This module states neither; it supplies the
entry and exit steps those compositions consume.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoop
import LeanLLVM.Refinement.JsonS1BlocksExit
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksRefine

namespace LeanLLVM.Refinement.JsonS1BlocksEntry

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonUtf8Spec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The preheader's environment

The hand-off's environment is `fb54PageEnv`; the preheader adds three cells to
it.  The bound, the stream, the count slot and the carry ride through the
hand-off's blocks; the lemmas below state each read at the cell the preheader's
page can see. -/

/-- The bound through the join's cells. -/
theorem lookupName_fb54PageEnv_shr (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) {shr : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (fb54PageEnv env c v v38) "%shr" = some (.int 64 shr) :=
  lookupName_ifEnd50Out_of _ _ _ _ _ _ _ _ _
    (lookupName_asciiHandoffOut_shr env c v v38 h)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The escape stream's base through the hand-off's blocks and the join. -/
theorem lookupName_asciiHandoffOut_xp (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (ifThen38Out (asciiHandoffEnv env c v) v38) "%xp" = some (.ptr xp) := by
  have hInc : lookupName (forIncEnv env c.i c.shr) "%xp" = some (.ptr xp) :=
    lookupName_forIncEnv_of env c.i c.shr h (by decide) (by decide)
  have hBody : lookupName (forBodyOut (forIncEnv env c.i c.shr) v) "%xp"
      = some (.ptr xp) := by
    handoff_lk
  have hEnd : lookupName (asciiHandoffEnv env c v) "%xp" = some (.ptr xp) :=
    lookupName_ifEndEnv_of _ _ _ hBody (by decide) (by decide) (by decide)
  ift_lk

/-- The stream count's slot through the hand-off's blocks and the join. -/
theorem lookupName_asciiHandoffOut_nxp (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (ifThen38Out (asciiHandoffEnv env c v) v38) "%nxp" = some (.ptr nxp) := by
  have hInc : lookupName (forIncEnv env c.i c.shr) "%nxp" = some (.ptr nxp) :=
    lookupName_forIncEnv_of env c.i c.shr h (by decide) (by decide)
  have hBody : lookupName (forBodyOut (forIncEnv env c.i c.shr) v) "%nxp"
      = some (.ptr nxp) := by
    handoff_lk
  have hEnd : lookupName (asciiHandoffEnv env c v) "%nxp" = some (.ptr nxp) :=
    lookupName_ifEndEnv_of _ _ _ hBody (by decide) (by decide) (by decide)
  ift_lk

/-- The carry's slot through the hand-off's blocks and the join. -/
theorem lookupName_asciiHandoffOut_xcarry (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (ifThen38Out (asciiHandoffEnv env c v) v38) "%xcarry"
      = some (.ptr xcarry) := by
  have hInc : lookupName (forIncEnv env c.i c.shr) "%xcarry" = some (.ptr xcarry) :=
    lookupName_forIncEnv_of env c.i c.shr h (by decide) (by decide)
  have hBody : lookupName (forBodyOut (forIncEnv env c.i c.shr) v) "%xcarry"
      = some (.ptr xcarry) := by
    handoff_lk
  have hEnd : lookupName (asciiHandoffEnv env c v) "%xcarry" = some (.ptr xcarry) :=
    lookupName_ifEndEnv_of _ _ _ hBody (by decide) (by decide) (by decide)
  ift_lk

/-- The escape stream's base through the join's cells. -/
theorem lookupName_fb54PageEnv_xp (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (fb54PageEnv env c v v38) "%xp" = some (.ptr xp) :=
  lookupName_ifEnd50Out_of _ _ _ _ _ _ _ _ _
    (lookupName_asciiHandoffOut_xp env c v v38 h)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The stream count's slot through the join's cells. -/
theorem lookupName_fb54PageEnv_nxp (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (fb54PageEnv env c v v38) "%nxp" = some (.ptr nxp) :=
  lookupName_ifEnd50Out_of _ _ _ _ _ _ _ _ _
    (lookupName_asciiHandoffOut_nxp env c v v38 h)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The carry's slot through the join's cells. -/
theorem lookupName_fb54PageEnv_xcarry (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (fb54PageEnv env c v v38) "%xcarry" = some (.ptr xcarry) :=
  lookupName_ifEnd50Out_of _ _ _ _ _ _ _ _ _
    (lookupName_asciiHandoffOut_xcarry env c v v38 h)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### The first page's carry and environment

The first pass enters the head with the hand-off's carried words and the
caller's pointers; its index is the hand-off's successor index, its carried byte
is zero, and its memory is the caller's.  `entryEnv` is the preheader's three
cells over the hand-off's environment, the environment the first body run leaves
its own cells over. -/

/-- The first page's carry: the hand-off's words, the caller's pointers, the
caller's memory, and the zero carried byte. -/
def entryCarry (c : AsciiCarry) (v : ForBodyValues) (v38 : IfThen38Values)
    (b ent xp nxp xcarry : Nat) (mem : Mem) : FusedCarry :=
  { i := v38.inc49
    prevS := v.shr17
    ascii := v38.or284
    u8k := v38.or291
    prevAscii := 0
    st0 := v.shrII
    st9 := v.conv13II
    st15 := v.shrI
    b := b
    ent := ent
    xp := xp
    nxp := nxp
    xcarry := xcarry
    shr := c.shr
    mem := mem }

/-- The preheader's environment: its three cells over the hand-off's. -/
def entryEnv (env : Env) (c : AsciiCarry) (v : ForBodyValues) (v38 : IfThen38Values)
    (arm : BitVec 64) (conv : BitVec 32) : Env :=
  forBody54LrPhEnv (fb54PageEnv env c v v38) arm conv

/-- The first page's body values are the hand-off's, at the first index. -/
theorem entryCarry_values (c : AsciiCarry) (v : ForBodyValues) (v38 : IfThen38Values)
    (b ent xp nxp xcarry : Nat) (mem : Mem) (bs73 bs74 : List UInt8) :
    fusedValues (entryCarry c v v38 b ent xp nxp xcarry mem) bs73 bs74
      = fb54FirstPassValues v v38 bs73 bs74 b ent := rfl

/-- The first page's store is the body's store at the caller's memory. -/
theorem entryCarry_store (c : AsciiCarry) (v : ForBodyValues) (v38 : IfThen38Values)
    (b ent xp nxp xcarry : Nat) (mem : Mem) (bs73 bs74 : List UInt8) :
    fusedStore (entryCarry c v v38 b ent xp nxp xcarry mem) bs73 bs74
      = writeBytes mem (fb54FirstPassValues v v38 bs73 bs74 b ent).arrayidx
          (natToBytes (fb54FirstPassValues v v38 bs73 bs74 b ent).or84.toNat 8) := rfl

/-- The bound through the preheader's three cells. -/
theorem lookupName_entryEnv_shr (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {shr : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (entryEnv env c v v38 arm conv) "%shr" = some (.int 64 shr) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_shr env c v v38 h) (by decide) (by decide) (by decide)

/-- The escape stream's base through the preheader's three cells. -/
theorem lookupName_entryEnv_xp (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (entryEnv env c v v38 arm conv) "%xp" = some (.ptr xp) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_xp env c v v38 h) (by decide) (by decide) (by decide)

/-- The stream count's slot through the preheader's three cells. -/
theorem lookupName_entryEnv_nxp (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (entryEnv env c v v38 arm conv) "%nxp" = some (.ptr nxp) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_nxp env c v v38 h) (by decide) (by decide) (by decide)

/-- The carry's slot through the preheader's three cells. -/
theorem lookupName_entryEnv_xcarry (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (entryEnv env c v v38 arm conv) "%xcarry" = some (.ptr xcarry) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_xcarry env c v v38 h) (by decide) (by decide) (by decide)

/-- The row base through the preheader's three cells. -/
theorem lookupName_entryEnv_b (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {b : Nat}
    (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (entryEnv env c v v38 arm conv) "%b" = some (.ptr b) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_b env c v v38 h) (by decide) (by decide) (by decide)

/-- The emit base through the preheader's three cells. -/
theorem lookupName_entryEnv_ent (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) {ent : Nat}
    (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (entryEnv env c v v38 arm conv) "%ent" = some (.ptr ent) :=
  lookupName_forBody54LrPhEnv_of _ arm conv
    (lookupName_fb54PageEnv_ent env c v v38 h) (by decide) (by decide) (by decide)

/-- The gate bit as the preheader leaves it. -/
theorem lookupName_entryEnv_gate (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) :
    lookupName (entryEnv env c v v38 arm conv) "%tobool87"
      = some (.int 1 (evalICmp .eq conv 0)) :=
  lookupName_forBody54LrPhEnv_tobool87 (fb54PageEnv env c v v38) arm conv

/-- The escape bit as the preheader leaves it. -/
theorem lookupName_entryEnv_escape (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32) :
    lookupName (entryEnv env c v v38 arm conv) "%tobool95.not"
      = some (.int 1 (evalICmp .eq (arm &&& 2) 0)) :=
  lookupName_forBody54LrPhEnv_tobool95 (fb54PageEnv env c v v38) arm conv

/-! ### The bound's block at the fused edge

`FusedTerm`'s exit constructor carries the seven words the block's phis name.
`fused_end_phi_selects` is the selection relation at `if.end98`, and
`fused_end_denote` is the block's own run at those cells. -/

/-- **The seven phis at the fused edge.**  Each selects the fused loop's own
register; `%u8k.1.lcssa` is `%u8k.2` and `%ascii.1.lcssa` is `%or.i282`. -/
theorem fused_end_phi_selects (env : Env) (s : State) (c : FusedCarry)
    (h : FusedExit env s c) :
    PhiSelects (stateAt env s) "if.end98" forEnd101Phis
      [("%st.sroa.15.2.lcssa", .int 64 c.st15),
       ("%st.sroa.9.2.lcssa", .int 64 c.st9),
       ("%st.sroa.0.2.lcssa", .int 64 c.st0),
       ("%prev_ascii.1.lcssa", .int 32 c.prevAscii),
       ("%u8k.1.lcssa", .vec 4 64 c.u8k),
       ("%ascii.1.lcssa", .vec 4 64 c.ascii),
       ("%prevS.2.lcssa", .int 64 c.prevS)] :=
  for_end101_phi_selects_fused env s c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15
    h.prevS h.ascii h.u8k h.prevAscii h.st0 h.st9 h.st15

/-- **The block's run at the fused edge.**  The seven phis select the fused
registers and the peel's test is `%and`'s zero comparison. -/
theorem fused_end_denote (env : Env) (s : State) (c : FusedCarry) (andv : BitVec 64)
    (h : FusedExit env s c) (hand : lookupName env "%and" = some (.int 64 andv)) :
    denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9
        c.st15 andv) s) :=
  for_end101_fused_denote env s c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv
    h.pre h.prevS h.ascii h.u8k h.prevAscii h.st0 h.st9 h.st15 hand

/-- A register read through the block's eight cells to the environment beneath
them. -/
theorem lookupName_forEnd101OutOf_of (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64)
    {k : String} {v : Value} (h : lookupName env k = some v)
    (h1 : "%tobool102.not" ≠ k) (h2 : "%prevS.2.lcssa" ≠ k)
    (h3 : "%ascii.1.lcssa" ≠ k) (h4 : "%u8k.1.lcssa" ≠ k)
    (h5 : "%prev_ascii.1.lcssa" ≠ k) (h6 : "%st.sroa.0.2.lcssa" ≠ k)
    (h7 : "%st.sroa.9.2.lcssa" ≠ k) (h8 : "%st.sroa.15.2.lcssa" ≠ k) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv) k
      = some v := by
  simp only [forEnd101OutOf, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4, lookupName_cons_ne _ _ h5, lookupName_cons_ne _ _ h6,
    lookupName_cons_ne _ _ h7, lookupName_cons_ne _ _ h8]
  exact h

/-- The staging's ASCII word at the block's output. -/
theorem lookupName_forEnd101OutOf_ascii (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%ascii.1.lcssa" = some (.vec 4 64 ascii) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The staging's accumulator at the block's output. -/
theorem lookupName_forEnd101OutOf_u8k (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%u8k.1.lcssa" = some (.vec 4 64 u8k) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The staging's carried byte at the block's output. -/
theorem lookupName_forEnd101OutOf_prevAscii (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%prev_ascii.1.lcssa" = some (.int 32 prevAscii) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The peel's shift register at the block's output. -/
theorem lookupName_forEnd101OutOf_prevS (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%prevS.2.lcssa" = some (.int 64 prevS) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The peel's first carried word at the block's output. -/
theorem lookupName_forEnd101OutOf_st0 (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%st.sroa.0.2.lcssa" = some (.int 64 st0) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The peel's second carried word at the block's output. -/
theorem lookupName_forEnd101OutOf_st9 (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%st.sroa.9.2.lcssa" = some (.int 64 st9) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The peel's third carried word at the block's output. -/
theorem lookupName_forEnd101OutOf_st15 (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%st.sroa.15.2.lcssa" = some (.int 64 st15) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- The peel's test at the block's output. -/
theorem lookupName_forEnd101OutOf_test (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
      "%tobool102.not" = some (.int 1 (evalICmp .eq andv 0)) := by
  simp only [forEnd101OutOf, cells]
  block_lk_cons

/-- **The block's output carries the staging's three words.**  The phi
destinations are `c.ascii`, `c.u8k` and `c.prevAscii`. -/
theorem fused_end_out_carries (env : Env) (s : State) (c : FusedCarry) (andv : BitVec 64)
    (h : FusedExit env s c) :
    lookupName (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        "%ascii.1.lcssa" = some (.vec 4 64 c.ascii) ∧
      lookupName (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        "%u8k.1.lcssa" = some (.vec 4 64 c.u8k) ∧
      lookupName (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        "%prev_ascii.1.lcssa" = some (.int 32 c.prevAscii) :=
  ⟨lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _,
    lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _,
    lookupName_forEnd101OutOf_prevAscii env _ _ _ _ _ _ _ _⟩

/-! ### The peel's entry from the fused edge

`for_end101_peel_denote` is stated at the ASCII phase's exit, whose phi
destinations are the constants the latch's arm carries.  At the fused edge the
same block hands the peel the fused words: the ASCII word is `%or.i282`, the
accumulator `%u8k.2`, the carried byte `%75`, and the four peeled words are the
fused state.  The tie is a lookup substitution on the block's own cells. -/

/-- **The peel's run from the fused edge.**  `if.then103` runs at the frozen
block's output with `ifThen103Values` at the fused cells. -/
theorem fused_end_peel_denote (env : Env) (s : State) (c : FusedCarry)
    (n andv : BitVec 64) (conv : BitVec 32) (bs136 bs137 : List UInt8)
    (h : FusedExit env s c)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hasciilen : c.ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshr63 : c.shr.toNat < 2 ^ 63) :
    let v := ifThen103Values n c.b bs136 bs137 c.ascii c.st0 c.st9 c.st15 c.prevS andv
      c.shr c.ent conv c.prevAscii
    denoteCode s1BlocksCalls if_then103Instrs
        (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
          { s with pc := "if.then103", pre := some "for.end101" }) =
      some (stateAt (ifThen103Out
          (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv) v)
        { s with
          pc := "if.then103",
          pre := some "for.end101",
          mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  intro v
  exact if_then103_denote
    (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
    { s with pc := "if.then103", pre := some "for.end101" } n c.b bs136 bs137 c.ascii
    c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv c.prevAscii
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ h.base
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _)
    hasciilen
    hpos h136 h137
    (lookupName_forEnd101OutOf_st0 env _ _ _ _ _ _ _ _)
    (lookupName_forEnd101OutOf_st9 env _ _ _ _ _ _ _ _)
    (lookupName_forEnd101OutOf_st15 env _ _ _ _ _ _ _ _)
    (lookupName_forEnd101OutOf_prevS env _ _ _ _ _ _ _ _)
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ hand
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ h.emit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ h.bound
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (by simpa [BitVec.signExtend] using hshr63)
    (lookupName_forEnd101OutOf_of env _ _ _ _ _ _ _ _ hconv
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (lookupName_forEnd101OutOf_prevAscii env _ _ _ _ _ _ _ _)

/-! ### The staging at the fused exit

The seven carried words are the staging's fields: the ASCII word, the
accumulator and the carried byte are the three `VerdictStaging` reads, and the
rest are the peel's. -/

/-- **The staging at the fused exit.**  From the loop's two carries, the block's
three phi destinations are a `VerdictStaging`. -/
theorem fused_end_staging (env : Env) (s : State) (c : FusedCarry) (bs : List UInt8)
    (n nb : Nat) (gate : Bool) (err : BitVec 1) (h : FusedExit env s c)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hascii_len : c.ascii.length = 4) (hu8k_len : c.u8k.length = 4)
    (hascii : packLanes c.ascii = bytesToNat (asciiAcc bs nb))
    (hacc : packLanes c.u8k = bytesToNat (klAll gate bs))
    (herr : err = 1 ↔ ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs n nb gate err :=
  staging_of_carry bs n nb gate c.ascii c.u8k err hascii_len hu8k_len hn hnb
    hascii hacc herr

/-! ### The DFA arm from the first body pass

The first page's body leaves `if.then90`'s state with the `for.body54` cells over
the preheader's environment; the arm's own computation is the loop's, at the
first pass's carry.  `EntryArm` is the invariant-shaped set of cells the arm and
the latch read when no `FusedInv` is available yet.  The two lemmas below run the
arm, the merge, the escape record or its skip, and reach the latch. -/

/-- The cells the first page's arm and latch read, as facts about the preheader's
environment: the bound, the two arena pointers, the three escape-region
pointers, the index's place in the bound, and the two words' lane counts.  The
gate and escape bits are read at the call's own cells, so each arm lemma takes
the one it uses. -/
structure EntryArm (env : Env) (c : FusedCarry) : Prop where
  /-- The index is inside the bound. -/
  index_lt : c.i.toNat < c.shr.toNat
  /-- The ASCII accumulator has four lanes. -/
  ascii_len : c.ascii.length = 4
  /-- The DFA's accumulator has four lanes. -/
  u8k_len : c.u8k.length = 4
  /-- The row base. -/
  base : lookupName env "%b" = some (.ptr c.b)
  /-- The emit base. -/
  emit : lookupName env "%ent" = some (.ptr c.ent)
  /-- The loop bound. -/
  bound : lookupName env "%shr" = some (.int 64 c.shr)
  /-- The escape stream's base. -/
  stream : lookupName env "%xp" = some (.ptr c.xp)
  /-- The stream count's slot. -/
  count : lookupName env "%nxp" = some (.ptr c.nxp)
  /-- The carry's slot. -/
  carry : lookupName env "%xcarry" = some (.ptr c.xcarry)

/-- Six admitted jumps are a `runFuel` prefix of six control steps. -/
theorem runFuel_jump6 {calls : Calls} {f : Function} {s0 s1 s2 s3 s4 s5 s6 : State}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .jump s3) (h34 : step calls f s3 = .jump s4)
    (h45 : step calls f s4 = .jump s5) (h56 : step calls f s5 = .jump s6) (k : Nat) :
    runFuel calls (6 + k) f s0 = runFuel calls k f s6 := by
  rw [show 6 + k = 1 + (1 + (1 + (1 + (1 + (1 + k))))) from by omega,
    runFuel_jump_prefix h01 (1 + (1 + (1 + (1 + (1 + k))))),
    runFuel_jump_prefix h12 (1 + (1 + (1 + (1 + k)))),
    runFuel_jump_prefix h23 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h34 (1 + (1 + k)),
    runFuel_jump_prefix h45 (1 + k),
    runFuel_jump_prefix h56 k]

/-- **The DFA arm's skip branch from the first body pass.**  The arm, the merge
and the latch's entry, with the successor's carry and the body's store. -/
theorem entry_dfa_skip_arm (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (harm : EntryArm env c)
    (hgate : lookupName env "%tobool87" = some (.int 1 gate))
    (hescape : lookupName env "%tobool95.not" = some (.int 1 1))
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (h41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (h42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (h43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (h57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (h58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (h59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction
        (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    FusedLatch (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaLatchCore s c bs73 bs74) c.i
      (fusedNext c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
        (fusedStore c bs73 bs74)) gate 1 := by
  have hi : c.i.toNat < c.shr.toNat := harm.index_lt
  have hj57 : c.i.toNat < 2 ^ 57 := by omega
  have ha : (fusedValues c bs73 bs74).addPtr57 = c.b + 64 * c.i.toNat :=
    fusedValues_addPtr57 c bs73 bs74 hj57
  have h1 : 1 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h2 : 2 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h3 : 3 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have hb1 : 1 ≤ c.b + 64 * c.i.toNat := by omega
  have h41' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 1)
      (n := 32) (by omega)]
    exact h41
  have h42' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 2)
      (n := 32) (by omega)]
    exact h42
  have h43' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 3)
      (n := 32) (by omega)]
    exact h43
  have h57' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001f#64).signExtend 64).toNat = 31 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 31)
      (n := 32) (by omega)]
    exact h57
  have h58' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001e#64).signExtend 64).toNat = 30 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 30)
      (n := 32) (by omega)]
    exact h58
  have h59' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001d#64).signExtend 64).toNat = 29 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 29)
      (n := 32) (by omega)]
    exact h59
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_then90Block
      (by rw [show (fusedDfaState env s c gate bs73 bs74).pc = "if.then90" from rfl]
          exact findBlock_if_then90) (by decide)]
    exact if_then90_step (fusedE3 env c gate bs73 bs74)
      (fusedDfaState env s c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) rfl
      (if_then90_denote (fusedE3 env c gate bs73 bs74)
        (fusedDfaState env s c gate bs73 bs74) (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
        bs41 bs42 bs43 bs57 bs58 bs59
        (lookupName_fb54Env9_addPtr57 env (fusedValues c bs73 bs74) gate) h1 h41'
        h2 h42' h3 h43'
        (lookupName_fb54Env9_p88 env (fusedValues c bs73 bs74) gate)
        (fusedValues_low88_length c bs73 bs74)
        (lookupName_fb54Env9_p97 env (fusedValues c bs73 bs74) gate)
        (fusedValues_low97_length c bs73 bs74)
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate) harm.u8k_len
        h57' h58' h59')
  have hesc : lookupName
      (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not"
      = some (.int 1 1) :=
    lookupName_fusedDfaEnv_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      hescape
  have h34 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).pc
          = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    exact if_end93_step_skip
      (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      "if.then90" (.reg "%or.i281")
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 1 rfl rfl
      (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _
        (lookupName_fusedDfaEnv_or281 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59))
      hesc rfl
  refine ⟨h12, h34, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      prevS := lookupName_fusedDfaLatch_shr85 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      ascii := lookupName_fusedDfaLatch_or282 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      u8k := lookupName_fusedDfaLatch_u8k env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      prevAscii := lookupName_fusedDfaLatch_p75 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st0 := lookupName_fusedDfaLatch_shrII env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st9 := lookupName_fusedDfaLatch_conv13 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st15 := lookupName_fusedDfaLatch_shrI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      base := lookupName_fusedDfaLatch_b env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.base
      emit := lookupName_fusedDfaLatch_ent env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.emit
      bound := lookupName_fusedDfaLatch_shr env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.bound
      stream := lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.stream
      count := lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.count
      carry := lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.carry
      gate := lookupName_fusedDfaLatch_tobool87 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        hgate
      escape := lookupName_fusedDfaLatch_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        hescape
      succ := rfl
      index_lt := harm.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74
        (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
        (fusedStore c bs73 bs74) harm.ascii_len
      u8k_len := ifThen90Values_or281_length (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
        bs41 bs42 bs43 bs57 bs58 bs59 harm.u8k_len }

/-- **The DFA arm's escape branch from the first body pass.**  The arm, the
merge, `if.then96`'s call, and the latch's entry at the record's memory. -/
theorem entry_dfa_escape_arm (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (harm : EntryArm env c)
    (hgate : lookupName env "%tobool87" = some (.int 1 gate))
    (hescape : lookupName env "%tobool95.not" = some (.int 1 0))
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (h41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (h42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (h43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (h57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (h58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (h59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59)
    (r : CallOutcome)
    (hc : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction
        (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction
        (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapedLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 r) ∧
    FusedLatch
      (fusedDfaEscapedLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaEscapedLatchCore s c bs73 bs74 r) c.i
      (fusedNext c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
        r.mem) gate 0 := by
  have hi : c.i.toNat < c.shr.toNat := harm.index_lt
  have hj57 : c.i.toNat < 2 ^ 57 := by omega
  have ha : (fusedValues c bs73 bs74).addPtr57 = c.b + 64 * c.i.toNat :=
    fusedValues_addPtr57 c bs73 bs74 hj57
  have h1 : 1 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h2 : 2 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h3 : 3 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have hb1 : 1 ≤ c.b + 64 * c.i.toNat := by omega
  have h41' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 1)
      (n := 32) (by omega)]
    exact h41
  have h42' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 2)
      (n := 32) (by omega)]
    exact h42
  have h43' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 3)
      (n := 32) (by omega)]
    exact h43
  have h57' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001f#64).signExtend 64).toNat = 31 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 31)
      (n := 32) (by omega)]
    exact h57
  have h58' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001e#64).signExtend 64).toNat = 30 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 30)
      (n := 32) (by omega)]
    exact h58
  have h59' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57
        + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001d#64).signExtend 64).toNat = 29 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 29)
      (n := 32) (by omega)]
    exact h59
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_then90Block
      (by rw [show (fusedDfaState env s c gate bs73 bs74).pc = "if.then90" from rfl]
          exact findBlock_if_then90) (by decide)]
    exact if_then90_step (fusedE3 env c gate bs73 bs74)
      (fusedDfaState env s c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) rfl
      (if_then90_denote (fusedE3 env c gate bs73 bs74)
        (fusedDfaState env s c gate bs73 bs74) (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
        bs41 bs42 bs43 bs57 bs58 bs59
        (lookupName_fb54Env9_addPtr57 env (fusedValues c bs73 bs74) gate) h1 h41'
        h2 h42' h3 h43'
        (lookupName_fb54Env9_p88 env (fusedValues c bs73 bs74) gate)
        (fusedValues_low88_length c bs73 bs74)
        (lookupName_fb54Env9_p97 env (fusedValues c bs73 bs74) gate)
        (fusedValues_low97_length c bs73 bs74)
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate) harm.u8k_len
        h57' h58' h59')
  have hesc : lookupName
      (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not"
      = some (.int 1 0) :=
    lookupName_fusedDfaEnv_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      hescape
  have h23 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).pc
          = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    exact if_end93_step_escape
      (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      "if.then90" (.reg "%or.i281")
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 0 rfl rfl
      (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _
        (lookupName_fusedDfaEnv_or281 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59))
      hesc rfl
  have h34 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapedLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 r) :=
    if_then96_step sel
      (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
      (fusedValues_w73_length c bs73 bs74) (fusedValues_w74_length c bs73 bs74)
      (fusedValues c bs73 bs74).or14 (fusedValues c bs73 bs74).xorI c.i c.xp c.nxp
      c.xcarry r rfl
      (lookupName_fusedDfaLatch_w73 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_w74 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_or14 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_xorI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.stream)
      (lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.count)
      (lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
        harm.carry)
      hc
  refine ⟨h12, h23, h34, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      prevS := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_shr85 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      ascii := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_or282 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      u8k := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_u8k env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      prevAscii := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_p75 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st0 := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_shrII env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st9 := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_conv13 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st15 := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_shrI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      base := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_b env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.base)
      emit := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_ent env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.emit)
      bound := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_shr env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.bound)
      stream := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.stream)
      count := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.count)
      carry := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          harm.carry)
      gate := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_tobool87 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          hgate)
      escape := lookupName_ifThen96Out_of
        (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _
        (by decide) (by decide) (by decide) (by decide)
        (lookupName_fusedDfaLatch_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
          hescape)
      succ := rfl
      index_lt := harm.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74
        (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 r.mem
        harm.ascii_len
      u8k_len := ifThen90Values_or281_length (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
        bs41 bs42 bs43 bs57 bs58 bs59 harm.u8k_len }

/-! ### The first page, composed

`for_body54_lr_ph_page` runs the preheader's step and the first body pass.  The
DFA arm's lemmas above continue from the state that pass leaves.  The seed takes
the first row's six windows — `fused_windows` at the first index — so the arm's
loads are the document's first row. -/

/-- **The first page reaches the latch.**  The preheader, the first body pass,
the DFA arm and the escape record or its skip reach a `FusedLatch` with the
successor's carry, in at most five control steps. -/
theorem entry_first_page_latch (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32)
    (bs73 bs74 : List UInt8) (b ent xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (hpc : s.pc = "for.body54.lr.ph")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 c.shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hi63 : (v38.inc49.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes s.mem
      (b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes s.mem
      ((b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : v38.or284.length = 4)
    (hu8k_len : v38.or291.length = 4)
    (hb3 : 3 ≤ b)
    (hzero : readBytes s.mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat → readBytes s.mem (b + 64 * j) 64 = some (doc j))
    (hirow : v38.inc49.toNat < c.shr.toNat)
    (hgap : b + 64 * c.shr.toNat ≤ ent)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) :
    ∃ (envL : Env) (core : State) (c' : FusedCarry) (k : Nat), k ≤ 5 ∧
      FusedLatch envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) ∧
      c'.shr = c.shr ∧ c'.b = b ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt (fb54PageEnv env c v v38) s) =
        runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt envL core) := by
  let c0 : FusedCarry := entryCarry c v v38 b ent xp nxp xcarry s.mem
  have hc0 : c0 = entryCarry c v v38 b ent xp nxp xcarry s.mem := rfl
  have hvalues : fusedValues c0 bs73 bs74 = fb54FirstPassValues v v38 bs73 bs74 b ent := rfl
  have hstore : fusedStore c0 bs73 bs74
      = writeBytes s.mem (fb54FirstPassValues v v38 bs73 bs74 b ent).arrayidx
          (natToBytes (fb54FirstPassValues v v38 bs73 bs74 b ent).or84.toNat 8) := rfl
  let env0 : Env := entryEnv env c v v38 arm conv
  let s0 : State := { s with pc := "for.body54", pre := some "for.body54.lr.ph" }
  have hlr := (for_body54_lr_ph_page env s c v v38 arm conv bs73 bs74 b ent hpc
      (lookupName_fb54PageEnv_arm env c v v38 harm)
      (lookupName_fb54PageEnv_conv env c v v38 hconv) hb hent hi63 hshl63 hread73
      hread74 h73len h74len hascii_len)
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (stateAt (fb54PageEnv env c v v38) s) = .jump (stateAt env0 s0) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt (fb54PageEnv env c v v38) s)
      for_body54_lr_phBlock
      (by rw [show (stateAt (fb54PageEnv env c v v38) s).pc = s.pc from rfl, hpc]
          exact findBlock_for_body54_lr_ph) (by decide)]
    exact hlr.1
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env0 s0) =
      .jump (fusedDfaState env0 s0 c0 (evalICmp .eq conv 0) bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env0 s0) for_body54Block
      (by rw [show (stateAt env0 s0).pc = "for.body54" from rfl]
          exact findBlock_for_body54) (by decide)]
    dsimp only [env0, s0, entryEnv]
    rw [hlr.2]
    rfl
  have hw : FusedWindows s.mem b c.shr.toNat v38.inc49 doc :=
    fused_windows s.mem b c.shr.toNat v38.inc49 doc hb3 hirow hzero hdoc
  have h41 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 1) 32 = some hw.bs41 := hw.w41
  have h42 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 2) 32 = some hw.bs42 := hw.w42
  have h43 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 3) 32 = some hw.bs43 := hw.w43
  have h57 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 31) 32 = some hw.bs57 := hw.w57
  have h58 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 30) 32 = some hw.bs58 := hw.w58
  have h59 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 29) 32 = some hw.bs59 := hw.w59
  have harmCells : EntryArm env0 c0 :=
    { index_lt := hirow
      ascii_len := hascii_len
      u8k_len := hu8k_len
      base := lookupName_entryEnv_b env c v v38 arm conv hb
      emit := lookupName_entryEnv_ent env c v v38 arm conv hent
      bound := lookupName_entryEnv_shr env c v v38 arm conv hshr
      stream := lookupName_entryEnv_xp env c v v38 arm conv hxp
      count := lookupName_entryEnv_nxp env c v v38 arm conv hnxp
      carry := lookupName_entryEnv_xcarry env c v v38 arm conv hxcarry }
  have hgate : lookupName env0 "%tobool87" = some (.int 1 (evalICmp .eq conv 0)) :=
    lookupName_entryEnv_gate env c v v38 arm conv
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (arm &&& 2) 0) with hesc | hesc
  · -- the escape record runs
    obtain ⟨r, hc⟩ := hcall
      [.int 64 (fusedValues c0 bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c0 bs73 bs74).w73
         (fusedValues c0 bs73 bs74).w74),
       .int 64 (fusedValues c0 bs73 bs74).xorI, .int 64 c0.i,
       .ptr c0.xp, .ptr c0.nxp, .ptr c0.xcarry]
      (fusedStore c0 bs73 bs74) s0.next
    have hescape : lookupName env0 "%tobool95.not" = some (.int 1 0) := by
      simpa only [hesc] using lookupName_entryEnv_escape env c v v38 arm conv
    obtain ⟨h23, h34, h45, hl⟩ := entry_dfa_escape_arm sel env0 s0 c0
      (evalICmp .eq conv 0) bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59
      harmCells hgate hescape hshr57 hb3 hgap h41 h42 h43 h57 h58 h59 r hc
    refine ⟨fusedDfaEscapedLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59,
      fusedDfaEscapedLatchCore s0 c0 bs73 bs74 r,
      fusedNext c0 bs73 bs74
        (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59).or281
        r.mem, 5, by omega, ?_, rfl, rfl, fun j => ?_⟩
    · rw [hesc]
      simpa only [c0, entryCarry] using hl
    · exact runFuel_jump5 h01 h12 h23 h34 h45 j
  · -- the escape record is skipped
    have hescape : lookupName env0 "%tobool95.not" = some (.int 1 1) := by
      simpa only [hesc] using lookupName_entryEnv_escape env c v v38 arm conv
    obtain ⟨h23, h34, hl⟩ := entry_dfa_skip_arm sel env0 s0 c0 (evalICmp .eq conv 0)
      bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59 harmCells hgate hescape
      hshr57 hb3 hgap h41 h42 h43 h57 h58 h59
    refine ⟨fusedDfaLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59,
      fusedDfaLatchCore s0 c0 bs73 bs74,
      fusedNext c0 bs73 bs74
        (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59).or281
        (fusedStore c0 bs73 bs74), 4, by omega, ?_, rfl, rfl, fun j => ?_⟩
    · rw [hesc]
      simpa only [c0, entryCarry] using hl
    · exact runFuel_jump4 h01 h12 h23 h34 j

/-- **The first page's terminal.**  The latch's own step sends the first page to
`for.end101`'s exit or the back edge, in at most six control steps.  The back
edge is `FusedInv` at `pre = "if.end98"` with the successor's carry. -/
theorem entry_first_page (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32)
    (bs73 bs74 : List UInt8) (b ent xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (hpc : s.pc = "for.body54.lr.ph")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 c.shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hi63 : (v38.inc49.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes s.mem
      (b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes s.mem
      ((b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : v38.or284.length = 4)
    (hu8k_len : v38.or291.length = 4)
    (hb3 : 3 ≤ b)
    (hzero : readBytes s.mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat → readBytes s.mem (b + 64 * j) 64 = some (doc j))
    (hirow : v38.inc49.toNat < c.shr.toNat)
    (hgap : b + 64 * c.shr.toNat ≤ ent)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) :
    ∃ (e : State) (k : Nat), k ≤ 6 ∧ FusedEnd e ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt (fb54PageEnv env c v v38) s) =
        runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction e := by
  obtain ⟨envL, core, c', k, hk, hl, hshrEq, hbEq, hrun⟩ :=
    entry_first_page_latch sel env s c v v38 arm conv bs73 bs74 b ent xp nxp xcarry
      doc hpc harm hconv hb hent hshr hxp hnxp hxcarry hi63 hshl63 hread73 hread74
      h73len h74len hascii_len hu8k_len hb3 hzero hdoc hirow hgap hshr57 hcall
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (v38.inc49 + 1) c'.shr)
    with hbit | hbit
  · obtain ⟨hstep, hinv⟩ :=
      fused_latch_loop sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbit (by rw [hshrEq]; exact hshr57)
    refine ⟨_, k + 1, by omega,
      FusedEnd.loop (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.body54", pre := some "if.end98" }) c'
        (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0) hinv, fun j => ?_⟩
    rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
      runFuel_jump_prefix hstep j]
    rfl
  · obtain ⟨hstep, hexit⟩ :=
      fused_latch_exit sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbit
    refine ⟨_, k + 1, by omega,
      FusedEnd.exit (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }) c' hexit, fun j => ?_⟩
    rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
      runFuel_jump_prefix hstep j]
    rfl

/-- **The first page's back edge.**  At a clear latch test the first page reaches
the loop's `FusedInv` at `for.body54` with `if.end98` as the predecessor and the
successor's carry. -/
theorem entry_first_page_loop (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32)
    (bs73 bs74 : List UInt8) (b ent xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (hpc : s.pc = "for.body54.lr.ph")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 c.shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hi63 : (v38.inc49.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes s.mem
      (b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes s.mem
      ((b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : v38.or284.length = 4)
    (hu8k_len : v38.or291.length = 4)
    (hb3 : 3 ≤ b)
    (hzero : readBytes s.mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat → readBytes s.mem (b + 64 * j) 64 = some (doc j))
    (hirow : v38.inc49.toNat < c.shr.toNat)
    (hgap : b + 64 * c.shr.toNat ≤ ent)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hbit : evalICmp .eq (v38.inc49 + 1) c.shr = 0) :
    ∃ (envL : Env) (s' : State) (c' : FusedCarry) (k : Nat), k ≤ 6 ∧
      FusedInv envL s' c' (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0) ∧
      c'.shr = c.shr ∧ c'.b = b ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt (fb54PageEnv env c v v38) s) =
        runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction s' := by
  obtain ⟨envL, core, c', k, hk, hl, hshrEq, hbEq, hrun⟩ :=
    entry_first_page_latch sel env s c v v38 arm conv bs73 bs74 b ent xp nxp xcarry
      doc hpc harm hconv hb hent hshr hxp hnxp hxcarry hi63 hshl63 hread73 hread74
      h73len h74len hascii_len hu8k_len hb3 hzero hdoc hirow hgap hshr57 hcall
  obtain ⟨hstep, hinv⟩ :=
    fused_latch_loop sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
      (evalICmp .eq (arm &&& 2) 0) hl (by rw [hshrEq]; exact hbit)
      (by rw [hshrEq]; exact hshr57)
  refine ⟨ifEnd98Env envL (v38.inc49) c'.shr,
    stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
      { core with pc := "for.body54", pre := some "if.end98" }, c', k + 1, by omega,
    hinv, hshrEq, hbEq, fun j => ?_⟩
  rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
    runFuel_jump_prefix hstep j]

/-- **The first page's bound exit.**  At a set latch test the first page reaches
`for.end101` with the latch as the predecessor. -/
theorem entry_first_page_exit (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32)
    (bs73 bs74 : List UInt8) (b ent xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (hpc : s.pc = "for.body54.lr.ph")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 c.shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hi63 : (v38.inc49.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes s.mem
      (b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes s.mem
      ((b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : v38.or284.length = 4)
    (hu8k_len : v38.or291.length = 4)
    (hb3 : 3 ≤ b)
    (hzero : readBytes s.mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat → readBytes s.mem (b + 64 * j) 64 = some (doc j))
    (hirow : v38.inc49.toNat < c.shr.toNat)
    (hgap : b + 64 * c.shr.toNat ≤ ent)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hbit : evalICmp .eq (v38.inc49 + 1) c.shr = 1) :
    ∃ (envL : Env) (s' : State) (c' : FusedCarry) (k : Nat), k ≤ 6 ∧
      FusedExit envL s' c' ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt (fb54PageEnv env c v v38) s) =
        runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction s' := by
  obtain ⟨envL, core, c', k, hk, hl, hshrEq, hbEq, hrun⟩ :=
    entry_first_page_latch sel env s c v v38 arm conv bs73 bs74 b ent xp nxp xcarry
      doc hpc harm hconv hb hent hshr hxp hnxp hxcarry hi63 hshl63 hread73 hread74
      h73len h74len hascii_len hu8k_len hb3 hzero hdoc hirow hgap hshr57 hcall
  obtain ⟨hstep, hexit⟩ :=
    fused_latch_exit sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
      (evalICmp .eq (arm &&& 2) 0) hl (by rw [hshrEq]; exact hbit)
  refine ⟨ifEnd98Env envL (v38.inc49) c'.shr,
    stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
      { core with pc := "for.end101", pre := some "if.end98" }, c', k + 1, by omega,
    hexit, fun j => ?_⟩
  rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
    runFuel_jump_prefix hstep j]

/-! ### The first row's windows

The DFA arm reads three windows below its pointer and three above it.
`fused_windows` states them at the document; at the first page's index they are
the first row's. -/

/-- **The first row the DFA arm reads.**  At the first page's index and the
document's blocks, the six window loads are the row's. -/
theorem entry_first_row (mem : Mem) (b shr : Nat) (i : BitVec 64)
    (doc : Nat → List UInt8) (hb3 : 3 ≤ b) (hi : i.toNat < shr)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < shr → readBytes mem (b + 64 * j) 64 = some (doc j)) :
    readBytes mem (b + 64 * i.toNat - 1) 32 = some (FusedWindows.bs41
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) ∧
      readBytes mem (b + 64 * i.toNat - 2) 32 = some (FusedWindows.bs42
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) ∧
      readBytes mem (b + 64 * i.toNat - 3) 32 = some (FusedWindows.bs43
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) ∧
      readBytes mem (b + 64 * i.toNat + 31) 32 = some (FusedWindows.bs57
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) ∧
      readBytes mem (b + 64 * i.toNat + 30) 32 = some (FusedWindows.bs58
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) ∧
      readBytes mem (b + 64 * i.toNat + 29) 32 = some (FusedWindows.bs59
        (fused_windows mem b shr i doc hb3 hi hzero hdoc)) :=
  let hw := fused_windows mem b shr i doc hb3 hi hzero hdoc
  ⟨hw.w41, hw.w42, hw.w43, hw.w57, hw.w58, hw.w59⟩

/-! ### The charge

The ASCII phase charges three per block plus four; the fused loop charges five
per remaining page plus five.  `%shr` is the entry's `n >>> 6`, and the peel's
slot is the last block exactly when the length is not block-aligned, which is
`shr + 1 = blocksOf`. -/

/-- **The charge sum at the unaligned exit.**  With `shr + 1` the document's
block count, the phase's and the loop's charges together are below the budget. -/
theorem entry_charge_sum (bs : List UInt8) (shr i : Nat)
    (hi : i + 1 ≤ shr) (hblocks : shr + 1 = blocksOf bs.length) :
    3 * (blocksOf bs.length - 1) + 4 + 5 * (shr - (i + 1)) + 5 ≤
      8 * blocksOf bs.length + 32 := by
  omega

/-- **The entry's charge at `shr = n >>> 6`.**  A document that leaves a partial
block has `shr + 1` blocks, and `%shr` is the entry's shift of the length. -/
theorem entry_charge (n : BitVec 64) (bs : List UInt8) (shr i : Nat)
    (hn : n.toNat = bs.length) (hshr : shr = (n >>> 6).toNat)
    (hi : i + 1 ≤ shr) (hmod : n.toNat % 64 ≠ 0) :
    3 * (blocksOf bs.length - 1) + 4 + 5 * (shr - (i + 1)) + 5 ≤
      8 * blocksOf bs.length + 32 := by
  have hblocks : shr + 1 = blocksOf bs.length := by
    rw [hshr, ← hn]
    exact ushr_six_succ_eq_blocksOf n hmod
  exact entry_charge_sum bs shr i hi hblocks

/-- **The entry's charge at the loop's own run bound.**  `fusedInv_runFuel`
charges at most `5 * (shr - (i + 1)) + 5`; with the phase's term the unit is
inside `8 * blocksOf n + 32`. -/
theorem entry_run_charge (n : BitVec 64) (bs : List UInt8) (shr i j : Nat)
    (hn : n.toNat = bs.length) (hshr : shr = (n >>> 6).toNat)
    (hi : i + 1 ≤ shr) (hmod : n.toNat % 64 ≠ 0)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5) :
    3 * (blocksOf bs.length - 1) + 4 + j ≤ 8 * blocksOf bs.length + 32 := by
  have := entry_charge n bs shr i hn hshr hi hmod
  omega

/-! ### Axiom footprints

The entry steps are the blocks' own `step` equations and the loop's page and
latch lemmas; the exit ties are `JsonS1BlocksExit`'s block run at the fused
registers; the charge is arithmetic.  The arm and seed theorems report `propext`,
`Classical.choice` and `Quot.sound`: the two-valued branch case split and the
latch lemmas carry the choice principle.  The exit ties, the row-window statement
and the charge report `propext` and `Quot.sound` only.  No statement reaches a
`sorryAx`. -/

#print axioms lookupName_fb54PageEnv_shr
#print axioms lookupName_fb54PageEnv_xp
#print axioms lookupName_fb54PageEnv_nxp
#print axioms lookupName_fb54PageEnv_xcarry
#print axioms lookupName_entryEnv_shr
#print axioms lookupName_entryEnv_xp
#print axioms lookupName_entryEnv_nxp
#print axioms lookupName_entryEnv_xcarry
#print axioms lookupName_entryEnv_b
#print axioms lookupName_entryEnv_ent
#print axioms lookupName_entryEnv_gate
#print axioms lookupName_entryEnv_escape
#print axioms entry_dfa_skip_arm
#print axioms entry_dfa_escape_arm
#print axioms entry_first_page_latch
#print axioms entry_first_page
#print axioms entry_first_page_loop
#print axioms entry_first_page_exit
#print axioms entry_first_row
#print axioms fused_end_phi_selects
#print axioms fused_end_denote
#print axioms lookupName_forEnd101OutOf_of
#print axioms fused_end_out_carries
#print axioms fused_end_peel_denote
#print axioms fused_end_staging
#print axioms entry_charge_sum
#print axioms entry_charge
#print axioms entry_run_charge

end LeanLLVM.Refinement.JsonS1BlocksEntry
