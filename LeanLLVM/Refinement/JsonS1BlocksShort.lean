/-
The short document's arm: `entry` → `if.end50` → `for.end101` → the aligned exit
or the peel, and the unit's return.

A document below one block (sixty-four bytes) never enters the ASCII phase: the
entry's length test leaves for `if.end50`, whose phis select the constants — the
zero carried state, the set carried byte, the zero accumulator and ASCII word,
and the zero index — and whose bound test is `0 < n >>> 6`, clear because the
document is below one block.  `for.end101` merges those seven constants, tests
the length's remainder (the whole length, `n < 64`), and leaves for `if.end153`
when the document is empty or for the peel at `if.then103` otherwise.

This module states the three denotations the composition consumes, each at its
own instruction list:

* `if_end50_entry_denote` — `if.end50`'s run at `pre = "entry"`, with the output
  `ifEnd50EntryOut` (the phis' constants over the caller's environment);
* `for_end101_join_denote` — `for.end101`'s run at `pre = "if.end50"`, with the
  block's seven phi cells read at the join's output;
* `for_end101_peel_denote_short` — `if.then103`'s run at that edge, with
  `ifThen103Values` at the join's own cells and the set carried byte.

It then composes: `s1BlocksShort_empty_run` (the empty document through
`if.end153`) and `s1BlocksShort_peel_run` (a non-empty short document through
the peel and the silent merge), each a `runFuel` prefix ending at the unit's
return with the post's verdict clause; `s1BlocksShort_run` is the length's case
split.

## What remains

The runs stop at the boundary the tail's own runs consume, so the pieces below
are explicit hypotheses rather than weakened conclusions:

* **The staging.**  The short arm carries no non-ASCII byte and no error of its
  own: `%ascii` and `%u8k` are the zero lanes the phis select.  Whether the zero
  lanes stage the caller's document — `VerdictStaging`'s three fields — is the
  loop's model carry (`JsonS1BlocksStaging`), not the short arm's trace; the two
  runs take the staging as a premise, exactly as the exit compositions do.
* **The peel's verdict.**  `%or.cond191` is the peel's own classification of the
  last block, so its being set (`hsilent`) is a hypothesis.  The peel's other
  exit (`if.then144`) is the partial tail's own windows: it is taken when the
  merge's test `%or.cond191` is clear (the gate's `%conv` nonzero, the high-bit
  probe zero, or the carried byte zero), and that arm is not stated here.
* **The windows.**  The two 32-byte reads at `b` and `b + 32` are the peel's
  block.  Deriving them from `s1BlocksPre`'s padded window is
  `for_end101_peel_last_block` at the peel's index zero, and it is not restated.
* **The post's memory conjuncts.**  The entry array's prefix, the escape stream,
  the count and the four-region frame (`JsonS1BlocksRecordFrame`,
  `JsonS1BlocksCompose`) are the run's memory obligations; these runs state the
  verdict clause (`VerdictPost`), which is what the return word carries.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksCompose
import LeanLLVM.Refinement.JsonEscapeDecodeRun
import LeanLLVM.Refinement.JsonEscapeListBody

namespace LeanLLVM.Refinement.JsonS1BlocksShort

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- The entry's environment at the block unit's own module, named here so the
short arm's environments are read at the right `entryEnv`. -/
abbrev shortEntryEnv (env : Env) (n arm : BitVec 64) : Env :=
  LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm

/-! ### The unit's start at the seven slots

The composition is stated over the argument vector the entry's own step reads, so
the initial environment is the caller's `initState` at those values. -/

/-- The unit's initial state at the seven ABI slots. -/
abbrev shortStart (mem : Mem) (b ent xp nxp xcarry : Nat) (n arm : BitVec 64) : State :=
  s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
    .int 64 arm] mem

/-- The initial environment at those slots. -/
abbrev shortStartEnv (mem : Mem) (b ent xp nxp xcarry : Nat) (n arm : BitVec 64) : Env :=
  (shortStart mem b ent xp nxp xcarry n arm).env

/-! ### `if.end50` at `pre = "entry"`

The join's eight phis select the constants the entry edge carries, and the
block's comparison asks whether the successor index `0` is inside the bound. -/

/-- `if.end50`'s output at the entry edge: the phis' constants and the bound.
The hand-off's output (`JsonS1BlocksRefine.ifEnd50Out`) is the same shape but
carries `%prev_ascii.0 = 0`; the entry arm carries `1`, since no byte preceded
the document, so the two edges cannot share that cell. -/
def ifEnd50EntryOut (env : Env) (shr : BitVec 64) : Env :=
  cells [("%cmp52516", .int 1 (evalICmp .ult 0 shr)),
         ("%i.1", .int 64 0),
         ("%ascii.0", .vec 4 64 (List.replicate 4 0)),
         ("%u8k.0", .vec 4 64 (List.replicate 4 0)),
         ("%prev_ascii.0", .int 32 1),
         ("%st.sroa.15.1485", .int 64 0),
         ("%st.sroa.9.1487", .int 64 0),
         ("%st.sroa.0.1489", .int 64 0),
         ("%prevS.1491", .int 64 0)] env

/-- The carried ASCII word, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_ascii (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%ascii.0"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The carried accumulator, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_u8k (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%u8k.0"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The carried byte, as the entry edge writes it: set, since no byte preceded. -/
theorem lookupName_ifEnd50EntryOut_prevAscii (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%prev_ascii.0" = some (.int 32 1) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The third carried word, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_st15 (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%st.sroa.15.1485" = some (.int 64 0) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The second carried word, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_st9 (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%st.sroa.9.1487" = some (.int 64 0) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The first carried word, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_st0 (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%st.sroa.0.1489" = some (.int 64 0) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- The shift register, as the join writes it. -/
theorem lookupName_ifEnd50EntryOut_prevS (env : Env) (shr : BitVec 64) :
    lookupName (ifEnd50EntryOut env shr) "%prevS.1491" = some (.int 64 0) := by
  simp only [ifEnd50EntryOut, cells]
  block_lk_cons

/-- A register read through the join's nine cells to the environment beneath
them. -/
theorem lookupName_ifEnd50EntryOut_of (env : Env) (shr : BitVec 64) {k : String}
    {v : Value} (h : lookupName env k = some v)
    (h1 : "%cmp52516" ≠ k) (h2 : "%i.1" ≠ k) (h3 : "%ascii.0" ≠ k)
    (h4 : "%u8k.0" ≠ k) (h5 : "%prev_ascii.0" ≠ k) (h6 : "%st.sroa.15.1485" ≠ k)
    (h7 : "%st.sroa.9.1487" ≠ k) (h8 : "%st.sroa.0.1489" ≠ k)
    (h9 : "%prevS.1491" ≠ k) :
    lookupName (ifEnd50EntryOut env shr) k = some v := by
  simp only [ifEnd50EntryOut, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4, lookupName_cons_ne _ _ h5, lookupName_cons_ne _ _ h6,
    lookupName_cons_ne _ _ h7, lookupName_cons_ne _ _ h8, lookupName_cons_ne _ _ h9]
  exact h

/-- **`if.end50`'s run at `pre = "entry"`.** -/
theorem if_end50_entry_denote (env : Env) (s : State) (shr : BitVec 64)
    (hpre : s.pre = some "entry")
    (hshr : lookupName env "%shr" = some (.int 64 shr)) :
    denoteCode s1BlocksCalls if_end50Instrs (stateAt env s) =
      some (stateAt (ifEnd50EntryOut env shr) s) := by
  simp only [if_end50Instrs, ifEnd50EntryOut]
  block_eval_c

/-- **`if.end50`'s step to the bound's block on a short document.**  The
successor index `0` is not inside the bound when the bound is zero, and the entry
edge only reaches the join when it is. -/
theorem if_end50_step_short {esc : Calls} (env : Env) (s : State) (shr : BitVec 64)
    (hpc : s.pc = "if.end50")
    (hpre : s.pre = some "entry")
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hbit : evalICmp .ult 0 shr = 0) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd50EntryOut env shr)
        { s with pc := "for.end101", pre := some "if.end50" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end50Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end50
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  rw [step_at hfind (if_end50_entry_denote env s shr hpre hshr)]
  rw [show if_end50Block.term = if_end50Term from rfl]
  simp only [if_end50Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      simp only [ifEnd50EntryOut, cells, lookupName_cons_self])) hbit]
  simp only [stateAt, hpc]

/-! ### The entry environment's remainder

The bound's block's test is the entry's `%and`, which the join's cells carry
beneath them. -/

/-- The entry's remainder cell, `%and = n &&& 63`. -/
theorem lookupName_entryEnv_and (env : Env) (n arm : BitVec 64) :
    lookupName (shortEntryEnv env n arm) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [shortEntryEnv, LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-! ### `for.end101` at `pre = "if.end50"`

The block merges whatever the join's cells hold, so the denotation is stated at
the seven selected values; the short arm instantiates them at the phis'
constants. -/

/-- **`for.end101`'s run at `pre = "if.end50"`.** -/
theorem for_end101_join_denote (env : Env) (s : State)
    (prevS st0 st9 st15 andv : BitVec 64) (prevAscii : BitVec 32)
    (ascii u8k : List (BitVec 64))
    (hpre : s.pre = some "if.end50")
    (hprevS : lookupName env "%prevS.1491" = some (.int 64 prevS))
    (hst0 : lookupName env "%st.sroa.0.1489" = some (.int 64 st0))
    (hst9 : lookupName env "%st.sroa.9.1487" = some (.int 64 st9))
    (hst15 : lookupName env "%st.sroa.15.1485" = some (.int 64 st15))
    (hprevAscii : lookupName env "%prev_ascii.0" = some (.int 32 prevAscii))
    (hu8k : lookupName env "%u8k.0" = some (.vec 4 64 u8k))
    (hascii : lookupName env "%ascii.0" = some (.vec 4 64 ascii))
    (hand : lookupName env "%and" = some (.int 64 andv)) :
    denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv) s) := by
  simp only [for_end101Instrs, forEnd101OutOf]
  block_eval_b

/-- **`for.end101`'s step to the aligned exit.** -/
theorem for_end101_step_join_aligned {esc : Calls} (env : Env) (s : State)
    (prevS st0 st9 st15 andv : BitVec 64) (prevAscii : BitVec 32)
    (ascii u8k : List (BitVec 64))
    (hpc : s.pc = "for.end101")
    (hpre : s.pre = some "if.end50")
    (hprevS : lookupName env "%prevS.1491" = some (.int 64 prevS))
    (hst0 : lookupName env "%st.sroa.0.1489" = some (.int 64 st0))
    (hst9 : lookupName env "%st.sroa.9.1487" = some (.int 64 st9))
    (hst15 : lookupName env "%st.sroa.15.1485" = some (.int 64 st15))
    (hprevAscii : lookupName env "%prev_ascii.0" = some (.int 32 prevAscii))
    (hu8k : lookupName env "%u8k.0" = some (.vec 4 64 u8k))
    (hascii : lookupName env "%ascii.0" = some (.vec 4 64 ascii))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hbit : evalICmp .eq andv 0 = 1) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
        { s with pc := "if.end153", pre := some "for.end101" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_end101Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  rw [step_at hfind (for_end101_join_denote env s prevS st0 st9 st15 andv prevAscii
    ascii u8k hpre hprevS hst0 hst9 hst15 hprevAscii hu8k hascii hand)]
  rw [show for_end101Block.term = for_end101Term from rfl]
  simp only [for_end101Term]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _
      (for_end101_tobool102_not env prevS ascii u8k prevAscii st0 st9 st15 andv)) hbit]
  simp only [stateAt, hpc]

/-- **`for.end101`'s step to the peel.** -/
theorem for_end101_step_join_peel {esc : Calls} (env : Env) (s : State)
    (prevS st0 st9 st15 andv : BitVec 64) (prevAscii : BitVec 32)
    (ascii u8k : List (BitVec 64))
    (hpc : s.pc = "for.end101")
    (hpre : s.pre = some "if.end50")
    (hprevS : lookupName env "%prevS.1491" = some (.int 64 prevS))
    (hst0 : lookupName env "%st.sroa.0.1489" = some (.int 64 st0))
    (hst9 : lookupName env "%st.sroa.9.1487" = some (.int 64 st9))
    (hst15 : lookupName env "%st.sroa.15.1485" = some (.int 64 st15))
    (hprevAscii : lookupName env "%prev_ascii.0" = some (.int 32 prevAscii))
    (hu8k : lookupName env "%u8k.0" = some (.vec 4 64 u8k))
    (hascii : lookupName env "%ascii.0" = some (.vec 4 64 ascii))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hbit : evalICmp .eq andv 0 = 0) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
        { s with pc := "if.then103", pre := some "for.end101" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_end101Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  rw [step_at hfind (for_end101_join_denote env s prevS st0 st9 st15 andv prevAscii
    ascii u8k hpre hprevS hst0 hst9 hst15 hprevAscii hu8k hascii hand)]
  rw [show for_end101Block.term = for_end101Term from rfl]
  simp only [for_end101Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _
      (for_end101_tobool102_not env prevS ascii u8k prevAscii st0 st9 st15 andv)) hbit]
  simp only [stateAt, hpc]

/-! ### The join's output, instantiated at the entry edge

The short arm's peel entry is the join's output at the entry's constants: the
zero carried state, the set carried byte, the zero words, and `%and`. -/

/-- The environment the short arm hands the peel. -/
abbrev shortJoinEnv (env : Env) (n arm : BitVec 64) : Env :=
  forEnd101OutOf (ifEnd50EntryOut (shortEntryEnv env n arm) (n >>> 6))
    (0 : BitVec 64) (List.replicate 4 0) (List.replicate 4 0) (1 : BitVec 32)
    0 0 0 (n &&& 63)

/-- The peel's carried byte, as the join selects it. -/
theorem lookupName_shortJoinEnv_prevAscii (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%prev_ascii.1.lcssa" = some (.int 32 1) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The peel's shift register, as the join selects it. -/
theorem lookupName_shortJoinEnv_prevS (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%prevS.2.lcssa" = some (.int 64 0) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The peel's first carried word, as the join selects it. -/
theorem lookupName_shortJoinEnv_st0 (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%st.sroa.0.2.lcssa" = some (.int 64 0) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The peel's second carried word, as the join selects it. -/
theorem lookupName_shortJoinEnv_st9 (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%st.sroa.9.2.lcssa" = some (.int 64 0) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The peel's third carried word, as the join selects it. -/
theorem lookupName_shortJoinEnv_st15 (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%st.sroa.15.2.lcssa" = some (.int 64 0) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The staging's ASCII word, as the join selects it. -/
theorem lookupName_shortJoinEnv_ascii (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%ascii.1.lcssa"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The staging's accumulator, as the join selects it. -/
theorem lookupName_shortJoinEnv_u8k (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%u8k.1.lcssa"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The entry's remainder, through the join's cells and the bound's. -/
theorem lookupName_shortJoinEnv_and (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The bound, through the join's cells. -/
theorem lookupName_shortJoinEnv_shr (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The gate bit, through the join's cells. -/
theorem lookupName_shortJoinEnv_conv (env : Env) (n arm : BitVec 64) :
    lookupName (shortJoinEnv env n arm) "%conv" = some (.int 32 (entryGate arm)) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The caller's length, through the join's cells. -/
theorem lookupName_shortJoinEnv_n (env : Env) (n arm : BitVec 64)
    {x : BitVec 64} (h : lookupName env "%n" = some (.int 64 x)) :
    lookupName (shortJoinEnv env n arm) "%n" = some (.int 64 x) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The block's base, through the join's cells. -/
theorem lookupName_shortJoinEnv_b (env : Env) (n arm : BitVec 64)
    {b : Nat} (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (shortJoinEnv env n arm) "%b" = some (.ptr b) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The emit base, through the join's cells. -/
theorem lookupName_shortJoinEnv_ent (env : Env) (n arm : BitVec 64)
    {ent : Nat} (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (shortJoinEnv env n arm) "%ent" = some (.ptr ent) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-- The caller's arm, through the join's cells. -/
theorem lookupName_shortJoinEnv_arm (env : Env) (n arm : BitVec 64)
    {a : BitVec 64} (h : lookupName env "%arm" = some (.int 64 a)) :
    lookupName (shortJoinEnv env n arm) "%arm" = some (.int 64 a) := by
  simp only [shortJoinEnv, forEnd101OutOf, ifEnd50EntryOut, shortEntryEnv,
    LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

/-! ### The peel at that edge

`if.then103`'s twelve segments run at the join's output with the model's values
at its cells: the caller's length and pointers, the four carried words the phis
selected, the ASCII word and carried byte the constants carry, and `%and`. -/

/-- **`if.then103`'s run from the entry edge's join.** -/
theorem for_end101_peel_denote_short (env : Env) (s : State)
    (n arm : BitVec 64) (b ent : Nat) (bs136 bs137 : List UInt8)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshrPos : ((n >>> 6).signExtend 64).toNat < 2 ^ 63) :
    denoteCode s1BlocksCalls if_then103Instrs
        (stateAt (shortJoinEnv env n arm)
          { s with pc := "if.then103", pre := some "for.end101" }) =
      some (stateAt (ifThen103Out (shortJoinEnv env n arm)
          (ifThen103Values n b bs136 bs137 (List.replicate 4 0) 0 0 0 0
            (n &&& 63) (n >>> 6) ent (entryGate arm) 1))
        { s with
          pc := "if.then103",
          pre := some "for.end101",
          mem := writeBytes s.mem
            (ifThen103Values n b bs136 bs137 (List.replicate 4 0) 0 0 0 0
              (n &&& 63) (n >>> 6) ent (entryGate arm) 1).arrayidx
            (natToBytes (ifThen103Values n b bs136 bs137 (List.replicate 4 0) 0 0 0 0
              (n &&& 63) (n >>> 6) ent (entryGate arm) 1).and137.toNat 8) }) := by
  exact if_then103_denote (shortJoinEnv env n arm)
    { s with pc := "if.then103", pre := some "for.end101" }
    n b bs136 bs137 (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent
    (entryGate arm) 1
    (lookupName_shortJoinEnv_n env n arm hn)
    (lookupName_shortJoinEnv_b env n arm hb)
    (lookupName_shortJoinEnv_ascii env n arm)
    (by simp)
    hpos h136 h137
    (lookupName_shortJoinEnv_st0 env n arm)
    (lookupName_shortJoinEnv_st9 env n arm)
    (lookupName_shortJoinEnv_st15 env n arm)
    (lookupName_shortJoinEnv_prevS env n arm)
    (lookupName_shortJoinEnv_and env n arm)
    (lookupName_shortJoinEnv_ent env n arm hent)
    (lookupName_shortJoinEnv_shr env n arm)
    hshrPos
    (lookupName_shortJoinEnv_conv env n arm)
    (lookupName_shortJoinEnv_prevAscii env n arm)

/-! ### The short document's run to the return

The entry's step, the join's step, the bound's block's step, then the tail: the
empty document's aligned exit (two control steps) or the peel's silent merge
(four).  Both end at the unit's return; the post's verdict clause is the tail's
own.  The empty document's run is five control steps and the peel's seven. -/

/-- **The empty document: `entry` → `if.end50` → `for.end101` → `if.end153` →
the return.** -/
theorem s1BlocksShort_empty_run {esc : Calls} (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (nb : Nat) (gate : Bool)
    (hbit : evalICmp .ult n 64 = 1) (hzero : n = 0)
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0)) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction
        (shortStart mem b ent xp nxp xcarry n arm) = some (.ret (some (.int 64 r)) m) ∧
      VerdictPost r bs := by
  have hn64 : n.toNat < 64 := (evalICmp_ult_one_iff n 64).mp hbit
  have hshr0 : (n >>> 6) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [ushr_six_toNat]
    simpa using Nat.div_eq_of_lt hn64
  have hbit50 : evalICmp .ult (0 : BitVec 64) (n >>> 6) = 0 := by
    rw [hshr0]
    decide
  have hstep1 := s1BlocksInit_step_short (esc := esc) mem b ent xp nxp xcarry n arm hbit
  have hshrE : lookupName (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
      "%shr" = some (.int 64 (n >>> 6)) :=
    lookupName_entryEnv_shr _ _ _
  have hstep2 := if_end50_step_short (esc := esc)
    (env := shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
    (s := { shortStart mem b ent xp nxp xcarry n arm with
              pc := "if.end50", pre := some "entry" })
    (shr := n >>> 6) rfl rfl hshrE hbit50
  have hand : lookupName
      (ifEnd50EntryOut (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
        (n >>> 6)) "%and" = some (.int 64 (n &&& 63)) :=
    lookupName_ifEnd50EntryOut_of _ _
      (lookupName_entryEnv_and _ _ _) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbit101 : evalICmp .eq (n &&& 63) 0 = 1 := by
    rw [hzero]
    decide
  have hstep3 := for_end101_step_join_aligned (esc := esc)
    (env := ifEnd50EntryOut (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
      (n >>> 6))
    (s := { shortStart mem b ent xp nxp xcarry n arm with
              pc := "for.end101", pre := some "if.end50" })
    (prevS := 0) (st0 := 0) (st9 := 0) (st15 := 0) (andv := n &&& 63)
    (prevAscii := 1) (ascii := List.replicate 4 0) (u8k := List.replicate 4 0)
    rfl rfl
    (lookupName_ifEnd50EntryOut_prevS _ _)
    (lookupName_ifEnd50EntryOut_st0 _ _)
    (lookupName_ifEnd50EntryOut_st9 _ _)
    (lookupName_ifEnd50EntryOut_st15 _ _)
    (lookupName_ifEnd50EntryOut_prevAscii _ _)
    (lookupName_ifEnd50EntryOut_u8k _ _)
    (lookupName_ifEnd50EntryOut_ascii _ _)
    hand hbit101
  have hbitN : evalICmp .eq n 0 = 1 := by
    rw [hzero]
    decide
  have htail := tail_aligned_run (esc := esc)
    (env := shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
    (s := { shortStart mem b ent xp nxp xcarry n arm with
              pc := "if.end153", pre := some "for.end101" })
    (n := n) (u8k := List.replicate 4 0) (ascii := List.replicate 4 0)
    (bs := bs) (nb := nb) (gate := gate)
    rfl
    (lookupName_shortJoinEnv_n _ _ _
      (s1BlocksInit_env_n mem b ent xp nxp xcarry n arm))
    (lookupName_shortJoinEnv_u8k _ _ _)
    (lookupName_shortJoinEnv_ascii _ _ _)
    hbitN hstage
  refine ⟨1 + (1 + (1 + 2)), verdictWord (List.replicate 4 0)
      (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0), mem, ?_, htail.2⟩
  rw [runFuel_jump_prefix hstep1 (1 + (1 + 2)),
    runFuel_jump_prefix hstep2 (1 + 2),
    runFuel_jump_prefix hstep3 2]
  exact htail.1

/-- **The non-empty short document: `entry` → `if.end50` → `for.end101` →
`if.then103` → `if.end147` → the return.** -/
theorem s1BlocksShort_peel_run {esc : Calls} (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (nb : Nat) (gate : Bool)
    (bs136 bs137 : List UInt8)
    (hbit : evalICmp .ult n 64 = 1) (hne : n ≠ 0)
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (h136 : readBytes mem b 32 = some bs136)
    (h137 : readBytes mem (b + 32) 32 = some bs137)
    (hsilent : ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      lookupName (ifThen103Out
        (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v)
        "%or.cond191" = some (.int 1 1))
    (hstage : ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0)) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction
        (shortStart mem b ent xp nxp xcarry n arm) = some (.ret (some (.int 64 r)) m) ∧
      VerdictPost r bs := by
  have hn64 : n.toNat < 64 := (evalICmp_ult_one_iff n 64).mp hbit
  have hshr0 : (n >>> 6) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [ushr_six_toNat]
    simpa using Nat.div_eq_of_lt hn64
  have hbit50 : evalICmp .ult (0 : BitVec 64) (n >>> 6) = 0 := by
    rw [hshr0]
    decide
  -- the peel's mask clears the whole length
  have hsign0 : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat = 0 := by
    rw [signExtend_self_toNat, and_high_mask_toNat]
    have h : n.toNat / 64 = 0 := Nat.div_eq_of_lt hn64
    rw [h, Nat.mul_zero]
  have hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63 := by
    rw [hsign0]
    decide
  have hshrPos : ((n >>> 6).signExtend 64).toNat < 2 ^ 63 := by
    rw [hshr0, signExtend_self_toNat]
    decide
  have h136' : readBytes mem
      (b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136 := by
    rw [hsign0]
    simpa using h136
  have h137' : readBytes mem
      ((b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137 := by
    have hproj : ((0x0000000000000020#64).signExtend 64).toNat = 32 := by
      rw [signExtend_self_toNat]
      decide
    rw [hsign0, hproj]
    simpa using h137
  have hstep1 := s1BlocksInit_step_short (esc := esc) mem b ent xp nxp xcarry n arm hbit
  have hshrE : lookupName (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
      "%shr" = some (.int 64 (n >>> 6)) :=
    lookupName_entryEnv_shr _ _ _
  have hstep2 := if_end50_step_short (esc := esc)
    (env := shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
    (s := { shortStart mem b ent xp nxp xcarry n arm with
              pc := "if.end50", pre := some "entry" })
    (shr := n >>> 6) rfl rfl hshrE hbit50
  have hand : lookupName
      (ifEnd50EntryOut (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
        (n >>> 6)) "%and" = some (.int 64 (n &&& 63)) :=
    lookupName_ifEnd50EntryOut_of _ _
      (lookupName_entryEnv_and _ _ _) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have handN : (n &&& 63 : BitVec 64) = n := by
    apply BitVec.eq_of_toNat_eq
    have h : (n &&& 63).toNat = n.toNat % 64 := and_sixtythree_toNat n
    rw [h, Nat.mod_eq_of_lt hn64]
  have hbit101 : evalICmp .eq (n &&& 63) 0 = 0 := by
    rw [handN]
    exact (evalICmp_eq_zero_iff n 0).mpr hne
  have hstep3 := for_end101_step_join_peel (esc := esc)
    (env := ifEnd50EntryOut (shortEntryEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
      (n >>> 6))
    (s := { shortStart mem b ent xp nxp xcarry n arm with
              pc := "for.end101", pre := some "if.end50" })
    (prevS := 0) (st0 := 0) (st9 := 0) (st15 := 0) (andv := n &&& 63)
    (prevAscii := 1) (ascii := List.replicate 4 0) (u8k := List.replicate 4 0)
    rfl rfl
    (lookupName_ifEnd50EntryOut_prevS _ _)
    (lookupName_ifEnd50EntryOut_st0 _ _)
    (lookupName_ifEnd50EntryOut_st9 _ _)
    (lookupName_ifEnd50EntryOut_st15 _ _)
    (lookupName_ifEnd50EntryOut_prevAscii _ _)
    (lookupName_ifEnd50EntryOut_u8k _ _)
    (lookupName_ifEnd50EntryOut_ascii _ _)
    hand hbit101
  -- the peel's own run at the join's output
  let A : State := stateAt (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
    { shortStart mem b ent xp nxp xcarry n arm with
      pc := "if.then103", pre := some "for.end101" }
  let v : IfThen103Values := ifThen103Values n b bs136 bs137 (List.replicate 4 0)
    0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1
  have hden : denoteCode s1BlocksCalls if_then103Instrs A =
      some (stateAt (ifThen103Out (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm)
        n arm) v)
        { shortStart mem b ent xp nxp xcarry n arm with
          pc := "if.then103", pre := some "for.end101",
          mem := writeBytes mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
    simpa only [A, shortStart, s1BlocksInit, v] using
      for_end101_peel_denote_short
        (shortStartEnv mem b ent xp nxp xcarry n arm)
        { shortStart mem b ent xp nxp xcarry n arm with
            pc := "if.then103", pre := some "for.end101" }
        n arm b ent bs136 bs137
        (s1BlocksInit_env_n mem b ent xp nxp xcarry n arm)
        (s1BlocksInit_env_b mem b ent xp nxp xcarry n arm)
        (s1BlocksInit_env_ent mem b ent xp nxp xcarry n arm)
        hpos h136' h137' hshrPos
  have hbn : lookupName (ifThen103Out
      (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v)
      "%or.cond191" = some (.int 1 1) := hsilent v rfl
  have hstep4 : step (s1BlocksCallsEsc esc) s1BlocksFunction A =
      .jump (stateAt (ifThen103Out
        (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v)
        { shortStart mem b ent xp nxp xcarry n arm with
          mem := writeBytes mem v.arrayidx (natToBytes v.and137.toNat 8),
          pc := "if.end147", pre := some "if.then103" }) := by
    have hfind103 : s1BlocksFunction.findBlock A.pc = some if_then103Block := by
      rw [show A.pc = "if.then103" from rfl]
      exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
    rw [step_esc_of_free esc s1BlocksFunction _ _ hfind103 (by decide)]
    exact if_then103_step_end147 _ A v rfl hbn hden
  have htail := tail_silent_run (esc := esc)
    (env := shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm)
    A v (List.replicate 4 0) arm bs bs.length nb gate
    (lookupName_ifThen103Out_u8k
      (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v
      (lookupName_shortJoinEnv_u8k (shortStartEnv mem b ent xp nxp xcarry n arm) n arm))
    (lookupName_ifThen103Out_arm
      (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v
      (lookupName_shortJoinEnv_arm (shortStartEnv mem b ent xp nxp xcarry n arm) n arm
        (s1BlocksInit_env_arm mem b ent xp nxp xcarry n arm)))
    hgate
    (hstage v rfl)
  refine ⟨1 + (1 + (1 + (1 + 3))), verdictWord v.or279
      (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0),
    writeBytes mem v.arrayidx (natToBytes v.and137.toNat 8), ?_, htail.2⟩
  rw [runFuel_jump_prefix hstep1 (1 + (1 + (1 + 3))),
    runFuel_jump_prefix hstep2 (1 + (1 + 3)),
    runFuel_jump_prefix hstep3 (1 + 3),
    runFuel_jump_prefix hstep4 3]
  exact htail.1

/-- **The short document's composed run to the return.**  A document below one
block leaves the entry for the join, whose bound test is clear; the bound's block
then takes the aligned exit when the document is empty and the peel when it is
not.  Both reach the unit's return with the post's verdict clause. -/
theorem s1BlocksShort_run {esc : Calls} (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (nb : Nat) (gate : Bool)
    (bs136 bs137 : List UInt8)
    (hbit : evalICmp .ult n 64 = 1)
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (h136 : readBytes mem b 32 = some bs136)
    (h137 : readBytes mem (b + 32) 32 = some bs137)
    (hsilent : ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      lookupName (ifThen103Out
        (shortJoinEnv (shortStartEnv mem b ent xp nxp xcarry n arm) n arm) v)
        "%or.cond191" = some (.int 1 1))
    (hstageEmpty : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs
      bs.length nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0)) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction
        (shortStart mem b ent xp nxp xcarry n arm) = some (.ret (some (.int 64 r)) m) ∧
      VerdictPost r bs := by
  by_cases hzero : n = 0
  · exact s1BlocksShort_empty_run mem b ent xp nxp xcarry n arm bs nb gate
      hbit hzero hstageEmpty
  · exact s1BlocksShort_peel_run mem b ent xp nxp xcarry n arm bs nb gate bs136 bs137
      hbit hzero hgate h136 h137 hsilent hstagePeel

/-! ### Axiom footprints

The denotations are the blocks' own `denoteCode` equations (`block_eval_b` /
`block_eval_c`), the steps are their terminators at the computed cells, and the
runs compose them with `runFuel`'s prefix rule.  The statements below carry no
`sorryAx`; their footprints are the modules they consume. -/

#print axioms lookupName_ifEnd50EntryOut_of
#print axioms if_end50_entry_denote
#print axioms if_end50_step_short
#print axioms for_end101_join_denote
#print axioms for_end101_step_join_aligned
#print axioms for_end101_step_join_peel
#print axioms lookupName_shortJoinEnv_and
#print axioms for_end101_peel_denote_short
#print axioms s1BlocksShort_empty_run
#print axioms s1BlocksShort_peel_run
#print axioms s1BlocksShort_run

end LeanLLVM.Refinement.JsonS1BlocksShort
