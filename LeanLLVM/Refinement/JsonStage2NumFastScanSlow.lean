/-
The fallback's second reader: the inlined `num_scan`'s block chain.

`num_fast_el1`'s fallback is reached at `if.end285` and is the inlined second
reader — the counters' bump, the sign's index, the integer digits, the fraction,
the exponent's marker and sign, the exponent's digits, and the handoff to the
inlined `to_double` at `for.body.outer.i.outer.i`.  `JsonStage2NumFastArm` names
this chain as the region's first missing link and `JsonStage2NumFastTier3` stops
at its poison edge, so the reader's blocks are stated here at the emitted block's
own `findBlock` pin.

**What each block contributes.**  The reader's state is the lexeme's `%p` and
`%n`, the caller's memory, the `to_double` digit array's base `%dig.i.i` (the
`entry` block's first allocation), the sign's index `%i.0.i` and the sign bit
`%cmp1.i`.  `if.end285` computes the last two and re-carrys the first three
(`slCarry`); every later block adds the cells it binds in front of the
environment its predecessor left.  The blocks are stated one edge at a time, as
`JsonStage2NumFastTier3CopySteps` states the copy's: each block's `denoteCode` at
the edge its predecessor delivered, and the `step` that edge takes.  A block
with two in-edges has one `denote` per predecessor, because a `phi`'s taken
incoming is a function of `s.pre`.

**The digit loops.**  Three loops consume digits — the integer part
(`land.lhs.true25.i`/`while.body.i`), the fraction
(`land.lhs.true63.i`/`while.body74.i`) and the exponent
(`land.lhs.true124.i`/`while.body135.i`).  Each is two blocks per digit: the
head's digit test and the body's cursor bump and end-of-lexeme test, so a loop
leaves *either* for the next stage (a non-digit) *or* for `if.then143.i` (the
digits ran to the lexeme's end).  Both blocks' edges are stated here at both
outcomes, so a digit list's traversal is one induction over these steps; that
induction is not stated in this module, and the arm's "scan's shape" hypothesis
is what carries it — the same division of labour as
`JsonStage2NumFastTier3CopyUnroll`'s visit count.  The module's last section
says so rather than assuming the run.

**The handoff.**  `if.then143.i` starts the 768-byte digit array's lifetime and
jumps to `for.body.outer.i.outer.i`, whose leading `phi` run — ten members —
carries the cells the copy takes: the array's base `%dig.i.i`, the sign's index
`%i.0.i` as the copy's digit index, and zeros for the accumulated mantissa, the
fraction and exponent counters, the leading digits and the seen/sticky flags.
`sl_entry_denote` is that run at its pin, so the copy's `F`/`T` parse reads the
digits the scan wrote and nothing else.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3
import LeanLLVM.Refinement.JsonStage2NumFastClass
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopySteps
import LeanLLVM.Refinement.JsonStage2NumFastSign
import LeanLLVM.Refinement.JsonS1MasksIR
import LeanLLVM.Refinement.JsonStage2HelperIRNumFast

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane

namespace NumFastScanSlow

/-! ### The five cells the reader never writes again -/

/-- The carried cells: the lexeme's bytes, the digit array's base, and the sign's
index and test. -/
def slCarry (env : Env) (p : Nat) (n i0 : BitVec 64) (sgn : BitVec 1) (digA : Nat) : Env :=
  ("%p", .ptr p) :: ("%n", .int 64 n) :: ("%i.0.i", .int 64 i0) ::
  ("%cmp1.i", .int 1 sgn) :: ("%dig.i.i", .ptr digA) :: env

/-- The first byte's sign test. -/
def slSignBit (b0 : UInt8) : BitVec 1 := evalICmp .eq (vByte b0) 0x2d#8

/-- The sign's index: the `zext` of the first byte's test. -/
def slSignIdx (b0 : UInt8) : BitVec 64 := BitVec.ofNat 64 (slSignBit b0).toNat

/-! ### The blocks' environments

Each is the cells the block binds, in front of the environment the edge
delivered.  A block's own `phi` cell is the edge's operand, so a block with two
in-edges has one builder per edge. -/

/-- `if.end285`'s environment. -/
def slEnv285 (env : Env) (p : Nat) (n : BitVec 64) (i0 : BitVec 64) (sgn : BitVec 1)
    (digA : Nat) (gv : BitVec 64) (b0 : UInt8) : Env :=
  ("%cmp3.not.i", .int 1 (evalICmp .ugt n (slSignIdx b0))) ::
  ("%i.0.i", .int 64 (slSignIdx b0)) ::
  ("%cmp1.i", .int 1 (slSignBit b0)) ::
  ("%38", .int 8 (vByte b0)) ::
  ("%inc287", .int 64 (gv + 1#64)) ::
  ("%37", .int 64 gv) ::
  slCarry env p n i0 sgn digA

/-- `if.end6.i`'s environment. -/
def slEnv6 (env : Env) (p : Nat) (i0 : BitVec 64) (b : UInt8) : Env :=
  ("%cmp9.i", .int 1 (evalICmp .eq (vByte b) 0x30#8)) ::
  ("%39", .int 8 (vByte b)) ::
  ("%arrayidx7.i", .ptr (p + (i0.signExtend 64).toNat)) :: env

/-- `if.then11.i`'s environment. -/
def slEnv11 (env : Env) (sgn : BitVec 1) : Env :=
  ("%inc12.i", .int 64 (if sgn = 1 then 2#64 else 1#64)) :: env

/-- `if.else.i`'s environment. -/
def slEnvElse (env : Env) (b : UInt8) : Env :=
  ("%or.cond.i", .int 1 (evalICmp .ult (vByte b + 0xcf#8) 0x09#8)) ::
  ("%40", .int 8 (vByte b + 0xcf#8)) :: env

/-- `if.end37.i`'s environment. -/
def slEnv37 (env : Env) (i2 n : BitVec 64) : Env :=
  ("%cmp38.i", .int 1 (evalICmp .ult i2 n)) :: ("%i.2.i", .int 64 i2) :: env

/-- `land.lhs.true25.i`'s environment. -/
def slEnv25 (env : Env) (p : Nat) (i : BitVec 64) (b : UInt8) : Env :=
  ("%or.cond222.i", .int 1 (evalICmp .ult (vByte b + 0xd0#8) 0x0a#8)) ::
  ("%42", .int 8 (vByte b + 0xd0#8)) ::
  ("%41", .int 8 (vByte b)) ::
  ("%arrayidx26.i", .ptr (p + (i.signExtend 64).toNat)) ::
  ("%i.1262.i", .int 64 i) :: env

/-- `while.body.i`'s environment. -/
def slEnvBody25 (env : Env) (i n : BitVec 64) : Env :=
  ("%exitcond.not.i", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc34.i", .int 64 (i + 1#64)) :: env

/-- `land.lhs.true40.i`'s environment. -/
def slEnv40 (env : Env) (p : Nat) (i2 : BitVec 64) (b : UInt8) : Env :=
  ("%cmp43.i", .int 1 (evalICmp .eq (vByte b) 0x2e#8)) ::
  ("%43", .int 8 (vByte b)) ::
  ("%arrayidx41.i", .ptr (p + (i2.signExtend 64).toNat)) :: env

/-- `if.then45.i`'s environment. -/
def slEnv45 (env : Env) (i2 n : BitVec 64) : Env :=
  ("%cmp47.not.i", .int 1 (evalICmp .ult (i2 + 1#64) n)) ::
  ("%inc46.i", .int 64 (i2 + 1#64)) :: env

/-- `lor.lhs.false.i`'s environment. -/
def slEnvLor (env : Env) (p : Nat) (i2 : BitVec 64) (b : UInt8) : Env :=
  ("%or.cond223.i", .int 1 (evalICmp .ult (vByte b + 0xc6#8) 0xf6#8)) ::
  ("%45", .int 8 (vByte b + 0xc6#8)) ::
  ("%44", .int 8 (vByte b)) ::
  ("%arrayidx49.i", .ptr (p + ((i2 + 1#64).signExtend 64).toNat)) :: env

/-- `land.lhs.true63.i`'s environment. -/
def slEnv63 (env : Env) (p : Nat) (i : BitVec 64) (b : UInt8) : Env :=
  ("%or.cond224.i", .int 1 (evalICmp .ult (vByte b + 0xd0#8) 0x0a#8)) ::
  ("%47", .int 8 (vByte b + 0xd0#8)) ::
  ("%46", .int 8 (vByte b)) ::
  ("%arrayidx64.i", .ptr (p + (i.signExtend 64).toNat)) ::
  ("%i.3265.i", .int 64 i) :: env

/-- `while.body74.i`'s environment. -/
def slEnvBody74 (env : Env) (i n : BitVec 64) : Env :=
  ("%exitcond306.not.i", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc75.i", .int 64 (i + 1#64)) :: env

/-- `if.end77.i`'s environment. -/
def slEnv77 (env : Env) (i4 n : BitVec 64) : Env :=
  ("%cmp78.i", .int 1 (evalICmp .ult i4 n)) :: ("%i.4.i", .int 64 i4) :: env

/-- `land.lhs.true80.i`'s environment. -/
def slEnv80 (env : Env) (p : Nat) (i4 : BitVec 64) (b : UInt8) : Env :=
  ("%48", .int 8 (vByte b)) ::
  ("%arrayidx81.i", .ptr (p + (i4.signExtend 64).toNat)) :: env

/-- `NodeBlock13`'s environment. -/
def slEnvNode13 (env : Env) (b : UInt8) : Env :=
  ("%Pivot14", .int 1 (evalICmp .slt (vByte b) 0x65#8)) :: env

/-- `LeafBlock11`'s environment. -/
def slEnvLeaf11 (env : Env) (b : UInt8) : Env :=
  ("%SwitchLeaf12", .int 1 (evalICmp .eq (vByte b) 0x65#8)) :: env

/-- `LeafBlock9`'s environment. -/
def slEnvLeaf9 (env : Env) (b : UInt8) : Env :=
  ("%SwitchLeaf10", .int 1 (evalICmp .eq (vByte b) 0x45#8)) :: env

/-- `if.then90.i`'s environment. -/
def slEnv90 (env : Env) (i4 n : BitVec 64) : Env :=
  ("%cmp92.i", .int 1 (evalICmp .ult (i4 + 1#64) n)) ::
  ("%inc91.i", .int 64 (i4 + 1#64)) :: env

/-- `land.lhs.true94.i`'s environment. -/
def slEnv94 (env : Env) (p : Nat) (i4 : BitVec 64) (b : UInt8) : Env :=
  ("%49", .int 8 (vByte b)) ::
  ("%arrayidx95.i", .ptr (p + ((i4 + 1#64).signExtend 64).toNat)) :: env

/-- `NodeBlock19`'s environment. -/
def slEnvNode19 (env : Env) (b : UInt8) : Env :=
  ("%Pivot20", .int 1 (evalICmp .slt (vByte b) 0x2d#8)) :: env

/-- `LeafBlock17`'s environment. -/
def slEnvLeaf17 (env : Env) (b : UInt8) : Env :=
  ("%SwitchLeaf18", .int 1 (evalICmp .eq (vByte b) 0x2d#8)) :: env

/-- `LeafBlock15`'s environment. -/
def slEnvLeaf15 (env : Env) (b : UInt8) : Env :=
  ("%SwitchLeaf16", .int 1 (evalICmp .eq (vByte b) 0x2b#8)) :: env

/-- `if.then104.i`'s environment. -/
def slEnv104 (env : Env) (i4 : BitVec 64) : Env :=
  ("%inc105.i", .int 64 (i4 + 2#64)) :: env

/-- `if.end106.i`'s environment. -/
def slEnv106 (env : Env) (i5 n : BitVec 64) : Env :=
  ("%cmp107.not.i", .int 1 (evalICmp .ult i5 n)) :: ("%i.5.i", .int 64 i5) :: env

/-- `lor.lhs.false109.i`'s environment. -/
def slEnvLor109 (env : Env) (p : Nat) (i5 : BitVec 64) (b : UInt8) : Env :=
  ("%or.cond225.i", .int 1 (evalICmp .ult (vByte b + 0xc6#8) 0xf6#8)) ::
  ("%51", .int 8 (vByte b + 0xc6#8)) ::
  ("%50", .int 8 (vByte b)) ::
  ("%arrayidx110.i", .ptr (p + (i5.signExtend 64).toNat)) :: env

/-- `land.lhs.true124.i`'s environment. -/
def slEnv124 (env : Env) (p : Nat) (i : BitVec 64) (b : UInt8) : Env :=
  ("%or.cond226.i", .int 1 (evalICmp .ult (vByte b + 0xd0#8) 0x0a#8)) ::
  ("%53", .int 8 (vByte b + 0xd0#8)) ::
  ("%52", .int 8 (vByte b)) ::
  ("%arrayidx125.i", .ptr (p + (i.signExtend 64).toNat)) ::
  ("%i.6269.i", .int 64 i) :: env

/-- `while.body135.i`'s environment. -/
def slEnvBody135 (env : Env) (i n : BitVec 64) : Env :=
  ("%exitcond307.not.i", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc136.i", .int 64 (i + 1#64)) :: env

/-- `if.end138.i`'s environment. -/
def slEnv138 (env : Env) (i7 n : BitVec 64) : Env :=
  ("%cmp139.not.i", .int 1 (evalICmp .eq i7 n)) :: ("%i.7.i", .int 64 i7) :: env

/-- The error exit's state: the stop index at `%err`, the return's block, and the
exiting block as the predecessor. -/
def slErrState (s : State) (e : Nat) (k : BitVec 64) (blk : String) : State :=
  { s with mem := writeBytes s.mem e (natToBytes k.toNat 8), pc := "cleanup300", pre := some blk }

/-- `for.body.outer.i.outer.i`'s ten-`phi` run, at the `if.then143.i` edge: the
sign's index as the digit cursor, the empty mantissa, and the counters at zero. -/
def slEntry (env : Env) (i0 : BitVec 64) : Env :=
  ("%sticky.0716.ph.i.ph.i", .int 32 0x00000000#32) ::
  ("%seen.0717.ph.i.ph.i", .int 32 0x00000000#32) ::
  ("%in_frac.0718.ph.i.ph.i", .int 32 0x00000000#32) ::
  ("%topn.0719.ph.i.ph.i", .int 64 0#64) ::
  ("%top.0720.ph.i.ph.i", .int 64 0#64) ::
  ("%lead.0721.ph.i.ph.i", .int 64 0#64) ::
  ("%F.0722.ph.i.ph.i", .int 64 0#64) ::
  ("%T.0723.ph.i.ph.i", .int 64 0#64) ::
  ("%R.0724.ph.i.ph.i", .int 64 0#64) ::
  ("%i.1725.ph.i.ph.i", .int 64 i0) :: env

/-! ### The lookup tactics -/

/-- The reader's environments, unfolded: a lookup at a successor's builder is a
lookup through the conses the blocks wrote.  `slCarry` is left folded, so the
peel stops at it and the caller's own hypothesis is found there. -/
macro "sl_env" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only
    [slSignBit, slSignIdx,
     slEnv285, slEnv6, slEnv11, slEnvElse, slEnv37, slEnv25, slEnvBody25,
     slEnv40, slEnv45, slEnvLor, slEnv63, slEnvBody74, slEnv77, slEnv80,
     slEnvNode13, slEnvLeaf11, slEnvLeaf9, slEnv90, slEnv94, slEnvNode19,
     slEnvLeaf17, slEnvLeaf15, slEnv104, slEnv106, slEnvLor109, slEnv124,
     slEnvBody135, slEnv138, slEntry]))

/-- Peel the environment's cells to the one the goal names. -/
macro "sl_lk" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      first | rw [lookupName_cons_self] | assumption | rfl)))

/-- The carried cells' own lookups. -/
macro "sl_carry" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [slCarry]
   first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      first | rw [lookupName_cons_self] | assumption | rfl)))


/-! ### `if.end285`: the counter's bump and the sign's index -/

/-- `if.end285`, from its pin. -/
def slInstrs285 : List Instr :=
  [Instr.load "%37" (Ty.int 64) (Operand.global "@g_nume1_slow"),
   Instr.binop "%inc287" (BinOp.add) 64 (Operand.reg "%37")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.store (Ty.int 64) (Operand.reg "%inc287") (Operand.global "@g_nume1_slow"),
   Instr.load "%38" (Ty.int 8) (Operand.reg "%p"),
   Instr.icmp "%cmp1.i" (IPred.eq) 8 (Operand.reg "%38")
     (Operand.imm (Const.int 8 0x2d#8)),
   Instr.zext "%i.0.i" 1 64 (Operand.reg "%cmp1.i"),
   Instr.icmp "%cmp3.not.i" (IPred.ugt) 64 (Operand.reg "%n") (Operand.reg "%i.0.i")]

theorem sl_find_285 :
    numFastBody.findBlock "if.end285" =
      some ⟨"if.end285", slInstrs285,
        Term.condbr (Operand.reg "%cmp3.not.i") "if.end6.i" "if.then5.i"⟩ := by
  simpa only [slInstrs285] using numFast_findBlock_if_end285

/-- `if.end285`'s chain. -/
theorem sl_285_denote {calls : Calls} {env : Env} {s : State}
    {gv : BitVec 64} {b0 : UInt8} {g p : Nat} {n i0 : BitVec 64} {sgn : BitVec 1}
    {digA : Nat}
    (hg : lookupName env "@g_nume1_slow" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp : lookupName env "%p" = some (.ptr p))
    (hb : readBytes s.mem p 1 = some [b0])
    (hbw : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) p 1 = some [b0])
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs285 (stateAt (slCarry env p n i0 sgn digA) s) =
      some (stateAt (slEnv285 env p n i0 sgn digA gv b0)
        { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8) }) := by
  have hg' : lookupName (slCarry env p n i0 sgn digA) "@g_nume1_slow" = some (.ptr g) := by
    sl_carry
  have hp' : lookupName (slCarry env p n i0 sgn digA) "%p" = some (.ptr p) := by sl_carry
  have hn' : lookupName (slCarry env p n i0 sgn digA) "%n" = some (.int 64 n) := by sl_carry
  unfold slInstrs285
  rw [denoteCode_load64_global calls _ s "%37" "@g_nume1_slow" hg' hgv]
  rw [denoteCode_add_imm calls _ s "%inc287" "%37" (by sl_env; sl_lk)]
  rw [denoteCode_store64_global calls _ s "%inc287" "@g_nume1_slow"
    (by sl_env; sl_lk) (by sl_env; sl_lk)]
  rw [denoteCode_load_i8 calls _ _ "%38" "%p" (by sl_env; sl_lk) hbw]
  rw [denoteCode_icmp_imm_w calls _ _ "%cmp1.i" "%38" .eq (by sl_env; sl_lk)]
  rw [denoteCode_zext calls _ _ "%i.0.i" "%cmp1.i" 1 64 (by sl_env; sl_lk)]
  rw [denoteCode_icmp_reg_w calls _ _ "%cmp3.not.i" "%n" "%i.0.i" .ugt 64
    (by sl_env; sl_lk) (by sl_env; sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv285, slSignBit, slSignIdx]
  rfl

/-- `if.end285`'s step: a nonempty lexeme takes `if.end6.i`. -/
theorem sl_285_step {calls : Calls} {env : Env} {s : State}
    {gv : BitVec 64} {b0 : UInt8} {g p : Nat} {n i0 : BitVec 64} {sgn : BitVec 1}
    {digA : Nat}
    (hpc : s.pc = "if.end285") (hpre : s.pre = some "cleanup282.thread462")
    (hg : lookupName env "@g_nume1_slow" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp : lookupName env "%p" = some (.ptr p))
    (hb : readBytes s.mem p 1 = some [b0])
    (hbw : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) p 1 = some [b0])
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ugt n (slSignIdx b0) = (1 : BitVec 1)) :
    step calls numFastBody (stateAt (slCarry env p n i0 sgn digA) s) =
      .jump (stateAt (slEnv285 env p n i0 sgn digA gv b0)
        { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8),
                 pc := "if.end6.i", pre := some "if.end285" }) := by
  refine numFast_step_at (s' := stateAt (slEnv285 env p n i0 sgn digA gv b0)
      { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8) })
    (b := ⟨"if.end285", slInstrs285,
      Term.condbr (Operand.reg "%cmp3.not.i") "if.end6.i" "if.then5.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, slCarry] using sl_find_285
  · simpa only [stateAt] using sl_285_denote hg hgv hp hb hbw hn
  · rw [numFast_execTerm_condbr_one _ "%cmp3.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end285`'s other edge: an empty lexeme is the reader's refusal. -/
theorem sl_285_step_empty {calls : Calls} {env : Env} {s : State}
    {gv : BitVec 64} {b0 : UInt8} {g p : Nat} {n i0 : BitVec 64} {sgn : BitVec 1}
    {digA : Nat}
    (hpc : s.pc = "if.end285") (hpre : s.pre = some "cleanup282.thread462")
    (hg : lookupName env "@g_nume1_slow" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp : lookupName env "%p" = some (.ptr p))
    (hb : readBytes s.mem p 1 = some [b0])
    (hbw : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) p 1 = some [b0])
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ugt n (slSignIdx b0) = (0 : BitVec 1)) :
    step calls numFastBody (stateAt (slCarry env p n i0 sgn digA) s) =
      .jump (stateAt (slEnv285 env p n i0 sgn digA gv b0)
        { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8),
                 pc := "if.then5.i", pre := some "if.end285" }) := by
  refine numFast_step_at (s' := stateAt (slEnv285 env p n i0 sgn digA gv b0)
      { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8) })
    (b := ⟨"if.end285", slInstrs285,
      Term.condbr (Operand.reg "%cmp3.not.i") "if.end6.i" "if.then5.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, slCarry] using sl_find_285
  · simpa only [stateAt] using sl_285_denote hg hgv hp hb hbw hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp3.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `if.end6.i`: the first digit's zero test -/

/-- `if.end6.i`, from its pin. -/
def slInstrs6 : List Instr :=
  [Instr.gep "%arrayidx7.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.0.i"),
   Instr.load "%39" (Ty.int 8) (Operand.reg "%arrayidx7.i"),
   Instr.icmp "%cmp9.i" (IPred.eq) 8 (Operand.reg "%39")
     (Operand.imm (Const.int 8 0x30#8))]

theorem sl_find_6 :
    numFastBody.findBlock "if.end6.i" =
      some ⟨"if.end6.i", slInstrs6,
        Term.condbr (Operand.reg "%cmp9.i") "if.then11.i" "if.else.i"⟩ := by
  simpa only [slInstrs6] using numFast_findBlock_if_end6_i

/-- `if.end6.i`'s chain. -/
theorem sl_6_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs6 (stateAt env s) =
      some (stateAt (slEnv6 env p i0 b) s) := by
  unfold slInstrs6
  rw [denoteCode_gep8_reg calls env s "%arrayidx7.i" "%p" "%i.0.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%39" "%arrayidx7.i" (by sl_env; sl_lk) hb]
  rw [denoteCode_icmp_imm_w calls _ s "%cmp9.i" "%39" .eq (by sl_env; sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv6]

/-- `if.end6.i`'s step: a leading `0` leaves for `if.then11.i`. -/
theorem sl_6_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "if.end6.i") (hpre : s.pre = some "if.end285")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .eq (vByte b) 0x30#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv6 env p i0 b)
        { s with pc := "if.then11.i", pre := some "if.end6.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv6 env p i0 b) s)
    (b := ⟨"if.end6.i", slInstrs6,
      Term.condbr (Operand.reg "%cmp9.i") "if.then11.i" "if.else.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_6
  · simpa only [stateAt] using sl_6_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%cmp9.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end6.i`'s other edge: a nonzero first byte takes the digit test. -/
theorem sl_6_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "if.end6.i") (hpre : s.pre = some "if.end285")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .eq (vByte b) 0x30#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv6 env p i0 b)
        { s with pc := "if.else.i", pre := some "if.end6.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv6 env p i0 b) s)
    (b := ⟨"if.end6.i", slInstrs6,
      Term.condbr (Operand.reg "%cmp9.i") "if.then11.i" "if.else.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_6
  · simpa only [stateAt] using sl_6_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%cmp9.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `if.then11.i` and `if.else.i` -/

/-- `if.then11.i`, from its pin. -/
def slInstrs11 : List Instr :=
  [Instr.select "%inc12.i" (Ty.int 64) (Operand.reg "%cmp1.i")
     (Operand.imm (Const.int 64 0x0000000000000002#64))
     (Operand.imm (Const.int 64 0x0000000000000001#64))]

theorem sl_find_11 :
    numFastBody.findBlock "if.then11.i" =
      some ⟨"if.then11.i", slInstrs11, Term.br "if.end37.i"⟩ := by
  simpa only [slInstrs11] using numFast_findBlock_if_then11_i

/-- `if.then11.i`'s chain. -/
theorem sl_11_denote {calls : Calls} {env : Env} {s : State} {sgn : BitVec 1}
    (hsign : lookupName env "%cmp1.i" = some (.int 1 sgn)) :
    denoteCode calls slInstrs11 (stateAt env s) =
      some (stateAt (slEnv11 env sgn) s) := by
  unfold slInstrs11
  rw [denoteCode_select_bit_imm_imm_w calls env s "%inc12.i" "%cmp1.i" 64 hsign]
  simp only [denoteCode_nil, stateAt, slEnv11]

/-- `if.then11.i`'s step. -/
theorem sl_11_step {calls : Calls} {env : Env} {s : State} {sgn : BitVec 1}
    (hpc : s.pc = "if.then11.i") (hpre : s.pre = some "if.end6.i")
    (hsign : lookupName env "%cmp1.i" = some (.int 1 sgn)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv11 env sgn)
        { s with pc := "if.end37.i", pre := some "if.then11.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv11 env sgn) s)
    (b := ⟨"if.then11.i", slInstrs11, Term.br "if.end37.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_11
  · simpa only [denoteCode_nil] using sl_11_denote hsign
  · simp only [execTerm, stateAt, hpc]

/-- `if.else.i`, from its pin. -/
def slInstrsElse : List Instr :=
  [Instr.binop "%40" (BinOp.add) 8 (Operand.reg "%39") (Operand.imm (Const.int 8 0xcf#8)),
   Instr.icmp "%or.cond.i" (IPred.ult) 8 (Operand.reg "%40")
     (Operand.imm (Const.int 8 0x09#8))]

theorem sl_find_else :
    numFastBody.findBlock "if.else.i" =
      some ⟨"if.else.i", slInstrsElse,
        Term.condbr (Operand.reg "%or.cond.i") "land.lhs.true25.i" "if.else35.i"⟩ := by
  simpa only [slInstrsElse] using numFast_findBlock_if_else_i

/-- `if.else.i`'s chain. -/
theorem sl_else_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%39" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrsElse (stateAt env s) =
      some (stateAt (slEnvElse env b) s) := by
  unfold slInstrsElse
  rw [denoteCode_add_imm_w calls env s "%40" "%39" 8 hb]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond.i" "%40" .ult (by sl_env; sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvElse]

/-- `if.else.i`'s step into the integer digits. -/
theorem sl_else_step {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "if.else.i") (hpre : s.pre = some "if.end6.i")
    (hb : lookupName env "%39" = some (.int 8 (vByte b)))
    (hbit : evalICmp .ult (vByte b + 0xcf#8) 0x09#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvElse env b)
        { s with pc := "land.lhs.true25.i", pre := some "if.else.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvElse env b) s)
    (b := ⟨"if.else.i", slInstrsElse,
      Term.condbr (Operand.reg "%or.cond.i") "land.lhs.true25.i" "if.else35.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_else
  · simpa only [stateAt] using sl_else_denote hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.else.i`'s refusing edge. -/
theorem sl_else_step_ne {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "if.else.i") (hpre : s.pre = some "if.end6.i")
    (hb : lookupName env "%39" = some (.int 8 (vByte b)))
    (hbit : evalICmp .ult (vByte b + 0xcf#8) 0x09#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvElse env b)
        { s with pc := "if.else35.i", pre := some "if.else.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvElse env b) s)
    (b := ⟨"if.else.i", slInstrsElse,
      Term.condbr (Operand.reg "%or.cond.i") "land.lhs.true25.i" "if.else35.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_else
  · simpa only [stateAt] using sl_else_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `if.end37.i`: the integer part's bound test -/

/-- `if.end37.i`, from its pin. -/
def slInstrs37 : List Instr :=
  [Instr.phi "%i.2.i" (Ty.int 64) [("if.then11.i", (Operand.reg "%inc12.i")),
                                    ("land.lhs.true25.i", (Operand.reg "%i.1262.i"))],
   Instr.icmp "%cmp38.i" (IPred.ult) 64 (Operand.reg "%i.2.i") (Operand.reg "%n")]

theorem sl_find_37 :
    numFastBody.findBlock "if.end37.i" =
      some ⟨"if.end37.i", slInstrs37,
        Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩ := by
  simpa only [slInstrs37] using numFast_findBlock_if_end37_i

/-- `if.end37.i`'s chain from the zero case's index. -/
theorem sl_37_denote_from_11 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpre : s.pre = some "if.then11.i")
    (hi : lookupName env "%inc12.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs37 (stateAt env s) =
      some (stateAt (slEnv37 env i2 n) s) := by
  unfold slInstrs37
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc12.i")
    (v := .int 64 i2) calls env s "%i.2.i" (Ty.int 64)
    [("if.then11.i", (Operand.reg "%inc12.i")),
     ("land.lhs.true25.i", (Operand.reg "%i.1262.i"))]
    [Instr.icmp "%cmp38.i" (IPred.ult) 64 (Operand.reg "%i.2.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc12.i" (.int 64 i2) hi)
    (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp38.i" "%i.2.i" "%n"
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv37]

/-- `if.end37.i`'s chain from the digit run's stop index. -/
theorem sl_37_denote_from_25 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpre : s.pre = some "land.lhs.true25.i")
    (hi : lookupName env "%i.1262.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs37 (stateAt env s) =
      some (stateAt (slEnv37 env i2 n) s) := by
  unfold slInstrs37
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.1262.i")
    (v := .int 64 i2) calls env s "%i.2.i" (Ty.int 64)
    [("if.then11.i", (Operand.reg "%inc12.i")),
     ("land.lhs.true25.i", (Operand.reg "%i.1262.i"))]
    [Instr.icmp "%cmp38.i" (IPred.ult) 64 (Operand.reg "%i.2.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.1262.i" (.int 64 i2) hi)
    (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp38.i" "%i.2.i" "%n"
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv37]

/-- `if.end37.i`'s bounded edge from the zero case's index. -/
theorem sl_37_step {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end37.i") (hpre : s.pre = some "if.then11.i")
    (hi : lookupName env "%inc12.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv37 env i2 n)
        { s with pc := "land.lhs.true40.i", pre := some "if.end37.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv37 env i2 n) s)
    (b := ⟨"if.end37.i", slInstrs37,
      Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_37
  · simpa only [stateAt] using sl_37_denote_from_11 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp38.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end37.i`'s bounded edge from the digit run's stop index. -/
theorem sl_37_step_from_25 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end37.i") (hpre : s.pre = some "land.lhs.true25.i")
    (hi : lookupName env "%i.1262.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv37 env i2 n)
        { s with pc := "land.lhs.true40.i", pre := some "if.end37.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv37 env i2 n) s)
    (b := ⟨"if.end37.i", slInstrs37,
      Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_37
  · simpa only [stateAt] using sl_37_denote_from_25 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp38.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end37.i`'s end edge from the zero case's index. -/
theorem sl_37_step_end {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end37.i") (hpre : s.pre = some "if.then11.i")
    (hi : lookupName env "%inc12.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv37 env i2 n)
        { s with pc := "if.end77.i", pre := some "if.end37.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv37 env i2 n) s)
    (b := ⟨"if.end37.i", slInstrs37,
      Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_37
  · simpa only [stateAt] using sl_37_denote_from_11 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp38.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end37.i`'s end edge from the digit run's stop index. -/
theorem sl_37_step_end_from_25 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end37.i") (hpre : s.pre = some "land.lhs.true25.i")
    (hi : lookupName env "%i.1262.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv37 env i2 n)
        { s with pc := "if.end77.i", pre := some "if.end37.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv37 env i2 n) s)
    (b := ⟨"if.end37.i", slInstrs37,
      Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_37
  · simpa only [stateAt] using sl_37_denote_from_25 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp38.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### The integer digits: `land.lhs.true25.i` and `while.body.i` -/

/-- `land.lhs.true25.i`, from its pin. -/
def slInstrs25 : List Instr :=
  [Instr.phi "%i.1262.i" (Ty.int 64) [("while.body.i", (Operand.reg "%inc34.i")),
                                      ("if.else.i", (Operand.reg "%i.0.i"))],
   Instr.gep "%arrayidx26.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1262.i"),
   Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx26.i"),
   Instr.binop "%42" (BinOp.add) 8 (Operand.reg "%41") (Operand.imm (Const.int 8 0xd0#8)),
   Instr.icmp "%or.cond222.i" (IPred.ult) 8 (Operand.reg "%42")
     (Operand.imm (Const.int 8 0x0a#8))]

theorem sl_find_25 :
    numFastBody.findBlock "land.lhs.true25.i" =
      some ⟨"land.lhs.true25.i", slInstrs25,
        Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩ := by
  simpa only [slInstrs25] using numFast_findBlock_land_lhs_true25_i

/-- `land.lhs.true25.i`'s chain, from the first digit's index. -/
theorem sl_25_denote_from_else {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "if.else.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs25 (stateAt env s) =
      some (stateAt (slEnv25 env p i0 b) s) := by
  unfold slInstrs25
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.0.i")
    (v := .int 64 i0) calls env s "%i.1262.i" (Ty.int 64)
    [("while.body.i", (Operand.reg "%inc34.i")), ("if.else.i", (Operand.reg "%i.0.i"))]
    [Instr.gep "%arrayidx26.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1262.i"),
     Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx26.i"),
     Instr.binop "%42" (BinOp.add) 8 (Operand.reg "%41") (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond222.i" (IPred.ult) 8 (Operand.reg "%42")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.0.i" (.int 64 i0) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx26.i" "%p" "%i.1262.i"
    (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%41" "%arrayidx26.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%42" "%41" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond222.i" "%42" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv25]

/-- `land.lhs.true25.i`'s chain, from the digit run's cursor. -/
theorem sl_25_denote_from_body {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "while.body.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc34.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs25 (stateAt env s) =
      some (stateAt (slEnv25 env p i b) s) := by
  unfold slInstrs25
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc34.i")
    (v := .int 64 i) calls env s "%i.1262.i" (Ty.int 64)
    [("while.body.i", (Operand.reg "%inc34.i")), ("if.else.i", (Operand.reg "%i.0.i"))]
    [Instr.gep "%arrayidx26.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1262.i"),
     Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx26.i"),
     Instr.binop "%42" (BinOp.add) 8 (Operand.reg "%41") (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond222.i" (IPred.ult) 8 (Operand.reg "%42")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc34.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx26.i" "%p" "%i.1262.i"
    (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%41" "%arrayidx26.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%42" "%41" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond222.i" "%42" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv25]

/-- `land.lhs.true25.i`'s step into the digit run. -/
theorem sl_25_step_from_else {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true25.i") (hpre : s.pre = some "if.else.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv25 env p i0 b)
        { s with pc := "while.body.i", pre := some "land.lhs.true25.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv25 env p i0 b) s)
    (b := ⟨"land.lhs.true25.i", slInstrs25,
      Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_25
  · simpa only [stateAt] using sl_25_denote_from_else hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond222.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true25.i`'s exit: a non-digit ends the integer part. -/
theorem sl_25_step_from_else_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i0 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true25.i") (hpre : s.pre = some "if.else.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (hpos : (i0.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i0.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv25 env p i0 b)
        { s with pc := "if.end37.i", pre := some "land.lhs.true25.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv25 env p i0 b) s)
    (b := ⟨"land.lhs.true25.i", slInstrs25,
      Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_25
  · simpa only [stateAt] using sl_25_denote_from_else hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond222.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true25.i`'s step from the digit run's cursor. -/
theorem sl_25_step_from_body {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true25.i") (hpre : s.pre = some "while.body.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc34.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv25 env p i b)
        { s with pc := "while.body.i", pre := some "land.lhs.true25.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv25 env p i b) s)
    (b := ⟨"land.lhs.true25.i", slInstrs25,
      Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_25
  · simpa only [stateAt] using sl_25_denote_from_body hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond222.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true25.i`'s exit from the digit run's cursor. -/
theorem sl_25_step_from_body_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true25.i") (hpre : s.pre = some "while.body.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc34.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv25 env p i b)
        { s with pc := "if.end37.i", pre := some "land.lhs.true25.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv25 env p i b) s)
    (b := ⟨"land.lhs.true25.i", slInstrs25,
      Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_25
  · simpa only [stateAt] using sl_25_denote_from_body hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond222.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body.i`, from its pin. -/
def slInstrsBody25 : List Instr :=
  [Instr.binop "%inc34.i" (BinOp.add) 64 (Operand.reg "%i.1262.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc34.i") (Operand.reg "%n")]

theorem sl_find_body25 :
    numFastBody.findBlock "while.body.i" =
      some ⟨"while.body.i", slInstrsBody25,
        Term.condbr (Operand.reg "%exitcond.not.i") "if.then143.i" "land.lhs.true25.i"⟩ := by
  simpa only [slInstrsBody25] using numFast_findBlock_while_body_i

/-- `while.body.i`'s chain. -/
theorem sl_body25_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.1262.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrsBody25 (stateAt env s) =
      some (stateAt (slEnvBody25 env i n) s) := by
  unfold slInstrsBody25
  rw [denoteCode_add_imm calls env s "%inc34.i" "%i.1262.i" hi]
  rw [denoteCode_icmp_reg_w calls _ s "%exitcond.not.i" "%inc34.i" "%n" .eq 64
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvBody25]

/-- `while.body.i`'s exit: the cursor reached the lexeme's end. -/
theorem sl_body25_step_exit {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body.i") (hpre : s.pre = some "land.lhs.true25.i")
    (hi : lookupName env "%i.1262.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody25 env i n)
        { s with pc := "if.then143.i", pre := some "while.body.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody25 env i n) s)
    (b := ⟨"while.body.i", slInstrsBody25,
      Term.condbr (Operand.reg "%exitcond.not.i") "if.then143.i" "land.lhs.true25.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body25
  · simpa only [stateAt] using sl_body25_denote hi hn
  · rw [numFast_execTerm_condbr_one _ "%exitcond.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body.i`'s back edge. -/
theorem sl_body25_step_loop {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body.i") (hpre : s.pre = some "land.lhs.true25.i")
    (hi : lookupName env "%i.1262.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody25 env i n)
        { s with pc := "land.lhs.true25.i", pre := some "while.body.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody25 env i n) s)
    (b := ⟨"while.body.i", slInstrsBody25,
      Term.condbr (Operand.reg "%exitcond.not.i") "if.then143.i" "land.lhs.true25.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body25
  · simpa only [stateAt] using sl_body25_denote hi hn
  · rw [numFast_execTerm_condbr_zero _ "%exitcond.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `land.lhs.true40.i`: the fraction's `.` -/

/-- `land.lhs.true40.i`, from its pin. -/
def slInstrs40 : List Instr :=
  [Instr.gep "%arrayidx41.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.2.i"),
   Instr.load "%43" (Ty.int 8) (Operand.reg "%arrayidx41.i"),
   Instr.icmp "%cmp43.i" (IPred.eq) 8 (Operand.reg "%43")
     (Operand.imm (Const.int 8 0x2e#8))]

theorem sl_find_40 :
    numFastBody.findBlock "land.lhs.true40.i" =
      some ⟨"land.lhs.true40.i", slInstrs40,
        Term.condbr (Operand.reg "%cmp43.i") "if.then45.i" "if.end77.i"⟩ := by
  simpa only [slInstrs40] using numFast_findBlock_land_lhs_true40_i

/-- `land.lhs.true40.i`'s chain. -/
theorem sl_40_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hpos : (i2.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i2.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs40 (stateAt env s) =
      some (stateAt (slEnv40 env p i2 b) s) := by
  unfold slInstrs40
  rw [denoteCode_gep8_reg calls env s "%arrayidx41.i" "%p" "%i.2.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%43" "%arrayidx41.i" (by sl_lk) hb]
  rw [denoteCode_icmp_imm_w calls _ s "%cmp43.i" "%43" .eq (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv40]

/-- `land.lhs.true40.i`'s step: the byte is `.`, so the fraction starts. -/
theorem sl_40_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true40.i") (hpre : s.pre = some "if.end37.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hpos : (i2.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i2.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .eq (vByte b) 0x2e#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv40 env p i2 b)
        { s with pc := "if.then45.i", pre := some "land.lhs.true40.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv40 env p i2 b) s)
    (b := ⟨"land.lhs.true40.i", slInstrs40,
      Term.condbr (Operand.reg "%cmp43.i") "if.then45.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_40
  · simpa only [stateAt] using sl_40_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%cmp43.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true40.i`'s other edge: no fraction. -/
theorem sl_40_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true40.i") (hpre : s.pre = some "if.end37.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hpos : (i2.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i2.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .eq (vByte b) 0x2e#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv40 env p i2 b)
        { s with pc := "if.end77.i", pre := some "land.lhs.true40.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv40 env p i2 b) s)
    (b := ⟨"land.lhs.true40.i", slInstrs40,
      Term.condbr (Operand.reg "%cmp43.i") "if.then45.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_40
  · simpa only [stateAt] using sl_40_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%cmp43.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `if.then45.i` and `lor.lhs.false.i`: the fraction's first digit -/

/-- `if.then45.i`, from its pin. -/
def slInstrs45 : List Instr :=
  [Instr.binop "%inc46.i" (BinOp.add) 64 (Operand.reg "%i.2.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%cmp47.not.i" (IPred.ult) 64 (Operand.reg "%inc46.i") (Operand.reg "%n")]

theorem sl_find_45 :
    numFastBody.findBlock "if.then45.i" =
      some ⟨"if.then45.i", slInstrs45,
        Term.condbr (Operand.reg "%cmp47.not.i") "lor.lhs.false.i" "if.then58.i"⟩ := by
  simpa only [slInstrs45] using numFast_findBlock_if_then45_i

/-- `if.then45.i`'s chain. -/
theorem sl_45_denote {calls : Calls} {env : Env} {s : State} {i2 n : BitVec 64}
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs45 (stateAt env s) =
      some (stateAt (slEnv45 env i2 n) s) := by
  unfold slInstrs45
  rw [denoteCode_add_imm calls env s "%inc46.i" "%i.2.i" hi]
  rw [denoteCode_icmp_reg_w calls _ s "%cmp47.not.i" "%inc46.i" "%n" .ult 64
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv45]

/-- `if.then45.i`'s bounded edge. -/
theorem sl_45_step {calls : Calls} {env : Env} {s : State} {i2 n : BitVec 64}
    (hpc : s.pc = "if.then45.i") (hpre : s.pre = some "land.lhs.true40.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i2 + 1#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv45 env i2 n)
        { s with pc := "lor.lhs.false.i", pre := some "if.then45.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv45 env i2 n) s)
    (b := ⟨"if.then45.i", slInstrs45,
      Term.condbr (Operand.reg "%cmp47.not.i") "lor.lhs.false.i" "if.then58.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_45
  · simpa only [stateAt] using sl_45_denote hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp47.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.then45.i`'s refusing edge: the `.` is the lexeme's last byte. -/
theorem sl_45_step_ne {calls : Calls} {env : Env} {s : State} {i2 n : BitVec 64}
    (hpc : s.pc = "if.then45.i") (hpre : s.pre = some "land.lhs.true40.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i2 + 1#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv45 env i2 n)
        { s with pc := "if.then58.i", pre := some "if.then45.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv45 env i2 n) s)
    (b := ⟨"if.then45.i", slInstrs45,
      Term.condbr (Operand.reg "%cmp47.not.i") "lor.lhs.false.i" "if.then58.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_45
  · simpa only [stateAt] using sl_45_denote hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp47.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `lor.lhs.false.i`, from its pin. -/
def slInstrsLor : List Instr :=
  [Instr.gep "%arrayidx49.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc46.i"),
   Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx49.i"),
   Instr.binop "%45" (BinOp.add) 8 (Operand.reg "%44") (Operand.imm (Const.int 8 0xc6#8)),
   Instr.icmp "%or.cond223.i" (IPred.ult) 8 (Operand.reg "%45")
     (Operand.imm (Const.int 8 0xf6#8))]

theorem sl_find_lor :
    numFastBody.findBlock "lor.lhs.false.i" =
      some ⟨"lor.lhs.false.i", slInstrsLor,
        Term.condbr (Operand.reg "%or.cond223.i") "if.then58.i" "land.lhs.true63.i"⟩ := by
  simpa only [slInstrsLor] using numFast_findBlock_lor_lhs_false_i

/-- `lor.lhs.false.i`'s chain: the byte after the `.` is not a digit. -/
theorem sl_lor_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 (i2 + 1#64)))
    (hpos : ((i2 + 1#64).signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + ((i2 + 1#64).signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrsLor (stateAt env s) =
      some (stateAt (slEnvLor env p i2 b) s) := by
  unfold slInstrsLor
  rw [denoteCode_gep8_reg calls env s "%arrayidx49.i" "%p" "%inc46.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%44" "%arrayidx49.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%45" "%44" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond223.i" "%45" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvLor]

/-- `lor.lhs.false.i`'s refusing edge. -/
theorem sl_lor_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "lor.lhs.false.i") (hpre : s.pre = some "if.then45.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 (i2 + 1#64)))
    (hpos : ((i2 + 1#64).signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + ((i2 + 1#64).signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xc6#8) 0xf6#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLor env p i2 b)
        { s with pc := "if.then58.i", pre := some "lor.lhs.false.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLor env p i2 b) s)
    (b := ⟨"lor.lhs.false.i", slInstrsLor,
      Term.condbr (Operand.reg "%or.cond223.i") "if.then58.i" "land.lhs.true63.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_lor
  · simpa only [stateAt] using sl_lor_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond223.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `lor.lhs.false.i`'s edge into the fraction digits. -/
theorem sl_lor_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i2 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "lor.lhs.false.i") (hpre : s.pre = some "if.then45.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 (i2 + 1#64)))
    (hpos : ((i2 + 1#64).signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + ((i2 + 1#64).signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xc6#8) 0xf6#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLor env p i2 b)
        { s with pc := "land.lhs.true63.i", pre := some "lor.lhs.false.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLor env p i2 b) s)
    (b := ⟨"lor.lhs.false.i", slInstrsLor,
      Term.condbr (Operand.reg "%or.cond223.i") "if.then58.i" "land.lhs.true63.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_lor
  · simpa only [stateAt] using sl_lor_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond223.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true63.i`, from its pin. -/
def slInstrs_63 : List Instr :=
  [Instr.phi "%i.3265.i" (Ty.int 64) [("while.body74.i", (Operand.reg "%inc75.i")), ("lor.lhs.false.i", (Operand.reg "%inc46.i"))],
   Instr.gep "%arrayidx64.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3265.i"),
   Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx64.i"),
   Instr.binop "%47" (BinOp.add) 8 (Operand.reg "%46")
     (Operand.imm (Const.int 8 0xd0#8)),
   Instr.icmp "%or.cond224.i" (IPred.ult) 8 (Operand.reg "%47")
     (Operand.imm (Const.int 8 0x0a#8))]

theorem sl_find_63 :
    numFastBody.findBlock "land.lhs.true63.i" =
      some ⟨"land.lhs.true63.i", slInstrs_63,
        Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩ := by
  simpa only [slInstrs_63] using numFast_findBlock_land_lhs_true63_i

/-- `land.lhs.true63.i`'s chain from `lor.lhs.false.i`. -/
theorem sl_63_denote_from_lor {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "lor.lhs.false.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs_63 (stateAt env s) =
      some (stateAt (slEnv63 env p i b) s) := by
  unfold slInstrs_63
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc46.i")
    (v := .int 64 i) calls env s "%i.3265.i" (Ty.int 64) [("while.body74.i", (Operand.reg "%inc75.i")), ("lor.lhs.false.i", (Operand.reg "%inc46.i"))]
    [Instr.gep "%arrayidx64.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3265.i"),
     Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx64.i"),
     Instr.binop "%47" (BinOp.add) 8 (Operand.reg "%46")
       (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond224.i" (IPred.ult) 8 (Operand.reg "%47")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc46.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx64.i" "%p" "%i.3265.i" (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%46" "%arrayidx64.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%47" "%46" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond224.i" "%47" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv63]

/-- `land.lhs.true63.i`'s chain from `while.body74.i`. -/
theorem sl_63_denote_from_body74 {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "while.body74.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc75.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs_63 (stateAt env s) =
      some (stateAt (slEnv63 env p i b) s) := by
  unfold slInstrs_63
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc75.i")
    (v := .int 64 i) calls env s "%i.3265.i" (Ty.int 64) [("while.body74.i", (Operand.reg "%inc75.i")), ("lor.lhs.false.i", (Operand.reg "%inc46.i"))]
    [Instr.gep "%arrayidx64.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3265.i"),
     Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx64.i"),
     Instr.binop "%47" (BinOp.add) 8 (Operand.reg "%46")
       (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond224.i" (IPred.ult) 8 (Operand.reg "%47")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc75.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx64.i" "%p" "%i.3265.i" (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%46" "%arrayidx64.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%47" "%46" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond224.i" "%47" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv63]

/-- `land.lhs.true63.i`'s step from `lor.lhs.false.i` into the digits. -/
theorem sl_63_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true63.i") (hpre : s.pre = some "lor.lhs.false.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv63 env p i b)
        { s with pc := "while.body74.i", pre := some "land.lhs.true63.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv63 env p i b) s)
    (b := ⟨"land.lhs.true63.i", slInstrs_63,
      Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_63
  · simpa only [stateAt] using sl_63_denote_from_lor hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond224.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true63.i`'s exit from `lor.lhs.false.i`. -/
theorem sl_63_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true63.i") (hpre : s.pre = some "lor.lhs.false.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc46.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv63 env p i b)
        { s with pc := "if.end77.i", pre := some "land.lhs.true63.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv63 env p i b) s)
    (b := ⟨"land.lhs.true63.i", slInstrs_63,
      Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_63
  · simpa only [stateAt] using sl_63_denote_from_lor hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond224.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true63.i`'s step from `while.body74.i` into the digits. -/
theorem sl_63_step_back {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true63.i") (hpre : s.pre = some "while.body74.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc75.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv63 env p i b)
        { s with pc := "while.body74.i", pre := some "land.lhs.true63.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv63 env p i b) s)
    (b := ⟨"land.lhs.true63.i", slInstrs_63,
      Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_63
  · simpa only [stateAt] using sl_63_denote_from_body74 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond224.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true63.i`'s exit from `while.body74.i`. -/
theorem sl_63_step_back_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true63.i") (hpre : s.pre = some "while.body74.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc75.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv63 env p i b)
        { s with pc := "if.end77.i", pre := some "land.lhs.true63.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv63 env p i b) s)
    (b := ⟨"land.lhs.true63.i", slInstrs_63,
      Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_63
  · simpa only [stateAt] using sl_63_denote_from_body74 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond224.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true124.i`, from its pin. -/
def slInstrs_124 : List Instr :=
  [Instr.phi "%i.6269.i" (Ty.int 64) [("while.body135.i", (Operand.reg "%inc136.i")), ("lor.lhs.false109.i", (Operand.reg "%i.5.i"))],
   Instr.gep "%arrayidx125.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.6269.i"),
   Instr.load "%52" (Ty.int 8) (Operand.reg "%arrayidx125.i"),
   Instr.binop "%53" (BinOp.add) 8 (Operand.reg "%52")
     (Operand.imm (Const.int 8 0xd0#8)),
   Instr.icmp "%or.cond226.i" (IPred.ult) 8 (Operand.reg "%53")
     (Operand.imm (Const.int 8 0x0a#8))]

theorem sl_find_124 :
    numFastBody.findBlock "land.lhs.true124.i" =
      some ⟨"land.lhs.true124.i", slInstrs_124,
        Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩ := by
  simpa only [slInstrs_124] using numFast_findBlock_land_lhs_true124_i

/-- `land.lhs.true124.i`'s chain from `lor.lhs.false109.i`. -/
theorem sl_124_denote_from_lor109 {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "lor.lhs.false109.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs_124 (stateAt env s) =
      some (stateAt (slEnv124 env p i b) s) := by
  unfold slInstrs_124
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.5.i")
    (v := .int 64 i) calls env s "%i.6269.i" (Ty.int 64) [("while.body135.i", (Operand.reg "%inc136.i")), ("lor.lhs.false109.i", (Operand.reg "%i.5.i"))]
    [Instr.gep "%arrayidx125.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.6269.i"),
     Instr.load "%52" (Ty.int 8) (Operand.reg "%arrayidx125.i"),
     Instr.binop "%53" (BinOp.add) 8 (Operand.reg "%52")
       (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond226.i" (IPred.ult) 8 (Operand.reg "%53")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.5.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx125.i" "%p" "%i.6269.i" (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%52" "%arrayidx125.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%53" "%52" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond226.i" "%53" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv124]

/-- `land.lhs.true124.i`'s chain from `while.body135.i`. -/
theorem sl_124_denote_from_body135 {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "while.body135.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc136.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs_124 (stateAt env s) =
      some (stateAt (slEnv124 env p i b) s) := by
  unfold slInstrs_124
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc136.i")
    (v := .int 64 i) calls env s "%i.6269.i" (Ty.int 64) [("while.body135.i", (Operand.reg "%inc136.i")), ("lor.lhs.false109.i", (Operand.reg "%i.5.i"))]
    [Instr.gep "%arrayidx125.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.6269.i"),
     Instr.load "%52" (Ty.int 8) (Operand.reg "%arrayidx125.i"),
     Instr.binop "%53" (BinOp.add) 8 (Operand.reg "%52")
       (Operand.imm (Const.int 8 0xd0#8)),
     Instr.icmp "%or.cond226.i" (IPred.ult) 8 (Operand.reg "%53")
       (Operand.imm (Const.int 8 0x0a#8))]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc136.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_gep8_reg calls _ s "%arrayidx125.i" "%p" "%i.6269.i" (by assumption) (by sl_lk) hpos]
  rw [denoteCode_load_i8 calls _ s "%52" "%arrayidx125.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%53" "%52" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond226.i" "%53" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv124]

/-- `land.lhs.true124.i`'s step from `lor.lhs.false109.i` into the digits. -/
theorem sl_124_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true124.i") (hpre : s.pre = some "lor.lhs.false109.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv124 env p i b)
        { s with pc := "while.body135.i", pre := some "land.lhs.true124.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv124 env p i b) s)
    (b := ⟨"land.lhs.true124.i", slInstrs_124,
      Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_124
  · simpa only [stateAt] using sl_124_denote_from_lor109 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond226.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true124.i`'s exit from `lor.lhs.false109.i`. -/
theorem sl_124_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true124.i") (hpre : s.pre = some "lor.lhs.false109.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv124 env p i b)
        { s with pc := "if.end138.i", pre := some "land.lhs.true124.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv124 env p i b) s)
    (b := ⟨"land.lhs.true124.i", slInstrs_124,
      Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_124
  · simpa only [stateAt] using sl_124_denote_from_lor109 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond226.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true124.i`'s step from `while.body135.i` into the digits. -/
theorem sl_124_step_back {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true124.i") (hpre : s.pre = some "while.body135.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc136.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv124 env p i b)
        { s with pc := "while.body135.i", pre := some "land.lhs.true124.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv124 env p i b) s)
    (b := ⟨"land.lhs.true124.i", slInstrs_124,
      Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_124
  · simpa only [stateAt] using sl_124_denote_from_body135 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond226.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true124.i`'s exit from `while.body135.i`. -/
theorem sl_124_step_back_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true124.i") (hpre : s.pre = some "while.body135.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc136.i" = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv124 env p i b)
        { s with pc := "if.end138.i", pre := some "land.lhs.true124.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv124 env p i b) s)
    (b := ⟨"land.lhs.true124.i", slInstrs_124,
      Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_124
  · simpa only [stateAt] using sl_124_denote_from_body135 hpre hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond226.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body74.i`, from its pin. -/
def slInstrs_body74 : List Instr :=
  [Instr.binop "%inc75.i" (BinOp.add) 64 (Operand.reg "%i.3265.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond306.not.i" (IPred.eq) 64 (Operand.reg "%inc75.i") (Operand.reg "%n")]

theorem sl_find_body74 :
    numFastBody.findBlock "while.body74.i" =
      some ⟨"while.body74.i", slInstrs_body74,
        Term.condbr (Operand.reg "%exitcond306.not.i") "if.then143.i" "land.lhs.true63.i"⟩ := by
  simpa only [slInstrs_body74] using numFast_findBlock_while_body74_i

/-- `while.body74.i`'s chain. -/
theorem sl_body74_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_body74 (stateAt env s) =
      some (stateAt (slEnvBody74 env i n) s) := by
  unfold slInstrs_body74
  rw [denoteCode_add_imm calls env s "%inc75.i" "%i.3265.i" hi]
  rw [denoteCode_icmp_reg_w calls _ s "%exitcond306.not.i" "%inc75.i" "%n" .eq 64
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvBody74]

/-- `while.body74.i`'s exit. -/
theorem sl_body74_step_exit {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body74.i") (hpre : s.pre = some "land.lhs.true63.i")
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody74 env i n)
        { s with pc := "if.then143.i", pre := some "while.body74.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody74 env i n) s)
    (b := ⟨"while.body74.i", slInstrs_body74,
      Term.condbr (Operand.reg "%exitcond306.not.i") "if.then143.i" "land.lhs.true63.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body74
  · simpa only [stateAt] using sl_body74_denote hi hn
  · rw [numFast_execTerm_condbr_one _ "%exitcond306.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body74.i`'s back edge. -/
theorem sl_body74_step_loop {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body74.i") (hpre : s.pre = some "land.lhs.true63.i")
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody74 env i n)
        { s with pc := "land.lhs.true63.i", pre := some "while.body74.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody74 env i n) s)
    (b := ⟨"while.body74.i", slInstrs_body74,
      Term.condbr (Operand.reg "%exitcond306.not.i") "if.then143.i" "land.lhs.true63.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body74
  · simpa only [stateAt] using sl_body74_denote hi hn
  · rw [numFast_execTerm_condbr_zero _ "%exitcond306.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body135.i`, from its pin. -/
def slInstrs_body135 : List Instr :=
  [Instr.binop "%inc136.i" (BinOp.add) 64 (Operand.reg "%i.6269.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond307.not.i" (IPred.eq) 64 (Operand.reg "%inc136.i") (Operand.reg "%n")]

theorem sl_find_body135 :
    numFastBody.findBlock "while.body135.i" =
      some ⟨"while.body135.i", slInstrs_body135,
        Term.condbr (Operand.reg "%exitcond307.not.i") "if.then143.i" "land.lhs.true124.i"⟩ := by
  simpa only [slInstrs_body135] using numFast_findBlock_while_body135_i

/-- `while.body135.i`'s chain. -/
theorem sl_body135_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_body135 (stateAt env s) =
      some (stateAt (slEnvBody135 env i n) s) := by
  unfold slInstrs_body135
  rw [denoteCode_add_imm calls env s "%inc136.i" "%i.6269.i" hi]
  rw [denoteCode_icmp_reg_w calls _ s "%exitcond307.not.i" "%inc136.i" "%n" .eq 64
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvBody135]

/-- `while.body135.i`'s exit. -/
theorem sl_body135_step_exit {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body135.i") (hpre : s.pre = some "land.lhs.true124.i")
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody135 env i n)
        { s with pc := "if.then143.i", pre := some "while.body135.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody135 env i n) s)
    (b := ⟨"while.body135.i", slInstrs_body135,
      Term.condbr (Operand.reg "%exitcond307.not.i") "if.then143.i" "land.lhs.true124.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body135
  · simpa only [stateAt] using sl_body135_denote hi hn
  · rw [numFast_execTerm_condbr_one _ "%exitcond307.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `while.body135.i`'s back edge. -/
theorem sl_body135_step_loop {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "while.body135.i") (hpre : s.pre = some "land.lhs.true124.i")
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 1#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvBody135 env i n)
        { s with pc := "land.lhs.true124.i", pre := some "while.body135.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvBody135 env i n) s)
    (b := ⟨"while.body135.i", slInstrs_body135,
      Term.condbr (Operand.reg "%exitcond307.not.i") "if.then143.i" "land.lhs.true124.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_body135
  · simpa only [stateAt] using sl_body135_denote hi hn
  · rw [numFast_execTerm_condbr_zero _ "%exitcond307.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`, from its pin. -/
def slInstrs_77 : List Instr :=
  [Instr.phi "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")), ("if.end37.i", (Operand.reg "%i.2.i")), ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))],
   Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")]

theorem sl_find_77 :
    numFastBody.findBlock "if.end77.i" =
      some ⟨"if.end77.i", slInstrs_77,
        Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩ := by
  simpa only [slInstrs_77] using numFast_findBlock_if_end77_i

/-- `if.end77.i`'s chain from `land.lhs.true40.i`. -/
theorem sl_77_denote_from_40 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "land.lhs.true40.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_77 (stateAt env s) =
      some (stateAt (slEnv77 env i n) s) := by
  unfold slInstrs_77
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.2.i")
    (v := .int 64 i) calls env s "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")), ("if.end37.i", (Operand.reg "%i.2.i")), ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))]
    [Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.2.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp78.i" "%i.4.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv77]

/-- `if.end77.i`'s `%cmp78.i`-taken edge from `land.lhs.true40.i`. -/
theorem sl_77_step_from_40 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "land.lhs.true40.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "land.lhs.true80.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_40 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`'s other edge from `land.lhs.true40.i`. -/
theorem sl_77_step_end_from_40 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "land.lhs.true40.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "if.end138.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_40 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`'s chain from `if.end37.i`. -/
theorem sl_77_denote_from_37 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "if.end37.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_77 (stateAt env s) =
      some (stateAt (slEnv77 env i n) s) := by
  unfold slInstrs_77
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.2.i")
    (v := .int 64 i) calls env s "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")), ("if.end37.i", (Operand.reg "%i.2.i")), ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))]
    [Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.2.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp78.i" "%i.4.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv77]

/-- `if.end77.i`'s `%cmp78.i`-taken edge from `if.end37.i`. -/
theorem sl_77_step_from_37 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "if.end37.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "land.lhs.true80.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_37 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`'s other edge from `if.end37.i`. -/
theorem sl_77_step_end_from_37 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "if.end37.i")
    (hi : lookupName env "%i.2.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "if.end138.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_37 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`'s chain from `land.lhs.true63.i`. -/
theorem sl_77_denote_from_63 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "land.lhs.true63.i")
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_77 (stateAt env s) =
      some (stateAt (slEnv77 env i n) s) := by
  unfold slInstrs_77
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.3265.i")
    (v := .int 64 i) calls env s "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")), ("if.end37.i", (Operand.reg "%i.2.i")), ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))]
    [Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.3265.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp78.i" "%i.4.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv77]

/-- `if.end77.i`'s `%cmp78.i`-taken edge from `land.lhs.true63.i`. -/
theorem sl_77_step_from_63 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "land.lhs.true63.i")
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "land.lhs.true80.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_63 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end77.i`'s other edge from `land.lhs.true63.i`. -/
theorem sl_77_step_end_from_63 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end77.i") (hpre : s.pre = some "land.lhs.true63.i")
    (hi : lookupName env "%i.3265.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv77 env i n)
        { s with pc := "if.end138.i", pre := some "if.end77.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv77 env i n) s)
    (b := ⟨"if.end77.i", slInstrs_77,
      Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_77
  · simpa only [stateAt] using sl_77_denote_from_63 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp78.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]


/-- `if.end106.i`, from its pin. -/
def slInstrs_106 : List Instr :=
  [Instr.phi "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")), ("if.then90.i", (Operand.reg "%inc91.i")), ("LeafBlock15", (Operand.reg "%inc91.i")), ("LeafBlock17", (Operand.reg "%inc91.i"))],
   Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")]

theorem sl_find_106 :
    numFastBody.findBlock "if.end106.i" =
      some ⟨"if.end106.i", slInstrs_106,
        Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩ := by
  simpa only [slInstrs_106] using numFast_findBlock_if_end106_i

/-- `if.end106.i`'s chain from `if.then104.i`. -/
theorem sl_106_denote_from_104 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "if.then104.i")
    (hi : lookupName env "%inc105.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_106 (stateAt env s) =
      some (stateAt (slEnv106 env i n) s) := by
  unfold slInstrs_106
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc105.i")
    (v := .int 64 i) calls env s "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")), ("if.then90.i", (Operand.reg "%inc91.i")), ("LeafBlock15", (Operand.reg "%inc91.i")), ("LeafBlock17", (Operand.reg "%inc91.i"))]
    [Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc105.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp107.not.i" "%i.5.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv106]

/-- `if.end106.i`'s `%cmp107.not.i`-taken edge from `if.then104.i`. -/
theorem sl_106_step_from_104 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "if.then104.i")
    (hi : lookupName env "%inc105.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "lor.lhs.false109.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_104 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s other edge from `if.then104.i`. -/
theorem sl_106_step_end_from_104 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "if.then104.i")
    (hi : lookupName env "%inc105.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "if.then119.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_104 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s chain from `if.then90.i`. -/
theorem sl_106_denote_from_90 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "if.then90.i")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_106 (stateAt env s) =
      some (stateAt (slEnv106 env i n) s) := by
  unfold slInstrs_106
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc91.i")
    (v := .int 64 i) calls env s "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")), ("if.then90.i", (Operand.reg "%inc91.i")), ("LeafBlock15", (Operand.reg "%inc91.i")), ("LeafBlock17", (Operand.reg "%inc91.i"))]
    [Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc91.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp107.not.i" "%i.5.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv106]

/-- `if.end106.i`'s `%cmp107.not.i`-taken edge from `if.then90.i`. -/
theorem sl_106_step_from_90 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "if.then90.i")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "lor.lhs.false109.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_90 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s other edge from `if.then90.i`. -/
theorem sl_106_step_end_from_90 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "if.then90.i")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "if.then119.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_90 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s chain from `LeafBlock15`. -/
theorem sl_106_denote_from_leaf15 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "LeafBlock15")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_106 (stateAt env s) =
      some (stateAt (slEnv106 env i n) s) := by
  unfold slInstrs_106
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc91.i")
    (v := .int 64 i) calls env s "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")), ("if.then90.i", (Operand.reg "%inc91.i")), ("LeafBlock15", (Operand.reg "%inc91.i")), ("LeafBlock17", (Operand.reg "%inc91.i"))]
    [Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc91.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp107.not.i" "%i.5.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv106]

/-- `if.end106.i`'s `%cmp107.not.i`-taken edge from `LeafBlock15`. -/
theorem sl_106_step_from_leaf15 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "LeafBlock15")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "lor.lhs.false109.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_leaf15 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s other edge from `LeafBlock15`. -/
theorem sl_106_step_end_from_leaf15 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "LeafBlock15")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "if.then119.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_leaf15 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s chain from `LeafBlock17`. -/
theorem sl_106_denote_from_leaf17 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "LeafBlock17")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_106 (stateAt env s) =
      some (stateAt (slEnv106 env i n) s) := by
  unfold slInstrs_106
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%inc91.i")
    (v := .int 64 i) calls env s "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")), ("if.then90.i", (Operand.reg "%inc91.i")), ("LeafBlock15", (Operand.reg "%inc91.i")), ("LeafBlock17", (Operand.reg "%inc91.i"))]
    [Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%inc91.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_ult_reg calls _ _ "%cmp107.not.i" "%i.5.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv106]

/-- `if.end106.i`'s `%cmp107.not.i`-taken edge from `LeafBlock17`. -/
theorem sl_106_step_from_leaf17 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "LeafBlock17")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "lor.lhs.false109.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_leaf17 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end106.i`'s other edge from `LeafBlock17`. -/
theorem sl_106_step_end_from_leaf17 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end106.i") (hpre : s.pre = some "LeafBlock17")
    (hi : lookupName env "%inc91.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv106 env i n)
        { s with pc := "if.then119.i", pre := some "if.end106.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv106 env i n) s)
    (b := ⟨"if.end106.i", slInstrs_106,
      Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_106
  · simpa only [stateAt] using sl_106_denote_from_leaf17 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp107.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]


/-- `if.end138.i`, from its pin. -/
def slInstrs_138 : List Instr :=
  [Instr.phi "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")), ("land.lhs.true124.i", (Operand.reg "%i.6269.i")), ("LeafBlock9", (Operand.reg "%i.4.i")), ("LeafBlock11", (Operand.reg "%i.4.i"))],
   Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")]

theorem sl_find_138 :
    numFastBody.findBlock "if.end138.i" =
      some ⟨"if.end138.i", slInstrs_138,
        Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩ := by
  simpa only [slInstrs_138] using numFast_findBlock_if_end138_i

/-- `if.end138.i`'s chain from `if.end77.i`. -/
theorem sl_138_denote_from_77 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "if.end77.i")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_138 (stateAt env s) =
      some (stateAt (slEnv138 env i n) s) := by
  unfold slInstrs_138
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.4.i")
    (v := .int 64 i) calls env s "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")), ("land.lhs.true124.i", (Operand.reg "%i.6269.i")), ("LeafBlock9", (Operand.reg "%i.4.i")), ("LeafBlock11", (Operand.reg "%i.4.i"))]
    [Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.4.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_eq_reg calls _ _ "%cmp139.not.i" "%i.7.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv138]

/-- `if.end138.i`'s `%cmp139.not.i`-taken edge from `if.end77.i`. -/
theorem sl_138_step_from_77 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "if.end77.i")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then143.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_77 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s other edge from `if.end77.i`. -/
theorem sl_138_step_end_from_77 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "if.end77.i")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then141.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_77 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s chain from `land.lhs.true124.i`. -/
theorem sl_138_denote_from_124 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "land.lhs.true124.i")
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_138 (stateAt env s) =
      some (stateAt (slEnv138 env i n) s) := by
  unfold slInstrs_138
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.6269.i")
    (v := .int 64 i) calls env s "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")), ("land.lhs.true124.i", (Operand.reg "%i.6269.i")), ("LeafBlock9", (Operand.reg "%i.4.i")), ("LeafBlock11", (Operand.reg "%i.4.i"))]
    [Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.6269.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_eq_reg calls _ _ "%cmp139.not.i" "%i.7.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv138]

/-- `if.end138.i`'s `%cmp139.not.i`-taken edge from `land.lhs.true124.i`. -/
theorem sl_138_step_from_124 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "land.lhs.true124.i")
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then143.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_124 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s other edge from `land.lhs.true124.i`. -/
theorem sl_138_step_end_from_124 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "land.lhs.true124.i")
    (hi : lookupName env "%i.6269.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then141.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_124 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s chain from `LeafBlock9`. -/
theorem sl_138_denote_from_leaf9 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "LeafBlock9")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_138 (stateAt env s) =
      some (stateAt (slEnv138 env i n) s) := by
  unfold slInstrs_138
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.4.i")
    (v := .int 64 i) calls env s "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")), ("land.lhs.true124.i", (Operand.reg "%i.6269.i")), ("LeafBlock9", (Operand.reg "%i.4.i")), ("LeafBlock11", (Operand.reg "%i.4.i"))]
    [Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.4.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_eq_reg calls _ _ "%cmp139.not.i" "%i.7.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv138]

/-- `if.end138.i`'s `%cmp139.not.i`-taken edge from `LeafBlock9`. -/
theorem sl_138_step_from_leaf9 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "LeafBlock9")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then143.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_leaf9 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s other edge from `LeafBlock9`. -/
theorem sl_138_step_end_from_leaf9 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "LeafBlock9")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then141.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_leaf9 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s chain from `LeafBlock11`. -/
theorem sl_138_denote_from_leaf11 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpre : s.pre = some "LeafBlock11")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs_138 (stateAt env s) =
      some (stateAt (slEnv138 env i n) s) := by
  unfold slInstrs_138
  rw [NumFastTier3Copy.t3_denoteCode_phi1 (op := Operand.reg "%i.4.i")
    (v := .int 64 i) calls env s "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")), ("land.lhs.true124.i", (Operand.reg "%i.6269.i")), ("LeafBlock9", (Operand.reg "%i.4.i")), ("LeafBlock11", (Operand.reg "%i.4.i"))]
    [Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")]
    hpre (by simp [phiIncoming])
    (BlockEval.evalOperand_reg_of env s "%i.4.i" (.int 64 i) hi) (hst := by rfl)]
  rw [denoteCode_icmp_eq_reg calls _ _ "%cmp139.not.i" "%i.7.i" "%n" (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv138]

/-- `if.end138.i`'s `%cmp139.not.i`-taken edge from `LeafBlock11`. -/
theorem sl_138_step_from_leaf11 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "LeafBlock11")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then143.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_leaf11 hpre hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.end138.i`'s other edge from `LeafBlock11`. -/
theorem sl_138_step_end_from_leaf11 {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64}
    (hpc : s.pc = "if.end138.i") (hpre : s.pre = some "LeafBlock11")
    (hi : lookupName env "%i.4.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq i n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv138 env i n)
        { s with pc := "if.then141.i", pre := some "if.end138.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv138 env i n) s)
    (b := ⟨"if.end138.i", slInstrs_138,
      Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_138
  · simpa only [stateAt] using sl_138_denote_from_leaf11 hpre hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp139.not.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]


/-- `NodeBlock13`, from its pin. -/
def slInstrs_node13 : List Instr :=
  [Instr.icmp "%Pivot14" (IPred.slt) 8 (Operand.reg "%48")
     (Operand.imm (Const.int 8 0x65#8))]

theorem sl_find_node13 :
    numFastBody.findBlock "NodeBlock13" =
      some ⟨"NodeBlock13", slInstrs_node13,
        Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11"⟩ := by
  simpa only [slInstrs_node13] using numFast_findBlock_NodeBlock13

/-- `NodeBlock13`'s chain. -/
theorem sl_node13_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%48" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_node13 (stateAt env s) =
      some (stateAt (slEnvNode13 env b) s) := by
  unfold slInstrs_node13
  rw [denoteCode_icmp_imm_w calls env s "%Pivot14" "%48" .slt hb]
  simp only [denoteCode_nil, stateAt, slEnvNode13]

/-- `NodeBlock13`'s taken edge. -/
theorem sl_node13_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "NodeBlock13") (hpre : s.pre = some "land.lhs.true80.i")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .slt (vByte b) 0x65#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvNode13 env b)
        { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) := by
  refine numFast_step_at (s' := stateAt (slEnvNode13 env b) s)
    (b := ⟨"NodeBlock13", slInstrs_node13,
      Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_node13
  · simpa only [stateAt] using sl_node13_denote hb
  · rw [numFast_execTerm_condbr_one _ "%Pivot14" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `NodeBlock13`'s other edge. -/
theorem sl_node13_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "NodeBlock13") (hpre : s.pre = some "land.lhs.true80.i")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .slt (vByte b) 0x65#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvNode13 env b)
        { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) := by
  refine numFast_step_at (s' := stateAt (slEnvNode13 env b) s)
    (b := ⟨"NodeBlock13", slInstrs_node13,
      Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_node13
  · simpa only [stateAt] using sl_node13_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%Pivot14" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock11`, from its pin. -/
def slInstrs_leaf11 : List Instr :=
  [Instr.icmp "%SwitchLeaf12" (IPred.eq) 8 (Operand.reg "%48")
     (Operand.imm (Const.int 8 0x65#8))]

theorem sl_find_leaf11 :
    numFastBody.findBlock "LeafBlock11" =
      some ⟨"LeafBlock11", slInstrs_leaf11,
        Term.condbr (Operand.reg "%SwitchLeaf12") "if.then90.i" "if.end138.i"⟩ := by
  simpa only [slInstrs_leaf11] using numFast_findBlock_LeafBlock11

/-- `LeafBlock11`'s chain. -/
theorem sl_leaf11_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%48" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_leaf11 (stateAt env s) =
      some (stateAt (slEnvLeaf11 env b) s) := by
  unfold slInstrs_leaf11
  rw [denoteCode_icmp_imm_w calls env s "%SwitchLeaf12" "%48" .eq hb]
  simp only [denoteCode_nil, stateAt, slEnvLeaf11]

/-- `LeafBlock11`'s taken edge. -/
theorem sl_leaf11_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock11") (hpre : s.pre = some "NodeBlock13")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x65#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf11 env b)
        { s with pc := "if.then90.i", pre := some "LeafBlock11" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf11 env b) s)
    (b := ⟨"LeafBlock11", slInstrs_leaf11,
      Term.condbr (Operand.reg "%SwitchLeaf12") "if.then90.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf11
  · simpa only [stateAt] using sl_leaf11_denote hb
  · rw [numFast_execTerm_condbr_one _ "%SwitchLeaf12" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock11`'s other edge. -/
theorem sl_leaf11_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock11") (hpre : s.pre = some "NodeBlock13")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x65#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf11 env b)
        { s with pc := "if.end138.i", pre := some "LeafBlock11" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf11 env b) s)
    (b := ⟨"LeafBlock11", slInstrs_leaf11,
      Term.condbr (Operand.reg "%SwitchLeaf12") "if.then90.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf11
  · simpa only [stateAt] using sl_leaf11_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf12" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock9`, from its pin. -/
def slInstrs_leaf9 : List Instr :=
  [Instr.icmp "%SwitchLeaf10" (IPred.eq) 8 (Operand.reg "%48")
     (Operand.imm (Const.int 8 0x45#8))]

theorem sl_find_leaf9 :
    numFastBody.findBlock "LeafBlock9" =
      some ⟨"LeafBlock9", slInstrs_leaf9,
        Term.condbr (Operand.reg "%SwitchLeaf10") "if.then90.i" "if.end138.i"⟩ := by
  simpa only [slInstrs_leaf9] using numFast_findBlock_LeafBlock9

/-- `LeafBlock9`'s chain. -/
theorem sl_leaf9_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%48" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_leaf9 (stateAt env s) =
      some (stateAt (slEnvLeaf9 env b) s) := by
  unfold slInstrs_leaf9
  rw [denoteCode_icmp_imm_w calls env s "%SwitchLeaf10" "%48" .eq hb]
  simp only [denoteCode_nil, stateAt, slEnvLeaf9]

/-- `LeafBlock9`'s taken edge. -/
theorem sl_leaf9_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock9") (hpre : s.pre = some "NodeBlock13")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x45#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf9 env b)
        { s with pc := "if.then90.i", pre := some "LeafBlock9" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf9 env b) s)
    (b := ⟨"LeafBlock9", slInstrs_leaf9,
      Term.condbr (Operand.reg "%SwitchLeaf10") "if.then90.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf9
  · simpa only [stateAt] using sl_leaf9_denote hb
  · rw [numFast_execTerm_condbr_one _ "%SwitchLeaf10" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock9`'s other edge. -/
theorem sl_leaf9_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock9") (hpre : s.pre = some "NodeBlock13")
    (hb : lookupName env "%48" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x45#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf9 env b)
        { s with pc := "if.end138.i", pre := some "LeafBlock9" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf9 env b) s)
    (b := ⟨"LeafBlock9", slInstrs_leaf9,
      Term.condbr (Operand.reg "%SwitchLeaf10") "if.then90.i" "if.end138.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf9
  · simpa only [stateAt] using sl_leaf9_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf10" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `NodeBlock19`, from its pin. -/
def slInstrs_node19 : List Instr :=
  [Instr.icmp "%Pivot20" (IPred.slt) 8 (Operand.reg "%49")
     (Operand.imm (Const.int 8 0x2d#8))]

theorem sl_find_node19 :
    numFastBody.findBlock "NodeBlock19" =
      some ⟨"NodeBlock19", slInstrs_node19,
        Term.condbr (Operand.reg "%Pivot20") "LeafBlock15" "LeafBlock17"⟩ := by
  simpa only [slInstrs_node19] using numFast_findBlock_NodeBlock19

/-- `NodeBlock19`'s chain. -/
theorem sl_node19_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%49" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_node19 (stateAt env s) =
      some (stateAt (slEnvNode19 env b) s) := by
  unfold slInstrs_node19
  rw [denoteCode_icmp_imm_w calls env s "%Pivot20" "%49" .slt hb]
  simp only [denoteCode_nil, stateAt, slEnvNode19]

/-- `NodeBlock19`'s taken edge. -/
theorem sl_node19_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "NodeBlock19") (hpre : s.pre = some "land.lhs.true94.i")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .slt (vByte b) 0x2d#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvNode19 env b)
        { s with pc := "LeafBlock15", pre := some "NodeBlock19" }) := by
  refine numFast_step_at (s' := stateAt (slEnvNode19 env b) s)
    (b := ⟨"NodeBlock19", slInstrs_node19,
      Term.condbr (Operand.reg "%Pivot20") "LeafBlock15" "LeafBlock17"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_node19
  · simpa only [stateAt] using sl_node19_denote hb
  · rw [numFast_execTerm_condbr_one _ "%Pivot20" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `NodeBlock19`'s other edge. -/
theorem sl_node19_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "NodeBlock19") (hpre : s.pre = some "land.lhs.true94.i")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .slt (vByte b) 0x2d#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvNode19 env b)
        { s with pc := "LeafBlock17", pre := some "NodeBlock19" }) := by
  refine numFast_step_at (s' := stateAt (slEnvNode19 env b) s)
    (b := ⟨"NodeBlock19", slInstrs_node19,
      Term.condbr (Operand.reg "%Pivot20") "LeafBlock15" "LeafBlock17"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_node19
  · simpa only [stateAt] using sl_node19_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%Pivot20" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock17`, from its pin. -/
def slInstrs_leaf17 : List Instr :=
  [Instr.icmp "%SwitchLeaf18" (IPred.eq) 8 (Operand.reg "%49")
     (Operand.imm (Const.int 8 0x2d#8))]

theorem sl_find_leaf17 :
    numFastBody.findBlock "LeafBlock17" =
      some ⟨"LeafBlock17", slInstrs_leaf17,
        Term.condbr (Operand.reg "%SwitchLeaf18") "if.then104.i" "if.end106.i"⟩ := by
  simpa only [slInstrs_leaf17] using numFast_findBlock_LeafBlock17

/-- `LeafBlock17`'s chain. -/
theorem sl_leaf17_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%49" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_leaf17 (stateAt env s) =
      some (stateAt (slEnvLeaf17 env b) s) := by
  unfold slInstrs_leaf17
  rw [denoteCode_icmp_imm_w calls env s "%SwitchLeaf18" "%49" .eq hb]
  simp only [denoteCode_nil, stateAt, slEnvLeaf17]

/-- `LeafBlock17`'s taken edge. -/
theorem sl_leaf17_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock17") (hpre : s.pre = some "NodeBlock19")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x2d#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf17 env b)
        { s with pc := "if.then104.i", pre := some "LeafBlock17" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf17 env b) s)
    (b := ⟨"LeafBlock17", slInstrs_leaf17,
      Term.condbr (Operand.reg "%SwitchLeaf18") "if.then104.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf17
  · simpa only [stateAt] using sl_leaf17_denote hb
  · rw [numFast_execTerm_condbr_one _ "%SwitchLeaf18" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock17`'s other edge. -/
theorem sl_leaf17_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock17") (hpre : s.pre = some "NodeBlock19")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x2d#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf17 env b)
        { s with pc := "if.end106.i", pre := some "LeafBlock17" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf17 env b) s)
    (b := ⟨"LeafBlock17", slInstrs_leaf17,
      Term.condbr (Operand.reg "%SwitchLeaf18") "if.then104.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf17
  · simpa only [stateAt] using sl_leaf17_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf18" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock15`, from its pin. -/
def slInstrs_leaf15 : List Instr :=
  [Instr.icmp "%SwitchLeaf16" (IPred.eq) 8 (Operand.reg "%49")
     (Operand.imm (Const.int 8 0x2b#8))]

theorem sl_find_leaf15 :
    numFastBody.findBlock "LeafBlock15" =
      some ⟨"LeafBlock15", slInstrs_leaf15,
        Term.condbr (Operand.reg "%SwitchLeaf16") "if.then104.i" "if.end106.i"⟩ := by
  simpa only [slInstrs_leaf15] using numFast_findBlock_LeafBlock15

/-- `LeafBlock15`'s chain. -/
theorem sl_leaf15_denote {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hb : lookupName env "%49" = some (.int 8 (vByte b))) :
    denoteCode calls slInstrs_leaf15 (stateAt env s) =
      some (stateAt (slEnvLeaf15 env b) s) := by
  unfold slInstrs_leaf15
  rw [denoteCode_icmp_imm_w calls env s "%SwitchLeaf16" "%49" .eq hb]
  simp only [denoteCode_nil, stateAt, slEnvLeaf15]

/-- `LeafBlock15`'s taken edge. -/
theorem sl_leaf15_step_one {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock15") (hpre : s.pre = some "NodeBlock19")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x2b#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf15 env b)
        { s with pc := "if.then104.i", pre := some "LeafBlock15" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf15 env b) s)
    (b := ⟨"LeafBlock15", slInstrs_leaf15,
      Term.condbr (Operand.reg "%SwitchLeaf16") "if.then104.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf15
  · simpa only [stateAt] using sl_leaf15_denote hb
  · rw [numFast_execTerm_condbr_one _ "%SwitchLeaf16" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock15`'s other edge. -/
theorem sl_leaf15_step_zero {calls : Calls} {env : Env} {s : State} {b : UInt8}
    (hpc : s.pc = "LeafBlock15") (hpre : s.pre = some "NodeBlock19")
    (hb : lookupName env "%49" = some (.int 8 (vByte b)))
    (hbit : evalICmp .eq (vByte b) 0x2b#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLeaf15 env b)
        { s with pc := "if.end106.i", pre := some "LeafBlock15" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLeaf15 env b) s)
    (b := ⟨"LeafBlock15", slInstrs_leaf15,
      Term.condbr (Operand.reg "%SwitchLeaf16") "if.then104.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_leaf15
  · simpa only [stateAt] using sl_leaf15_denote hb
  · rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf16" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### `land.lhs.true80.i`, `NodeBlock13` and the marker's leaves

`land.lhs.true80.i` loads the byte the exponent test reads; the switch's pivot
and its two leaves accept `e` and `E`. -/

/-- `land.lhs.true80.i`, from its pin. -/
def slInstrs80 : List Instr :=
  [Instr.gep "%arrayidx81.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4.i"),
   Instr.load "%48" (Ty.int 8) (Operand.reg "%arrayidx81.i")]

theorem sl_find_80 :
    numFastBody.findBlock "land.lhs.true80.i" =
      some ⟨"land.lhs.true80.i", slInstrs80, Term.br "NodeBlock13"⟩ := by
  simpa only [slInstrs80] using numFast_findBlock_land_lhs_true80_i

/-- `land.lhs.true80.i`'s chain. -/
theorem sl_80_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i4 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.4.i" = some (.int 64 i4))
    (hpos : (i4.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i4.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs80 (stateAt env s) =
      some (stateAt (slEnv80 env p i4 b) s) := by
  unfold slInstrs80
  rw [denoteCode_gep8_reg calls env s "%arrayidx81.i" "%p" "%i.4.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%48" "%arrayidx81.i" (by sl_lk) hb]
  simp only [denoteCode_nil, stateAt, slEnv80]

/-- `land.lhs.true80.i`'s step. -/
theorem sl_80_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i4 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true80.i") (hpre : s.pre = some "if.end77.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.4.i" = some (.int 64 i4))
    (hpos : (i4.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i4.signExtend 64).toNat) 1 = some [b]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv80 env p i4 b)
        { s with pc := "NodeBlock13", pre := some "land.lhs.true80.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv80 env p i4 b) s)
    (b := ⟨"land.lhs.true80.i", slInstrs80, Term.br "NodeBlock13"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_80
  · simpa only [stateAt] using sl_80_denote hp hi hpos hb
  · simp only [execTerm, stateAt, hpc]

/-! ### `if.then90.i`, `land.lhs.true94.i` and the exponent's sign -/

/-- `if.then90.i`, from its pin. -/
def slInstrs90 : List Instr :=
  [Instr.binop "%inc91.i" (BinOp.add) 64 (Operand.reg "%i.4.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%cmp92.i" (IPred.ult) 64 (Operand.reg "%inc91.i") (Operand.reg "%n")]

theorem sl_find_90 :
    numFastBody.findBlock "if.then90.i" =
      some ⟨"if.then90.i", slInstrs90,
        Term.condbr (Operand.reg "%cmp92.i") "land.lhs.true94.i" "if.end106.i"⟩ := by
  simpa only [slInstrs90] using numFast_findBlock_if_then90_i

/-- `if.then90.i`'s chain. -/
theorem sl_90_denote {calls : Calls} {env : Env} {s : State} {i4 n : BitVec 64}
    (hi : lookupName env "%i.4.i" = some (.int 64 i4))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls slInstrs90 (stateAt env s) =
      some (stateAt (slEnv90 env i4 n) s) := by
  unfold slInstrs90
  rw [denoteCode_add_imm calls env s "%inc91.i" "%i.4.i" hi]
  rw [denoteCode_icmp_reg_w calls _ s "%cmp92.i" "%inc91.i" "%n" .ult 64
    (by sl_lk) (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnv90]

/-- `if.then90.i`'s step: there is a byte after the marker. -/
theorem sl_90_step {calls : Calls} {env : Env} {s : State} {i4 n : BitVec 64}
    (hpc : s.pc = "if.then90.i") (hpre : s.pre = some "LeafBlock11")
    (hi : lookupName env "%i.4.i" = some (.int 64 i4))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i4 + 1#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv90 env i4 n)
        { s with pc := "land.lhs.true94.i", pre := some "if.then90.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv90 env i4 n) s)
    (b := ⟨"if.then90.i", slInstrs90,
      Term.condbr (Operand.reg "%cmp92.i") "land.lhs.true94.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_90
  · simpa only [stateAt] using sl_90_denote hi hn
  · rw [numFast_execTerm_condbr_one _ "%cmp92.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `if.then90.i`'s other edge: the marker is the lexeme's last byte. -/
theorem sl_90_step_ne {calls : Calls} {env : Env} {s : State} {i4 n : BitVec 64}
    (hpc : s.pc = "if.then90.i") (hpre : s.pre = some "LeafBlock11")
    (hi : lookupName env "%i.4.i" = some (.int 64 i4))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i4 + 1#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv90 env i4 n)
        { s with pc := "if.end106.i", pre := some "if.then90.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv90 env i4 n) s)
    (b := ⟨"if.then90.i", slInstrs90,
      Term.condbr (Operand.reg "%cmp92.i") "land.lhs.true94.i" "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_90
  · simpa only [stateAt] using sl_90_denote hi hn
  · rw [numFast_execTerm_condbr_zero _ "%cmp92.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `land.lhs.true94.i`, from its pin. -/
def slInstrs94 : List Instr :=
  [Instr.gep "%arrayidx95.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc91.i"),
   Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx95.i")]

theorem sl_find_94 :
    numFastBody.findBlock "land.lhs.true94.i" =
      some ⟨"land.lhs.true94.i", slInstrs94, Term.br "NodeBlock19"⟩ := by
  simpa only [slInstrs94] using numFast_findBlock_land_lhs_true94_i

/-- `land.lhs.true94.i`'s chain: the exponent's sign byte. -/
theorem sl_94_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i4 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc91.i" = some (.int 64 (i4 + 1#64)))
    (hpos : ((i4 + 1#64).signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + ((i4 + 1#64).signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrs94 (stateAt env s) =
      some (stateAt (slEnv94 env p i4 b) s) := by
  unfold slInstrs94
  rw [denoteCode_gep8_reg calls env s "%arrayidx95.i" "%p" "%inc91.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%49" "%arrayidx95.i" (by sl_lk) hb]
  simp only [denoteCode_nil, stateAt, slEnv94]

/-- `land.lhs.true94.i`'s step. -/
theorem sl_94_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i4 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "land.lhs.true94.i") (hpre : s.pre = some "if.then90.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%inc91.i" = some (.int 64 (i4 + 1#64)))
    (hpos : ((i4 + 1#64).signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + ((i4 + 1#64).signExtend 64).toNat) 1 = some [b]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv94 env p i4 b)
        { s with pc := "NodeBlock19", pre := some "land.lhs.true94.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv94 env p i4 b) s)
    (b := ⟨"land.lhs.true94.i", slInstrs94, Term.br "NodeBlock19"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_94
  · simpa only [stateAt] using sl_94_denote hp hi hpos hb
  · simp only [execTerm, stateAt, hpc]

/-- `if.then104.i`, from its pin. -/
def slInstrs104 : List Instr :=
  [Instr.binop "%inc105.i" (BinOp.add) 64 (Operand.reg "%i.4.i")
     (Operand.imm (Const.int 64 0x0000000000000002#64))]

theorem sl_find_104 :
    numFastBody.findBlock "if.then104.i" =
      some ⟨"if.then104.i", slInstrs104, Term.br "if.end106.i"⟩ := by
  simpa only [slInstrs104] using numFast_findBlock_if_then104_i

/-- `if.then104.i`'s chain: the marker, its sign, and the digit after it. -/
theorem sl_104_denote {calls : Calls} {env : Env} {s : State} {i4 : BitVec 64}
    (hi : lookupName env "%i.4.i" = some (.int 64 i4)) :
    denoteCode calls slInstrs104 (stateAt env s) =
      some (stateAt (slEnv104 env i4) s) := by
  unfold slInstrs104
  rw [denoteCode_add_imm calls env s "%inc105.i" "%i.4.i" hi]
  simp only [denoteCode_nil, stateAt, slEnv104]

/-- `if.then104.i`'s step. -/
theorem sl_104_step {calls : Calls} {env : Env} {s : State} {i4 : BitVec 64}
    (hpc : s.pc = "if.then104.i") (hpre : s.pre = some "LeafBlock17")
    (hi : lookupName env "%i.4.i" = some (.int 64 i4)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnv104 env i4)
        { s with pc := "if.end106.i", pre := some "if.then104.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnv104 env i4) s)
    (b := ⟨"if.then104.i", slInstrs104, Term.br "if.end106.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_104
  · simpa only [stateAt] using sl_104_denote hi
  · simp only [execTerm, stateAt, hpc]

/-! ### `lor.lhs.false109.i`: the exponent's first digit -/

/-- `lor.lhs.false109.i`, from its pin. -/
def slInstrsLor109 : List Instr :=
  [Instr.gep "%arrayidx110.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5.i"),
   Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx110.i"),
   Instr.binop "%51" (BinOp.add) 8 (Operand.reg "%50") (Operand.imm (Const.int 8 0xc6#8)),
   Instr.icmp "%or.cond225.i" (IPred.ult) 8 (Operand.reg "%51")
     (Operand.imm (Const.int 8 0xf6#8))]

theorem sl_find_lor109 :
    numFastBody.findBlock "lor.lhs.false109.i" =
      some ⟨"lor.lhs.false109.i", slInstrsLor109,
        Term.condbr (Operand.reg "%or.cond225.i") "if.then119.i" "land.lhs.true124.i"⟩ := by
  simpa only [slInstrsLor109] using numFast_findBlock_lor_lhs_false109_i

/-- `lor.lhs.false109.i`'s chain. -/
theorem sl_lor109_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i5 : BitVec 64} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i5))
    (hpos : (i5.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i5.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls slInstrsLor109 (stateAt env s) =
      some (stateAt (slEnvLor109 env p i5 b) s) := by
  unfold slInstrsLor109
  rw [denoteCode_gep8_reg calls env s "%arrayidx110.i" "%p" "%i.5.i" hp hi hpos]
  rw [denoteCode_load_i8 calls _ s "%50" "%arrayidx110.i" (by sl_lk) hb]
  rw [denoteCode_add_imm_w calls _ s "%51" "%50" 8 (by sl_lk)]
  rw [denoteCode_icmp_imm_w calls _ s "%or.cond225.i" "%51" .ult (by sl_lk)]
  simp only [denoteCode_nil, stateAt, slEnvLor109]

/-- `lor.lhs.false109.i`'s refusing edge. -/
theorem sl_lor109_step {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i5 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "lor.lhs.false109.i") (hpre : s.pre = some "if.end106.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i5))
    (hpos : (i5.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i5.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xc6#8) 0xf6#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLor109 env p i5 b)
        { s with pc := "if.then119.i", pre := some "lor.lhs.false109.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLor109 env p i5 b) s)
    (b := ⟨"lor.lhs.false109.i", slInstrsLor109,
      Term.condbr (Operand.reg "%or.cond225.i") "if.then119.i" "land.lhs.true124.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_lor109
  · simpa only [stateAt] using sl_lor109_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_one _ "%or.cond225.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-- `lor.lhs.false109.i`'s edge into the exponent's digits. -/
theorem sl_lor109_step_ne {calls : Calls} {env : Env} {s : State}
    {p : Nat} {i5 : BitVec 64} {b : UInt8}
    (hpc : s.pc = "lor.lhs.false109.i") (hpre : s.pre = some "if.end106.i")
    (hp : lookupName env "%p" = some (.ptr p))
    (hi : lookupName env "%i.5.i" = some (.int 64 i5))
    (hpos : (i5.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (i5.signExtend 64).toNat) 1 = some [b])
    (hbit : evalICmp .ult (vByte b + 0xc6#8) 0xf6#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEnvLor109 env p i5 b)
        { s with pc := "land.lhs.true124.i", pre := some "lor.lhs.false109.i" }) := by
  refine numFast_step_at (s' := stateAt (slEnvLor109 env p i5 b) s)
    (b := ⟨"lor.lhs.false109.i", slInstrsLor109,
      Term.condbr (Operand.reg "%or.cond225.i") "if.then119.i" "land.lhs.true124.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_lor109
  · simpa only [stateAt] using sl_lor109_denote hp hi hpos hb
  · rw [numFast_execTerm_condbr_zero _ "%or.cond225.i" _ _ (by sl_env; sl_lk) hbit]
    simp only [stateAt, hpc]

/-! ### The refusal exits

Five blocks store the reader's stop index at `%err` and leave for `cleanup300`:
`if.then5.i` (an empty lexeme), `if.else35.i` (a non-digit first byte),
`if.then58.i` (a `.` with no fraction digit), `if.then119.i` (an exponent
marker or sign with no digit), and `if.then141.i` (a digit run that does not
reach the lexeme's end). -/

/-- A store of a 64-bit immediate, as a chain step. -/
theorem sl_store64_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 64) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hs : storeValue (stateAt env s) (.int 64) (.int 64 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    simp [storeValue, stateAt, show (64 + 7) / 8 = 8 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 64 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
      (hv := evalOperand_lit_of (stateAt env s) 64 x)
      (hp := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s p (.ptr a) hp)
      (hs := hs)])]

/-- `if.then5.i`, from its pin. -/
def slInstrsErr1 : List Instr :=
  [Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64))
     (Operand.reg "%err")]

theorem sl_find_err1 :
    numFastBody.findBlock "if.then5.i" =
      some ⟨"if.then5.i", slInstrsErr1, Term.br "cleanup300"⟩ := by
  simpa only [slInstrsErr1] using numFast_findBlock_if_then5_i

/-- The empty lexeme's exit: the stop index is one. -/
theorem sl_err1_step {calls : Calls} {env : Env} {s : State} {e : Nat}
    (hpc : s.pc = "if.then5.i") (hpre : s.pre = some "if.end285")
    (he : lookupName env "%err" = some (.ptr e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env (slErrState s e (1#64) "if.then5.i")) := by
  refine numFast_step_at (s' := stateAt env
      ({ s with mem := writeBytes s.mem e (natToBytes (1#64).toNat 8) }))
    (b := ⟨"if.then5.i", slInstrsErr1, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_err1
  · show denoteCode calls slInstrsErr1 (stateAt env s) = _
    unfold slInstrsErr1
    rw [sl_store64_imm calls env s (0x0000000000000001#64) "%err" he]
    simp only [denoteCode_nil, stateAt]
  · simp only [execTerm, stateAt, hpc, slErrState]

/-- `if.else35.i`, from its pin. -/
def slInstrsErr35 : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%i.0.i") (Operand.reg "%err")]

theorem sl_find_err35 :
    numFastBody.findBlock "if.else35.i" =
      some ⟨"if.else35.i", slInstrsErr35, Term.br "cleanup300"⟩ := by
  simpa only [slInstrsErr35] using numFast_findBlock_if_else35_i

/-- The non-digit first byte's exit: the stop index is the sign's index. -/
theorem sl_err35_step {calls : Calls} {env : Env} {s : State} {e : Nat} {i0 : BitVec 64}
    (hpc : s.pc = "if.else35.i") (hpre : s.pre = some "if.else.i")
    (hi : lookupName env "%i.0.i" = some (.int 64 i0))
    (he : lookupName env "%err" = some (.ptr e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env (slErrState s e i0 "if.else35.i")) := by
  refine numFast_step_at (s' := stateAt env
      ({ s with mem := writeBytes s.mem e (natToBytes i0.toNat 8) }))
    (b := ⟨"if.else35.i", slInstrsErr35, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_err35
  · show denoteCode calls slInstrsErr35 (stateAt env s) = _
    unfold slInstrsErr35
    rw [denoteCode_store64 calls env s "%i.0.i" "%err" hi he]
    simp only [denoteCode_nil, stateAt]
  · simp only [execTerm, stateAt, hpc, slErrState]

/-- `if.then58.i`, from its pin. -/
def slInstrsErr58 : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%inc46.i") (Operand.reg "%err")]

theorem sl_find_err58 :
    numFastBody.findBlock "if.then58.i" =
      some ⟨"if.then58.i", slInstrsErr58, Term.br "cleanup300"⟩ := by
  simpa only [slInstrsErr58] using numFast_findBlock_if_then58_i

/-- The empty fraction's exit. -/
theorem sl_err58_step {calls : Calls} {env : Env} {s : State} {e : Nat} {i2 : BitVec 64}
    (hpc : s.pc = "if.then58.i") (hpre : s.pre = some "if.then45.i")
    (hi : lookupName env "%inc46.i" = some (.int 64 (i2 + 1#64)))
    (he : lookupName env "%err" = some (.ptr e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env (slErrState s e (i2 + 1#64) "if.then58.i")) := by
  refine numFast_step_at (s' := stateAt env
      ({ s with mem := writeBytes s.mem e (natToBytes (i2 + 1#64).toNat 8) }))
    (b := ⟨"if.then58.i", slInstrsErr58, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_err58
  · show denoteCode calls slInstrsErr58 (stateAt env s) = _
    unfold slInstrsErr58
    rw [denoteCode_store64 calls env s "%inc46.i" "%err" hi he]
    simp only [denoteCode_nil, stateAt]
  · simp only [execTerm, stateAt, hpc, slErrState]

/-- `if.then119.i`, from its pin. -/
def slInstrsErr119 : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%i.5.i") (Operand.reg "%err")]

theorem sl_find_err119 :
    numFastBody.findBlock "if.then119.i" =
      some ⟨"if.then119.i", slInstrsErr119, Term.br "cleanup300"⟩ := by
  simpa only [slInstrsErr119] using numFast_findBlock_if_then119_i

/-- The empty exponent's exit. -/
theorem sl_err119_step {calls : Calls} {env : Env} {s : State} {e : Nat} {i5 : BitVec 64}
    (hpc : s.pc = "if.then119.i") (hpre : s.pre = some "if.end106.i")
    (hi : lookupName env "%i.5.i" = some (.int 64 i5))
    (he : lookupName env "%err" = some (.ptr e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env (slErrState s e i5 "if.then119.i")) := by
  refine numFast_step_at (s' := stateAt env
      ({ s with mem := writeBytes s.mem e (natToBytes i5.toNat 8) }))
    (b := ⟨"if.then119.i", slInstrsErr119, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_err119
  · show denoteCode calls slInstrsErr119 (stateAt env s) = _
    unfold slInstrsErr119
    rw [denoteCode_store64 calls env s "%i.5.i" "%err" hi he]
    simp only [denoteCode_nil, stateAt]
  · simp only [execTerm, stateAt, hpc, slErrState]

/-- `if.then141.i`, from its pin. -/
def slInstrsErr141 : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%i.7.i") (Operand.reg "%err")]

theorem sl_find_err141 :
    numFastBody.findBlock "if.then141.i" =
      some ⟨"if.then141.i", slInstrsErr141, Term.br "cleanup300"⟩ := by
  simpa only [slInstrsErr141] using numFast_findBlock_if_then141_i

/-- The short digit run's exit. -/
theorem sl_err141_step {calls : Calls} {env : Env} {s : State} {e : Nat} {i7 : BitVec 64}
    (hpc : s.pc = "if.then141.i") (hpre : s.pre = some "if.end138.i")
    (hi : lookupName env "%i.7.i" = some (.int 64 i7))
    (he : lookupName env "%err" = some (.ptr e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env (slErrState s e i7 "if.then141.i")) := by
  refine numFast_step_at (s' := stateAt env
      ({ s with mem := writeBytes s.mem e (natToBytes i7.toNat 8) }))
    (b := ⟨"if.then141.i", slInstrsErr141, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_err141
  · show denoteCode calls slInstrsErr141 (stateAt env s) = _
    unfold slInstrsErr141
    rw [denoteCode_store64 calls env s "%i.7.i" "%err" hi he]
    simp only [denoteCode_nil, stateAt]
  · simp only [execTerm, stateAt, hpc, slErrState]

/-! ### `if.then143.i`: the digit array's lifetime and the handoff

The reader's last block starts the 768-byte array's lifetime and jumps to
`to_double`'s entry.  The array's base is `entry`'s first allocation, so it is
the caller's cell and the block's own step is the call and the jump. -/

/-- `if.then143.i`, from its pin. -/
def slInstrs143 : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
      (Ty.ptr, (Operand.reg "%dig.i.i"))]]

theorem sl_find_143 :
    numFastBody.findBlock "if.then143.i" =
      some ⟨"if.then143.i", slInstrs143, Term.br "for.body.outer.i.outer.i"⟩ := by
  simpa only [slInstrs143] using numFast_findBlock_if_then143_i

/-- `if.then143.i`'s chain: the marker's call, at the array's base. -/
theorem sl_143_denote {calls : Calls} {env : Env} {s : State} {digA : Nat}
    {r : CallOutcome}
    (hd : lookupName env "%dig.i.i" = some (.ptr digA))
    (hstart : calls "llvm.lifetime.start.p0" [.int 64 0x0000000000000300#64, .ptr digA]
      s.mem s.next = some r) :
    denoteCode calls slInstrs143 (stateAt env s) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  unfold slInstrs143
  rw [denoteCode_callVoid_some (calls := calls) (env := env) (s := s)
    (callee := "llvm.lifetime.start.p0")
    (args := [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
      (Ty.ptr, (Operand.reg "%dig.i.i"))])
    (vs := [.int 64 0x0000000000000300#64, .ptr digA]) (r := r)
    (evalOperands_lifetimeMark (s := s) (w := 0x300) hd) hstart []]
  rw [denoteCode_nil]

/-- `if.then143.i`'s step: the array starts and the reader hands to `to_double`. -/
theorem sl_143_step {calls : Calls} {env : Env} {s : State} {digA : Nat}
    {r : CallOutcome}
    (hpc : s.pc = "if.then143.i") (hpre : s.pre = some "if.end138.i")
    (hd : lookupName env "%dig.i.i" = some (.ptr digA))
    (hstart : calls "llvm.lifetime.start.p0" [.int 64 0x0000000000000300#64, .ptr digA]
      s.mem s.next = some r) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env ({ s with mem := r.mem, next := r.next, pre := some "if.then143.i", pc := "for.body.outer.i.outer.i" })) := by
  refine numFast_step_at
    (s' := stateAt env ({ s with mem := r.mem, next := r.next }))
    (b := ⟨"if.then143.i", slInstrs143, Term.br "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_143
  · simpa only [stateAt] using sl_143_denote hd hstart
  · simp only [execTerm, stateAt, hpc]

/-! ### `for.body.outer.i.outer.i`: the ten-`phi` run at the copy's entry

`if.then143.i` has started the digit array's lifetime and jumped here.  The block
binds the ten cells `to_double`'s own parse carries: the digit cursor at the
sign's index, the six accumulators at zero, and the three flags at zero, with the
lexeme and the array's base carried through from `slCarry`.  Its terminator
continues at `for.body.outer.i.i`; the peel between there and the copy's head is
the region's interior, not this module's. -/

/-- `for.body.outer.i.outer.i`, from its pin. -/
def slInstrsEntry : List Instr :=
  [Instr.phi "%i.1725.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.reg "%i.0.i")),
      ("for.inc.i.i", (Operand.reg "%inc57.i.i"))],
   Instr.phi "%R.0724.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%R.4.ph.i.i"))],
   Instr.phi "%T.0723.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%T.2.ph.i.i"))],
   Instr.phi "%F.0722.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%F.3.ph.i.i"))],
   Instr.phi "%lead.0721.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%lead.0721.i287.i"))],
   Instr.phi "%top.0720.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%top.4.ph.i.i"))],
   Instr.phi "%topn.0719.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc.i.i", (Operand.reg "%topn.4.ph.i.i"))],
   Instr.phi "%in_frac.0718.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
      ("for.inc.i.i", (Operand.reg "%in_frac.2.ph.i.i"))],
   Instr.phi "%seen.0717.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
      ("for.inc.i.i", (Operand.reg "%seen.4.ph.i.i"))],
   Instr.phi "%sticky.0716.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
      ("for.inc.i.i", (Operand.reg "%sticky.4.ph.i.i"))]]

theorem sl_find_entry :
    numFastBody.findBlock "for.body.outer.i.outer.i" =
      some ⟨"for.body.outer.i.outer.i", slInstrsEntry, Term.br "for.body.outer.i.i"⟩ := by
  simpa only [slInstrsEntry] using numFast_findBlock_for_body_outer_i_outer_i

/-- `for.body.outer.i.outer.i`'s chain: the ten `phi`s at `if.then143.i`'s edge. -/
theorem sl_entry_denote {calls : Calls} {env : Env} {s : State} {i0 : BitVec 64}
    (hpre : s.pre = some "if.then143.i")
    (hi : lookupName env "%i.0.i" = some (.int 64 i0)) :
    denoteCode calls slInstrsEntry (stateAt env s) =
      some (stateAt (slEntry env i0) s) := by
  unfold slInstrsEntry
  block_phi_run
  all_goals block_close

/-- `for.body.outer.i.outer.i`'s step: the reader hands the copy its ten cells. -/
theorem sl_entry_step {calls : Calls} {env : Env} {s : State} {i0 : BitVec 64}
    (hpc : s.pc = "for.body.outer.i.outer.i")
    (hpre : s.pre = some "if.then143.i")
    (hi : lookupName env "%i.0.i" = some (.int 64 i0)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (slEntry env i0) ({ s with pc := "for.body.outer.i.i", pre := some "for.body.outer.i.outer.i" })) := by
  refine numFast_step_at (s' := stateAt (slEntry env i0) s)
    (b := ⟨"for.body.outer.i.outer.i", slInstrsEntry, Term.br "for.body.outer.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sl_find_entry
  · simpa only [stateAt] using sl_entry_denote hpre hi
  · simp only [execTerm, stateAt, hpc]

/-- The cells the entry leaves: the copy's ten carried registers, at the values
`slEntry` binds. -/
def slEntryFields (env : Env) (i0 : BitVec 64) : Prop :=
  lookupName env "%i.1725.ph.i.ph.i" = some (.int 64 i0) ∧
  lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%T.0723.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%F.0722.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%lead.0721.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 0#64) ∧
  lookupName env "%in_frac.0718.ph.i.ph.i" = some (.int 32 0#32) ∧
  lookupName env "%seen.0717.ph.i.ph.i" = some (.int 32 0#32) ∧
  lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 0#32)

/-- The entry's ten cells are the ones `slEntry` builds. -/
theorem sl_entry_fields (env : Env) (i0 : BitVec 64) : slEntryFields (slEntry env i0) i0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (simp only [slEntry]; sl_lk)

/-! ### The sign's byte against the decomposition

The reader's `%cmp1.i` and `%i.0.i` are the first byte's `-` test and the index it
makes.  The decomposition's sign is `Decimal.neg`, and the two agree on every
well-formed lexeme: a leading `minus` puts `0x2D` first, and no other shape can,
because an `IntPart` starts with a digit.  So the cells the copy carries at its
entry are the model's sign bit and sign index, which is how `StrtodTier3`'s
`tier3Mag`/`tier3Emitted` read the same lexeme. -/

/-- The reader's sign test as an `if`: `1` exactly at a leading `minus`. -/
theorem slSignBit_eq (b : UInt8) :
    slSignBit b = (if b = 0x2D then 1 else 0) := by
  unfold slSignBit
  by_cases h : b = 0x2D
  · subst h
    simp only [evalICmp]
    decide
  · have hne : ¬ (JsonScanLane.vByte b = (0x2d#8 : BitVec 8)) := by
      intro hv
      exact h (NumFastStarts.vByte_inj hv)
    simp only [evalICmp]
    rw [ite_eq_right h, decide_eq_false hne]
    rfl

/-- **The reader's sign bit is the model's.**  A well-formed lexeme's first byte
is `0x2D` exactly at `Decimal.neg`, so `%cmp1.i` is the decomposition's sign. -/
theorem sl_sign_tie {d : Decimal} {b0 : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b0) :
    slSignBit b0 = (if d.neg then 1 else 0) := by
  have hiff : b0 = 0x2D ↔ d.neg = true := by
    constructor
    · intro hb0
      by_contra hneg
      have hfalse : d.neg = false := by
        cases hd' : d.neg <;> simp_all
      obtain ⟨b, rest, hbx, hne⟩ := NumFastSign.lexeme_head_pos hd hfalse
      have hbeq : b = b0 := by
        rw [hbx] at hb
        simpa only [List.head?_cons, Option.some.injEq] using hb
      exact hne (hbeq.trans hb0)
    · intro htrue
      have hn := NumFastSign.lexeme_head_neg htrue
      rw [hn] at hb
      simpa only [Option.some.injEq] using hb.symm
  rw [slSignBit_eq]
  cases hd' : d.neg with
  | false =>
      have hbne : ¬ (b0 = 0x2D) := fun hb0 => by
        have h := hiff.mp hb0
        rw [hd'] at h
        exact Bool.noConfusion h
      rw [if_neg hbne]
      rfl
  | true =>
      have hb0 : b0 = 0x2D := hiff.mpr hd'
      rw [if_pos hb0]
      rfl

/-- **The reader's sign index is the model's.**  `%i.0.i` is the sign bit as a
sixty-four-bit word, so at a well-formed lexeme it is `1` exactly at a negative
decomposition. -/
theorem sl_signIdx_tie {d : Decimal} {b0 : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b0) :
    slSignIdx b0 = (if d.neg then 1#64 else 0#64) := by
  unfold slSignIdx
  rw [sl_sign_tie hd hb]
  cases hd' : d.neg <;> rfl

/-- **The scan's model fields at the copy's entry.**  The entry's ten cells, the
sign bit and the sign index are read against the decomposition: the cursor is the
sign's index, the accumulators and flags are zero, `%cmp1.i` is `1` exactly at
`d.neg`, and the index is `d.neg`'s word.  This is the statement the fallback's
seam carries to the copy, whose `F`/`T` parse reads exactly these cells. -/
theorem sl_entry_model {env : Env} {p n digA : Nat} {b0 : UInt8} {sgn : BitVec 1}
    {i0 : BitVec 64} {d : Decimal} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b0)
    (hsgn : sgn = slSignBit b0) (hi0 : i0 = slSignIdx b0) :
    slEntryFields (slEntry (slCarry env p n i0 sgn digA) i0) i0 ∧
    lookupName (slEntry (slCarry env p n i0 sgn digA) i0) "%cmp1.i"
      = some (.int 1 sgn) ∧
    (sgn = 1 ↔ d.neg = true) ∧
    i0 = (if d.neg then 1#64 else 0#64) := by
  refine ⟨sl_entry_fields _ _, ?_, ?_, ?_⟩
  · simp only [slEntry]
    sl_carry
  · subst hsgn
    rw [sl_sign_tie hd hb]
    cases hd' : d.neg <;> decide
  · subst hi0
    exact sl_signIdx_tie hd hb

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sl_entry_denote

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_entry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sl_entry_step

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_entry_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sl_entry_fields

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_sign_tie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sl_sign_tie

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_signIdx_tie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sl_signIdx_tie

/-- info: 'LeanLLVM.Refinement.NumFastScanSlow.sl_entry_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sl_entry_model

end NumFastScanSlow

end LeanLLVM.Refinement
