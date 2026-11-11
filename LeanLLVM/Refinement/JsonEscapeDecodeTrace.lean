/-
The decoder's run at the pinned body, block by block.

`@us_dec_x` is one program: it walks the caller's position list, copying the bytes
between positions and decoding each escape, then copies the rest of the body in
whole vectors.  `JsonEscapeExpandContract` states the invariant the loop carries —
`DecodeInv`, against the specification's own recursion — and where a run of the body
is a run of that invariant.  This module states the other half: what the pinned
body's blocks actually do, as the cells their successors read and the memory they
leave.

The shape is the one `JsonEscapeListWriter` and `JsonEscapeListRun` use for the
other bodies of the unit: a block's `denoteCode` is stated as the memory it leaves
(`Option.map State.mem`) together with the lookups of the registers the next block
reads, and its step is the `condbr` arm at the value the block computed.  A block
that writes memory names the memory expression it leaves, so a chain of blocks
composes by rewriting one expression into the next rather than by carrying a whole
environment through every lemma.

What is here is the front of the run and both copy loops: `entry`, `land.rhs`,
`while.body`, `while.end`, `while.body6`, `if.end`, `if.end.i`, `if.then6.i`,
`if.end9.i`, `if.end.i115`, the
two refusals, `us_run.exit`, `us_run.exit112`, `cleanup41`, and the two
double-word copies with their tails
(`while.body.i91`/`us_run_long.exit99`/`if.then.i104` and
`while.body.i`/`us_run_long.exit`/`if.then.i109`).  Each block is a `denoteCode`
fact naming its memory expression and a run fact naming the cells its successors
read, and each branch is the `condbr` arm at the value the block computed.

The hex reader's tests and its value are bridged to the specification's own
vocabulary in the same module: `hexDigit_lane` and `hexLaneTest_iff` identify a
lane test with `hexDigit`'s success, `hexTest_low_four` identifies the masked
four-lane aggregate with the four tests, and `pmadd_hexFour`/`hex4_pmadd`
identify the two multiply-adds' lane 0 with `hex4`'s code unit.

The copies rest on one identity — `packLanes_copy32`, that a `<4 x i64>` load's
lanes stored back are the bytes it read — so a copy's memory is the bytes it moved
and not a lane term.  The blocks' steps take the sign extension's width equality as
a hypothesis (`(k.signExtend 64).toNat = k.toNat`) rather than proving it: the
core lemma that would prove it, `BitVec.toNat_signExtend`, is stated with
`Classical.choice`, and the trace's own pins stay at `[propext, Quot.sound]` while
the equality is a caller's.  Discharging it at the boundary is where a carrier, if
one is used, will appear, and it belongs to the assembly rather than to these
blocks.

The rest of the walk is here too, each block in the same shape: the hex reader
(`if.end3.i`), the pair and UTF-8 emitter (`if.then17.i`,
`land.lhs.true22.i`, `if.then26.i`), the block that packs an escape's word and
stores it (`if.end32.i`), and `cleanup32`.  `if.end32.i` is the block whose run
leaves the four bytes of the packed word (`udIfEnd32Word cp`) at `%dst + %add15`
rather than the input memory, and `store32_frame`/`udIfEnd32I_frame` are its
store frame; `readBytes_writeBytes_extend` composes that store with a prefix the
caller already holds, and `udIfEnd32I_decode` is the pair together, conditional on
the word-to-encoding equation its docstring records.

What is not here yet is the assembly above the trace: the budget term as a
function of the arguments and the caller's memory, the destination prefix
composed across the stores, and `escape_expand_satisfies` with its companion.
The blocks' steps take the sign-extension width equality as a hypothesis, so the
assembly is also where that hypothesis is discharged.

Every theorem is pinned where it is proved; the pins are the module's instrument.
-/
import LeanLLVM.Refinement.JsonEscapeExpandContract
import LeanLLVM.Refinement.JsonEscapeListRun
import LeanLLVM.Refinement.JsonEntrySteps

set_option maxRecDepth 8000
set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec

/-! ### Reading a cell out of an environment the block built

The same walk the list trace uses: `ud_lk` closes a cell the block wrote or a cell
the incoming environment still has, and `ud_lk_h` closes it from a hypothesis. -/

macro "ud_lk" : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | rw [lookupName_cons_self] | rfl)))

macro "ud_lk_h " h:term : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | rw [lookupName_cons_self] | exact $h)))

/-! ### Naming a block of the decoder -/

def udEntry : Block := blockAt usDecFunction 0 (by decide)

def udLandRhs : Block := blockAt usDecFunction 1 (by decide)

def udWhileBody : Block := blockAt usDecFunction 2 (by decide)

def udWhileEnd : Block := blockAt usDecFunction 3 (by decide)

def udWhileBody6 : Block := blockAt usDecFunction 4 (by decide)

def udIfEnd : Block := blockAt usDecFunction 5 (by decide)

def udIfThen20 : Block := blockAt usDecFunction 10 (by decide)

def udIfThen22 : Block := blockAt usDecFunction 21 (by decide)

def udCleanup32 : Block := blockAt usDecFunction 22 (by decide)

def udUsRunExit112 : Block := blockAt usDecFunction 27 (by decide)

def udCleanup41 : Block := blockAt usDecFunction 28 (by decide)

theorem findBlock_udEntry : usDecFunction.findBlock "entry" = some udEntry := by decide

theorem findBlock_udLandRhs : usDecFunction.findBlock "land.rhs" = some udLandRhs := by
  decide

theorem findBlock_udWhileBody : usDecFunction.findBlock "while.body" = some udWhileBody := by
  decide

theorem findBlock_udWhileEnd : usDecFunction.findBlock "while.end" = some udWhileEnd := by
  decide

theorem findBlock_udWhileBody6 : usDecFunction.findBlock "while.body6" = some udWhileBody6 := by
  decide

theorem findBlock_udIfEnd : usDecFunction.findBlock "if.end" = some udIfEnd := by decide

theorem findBlock_udIfThen20 : usDecFunction.findBlock "if.then20" = some udIfThen20 := by
  decide

theorem findBlock_udIfThen22 : usDecFunction.findBlock "if.then22" = some udIfThen22 := by
  decide

theorem findBlock_udCleanup32 : usDecFunction.findBlock "cleanup32" = some udCleanup32 := by
  decide

theorem findBlock_udUsRunExit112 :
    usDecFunction.findBlock "us_run.exit112" = some udUsRunExit112 := by decide

theorem findBlock_udCleanup41 : usDecFunction.findBlock "cleanup41" = some udCleanup41 := by
  decide

/-! ### One block's control step -/

theorem udStep_of (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : usDecFunction.findBlock name = some b)
    (hbody : denoteCode escapeCalls b.instrs s = some s') :
    step escapeCalls usDecFunction s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

theorem udRun_jump {s s' : State} {n : Nat}
    (h : step escapeCalls usDecFunction s = .jump s') :
    runFuel escapeCalls (n + 1) usDecFunction s =
      runFuel escapeCalls n usDecFunction s' :=
  runFuel_jump h

theorem udRun_ret {s s' : State} {v : Option Value} {n : Nat}
    (h : step escapeCalls usDecFunction s = .ret v s') :
    runFuel escapeCalls (n + 1) usDecFunction s = some (.ret v s'.mem) :=
  runFuel_ret h

theorem udCondbr_one (s : State) (c : Operand) (t f : String) (v : BitVec 1)
    (h : evalOperand s c = some (.int 1 v)) (hv : v = (1 : BitVec 1)) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } :=
  execTerm_condbr_one s c t f v h hv

theorem udCondbr_zero (s : State) (c : Operand) (t f : String) (v : BitVec 1)
    (h : evalOperand s c = some (.int 1 v)) (hv : v = (0 : BitVec 1)) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } :=
  execTerm_condbr_zero s c t f v h hv

/-! ### Instruction shapes the walk needs

The batch module's helpers cover the arithmetic the seed blocks use; the position
walk adds a 32-bit load, an unsigned 64-bit compare, a 64-bit subtraction and an
8-bit compare. -/

/-- `%d = icmp ult i64 %a, %b`. -/
theorem b_icmp_ult64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d .ult 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (evalICmp .ult x y)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

/-- `%d = icmp ugt i64 %a, <c>`. -/
theorem b_icmp_ugt64_imm (env : Env) (s : State) (d a : String) (x c : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .ugt 64 (.reg a) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 1 (evalICmp .ugt x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 c)]
  simp only [withEnv, State.bind]

/-- `%d = icmp ult i64 %a, <c>`. -/
theorem b_icmp_ult64_imm (env : Env) (s : State) (d a : String) (x c : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .ult 64 (.reg a) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 c)]
  simp only [withEnv, State.bind]

/-- `%d = sub i64 %a, %b`. -/
theorem b_sub64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .sub 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 (x - y)) :: env) s) := by
  rw [evalInstr_binop (r := (x - y).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]

/-- A 32-bit load of four bytes binds the word those bytes denote. -/
theorem b_load32 (env : Env) (s : State) (d p : String) (a : Nat) (v : BitVec 32)
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) :
    evalInstr escapeCalls (withEnv env s) (.load d (.int 32) (.reg p)) =
      some (withEnv ((d, .int 32 v) :: env) s) := by
  have hval : loadValue s.mem (.int 32) a = some (.int 32 v) := by
    have hvlt : v.toNat < 256 ^ 4 := by
      have hlt : 2 ^ 32 = 256 ^ 4 := by decide
      rw [← hlt]; exact v.isLt
    have hb : bytesToNat (natToBytes v.toNat 4) = v.toNat := by
      rw [natToBytes_toNat, Nat.mod_eq_of_lt hvlt]
    simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
      show (32 = 0) = False from by decide, ite_false, hv, hb]
    simp
  exact evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hval)


/-- `%d = getelementptr i8, ptr %base, %off` at a 64-bit register index. -/
theorem b_gep8_reg (env : Env) (s : State) (d base off : String) (a : Nat)
    (x : BitVec 64) (k : Nat)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    evalInstr escapeCalls (withEnv env s) (.gep d (.int 8) (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a + k)) :: env) s) := by
  rw [evalInstr_gep_i8 (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 x) ho) (hpos := by rw [hk]; exact hpos)]
  simp only [withEnv, State.bind, hk]

/-- A 32-bit compare against a literal. -/
theorem b_icmp_eq32_imm (env : Env) (s : State) (d a : String) (x c : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .eq 32 (.reg a) (.imm (.int 32 c))) =
      some (withEnv ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_lit_of _ 32 c)]
  simp only [withEnv, State.bind]

/-! ### `entry`

The entry block loads the caller's position cursor, forms the body's end offset
`pos0 + n`, and tests the cursor against the list's length.  It writes nothing, so
its memory projection is the input's; the cells `land.rhs` and `while.end` read are
the three it binds and the parameters it inherits. -/

theorem udEntry_instrs :
    udEntry.instrs =
      [ .load "%0" (.int 64) (.reg "%xj"),
        .binop "%add" .add 64 (.reg "%pos0") (.reg "%n"),
        .icmp "%cmp286" .ult 64 (.reg "%0") (.reg "%nxp") ] := by
  decide

theorem udEntry_term :
    udEntry.term = .condbr (.reg "%cmp286") "land.rhs" "while.end" := by decide

def udEntryEnv (env : Env) (k0 pos0 n nxp : BitVec 64) : Env :=
  ("%cmp286", .int 1 (evalICmp .ult k0 nxp)) ::
    ("%add", .int 64 (pos0 + n)) ::
    ("%0", .int 64 k0) :: env

theorem udEntry_denote (env : Env) (s : State) (xj : Nat) (k0 pos0 n nxp : BitVec 64)
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hld : readBytes s.mem xj 8 = some (natToBytes k0.toNat 8))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode escapeCalls udEntry.instrs (withEnv env s) =
      some (withEnv (udEntryEnv env k0 pos0 n nxp) s) := by
  rw [udEntry_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load64 _ s "%0" "%xj" xj k0 (by ud_lk_h hxj) hld)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ s "%add" "%pos0" "%n" pos0 n
    (by ud_lk_h hpos0) (by ud_lk_h hn))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult64 _ s "%cmp286" "%0" "%nxp" k0 nxp
    (by ud_lk) (by ud_lk_h hnxp))]
  simp only [denoteCode, udEntryEnv]

theorem udEntry_run (env : Env) (s : State) (xj : Nat) (k0 pos0 n nxp : BitVec 64)
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hld : readBytes s.mem xj 8 = some (natToBytes k0.toNat 8))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    Option.map State.mem (denoteCode escapeCalls udEntry.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udEntry.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%0") = some (.int 64 k0) ∧
      (denoteCode escapeCalls udEntry.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add") = some (.int 64 (pos0 + n)) ∧
      (denoteCode escapeCalls udEntry.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp286") =
        some (.int 1 (evalICmp .ult k0 nxp)) := by
  rw [udEntry_denote env s xj k0 pos0 n nxp hxj hld hpos0 hn hnxp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udEntryEnv] <;> ud_lk)

theorem udEntry_cells (env : Env) (k0 pos0 n nxp : BitVec 64) :
    lookupName (udEntryEnv env k0 pos0 n nxp) "%0" = some (.int 64 k0) ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%add" = some (.int 64 (pos0 + n)) ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%cmp286" =
        some (.int 1 (evalICmp .ult k0 nxp)) ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%pos0" = lookupName env "%pos0" ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%n" = lookupName env "%n" ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%nxp" = lookupName env "%nxp" ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%xj" = lookupName env "%xj" ∧
      lookupName (udEntryEnv env k0 pos0 n nxp) "%xp" = lookupName env "%xp" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [udEntryEnv] <;> ud_lk)

theorem udEntry_step (env : Env) (s : State) (xj : Nat) (k0 pos0 n nxp : BitVec 64)
    (hpc : s.pc = "entry")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hld : readBytes s.mem xj 8 = some (natToBytes k0.toNat 8))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult k0 nxp = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udEntryEnv env k0 pos0 n nxp) s) with
              pc := "land.rhs", pre := some "entry" } := by
  rw [udStep_of (withEnv env s) "entry" udEntry _
    (by rw [withEnv]; exact hpc) findBlock_udEntry
    (udEntry_denote env s xj k0 pos0 n nxp hxj hld hpos0 hn hnxp), udEntry_term]
  have hcmp : evalOperand (withEnv (udEntryEnv env k0 pos0 n nxp) s) (.reg "%cmp286") =
      some (.int 1 (evalICmp .ult k0 nxp)) :=
    evalOperand_reg_of _ s "%cmp286" _ (udEntry_cells env k0 pos0 n nxp).2.2.1
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udEntry_step_zero (env : Env) (s : State) (xj : Nat) (k0 pos0 n nxp : BitVec 64)
    (hpc : s.pc = "entry")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hld : readBytes s.mem xj 8 = some (natToBytes k0.toNat 8))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult k0 nxp = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udEntryEnv env k0 pos0 n nxp) s) with
              pc := "while.end", pre := some "entry" } := by
  rw [udStep_of (withEnv env s) "entry" udEntry _
    (by rw [withEnv]; exact hpc) findBlock_udEntry
    (udEntry_denote env s xj k0 pos0 n nxp hxj hld hpos0 hn hnxp), udEntry_term]
  have hcmp : evalOperand (withEnv (udEntryEnv env k0 pos0 n nxp) s) (.reg "%cmp286") =
      some (.int 1 (evalICmp .ult k0 nxp)) :=
    evalOperand_reg_of _ s "%cmp286" _ (udEntry_cells env k0 pos0 n nxp).2.2.1
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `while.body`

The walk's head: one position consumed, and the test for the list's end. -/

theorem udWhileBody_instrs :
    udWhileBody.instrs =
      [ .binop "%inc" .add 64 (.reg "%k.0287") (.imm (.int 64 (BitVec.ofInt 64 1))),
        .icmp "%exitcond.not" .eq 64 (.reg "%inc") (.reg "%nxp") ] := by
  decide

theorem udWhileBody_term :
    udWhileBody.term = .condbr (.reg "%exitcond.not") "while.end35" "land.rhs" := by
  decide

def udWhileBodyEnv (env : Env) (k nxp : BitVec 64) : Env :=
  ("%exitcond.not", .int 1 (evalICmp .eq (k + BitVec.ofInt 64 1) nxp)) ::
    ("%inc", .int 64 (k + BitVec.ofInt 64 1)) :: env

theorem udWhileBody_denote (env : Env) (s : State) (k nxp : BitVec 64)
    (hk : lookupName env "%k.0287" = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode escapeCalls udWhileBody.instrs (withEnv env s) =
      some (withEnv (udWhileBodyEnv env k nxp) s) := by
  rw [udWhileBody_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%inc" "%k.0287" k
    (BitVec.ofInt 64 1) (by ud_lk_h hk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64 _ s "%exitcond.not" "%inc" "%nxp"
    (k + BitVec.ofInt 64 1) nxp (by ud_lk) (by ud_lk_h hnxp))]
  simp only [denoteCode, udWhileBodyEnv]

theorem udWhileBody_run (env : Env) (s : State) (k nxp : BitVec 64)
    (hk : lookupName env "%k.0287" = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    Option.map State.mem (denoteCode escapeCalls udWhileBody.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udWhileBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%inc") = some (.int 64 (k + BitVec.ofInt 64 1)) ∧
      (denoteCode escapeCalls udWhileBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%exitcond.not") =
        some (.int 1 (evalICmp .eq (k + BitVec.ofInt 64 1) nxp)) := by
  rw [udWhileBody_denote env s k nxp hk hnxp]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udWhileBodyEnv] <;> ud_lk)

theorem udWhileBody_cells (env : Env) (k nxp : BitVec 64) :
    lookupName (udWhileBodyEnv env k nxp) "%inc" = some (.int 64 (k + BitVec.ofInt 64 1)) ∧
      lookupName (udWhileBodyEnv env k nxp) "%exitcond.not" =
        some (.int 1 (evalICmp .eq (k + BitVec.ofInt 64 1) nxp)) ∧
      lookupName (udWhileBodyEnv env k nxp) "%k.0287" = lookupName env "%k.0287" ∧
      lookupName (udWhileBodyEnv env k nxp) "%nxp" = lookupName env "%nxp" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [udWhileBodyEnv] <;> ud_lk)

theorem udWhileBody_step (env : Env) (s : State) (k nxp : BitVec 64)
    (hpc : s.pc = "while.body")
    (hk : lookupName env "%k.0287" = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .eq (k + BitVec.ofInt 64 1) nxp = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileBodyEnv env k nxp) s) with
              pc := "land.rhs", pre := some "while.body" } := by
  rw [udStep_of (withEnv env s) "while.body" udWhileBody _
    (by rw [withEnv]; exact hpc) findBlock_udWhileBody
    (udWhileBody_denote env s k nxp hk hnxp), udWhileBody_term]
  have hcmp : evalOperand (withEnv (udWhileBodyEnv env k nxp) s) (.reg "%exitcond.not") =
      some (.int 1 (evalICmp .eq (k + BitVec.ofInt 64 1) nxp)) :=
    evalOperand_reg_of _ s "%exitcond.not" _ (udWhileBody_cells env k nxp).2.1
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udWhileBody_step_one (env : Env) (s : State) (k nxp : BitVec 64)
    (hpc : s.pc = "while.body")
    (hk : lookupName env "%k.0287" = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .eq (k + BitVec.ofInt 64 1) nxp = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileBodyEnv env k nxp) s) with
              pc := "while.end35", pre := some "while.body" } := by
  rw [udStep_of (withEnv env s) "while.body" udWhileBody _
    (by rw [withEnv]; exact hpc) findBlock_udWhileBody
    (udWhileBody_denote env s k nxp hk hnxp), udWhileBody_term]
  have hcmp : evalOperand (withEnv (udWhileBodyEnv env k nxp) s) (.reg "%exitcond.not") =
      some (.int 1 (evalICmp .eq (k + BitVec.ofInt 64 1) nxp)) :=
    evalOperand_reg_of _ s "%exitcond.not" _ (udWhileBody_cells env k nxp).2.1
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `while.end`

The walk's exit test: the position index it carries against the list's length.  The
phi selects the caller's cursor or the walk's last index; the lemma is stated at the
selected operand, so both predecessors are the same statement. -/

def udWhileEndIncoming : List (String × Operand) :=
  [("entry", .reg "%0"), ("land.rhs", .reg "%k.0287")]

theorem udWhileEnd_instrs :
    udWhileEnd.instrs =
      [ .phi "%k.0.lcssa" (.int 64) udWhileEndIncoming,
        .icmp "%cmp4293" .ult 64 (.reg "%k.0.lcssa") (.reg "%nxp") ] := by
  decide

theorem udWhileEnd_term :
    udWhileEnd.term = .condbr (.reg "%cmp4293") "while.body6" "while.end35" := by
  decide

def udWhileEndEnv (env : Env) (k nxp : BitVec 64) : Env :=
  ("%cmp4293", .int 1 (evalICmp .ult k nxp)) ::
    ("%k.0.lcssa", .int 64 k) :: env

theorem udWhileEnd_denote (env : Env) (s : State) (prev : String) (op : Operand)
    (k nxp : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udWhileEndIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode escapeCalls udWhileEnd.instrs (withEnv env s) =
      some (withEnv (udWhileEndEnv env k nxp) s) := by
  rw [udWhileEnd_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0.lcssa") (ty := .int 64) (inc := udWhileEndIncoming) hpre hinc hop)]
  rw [show (withEnv env s).bind "%k.0.lcssa" (.int 64 k) =
      withEnv (("%k.0.lcssa", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult64 _ s
    "%cmp4293" "%k.0.lcssa" "%nxp" k nxp (by ud_lk) (by ud_lk_h hnxp))]
  simp only [denoteCode, withEnv, udWhileEndEnv]

theorem udWhileEnd_run (env : Env) (s : State) (prev : String) (op : Operand)
    (k nxp : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udWhileEndIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    Option.map State.mem (denoteCode escapeCalls udWhileEnd.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udWhileEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%k.0.lcssa") = some (.int 64 k) ∧
      (denoteCode escapeCalls udWhileEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp4293") =
        some (.int 1 (evalICmp .ult k nxp)) := by
  rw [udWhileEnd_denote env s prev op k nxp hpre hinc hop hnxp]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udWhileEndEnv] <;> ud_lk)

theorem udWhileEnd_cells (env : Env) (k nxp : BitVec 64) :
    lookupName (udWhileEndEnv env k nxp) "%k.0.lcssa" = some (.int 64 k) ∧
      lookupName (udWhileEndEnv env k nxp) "%cmp4293" =
        some (.int 1 (evalICmp .ult k nxp)) ∧
      lookupName (udWhileEndEnv env k nxp) "%nxp" = lookupName env "%nxp" ∧
      lookupName (udWhileEndEnv env k nxp) "%pos0" = lookupName env "%pos0" ∧
      lookupName (udWhileEndEnv env k nxp) "%xp" = lookupName env "%xp" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [udWhileEndEnv] <;> ud_lk)

theorem udWhileEnd_step (env : Env) (s : State) (prev : String) (op : Operand)
    (k nxp : BitVec 64)
    (hpc : s.pc = "while.end")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udWhileEndIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult k nxp = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileEndEnv env k nxp) s) with
              pc := "while.end35", pre := some "while.end" } := by
  rw [udStep_of (withEnv env s) "while.end" udWhileEnd _
    (by rw [withEnv]; exact hpc) findBlock_udWhileEnd
    (udWhileEnd_denote env s prev op k nxp hpre hinc hop hnxp), udWhileEnd_term]
  have hcmp : evalOperand (withEnv (udWhileEndEnv env k nxp) s) (.reg "%cmp4293") =
      some (.int 1 (evalICmp .ult k nxp)) :=
    evalOperand_reg_of _ s "%cmp4293" _ (udWhileEnd_cells env k nxp).2.1
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udWhileEnd_step_one (env : Env) (s : State) (prev : String) (op : Operand)
    (k nxp : BitVec 64)
    (hpc : s.pc = "while.end")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udWhileEndIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult k nxp = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileEndEnv env k nxp) s) with
              pc := "while.body6", pre := some "while.end" } := by
  rw [udStep_of (withEnv env s) "while.end" udWhileEnd _
    (by rw [withEnv]; exact hpc) findBlock_udWhileEnd
    (udWhileEnd_denote env s prev op k nxp hpre hinc hop hnxp), udWhileEnd_term]
  have hcmp : evalOperand (withEnv (udWhileEndEnv env k nxp) s) (.reg "%cmp4293") =
      some (.int 1 (evalICmp .ult k nxp)) :=
    evalOperand_reg_of _ s "%cmp4293" _ (udWhileEnd_cells env k nxp).2.1
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### The refusals

Both refusal blocks store the body-relative offset and the position index, then
jump out of the loop.  They bind nothing, so their environments are their
predecessors'; the memory is the two stores. -/

theorem udIfThen20_instrs :
    udIfThen20.instrs =
      [ .store (.int 64) (.reg "%sub") (.reg "%err"),
        .store (.int 64) (.reg "%inc11") (.reg "%xj") ] := by
  decide

theorem udIfThen20_term : udIfThen20.term = .br "cleanup41" := by decide

theorem udIfThen22_instrs :
    udIfThen22.instrs =
      [ .store (.int 64) (.reg "%sub") (.reg "%err"),
        .store (.int 64) (.reg "%inc11") (.reg "%xj") ] := by
  decide

theorem udIfThen22_term : udIfThen22.term = .br "cleanup41" := by decide

/-- The two stores a refusal makes, in order: the offset at `%err`, then the index
at `%xj`. -/
def udRefusalMem (mem : Mem) (off err k xj : Nat) : Mem :=
  writeBytes (writeBytes mem err (natToBytes off 8)) xj (natToBytes k 8)

theorem udIfThen20_denote (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    denoteCode escapeCalls udIfThen20.instrs (withEnv env s) =
      some (withEnv env { s with mem := udRefusalMem s.mem off.toNat err k.toNat xj }) := by
  rw [udIfThen20_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem env s s.mem "%sub" "%err" off err
    hoff herr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem env
    { s with mem := writeBytes s.mem err (natToBytes off.toNat 8) }
    (writeBytes s.mem err (natToBytes off.toNat 8)) "%inc11" "%xj" k xj hk hxj)]
  simp only [denoteCode, withEnv, udRefusalMem]

theorem udIfThen22_denote (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    denoteCode escapeCalls udIfThen22.instrs (withEnv env s) =
      some (withEnv env { s with mem := udRefusalMem s.mem off.toNat err k.toNat xj }) := by
  rw [udIfThen22_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem env s s.mem "%sub" "%err" off err
    hoff herr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem env
    { s with mem := writeBytes s.mem err (natToBytes off.toNat 8) }
    (writeBytes s.mem err (natToBytes off.toNat 8)) "%inc11" "%xj" k xj hk hxj)]
  simp only [denoteCode, withEnv, udRefusalMem]

theorem udIfThen20_run (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    Option.map State.mem (denoteCode escapeCalls udIfThen20.instrs (withEnv env s)) =
      some (udRefusalMem s.mem off.toNat err k.toNat xj) := by
  rw [udIfThen20_denote env s off k err xj hoff hk herr hxj]
  rfl

theorem udIfThen22_run (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    Option.map State.mem (denoteCode escapeCalls udIfThen22.instrs (withEnv env s)) =
      some (udRefusalMem s.mem off.toNat err k.toNat xj) := by
  rw [udIfThen22_denote env s off k err xj hoff hk herr hxj]
  rfl

theorem udIfThen20_step (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hpc : s.pc = "if.then20")
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv env
                { s with mem := udRefusalMem s.mem off.toNat err k.toNat xj })
              with pc := "cleanup41", pre := some "if.then20" } := by
  rw [udStep_of (withEnv env s) "if.then20" udIfThen20 _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen20
    (udIfThen20_denote env s off k err xj hoff hk herr hxj), udIfThen20_term]
  simp only [execTerm, withEnv, hpc]

theorem udIfThen22_step (env : Env) (s : State) (off k : BitVec 64) (err xj : Nat)
    (hpc : s.pc = "if.then22")
    (hoff : lookupName env "%sub" = some (.int 64 off))
    (hk : lookupName env "%inc11" = some (.int 64 k))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv env
                { s with mem := udRefusalMem s.mem off.toNat err k.toNat xj })
              with pc := "cleanup41", pre := some "if.then22" } := by
  rw [udStep_of (withEnv env s) "if.then22" udIfThen22 _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen22
    (udIfThen22_denote env s off k err xj hoff hk herr hxj), udIfThen22_term]
  simp only [execTerm, withEnv, hpc]

/-! ### `us_run.exit112`

The run's last block before the cleanup: the position cursor is stored, and the
returned value is the remaining byte count plus the written count.  Its `%xj` store
is the only memory it writes, and it is the clause the record's `*xj` post reads. -/

theorem udUsRunExit112_instrs :
    udUsRunExit112.instrs =
      [ .store (.int 64) (.reg "%k.1.lcssa") (.reg "%xj"),
        .binop "%add40" .add 64 (.reg "%sub38") (.reg "%j.0.lcssa") ] := by
  decide

theorem udUsRunExit112_term : udUsRunExit112.term = .br "cleanup41" := by decide

def udUsRunExit112Env (env : Env) (rem j : BitVec 64) : Env :=
  ("%add40", .int 64 (rem + j)) :: env

theorem udUsRunExit112_denote (env : Env) (s : State) (k rem j : BitVec 64) (xj : Nat)
    (hk : lookupName env "%k.1.lcssa" = some (.int 64 k))
    (hrem : lookupName env "%sub38" = some (.int 64 rem))
    (hj : lookupName env "%j.0.lcssa" = some (.int 64 j))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    denoteCode escapeCalls udUsRunExit112.instrs (withEnv env s) =
      some (withEnv (udUsRunExit112Env env rem j)
        { s with mem := writeBytes s.mem xj (natToBytes k.toNat 8) }) := by
  rw [udUsRunExit112_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem env s s.mem "%k.1.lcssa" "%xj" k xj
    hk hxj)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 env
    { s with mem := writeBytes s.mem xj (natToBytes k.toNat 8) }
    "%add40" "%sub38" "%j.0.lcssa" rem j hrem hj)]
  simp only [denoteCode, withEnv, udUsRunExit112Env]

theorem udUsRunExit112_run (env : Env) (s : State) (k rem j : BitVec 64) (xj : Nat)
    (hk : lookupName env "%k.1.lcssa" = some (.int 64 k))
    (hrem : lookupName env "%sub38" = some (.int 64 rem))
    (hj : lookupName env "%j.0.lcssa" = some (.int 64 j))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    Option.map State.mem (denoteCode escapeCalls udUsRunExit112.instrs (withEnv env s)) =
        some (writeBytes s.mem xj (natToBytes k.toNat 8)) ∧
      (denoteCode escapeCalls udUsRunExit112.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add40") = some (.int 64 (rem + j)) := by
  rw [udUsRunExit112_denote env s k rem j xj hk hrem hj hxj]
  refine ⟨?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udUsRunExit112Env] <;> ud_lk

theorem udUsRunExit112_cells (env : Env) (rem j : BitVec 64) :
    lookupName (udUsRunExit112Env env rem j) "%add40" = some (.int 64 (rem + j)) ∧
      lookupName (udUsRunExit112Env env rem j) "%sub38" = lookupName env "%sub38" := by
  refine ⟨?_, ?_⟩ <;> (simp only [udUsRunExit112Env] <;> ud_lk)

theorem udUsRunExit112_step (env : Env) (s : State) (k rem j : BitVec 64) (xj : Nat)
    (hpc : s.pc = "us_run.exit112")
    (hk : lookupName env "%k.1.lcssa" = some (.int 64 k))
    (hrem : lookupName env "%sub38" = some (.int 64 rem))
    (hj : lookupName env "%j.0.lcssa" = some (.int 64 j))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udUsRunExit112Env env rem j)
                { s with mem := writeBytes s.mem xj (natToBytes k.toNat 8) })
              with pc := "cleanup41", pre := some "us_run.exit112" } := by
  rw [udStep_of (withEnv env s) "us_run.exit112" udUsRunExit112 _
    (by rw [withEnv]; exact hpc) findBlock_udUsRunExit112
    (udUsRunExit112_denote env s k rem j xj hk hrem hj hxj), udUsRunExit112_term]
  simp only [execTerm, withEnv, hpc]

/-! ### `cleanup41`

The function's single return: the phi selects the returned value from the three
blocks that reach it.  The lemma is stated at the selected operand so the three
incoming edges are one statement, and it is the record's return clause read off the
pinned body. -/

def udCleanup41Incoming : List (String × Operand) :=
  [("us_run.exit112", .reg "%add40"),
   ("if.then20", .imm (.int 64 (BitVec.ofInt 64 (-1)))),
   ("if.then22", .imm (.int 64 (BitVec.ofInt 64 (-1))))]

theorem udCleanup41_instrs :
    udCleanup41.instrs =
      [ .phi "%retval.4" (.int 64) udCleanup41Incoming ] := by
  decide

theorem udCleanup41_term :
    udCleanup41.term = .ret (.int 64) (some (.reg "%retval.4")) := by decide

def udCleanup41Env (env : Env) (rv : BitVec 64) : Env :=
  ("%retval.4", .int 64 rv) :: env

theorem udCleanup41_denote (env : Env) (s : State) (prev : String) (op : Operand)
    (rv : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCleanup41Incoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 rv)) :
    denoteCode escapeCalls udCleanup41.instrs (withEnv env s) =
      some (withEnv (udCleanup41Env env rv) s) := by
  rw [udCleanup41_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%retval.4") (ty := .int 64) (inc := udCleanup41Incoming) hpre hinc hop)]
  simp only [denoteCode, withEnv, State.bind, udCleanup41Env]

theorem udCleanup41_run (env : Env) (s : State) (prev : String) (op : Operand)
    (rv : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCleanup41Incoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 rv)) :
    Option.map State.mem (denoteCode escapeCalls udCleanup41.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udCleanup41.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%retval.4") = some (.int 64 rv) := by
  rw [udCleanup41_denote env s prev op rv hpre hinc hop]
  refine ⟨?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udCleanup41Env] <;> ud_lk

theorem udCleanup41_step (env : Env) (s : State) (prev : String) (op : Operand)
    (rv : BitVec 64)
    (hpc : s.pc = "cleanup41")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCleanup41Incoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 rv)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .ret (some (.int 64 rv)) (withEnv (udCleanup41Env env rv) s) := by
  rw [udStep_of (withEnv env s) "cleanup41" udCleanup41 _
    (by rw [withEnv]; exact hpc) findBlock_udCleanup41
    (udCleanup41_denote env s prev op rv hpre hinc hop), udCleanup41_term]
  have hop' : evalOperand (withEnv (udCleanup41Env env rv) s) (.reg "%retval.4") =
      some (.int 64 rv) := by
    refine evalOperand_reg_of _ s "%retval.4" _ ?_
    simp only [udCleanup41Env]
    exact lookupName_cons_self _ _ _
  simp only [execTerm, hop']

/-! ### `land.rhs`

The walk's head: the position at the index is read as a `uint32`, zero-extended,
and compared with `pos0`.  The read's address is `%xp + 4 * %k`, which is the
window `readBytes_positionsBytes` names, so the two hypotheses are the stream's
read and the index's range. -/

def udLandRhsIncoming : List (String × Operand) :=
  [("while.body", .reg "%inc"), ("entry", .reg "%0")]

theorem udLandRhs_instrs :
    udLandRhs.instrs =
      [ .phi "%k.0287" (.int 64) udLandRhsIncoming,
        .gep "%arrayidx" (.int 32) (.reg "%xp") (.reg "%k.0287"),
        .load "%1" (.int 32) (.reg "%arrayidx"),
        .zext "%conv" 32 64 (.reg "%1"),
        .icmp "%cmp1" .ugt 64 (.reg "%pos0") (.reg "%conv") ] := by
  decide

theorem udLandRhs_term :
    udLandRhs.term = .condbr (.reg "%cmp1") "while.body" "while.end" := by decide

def udLandRhsEnv (env : Env) (xp : Nat) (k : BitVec 64) (v : BitVec 32)
    (pos0v : BitVec 64) : Env :=
  ("%cmp1", .int 1 (evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat))) ::
    ("%conv", .int 64 (BitVec.ofNat 64 v.toNat)) ::
    ("%1", .int 32 v) ::
    ("%arrayidx", .ptr (xp + k.toNat * 4)) ::
    ("%k.0287", .int 64 k) :: env

theorem udLandRhs_denote (env : Env) (s : State) (prev : String) (op : Operand)
    (xp : Nat) (k : BitVec 64) (v : BitVec 32) (pos0v : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udLandRhsIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v)) :
    denoteCode escapeCalls udLandRhs.instrs (withEnv env s) =
      some (withEnv (udLandRhsEnv env xp k v pos0v) s) := by
  rw [udLandRhs_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0287") (ty := .int 64) (inc := udLandRhsIncoming) hpre hinc hop)]
  rw [show (withEnv env s).bind "%k.0287" (.int 64 k) =
      withEnv (("%k.0287", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep4_reg64 _ s "%arrayidx" "%xp" "%k.0287" xp k
    k.toNat (by ud_lk_h hxp) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load32 _ s "%1" "%arrayidx" (xp + k.toNat * 4) v
    (by ud_lk) hv)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext32_64 _ s "%conv" "%1" v (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64 _ s "%cmp1" "%pos0" "%conv"
    pos0v (BitVec.ofNat 64 v.toNat) (by ud_lk_h hpos0) (by ud_lk))]
  simp only [denoteCode, withEnv, udLandRhsEnv]

theorem udLandRhs_run (env : Env) (s : State) (prev : String) (op : Operand)
    (xp : Nat) (k : BitVec 64) (v : BitVec 32) (pos0v : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udLandRhsIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v)) :
    Option.map State.mem (denoteCode escapeCalls udLandRhs.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udLandRhs.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%k.0287") = some (.int 64 k) ∧
      (denoteCode escapeCalls udLandRhs.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%conv") = some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
      (denoteCode escapeCalls udLandRhs.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp1") =
        some (.int 1 (evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat))) := by
  rw [udLandRhs_denote env s prev op xp k v pos0v hpre hinc hop hxp hk63 hkw hv hpos0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udLandRhsEnv] <;> ud_lk)

theorem udLandRhs_cells (env : Env) (xp : Nat) (k : BitVec 64) (v : BitVec 32)
    (pos0v : BitVec 64) :
    lookupName (udLandRhsEnv env xp k v pos0v) "%k.0287" = some (.int 64 k) ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%arrayidx" =
        some (.ptr (xp + k.toNat * 4)) ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%1" = some (.int 32 v) ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%conv" =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%cmp1" =
        some (.int 1 (evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat))) ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%xp" = lookupName env "%xp" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%pos0" = lookupName env "%pos0" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%nxp" = lookupName env "%nxp" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%n" = lookupName env "%n" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%xj" = lookupName env "%xj" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%dst" = lookupName env "%dst" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%p" = lookupName env "%p" ∧
      lookupName (udLandRhsEnv env xp k v pos0v) "%err" = lookupName env "%err" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [udLandRhsEnv] <;> ud_lk)

theorem udLandRhs_step (env : Env) (s : State) (prev : String) (op : Operand)
    (xp : Nat) (k : BitVec 64) (v : BitVec 32) (pos0v : BitVec 64)
    (hpc : s.pc = "land.rhs")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udLandRhsIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hcond : evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udLandRhsEnv env xp k v pos0v) s) with
              pc := "while.body", pre := some "land.rhs" } := by
  rw [udStep_of (withEnv env s) "land.rhs" udLandRhs _
    (by rw [withEnv]; exact hpc) findBlock_udLandRhs
    (udLandRhs_denote env s prev op xp k v pos0v hpre hinc hop hxp hk63 hkw hv hpos0),
    udLandRhs_term]
  have hcmp : evalOperand (withEnv (udLandRhsEnv env xp k v pos0v) s) (.reg "%cmp1") =
      some (.int 1 (evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat))) :=
    evalOperand_reg_of _ s "%cmp1" _ (udLandRhs_cells env xp k v pos0v).2.2.2.2.1
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udLandRhs_step_zero (env : Env) (s : State) (prev : String) (op : Operand)
    (xp : Nat) (k : BitVec 64) (v : BitVec 32) (pos0v : BitVec 64)
    (hpc : s.pc = "land.rhs")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udLandRhsIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hcond : evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udLandRhsEnv env xp k v pos0v) s) with
              pc := "while.end", pre := some "land.rhs" } := by
  rw [udStep_of (withEnv env s) "land.rhs" udLandRhs _
    (by rw [withEnv]; exact hpc) findBlock_udLandRhs
    (udLandRhs_denote env s prev op xp k v pos0v hpre hinc hop hxp hk63 hkw hv hpos0),
    udLandRhs_term]
  have hcmp : evalOperand (withEnv (udLandRhsEnv env xp k v pos0v) s) (.reg "%cmp1") =
      some (.int 1 (evalICmp .ugt pos0v (BitVec.ofNat 64 v.toNat))) :=
    evalOperand_reg_of _ s "%cmp1" _ (udLandRhs_cells env xp k v pos0v).2.2.2.2.1
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `while.body6`

The decode's loop head: three phis over the walk's state, the same position read,
and the test of the position against the body's end offset. -/

def udWhileBody6IncomingK : List (String × Operand) :=
  [("cleanup32", .reg "%add28"), ("while.end", .reg "%k.0.lcssa")]

def udWhileBody6IncomingI : List (String × Operand) :=
  [("cleanup32", .reg "%add24"), ("while.end", .imm (.int 64 (BitVec.ofInt 64 0)))]

def udWhileBody6IncomingJ : List (String × Operand) :=
  [("cleanup32", .reg "%j.3"), ("while.end", .imm (.int 64 (BitVec.ofInt 64 0)))]

theorem udWhileBody6_instrs :
    udWhileBody6.instrs =
      [ .phi "%k.1296" (.int 64) udWhileBody6IncomingK,
        .phi "%i.0295" (.int 64) udWhileBody6IncomingI,
        .phi "%j.0294" (.int 64) udWhileBody6IncomingJ,
        .gep "%arrayidx7" (.int 32) (.reg "%xp") (.reg "%k.1296"),
        .load "%2" (.int 32) (.reg "%arrayidx7"),
        .zext "%conv8" 32 64 (.reg "%2"),
        .icmp "%cmp9.not" .ugt 64 (.reg "%add") (.reg "%conv8") ] := by
  decide

theorem udWhileBody6_term :
    udWhileBody6.term = .condbr (.reg "%cmp9.not") "if.end" "while.end35" := by
  decide

def udWhileBody6Env (env : Env) (xp : Nat) (k i j : BitVec 64) (v : BitVec 32)
    (endv : BitVec 64) : Env :=
  ("%cmp9.not", .int 1 (evalICmp .ugt endv (BitVec.ofNat 64 v.toNat))) ::
    ("%conv8", .int 64 (BitVec.ofNat 64 v.toNat)) ::
    ("%2", .int 32 v) ::
    ("%arrayidx7", .ptr (xp + k.toNat * 4)) ::
    ("%j.0294", .int 64 j) ::
    ("%i.0295", .int 64 i) ::
    ("%k.1296", .int 64 k) :: env

theorem udWhileBody6_denote (env : Env) (s : State) (prev : String)
    (opk opi opj : Operand) (xp : Nat) (k i j : BitVec 64) (v : BitVec 32)
    (endv : BitVec 64)
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udWhileBody6IncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hinci : phiIncoming prev udWhileBody6IncomingI = some opi)
    (hopi : evalOperand (withEnv (("%k.1296", .int 64 k) :: env) s) opi = some (.int 64 i))
    (hincj : phiIncoming prev udWhileBody6IncomingJ = some opj)
    (hopj : evalOperand (withEnv (("%i.0295", .int 64 i) ::
      ("%k.1296", .int 64 k) :: env) s) opj = some (.int 64 j))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hend : lookupName env "%add" = some (.int 64 endv))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4)) :
    denoteCode escapeCalls udWhileBody6.instrs (withEnv env s) =
      some (withEnv (udWhileBody6Env env xp k i j v endv) s) := by
  rw [udWhileBody6_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.1296") (ty := .int 64) (inc := udWhileBody6IncomingK) hpre hinck hopk)]
  rw [show (withEnv env s).bind "%k.1296" (.int 64 k) =
      withEnv (("%k.1296", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi
    (s := withEnv (("%k.1296", .int 64 k) :: env) s)
    (d := "%i.0295") (ty := .int 64) (inc := udWhileBody6IncomingI) hpre hinci hopi)]
  rw [show (withEnv (("%k.1296", .int 64 k) :: env) s).bind "%i.0295" (.int 64 i) =
      withEnv (("%i.0295", .int 64 i) :: ("%k.1296", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi
    (s := withEnv (("%i.0295", .int 64 i) :: ("%k.1296", .int 64 k) :: env) s)
    (d := "%j.0294") (ty := .int 64) (inc := udWhileBody6IncomingJ) hpre hincj hopj)]
  rw [show (withEnv (("%i.0295", .int 64 i) :: ("%k.1296", .int 64 k) :: env) s).bind
      "%j.0294" (.int 64 j) =
      withEnv (("%j.0294", .int 64 j) :: ("%i.0295", .int 64 i) ::
        ("%k.1296", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep4_reg64 _ s "%arrayidx7" "%xp" "%k.1296" xp k
    k.toNat (by ud_lk_h hxp) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load32 _ s "%2" "%arrayidx7" (xp + k.toNat * 4) v
    (by ud_lk) hv)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext32_64 _ s "%conv8" "%2" v (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64 _ s "%cmp9.not" "%add" "%conv8"
    endv (BitVec.ofNat 64 v.toNat) (by ud_lk_h hend) (by ud_lk))]
  simp only [denoteCode, withEnv, udWhileBody6Env]

theorem udWhileBody6_run (env : Env) (s : State) (prev : String)
    (opk opi opj : Operand) (xp : Nat) (k i j : BitVec 64) (v : BitVec 32)
    (endv : BitVec 64)
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udWhileBody6IncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hinci : phiIncoming prev udWhileBody6IncomingI = some opi)
    (hopi : evalOperand (withEnv (("%k.1296", .int 64 k) :: env) s) opi = some (.int 64 i))
    (hincj : phiIncoming prev udWhileBody6IncomingJ = some opj)
    (hopj : evalOperand (withEnv (("%i.0295", .int 64 i) ::
      ("%k.1296", .int 64 k) :: env) s) opj = some (.int 64 j))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hend : lookupName env "%add" = some (.int 64 endv))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4)) :
    Option.map State.mem (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%k.1296") = some (.int 64 k) ∧
      (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%i.0295") = some (.int 64 i) ∧
      (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%j.0294") = some (.int 64 j) ∧
      (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%conv8") =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
      (denoteCode escapeCalls udWhileBody6.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp9.not") =
        some (.int 1 (evalICmp .ugt endv (BitVec.ofNat 64 v.toNat))) := by
  rw [udWhileBody6_denote env s prev opk opi opj xp k i j v endv
    hpre hinck hopk hinci hopi hincj hopj hxp hend hk63 hkw hv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udWhileBody6Env] <;> ud_lk)

theorem udWhileBody6_step (env : Env) (s : State) (prev : String)
    (opk opi opj : Operand) (xp : Nat) (k i j : BitVec 64) (v : BitVec 32)
    (endv : BitVec 64)
    (hpc : s.pc = "while.body6")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udWhileBody6IncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hinci : phiIncoming prev udWhileBody6IncomingI = some opi)
    (hopi : evalOperand (withEnv (("%k.1296", .int 64 k) :: env) s) opi = some (.int 64 i))
    (hincj : phiIncoming prev udWhileBody6IncomingJ = some opj)
    (hopj : evalOperand (withEnv (("%i.0295", .int 64 i) ::
      ("%k.1296", .int 64 k) :: env) s) opj = some (.int 64 j))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hend : lookupName env "%add" = some (.int 64 endv))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hcond : evalICmp .ugt endv (BitVec.ofNat 64 v.toNat) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileBody6Env env xp k i j v endv) s) with
              pc := "while.end35", pre := some "while.body6" } := by
  rw [udStep_of (withEnv env s) "while.body6" udWhileBody6 _
    (by rw [withEnv]; exact hpc) findBlock_udWhileBody6
    (udWhileBody6_denote env s prev opk opi opj xp k i j v endv
      hpre hinck hopk hinci hopi hincj hopj hxp hend hk63 hkw hv), udWhileBody6_term]
  have hcmp : evalOperand (withEnv (udWhileBody6Env env xp k i j v endv) s)
      (.reg "%cmp9.not") =
      some (.int 1 (evalICmp .ugt endv (BitVec.ofNat 64 v.toNat))) :=
    evalOperand_reg_of _ s "%cmp9.not" _ (by
      simp only [udWhileBody6Env]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udWhileBody6_step_one (env : Env) (s : State) (prev : String)
    (opk opi opj : Operand) (xp : Nat) (k i j : BitVec 64) (v : BitVec 32)
    (endv : BitVec 64)
    (hpc : s.pc = "while.body6")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udWhileBody6IncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hinci : phiIncoming prev udWhileBody6IncomingI = some opi)
    (hopi : evalOperand (withEnv (("%k.1296", .int 64 k) :: env) s) opi = some (.int 64 i))
    (hincj : phiIncoming prev udWhileBody6IncomingJ = some opj)
    (hopj : evalOperand (withEnv (("%i.0295", .int 64 i) ::
      ("%k.1296", .int 64 k) :: env) s) opj = some (.int 64 j))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hend : lookupName env "%add" = some (.int 64 endv))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hv : readBytes s.mem (xp + k.toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hcond : evalICmp .ugt endv (BitVec.ofNat 64 v.toNat) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileBody6Env env xp k i j v endv) s) with
              pc := "if.end", pre := some "while.body6" } := by
  rw [udStep_of (withEnv env s) "while.body6" udWhileBody6 _
    (by rw [withEnv]; exact hpc) findBlock_udWhileBody6
    (udWhileBody6_denote env s prev opk opi opj xp k i j v endv
      hpre hinck hopk hinci hopi hincj hopj hxp hend hk63 hkw hv), udWhileBody6_term]
  have hcmp : evalOperand (withEnv (udWhileBody6Env env xp k i j v endv) s)
      (.reg "%cmp9.not") =
      some (.int 1 (evalICmp .ugt endv (BitVec.ofNat 64 v.toNat))) :=
    evalOperand_reg_of _ s "%cmp9.not" _ (by
      simp only [udWhileBody6Env]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `if.end`

The decode's arithmetic for one position: the next index, the body-relative offset
of the position, the source and destination cursors, the remaining byte count, and
the test that sends a run to the double-word copy. -/

theorem udIfEnd_instrs :
    udIfEnd.instrs =
      [ .binop "%inc11" .add 64 (.reg "%k.1296") (.imm (.int 64 (BitVec.ofInt 64 1))),
        .binop "%sub" .sub 64 (.reg "%conv8") (.reg "%pos0"),
        .gep "%add.ptr" (.int 8) (.reg "%p") (.reg "%i.0295"),
        .gep "%add.ptr12" (.int 8) (.reg "%dst") (.reg "%j.0294"),
        .binop "%sub13" .sub 64 (.reg "%sub") (.reg "%i.0295"),
        .icmp "%cmp.i88289" .ugt 64 (.reg "%sub13")
          (.imm (.int 64 (BitVec.ofInt 64 64))) ] := by
  decide

theorem udIfEnd_term :
    udIfEnd.term = .condbr (.reg "%cmp.i88289") "while.body.i91" "us_run_long.exit99" := by
  decide

def udIfEndEnv (env : Env) (paddr daddr : Nat) (k i j : BitVec 64) (conv8v pos0v : BitVec 64) :
    Env :=
  ("%cmp.i88289", .int 1 (evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64))) ::
    ("%sub13", .int 64 (conv8v - pos0v - i)) ::
    ("%add.ptr12", .ptr (daddr + j.toNat)) ::
    ("%add.ptr", .ptr (paddr + i.toNat)) ::
    ("%sub", .int 64 (conv8v - pos0v)) ::
    ("%inc11", .int 64 (k + BitVec.ofInt 64 1)) :: env

theorem udIfEnd_denote (env : Env) (s : State) (paddr daddr : Nat) (k i j : BitVec 64)
    (conv8v pos0v : BitVec 64)
    (hk : lookupName env "%k.1296" = some (.int 64 k))
    (hconv8 : lookupName env "%conv8" = some (.int 64 conv8v))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hi : lookupName env "%i.0295" = some (.int 64 i))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat) :
    denoteCode escapeCalls udIfEnd.instrs (withEnv env s) =
      some (withEnv (udIfEndEnv env paddr daddr k i j conv8v pos0v) s) := by
  rw [udIfEnd_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%inc11" "%k.1296" k
    (BitVec.ofInt 64 1) (by ud_lk_h hk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_sub64 _ s "%sub" "%conv8" "%pos0" conv8v pos0v
    (by ud_lk_h hconv8) (by ud_lk_h hpos0))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ s "%add.ptr" "%p" "%i.0295" paddr i
    i.toNat (by ud_lk_h hp) (by ud_lk_h hi) hiw hi63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ s "%add.ptr12" "%dst" "%j.0294" daddr j
    j.toNat (by ud_lk_h hdst) (by ud_lk_h hj) hjw hj63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_sub64 _ s "%sub13" "%sub" "%i.0295"
    (conv8v - pos0v) i (by ud_lk) (by ud_lk_h hi))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ s "%cmp.i88289" "%sub13"
    (conv8v - pos0v - i) (BitVec.ofInt 64 64) (by ud_lk))]
  simp only [denoteCode, withEnv, udIfEndEnv]

theorem udIfEnd_run (env : Env) (s : State) (paddr daddr : Nat) (k i j : BitVec 64)
    (conv8v pos0v : BitVec 64)
    (hk : lookupName env "%k.1296" = some (.int 64 k))
    (hconv8 : lookupName env "%conv8" = some (.int 64 conv8v))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hi : lookupName env "%i.0295" = some (.int 64 i))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat) :
    Option.map State.mem (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%inc11") =
        some (.int 64 (k + BitVec.ofInt 64 1)) ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%sub") = some (.int 64 (conv8v - pos0v)) ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr") = some (.ptr (paddr + i.toNat)) ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr12") = some (.ptr (daddr + j.toNat)) ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%sub13") =
        some (.int 64 (conv8v - pos0v - i)) ∧
      (denoteCode escapeCalls udIfEnd.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.i88289") =
        some (.int 1 (evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64))) := by
  rw [udIfEnd_denote env s paddr daddr k i j conv8v pos0v hk hconv8 hpos0 hp hi hdst hj
    hi63 hj63 hiw hjw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udIfEndEnv] <;> ud_lk)

theorem udIfEnd_step (env : Env) (s : State) (paddr daddr : Nat) (k i j : BitVec 64)
    (conv8v pos0v : BitVec 64)
    (hpc : s.pc = "if.end")
    (hk : lookupName env "%k.1296" = some (.int 64 k))
    (hconv8 : lookupName env "%conv8" = some (.int 64 conv8v))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hi : lookupName env "%i.0295" = some (.int 64 i))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat)
    (hcond : evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndEnv env paddr daddr k i j conv8v pos0v) s) with
              pc := "while.body.i91", pre := some "if.end" } := by
  rw [udStep_of (withEnv env s) "if.end" udIfEnd _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd
    (udIfEnd_denote env s paddr daddr k i j conv8v pos0v hk hconv8 hpos0 hp hi hdst hj
      hi63 hj63 hiw hjw), udIfEnd_term]
  have hcmp : evalOperand (withEnv (udIfEndEnv env paddr daddr k i j conv8v pos0v) s)
      (.reg "%cmp.i88289") =
      some (.int 1 (evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ s "%cmp.i88289" _ (by
      simp only [udIfEndEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udIfEnd_step_zero (env : Env) (s : State) (paddr daddr : Nat) (k i j : BitVec 64)
    (conv8v pos0v : BitVec 64)
    (hpc : s.pc = "if.end")
    (hk : lookupName env "%k.1296" = some (.int 64 k))
    (hconv8 : lookupName env "%conv8" = some (.int 64 conv8v))
    (hpos0 : lookupName env "%pos0" = some (.int 64 pos0v))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hi : lookupName env "%i.0295" = some (.int 64 i))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat)
    (hcond : evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndEnv env paddr daddr k i j conv8v pos0v) s) with
              pc := "us_run_long.exit99", pre := some "if.end" } := by
  rw [udStep_of (withEnv env s) "if.end" udIfEnd _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd
    (udIfEnd_denote env s paddr daddr k i j conv8v pos0v hk hconv8 hpos0 hp hi hdst hj
      hi63 hj63 hiw hjw), udIfEnd_term]
  have hcmp : evalOperand (withEnv (udIfEndEnv env paddr daddr k i j conv8v pos0v) s)
      (.reg "%cmp.i88289") =
      some (.int 1 (evalICmp .ugt (conv8v - pos0v - i) (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ s "%cmp.i88289" _ (by
      simp only [udIfEndEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]


/-! ### The two double-word copies

Both copy loops move a body in `<4 x i64>` pairs: thirty-two bytes per load, two
loads per iteration, and an exit block with one more pair and an optional second
half.  The block lemmas below are stated at the two base pointers and the byte
index, so the same shape serves the copy that follows a position (`%add.ptr`) and
the copy that follows the walk (`%add.ptr36`).

The copy's own arithmetic is the load and store's: a `<4 x i64>` load reads the
`n * w / 8 = 32` bytes at its address as four lanes, and the store packs the same
lanes back, so a pair of them writes the bytes that were read.  That identity is
`packLanes_copy32`, and it is what lets a block's memory be named by the bytes it
moved rather than by the lanes it bound. -/

/-- A `<4 x i64>` load at thirty-two readable bytes. -/
theorem b_load_vec4_64 (env : Env) (s : State) (d p : String) (addr : Nat)
    (bs : List UInt8)
    (hp : lookupName env p = some (.ptr addr))
    (hr : readBytes s.mem addr 32 = some bs) :
    evalInstr escapeCalls (withEnv env s) (.load d (.vec 4 (.int 64)) (.reg p)) =
      some (withEnv ((d, .vec 4 64 (unpackLanes 64 4 (bytesToNat bs))) :: env) s) := by
  have hv : loadValue s.mem (.vec 4 (.int 64)) addr =
      some (.vec 4 64 (unpackLanes 64 4 (bytesToNat bs))) :=
    loadValue_vec_int (m := s.mem) (n := 4) (w := 64) (addr := addr)
      (by decide) (by decide) hr
  exact evalInstr_load (hp := evalOperand_reg_of env s p (.ptr addr) hp) (hv := hv)

/-- A `<4 x i64>` store writes the packed lanes as thirty-two bytes. -/
theorem b_store_vec4_64 (env : Env) (s : State) (r p : String) (lanes : List (BitVec 64))
    (addr : Nat)
    (hv : lookupName env r = some (.vec 4 64 lanes))
    (hp : lookupName env p = some (.ptr addr))
    (hlen : lanes.length = 4) :
    evalInstr escapeCalls (withEnv env s)
        (.store (.vec 4 (.int 64)) (.reg r) (.reg p)) =
      some (withEnv env
        { s with mem := writeBytes s.mem addr (natToBytes (packLanes lanes) 32) }) := by
  refine evalInstr_store (vv := .vec 4 64 lanes) (a := addr)
    (s' := withEnv env
      { s with mem := writeBytes s.mem addr (natToBytes (packLanes lanes) 32) }) ?_ ?_ ?_
  · exact evalOperand_reg_of env s r (.vec 4 64 lanes) hv
  · exact evalOperand_reg_of env s p (.ptr addr) hp
  · simp [storeValue, hlen, withEnv]

/-- The lanes a load bound at thirty-two bytes are packed back into those bytes:
reading four sixty-four-bit lanes out of a thirty-two-byte block and storing them
writes the block. -/
theorem packLanes_copy32 (bs : List UInt8) (hlen : bs.length = 32) :
    natToBytes (packLanes (unpackLanes 64 4 (bytesToNat bs))) 32 = bs := by
  rw [packLanes_unpackLanes]
  have hlt : bytesToNat bs < 256 ^ 32 := by
    have h := bytesToNat_lt bs
    rw [hlen] at h
    exact h
  have hpow : (2 : Nat) ^ (4 * 64) = 256 ^ 32 := by decide
  rw [hpow, Nat.mod_eq_of_lt hlt, ← hlen]
  exact JsonEntrySteps.natToBytes_bytesToNat bs

/-- The eight-byte load the escape-byte test makes. -/
theorem b_load8 (env : Env) (s : State) (d p : String) (addr : Nat) (b : BitVec 8)
    (hp : lookupName env p = some (.ptr addr))
    (hv : readBytes s.mem addr 1 = some (natToBytes b.toNat 1)) :
    evalInstr escapeCalls (withEnv env s) (.load d (.int 8) (.reg p)) =
      some (withEnv ((d, .int 8 b) :: env) s) := by
  have hval : loadValue s.mem (.int 8) addr = some (.int 8 b) := by
    have hlt : b.toNat < 256 := by simpa using b.isLt
    have hb : bytesToNat (natToBytes b.toNat 1) = b.toNat := by
      rw [natToBytes_toNat, Nat.mod_eq_of_lt hlt]
    simp only [loadValue, show (8 + 7) / 8 = 1 from rfl, show (8 = 0) = False from by decide,
      ite_false, hv, hb]
    simp
  exact evalInstr_load (hp := evalOperand_reg_of env s p (.ptr addr) hp) (hv := hval)

/-- `%d = icmp ult i8 %a, <c>`. -/
theorem b_icmp_ult8_imm (env : Env) (s : State) (d a : String) (x c : BitVec 8)
    (ha : lookupName env a = some (.int 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .ult 8 (.reg a) (.imm (.int 8 c))) =
      some (withEnv ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 8 x) ha)
    (hb := evalOperand_lit_of _ 8 c)]
  simp only [withEnv, State.bind]

def udCopyBody : Block := blockAt usDecFunction 6 (by decide)

def udCopyTail : Block := blockAt usDecFunction 7 (by decide)

def udCopyTailIf : Block := blockAt usDecFunction 8 (by decide)

def udRunExit : Block := blockAt usDecFunction 9 (by decide)

def udCopyBodyN : Block := blockAt usDecFunction 24 (by decide)

def udCopyTailN : Block := blockAt usDecFunction 25 (by decide)

def udCopyTailIfN : Block := blockAt usDecFunction 26 (by decide)

theorem findBlock_udCopyBody :
    usDecFunction.findBlock "while.body.i91" = some udCopyBody := by decide

theorem findBlock_udCopyTail :
    usDecFunction.findBlock "us_run_long.exit99" = some udCopyTail := by decide

theorem findBlock_udCopyTailIf :
    usDecFunction.findBlock "if.then.i104" = some udCopyTailIf := by decide

theorem findBlock_udRunExit :
    usDecFunction.findBlock "us_run.exit" = some udRunExit := by decide

theorem findBlock_udCopyBodyN :
    usDecFunction.findBlock "while.body.i" = some udCopyBodyN := by decide

theorem findBlock_udCopyTailN :
    usDecFunction.findBlock "us_run_long.exit" = some udCopyTailN := by decide

theorem findBlock_udCopyTailIfN :
    usDecFunction.findBlock "if.then.i109" = some udCopyTailIfN := by decide

/-! ### The first copy block

One iteration of the copy after a position: two thirty-two-byte copies at
`%add.ptr + %k` and `%add.ptr + %k + 32` into `%add.ptr12 + %k` and
`%add.ptr12 + %k + 32`, then the residual count and the loop test.  The two reads
are hypotheses of the post-store state, because the first store's destination is
the second read's source only when the record's extents are disjoint; that
disjointness is the caller's staging and not this block's business. -/

def udCopyBodyIncoming : List (String × Operand) :=
  [("while.body.i91", .reg "%add.i98"), ("if.end", .imm (.int 64 (BitVec.ofInt 64 0)))]

theorem udCopyBody_instrs :
    udCopyBody.instrs =
      [ .phi "%k.0.i86290" (.int 64) udCopyBodyIncoming,
        .gep "%add.ptr.i92" (.int 8) (.reg "%add.ptr12") (.reg "%k.0.i86290"),
        .gep "%add.ptr1.i93" (.int 8) (.reg "%add.ptr") (.reg "%k.0.i86290"),
        .load "%3" (.vec 4 (.int 64)) (.reg "%add.ptr1.i93"),
        .store (.vec 4 (.int 64)) (.reg "%3") (.reg "%add.ptr.i92"),
        .gep "%add.ptr3.i95" (.int 8) (.reg "%add.ptr.i92")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .gep "%add.ptr5.i96" (.int 8) (.reg "%add.ptr1.i93")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .load "%4" (.vec 4 (.int 64)) (.reg "%add.ptr5.i96"),
        .store (.vec 4 (.int 64)) (.reg "%4") (.reg "%add.ptr3.i95"),
        .binop "%add.i98" .add 64 (.reg "%k.0.i86290")
          (.imm (.int 64 (BitVec.ofInt 64 64))),
        .binop "%sub.i87" .sub 64 (.reg "%sub13") (.reg "%add.i98"),
        .icmp "%cmp.i88" .ugt 64 (.reg "%sub.i87") (.imm (.int 64 (BitVec.ofInt 64 64))) ] := by
  decide

theorem udCopyBody_term :
    udCopyBody.term = .condbr (.reg "%cmp.i88") "while.body.i91" "us_run_long.exit99" := by
  decide

/-- The lanes the first copy's two loads bound. -/
def udK64 (bs : List UInt8) : List (BitVec 64) := unpackLanes 64 4 (bytesToNat bs)

def udCopyBodyEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (sub13 : BitVec 64) : Env :=
  ("%cmp.i88", .int 1 (evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64))
    (BitVec.ofInt 64 64))) ::
    ("%sub.i87", .int 64 (sub13 - (k + BitVec.ofInt 64 64))) ::
    ("%add.i98", .int 64 (k + BitVec.ofInt 64 64)) ::
    ("%4", .vec 4 64 (udK64 bs2)) ::
    ("%add.ptr5.i96", .ptr (src + k.toNat + 32)) ::
    ("%add.ptr3.i95", .ptr (dst + k.toNat + 32)) ::
    ("%3", .vec 4 64 (udK64 bs1)) ::
    ("%add.ptr1.i93", .ptr (src + k.toNat)) ::
    ("%add.ptr.i92", .ptr (dst + k.toNat)) ::
    ("%k.0.i86290", .int 64 k) :: env

/-- The memory the copy block leaves: the first block written at `dst + k`, the
second at `dst + k + 32`. -/
def udCopy2Mem (mem : Mem) (dst : Nat) (bs1 bs2 : List UInt8) : Mem :=
  writeBytes (writeBytes mem dst bs1) (dst + 32) bs2

theorem udCopyBody_denote (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub13 : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hsub : lookupName env "%sub13" = some (.int 64 sub13))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32) :
    denoteCode escapeCalls udCopyBody.instrs (withEnv env s) =
      some (withEnv (udCopyBodyEnv env src dst k bs1 bs2 sub13)
        { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) := by
  rw [udCopyBody_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0.i86290") (ty := .int 64) (inc := udCopyBodyIncoming) hpre hinc hop)]
  rw [show (withEnv env s).bind "%k.0.i86290" (.int 64 k) =
      withEnv (("%k.0.i86290", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr.i92" "%add.ptr12"
    "%k.0.i86290" dst k k.toNat (by ud_lk_h hdst) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr1.i93" "%add.ptr"
    "%k.0.i86290" src k k.toNat (by ud_lk_h hsrc) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%3" "%add.ptr1.i93"
    (src + k.toNat) bs1 (by ud_lk) hr1)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%3" "%add.ptr.i92"
    _ (dst + k.toNat) (by ud_lk) (by ud_lk) (by
      simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs1 hlen1]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr3.i95" "%add.ptr.i92"
    (dst + k.toNat) 32 (BitVec.ofInt 64 32)
    (by ud_lk) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr5.i96" "%add.ptr1.i93"
    (src + k.toNat) 32 (BitVec.ofInt 64 32)
    (by ud_lk) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%4" "%add.ptr5.i96"
    (src + k.toNat + 32) bs2 (by ud_lk) hr2)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%4" "%add.ptr3.i95"
    _ (dst + k.toNat + 32) (by ud_lk) (by ud_lk) (by
      simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs2 hlen2]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%add.i98" "%k.0.i86290" k
    (BitVec.ofInt 64 64) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_sub64 _ _ "%sub.i87" "%sub13" "%add.i98"
    sub13 (k + BitVec.ofInt 64 64) (by ud_lk_h hsub)
    (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ _ "%cmp.i88" "%sub.i87"
    (sub13 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64)
    (by ud_lk))]
  simp only [denoteCode, withEnv, udCopyBodyEnv, udK64, udCopy2Mem, Nat.add_assoc]

theorem udCopyBody_run (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub13 : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hsub : lookupName env "%sub13" = some (.int 64 sub13))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32) :
    Option.map State.mem (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)) =
        some (udCopy2Mem s.mem (dst + k.toNat) bs1 bs2) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%k.0.i86290") = some (.int 64 k) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr.i92") = some (.ptr (dst + k.toNat)) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr1.i93") = some (.ptr (src + k.toNat)) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i98") =
        some (.int 64 (k + BitVec.ofInt 64 64)) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%sub.i87") =
        some (.int 64 (sub13 - (k + BitVec.ofInt 64 64))) ∧
      (denoteCode escapeCalls udCopyBody.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.i88") =
        some (.int 1 (evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64))
          (BitVec.ofInt 64 64))) := by
  rw [udCopyBody_denote env s prev op src dst k bs1 bs2 sub13 hpre hinc hop hsrc hdst hsub
    hk63 hkw hr1 hr2 hlen1 hlen2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udCopyBodyEnv] <;> ud_lk)

theorem udCopyBody_step (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub13 : BitVec 64)
    (hpc : s.pc = "while.body.i91")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hsub : lookupName env "%sub13" = some (.int 64 sub13))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hcond : evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64) =
      (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyBodyEnv env src dst k bs1 bs2 sub13)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "while.body.i91", pre := some "while.body.i91" } := by
  rw [udStep_of (withEnv env s) "while.body.i91" udCopyBody _
    (by rw [withEnv]; exact hpc) findBlock_udCopyBody
    (udCopyBody_denote env s prev op src dst k bs1 bs2 sub13 hpre hinc hop hsrc hdst hsub
      hk63 hkw hr1 hr2 hlen1 hlen2), udCopyBody_term]
  have hcmp : evalOperand (withEnv (udCopyBodyEnv env src dst k bs1 bs2 sub13)
      { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 })
      (.reg "%cmp.i88") =
      some (.int 1 (evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64))
        (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ _ "%cmp.i88" _ (by
      simp only [udCopyBodyEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udCopyBody_step_zero (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub13 : BitVec 64)
    (hpc : s.pc = "while.body.i91")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hsub : lookupName env "%sub13" = some (.int 64 sub13))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hcond : evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64) =
      (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyBodyEnv env src dst k bs1 bs2 sub13)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "us_run_long.exit99", pre := some "while.body.i91" } := by
  rw [udStep_of (withEnv env s) "while.body.i91" udCopyBody _
    (by rw [withEnv]; exact hpc) findBlock_udCopyBody
    (udCopyBody_denote env s prev op src dst k bs1 bs2 sub13 hpre hinc hop hsrc hdst hsub
      hk63 hkw hr1 hr2 hlen1 hlen2), udCopyBody_term]
  have hcmp : evalOperand (withEnv (udCopyBodyEnv env src dst k bs1 bs2 sub13)
      { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 })
      (.reg "%cmp.i88") =
      some (.int 1 (evalICmp .ugt (sub13 - (k + BitVec.ofInt 64 64))
        (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ _ "%cmp.i88" _ (by
      simp only [udCopyBodyEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]



/-! ### The first copy's tail

The exit block copies one more thirty-two-byte block unconditionally and tests the
residual against thirty-two; `if.then.i104` copies a second block when the
residual reaches it, and both then rejoin at `us_run.exit`. -/

def udCopyTailIncomingK : List (String × Operand) :=
  [("if.end", .imm (.int 64 (BitVec.ofInt 64 0))),
   ("while.body.i91", .reg "%add.i98")]

def udCopyTailIncomingS : List (String × Operand) :=
  [("if.end", .reg "%sub13"), ("while.body.i91", .reg "%sub.i87")]

theorem udCopyTail_instrs :
    udCopyTail.instrs =
      [ .phi "%k.0.i86.lcssa" (.int 64) udCopyTailIncomingK,
        .phi "%sub.i87.lcssa" (.int 64) udCopyTailIncomingS,
        .gep "%add.ptr7.i89" (.int 8) (.reg "%add.ptr") (.reg "%k.0.i86.lcssa"),
        .gep "%add.ptr8.i90" (.int 8) (.reg "%add.ptr12") (.reg "%k.0.i86.lcssa"),
        .load "%5" (.vec 4 (.int 64)) (.reg "%add.ptr7.i89"),
        .store (.vec 4 (.int 64)) (.reg "%5") (.reg "%add.ptr8.i90"),
        .icmp "%cmp.i102" .ugt 64 (.reg "%sub.i87.lcssa")
          (.imm (.int 64 (BitVec.ofInt 64 32))) ] := by
  decide

theorem udCopyTail_term :
    udCopyTail.term = .condbr (.reg "%cmp.i102") "if.then.i104" "us_run.exit" := by
  decide

def udCopyTailEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub13 : BitVec 64) : Env :=
  ("%cmp.i102", .int 1 (evalICmp .ugt sub13 (BitVec.ofInt 64 32))) ::
    ("%5", .vec 4 64 (udK64 bs)) ::
    ("%add.ptr8.i90", .ptr (dst + k.toNat)) ::
    ("%add.ptr7.i89", .ptr (src + k.toNat)) ::
    ("%sub.i87.lcssa", .int 64 sub13) ::
    ("%k.0.i86.lcssa", .int 64 k) :: env

theorem udCopyTail_denote (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub13 : BitVec 64)
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub13))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32) :
    denoteCode escapeCalls udCopyTail.instrs (withEnv env s) =
      some (withEnv (udCopyTailEnv env src dst k bs sub13)
        { s with mem := writeBytes s.mem (dst + k.toNat) bs }) := by
  rw [udCopyTail_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0.i86.lcssa") (ty := .int 64) (inc := udCopyTailIncomingK) hpre hinck hopk)]
  rw [show (withEnv env s).bind "%k.0.i86.lcssa" (.int 64 k) =
      withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi
    (s := withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s)
    (d := "%sub.i87.lcssa") (ty := .int 64) (inc := udCopyTailIncomingS) hpre hincs hops)]
  rw [show (withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s).bind
      "%sub.i87.lcssa" (.int 64 sub13) =
      withEnv (("%sub.i87.lcssa", .int 64 sub13) ::
        ("%k.0.i86.lcssa", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg
    (("%sub.i87.lcssa", .int 64 sub13) :: ("%k.0.i86.lcssa", .int 64 k) :: env) s
    "%add.ptr7.i89" "%add.ptr" "%k.0.i86.lcssa" src k k.toNat
    (by ud_lk_h hsrc) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr8.i90" "%add.ptr12"
    "%k.0.i86.lcssa" dst k k.toNat (by ud_lk_h hdst) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%5" "%add.ptr7.i89"
    (src + k.toNat) bs (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%5" "%add.ptr8.i90"
    _ (dst + k.toNat) (by ud_lk) (by ud_lk) (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs hlen]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ _ "%cmp.i102" "%sub.i87.lcssa"
    sub13 (BitVec.ofInt 64 32) (by ud_lk))]
  simp only [denoteCode, withEnv, udCopyTailEnv, udK64]

theorem udCopyTail_step (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub13 : BitVec 64)
    (hpc : s.pc = "us_run_long.exit99")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub13))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32)
    (hcond : evalICmp .ugt sub13 (BitVec.ofInt 64 32) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyTailEnv env src dst k bs sub13)
                { s with mem := writeBytes s.mem (dst + k.toNat) bs }) with
              pc := "if.then.i104", pre := some "us_run_long.exit99" } := by
  rw [udStep_of (withEnv env s) "us_run_long.exit99" udCopyTail _
    (by rw [withEnv]; exact hpc) findBlock_udCopyTail
    (udCopyTail_denote env s prev opk ops src dst k bs sub13
      hpre hinck hopk hincs hops hsrc hdst hk63 hkw hr hlen), udCopyTail_term]
  have hcmp : evalOperand (withEnv (udCopyTailEnv env src dst k bs sub13)
      { s with mem := writeBytes s.mem (dst + k.toNat) bs }) (.reg "%cmp.i102") =
      some (.int 1 (evalICmp .ugt sub13 (BitVec.ofInt 64 32))) :=
    evalOperand_reg_of _ _ "%cmp.i102" _ (by simp only [udCopyTailEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udCopyTail_step_zero (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub13 : BitVec 64)
    (hpc : s.pc = "us_run_long.exit99")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i86.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub13))
    (hsrc : lookupName env "%add.ptr" = some (.ptr src))
    (hdst : lookupName env "%add.ptr12" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32)
    (hcond : evalICmp .ugt sub13 (BitVec.ofInt 64 32) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyTailEnv env src dst k bs sub13)
                { s with mem := writeBytes s.mem (dst + k.toNat) bs }) with
              pc := "us_run.exit", pre := some "us_run_long.exit99" } := by
  rw [udStep_of (withEnv env s) "us_run_long.exit99" udCopyTail _
    (by rw [withEnv]; exact hpc) findBlock_udCopyTail
    (udCopyTail_denote env s prev opk ops src dst k bs sub13
      hpre hinck hopk hincs hops hsrc hdst hk63 hkw hr hlen), udCopyTail_term]
  have hcmp : evalOperand (withEnv (udCopyTailEnv env src dst k bs sub13)
      { s with mem := writeBytes s.mem (dst + k.toNat) bs }) (.reg "%cmp.i102") =
      some (.int 1 (evalICmp .ugt sub13 (BitVec.ofInt 64 32))) :=
    evalOperand_reg_of _ _ "%cmp.i102" _ (by simp only [udCopyTailEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- `if.then.i104`: the second half of the tail's copy. -/
theorem udCopyTailIf_instrs :
    udCopyTailIf.instrs =
      [ .gep "%add.ptr.i105" (.int 8) (.reg "%add.ptr8.i90")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .gep "%add.ptr1.i106" (.int 8) (.reg "%add.ptr7.i89")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .load "%6" (.vec 4 (.int 64)) (.reg "%add.ptr1.i106"),
        .store (.vec 4 (.int 64)) (.reg "%6") (.reg "%add.ptr.i105") ] := by
  decide

theorem udCopyTailIf_term : udCopyTailIf.term = .br "us_run.exit" := by decide

def udCopyTailIfEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs2 : List UInt8) : Env :=
  ("%6", .vec 4 64 (udK64 bs2)) ::
    ("%add.ptr1.i106", .ptr (src + k.toNat + 32)) ::
    ("%add.ptr.i105", .ptr (dst + k.toNat + 32)) :: env

theorem udCopyTailIf_denote (env : Env) (s : State) (src dst : Nat) (k : BitVec 64)
    (bs1 bs2 : List UInt8)
    (h7 : lookupName env "%add.ptr7.i89" = some (.ptr (src + k.toNat)))
    (h8 : lookupName env "%add.ptr8.i90" = some (.ptr (dst + k.toNat)))
    (hr : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen : bs2.length = 32) :
    denoteCode escapeCalls udCopyTailIf.instrs
        (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }) =
      some (withEnv (udCopyTailIfEnv env src dst k bs2)
        { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) := by
  rw [udCopyTailIf_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr.i105" "%add.ptr8.i90"
    (dst + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk_h h8) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr1.i106" "%add.ptr7.i89"
    (src + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk_h h7) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _
    { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }
    "%6" "%add.ptr1.i106" (src + k.toNat + 32) bs2 (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _
    { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }
    "%6" "%add.ptr.i105" _ (dst + k.toNat + 32) (by ud_lk) (by ud_lk)
    (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs2 hlen]
  simp only [denoteCode, withEnv, udCopyTailIfEnv, udK64, udCopy2Mem]

theorem udCopyTailIf_step (env : Env) (s : State) (src dst : Nat) (k : BitVec 64)
    (bs1 bs2 : List UInt8)
    (hpc : s.pc = "if.then.i104")
    (h7 : lookupName env "%add.ptr7.i89" = some (.ptr (src + k.toNat)))
    (h8 : lookupName env "%add.ptr8.i90" = some (.ptr (dst + k.toNat)))
    (hr : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen : bs2.length = 32) :
    step escapeCalls usDecFunction
        (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }) =
      .jump { (withEnv (udCopyTailIfEnv env src dst k bs2)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "us_run.exit", pre := some "if.then.i104" } := by
  rw [udStep_of (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 })
    "if.then.i104" udCopyTailIf _ (by rw [withEnv]; exact hpc) findBlock_udCopyTailIf
    (udCopyTailIf_denote env s src dst k bs1 bs2 h7 h8 hr hlen), udCopyTailIf_term]
  simp only [execTerm, withEnv, hpc]

/-! ### `us_run.exit`

The escape byte at the position, and the test that sends it to the refusal when it
is a control byte: the `i8` load and the unsigned compare against thirty-two. -/

theorem udRunExit_instrs :
    udRunExit.instrs =
      [ .binop "%add15" .add 64 (.reg "%sub13") (.reg "%j.0294"),
        .gep "%arrayidx16" (.int 8) (.reg "%p") (.reg "%sub"),
        .load "%7" (.int 8) (.reg "%arrayidx16"),
        .icmp "%cmp18" .ult 8 (.reg "%7") (.imm (.int 8 (BitVec.ofInt 8 32))) ] := by
  decide

theorem udRunExit_term :
    udRunExit.term = .condbr (.reg "%cmp18") "if.then20" "if.end21" := by decide

/-- `us_run.exit`'s environment, at one value for its two operand registers.

**Its single `subv` is narrower than the block.**  The block reads `%add15 = %sub13 +
%j.0294` from the *residual* and `%arrayidx16 = %p + %sub` from the *head position*;
on the decoder's own iteration these are `q - i` and `q`, which agree only at cursor
zero, and the loop's cursor advances.  So the steps below — and the environment above
— state `us_run.exit` only at that one state; the iteration's exit needs the block's
step at both values, which `udRunExit_stepS_zero` in `JsonEscapeExpandAssembly`
states.  The consumers of the single-value form are the cursor-zero edge alone. -/
def udRunExitEnv (env : Env) (paddr : Nat) (subv j : BitVec 64) (b : BitVec 8) : Env :=
  ("%cmp18", .int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) ::
    ("%7", .int 8 b) ::
    ("%arrayidx16", .ptr (paddr + subv.toNat)) ::
    ("%add15", .int 64 (subv + j)) :: env

theorem udRunExit_denote (env : Env) (s : State) (paddr : Nat) (subv j : BitVec 64)
    (b : BitVec 8)
    (hsub13 : lookupName env "%sub13" = some (.int 64 subv))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode escapeCalls udRunExit.instrs (withEnv env s) =
      some (withEnv (udRunExitEnv env paddr subv j b) s) := by
  rw [udRunExit_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add15" "%sub13" "%j.0294" subv j
    (by ud_lk_h hsub13) (by ud_lk_h hj))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%arrayidx16" "%p" "%sub" paddr subv
    subv.toNat (by ud_lk_h hp) (by ud_lk_h hsub) hsw hs63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load8 _ _ "%7" "%arrayidx16" (paddr + subv.toNat) b
    (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult8_imm _ _ "%cmp18" "%7" b
    (BitVec.ofInt 8 32) (by ud_lk))]
  simp only [denoteCode, withEnv, udRunExitEnv]

theorem udRunExit_step (env : Env) (s : State) (paddr : Nat) (subv j : BitVec 64)
    (b : BitVec 8)
    (hpc : s.pc = "us_run.exit")
    (hsub13 : lookupName env "%sub13" = some (.int 64 subv))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1))
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udRunExitEnv env paddr subv j b) s) with
              pc := "if.end21", pre := some "us_run.exit" } := by
  rw [udStep_of (withEnv env s) "us_run.exit" udRunExit _
    (by rw [withEnv]; exact hpc) findBlock_udRunExit
    (udRunExit_denote env s paddr subv j b hsub13 hj hp hsub hsw hs63 hr), udRunExit_term]
  have hcmp : evalOperand (withEnv (udRunExitEnv env paddr subv j b) s) (.reg "%cmp18") =
      some (.int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) :=
    evalOperand_reg_of _ s "%cmp18" _ (by simp only [udRunExitEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udRunExit_step_one (env : Env) (s : State) (paddr : Nat) (subv j : BitVec 64)
    (b : BitVec 8)
    (hpc : s.pc = "us_run.exit")
    (hsub13 : lookupName env "%sub13" = some (.int 64 subv))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1))
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udRunExitEnv env paddr subv j b) s) with
              pc := "if.then20", pre := some "us_run.exit" } := by
  rw [udStep_of (withEnv env s) "us_run.exit" udRunExit _
    (by rw [withEnv]; exact hpc) findBlock_udRunExit
    (udRunExit_denote env s paddr subv j b hsub13 hj hp hsub hsw hs63 hr), udRunExit_term]
  have hcmp : evalOperand (withEnv (udRunExitEnv env paddr subv j b) s) (.reg "%cmp18") =
      some (.int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) :=
    evalOperand_reg_of _ s "%cmp18" _ (by simp only [udRunExitEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]


/-! ### The second copy block

The copy the walk runs after `while.end35`: the same two thirty-two-byte copies at
`%add.ptr36` and `%add.ptr37`, with the byte count taken from `%sub38`. -/

def udCopyBodyNIncoming : List (String × Operand) :=
  [("while.body.i", .reg "%add.i"), ("while.end35", .imm (.int 64 (BitVec.ofInt 64 0)))]

theorem udCopyBodyN_instrs :
    udCopyBodyN.instrs =
      [ .phi "%k.0.i304" (.int 64) udCopyBodyNIncoming,
        .gep "%add.ptr.i" (.int 8) (.reg "%add.ptr37") (.reg "%k.0.i304"),
        .gep "%add.ptr1.i" (.int 8) (.reg "%add.ptr36") (.reg "%k.0.i304"),
        .load "%31" (.vec 4 (.int 64)) (.reg "%add.ptr1.i"),
        .store (.vec 4 (.int 64)) (.reg "%31") (.reg "%add.ptr.i"),
        .gep "%add.ptr3.i" (.int 8) (.reg "%add.ptr.i")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .gep "%add.ptr5.i" (.int 8) (.reg "%add.ptr1.i")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .load "%32" (.vec 4 (.int 64)) (.reg "%add.ptr5.i"),
        .store (.vec 4 (.int 64)) (.reg "%32") (.reg "%add.ptr3.i"),
        .binop "%add.i" .add 64 (.reg "%k.0.i304")
          (.imm (.int 64 (BitVec.ofInt 64 64))),
        .binop "%sub.i" .sub 64 (.reg "%sub38") (.reg "%add.i"),
        .icmp "%cmp.i" .ugt 64 (.reg "%sub.i") (.imm (.int 64 (BitVec.ofInt 64 64))) ] := by
  decide

theorem udCopyBodyN_term :
    udCopyBodyN.term = .condbr (.reg "%cmp.i") "while.body.i" "us_run_long.exit" := by
  decide

def udCopyBodyNEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (sub38 : BitVec 64) : Env :=
  ("%cmp.i", .int 1 (evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64))
    (BitVec.ofInt 64 64))) ::
    ("%sub.i", .int 64 (sub38 - (k + BitVec.ofInt 64 64))) ::
    ("%add.i", .int 64 (k + BitVec.ofInt 64 64)) ::
    ("%32", .vec 4 64 (udK64 bs2)) ::
    ("%add.ptr5.i", .ptr (src + k.toNat + 32)) ::
    ("%add.ptr3.i", .ptr (dst + k.toNat + 32)) ::
    ("%31", .vec 4 64 (udK64 bs1)) ::
    ("%add.ptr1.i", .ptr (src + k.toNat)) ::
    ("%add.ptr.i", .ptr (dst + k.toNat)) ::
    ("%k.0.i304", .int 64 k) :: env

theorem udCopyBodyN_denote (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub38 : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyNIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hsub : lookupName env "%sub38" = some (.int 64 sub38))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32) :
    denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s) =
      some (withEnv (udCopyBodyNEnv env src dst k bs1 bs2 sub38)
        { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) := by
  rw [udCopyBodyN_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0.i304") (ty := .int 64) (inc := udCopyBodyNIncoming) hpre hinc hop)]
  rw [show (withEnv env s).bind "%k.0.i304" (.int 64 k) =
      withEnv (("%k.0.i304", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr.i" "%add.ptr37"
    "%k.0.i304" dst k k.toNat (by ud_lk_h hdst) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr1.i" "%add.ptr36"
    "%k.0.i304" src k k.toNat (by ud_lk_h hsrc) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%31" "%add.ptr1.i"
    (src + k.toNat) bs1 (by ud_lk) hr1)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%31" "%add.ptr.i"
    _ (dst + k.toNat) (by ud_lk) (by ud_lk) (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs1 hlen1]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr3.i" "%add.ptr.i"
    (dst + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr5.i" "%add.ptr1.i"
    (src + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%32" "%add.ptr5.i"
    (src + k.toNat + 32) bs2 (by ud_lk) hr2)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%32" "%add.ptr3.i"
    _ (dst + k.toNat + 32) (by ud_lk) (by ud_lk) (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs2 hlen2]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%add.i" "%k.0.i304" k
    (BitVec.ofInt 64 64) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_sub64 _ _ "%sub.i" "%sub38" "%add.i"
    sub38 (k + BitVec.ofInt 64 64) (by ud_lk_h hsub) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ _ "%cmp.i" "%sub.i"
    (sub38 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64) (by ud_lk))]
  simp only [denoteCode, withEnv, udCopyBodyNEnv, udK64, udCopy2Mem]

theorem udCopyBodyN_run (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub38 : BitVec 64)
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyNIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hsub : lookupName env "%sub38" = some (.int 64 sub38))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32) :
    Option.map State.mem (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)) =
        some (udCopy2Mem s.mem (dst + k.toNat) bs1 bs2) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%k.0.i304") = some (.int 64 k) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr.i") = some (.ptr (dst + k.toNat)) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr1.i") = some (.ptr (src + k.toNat)) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i") =
        some (.int 64 (k + BitVec.ofInt 64 64)) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%sub.i") =
        some (.int 64 (sub38 - (k + BitVec.ofInt 64 64))) ∧
      (denoteCode escapeCalls udCopyBodyN.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.i") =
        some (.int 1 (evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64))
          (BitVec.ofInt 64 64))) := by
  rw [udCopyBodyN_denote env s prev op src dst k bs1 bs2 sub38 hpre hinc hop hsrc hdst hsub
    hk63 hkw hr1 hr2 hlen1 hlen2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udCopyBodyNEnv] <;> ud_lk)

theorem udCopyBodyN_step (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub38 : BitVec 64)
    (hpc : s.pc = "while.body.i")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyNIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hsub : lookupName env "%sub38" = some (.int 64 sub38))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hcond : evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64) =
      (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyBodyNEnv env src dst k bs1 bs2 sub38)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "while.body.i", pre := some "while.body.i" } := by
  rw [udStep_of (withEnv env s) "while.body.i" udCopyBodyN _
    (by rw [withEnv]; exact hpc) findBlock_udCopyBodyN
    (udCopyBodyN_denote env s prev op src dst k bs1 bs2 sub38 hpre hinc hop hsrc hdst hsub
      hk63 hkw hr1 hr2 hlen1 hlen2), udCopyBodyN_term]
  have hcmp : evalOperand (withEnv (udCopyBodyNEnv env src dst k bs1 bs2 sub38)
      { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 })
      (.reg "%cmp.i") =
      some (.int 1 (evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64))
        (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ _ "%cmp.i" _ (by simp only [udCopyBodyNEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udCopyBodyN_step_zero (env : Env) (s : State) (prev : String) (op : Operand)
    (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (sub38 : BitVec 64)
    (hpc : s.pc = "while.body.i")
    (hpre : s.pre = some prev) (hinc : phiIncoming prev udCopyBodyNIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 k))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hsub : lookupName env "%sub38" = some (.int 64 sub38))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr1 : readBytes s.mem (src + k.toNat) 32 = some bs1)
    (hr2 : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hcond : evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64) =
      (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyBodyNEnv env src dst k bs1 bs2 sub38)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "us_run_long.exit", pre := some "while.body.i" } := by
  rw [udStep_of (withEnv env s) "while.body.i" udCopyBodyN _
    (by rw [withEnv]; exact hpc) findBlock_udCopyBodyN
    (udCopyBodyN_denote env s prev op src dst k bs1 bs2 sub38 hpre hinc hop hsrc hdst hsub
      hk63 hkw hr1 hr2 hlen1 hlen2), udCopyBodyN_term]
  have hcmp : evalOperand (withEnv (udCopyBodyNEnv env src dst k bs1 bs2 sub38)
      { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 })
      (.reg "%cmp.i") =
      some (.int 1 (evalICmp .ugt (sub38 - (k + BitVec.ofInt 64 64))
        (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ _ "%cmp.i" _ (by simp only [udCopyBodyNEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### The second copy's tail -/

def udCopyTailNIncomingK : List (String × Operand) :=
  [("while.end35", .imm (.int 64 (BitVec.ofInt 64 0))),
   ("while.body.i", .reg "%add.i")]

def udCopyTailNIncomingS : List (String × Operand) :=
  [("while.end35", .reg "%sub38"), ("while.body.i", .reg "%sub.i")]

theorem udCopyTailN_instrs :
    udCopyTailN.instrs =
      [ .phi "%k.0.i.lcssa" (.int 64) udCopyTailNIncomingK,
        .phi "%sub.i.lcssa" (.int 64) udCopyTailNIncomingS,
        .gep "%add.ptr7.i" (.int 8) (.reg "%add.ptr36") (.reg "%k.0.i.lcssa"),
        .gep "%add.ptr8.i" (.int 8) (.reg "%add.ptr37") (.reg "%k.0.i.lcssa"),
        .load "%33" (.vec 4 (.int 64)) (.reg "%add.ptr7.i"),
        .store (.vec 4 (.int 64)) (.reg "%33") (.reg "%add.ptr8.i"),
        .icmp "%cmp.i107" .ugt 64 (.reg "%sub.i.lcssa")
          (.imm (.int 64 (BitVec.ofInt 64 32))) ] := by
  decide

theorem udCopyTailN_term :
    udCopyTailN.term = .condbr (.reg "%cmp.i107") "if.then.i109" "us_run.exit112" := by
  decide

def udCopyTailNEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub38 : BitVec 64) : Env :=
  ("%cmp.i107", .int 1 (evalICmp .ugt sub38 (BitVec.ofInt 64 32))) ::
    ("%33", .vec 4 64 (udK64 bs)) ::
    ("%add.ptr8.i", .ptr (dst + k.toNat)) ::
    ("%add.ptr7.i", .ptr (src + k.toNat)) ::
    ("%sub.i.lcssa", .int 64 sub38) ::
    ("%k.0.i.lcssa", .int 64 k) :: env

theorem udCopyTailN_denote (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub38 : BitVec 64)
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailNIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailNIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub38))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32) :
    denoteCode escapeCalls udCopyTailN.instrs (withEnv env s) =
      some (withEnv (udCopyTailNEnv env src dst k bs sub38)
        { s with mem := writeBytes s.mem (dst + k.toNat) bs }) := by
  rw [udCopyTailN_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%k.0.i.lcssa") (ty := .int 64) (inc := udCopyTailNIncomingK) hpre hinck hopk)]
  rw [show (withEnv env s).bind "%k.0.i.lcssa" (.int 64 k) =
      withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi
    (s := withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s)
    (d := "%sub.i.lcssa") (ty := .int 64) (inc := udCopyTailNIncomingS) hpre hincs hops)]
  rw [show (withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s).bind
      "%sub.i.lcssa" (.int 64 sub38) =
      withEnv (("%sub.i.lcssa", .int 64 sub38) ::
        ("%k.0.i.lcssa", .int 64 k) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr7.i" "%add.ptr36"
    "%k.0.i.lcssa" src k k.toNat (by ud_lk_h hsrc) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr8.i" "%add.ptr37"
    "%k.0.i.lcssa" dst k k.toNat (by ud_lk_h hdst) (by ud_lk) hkw hk63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _ _ "%33" "%add.ptr7.i"
    (src + k.toNat) bs (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _ _ "%33" "%add.ptr8.i"
    _ (dst + k.toNat) (by ud_lk) (by ud_lk) (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs hlen]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ _ "%cmp.i107" "%sub.i.lcssa"
    sub38 (BitVec.ofInt 64 32) (by ud_lk))]
  simp only [denoteCode, withEnv, udCopyTailNEnv, udK64]

theorem udCopyTailN_step (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub38 : BitVec 64)
    (hpc : s.pc = "us_run_long.exit")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailNIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailNIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub38))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32)
    (hcond : evalICmp .ugt sub38 (BitVec.ofInt 64 32) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyTailNEnv env src dst k bs sub38)
                { s with mem := writeBytes s.mem (dst + k.toNat) bs }) with
              pc := "if.then.i109", pre := some "us_run_long.exit" } := by
  rw [udStep_of (withEnv env s) "us_run_long.exit" udCopyTailN _
    (by rw [withEnv]; exact hpc) findBlock_udCopyTailN
    (udCopyTailN_denote env s prev opk ops src dst k bs sub38
      hpre hinck hopk hincs hops hsrc hdst hk63 hkw hr hlen), udCopyTailN_term]
  have hcmp : evalOperand (withEnv (udCopyTailNEnv env src dst k bs sub38)
      { s with mem := writeBytes s.mem (dst + k.toNat) bs }) (.reg "%cmp.i107") =
      some (.int 1 (evalICmp .ugt sub38 (BitVec.ofInt 64 32))) :=
    evalOperand_reg_of _ _ "%cmp.i107" _ (by simp only [udCopyTailNEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udCopyTailN_step_zero (env : Env) (s : State) (prev : String)
    (opk ops : Operand) (src dst : Nat) (k : BitVec 64) (bs : List UInt8)
    (sub38 : BitVec 64)
    (hpc : s.pc = "us_run_long.exit")
    (hpre : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailNIncomingK = some opk)
    (hopk : evalOperand (withEnv env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailNIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i.lcssa", .int 64 k) :: env) s) ops =
      some (.int 64 sub38))
    (hsrc : lookupName env "%add.ptr36" = some (.ptr src))
    (hdst : lookupName env "%add.ptr37" = some (.ptr dst))
    (hk63 : k.toNat < 2 ^ 63)
    (hkw : (k.signExtend 64).toNat = k.toNat)
    (hr : readBytes s.mem (src + k.toNat) 32 = some bs)
    (hlen : bs.length = 32)
    (hcond : evalICmp .ugt sub38 (BitVec.ofInt 64 32) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCopyTailNEnv env src dst k bs sub38)
                { s with mem := writeBytes s.mem (dst + k.toNat) bs }) with
              pc := "us_run.exit112", pre := some "us_run_long.exit" } := by
  rw [udStep_of (withEnv env s) "us_run_long.exit" udCopyTailN _
    (by rw [withEnv]; exact hpc) findBlock_udCopyTailN
    (udCopyTailN_denote env s prev opk ops src dst k bs sub38
      hpre hinck hopk hincs hops hsrc hdst hk63 hkw hr hlen), udCopyTailN_term]
  have hcmp : evalOperand (withEnv (udCopyTailNEnv env src dst k bs sub38)
      { s with mem := writeBytes s.mem (dst + k.toNat) bs }) (.reg "%cmp.i107") =
      some (.int 1 (evalICmp .ugt sub38 (BitVec.ofInt 64 32))) :=
    evalOperand_reg_of _ _ "%cmp.i107" _ (by simp only [udCopyTailNEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- `if.then.i109`: the second half of the second copy's tail. -/
theorem udCopyTailIfN_instrs :
    udCopyTailIfN.instrs =
      [ .gep "%add.ptr.i110" (.int 8) (.reg "%add.ptr8.i")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .gep "%add.ptr1.i111" (.int 8) (.reg "%add.ptr7.i")
          (.imm (.int 64 (BitVec.ofInt 64 32))),
        .load "%34" (.vec 4 (.int 64)) (.reg "%add.ptr1.i111"),
        .store (.vec 4 (.int 64)) (.reg "%34") (.reg "%add.ptr.i110") ] := by
  decide

theorem udCopyTailIfN_term : udCopyTailIfN.term = .br "us_run.exit112" := by decide

def udCopyTailIfNEnv (env : Env) (src dst : Nat) (k : BitVec 64) (bs2 : List UInt8) : Env :=
  ("%34", .vec 4 64 (udK64 bs2)) ::
    ("%add.ptr1.i111", .ptr (src + k.toNat + 32)) ::
    ("%add.ptr.i110", .ptr (dst + k.toNat + 32)) :: env

theorem udCopyTailIfN_denote (env : Env) (s : State) (src dst : Nat) (k : BitVec 64)
    (bs1 bs2 : List UInt8)
    (h7 : lookupName env "%add.ptr7.i" = some (.ptr (src + k.toNat)))
    (h8 : lookupName env "%add.ptr8.i" = some (.ptr (dst + k.toNat)))
    (hr : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen : bs2.length = 32) :
    denoteCode escapeCalls udCopyTailIfN.instrs
        (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }) =
      some (withEnv (udCopyTailIfNEnv env src dst k bs2)
        { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) := by
  rw [udCopyTailIfN_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr.i110" "%add.ptr8.i"
    (dst + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk_h h8) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr1.i111" "%add.ptr7.i"
    (src + k.toNat) 32 (BitVec.ofInt 64 32) (by ud_lk_h h7) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load_vec4_64 _
    { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }
    "%34" "%add.ptr1.i111" (src + k.toNat + 32) bs2 (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store_vec4_64 _
    { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }
    "%34" "%add.ptr.i110" _ (dst + k.toNat + 32) (by ud_lk) (by ud_lk)
    (by simp [unpackLanes_length]))]
  rw [packLanes_copy32 bs2 hlen]
  simp only [denoteCode, withEnv, udCopyTailIfNEnv, udK64, udCopy2Mem]

theorem udCopyTailIfN_step (env : Env) (s : State) (src dst : Nat) (k : BitVec 64)
    (bs1 bs2 : List UInt8)
    (hpc : s.pc = "if.then.i109")
    (h7 : lookupName env "%add.ptr7.i" = some (.ptr (src + k.toNat)))
    (h8 : lookupName env "%add.ptr8.i" = some (.ptr (dst + k.toNat)))
    (hr : readBytes (writeBytes s.mem (dst + k.toNat) bs1)
      (src + k.toNat + 32) 32 = some bs2)
    (hlen : bs2.length = 32) :
    step escapeCalls usDecFunction
        (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 }) =
      .jump { (withEnv (udCopyTailIfNEnv env src dst k bs2)
                { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }) with
              pc := "us_run.exit112", pre := some "if.then.i109" } := by
  rw [udStep_of (withEnv env { s with mem := writeBytes s.mem (dst + k.toNat) bs1 })
    "if.then.i109" udCopyTailIfN _ (by rw [withEnv]; exact hpc) findBlock_udCopyTailIfN
    (udCopyTailIfN_denote env s src dst k bs1 bs2 h7 h8 hr hlen), udCopyTailIfN_term]
  simp only [execTerm, withEnv, hpc]


/-! ### The escape table's reading

The rewritten body reads a byte's escape image out of `%tab` and decides with a
signed compare against `-1`.  `unescapeTable` is `simpleEscape`'s image at every
byte and `0xFF` elsewhere, so the compare's bit is the rule's own test — and that
is the bridge this group states, separately from the block, because the block's
trace is about the byte it loaded and the bridge is about what the table means.

The bridge's signed comparison carries one of this module's two `Classical.choice`
carriers, and it is the proof's rather than a lemma's: `evalICmp_sgt_negone_one_iff`
unfolds `BitVec.toInt` on an eight-bit word into its two branches and closes each
with `omega`, which reaches `Decidable.byContradiction` on the goal's `↔` —
`Classical.propDecidable` — in the two branch helpers it generates.
`unescapeTable_test` inherits exactly that carrier and nothing else.  The module's
other carrier is `Nat.and_two_pow_sub_one_eq_mod`, named at `and65535_ofNat` and
inherited by `pmadd_hexFour` and `hex4_pmadd`.  The block lemmas use neither and
stay at `[propext, Quot.sound]`. -/

/-- The table's entry at a byte is that byte's escape image, or `0xFF`. -/
theorem unescapeTable_getElem? (b : UInt8) :
    unescapeTable[b.toNat]? = some ((simpleEscape b).getD 0xFF) := by
  unfold unescapeTable
  rw [List.getElem?_map, List.getElem?_range (by simpa using b.toNat_lt)]
  simp

/-- A table entry is a positive signed byte exactly for the bytes an escape stands
for: `simpleEscape`'s images are all below `0x80`, and its absence is `0xFF`. -/
theorem simpleEscape_getD_highBit (b : UInt8) :
    ((simpleEscape b).getD 0xFF).toNat < 128 ↔ simpleEscape b ≠ none := by
  cases h : simpleEscape b with
  | none => simp
  | some e =>
      have he : e.toNat < 128 := by
        unfold simpleEscape at h
        repeat' split at h
        all_goals (first
          | (simp only [Option.some.injEq] at h; subst h; decide)
          | (simp at h))
      simp [he]

/-- The signed compare against `-1` reads the byte's high bit: `sgt` is true
exactly at a byte below `0x80`. -/
theorem evalICmp_sgt_negone_one_iff (t : BitVec 8) :
    evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1) ↔ t.toNat < 128 := by
  rw [show evalICmp .sgt t (BitVec.ofInt 8 (-1)) =
      BitVec.ofBool (decide ((BitVec.ofInt 8 (-1)).toInt < t.toInt)) from rfl]
  rw [ofBool_decide_one_iff]
  have hneg : (BitVec.ofInt 8 (-1)).toInt = (-1 : Int) := by decide
  rw [hneg]
  unfold BitVec.toInt
  split <;> omega

/-- **The table bridge.**  Given the table entry the body loaded, the body's
signed test is the specification's "this byte is a two-character escape". -/
theorem unescapeTable_test (b u : UInt8)
    (ht : unescapeTable[b.toNat]? = some u) :
    evalICmp .sgt (BitVec.ofNat 8 u.toNat) (BitVec.ofInt 8 (-1)) = (1 : BitVec 1) ↔
      simpleEscape b ≠ none := by
  rw [unescapeTable_getElem?] at ht
  injection ht with ht
  subst ht
  rw [evalICmp_sgt_negone_one_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by
      have h := UInt8.toNat_lt ((simpleEscape b).getD 0xFF)
      rwa [show (2 : Nat) ^ 8 = 256 from by decide] at h),
    simpleEscape_getD_highBit]

/-! ### The instruction shapes the reader needs -/

/-- `%d = zext i8 %src to i64`. -/
theorem b_zext8_64 (env : Env) (s : State) (d src : String) (x : BitVec 8)
    (h : lookupName env src = some (.int 8 x)) :
    evalInstr escapeCalls (withEnv env s) (.zext d 8 64 (.reg src)) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s src (.int 8 x) h)]
  simp only [withEnv, State.bind]

/-- `store i8 %v, ptr %p`. -/
theorem b_store8 (env : Env) (s : State) (r p : String) (x : BitVec 8) (a : Nat)
    (hv : lookupName env r = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr escapeCalls (withEnv env s) (.store (.int 8) (.reg r) (.reg p)) =
      some (withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  refine evalInstr_store (vv := .int 8 x) (a := a)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
    ?_ ?_ ?_
  · exact evalOperand_reg_of env s r (.int 8 x) hv
  · exact evalOperand_reg_of env s p (.ptr a) hp
  · simp [storeValue, withEnv]

/-- `%d = icmp sgt i8 %a, <c>`. -/
theorem b_icmp_sgt8_imm (env : Env) (s : State) (d a : String) (x c : BitVec 8)
    (ha : lookupName env a = some (.int 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .sgt 8 (.reg a) (.imm (.int 8 c))) =
      some (withEnv ((d, .int 1 (evalICmp .sgt x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 8 x) ha)
    (hb := evalOperand_lit_of _ 8 c)]
  simp only [withEnv, State.bind]

/-! ### `if.end.i`

The escape reader: the byte at the body cursor, its table image, and the signed
test that says whether it is a two-character escape. -/

def udIfEndI : Block := blockAt usDecFunction 12 (by decide)

def udIfThen6I : Block := blockAt usDecFunction 13 (by decide)

theorem findBlock_udIfEndI : usDecFunction.findBlock "if.end.i" = some udIfEndI := by
  decide

theorem findBlock_udIfThen6I :
    usDecFunction.findBlock "if.then6.i" = some udIfThen6I := by decide

theorem udIfEndI_instrs :
    udIfEndI.instrs =
      [ .gep "%arrayidx.i" (.int 8) (.reg "%p") (.reg "%add.i100"),
        .load "%8" (.int 8) (.reg "%arrayidx.i"),
        .zext "%idxprom.i" 8 64 (.reg "%8"),
        .gep "%arrayidx2.i" (.int 8) (.reg "%tab") (.reg "%idxprom.i"),
        .load "%9" (.int 8) (.reg "%arrayidx2.i"),
        .icmp "%cmp4.i" .sgt 8 (.reg "%9") (.imm (.int 8 (BitVec.ofInt 8 (-1)))) ] := by
  decide

theorem udIfEndI_term :
    udIfEndI.term = .condbr (.reg "%cmp4.i") "if.then6.i" "if.end9.i" := by decide

def udIfEndIEnv (env : Env) (paddr tab : Nat) (off : BitVec 64) (b t : BitVec 8) : Env :=
  ("%cmp4.i", .int 1 (evalICmp .sgt t (BitVec.ofInt 8 (-1)))) ::
    ("%9", .int 8 t) ::
    ("%arrayidx2.i", .ptr (tab + b.toNat)) ::
    ("%idxprom.i", .int 64 (BitVec.ofNat 64 b.toNat)) ::
    ("%8", .int 8 b) ::
    ("%arrayidx.i", .ptr (paddr + off.toNat)) :: env

theorem udIfEndI_denote (env : Env) (s : State) (paddr tab : Nat) (off : BitVec 64)
    (b t : BitVec 8)
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hoffw : (off.signExtend 64).toNat = off.toNat)
    (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes b.toNat 1))
    (ht : readBytes s.mem (tab + b.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 b.toNat).signExtend 64).toNat = b.toNat) :
    denoteCode escapeCalls udIfEndI.instrs (withEnv env s) =
      some (withEnv (udIfEndIEnv env paddr tab off b t) s) := by
  rw [udIfEndI_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%arrayidx.i" "%p" "%add.i100"
    paddr off off.toNat (by ud_lk_h hp) (by ud_lk_h hoff) hoffw hoff63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load8 _ _ "%8" "%arrayidx.i" (paddr + off.toNat) b
    (by ud_lk) hb)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext8_64 _ _ "%idxprom.i" "%8" b (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%arrayidx2.i" "%tab" "%idxprom.i"
    tab (BitVec.ofNat 64 b.toNat) b.toNat (by ud_lk_h htab) (by ud_lk)
    hgw (by exact Nat.lt_of_lt_of_le b.isLt (by decide)))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load8 _ _ "%9" "%arrayidx2.i" (tab + b.toNat) t
    (by ud_lk) ht)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_sgt8_imm _ _ "%cmp4.i" "%9" t
    (BitVec.ofInt 8 (-1)) (by ud_lk))]
  simp only [denoteCode, withEnv, udIfEndIEnv]

theorem udIfEndI_run (env : Env) (s : State) (paddr tab : Nat) (off : BitVec 64)
    (b t : BitVec 8)
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hoffw : (off.signExtend 64).toNat = off.toNat)
    (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes b.toNat 1))
    (ht : readBytes s.mem (tab + b.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 b.toNat).signExtend 64).toNat = b.toNat) :
    Option.map State.mem (denoteCode escapeCalls udIfEndI.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEndI.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%8") = some (.int 8 b) ∧
      (denoteCode escapeCalls udIfEndI.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%9") = some (.int 8 t) ∧
      (denoteCode escapeCalls udIfEndI.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp4.i") =
        some (.int 1 (evalICmp .sgt t (BitVec.ofInt 8 (-1)))) := by
  rw [udIfEndI_denote env s paddr tab off b t hp hoff htab hoffw hoff63 hb ht hgw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udIfEndIEnv] <;> ud_lk)

theorem udIfEndI_step (env : Env) (s : State) (paddr tab : Nat) (off : BitVec 64)
    (b t : BitVec 8)
    (hpc : s.pc = "if.end.i")
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hoffw : (off.signExtend 64).toNat = off.toNat)
    (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes b.toNat 1))
    (ht : readBytes s.mem (tab + b.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 b.toNat).signExtend 64).toNat = b.toNat)
    (hcond : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndIEnv env paddr tab off b t) s) with
              pc := "if.then6.i", pre := some "if.end.i" } := by
  rw [udStep_of (withEnv env s) "if.end.i" udIfEndI _
    (by rw [withEnv]; exact hpc) findBlock_udIfEndI
    (udIfEndI_denote env s paddr tab off b t hp hoff htab hoffw hoff63 hb ht hgw),
    udIfEndI_term]
  have hcmp : evalOperand (withEnv (udIfEndIEnv env paddr tab off b t) s)
      (.reg "%cmp4.i") =
      some (.int 1 (evalICmp .sgt t (BitVec.ofInt 8 (-1)))) :=
    evalOperand_reg_of _ s "%cmp4.i" _ (by simp only [udIfEndIEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udIfEndI_step_zero (env : Env) (s : State) (paddr tab : Nat) (off : BitVec 64)
    (b t : BitVec 8)
    (hpc : s.pc = "if.end.i")
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hoffw : (off.signExtend 64).toNat = off.toNat)
    (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes b.toNat 1))
    (ht : readBytes s.mem (tab + b.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 b.toNat).signExtend 64).toNat = b.toNat)
    (hcond : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndIEnv env paddr tab off b t) s) with
              pc := "if.end9.i", pre := some "if.end.i" } := by
  rw [udStep_of (withEnv env s) "if.end.i" udIfEndI _
    (by rw [withEnv]; exact hpc) findBlock_udIfEndI
    (udIfEndI_denote env s paddr tab off b t hp hoff htab hoffw hoff63 hb ht hgw),
    udIfEndI_term]
  have hcmp : evalOperand (withEnv (udIfEndIEnv env paddr tab off b t) s)
      (.reg "%cmp4.i") =
      some (.int 1 (evalICmp .sgt t (BitVec.ofInt 8 (-1)))) :=
    evalOperand_reg_of _ s "%cmp4.i" _ (by simp only [udIfEndIEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `if.then6.i`

The two-character escape's store: the table's byte written at the destination
cursor, and the cursor advanced by one. -/

theorem udIfThen6I_instrs :
    udIfThen6I.instrs =
      [ .gep "%arrayidx7.i" (.int 8) (.reg "%dst") (.reg "%add15"),
        .store (.int 8) (.reg "%9") (.reg "%arrayidx7.i"),
        .binop "%add8.i" .add 64 (.reg "%add15")
          (.imm (.int 64 (BitVec.ofInt 64 1))) ] := by
  decide

theorem udIfThen6I_term : udIfThen6I.term = .br "cleanup32" := by decide

def udIfThen6IEnv (env : Env) (daddr : Nat) (out : BitVec 64) : Env :=
  ("%add8.i", .int 64 (out + BitVec.ofInt 64 1)) ::
    ("%arrayidx7.i", .ptr (daddr + out.toNat)) :: env

theorem udIfThen6I_denote (env : Env) (s : State) (daddr : Nat) (out : BitVec 64)
    (t : BitVec 8)
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hout : lookupName env "%add15" = some (.int 64 out))
    (ht : lookupName env "%9" = some (.int 8 t))
    (how : (out.signExtend 64).toNat = out.toNat)
    (ho63 : out.toNat < 2 ^ 63) :
    denoteCode escapeCalls udIfThen6I.instrs (withEnv env s) =
      some (withEnv (udIfThen6IEnv env daddr out)
        { s with mem := writeBytes s.mem (daddr + out.toNat) (natToBytes t.toNat 1) }) := by
  rw [udIfThen6I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%arrayidx7.i" "%dst" "%add15"
    daddr out out.toNat (by ud_lk_h hdst) (by ud_lk_h hout) how ho63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store8 _ s "%9" "%arrayidx7.i" t
    (daddr + out.toNat) (by ud_lk_h ht) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _
    { s with mem := writeBytes s.mem (daddr + out.toNat) (natToBytes t.toNat 1) }
    "%add8.i" "%add15" out (BitVec.ofInt 64 1)
    (by ud_lk_h hout))]
  simp only [denoteCode, withEnv, udIfThen6IEnv]

theorem udIfThen6I_step (env : Env) (s : State) (daddr : Nat) (out : BitVec 64)
    (t : BitVec 8)
    (hpc : s.pc = "if.then6.i")
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hout : lookupName env "%add15" = some (.int 64 out))
    (ht : lookupName env "%9" = some (.int 8 t))
    (how : (out.signExtend 64).toNat = out.toNat)
    (ho63 : out.toNat < 2 ^ 63) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfThen6IEnv env daddr out)
                { s with mem := writeBytes s.mem (daddr + out.toNat) (natToBytes t.toNat 1) }) with
              pc := "cleanup32", pre := some "if.then6.i" } := by
  rw [udStep_of (withEnv env s) "if.then6.i" udIfThen6I _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen6I
    (udIfThen6I_denote env s daddr out t hdst hout ht how ho63), udIfThen6I_term]
  simp only [execTerm, withEnv, hpc]



end LeanLLVM.Refinement


namespace LeanLLVM.Refinement

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.udStep_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udStep_of

/-- info: 'LeanLLVM.Refinement.udRun_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRun_jump

/-- info: 'LeanLLVM.Refinement.udRun_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRun_ret

/-- info: 'LeanLLVM.Refinement.udCondbr_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCondbr_one

/-- info: 'LeanLLVM.Refinement.udCondbr_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCondbr_zero

/-- info: 'LeanLLVM.Refinement.b_icmp_ult64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult64

/-- info: 'LeanLLVM.Refinement.b_icmp_ult64_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult64_imm

/-- info: 'LeanLLVM.Refinement.b_sub64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_sub64

/-- info: 'LeanLLVM.Refinement.b_load32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load32

/-- info: 'LeanLLVM.Refinement.b_icmp_eq32_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_eq32_imm

/-- info: 'LeanLLVM.Refinement.udEntry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_denote

/-- info: 'LeanLLVM.Refinement.udEntry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_run

/-- info: 'LeanLLVM.Refinement.udEntry_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_cells

/-- info: 'LeanLLVM.Refinement.udEntry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_step

/-- info: 'LeanLLVM.Refinement.udEntry_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_step_zero

/-- info: 'LeanLLVM.Refinement.udWhileBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_denote

/-- info: 'LeanLLVM.Refinement.udWhileBody_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_run

/-- info: 'LeanLLVM.Refinement.udWhileBody_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_cells

/-- info: 'LeanLLVM.Refinement.udWhileBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_step

/-- info: 'LeanLLVM.Refinement.udWhileBody_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_step_one

/-- info: 'LeanLLVM.Refinement.udWhileEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_denote

/-- info: 'LeanLLVM.Refinement.udWhileEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_run

/-- info: 'LeanLLVM.Refinement.udWhileEnd_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_cells

/-- info: 'LeanLLVM.Refinement.udWhileEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_step

/-- info: 'LeanLLVM.Refinement.udWhileEnd_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_step_one

/-- info: 'LeanLLVM.Refinement.udIfThen20_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_denote

/-- info: 'LeanLLVM.Refinement.udIfThen20_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_run

/-- info: 'LeanLLVM.Refinement.udIfThen20_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_step

/-- info: 'LeanLLVM.Refinement.udIfThen22_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_denote

/-- info: 'LeanLLVM.Refinement.udIfThen22_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_run

/-- info: 'LeanLLVM.Refinement.udIfThen22_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_step

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_denote

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_run

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_cells

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_step

/-- info: 'LeanLLVM.Refinement.udCleanup41_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_denote

/-- info: 'LeanLLVM.Refinement.udCleanup41_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_run

/-- info: 'LeanLLVM.Refinement.udCleanup41_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_step





/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.b_gep8_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_gep8_reg

/-- info: 'LeanLLVM.Refinement.b_icmp_ugt64_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ugt64_imm

/-- info: 'LeanLLVM.Refinement.udLandRhs_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_denote

/-- info: 'LeanLLVM.Refinement.udLandRhs_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_run

/-- info: 'LeanLLVM.Refinement.udLandRhs_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_cells

/-- info: 'LeanLLVM.Refinement.udLandRhs_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_step

/-- info: 'LeanLLVM.Refinement.udLandRhs_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_step_zero

/-- info: 'LeanLLVM.Refinement.udWhileBody6_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_denote

/-- info: 'LeanLLVM.Refinement.udWhileBody6_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_run

/-- info: 'LeanLLVM.Refinement.udWhileBody6_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_step

/-- info: 'LeanLLVM.Refinement.udWhileBody6_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_step_one

/-- info: 'LeanLLVM.Refinement.udIfEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_denote

/-- info: 'LeanLLVM.Refinement.udIfEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_run

/-- info: 'LeanLLVM.Refinement.udIfEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_step

/-- info: 'LeanLLVM.Refinement.udIfEnd_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_step_zero

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### Axiom footprints: the copy and escape-byte blocks -/

/-- info: 'LeanLLVM.Refinement.b_load_vec4_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load_vec4_64

/-- info: 'LeanLLVM.Refinement.b_store_vec4_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store_vec4_64

/-- info: 'LeanLLVM.Refinement.packLanes_copy32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms packLanes_copy32

/-- info: 'LeanLLVM.Refinement.b_load8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load8

/-- info: 'LeanLLVM.Refinement.b_icmp_ult8_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult8_imm

/-- info: 'LeanLLVM.Refinement.udCopyBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_denote

/-- info: 'LeanLLVM.Refinement.udCopyBody_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_run

/-- info: 'LeanLLVM.Refinement.udCopyBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_step

/-- info: 'LeanLLVM.Refinement.udCopyBody_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_step_zero

/-- info: 'LeanLLVM.Refinement.udCopyTail_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_denote

/-- info: 'LeanLLVM.Refinement.udCopyTail_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_step

/-- info: 'LeanLLVM.Refinement.udCopyTail_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_step_zero

/-- info: 'LeanLLVM.Refinement.udCopyTailIf_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIf_denote

/-- info: 'LeanLLVM.Refinement.udCopyTailIf_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIf_step

/-- info: 'LeanLLVM.Refinement.udRunExit_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_denote

/-- info: 'LeanLLVM.Refinement.udRunExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_step

/-- info: 'LeanLLVM.Refinement.udRunExit_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_step_one

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_denote

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_run

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_step

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_step_zero

/-- info: 'LeanLLVM.Refinement.udCopyTailN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_denote

/-- info: 'LeanLLVM.Refinement.udCopyTailN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_step

/-- info: 'LeanLLVM.Refinement.udCopyTailN_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_step_zero

/-- info: 'LeanLLVM.Refinement.udCopyTailIfN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIfN_denote

/-- info: 'LeanLLVM.Refinement.udCopyTailIfN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIfN_step

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### Axiom footprints: the block shapes -/

/-- info: 'LeanLLVM.Refinement.findBlock_udEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udEntry

/-- info: 'LeanLLVM.Refinement.findBlock_udLandRhs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udLandRhs

/-- info: 'LeanLLVM.Refinement.findBlock_udWhileBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileBody

/-- info: 'LeanLLVM.Refinement.findBlock_udWhileEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileEnd

/-- info: 'LeanLLVM.Refinement.findBlock_udWhileBody6' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileBody6

/-- info: 'LeanLLVM.Refinement.findBlock_udIfEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEnd

/-- info: 'LeanLLVM.Refinement.findBlock_udIfThen20' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen20

/-- info: 'LeanLLVM.Refinement.findBlock_udIfThen22' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen22

/-- info: 'LeanLLVM.Refinement.findBlock_udCleanup32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCleanup32

/-- info: 'LeanLLVM.Refinement.findBlock_udUsRunExit112' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udUsRunExit112

/-- info: 'LeanLLVM.Refinement.findBlock_udCleanup41' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCleanup41

/-- info: 'LeanLLVM.Refinement.udEntry_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_instrs

/-- info: 'LeanLLVM.Refinement.udEntry_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_term

/-- info: 'LeanLLVM.Refinement.udWhileBody_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_instrs

/-- info: 'LeanLLVM.Refinement.udWhileBody_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_term

/-- info: 'LeanLLVM.Refinement.udWhileEnd_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_instrs

/-- info: 'LeanLLVM.Refinement.udWhileEnd_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_term

/-- info: 'LeanLLVM.Refinement.udIfThen20_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen20_instrs

/-- info: 'LeanLLVM.Refinement.udIfThen20_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen20_term

/-- info: 'LeanLLVM.Refinement.udIfThen22_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen22_instrs

/-- info: 'LeanLLVM.Refinement.udIfThen22_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen22_term

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_instrs

/-- info: 'LeanLLVM.Refinement.udUsRunExit112_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_term

/-- info: 'LeanLLVM.Refinement.udCleanup41_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup41_instrs

/-- info: 'LeanLLVM.Refinement.udCleanup41_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup41_term

/-- info: 'LeanLLVM.Refinement.udLandRhs_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_instrs

/-- info: 'LeanLLVM.Refinement.udLandRhs_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_term

/-- info: 'LeanLLVM.Refinement.udWhileBody6_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody6_instrs

/-- info: 'LeanLLVM.Refinement.udWhileBody6_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody6_term

/-- info: 'LeanLLVM.Refinement.udIfEnd_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd_instrs

/-- info: 'LeanLLVM.Refinement.udIfEnd_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd_term

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyBody

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyTail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTail

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyTailIf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailIf

/-- info: 'LeanLLVM.Refinement.findBlock_udRunExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udRunExit

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyBodyN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyBodyN

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyTailN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailN

/-- info: 'LeanLLVM.Refinement.findBlock_udCopyTailIfN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailIfN

/-- info: 'LeanLLVM.Refinement.udCopyBody_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBody_instrs

/-- info: 'LeanLLVM.Refinement.udCopyBody_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBody_term

/-- info: 'LeanLLVM.Refinement.udCopyTail_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTail_instrs

/-- info: 'LeanLLVM.Refinement.udCopyTail_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTail_term

/-- info: 'LeanLLVM.Refinement.udCopyTailIf_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIf_instrs

/-- info: 'LeanLLVM.Refinement.udCopyTailIf_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIf_term

/-- info: 'LeanLLVM.Refinement.udRunExit_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udRunExit_instrs

/-- info: 'LeanLLVM.Refinement.udRunExit_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udRunExit_term

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBodyN_instrs

/-- info: 'LeanLLVM.Refinement.udCopyBodyN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBodyN_term

/-- info: 'LeanLLVM.Refinement.udCopyTailN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailN_instrs

/-- info: 'LeanLLVM.Refinement.udCopyTailN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailN_term

/-- info: 'LeanLLVM.Refinement.udCopyTailIfN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIfN_instrs

/-- info: 'LeanLLVM.Refinement.udCopyTailIfN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIfN_term

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

open LeanLLVM.Refinement.BitLanes

/-! ### The hex bridge

`if.end.i115` tests four byte lanes with the emitted range arithmetic and computes
the code unit with two multiply-adds.  The predicates here are the specification's
`hexDigit` and `hex4`: the lane test is `hexDigit`'s success (`hexDigit_lane`,
`hexLaneTest_iff`), the four-lane aggregate is the conjunction of the four tests
(`hexTest_low_four`), and the multiply-adds' lane 0 masked to sixteen bits is
`hex4`'s value (`pmadd_hexFour`, `hex4_pmadd`). -/

/-- The emitted test at one byte lane: a digit, or a letter after the `| 32`. -/
def hexLaneTest (x : BitVec 8) : Bool :=
  BitVec.ult (x + BitVec.ofInt 8 (-48)) (BitVec.ofInt 8 10) ||
  BitVec.ult ((x ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97)) (BitVec.ofInt 8 6)

/-- The nibble a hex lane contributes: its low four bits, plus nine for a letter. -/
def hexNib (x : BitVec 8) : Nat :=
  (x &&& BitVec.ofInt 8 15).toNat +
    (if BitVec.ult ((x ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97)) (BitVec.ofInt 8 6)
     then 9 else 0)

/-- The nibble as the byte the emitted `select` and `and` build. -/
def hexNib8 (x : BitVec 8) : BitVec 8 :=
  (x &&& BitVec.ofInt 8 15) +
    (if BitVec.ult ((x ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97)) (BitVec.ofInt 8 6)
     then 9 else 0)

/-- The lane-test vector, one lane per byte. -/
def hexTestLanes (l : List (BitVec 8)) : List (BitVec 1) :=
  l.map (fun x => BitVec.ofBool (hexLaneTest x))

/-- The code unit four nibble lanes spell. -/
def hexFour (x0 x1 x2 x3 : BitVec 8) : Nat :=
  hexNib x0 * 4096 + hexNib x1 * 256 + hexNib x2 * 16 + hexNib x3

theorem ofBool_eq_one (b : Bool) : (BitVec.ofBool b = (1 : BitVec 1)) ↔ b = true := by
  cases b <;> simp

/-- A lane's test is `hexDigit`'s own success. -/
theorem hexDigit_lane (x : BitVec 8) :
    hexDigit (UInt8.ofBitVec x) =
      (if hexLaneTest x then some (hexNib x) else none) := by
  decide +revert

/-- A lane's test succeeds exactly when `hexDigit` does. -/
theorem hexLaneTest_iff (x : BitVec 8) :
    hexLaneTest x = true ↔ hexDigit (UInt8.ofBitVec x) ≠ none := by
  rw [hexDigit_lane]
  by_cases h : hexLaneTest x <;> simp [h]

theorem hexNib_eq (x : BitVec 8) : hexNib x = (hexNib8 x).toNat := by
  decide +revert

theorem hexNib_lt {x : BitVec 8} (h : hexLaneTest x = true) : hexNib x < 16 := by
  decide +revert

theorem hexFour_eq_nib (l : List (BitVec 8)) :
    hexFour (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) =
      4096 * (hexNib8 (l.getD 0 0)).toNat + 256 * (hexNib8 (l.getD 1 0)).toNat +
        16 * (hexNib8 (l.getD 2 0)).toNat + (hexNib8 (l.getD 3 0)).toNat := by
  simp [hexFour, hexNib_eq]
  omega

theorem ofInt_toNat_of_range {w : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < (2 ^ w : Int)) :
    (BitVec.ofInt w k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt]
  exact congrArg Int.toNat (Int.emod_eq_of_lt h0 h1)

theorem ofInt_eq_ofNat_of_range {w : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < (2 ^ w : Int)) :
    BitVec.ofInt w k = BitVec.ofNat w k.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [ofInt_toNat_of_range h0 h1, BitVec.toNat_ofNat]
  have hk : k.toNat < 2 ^ w := by
    have hk' : (↑(k.toNat) : Int) < (↑(2 ^ w) : Int) := by
      rw [Int.toNat_of_nonneg h0]; exact h1
    exact_mod_cast hk'
  exact (Nat.mod_eq_of_lt hk).symm

theorem hK0 {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    (0 : Int) ≤ (x0.toNat : Int) * 16 + (x1.toNat : Int) * 1 := by omega
theorem hKhi {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    (x0.toNat : Int) * 16 + (x1.toNat : Int) * 1 ≤ 32767 := by omega
theorem hKlo {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    -32768 ≤ (x0.toNat : Int) * 16 + (x1.toNat : Int) * 1 := by omega
theorem hKlt {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    (x0.toNat : Int) * 16 + (x1.toNat : Int) * 1 < (2 ^ 16 : Int) := by omega
theorem hKn {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    ((x0.toNat : Int) * 16 + (x1.toNat : Int) * 1).toNat = 16 * x0.toNat + x1.toNat := by omega

theorem pmaddUbSwLane_small {x0 x1 : BitVec 8} (h0 : x0.toNat < 16) (h1 : x1.toNat < 16) :
    pmaddUbSwLane x0 x1 (BitVec.ofNat 8 16) (BitVec.ofNat 8 1) =
      BitVec.ofNat 16 (16 * x0.toNat + x1.toNat) := by
  unfold pmaddUbSwLane
  rw [show (BitVec.ofNat 8 16).toInt = 16 from by decide,
      show (BitVec.ofNat 8 1).toInt = 1 from by decide]
  rw [satI16_of_range (hKhi h0 h1) (hKlo h0 h1)]
  rw [ofInt_eq_ofNat_of_range (w := 16) (hK0 h0 h1) (hKlt h0 h1)]
  rw [hKn h0 h1]

theorem wK0 {w0 w1 : BitVec 16} (h0 : w0.toNat < 256) (h1 : w1.toNat < 256) :
    (0 : Int) ≤ (w0.toNat : Int) * 256 + (w1.toNat : Int) * 1 := by omega
theorem wKlt {w0 w1 : BitVec 16} (h0 : w0.toNat < 256) (h1 : w1.toNat < 256) :
    (w0.toNat : Int) * 256 + (w1.toNat : Int) * 1 < (2 ^ 32 : Int) := by omega
theorem wKn {w0 w1 : BitVec 16} (h0 : w0.toNat < 256) (h1 : w1.toNat < 256) :
    ((w0.toNat : Int) * 256 + (w1.toNat : Int) * 1).toNat = 256 * w0.toNat + w1.toNat := by omega

theorem pmaddWdLane_small {w0 w1 : BitVec 16} (h0 : w0.toNat < 256) (h1 : w1.toNat < 256) :
    pmaddWdLane w0 w1 (BitVec.ofNat 16 256) (BitVec.ofNat 16 1) =
      BitVec.ofNat 32 (256 * w0.toNat + w1.toNat) := by
  unfold pmaddWdLane
  rw [show (BitVec.ofNat 16 256).toInt = 256 from by decide,
      show (BitVec.ofNat 16 1).toInt = 1 from by decide]
  have i0 : w0.toInt = (w0.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  have i1 : w1.toInt = (w1.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  rw [i0, i1]
  rw [ofInt_eq_ofNat_of_range (w := 32) (wK0 h0 h1) (wKlt h0 h1)]
  rw [wKn h0 h1]

/-- Masking a value below `2 ^ 16` with `65535` is the identity.  The carrier is
`Nat.and_two_pow_sub_one_eq_mod`'s `Classical.choice`. -/
theorem and65535_ofNat {v : Nat} (h : v < 65536) :
    (BitVec.ofNat 32 v) &&& (BitVec.ofNat 32 65535) = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show 65535 % 2 ^ 32 = 65535 from Nat.mod_eq_of_lt (by decide)]
  rw [show v % 2 ^ 32 = v from Nat.mod_eq_of_lt (by omega)]
  rw [show (65535 : Nat) = 2 ^ 16 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

def hexW8 : List (BitVec 8) :=
  [16, 1, 16, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].map fun n => BitVec.ofNat 8 n

def hexW16 : List (BitVec 16) :=
  [256, 1, 0, 0, 0, 0, 0, 0].map fun n => BitVec.ofNat 16 n

def nibVec (n0 n1 n2 n3 : BitVec 8) : List (BitVec 8) :=
  [n0, n1, n2, n3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem hexW8_eq : hexW8 =
    (BitVec.ofNat 8 16) :: (BitVec.ofNat 8 1) ::
    (BitVec.ofNat 8 16) :: (BitVec.ofNat 8 1) ::
    [0,0,0,0,0,0,0,0,0,0,0,0] := rfl

theorem hexW16_eq : hexW16 =
    (BitVec.ofNat 16 256) :: (BitVec.ofNat 16 1) :: [0,0,0,0,0,0] := rfl

theorem hexReduceUbSw (n0 n1 n2 n3 : BitVec 8) :
    pmaddUbSw (nibVec n0 n1 n2 n3) hexW8 =
      [pmaddUbSwLane n0 n1 (BitVec.ofNat 8 16) (BitVec.ofNat 8 1),
       pmaddUbSwLane n2 n3 (BitVec.ofNat 8 16) (BitVec.ofNat 8 1),
       0, 0, 0, 0, 0, 0] := by
  rw [hexW8_eq]
  change pmaddUbSw (n0 :: n1 :: n2 :: n3 :: [0,0,0,0,0,0,0,0,0,0,0,0])
    ((BitVec.ofNat 8 16) :: (BitVec.ofNat 8 1) :: (BitVec.ofNat 8 16) ::
     (BitVec.ofNat 8 1) :: [0,0,0,0,0,0,0,0,0,0,0,0]) = _
  rw [pmaddUbSw_cons]
  rw [pmaddUbSw_cons]
  have h : pmaddUbSw [0,0,0,0,0,0,0,0,0,0,0,0] [0,0,0,0,0,0,0,0,0,0,0,0] =
      [0,0,0,0,0,0] := by decide
  rw [h]

theorem hexReduceWd (w0 w1 : BitVec 16) :
    pmaddWd (w0 :: w1 :: [0,0,0,0,0,0]) hexW16 =
      [pmaddWdLane w0 w1 (BitVec.ofNat 16 256) (BitVec.ofNat 16 1), 0, 0, 0] := by
  rw [hexW16_eq]
  rw [pmaddWd_cons]
  have h : pmaddWd [0,0,0,0,0,0] [0,0,0,0,0,0] = [0,0,0] := by decide
  rw [h]

/-- The two multiply-adds on four nibble lanes are `hex4`'s value. -/
theorem pmadd_hexFour (n0 n1 n2 n3 : BitVec 8)
    (h0 : n0.toNat < 16) (h1 : n1.toNat < 16) (h2 : n2.toNat < 16) (h3 : n3.toNat < 16) :
    ((pmaddWd (pmaddUbSw (nibVec n0 n1 n2 n3) hexW8) hexW16)[0]!) &&&
        (BitVec.ofNat 32 65535) =
      BitVec.ofNat 32 (4096 * n0.toNat + 256 * n1.toNat + 16 * n2.toNat + n3.toNat) := by
  rw [hexReduceUbSw]
  rw [hexReduceWd]
  rw [pmaddUbSwLane_small h0 h1, pmaddUbSwLane_small h2 h3]
  change pmaddWdLane (BitVec.ofNat 16 (16 * n0.toNat + n1.toNat))
      (BitVec.ofNat 16 (16 * n2.toNat + n3.toNat))
      (BitVec.ofNat 16 256) (BitVec.ofNat 16 1) &&& (BitVec.ofNat 32 65535) =
    BitVec.ofNat 32 (4096 * n0.toNat + 256 * n1.toNat + 16 * n2.toNat + n3.toNat)
  have b0 : (BitVec.ofNat 16 (16 * n0.toNat + n1.toNat)).toNat < 256 := by
    rw [BitVec.toNat_ofNat]
    have hv : 16 * n0.toNat + n1.toNat < 256 := by omega
    omega
  have b1 : (BitVec.ofNat 16 (16 * n2.toNat + n3.toNat)).toNat < 256 := by
    rw [BitVec.toNat_ofNat]
    have hv : 16 * n2.toNat + n3.toNat < 256 := by omega
    omega
  rw [pmaddWdLane_small b0 b1]
  have e0 : (BitVec.ofNat 16 (16 * n0.toNat + n1.toNat)).toNat = 16 * n0.toNat + n1.toNat := by
    rw [BitVec.toNat_ofNat]
    have hv : 16 * n0.toNat + n1.toNat < 256 := by omega
    omega
  have e1 : (BitVec.ofNat 16 (16 * n2.toNat + n3.toNat)).toNat = 16 * n2.toNat + n3.toNat := by
    rw [BitVec.toNat_ofNat]
    have hv : 16 * n2.toNat + n3.toNat < 256 := by omega
    omega
  rw [e0, e1]
  rw [show 256 * (16 * n0.toNat + n1.toNat) + (16 * n2.toNat + n3.toNat) =
      4096 * n0.toNat + 256 * n1.toNat + 16 * n2.toNat + n3.toNat from by omega]
  rw [and65535_ofNat (by omega)]

/-- With the four lane tests satisfied, `hex4` is the pmadd chain's value. -/
theorem hex4_of_lane_test {bs : List UInt8} {q : Nat} {l : List (BitVec 8)}
    (hbytes : ∀ i, i < 16 → bs[q + i]? = some (UInt8.ofBitVec (l.getD i 0)))
    (h0 : hexLaneTest (l.getD 0 0) = true) (h1 : hexLaneTest (l.getD 1 0) = true)
    (h2 : hexLaneTest (l.getD 2 0) = true) (h3 : hexLaneTest (l.getD 3 0) = true) :
    hex4 bs q = some (hexFour (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)) := by
  unfold hex4
  rw [show bs[q]? = some (UInt8.ofBitVec (l.getD 0 0)) from by
        simpa using hbytes 0 (by decide),
      show bs[q+1]? = some (UInt8.ofBitVec (l.getD 1 0)) from by
        simpa using hbytes 1 (by decide),
      show bs[q+2]? = some (UInt8.ofBitVec (l.getD 2 0)) from by
        simpa using hbytes 2 (by decide),
      show bs[q+3]? = some (UInt8.ofBitVec (l.getD 3 0)) from by
        simpa using hbytes 3 (by decide)]
  simp only [hexDigit_lane, h0, h1, h2, h3]
  rfl

/-- A failing lane test is `hex4`'s refusal. -/
theorem hex4_none_of_lane_test {bs : List UInt8} {q : Nat} {l : List (BitVec 8)}
    (hbytes : ∀ i, i < 16 → bs[q + i]? = some (UInt8.ofBitVec (l.getD i 0)))
    (h : hexLaneTest (l.getD 0 0) = false ∨ hexLaneTest (l.getD 1 0) = false ∨
         hexLaneTest (l.getD 2 0) = false ∨ hexLaneTest (l.getD 3 0) = false) :
    hex4 bs q = none := by
  unfold hex4
  rw [show bs[q]? = some (UInt8.ofBitVec (l.getD 0 0)) from by simpa using hbytes 0 (by decide),
      show bs[q+1]? = some (UInt8.ofBitVec (l.getD 1 0)) from by simpa using hbytes 1 (by decide),
      show bs[q+2]? = some (UInt8.ofBitVec (l.getD 2 0)) from by simpa using hbytes 2 (by decide),
      show bs[q+3]? = some (UInt8.ofBitVec (l.getD 3 0)) from by simpa using hbytes 3 (by decide)]
  simp only [hexDigit_lane]
  simp only [List.getD] at h
  rcases h with h|h|h|h <;> (split <;> simp_all)

/-- The four low lanes of the body's mask are the four bytes' tests. -/
theorem hexTest_low_four (x0 x1 x2 x3 : BitVec 8) (rest : List (BitVec 8)) :
    (lanesToNat (hexTestLanes (x0 :: x1 :: x2 :: x3 :: rest))) % 16 =
      (if hexLaneTest x0 then 1 else 0) + 2 * (if hexLaneTest x1 then 1 else 0) +
      4 * (if hexLaneTest x2 then 1 else 0) + 8 * (if hexLaneTest x3 then 1 else 0) := by
  have hEq : lanesToNat (hexTestLanes (x0 :: x1 :: x2 :: x3 :: rest)) =
      16 * lanesToNat (hexTestLanes rest) +
      ((if hexLaneTest x0 then 1 else 0) + 2 * (if hexLaneTest x1 then 1 else 0) +
       4 * (if hexLaneTest x2 then 1 else 0) + 8 * (if hexLaneTest x3 then 1 else 0)) := by
    simp only [hexTestLanes, List.map_cons, lanesToNat, ofBool_eq_one]
    omega
  rw [hEq, Nat.mul_comm 16]
  rw [Nat.mul_add_mod_self_right]
  have hlt : (if hexLaneTest x0 then 1 else 0) + 2 * (if hexLaneTest x1 then 1 else 0) +
      4 * (if hexLaneTest x2 then 1 else 0) + 8 * (if hexLaneTest x3 then 1 else 0) < 16 := by
    split <;> split <;> split <;> split <;> omega
  exact Nat.mod_eq_of_lt hlt

theorem hexTest_four_eq_fifteen (b0 b1 b2 b3 : Bool) :
    ((if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) +
     4 * (if b2 then 1 else 0) + 8 * (if b3 then 1 else 0) = 15) ↔
      (b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

/-- **The hex bridge.**  From the four lane tests, `hex4` is the code unit the
pmadd chain's lane 0 masked with `65535` carries. -/
theorem hex4_pmadd {bs : List UInt8} {q : Nat} {l : List (BitVec 8)}
    (hbytes : ∀ i, i < 16 → bs[q + i]? = some (UInt8.ofBitVec (l.getD i 0)))
    (h0 : hexLaneTest (l.getD 0 0) = true) (h1 : hexLaneTest (l.getD 1 0) = true)
    (h2 : hexLaneTest (l.getD 2 0) = true) (h3 : hexLaneTest (l.getD 3 0) = true) :
    hex4 bs q = some
      (((pmaddWd (pmaddUbSw
          (nibVec (hexNib8 (l.getD 0 0)) (hexNib8 (l.getD 1 0))
                  (hexNib8 (l.getD 2 0)) (hexNib8 (l.getD 3 0))) hexW8) hexW16)[0]!) &&&
        (BitVec.ofInt 32 65535)).toNat := by
  rw [hex4_of_lane_test hbytes h0 h1 h2 h3]
  have n0 : (hexNib8 (l.getD 0 0)).toNat < 16 := by
    rw [← hexNib_eq]; exact hexNib_lt h0
  have n1 : (hexNib8 (l.getD 1 0)).toNat < 16 := by
    rw [← hexNib_eq]; exact hexNib_lt h1
  have n2 : (hexNib8 (l.getD 2 0)).toNat < 16 := by
    rw [← hexNib_eq]; exact hexNib_lt h2
  have n3 : (hexNib8 (l.getD 3 0)).toNat < 16 := by
    rw [← hexNib_eq]; exact hexNib_lt h3
  rw [show (BitVec.ofInt 32 65535) = (BitVec.ofNat 32 65535) from BitVec.ofInt_ofNat 32 65535]
  rw [pmadd_hexFour _ _ _ _ n0 n1 n2 n3]
  rw [BitVec.toNat_ofNat]
  have hV : 4096 * (hexNib8 (l.getD 0 0)).toNat + 256 * (hexNib8 (l.getD 1 0)).toNat +
      16 * (hexNib8 (l.getD 2 0)).toNat + (hexNib8 (l.getD 3 0)).toNat < 2 ^ 32 := by
    have a0 := (hexNib8 (l.getD 0 0)).isLt
    have a1 := (hexNib8 (l.getD 1 0)).isLt
    have a2 := (hexNib8 (l.getD 2 0)).isLt
    have a3 := (hexNib8 (l.getD 3 0)).isLt
    simp only [BitVec.isLt] at a0 a1 a2 a3
    omega
  rw [Nat.mod_eq_of_lt hV]
  rw [hexFour_eq_nib]

/-- info: 'LeanLLVM.Refinement.hexDigit_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexDigit_lane

/-- info: 'LeanLLVM.Refinement.hexLaneTest_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexLaneTest_iff

/-- info: 'LeanLLVM.Refinement.hex4_of_lane_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hex4_of_lane_test

/-- info: 'LeanLLVM.Refinement.hex4_none_of_lane_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hex4_none_of_lane_test

/-- info: 'LeanLLVM.Refinement.hexTest_low_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexTest_low_four

/-! The two multiply-adds inherit `and65535_ofNat`'s carrier — the mask to sixteen
bits is `Nat.and_two_pow_sub_one_eq_mod`, whose own proof carries
`Classical.choice` through `Nat.testBit_two_pow_sub_one` — and add nothing to it. -/

/-- info: 'LeanLLVM.Refinement.pmadd_hexFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pmadd_hexFour

/-- info: 'LeanLLVM.Refinement.hex4_pmadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hex4_pmadd

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes

/-! ### `if.end9.i`

The `\u` guard: the second body byte is `u`, the escape's six bytes fit, and the
branch taken depends on both. -/

theorem b_icmp_ne8_imm (env : Env) (s : State) (d a : String) (x c : BitVec 8)
    (ha : lookupName env a = some (.int 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .ne 8 (.reg a) (.imm (.int 8 c))) =
      some (withEnv ((d, .int 1 (evalICmp .ne x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 8 x) ha)
    (hb := evalOperand_lit_of _ 8 c)]
  simp only [withEnv, State.bind]

theorem b_icmp_ugt64r (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d .ugt 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (evalICmp .ugt x y)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

theorem evalBinopNat_or1 (x y : BitVec 1) :
    evalBinopNat .or 1 x.toNat y.toNat = some (x.toNat ||| y.toNat) := by
  simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.toNat_or]

theorem b_or1 (env : Env) (s : State) (d a b : String) (x y : BitVec 1)
    (ha : lookupName env a = some (.int 1 x)) (hb : lookupName env b = some (.int 1 y)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .or 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (x ||| y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 1 x) ha)
    (hb := evalOperand_reg_of env s b (.int 1 y) hb)
    (hr := evalBinopNat_or1 x y)]
  simp only [withEnv, State.bind]
  rw [show BitVec.ofNat 1 (x.toNat ||| y.toNat) = x ||| y from by
    rw [← BitVec.toNat_or x y, BitVec.ofNat_toNat, BitVec.setWidth_eq]]

def udIfEnd9I : Block := blockAt usDecFunction 14 (by decide)

theorem findBlock_udIfEnd9I : usDecFunction.findBlock "if.end9.i" = some udIfEnd9I := by
  decide

theorem udIfEnd9I_instrs :
    udIfEnd9I.instrs =
      [ .icmp "%cmp10.not.i" .ne 8 (.reg "%8") (.imm (.int 8 (BitVec.ofInt 8 117))),
        .binop "%add.i113" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 6))),
        .icmp "%cmp.i114" .ugt 64 (.reg "%add.i113") (.reg "%n"),
        .binop "%or.cond335" .or 1 (.reg "%cmp10.not.i") (.reg "%cmp.i114") ] := by
  decide

theorem udIfEnd9I_term :
    udIfEnd9I.term = .condbr (.reg "%or.cond335") "if.then22" "if.end.i115" := by decide

def udIfEnd9IEnv (env : Env) (off : BitVec 64) (c1 c2 : BitVec 1) : Env :=
  ("%or.cond335", .int 1 (c1 ||| c2)) ::
    ("%cmp.i114", .int 1 c2) ::
    ("%add.i113", .int 64 off) ::
    ("%cmp10.not.i", .int 1 c1) :: env

theorem udIfEnd9I_denote (env : Env) (s : State) (sub n : BitVec 64) (b : BitVec 8)
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode escapeCalls udIfEnd9I.instrs (withEnv env s) =
      some (withEnv (udIfEnd9IEnv env (sub + BitVec.ofInt 64 6)
        (evalICmp .ne b (BitVec.ofInt 8 117))
        (evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) s) := by
  rw [udIfEnd9I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ne8_imm _ _ "%cmp10.not.i" "%8" b
    (BitVec.ofInt 8 117) (by ud_lk_h h8))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _
    "%add.i113" "%sub" sub (BitVec.ofInt 64 6) (by ud_lk_h hsub))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64r _ _
    "%cmp.i114" "%add.i113" "%n" (sub + BitVec.ofInt 64 6) n (by ud_lk) (by ud_lk_h hn))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or1 _ _
    "%or.cond335" "%cmp10.not.i" "%cmp.i114"
    (evalICmp .ne b (BitVec.ofInt 8 117))
    (evalICmp .ugt (sub + BitVec.ofInt 64 6) n) (by ud_lk) (by ud_lk))]
  simp only [denoteCode, withEnv, udIfEnd9IEnv]

theorem udIfEnd9I_run (env : Env) (s : State) (sub n : BitVec 64) (b : BitVec 8)
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    Option.map State.mem (denoteCode escapeCalls udIfEnd9I.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEnd9I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%or.cond335") =
        some (.int 1 (evalICmp .ne b (BitVec.ofInt 8 117) |||
                       evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) := by
  rw [udIfEnd9I_denote env s sub n b h8 hsub hn]
  refine ⟨?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udIfEnd9IEnv]
    ud_lk

theorem udIfEnd9I_step (env : Env) (s : State) (sub n : BitVec 64) (b : BitVec 8)
    (hpc : s.pc = "if.end9.i")
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hcond : (evalICmp .ne b (BitVec.ofInt 8 117) |||
              evalICmp .ugt (sub + BitVec.ofInt 64 6) n) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd9IEnv env (sub + BitVec.ofInt 64 6)
                (evalICmp .ne b (BitVec.ofInt 8 117))
                (evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) s) with
              pc := "if.then22", pre := some "if.end9.i" } := by
  rw [udStep_of (withEnv env s) "if.end9.i" udIfEnd9I _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd9I
    (udIfEnd9I_denote env s sub n b h8 hsub hn), udIfEnd9I_term]
  have hcmp : evalOperand (withEnv (udIfEnd9IEnv env (sub + BitVec.ofInt 64 6)
      (evalICmp .ne b (BitVec.ofInt 8 117))
      (evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) s) (.reg "%or.cond335") =
      some (.int 1 (evalICmp .ne b (BitVec.ofInt 8 117) |||
                     evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) :=
    evalOperand_reg_of _ s "%or.cond335" _ (by simp only [udIfEnd9IEnv]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udIfEnd9I_step_zero (env : Env) (s : State) (sub n : BitVec 64) (b : BitVec 8)
    (hpc : s.pc = "if.end9.i")
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hcond : (evalICmp .ne b (BitVec.ofInt 8 117) |||
              evalICmp .ugt (sub + BitVec.ofInt 64 6) n) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd9IEnv env (sub + BitVec.ofInt 64 6)
                (evalICmp .ne b (BitVec.ofInt 8 117))
                (evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) s) with
              pc := "if.end.i115", pre := some "if.end9.i" } := by
  rw [udStep_of (withEnv env s) "if.end9.i" udIfEnd9I _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd9I
    (udIfEnd9I_denote env s sub n b h8 hsub hn), udIfEnd9I_term]
  have hcmp : evalOperand (withEnv (udIfEnd9IEnv env (sub + BitVec.ofInt 64 6)
      (evalICmp .ne b (BitVec.ofInt 8 117))
      (evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) s) (.reg "%or.cond335") =
      some (.int 1 (evalICmp .ne b (BitVec.ofInt 8 117) |||
                     evalICmp .ugt (sub + BitVec.ofInt 64 6) n)) :=
    evalOperand_reg_of _ s "%or.cond335" _ (by simp only [udIfEnd9IEnv]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- info: 'LeanLLVM.Refinement.udIfEnd9I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd9I_denote

/-- info: 'LeanLLVM.Refinement.udIfEnd9I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd9I_run

/-- info: 'LeanLLVM.Refinement.udIfEnd9I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd9I_step

/-- info: 'LeanLLVM.Refinement.udIfEnd9I_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd9I_step_zero

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes

def hexAddL (l : List (BitVec 8)) (c : BitVec 8) : List (BitVec 8) := l.map fun v => v + c
def hexOrL (l : List (BitVec 8)) (c : BitVec 8) : List (BitVec 8) := l.map fun v => v ||| c
def hexUltL (l : List (BitVec 8)) (c : BitVec 8) : List (BitVec 1) := l.map fun v => evalICmp .ult v c
def hexZipOr (x y : List (BitVec 1)) : List (BitVec 1) := (x.zip y).map fun p => p.1 ||| p.2

theorem hexAddL_length (l : List (BitVec 8)) (c : BitVec 8) : (hexAddL l c).length = l.length := by
  simp [hexAddL]
theorem hexOrL_length (l : List (BitVec 8)) (c : BitVec 8) : (hexOrL l c).length = l.length := by
  simp [hexOrL]
theorem hexUltL_length (l : List (BitVec 8)) (c : BitVec 8) : (hexUltL l c).length = l.length := by
  simp [hexUltL]
theorem hexZipOr_length (x y : List (BitVec 1)) : (hexZipOr x y).length = min x.length y.length := by
  simp [hexZipOr]

theorem bitcast_vec2_64_16_8 {bs : List UInt8} (hlen : bs.length = 16) :
    bitcastVecLanes 8 16 (unpackLanes 64 2 (bytesToNat bs)) = byteLanes bs := by
  unfold bitcastVecLanes
  rw [packLanes_unpackLanes]
  rw [show 2 * 64 = 128 from rfl]
  rw [show bytesToNat bs % 2 ^ 128 = bytesToNat bs from by
    apply Nat.mod_eq_of_lt
    have := bytesToNat_lt bs
    rw [hlen] at this
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul] at this
    rw [show (16 * 8 : Nat) = 128 from rfl] at this
    exact this]
  exact byteLanes_eq_unpackLanes hlen

theorem load_vec2_64 (env : Env) (s : State) (d p : String) (addr : Nat) (bs : List UInt8)
    (hp : lookupName env p = some (.ptr addr))
    (hlen : bs.length = 16)
    (hr : readBytes s.mem addr 16 = some bs) :
    evalInstr escapeCalls (withEnv env s) (.load d (.vec 2 (.int 64)) (.reg p)) =
      some (withEnv ((d, .vec 2 64 (unpackLanes 64 2 (bytesToNat bs))) :: env) s) := by
  rw [evalInstr_load (p := .reg p) (a := addr)
    (by simp only [withEnv, evalOperand, hp])
    (loadValue_vec_int (by decide) (by decide) hr)]
  rfl

theorem b_vecBitcast_2_64_16_8 (env : Env) (s : State) (d a : String)
    (bs : List UInt8)
    (ha : lookupName env a = some (.vec 2 64 (unpackLanes 64 2 (bytesToNat bs))))
    (hlen : bs.length = 16) :
    evalInstr escapeCalls (withEnv env s) (.vecBitcast d 2 64 16 8 (.reg a)) =
      some (withEnv ((d, .vec 16 8 (byteLanes bs)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := evalOperand_reg_of env s a _ ha)
    (hl := vecLanes_self (unpackLanes_length 64 2 (bytesToNat bs))) (hwidth := by decide)]
  simp only [withEnv, State.bind]
  rw [bitcast_vec2_64_16_8 hlen]

theorem b_binopVec_add_splat (env : Env) (s : State) (d a : String)
    (x : List (BitVec 8)) (c : BitVec 8) (hlen : x.length = 16)
    (ha : lookupName env a = some (.vec 16 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binopVec d .add 16 8 (.reg a) (.imm (.splat 16 8 c))) =
      some (withEnv ((d, .vec 16 8 (hexAddL x c)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := List.replicate 16 c)
    (ls := hexAddL x c) hlen (by simp)
    (by simp only [withEnv, evalOperand, ha])
    (by simp only [withEnv, evalOperand, Const.toValue])
    (by
      rw [← hlen]
      exact zipReplicate_mapM x c (fun u v => evalBinop .add u v) (fun v => v + c) (fun v => rfl))]
  simp only [withEnv, State.bind, hexAddL]

theorem b_binopVec_or_splat (env : Env) (s : State) (d a : String)
    (x : List (BitVec 8)) (c : BitVec 8) (hlen : x.length = 16)
    (ha : lookupName env a = some (.vec 16 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binopVec d .or 16 8 (.reg a) (.imm (.splat 16 8 c))) =
      some (withEnv ((d, .vec 16 8 (hexOrL x c)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := List.replicate 16 c)
    (ls := hexOrL x c) hlen (by simp)
    (by simp only [withEnv, evalOperand, ha])
    (by simp only [withEnv, evalOperand, Const.toValue])
    (by
      rw [← hlen]
      exact zipReplicate_mapM x c (fun u v => evalBinop .or u v) (fun v => v ||| c) (fun v => rfl))]
  simp only [withEnv, State.bind, hexOrL]

theorem b_icmpVec_ult_splat (env : Env) (s : State) (d a : String)
    (x : List (BitVec 8)) (c : BitVec 8) (hlen : x.length = 16)
    (ha : lookupName env a = some (.vec 16 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmpVec d .ult 16 8 (.reg a) (.imm (.splat 16 8 c))) =
      some (withEnv ((d, .vec 16 1 (hexUltL x c)) :: env) s) := by
  rw [evalInstr_icmpVec (va := .vec 16 8 x) (vb := .vec 16 8 (List.replicate 16 c))
    (l1 := x) (l2 := List.replicate 16 c)
    (by simp only [withEnv, evalOperand, ha])
    (by simp only [withEnv, evalOperand, Const.toValue])
    (vecLanes_self hlen) (vecLanes_self (by simp))]
  rw [← hlen, zipReplicate_map]
  simp [withEnv, State.bind, hexUltL]

theorem b_binopVec_or1 (env : Env) (s : State) (d a b : String)
    (x y : List (BitVec 1)) (hlenx : x.length = 16) (hleny : y.length = 16)
    (ha : lookupName env a = some (.vec 16 1 x))
    (hb : lookupName env b = some (.vec 16 1 y)) :
    evalInstr escapeCalls (withEnv env s) (.binopVec d .or 16 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .vec 16 1 (hexZipOr x y)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := hexZipOr x y) hlenx hleny
    (by simp only [withEnv, evalOperand, ha])
    (by simp only [withEnv, evalOperand, hb])
    (by simpa [evalBinop, hexZipOr] using mapM_some_map (x.zip y) (fun p : BitVec 1 × BitVec 1 => p.1 ||| p.2))]
  simp only [withEnv, State.bind, hexZipOr]

theorem b_bitcastMask16 (env : Env) (s : State) (d a : String) (x : List (BitVec 1))
    (hlen : x.length = 16) (ha : lookupName env a = some (.vec 16 1 x)) :
    evalInstr escapeCalls (withEnv env s) (.bitcastMask d 16 (.reg a)) =
      some (withEnv ((d, .int 16 (BitVec.ofNat 16 (lanesToNat x))) :: env) s) := by
  rw [evalInstr_bitcastMask (hv := evalOperand_reg_of env s a _ ha) hlen]
  rfl

theorem evalBinopNat_and16 (x c : BitVec 16) :
    evalBinopNat .and 16 x.toNat c.toNat = some (x.toNat &&& c.toNat) := by
  simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.toNat_and]

theorem b_and16_imm (env : Env) (s : State) (d a : String) (x c : BitVec 16)
    (ha : lookupName env a = some (.int 16 x)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .and 16 (.reg a) (.imm (.int 16 c))) =
      some (withEnv ((d, .int 16 (x &&& c)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 16 x) ha)
    (hb := evalOperand_lit_of _ 16 c) (hr := evalBinopNat_and16 x c)]
  simp only [withEnv, State.bind]
  rw [show BitVec.ofNat 16 (x.toNat &&& c.toNat) = x &&& c from by
    rw [← BitVec.toNat_and x c, BitVec.ofNat_toNat, BitVec.setWidth_eq]]

theorem b_icmp_eq16_imm (env : Env) (s : State) (d a : String) (x c : BitVec 16)
    (ha : lookupName env a = some (.int 16 x)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d .eq 16 (.reg a) (.imm (.int 16 c))) =
      some (withEnv ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 16 x) ha)
    (hb := evalOperand_lit_of _ 16 c)]
  simp only [withEnv, State.bind]

def udIfEndI115 : Block := blockAt usDecFunction 15 (by decide)

theorem findBlock_udIfEndI115 : usDecFunction.findBlock "if.end.i115" = some udIfEndI115 := by
  decide

theorem udIfEndI115_instrs :
    udIfEndI115.instrs =
      [ .gep "%add.ptr1.i117" (.int 8) (.reg "%arrayidx16") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .load "%10" (.vec 2 (.int 64)) (.reg "%add.ptr1.i117"),
        .vecBitcast "%11" 2 64 16 8 (.reg "%10"),
        .binopVec "%sub.i169" .add 16 8 (.reg "%11") (.imm (.splat 16 8 (BitVec.ofInt 8 (-48)))),
        .binopVec "%12" .or 16 8 (.reg "%11") (.imm (.splat 16 8 (BitVec.ofInt 8 32))),
        .binopVec "%sub.i168" .add 16 8 (.reg "%12") (.imm (.splat 16 8 (BitVec.ofInt 8 (-97)))),
        .icmpVec "%cmp.i192" .ult 16 8 (.reg "%sub.i169") (.imm (.splat 16 8 (BitVec.ofInt 8 10))),
        .icmpVec "%cmp.i190" .ult 16 8 (.reg "%sub.i168") (.imm (.splat 16 8 (BitVec.ofInt 8 6))),
        .binopVec "%or.i185258259" .or 16 1 (.reg "%cmp.i192") (.reg "%cmp.i190"),
        .bitcastMask "%13" 16 (.reg "%or.i185258259"),
        .binop "%14" .and 16 (.reg "%13") (.imm (.int 16 (BitVec.ofInt 16 15))),
        .icmp "%cmp.not.i128" .eq 16 (.reg "%14") (.imm (.int 16 (BitVec.ofInt 16 15))) ] := by
  decide

theorem udIfEndI115_term :
    udIfEndI115.term = .condbr (.reg "%cmp.not.i128") "if.end3.i" "if.then22" := by decide

def udIfEndI115Env (env : Env) (addr : Nat) (bs : List UInt8) : Env :=
  let l := byteLanes bs
  let a := hexAddL l (BitVec.ofInt 8 (-48))
  let b := hexOrL l (BitVec.ofInt 8 32)
  let da := hexUltL a (BitVec.ofInt 8 10)
  let db := hexUltL (hexAddL b (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)
  let o := hexZipOr da db
  let n13 := BitVec.ofNat 16 (lanesToNat o)
  ("%cmp.not.i128", .int 1 (evalICmp .eq (n13 &&& BitVec.ofInt 16 15)
    (BitVec.ofInt 16 15))) ::
  ("%14", .int 16 (n13 &&& BitVec.ofInt 16 15)) ::
  ("%13", .int 16 n13) ::
  ("%or.i185258259", .vec 16 1 o) ::
  ("%cmp.i190", .vec 16 1 db) ::
  ("%cmp.i192", .vec 16 1 da) ::
  ("%sub.i168", .vec 16 8 (hexAddL b (BitVec.ofInt 8 (-97)))) ::
  ("%12", .vec 16 8 b) ::
  ("%sub.i169", .vec 16 8 a) ::
  ("%11", .vec 16 8 l) ::
  ("%10", .vec 2 64 (unpackLanes 64 2 (bytesToNat bs))) ::
  ("%add.ptr1.i117", .ptr (addr + 2)) :: env

theorem udIfEndI115_denote (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs) :
    denoteCode escapeCalls udIfEndI115.instrs (withEnv env s) =
      some (withEnv (udIfEndI115Env env addr bs) s) := by
  rw [udIfEndI115_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr1.i117" "%arrayidx16"
    addr 2 (BitVec.ofInt 64 2) (by ud_lk_h haddr) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (load_vec2_64 _ _ "%10" "%add.ptr1.i117"
    (addr + 2) bs (by ud_lk) hlen hload)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_vecBitcast_2_64_16_8 _ _ "%11" "%10" bs
    (by ud_lk) hlen)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_splat _ _ "%sub.i169" "%11"
    (byteLanes bs) (BitVec.ofInt 8 (-48)) (by rw [byteLanes_length]; exact hlen) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_or_splat _ _ "%12" "%11"
    (byteLanes bs) (BitVec.ofInt 8 32) (by rw [byteLanes_length]; exact hlen) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_splat _ _ "%sub.i168" "%12"
    (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97))
    (by rw [hexOrL_length, byteLanes_length]; exact hlen) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmpVec_ult_splat _ _ "%cmp.i192" "%sub.i169"
    (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10)
    (by rw [hexAddL_length, byteLanes_length]; exact hlen) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmpVec_ult_splat _ _ "%cmp.i190" "%sub.i168"
    (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
    (BitVec.ofInt 8 6)
    (by rw [hexAddL_length, hexOrL_length, byteLanes_length]; exact hlen) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_or1 _ _ "%or.i185258259" "%cmp.i192" "%cmp.i190"
    (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
    (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
      (BitVec.ofInt 8 6))
    (by rw [hexUltL_length, hexAddL_length, byteLanes_length]; exact hlen)
    (by rw [hexUltL_length, hexAddL_length, hexOrL_length, byteLanes_length]; exact hlen)
    (by ud_lk) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_bitcastMask16 _ _ "%13" "%or.i185258259"
    (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
      (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
        (BitVec.ofInt 8 6)))
    (by rw [hexZipOr_length, hexUltL_length, hexAddL_length, hexUltL_length,
        hexAddL_length, hexOrL_length, byteLanes_length, Nat.min_self]; exact hlen)
    (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and16_imm _ _ "%14" "%13"
    (BitVec.ofNat 16 (lanesToNat
      (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
          (BitVec.ofInt 8 6)))))
    (BitVec.ofInt 16 15) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq16_imm _ _ "%cmp.not.i128" "%14"
    (BitVec.ofNat 16 (lanesToNat
      (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
          (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
    (BitVec.ofInt 16 15) (by ud_lk))]
  simp only [denoteCode, withEnv, udIfEndI115Env]

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes

theorem udIfEndI115_run (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs) :
    Option.map State.mem (denoteCode escapeCalls udIfEndI115.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEndI115.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.not.i128") =
        some (.int 1 (evalICmp .eq
          (BitVec.ofNat 16 (lanesToNat
            (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
              (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
                (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
          (BitVec.ofInt 16 15))) := by
  rw [udIfEndI115_denote env s addr bs haddr hlen hload]
  refine ⟨?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udIfEndI115Env]
    ud_lk

theorem udIfEndI115_step (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (hpc : s.pc = "if.end.i115")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs)
    (hcond : evalICmp .eq
      (BitVec.ofNat 16 (lanesToNat
        (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
          (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
            (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
      (BitVec.ofInt 16 15) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndI115Env env addr bs) s) with
              pc := "if.end3.i", pre := some "if.end.i115" } := by
  rw [udStep_of (withEnv env s) "if.end.i115" udIfEndI115 _
    (by rw [withEnv]; exact hpc) findBlock_udIfEndI115
    (udIfEndI115_denote env s addr bs haddr hlen hload), udIfEndI115_term]
  have hcmp : evalOperand (withEnv (udIfEndI115Env env addr bs) s) (.reg "%cmp.not.i128") =
      some (.int 1 (evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat
          (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
              (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15))) :=
    evalOperand_reg_of _ s "%cmp.not.i128" _ (by simp only [udIfEndI115Env]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udIfEndI115_step_zero (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (hpc : s.pc = "if.end.i115")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs)
    (hcond : evalICmp .eq
      (BitVec.ofNat 16 (lanesToNat
        (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
          (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
            (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
      (BitVec.ofInt 16 15) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEndI115Env env addr bs) s) with
              pc := "if.then22", pre := some "if.end.i115" } := by
  rw [udStep_of (withEnv env s) "if.end.i115" udIfEndI115 _
    (by rw [withEnv]; exact hpc) findBlock_udIfEndI115
    (udIfEndI115_denote env s addr bs haddr hlen hload), udIfEndI115_term]
  have hcmp : evalOperand (withEnv (udIfEndI115Env env addr bs) s) (.reg "%cmp.not.i128") =
      some (.int 1 (evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat
          (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
              (BitVec.ofInt 8 6)))) &&& BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15))) :=
    evalOperand_reg_of _ s "%cmp.not.i128" _ (by simp only [udIfEndI115Env]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- info: 'LeanLLVM.Refinement.udIfEndI115_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI115_denote

/-- info: 'LeanLLVM.Refinement.udIfEndI115_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI115_run

/-- info: 'LeanLLVM.Refinement.udIfEndI115_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI115_step

/-- info: 'LeanLLVM.Refinement.udIfEndI115_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI115_step_zero

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### Axiom footprints: the escape table and its reader

`evalICmp_sgt_negone_one_iff` and `unescapeTable_test` carry
`Classical.propDecidable`, which the `split <;> omega` in the former's proof
reaches; every other declaration in this group is at `[propext]` or
`[propext, Quot.sound]`. -/

/-- info: 'LeanLLVM.Refinement.unescapeTable_getElem?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unescapeTable_getElem?

/-- info: 'LeanLLVM.Refinement.simpleEscape_getD_highBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms simpleEscape_getD_highBit

/-- info: 'LeanLLVM.Refinement.evalICmp_sgt_negone_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_sgt_negone_one_iff

/-- info: 'LeanLLVM.Refinement.unescapeTable_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unescapeTable_test

/-- info: 'LeanLLVM.Refinement.b_zext8_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_zext8_64

/-- info: 'LeanLLVM.Refinement.b_store8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store8

/-- info: 'LeanLLVM.Refinement.b_icmp_sgt8_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_sgt8_imm

/-- info: 'LeanLLVM.Refinement.findBlock_udIfEndI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEndI

/-- info: 'LeanLLVM.Refinement.findBlock_udIfThen6I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen6I

/-- info: 'LeanLLVM.Refinement.udIfEndI_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEndI_instrs

/-- info: 'LeanLLVM.Refinement.udIfEndI_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEndI_term

/-- info: 'LeanLLVM.Refinement.udIfEndI_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_denote

/-- info: 'LeanLLVM.Refinement.udIfEndI_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_run

/-- info: 'LeanLLVM.Refinement.udIfEndI_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_step

/-- info: 'LeanLLVM.Refinement.udIfEndI_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_step_zero

/-- info: 'LeanLLVM.Refinement.udIfThen6I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen6I_instrs

/-- info: 'LeanLLVM.Refinement.udIfThen6I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen6I_term

/-- info: 'LeanLLVM.Refinement.udIfThen6I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen6I_denote

/-- info: 'LeanLLVM.Refinement.udIfThen6I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen6I_step

end LeanLLVM.Refinement

set_option autoImplicit false
set_option maxRecDepth 8000
open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes

namespace LeanLLVM.Refinement

/-! ### The lane-list alignment -/

/-- `l[n]?` is the `getD` lane when the index is in range. -/
theorem getD?_eq {α : Type} {l : List α} {n : Nat} {d : α} (h : n < l.length) :
    l[n]? = some (l.getD n d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A one-bit value is zero or one. -/
theorem bv1_cases (x : BitVec 1) : x = 0 ∨ x = 1 := by
  have h := x.isLt
  have h' : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases h' with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; simpa using h0
  · right; apply BitVec.eq_of_toNat_eq; simpa using h1

/-- A lane's two emitted tests, `or`-ed, are the byte's `hexLaneTest`. -/
theorem lane_test_eq (x : BitVec 8) :
    evalICmp .ult (x + BitVec.ofInt 8 (-48)) (BitVec.ofInt 8 10) |||
      evalICmp .ult ((x ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97)) (BitVec.ofInt 8 6) =
      BitVec.ofBool (hexLaneTest x) := by
  decide +revert

/-- The digit tests, as the single map the byte list gives. -/
theorem hexLanes_digit (l : List (BitVec 8)) :
    hexUltL (hexAddL l (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10) =
      l.map (fun v => evalICmp .ult (v + BitVec.ofInt 8 (-48)) (BitVec.ofInt 8 10)) := by
  simp [hexUltL, hexAddL, List.map_map]

/-- The letter tests, as the single map the byte list gives. -/
theorem hexLanes_letter (l : List (BitVec 8)) :
    hexUltL (hexAddL (hexOrL l (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
        (BitVec.ofInt 8 6) =
      l.map (fun v => evalICmp .ult ((v ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97))
        (BitVec.ofInt 8 6)) := by
  simp [hexUltL, hexAddL, hexOrL, List.map_map]

/-- `or`-ing two lane lists of one byte list is one map. -/
theorem hexZipOr_map_map {l : List (BitVec 8)} (f g : BitVec 8 → BitVec 1) :
    hexZipOr (l.map f) (l.map g) = l.map fun x => f x ||| g x := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show (f x ||| g x) :: hexZipOr (xs.map f) (xs.map g) =
        (f x ||| g x) :: xs.map (fun x => f x ||| g x)
      rw [ih]

/-- **The lane-list alignment.**  The lane tests the hex reader emits, at the
abbreviated lane lists its own arithmetic builds, are `hexTestLanes`'s list. -/
theorem hexTestLanes_emit (l : List (BitVec 8)) :
    hexZipOr (hexUltL (hexAddL l (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL l (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97)))
          (BitVec.ofInt 8 6)) =
      hexTestLanes l := by
  rw [hexLanes_digit, hexLanes_letter, hexZipOr_map_map]
  simp only [hexTestLanes]
  apply List.map_congr_left
  intro x _
  exact lane_test_eq x

/-- The block's mask word's low nibble is the four loaded bytes' tests. -/
theorem hexLanes_low_four {bs : List UInt8} {x0 x1 x2 x3 : BitVec 8}
    {rest : List (BitVec 8)} (hl : byteLanes bs = x0 :: x1 :: x2 :: x3 :: rest) :
    lanesToNat (hexZipOr (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
          (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))) % 16 =
      (if hexLaneTest x0 then 1 else 0) + 2 * (if hexLaneTest x1 then 1 else 0) +
      4 * (if hexLaneTest x2 then 1 else 0) + 8 * (if hexLaneTest x3 then 1 else 0) := by
  rw [hexTestLanes_emit, hl, hexTest_low_four]

/-! ### Generic instruction shapes -/

theorem evalBinopNat_eq_map (op : BinOp) (w : Nat) (x y : BitVec w) :
    evalBinopNat op w x.toNat y.toNat = (evalBinop op x y).map BitVec.toNat := by
  simp [evalBinopNat, BitVec.ofNat_toNat]

/-- A constant vector operand reads as its own lane list. -/
theorem evalOperand_vector_of (s : State) (w n : Nat) (y : List (BitVec w))
    (hlen : y.length = n) :
    evalOperand s (.imm (.vector w y)) = some (.vec n w y) := by
  simp only [evalOperand, Const.toValue, hlen]

/-- `%d = op iw %a, <c>`. -/
theorem b_binop_imm (env : Env) (s : State) (d a : String) (op : BinOp) (w : Nat)
    (x c r : BitVec w) (hr : evalBinop op x c = some r)
    (ha : lookupName env a = some (.int w x)) :
    evalInstr escapeCalls (withEnv env s) (.binop d op w (.reg a) (.imm (.int w c))) =
      some (withEnv ((d, .int w r) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of _ w c)
    (hr := by rw [evalBinopNat_eq_map, hr]; rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = op iw %a, %b`. -/
theorem b_binop_reg (env : Env) (s : State) (d a b : String) (op : BinOp) (w : Nat)
    (x y r : BitVec w) (hr : evalBinop op x y = some r)
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr escapeCalls (withEnv env s) (.binop d op w (.reg a) (.reg b)) =
      some (withEnv ((d, .int w r) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb)
    (hr := by rw [evalBinopNat_eq_map, hr]; rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = icmp p iw %a, <c>`. -/
theorem b_icmp_imm (env : Env) (s : State) (d a : String) (p : IPred) (w : Nat)
    (x c : BitVec w) (ha : lookupName env a = some (.int w x)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d p w (.reg a) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (evalICmp p x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of _ w c)]
  simp only [withEnv, State.bind, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = icmp p iw %a, %b`. -/
theorem b_icmp_reg (env : Env) (s : State) (d a b : String) (p : IPred) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d p w (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (evalICmp p x y)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb)]
  simp only [withEnv, State.bind, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A scalar select whose condition register holds `cb`. -/
theorem b_select_reg (env : Env) (s : State) (d c a b : String) (ty : Ty)
    (cb : BitVec 1) (va vb : Value)
    (hc : lookupName env c = some (.int 1 cb))
    (ha : lookupName env a = some va) (hb : lookupName env b = some vb) :
    evalInstr escapeCalls (withEnv env s) (.select d ty (.reg c) (.reg a) (.reg b)) =
      some (withEnv ((d, if cb = (1 : BitVec 1) then va else vb) :: env) s) := by
  rw [evalInstr, show (evalOperand (withEnv env s) (.reg c)) = some (.int 1 cb) from hc,
    show (evalOperand (withEnv env s) (.reg a)) = some va from ha,
    show (evalOperand (withEnv env s) (.reg b)) = some vb from hb]
  rcases bv1_cases cb with h | h <;> simp [h, withEnv, State.bind]

/-- A lane read out of a vector register. -/
theorem b_extract_lane (env : Env) (s : State) (d a : String) (n w wi : Nat)
    (x : List (BitVec w)) (k : BitVec wi) (v : BitVec w) (hlen : x.length = n)
    (ha : lookupName env a = some (.vec n w x)) (hk : x[k.toNat]? = some v) :
    evalInstr escapeCalls (withEnv env s) (.extractelement d n w (.reg a) (.imm (.int wi k))) =
      some (withEnv ((d, .int w v) :: env) s) := by
  rw [evalInstr_extractelement (hv := evalOperand_reg_of env s a _ ha)
    (hl := vecLanes_self hlen) (hi := evalOperand_lit_of _ wi k) (hx := hk)]
  simp only [withEnv, State.bind]

/-- The lanes a lane-wise `and` of a constant vector binds. -/
theorem b_binopVec_and_vec (env : Env) (s : State) (d a : String) (n w : Nat)
    (x y : List (BitVec w)) (hlenx : x.length = n) (hleny : y.length = n)
    (ha : lookupName env a = some (.vec n w x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binopVec d .and n w (.reg a) (.imm (.vector w y))) =
      some (withEnv ((d, .vec n w ((x.zip y).map fun p => p.1 &&& p.2)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := (x.zip y).map fun p => p.1 &&& p.2)
    hlenx hleny
    (evalOperand_reg_of env s a (.vec n w x) ha)
    (evalOperand_vector_of (withEnv env s) w n y hleny)
    (by simpa [evalBinop] using
      mapM_some_map (x.zip y) (fun p : BitVec w × BitVec w => p.1 &&& p.2))]
  simp only [withEnv, State.bind]

/-- A lane-wise `add` of two vector registers. -/
theorem b_binopVec_add_reg (env : Env) (s : State) (d a b : String) (n w : Nat)
    (x y : List (BitVec w)) (hlenx : x.length = n) (hleny : y.length = n)
    (ha : lookupName env a = some (.vec n w x))
    (hb : lookupName env b = some (.vec n w y)) :
    evalInstr escapeCalls (withEnv env s) (.binopVec d .add n w (.reg a) (.reg b)) =
      some (withEnv ((d, .vec n w ((x.zip y).map fun p => p.1 + p.2)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := (x.zip y).map fun p => p.1 + p.2)
    hlenx hleny
    (evalOperand_reg_of env s a (.vec n w x) ha)
    (evalOperand_reg_of env s b (.vec n w y) hb)
    (by simpa [evalBinop] using
      mapM_some_map (x.zip y) (fun p : BitVec w × BitVec w => p.1 + p.2))]
  simp only [withEnv, State.bind]

/-- A lane-wise select of two constant vectors at a mask register. -/
theorem b_select_vec (env : Env) (s : State) (d c : String)
    (cs : List (BitVec 1)) (a b : List (BitVec 8))
    (hlen : cs.length = 16) (hlena : a.length = 16) (hlenb : b.length = 16)
    (hc : lookupName env c = some (.vec 16 1 cs)) :
    evalInstr escapeCalls (withEnv env s)
        (.select d (.vec 16 (.int 8)) (.reg c) (.imm (.vector 8 a)) (.imm (.vector 8 b))) =
      some (withEnv ((d, .vec 16 8 (selectLanes cs a b)) :: env) s) := by
  rw [evalInstr,
    show evalOperand (withEnv env s) (.reg c) = some (.vec 16 1 cs) from hc,
    show evalOperand (withEnv env s) (.imm (.vector 8 a)) = some (.vec 16 8 a) from
      evalOperand_vector_of (withEnv env s) 8 16 a hlena,
    show evalOperand (withEnv env s) (.imm (.vector 8 b)) = some (.vec 16 8 b) from
      evalOperand_vector_of (withEnv env s) 8 16 b hlenb]
  simp only [withEnv, State.bind, hlen, vecLanes_self hlena, vecLanes_self hlenb, reduceIte]

/-- The unsigned byte multiply-add at the body's two operands. -/
theorem b_call_pmaddUbSw (env : Env) (s : State) (d a : String) (b : Operand)
    (x y : List (BitVec 8))
    (ha : lookupName env a = some (.vec 16 8 x))
    (hb : evalOperand (withEnv env s) b = some (.vec 16 8 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.vec 8 (.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128"
          [(.vec 16 (.int 8), .reg a), (.vec 16 (.int 8), b)]) =
      some (withEnv ((d, .vec 8 16 (pmaddUbSw x y)) :: env) s) := by
  rw [evalInstr_call (s := withEnv env s) (ty := .vec 8 (.int 16))
    (ha := evalOperands_cons (evalOperand_reg_of env s a (.vec 16 8 x) ha)
      (evalOperands_cons hb (by rfl)))
    (hc := escapeCalls_pmaddUbSw x y s.mem s.next)]
  simp only [withEnv, State.bind]

/-- The signed word multiply-add at the body's two operands. -/
theorem b_call_pmaddWd (env : Env) (s : State) (d a : String) (b : Operand)
    (x y : List (BitVec 16))
    (ha : lookupName env a = some (.vec 8 16 x))
    (hb : evalOperand (withEnv env s) b = some (.vec 8 16 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.vec 4 (.int 32)) "llvm.x86.sse2.pmadd.wd"
          [(.vec 8 (.int 16), .reg a), (.vec 8 (.int 16), b)]) =
      some (withEnv ((d, .vec 4 32 (pmaddWd x y)) :: env) s) := by
  rw [evalInstr_call (s := withEnv env s) (ty := .vec 4 (.int 32))
    (ha := evalOperands_cons (evalOperand_reg_of env s a (.vec 8 16 x) ha)
      (evalOperands_cons hb (by rfl)))
    (hc := escapeCalls_pmaddWd x y s.mem s.next)]
  simp only [withEnv, State.bind]

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### The hex reader's guard shapes -/

macro "hex_lk" : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | (rw [lookupName_cons_self]; rfl) | rfl)))

macro "hex_lk_h " h:term : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | (rw [lookupName_cons_self]; rfl) | exact $h)))

theorem selectLanes_length {w : Nat} (cs : List (BitVec 1)) (a b : List (BitVec w)) :
    (selectLanes cs a b).length = min cs.length (min a.length b.length) := by
  simp [selectLanes, List.length_map, List.length_zip]

/-- A `<16 x i8>` load at sixteen readable bytes. -/
theorem load_vec16_8 (env : Env) (s : State) (d p : String) (addr : Nat) (bs : List UInt8)
    (hp : lookupName env p = some (.ptr addr))
    (hr : readBytes s.mem addr 16 = some bs) :
    evalInstr escapeCalls (withEnv env s) (.load d (.vec 16 (.int 8)) (.reg p)) =
      some (withEnv ((d, .vec 16 8 (byteLanes bs)) :: env) s) := by
  exact evalInstr_load (s := withEnv env s) (d := d) (ty := .vec 16 (.int 8))
    (p := .reg p) (a := addr) (v := .vec 16 8 (byteLanes bs))
    (evalOperand_reg_of env s p (.ptr addr) hp) (loadValue_vec_i8 (n := 16) hr)

/-- The `%17` mask's lanes: fifteen for the four low lanes and zero after. -/
def hxLowMask : List (BitVec 8) :=
  [BitVec.ofInt 8 15, BitVec.ofInt 8 15, BitVec.ofInt 8 15, BitVec.ofInt 8 15,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0]

/-- The `%18` select's true arm: nine in the four low lanes. -/
def hxNine : List (BitVec 8) :=
  [BitVec.ofInt 8 9, BitVec.ofInt 8 9, BitVec.ofInt 8 9, BitVec.ofInt 8 9,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0]

/-- The `%18` select's false arm. -/
def hxZero : List (BitVec 8) :=
  [BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0]

/-- `%17`: the loaded bytes' low nibbles. -/
def hxLow (l : List (BitVec 8)) : List (BitVec 8) :=
  (l.zip hxLowMask).map fun p => p.1 &&& p.2

/-- `%18`: nine wherever the letter test holds. -/
def hxNineSel (c : List (BitVec 1)) : List (BitVec 8) := selectLanes c hxNine hxZero

/-- `%add.i202`: each low nibble with its nine. -/
def hxPadd (l : List (BitVec 8)) (c : List (BitVec 1)) : List (BitVec 8) :=
  ((hxNineSel c).zip (hxLow l)).map fun p => p.1 + p.2

/-- `%vecext.i207`: the multiply-add chain's lane 0, the code unit. -/
def hxCode (l : List (BitVec 8)) (c : List (BitVec 1)) : BitVec 32 :=
  (pmaddWd (pmaddUbSw (hxPadd l c) hexW8) hexW16).getD 0 0

/-! ### `if.end3.i`

The guard the hex reader falls through to: the code unit's high bits at
`0xD800`, room for twelve more bytes, and the two trailing bytes `\` and `u`. -/

def udIfEnd3I : Block := blockAt usDecFunction 16 (by decide)

theorem findBlock_udIfEnd3I :
    usDecFunction.findBlock "if.end3.i" = some udIfEnd3I := by decide

theorem udIfEnd3I_instrs :
    udIfEnd3I.instrs =
      [ .vecBitcast "%bc318" 2 64 16 8 (.reg "%10"),
        .extractelement "%15" 16 8 (.reg "%bc318") (.imm (.int 64 (BitVec.ofInt 64 5))),
        .vecBitcast "%bc" 2 64 16 8 (.reg "%10"),
        .extractelement "%16" 16 8 (.reg "%bc") (.imm (.int 64 (BitVec.ofInt 64 4))),
        .binopVec "%17" .and 16 8 (.reg "%11") (.imm (.vector 8 hxLowMask)),
        .select "%18" (.vec 16 (.int 8)) (.reg "%cmp.i190")
          (.imm (.vector 8 hxNine)) (.imm (.vector 8 hxZero)),
        .binopVec "%add.i202" .add 16 8 (.reg "%18") (.reg "%17"),
        .call "%19" (.vec 8 (.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128"
          [(.vec 16 (.int 8), .reg "%add.i202"), (.vec 16 (.int 8), .imm (.vector 8 hexW8))],
        .call "%20" (.vec 4 (.int 32)) "llvm.x86.sse2.pmadd.wd"
          [(.vec 8 (.int 16), .reg "%19"), (.vec 8 (.int 16), .imm (.vector 16 hexW16))],
        .extractelement "%vecext.i207" 4 32 (.reg "%20") (.imm (.int 64 (BitVec.ofInt 64 0))),
        .binop "%and27.i" .and 32 (.reg "%vecext.i207")
          (.imm (.int 32 (BitVec.ofInt 32 65535))),
        .binop "%21" .and 32 (.reg "%vecext.i207")
          (.imm (.int 32 (BitVec.ofInt 32 64512))),
        .icmp "%cmp4.i118" .eq 32 (.reg "%21") (.imm (.int 32 (BitVec.ofInt 32 55296))),
        .binop "%add5.i" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 12))),
        .icmp "%cmp6.not.i" .ule 64 (.reg "%add5.i") (.reg "%n"),
        .binop "%or.cond.i.not336" .and 1 (.reg "%cmp6.not.i") (.reg "%cmp4.i118"),
        .icmp "%cmp9.i" .eq 8 (.reg "%16") (.imm (.int 8 (BitVec.ofInt 8 92))),
        .binop "%or.cond" .and 1 (.reg "%or.cond.i.not336") (.reg "%cmp9.i"),
        .icmp "%cmp15.i" .eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofInt 8 117))),
        .binop "%or.cond334" .and 1 (.reg "%or.cond") (.reg "%cmp15.i") ] := by
  decide

theorem udIfEnd3I_term :
    udIfEnd3I.term = .condbr (.reg "%or.cond334") "if.then17.i" "if.end32.i" := by decide

/-- The block's branch value: the code unit's high bits, twelve bytes of room, and
the two trailing bytes. -/
def udIfEnd3IGuard (bs : List UInt8) (c : List (BitVec 1)) (sub n : BitVec 64) : BitVec 1 :=
  (((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
    (evalICmp .eq (hxCode (byteLanes bs) c &&& BitVec.ofInt 32 64512)
      (BitVec.ofInt 32 55296))) &&&
    (evalICmp .eq ((byteLanes bs).getD 4 0) (BitVec.ofInt 8 92))) &&&
    (evalICmp .eq ((byteLanes bs).getD 5 0) (BitVec.ofInt 8 117))

/-- The cells the block binds, at the lane lists its own arithmetic produces. -/
def udIfEnd3IEnv (env : Env) (bs : List UInt8) (c : List (BitVec 1))
    (sub n : BitVec 64) : Env :=
  let l := byteLanes bs
  let cp := hxCode l c
  let hi := cp &&& BitVec.ofInt 32 64512
  let h4 := evalICmp .eq hi (BitVec.ofInt 32 55296)
  let h6 := evalICmp .ule (sub + BitVec.ofInt 64 12) n
  let h9 := evalICmp .eq (l.getD 4 0) (BitVec.ofInt 8 92)
  let h15 := evalICmp .eq (l.getD 5 0) (BitVec.ofInt 8 117)
  let hb := h6 &&& h4
  let hc := hb &&& h9
  ("%or.cond334", .int 1 (hc &&& h15)) ::
    ("%cmp15.i", .int 1 h15) ::
    ("%or.cond", .int 1 hc) ::
    ("%cmp9.i", .int 1 h9) ::
    ("%or.cond.i.not336", .int 1 hb) ::
    ("%cmp6.not.i", .int 1 h6) ::
    ("%add5.i", .int 64 (sub + BitVec.ofInt 64 12)) ::
    ("%cmp4.i118", .int 1 h4) ::
    ("%21", .int 32 hi) ::
    ("%and27.i", .int 32 (cp &&& BitVec.ofInt 32 65535)) ::
    ("%vecext.i207", .int 32 cp) ::
    ("%20", .vec 4 32 (pmaddWd (pmaddUbSw (hxPadd l c) hexW8) hexW16)) ::
    ("%19", .vec 8 16 (pmaddUbSw (hxPadd l c) hexW8)) ::
    ("%add.i202", .vec 16 8 (hxPadd l c)) ::
    ("%18", .vec 16 8 (hxNineSel c)) ::
    ("%17", .vec 16 8 (hxLow l)) ::
    ("%16", .int 8 (l.getD 4 0)) ::
    ("%bc", .vec 16 8 l) ::
    ("%15", .int 8 (l.getD 5 0)) ::
    ("%bc318", .vec 16 8 l) :: env

theorem udIfEnd3I_denote (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (c : List (BitVec 1)) (sub n : BitVec 64)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (h10 : lookupName env "%10" = some (.vec 2 64 (unpackLanes 64 2 (bytesToNat bs))))
    (h11 : lookupName env "%11" = some (.vec 16 8 (byteLanes bs)))
    (hc190 : lookupName env "%cmp.i190" = some (.vec 16 1 c))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hlen : bs.length = 16) (hc16 : c.length = 16) :
    denoteCode escapeCalls udIfEnd3I.instrs (withEnv env s) =
      some (withEnv (udIfEnd3IEnv env bs c sub n) s) := by
  let l : List (BitVec 8) := byteLanes bs
  have hl : l.length = 16 := by simp only [l, byteLanes, List.length_map, hlen]
  have hmask : hxLowMask.length = 16 := by decide
  have hnine : hxNine.length = 16 := by decide
  have hzero : hxZero.length = 16 := by decide
  have hu16 : hexW8.length = 16 := by decide
  have hw8 : hexW16.length = 8 := by decide
  have hlow16 : (hxLow l).length = 16 := by
    simp [hxLow, hl, hmask]
  have hsel16 : (hxNineSel c).length = 16 := by
    simp [hxNineSel, selectLanes_length, hc16, hnine, hzero]
  have hp16 : (hxPadd l c).length = 16 := by
    simp [hxPadd, hsel16, hlow16]
  have hub8 : (pmaddUbSw (hxPadd l c) hexW8).length = 8 :=
    pmaddUbSw_length_sixteen hp16 hu16
  have hwd4 : (pmaddWd (pmaddUbSw (hxPadd l c) hexW8) hexW16).length = 4 :=
    pmaddWd_length_eight hub8 hw8
  rw [udIfEnd3I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_vecBitcast_2_64_16_8 _ _ "%bc318" "%10" bs
    (by hex_lk_h h10) hlen)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_extract_lane _ _ "%15" "%bc318" 16 8 64
    l (BitVec.ofInt 64 5) (l.getD 5 0) hl (by hex_lk)
    (getD?_eq (by rw [hl]; decide)))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_vecBitcast_2_64_16_8 _ _ "%bc" "%10" bs
    (by hex_lk_h h10) hlen)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_extract_lane _ _ "%16" "%bc" 16 8 64
    l (BitVec.ofInt 64 4) (l.getD 4 0) hl (by hex_lk)
    (getD?_eq (by rw [hl]; decide)))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_and_vec _ _ "%17" "%11" 16 8
    l hxLowMask hl hmask (by hex_lk_h h11))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_vec _ _ "%18" "%cmp.i190"
    c hxNine hxZero hc16 hnine hzero (by hex_lk_h hc190))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_reg _ _ "%add.i202" "%18" "%17"
    16 8 (hxNineSel c) (hxLow l) hsel16 hlow16 (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_pmaddUbSw _ _ "%19" "%add.i202"
    (.imm (.vector 8 hexW8)) (hxPadd l c) hexW8 (by hex_lk)
    (by simp [evalOperand, Const.toValue, hu16]))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_pmaddWd _ _ "%20" "%19"
    (.imm (.vector 16 hexW16)) (pmaddUbSw (hxPadd l c) hexW8) hexW16 (by hex_lk)
    (by simp [evalOperand, Const.toValue, hw8]))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_extract_lane _ _ "%vecext.i207" "%20" 4 32 64
    (pmaddWd (pmaddUbSw (hxPadd l c) hexW8) hexW16) (BitVec.ofInt 64 0)
    ((pmaddWd (pmaddUbSw (hxPadd l c) hexW8) hexW16).getD 0 0) hwd4 (by hex_lk)
    (getD?_eq (by rw [hwd4]; decide)))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%and27.i" "%vecext.i207" .and 32
    (hxCode l c) (BitVec.ofInt 32 65535) ((hxCode l c) &&& BitVec.ofInt 32 65535) rfl
    (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%21" "%vecext.i207" .and 32
    (hxCode l c) (BitVec.ofInt 32 64512) ((hxCode l c) &&& BitVec.ofInt 32 64512) rfl
    (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp4.i118" "%21" .eq 32
    ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%add5.i" "%sub" .add 64
    sub (BitVec.ofInt 64 12) (sub + BitVec.ofInt 64 12) rfl (by hex_lk_h hsub))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_reg _ _ "%cmp6.not.i" "%add5.i" "%n" .ule 64
    (sub + BitVec.ofInt 64 12) n (by hex_lk) (by hex_lk_h hn))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or.cond.i.not336"
    "%cmp6.not.i" "%cmp4.i118" .and 1
    (evalICmp .ule (sub + BitVec.ofInt 64 12) n)
    (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296))
    ((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
      (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296)))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp9.i" "%16" .eq 8
    (l.getD 4 0) (BitVec.ofInt 8 92) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or.cond"
    "%or.cond.i.not336" "%cmp9.i" .and 1
    ((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
      (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296)))
    (evalICmp .eq (l.getD 4 0) (BitVec.ofInt 8 92))
    (((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
      (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296))) &&&
      (evalICmp .eq (l.getD 4 0) (BitVec.ofInt 8 92)))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp15.i" "%15" .eq 8
    (l.getD 5 0) (BitVec.ofInt 8 117) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or.cond334"
    "%or.cond" "%cmp15.i" .and 1
    (((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
      (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296))) &&&
      (evalICmp .eq (l.getD 4 0) (BitVec.ofInt 8 92)))
    (evalICmp .eq (l.getD 5 0) (BitVec.ofInt 8 117))
    ((((evalICmp .ule (sub + BitVec.ofInt 64 12) n) &&&
      (evalICmp .eq ((hxCode l c) &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296))) &&&
      (evalICmp .eq (l.getD 4 0) (BitVec.ofInt 8 92))) &&&
      (evalICmp .eq (l.getD 5 0) (BitVec.ofInt 8 117)))
    rfl (by hex_lk) (by hex_lk))]
  simp only [denoteCode, withEnv, udIfEnd3IEnv, udIfEnd3IGuard]
  try rfl

theorem udIfEnd3I_run (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (c : List (BitVec 1)) (sub n : BitVec 64)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (h10 : lookupName env "%10" = some (.vec 2 64 (unpackLanes 64 2 (bytesToNat bs))))
    (h11 : lookupName env "%11" = some (.vec 16 8 (byteLanes bs)))
    (hc190 : lookupName env "%cmp.i190" = some (.vec 16 1 c))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hlen : bs.length = 16) (hc16 : c.length = 16) :
    Option.map State.mem (denoteCode escapeCalls udIfEnd3I.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEnd3I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%and27.i") =
        some (.int 32 (hxCode (byteLanes bs) c &&& BitVec.ofInt 32 65535)) ∧
      (denoteCode escapeCalls udIfEnd3I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%or.cond334") =
        some (.int 1 (udIfEnd3IGuard bs c sub n)) := by
  rw [udIfEnd3I_denote env s addr bs c sub n haddr h10 h11 hc190 hsub hn hlen hc16]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udIfEnd3IEnv]
    hex_lk
  · simp only [Option.bind_some, withEnv, udIfEnd3IEnv]
    hex_lk

theorem udIfEnd3I_step (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (c : List (BitVec 1)) (sub n : BitVec 64)
    (hpc : s.pc = "if.end3.i")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (h10 : lookupName env "%10" = some (.vec 2 64 (unpackLanes 64 2 (bytesToNat bs))))
    (h11 : lookupName env "%11" = some (.vec 16 8 (byteLanes bs)))
    (hc190 : lookupName env "%cmp.i190" = some (.vec 16 1 c))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hlen : bs.length = 16) (hc16 : c.length = 16)
    (hcond : udIfEnd3IGuard bs c sub n = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd3IEnv env bs c sub n) s) with
              pc := "if.then17.i", pre := some "if.end3.i" } := by
  rw [udStep_of (withEnv env s) "if.end3.i" udIfEnd3I _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd3I
    (udIfEnd3I_denote env s addr bs c sub n haddr h10 h11 hc190 hsub hn hlen hc16),
    udIfEnd3I_term]
  have hcmp : evalOperand (withEnv (udIfEnd3IEnv env bs c sub n) s)
      (.reg "%or.cond334") =
      some (.int 1 (udIfEnd3IGuard bs c sub n)) :=
    evalOperand_reg_of _ s "%or.cond334" _ (by simp only [udIfEnd3IEnv]; hex_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### `if.then17.i`

The four lane tests at the second half of the escape's bytes: the same three
arithmetic steps and two compares `if.end.i115` makes, then the mask word. -/

def udIfThen17I : Block := blockAt usDecFunction 17 (by decide)

theorem findBlock_udIfThen17I :
    usDecFunction.findBlock "if.then17.i" = some udIfThen17I := by decide

theorem udIfThen17I_instrs :
    udIfThen17I.instrs =
      [ .gep "%add.ptr19.i" (.int 8) (.reg "%arrayidx16")
          (.imm (.int 64 (BitVec.ofInt 64 8))),
        .load "%22" (.vec 16 (.int 8)) (.reg "%add.ptr19.i"),
        .binopVec "%sub.i167" .add 16 8 (.reg "%22")
          (.imm (.splat 16 8 (BitVec.ofInt 8 (-48)))),
        .binopVec "%23" .or 16 8 (.reg "%22") (.imm (.splat 16 8 (BitVec.ofInt 8 32))),
        .binopVec "%sub.i166" .add 16 8 (.reg "%23")
          (.imm (.splat 16 8 (BitVec.ofInt 8 (-97)))),
        .icmpVec "%cmp.i188" .ult 16 8 (.reg "%sub.i167")
          (.imm (.splat 16 8 (BitVec.ofInt 8 10))),
        .icmpVec "%cmp.i187" .ult 16 8 (.reg "%sub.i166")
          (.imm (.splat 16 8 (BitVec.ofInt 8 6))),
        .binopVec "%or.i260261" .or 16 1 (.reg "%cmp.i188") (.reg "%cmp.i187"),
        .bitcastMask "%24" 16 (.reg "%or.i260261"),
        .binop "%25" .and 16 (.reg "%24") (.imm (.int 16 (BitVec.ofInt 16 15))),
        .icmp "%cmp.not.i150" .eq 16 (.reg "%25") (.imm (.int 16 (BitVec.ofInt 16 15))) ] := by
  decide

theorem udIfThen17I_term :
    udIfThen17I.term = .condbr (.reg "%cmp.not.i150") "land.lhs.true22.i" "if.end32.i" := by
  decide

def udIfThen17IEnv (env : Env) (addr : Nat) (bs : List UInt8) : Env :=
  let l := byteLanes bs
  let a := hexAddL l (BitVec.ofInt 8 (-48))
  let b := hexOrL l (BitVec.ofInt 8 32)
  let c := hexAddL b (BitVec.ofInt 8 (-97))
  let da := hexUltL a (BitVec.ofInt 8 10)
  let db := hexUltL c (BitVec.ofInt 8 6)
  let o := hexZipOr da db
  let n := BitVec.ofNat 16 (lanesToNat o)
  ("%cmp.not.i150",
      .int 1 (evalICmp .eq (n &&& BitVec.ofInt 16 15) (BitVec.ofInt 16 15))) ::
    ("%25", .int 16 (n &&& BitVec.ofInt 16 15)) ::
    ("%24", .int 16 n) ::
    ("%or.i260261", .vec 16 1 o) ::
    ("%cmp.i187", .vec 16 1 db) ::
    ("%cmp.i188", .vec 16 1 da) ::
    ("%sub.i166", .vec 16 8 c) ::
    ("%23", .vec 16 8 b) ::
    ("%sub.i167", .vec 16 8 a) ::
    ("%22", .vec 16 8 l) ::
    ("%add.ptr19.i", .ptr (addr + 8)) :: env

theorem udIfThen17I_denote (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 8) 16 = some bs) :
    denoteCode escapeCalls udIfThen17I.instrs (withEnv env s) =
      some (withEnv (udIfThen17IEnv env addr bs) s) := by
  let l : List (BitVec 8) := byteLanes bs
  let a : List (BitVec 8) := hexAddL l (BitVec.ofInt 8 (-48))
  let b : List (BitVec 8) := hexOrL l (BitVec.ofInt 8 32)
  let c : List (BitVec 8) := hexAddL b (BitVec.ofInt 8 (-97))
  let da : List (BitVec 1) := hexUltL a (BitVec.ofInt 8 10)
  let db : List (BitVec 1) := hexUltL c (BitVec.ofInt 8 6)
  let o : List (BitVec 1) := hexZipOr da db
  have hl : l.length = 16 := by
    simp only [l, byteLanes, List.length_map, hlen]
  have ha16 : a.length = 16 := by simp only [a, hexAddL, List.length_map, hl]
  have hb16 : b.length = 16 := by simp only [b, hexOrL, List.length_map, hl]
  have hc16 : c.length = 16 := by simp only [c, hexAddL, List.length_map, hb16]
  have hda16 : da.length = 16 := by simp only [da, hexUltL, List.length_map, ha16]
  have hdb16 : db.length = 16 := by simp only [db, hexUltL, List.length_map, hc16]
  have ho16 : o.length = 16 := by
    simp only [o, hexZipOr, List.length_map, List.length_zip, hda16, hdb16, Nat.min_self]
  rw [udIfThen17I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%add.ptr19.i" "%arrayidx16"
    addr 8 (BitVec.ofInt 64 8) (by hex_lk_h haddr) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (load_vec16_8 _ _ "%22" "%add.ptr19.i"
    (addr + 8) bs (by hex_lk) hload)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_splat _ _ "%sub.i167" "%22"
    l (BitVec.ofInt 8 (-48)) hl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_or_splat _ _ "%23" "%22"
    l (BitVec.ofInt 8 32) hl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_splat _ _ "%sub.i166" "%23"
    b (BitVec.ofInt 8 (-97)) hb16 (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmpVec_ult_splat _ _ "%cmp.i188" "%sub.i167"
    a (BitVec.ofInt 8 10) ha16 (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmpVec_ult_splat _ _ "%cmp.i187" "%sub.i166"
    c (BitVec.ofInt 8 6) hc16 (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_or1 _ _ "%or.i260261" "%cmp.i188"
    "%cmp.i187" da db hda16 hdb16 (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_bitcastMask16 _ _ "%24" "%or.i260261"
    o ho16 (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and16_imm _ _ "%25" "%24"
    (BitVec.ofNat 16 (lanesToNat o)) (BitVec.ofInt 16 15) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq16_imm _ _ "%cmp.not.i150" "%25"
    (BitVec.ofNat 16 (lanesToNat o) &&& BitVec.ofInt 16 15) (BitVec.ofInt 16 15)
    (by hex_lk))]
  simp only [denoteCode, withEnv, udIfThen17IEnv]
  try rfl

theorem udIfThen17I_run (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 8) 16 = some bs) :
    Option.map State.mem (denoteCode escapeCalls udIfThen17I.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfThen17I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%22") = some (.vec 16 8 (byteLanes bs)) ∧
      (denoteCode escapeCalls udIfThen17I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.i187") =
        some (.vec 16 1
          (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
            (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))) ∧
      (denoteCode escapeCalls udIfThen17I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.not.i150") =
        some (.int 1 (evalICmp .eq
          (BitVec.ofNat 16 (lanesToNat (hexZipOr
              (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
                (BitVec.ofInt 8 10))
              (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
                (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
            BitVec.ofInt 16 15)
          (BitVec.ofInt 16 15))) := by
  rw [udIfThen17I_denote env s addr bs haddr hlen hload]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udIfThen17IEnv] <;> hex_lk)

theorem udIfThen17I_step (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (hpc : s.pc = "if.then17.i")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 8) 16 = some bs)
    (hcond : evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat (hexZipOr
            (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
              (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
              (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
          BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfThen17IEnv env addr bs) s) with
              pc := "land.lhs.true22.i", pre := some "if.then17.i" } := by
  rw [udStep_of (withEnv env s) "if.then17.i" udIfThen17I _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen17I
    (udIfThen17I_denote env s addr bs haddr hlen hload), udIfThen17I_term]
  have hcmp : evalOperand (withEnv (udIfThen17IEnv env addr bs) s)
      (.reg "%cmp.not.i150") =
      some (.int 1 (evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat (hexZipOr
            (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
              (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
              (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
          BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15))) :=
    evalOperand_reg_of _ s "%cmp.not.i150" _ (by simp only [udIfThen17IEnv]; hex_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udIfThen17I_step_zero (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (hpc : s.pc = "if.then17.i")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 8) 16 = some bs)
    (hcond : evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat (hexZipOr
            (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
              (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
              (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
          BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfThen17IEnv env addr bs) s) with
              pc := "if.end32.i", pre := some "if.then17.i" } := by
  rw [udStep_of (withEnv env s) "if.then17.i" udIfThen17I _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen17I
    (udIfThen17I_denote env s addr bs haddr hlen hload), udIfThen17I_term]
  have hcmp : evalOperand (withEnv (udIfThen17IEnv env addr bs) s)
      (.reg "%cmp.not.i150") =
      some (.int 1 (evalICmp .eq
        (BitVec.ofNat 16 (lanesToNat (hexZipOr
            (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48)))
              (BitVec.ofInt 8 10))
            (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
              (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
          BitVec.ofInt 16 15)
        (BitVec.ofInt 16 15))) :=
    evalOperand_reg_of _ s "%cmp.not.i150" _ (by simp only [udIfThen17IEnv]; hex_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `land.lhs.true22.i`

The low nibbles of the second half's bytes, nine where the letter test holds, and
the two multiply-adds' lane 0 read as a surrogate's low ten bits. -/

def udLandLhsTrue22I : Block := blockAt usDecFunction 18 (by decide)

theorem findBlock_udLandLhsTrue22I :
    usDecFunction.findBlock "land.lhs.true22.i" = some udLandLhsTrue22I := by decide

theorem udLandLhsTrue22I_instrs :
    udLandLhsTrue22I.instrs =
      [ .binopVec "%26" .and 16 8 (.reg "%22") (.imm (.vector 8 hxLowMask)),
        .select "%27" (.vec 16 (.int 8)) (.reg "%cmp.i187")
          (.imm (.vector 8 hxNine)) (.imm (.vector 8 hxZero)),
        .binopVec "%add.i201" .add 16 8 (.reg "%27") (.reg "%26"),
        .call "%28" (.vec 8 (.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128"
          [(.vec 16 (.int 8), .reg "%add.i201"), (.vec 16 (.int 8), .imm (.vector 8 hexW8))],
        .call "%29" (.vec 4 (.int 32)) "llvm.x86.sse2.pmadd.wd"
          [(.vec 8 (.int 16), .reg "%28"), (.vec 8 (.int 16), .imm (.vector 16 hexW16))],
        .extractelement "%vecext.i" 4 32 (.reg "%29") (.imm (.int 64 (BitVec.ofInt 64 0))),
        .binop "%and27.i164" .and 32 (.reg "%vecext.i")
          (.imm (.int 32 (BitVec.ofInt 32 65535))),
        .binop "%sub23.i" .add 32 (.reg "%and27.i164")
          (.imm (.int 32 (BitVec.ofInt 32 (-56320)))),
        .icmp "%cmp24.i" .ult 32 (.reg "%sub23.i")
          (.imm (.int 32 (BitVec.ofInt 32 1024))) ] := by
  decide

theorem udLandLhsTrue22I_term :
    udLandLhsTrue22I.term = .condbr (.reg "%cmp24.i") "if.then26.i" "if.end32.i" := by
  decide

def udLandLhsTrue22IEnv (env : Env) (bs : List UInt8) (cl : List (BitVec 1)) : Env :=
  let l := byteLanes bs
  let cp := hxCode l cl
  let a27 := cp &&& BitVec.ofInt 32 65535
  let s23 := a27 + BitVec.ofInt 32 (-56320)
  ("%cmp24.i", .int 1 (evalICmp .ult s23 (BitVec.ofInt 32 1024))) ::
    ("%sub23.i", .int 32 s23) ::
    ("%and27.i164", .int 32 a27) ::
    ("%vecext.i", .int 32 cp) ::
    ("%29", .vec 4 32 (pmaddWd (pmaddUbSw (hxPadd l cl) hexW8) hexW16)) ::
    ("%28", .vec 8 16 (pmaddUbSw (hxPadd l cl) hexW8)) ::
    ("%add.i201", .vec 16 8 (hxPadd l cl)) ::
    ("%27", .vec 16 8 (hxNineSel cl)) ::
    ("%26", .vec 16 8 (hxLow l)) :: env

theorem udLandLhsTrue22I_denote (env : Env) (s : State) (bs : List UInt8)
    (cl : List (BitVec 1))
    (h22 : lookupName env "%22" = some (.vec 16 8 (byteLanes bs)))
    (hc187 : lookupName env "%cmp.i187" = some (.vec 16 1 cl))
    (hlen : bs.length = 16) (hc16 : cl.length = 16) :
    denoteCode escapeCalls udLandLhsTrue22I.instrs (withEnv env s) =
      some (withEnv (udLandLhsTrue22IEnv env bs cl) s) := by
  let l : List (BitVec 8) := byteLanes bs
  have hl : l.length = 16 := by simp only [l, byteLanes, List.length_map, hlen]
  have hmask : hxLowMask.length = 16 := by decide
  have hnine : hxNine.length = 16 := by decide
  have hzero : hxZero.length = 16 := by decide
  have hu16 : hexW8.length = 16 := by decide
  have hw8 : hexW16.length = 8 := by decide
  have hlow16 : (hxLow l).length = 16 := by simp [hxLow, hl, hmask]
  have hsel16 : (hxNineSel cl).length = 16 := by
    simp [hxNineSel, selectLanes_length, hc16, hnine, hzero]
  have hp16 : (hxPadd l cl).length = 16 := by simp [hxPadd, hsel16, hlow16]
  have hub8 : (pmaddUbSw (hxPadd l cl) hexW8).length = 8 :=
    pmaddUbSw_length_sixteen hp16 hu16
  have hwd4 : (pmaddWd (pmaddUbSw (hxPadd l cl) hexW8) hexW16).length = 4 :=
    pmaddWd_length_eight hub8 hw8
  rw [udLandLhsTrue22I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_and_vec _ _ "%26" "%22" 16 8
    l hxLowMask hl hmask (by hex_lk_h h22))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_vec _ _ "%27" "%cmp.i187"
    cl hxNine hxZero hc16 hnine hzero (by hex_lk_h hc187))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binopVec_add_reg _ _ "%add.i201" "%27" "%26"
    16 8 (hxNineSel cl) (hxLow l) hsel16 hlow16 (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_pmaddUbSw _ _ "%28" "%add.i201"
    (.imm (.vector 8 hexW8)) (hxPadd l cl) hexW8 (by hex_lk)
    (evalOperand_vector_of _ 8 16 hexW8 hu16))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_pmaddWd _ _ "%29" "%28"
    (.imm (.vector 16 hexW16)) (pmaddUbSw (hxPadd l cl) hexW8) hexW16 (by hex_lk)
    (evalOperand_vector_of _ 16 8 hexW16 hw8))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_extract_lane _ _ "%vecext.i" "%29" 4 32 64
    (pmaddWd (pmaddUbSw (hxPadd l cl) hexW8) hexW16) (BitVec.ofInt 64 0)
    ((pmaddWd (pmaddUbSw (hxPadd l cl) hexW8) hexW16).getD 0 0) hwd4 (by hex_lk)
    (getD?_eq (by rw [hwd4]; decide)))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%and27.i164" "%vecext.i" .and 32
    (hxCode l cl) (BitVec.ofInt 32 65535) ((hxCode l cl) &&& BitVec.ofInt 32 65535)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%sub23.i" "%and27.i164" .add 32
    ((hxCode l cl) &&& BitVec.ofInt 32 65535) (BitVec.ofInt 32 (-56320))
    (((hxCode l cl) &&& BitVec.ofInt 32 65535) + BitVec.ofInt 32 (-56320))
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp24.i" "%sub23.i" .ult 32
    (((hxCode l cl) &&& BitVec.ofInt 32 65535) + BitVec.ofInt 32 (-56320))
    (BitVec.ofInt 32 1024) (by hex_lk))]
  simp only [denoteCode, withEnv, udLandLhsTrue22IEnv]
  try rfl

theorem udLandLhsTrue22I_run (env : Env) (s : State) (bs : List UInt8)
    (cl : List (BitVec 1))
    (h22 : lookupName env "%22" = some (.vec 16 8 (byteLanes bs)))
    (hc187 : lookupName env "%cmp.i187" = some (.vec 16 1 cl))
    (hlen : bs.length = 16) (hc16 : cl.length = 16) :
    Option.map State.mem
        (denoteCode escapeCalls udLandLhsTrue22I.instrs (withEnv env s)) = some s.mem ∧
      (denoteCode escapeCalls udLandLhsTrue22I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%and27.i164") =
        some (.int 32 (hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535)) ∧
      (denoteCode escapeCalls udLandLhsTrue22I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%sub23.i") =
        some (.int 32 ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
          BitVec.ofInt 32 (-56320))) ∧
      (denoteCode escapeCalls udLandLhsTrue22I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp24.i") =
        some (.int 1 (evalICmp .ult
          ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
            BitVec.ofInt 32 (-56320)) (BitVec.ofInt 32 1024))) := by
  rw [udLandLhsTrue22I_denote env s bs cl h22 hc187 hlen hc16]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udLandLhsTrue22IEnv] <;> hex_lk)

theorem udLandLhsTrue22I_step (env : Env) (s : State) (bs : List UInt8)
    (cl : List (BitVec 1))
    (hpc : s.pc = "land.lhs.true22.i")
    (h22 : lookupName env "%22" = some (.vec 16 8 (byteLanes bs)))
    (hc187 : lookupName env "%cmp.i187" = some (.vec 16 1 cl))
    (hlen : bs.length = 16) (hc16 : cl.length = 16)
    (hcond : evalICmp .ult
        ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
          BitVec.ofInt 32 (-56320)) (BitVec.ofInt 32 1024) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udLandLhsTrue22IEnv env bs cl) s) with
              pc := "if.then26.i", pre := some "land.lhs.true22.i" } := by
  rw [udStep_of (withEnv env s) "land.lhs.true22.i" udLandLhsTrue22I _
    (by rw [withEnv]; exact hpc) findBlock_udLandLhsTrue22I
    (udLandLhsTrue22I_denote env s bs cl h22 hc187 hlen hc16), udLandLhsTrue22I_term]
  have hcmp : evalOperand (withEnv (udLandLhsTrue22IEnv env bs cl) s) (.reg "%cmp24.i") =
      some (.int 1 (evalICmp .ult
        ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
          BitVec.ofInt 32 (-56320)) (BitVec.ofInt 32 1024))) :=
    evalOperand_reg_of _ s "%cmp24.i" _ (by simp only [udLandLhsTrue22IEnv]; hex_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udLandLhsTrue22I_step_zero (env : Env) (s : State) (bs : List UInt8)
    (cl : List (BitVec 1))
    (hpc : s.pc = "land.lhs.true22.i")
    (h22 : lookupName env "%22" = some (.vec 16 8 (byteLanes bs)))
    (hc187 : lookupName env "%cmp.i187" = some (.vec 16 1 cl))
    (hlen : bs.length = 16) (hc16 : cl.length = 16)
    (hcond : evalICmp .ult
        ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
          BitVec.ofInt 32 (-56320)) (BitVec.ofInt 32 1024) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udLandLhsTrue22IEnv env bs cl) s) with
              pc := "if.end32.i", pre := some "land.lhs.true22.i" } := by
  rw [udStep_of (withEnv env s) "land.lhs.true22.i" udLandLhsTrue22I _
    (by rw [withEnv]; exact hpc) findBlock_udLandLhsTrue22I
    (udLandLhsTrue22I_denote env s bs cl h22 hc187 hlen hc16), udLandLhsTrue22I_term]
  have hcmp : evalOperand (withEnv (udLandLhsTrue22IEnv env bs cl) s) (.reg "%cmp24.i") =
      some (.int 1 (evalICmp .ult
        ((hxCode (byteLanes bs) cl &&& BitVec.ofInt 32 65535) +
          BitVec.ofInt 32 (-56320)) (BitVec.ofInt 32 1024))) :=
    evalOperand_reg_of _ s "%cmp24.i" _ (by simp only [udLandLhsTrue22IEnv]; hex_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `if.then26.i`

The second code unit's bits folded into the first: the low twelve bits of the
surrogate pair. -/

def udIfThen26I : Block := blockAt usDecFunction 19 (by decide)

theorem findBlock_udIfThen26I :
    usDecFunction.findBlock "if.then26.i" = some udIfThen26I := by decide

theorem udIfThen26I_instrs :
    udIfThen26I.instrs =
      [ .binop "%sub27.i" .shl 32 (.reg "%and27.i")
          (.imm (.int 32 (BitVec.ofInt 32 10))),
        .binop "%add28.i" .add 32 (.reg "%sub27.i")
          (.imm (.int 32 (BitVec.ofInt 32 (-56557568)))),
        .binop "%add30.i" .or 32 (.reg "%sub23.i") (.reg "%add28.i") ] := by
  decide

theorem udIfThen26I_term : udIfThen26I.term = .br "if.end32.i" := by decide

def udIfThen26IEnv (env : Env) (cp s23 : BitVec 32) : Env :=
  ("%add30.i", .int 32 (s23 ||| ((cp <<< BitVec.ofInt 32 10) +
      BitVec.ofInt 32 (-56557568)))) ::
    ("%add28.i", .int 32 ((cp <<< BitVec.ofInt 32 10) +
      BitVec.ofInt 32 (-56557568))) ::
    ("%sub27.i", .int 32 (cp <<< BitVec.ofInt 32 10)) :: env

theorem udIfThen26I_denote (env : Env) (s : State) (cp s23 : BitVec 32)
    (hcp : lookupName env "%and27.i" = some (.int 32 cp))
    (hs23 : lookupName env "%sub23.i" = some (.int 32 s23)) :
    denoteCode escapeCalls udIfThen26I.instrs (withEnv env s) =
      some (withEnv (udIfThen26IEnv env cp s23) s) := by
  rw [udIfThen26I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%sub27.i" "%and27.i" .shl 32
    cp (BitVec.ofInt 32 10) (cp <<< BitVec.ofInt 32 10) rfl (by hex_lk_h hcp))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%add28.i" "%sub27.i" .add 32
    (cp <<< BitVec.ofInt 32 10) (BitVec.ofInt 32 (-56557568))
    ((cp <<< BitVec.ofInt 32 10) + BitVec.ofInt 32 (-56557568)) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%add30.i" "%sub23.i" "%add28.i"
    .or 32 s23 ((cp <<< BitVec.ofInt 32 10) + BitVec.ofInt 32 (-56557568))
    (s23 ||| ((cp <<< BitVec.ofInt 32 10) + BitVec.ofInt 32 (-56557568)))
    rfl (by hex_lk_h hs23) (by hex_lk))]
  simp only [denoteCode, withEnv, udIfThen26IEnv]
  try rfl

theorem udIfThen26I_run (env : Env) (s : State) (cp s23 : BitVec 32)
    (hcp : lookupName env "%and27.i" = some (.int 32 cp))
    (hs23 : lookupName env "%sub23.i" = some (.int 32 s23)) :
    Option.map State.mem (denoteCode escapeCalls udIfThen26I.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfThen26I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add30.i") =
        some (.int 32 (s23 ||| ((cp <<< BitVec.ofInt 32 10) +
          BitVec.ofInt 32 (-56557568)))) := by
  rw [udIfThen26I_denote env s cp s23 hcp hs23]
  refine ⟨?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  · simp only [Option.bind_some, withEnv, udIfThen26IEnv]
    hex_lk

theorem udIfThen26I_step (env : Env) (s : State) (cp s23 : BitVec 32)
    (hpc : s.pc = "if.then26.i")
    (hcp : lookupName env "%and27.i" = some (.int 32 cp))
    (hs23 : lookupName env "%sub23.i" = some (.int 32 s23)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfThen26IEnv env cp s23) s) with
              pc := "if.end32.i", pre := some "if.then26.i" } := by
  rw [udStep_of (withEnv env s) "if.then26.i" udIfThen26I _
    (by rw [withEnv]; exact hpc) findBlock_udIfThen26I
    (udIfThen26I_denote env s cp s23 hcp hs23), udIfThen26I_term]
  simp only [execTerm, withEnv, hpc]

/-! ### `cleanup32`

The loop's advance: the destination index moved by the unit's length, and the
loop's test at the next position. -/

def udCleanup32IncomingJ : List (String × Operand) :=
  [("if.then6.i", .reg "%add8.i"), ("if.end32.i", .reg "%add.i125")]

def udCleanup32IncomingAdv : List (String × Operand) :=
  [("if.then6.i", .imm (.int 64 (BitVec.ofInt 64 2))),
   ("if.end32.i", .reg "%adv.1.i")]

theorem udCleanup32_instrs :
    udCleanup32.instrs =
      [ .phi "%j.3" (.int 64) udCleanup32IncomingJ,
        .phi "%adv.2" (.int 64) udCleanup32IncomingAdv,
        .binop "%add24" .add 64 (.reg "%adv.2") (.reg "%sub"),
        .icmp "%cmp25" .eq 64 (.reg "%adv.2") (.imm (.int 64 (BitVec.ofInt 64 12))),
        .zext "%conv27" 1 64 (.reg "%cmp25"),
        .binop "%add28" .add 64 (.reg "%inc11") (.reg "%conv27"),
        .icmp "%cmp4" .ult 64 (.reg "%add28") (.reg "%nxp") ] := by
  decide

theorem udCleanup32_term :
    udCleanup32.term = .condbr (.reg "%cmp4") "while.body6" "while.end35" := by
  decide

def udCleanup32Env (env : Env) (j adv sub inc11 nxp : BitVec 64) : Env :=
  let conv := BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat
  let add := inc11 + conv
  ("%cmp4", .int 1 (evalICmp .ult add nxp)) ::
    ("%add28", .int 64 add) ::
    ("%conv27", .int 64 conv) ::
    ("%cmp25", .int 1 (evalICmp .eq adv (BitVec.ofInt 64 12))) ::
    ("%add24", .int 64 (adv + sub)) ::
    ("%adv.2", .int 64 adv) ::
    ("%j.3", .int 64 j) :: env

theorem udCleanup32_denote (env : Env) (s : State) (prev : String) (opj opa : Operand)
    (j adv sub inc11 nxp : BitVec 64)
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udCleanup32IncomingJ = some opj)
    (ha : phiIncoming prev udCleanup32IncomingAdv = some opa)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopa : evalOperand (withEnv (("%j.3", .int 64 j) :: env) s) opa =
      some (.int 64 adv))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode escapeCalls udCleanup32.instrs (withEnv env s) =
      some (withEnv (udCleanup32Env env j adv sub inc11 nxp) s) := by
  let conv : BitVec 64 := BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat
  rw [udCleanup32_instrs]
  have h1 : evalInstr escapeCalls (withEnv env s)
      (.phi "%j.3" (.int 64) udCleanup32IncomingJ) =
      some (withEnv (("%j.3", .int 64 j) :: env) s) := by
    rw [evalInstr_phi (s := withEnv env s) (d := "%j.3") (ty := .int 64)
      (inc := udCleanup32IncomingJ) hpre hj hopj]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ h1]
  have h2 : evalInstr escapeCalls (withEnv (("%j.3", .int 64 j) :: env) s)
      (.phi "%adv.2" (.int 64) udCleanup32IncomingAdv) =
      some (withEnv (("%adv.2", .int 64 adv) :: ("%j.3", .int 64 j) :: env) s) := by
    rw [evalInstr_phi (s := withEnv (("%j.3", .int 64 j) :: env) s) (d := "%adv.2")
      (ty := .int 64) (inc := udCleanup32IncomingAdv) hpre ha hopa]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ h2]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _
    "%add24" "%adv.2" "%sub" adv sub (by hex_lk) (by hex_lk_h hsub))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64_imm _ _
    "%cmp25" "%adv.2" adv (BitVec.ofInt 64 12) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_zext
    (d := "%conv27") (wIn := 1) (wOut := 64) (v := .reg "%cmp25")
    (x := evalICmp .eq adv (BitVec.ofInt 64 12)) (by hex_lk))]
  rw [show (withEnv (("%cmp25", .int 1 (evalICmp .eq adv (BitVec.ofInt 64 12))) ::
        ("%add24", .int 64 (adv + sub)) :: ("%adv.2", .int 64 adv) ::
        ("%j.3", .int 64 j) :: env) s).bind "%conv27"
        (.int 64 (BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat)) =
      withEnv (("%conv27", .int 64 conv) ::
        ("%cmp25", .int 1 (evalICmp .eq adv (BitVec.ofInt 64 12))) ::
        ("%add24", .int 64 (adv + sub)) :: ("%adv.2", .int 64 adv) ::
        ("%j.3", .int 64 j) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _
    "%add28" "%inc11" "%conv27" inc11 conv (by hex_lk_h hinc11) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult64 _ _
    "%cmp4" "%add28" "%nxp" (inc11 + conv) nxp (by hex_lk) (by hex_lk_h hnxp))]
  simp only [denoteCode, withEnv, udCleanup32Env]
  try rfl

theorem udCleanup32_run (env : Env) (s : State) (prev : String) (opj opa : Operand)
    (j adv sub inc11 nxp : BitVec 64)
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udCleanup32IncomingJ = some opj)
    (ha : phiIncoming prev udCleanup32IncomingAdv = some opa)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopa : evalOperand (withEnv (("%j.3", .int 64 j) :: env) s) opa =
      some (.int 64 adv))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    Option.map State.mem (denoteCode escapeCalls udCleanup32.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udCleanup32.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%j.3") = some (.int 64 j) ∧
      (denoteCode escapeCalls udCleanup32.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%adv.2") = some (.int 64 adv) ∧
      (denoteCode escapeCalls udCleanup32.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add28") =
        some (.int 64 (inc11 + BitVec.ofNat 64
          (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat)) ∧
      (denoteCode escapeCalls udCleanup32.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp4") =
        some (.int 1 (evalICmp .ult
          (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp)) := by
  rw [udCleanup32_denote env s prev opj opa j adv sub inc11 nxp
    hpre hj ha hopj hopa hsub hinc11 hnxp]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udCleanup32Env] <;> hex_lk)

theorem udCleanup32_step (env : Env) (s : State) (prev : String) (opj opa : Operand)
    (j adv sub inc11 nxp : BitVec 64)
    (hpc : s.pc = "cleanup32")
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udCleanup32IncomingJ = some opj)
    (ha : phiIncoming prev udCleanup32IncomingAdv = some opa)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopa : evalOperand (withEnv (("%j.3", .int 64 j) :: env) s) opa =
      some (.int 64 adv))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult
        (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp =
        (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCleanup32Env env j adv sub inc11 nxp) s) with
              pc := "while.body6", pre := some "cleanup32" } := by
  rw [udStep_of (withEnv env s) "cleanup32" udCleanup32 _
    (by rw [withEnv]; exact hpc) findBlock_udCleanup32
    (udCleanup32_denote env s prev opj opa j adv sub inc11 nxp
      hpre hj ha hopj hopa hsub hinc11 hnxp), udCleanup32_term]
  have hcmp : evalOperand (withEnv (udCleanup32Env env j adv sub inc11 nxp) s)
      (.reg "%cmp4") =
      some (.int 1 (evalICmp .ult
        (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp)) :=
    evalOperand_reg_of _ s "%cmp4" _ (by simp only [udCleanup32Env]; hex_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

theorem udCleanup32_step_zero (env : Env) (s : State) (prev : String) (opj opa : Operand)
    (j adv sub inc11 nxp : BitVec 64)
    (hpc : s.pc = "cleanup32")
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udCleanup32IncomingJ = some opj)
    (ha : phiIncoming prev udCleanup32IncomingAdv = some opa)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopa : evalOperand (withEnv (("%j.3", .int 64 j) :: env) s) opa =
      some (.int 64 adv))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult
        (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp =
        (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udCleanup32Env env j adv sub inc11 nxp) s) with
              pc := "while.end35", pre := some "cleanup32" } := by
  rw [udStep_of (withEnv env s) "cleanup32" udCleanup32 _
    (by rw [withEnv]; exact hpc) findBlock_udCleanup32
    (udCleanup32_denote env s prev opj opa j adv sub inc11 nxp
      hpre hj ha hopj hopa hsub hinc11 hnxp), udCleanup32_term]
  have hcmp : evalOperand (withEnv (udCleanup32Env env j adv sub inc11 nxp) s)
      (.reg "%cmp4") =
      some (.int 1 (evalICmp .ult
        (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp)) :=
    evalOperand_reg_of _ s "%cmp4" _ (by simp only [udCleanup32Env]; hex_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

end LeanLLVM.Refinement


namespace LeanLLVM.Refinement

/-! ### `if.end32.i`

The escape's bytes packed into a word and stored: the three length tests select
the one-, two-, three- or four-byte packing, and the same tests select the
length the cursor advances by. -/

def udIfEnd32I : Block := blockAt usDecFunction 20 (by decide)

theorem findBlock_udIfEnd32I :
    usDecFunction.findBlock "if.end32.i" = some udIfEnd32I := by decide

def udIfEnd32IIncomingCp : List (String × Operand) :=
  [("if.end3.i", .reg "%and27.i"), ("if.then26.i", .reg "%add30.i"),
   ("land.lhs.true22.i", .reg "%and27.i"), ("if.then17.i", .reg "%and27.i")]

def udIfEnd32IIncomingAdv : List (String × Operand) :=
  [("if.end3.i", .imm (.int 64 (BitVec.ofInt 64 6))),
   ("if.then26.i", .imm (.int 64 (BitVec.ofInt 64 12))),
   ("land.lhs.true22.i", .imm (.int 64 (BitVec.ofInt 64 6))),
   ("if.then17.i", .imm (.int 64 (BitVec.ofInt 64 6)))]

theorem udIfEnd32I_instrs :
    udIfEnd32I.instrs =
      [ .phi "%cp.i.3" (.int 32) udIfEnd32IIncomingCp,
        .phi "%adv.1.i" (.int 64) udIfEnd32IIncomingAdv,
        .binop "%shr.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (6)))),
        .binop "%and.i208" .and 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (63)))),
        .binop "%or1.i" .or 32 (.reg "%and.i208") (.imm (.int 32 (BitVec.ofInt 32 (128)))),
        .binop "%shl.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
        .binop "%or.i209" .or 32 (.reg "%shr.i") (.reg "%shl.i"),
        .binop "%or2.i" .or 32 (.reg "%or.i209") (.imm (.int 32 (BitVec.ofInt 32 (192)))),
        .binop "%shr3.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (12)))),
        .binop "%and6.i" .and 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofInt 32 (63)))),
        .binop "%or7.i" .or 32 (.reg "%and6.i") (.imm (.int 32 (BitVec.ofInt 32 (128)))),
        .binop "%shl8.i" .shl 32 (.reg "%or7.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
        .binop "%shl12.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (16)))),
        .binop "%30" .or 32 (.reg "%shl8.i") (.reg "%shl12.i"),
        .binop "%or9.i" .or 32 (.reg "%shr3.i") (.reg "%30"),
        .binop "%or13.i" .or 32 (.reg "%or9.i") (.imm (.int 32 (BitVec.ofInt 32 (224)))),
        .binop "%shr14.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (18)))),
        .binop "%and17.i" .shl 32 (.reg "%shr3.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
        .binop "%or18.i" .and 32 (.reg "%and17.i") (.imm (.int 32 (BitVec.ofInt 32 (16128)))),
        .binop "%shl19.i" .or 32 (.reg "%shr14.i") (.reg "%or18.i"),
        .binop "%shl24.i" .shl 32 (.reg "%or7.i") (.imm (.int 32 (BitVec.ofInt 32 (16)))),
        .binop "%or20.i" .or 32 (.reg "%shl19.i") (.reg "%shl24.i"),
        .binop "%shl28.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (24)))),
        .binop "%or25.i" .or 32 (.reg "%or20.i") (.reg "%shl28.i"),
        .binop "%or29.i" .or 32 (.reg "%or25.i") (.imm (.int 32 (BitVec.ofInt 32 (33008)))),
        .icmp "%cmp.i210" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (127)))),
        .icmp "%cmp30.i" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (2047)))),
        .zext "%conv31.i" 1 64 (.reg "%cmp30.i"),
        .icmp "%cmp32.i" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (65535)))),
        .zext "%conv33.i" 1 64 (.reg "%cmp32.i"),
        .select "%cond.i" (.int 32) (.reg "%cmp.i210") (.reg "%or2.i") (.reg "%cp.i.3"),
        .select "%cond38.i" (.int 32) (.reg "%cmp30.i") (.reg "%or13.i") (.reg "%cond.i"),
        .select "%cond43.i" (.int 32) (.reg "%cmp32.i") (.reg "%or29.i") (.reg "%cond38.i"),
        .select "%add.i211" (.int 64) (.reg "%cmp.i210") (.imm (.int 64 (BitVec.ofInt 64 2))) (.imm (.int 64 (BitVec.ofInt 64 1))),
        .gep "%add.ptr.i124" (.int 8) (.reg "%dst") (.reg "%add15"),
        .store (.int 32) (.reg "%cond43.i") (.reg "%add.ptr.i124"),
        .binop "%add44.i" .add 64 (.reg "%add15") (.reg "%conv31.i"),
        .binop "%add45.i" .add 64 (.reg "%add44.i") (.reg "%add.i211"),
        .binop "%add.i125" .add 64 (.reg "%add45.i") (.reg "%conv33.i") ] := by
  decide

theorem udIfEnd32I_term : udIfEnd32I.term = .br "cleanup32" := by decide

/-- The two-byte form's word: nine in the high byte of the low pair. -/
def udIfEnd32Or2 (cp : BitVec 32) : BitVec 32 :=
  ((cp >>> BitVec.ofInt 32 6) |||
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8)) |||
    BitVec.ofInt 32 192

/-- The three-byte form's word. -/
def udIfEnd32Or13 (cp : BitVec 32) : BitVec 32 :=
  ((cp >>> BitVec.ofInt 32 12) |||
    (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 8) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16))) |||
    BitVec.ofInt 32 224

/-- The four-byte form's word. -/
def udIfEnd32Or29 (cp : BitVec 32) : BitVec 32 :=
  (((cp >>> BitVec.ofInt 32 18) |||
    (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
    ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
      BitVec.ofInt 32 16)) |||
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24) |||
    BitVec.ofInt 32 33008

/-- The first select's word: two bytes once the unit is above `0x7F`. -/
def udIfEnd32S1 (cp : BitVec 32) : BitVec 32 :=
  if evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1) then udIfEnd32Or2 cp else cp

/-- The second select's word: three bytes once the unit is above `0x7FF`. -/
def udIfEnd32S2 (cp : BitVec 32) : BitVec 32 :=
  if evalICmp .ugt cp (BitVec.ofInt 32 2047) = (1 : BitVec 1) then udIfEnd32Or13 cp
  else udIfEnd32S1 cp

/-- **The stored word**: the packing the three tests select, as one term. -/
def udIfEnd32Word (cp : BitVec 32) : BitVec 32 :=
  if evalICmp .ugt cp (BitVec.ofInt 32 65535) = (1 : BitVec 1) then udIfEnd32Or29 cp
  else udIfEnd32S2 cp

/-- The advance the same test selects: two bytes below `0x80`, one above. -/
def udIfEnd32Adv (cp : BitVec 32) : BitVec 64 :=
  if evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1) then BitVec.ofInt 64 2
  else BitVec.ofInt 64 1

/-! ### The block's two scalar instructions the trace needs

A scalar select keeps its condition in the value: the cell is the selected word,
so the branch stays an `if` over BitVec values and the store's word is one term.
`b_select_op`'s verdict is the same instruction at a `Value`-level `if`; here the
`if` is pushed inside the integer, which is what lets `storeValue` see a word. -/

/-- `%d = select i1 %c, i32 %a, i32 %b`. -/
theorem b_select_i32 (env : Env) (s : State) (d c a b : String) (cb : BitVec 1)
    (x y : BitVec 32)
    (hc : lookupName env c = some (.int 1 cb))
    (ha : lookupName env a = some (.int 32 x))
    (hb : lookupName env b = some (.int 32 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.select d (.int 32) (.reg c) (.reg a) (.reg b)) =
      some (withEnv ((d, .int 32 (if cb = (1 : BitVec 1) then x else y)) :: env) s) := by
  rw [evalInstr,
    show evalOperand (withEnv env s) (.reg c) = some (.int 1 cb) from hc,
    show evalOperand (withEnv env s) (.reg a) = some (.int 32 x) from ha,
    show evalOperand (withEnv env s) (.reg b) = some (.int 32 y) from hb]
  rcases bv1_cases cb with h | h <;> simp [h, withEnv, State.bind]

/-- `%d = select i1 %c, i64 <x>, i64 <y>`, at whatever the arms read as. -/
theorem b_select_i64_op (env : Env) (s : State) (d c : String) (a b : Operand)
    (cb : BitVec 1) (x y : BitVec 64)
    (hc : lookupName env c = some (.int 1 cb))
    (ha : evalOperand (withEnv env s) a = some (.int 64 x))
    (hb : evalOperand (withEnv env s) b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.select d (.int 64) (.reg c) a b) =
      some (withEnv ((d, .int 64 (if cb = (1 : BitVec 1) then x else y)) :: env) s) := by
  rw [evalInstr,
    show evalOperand (withEnv env s) (.reg c) = some (.int 1 cb) from hc, ha, hb]
  rcases bv1_cases cb with h | h <;> simp [h, withEnv, State.bind]

/-- `%d = zext i1 %src to i64`, in the environment shape the block builds. -/
theorem b_zext1_64w (env : Env) (s : State) (d src : String) (x : BitVec 1)
    (h : lookupName env src = some (.int 1 x)) :
    evalInstr escapeCalls (withEnv env s) (.zext d 1 64 (.reg src)) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s src (.int 1 x) h)]
  simp only [withEnv, State.bind]

def udIfEnd32IEnv (env : Env) (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat) : Env :=
  let shr := cp >>> BitVec.ofInt 32 6
  let m := cp &&& BitVec.ofInt 32 63
  let or1 := m ||| BitVec.ofInt 32 128
  let shl := or1 <<< BitVec.ofInt 32 8
  let or0 := shr ||| shl
  let or2 := or0 ||| BitVec.ofInt 32 192
  let shr3 := cp >>> BitVec.ofInt 32 12
  let and6 := shr &&& BitVec.ofInt 32 63
  let or7 := and6 ||| BitVec.ofInt 32 128
  let shl8 := or7 <<< BitVec.ofInt 32 8
  let shl12 := or1 <<< BitVec.ofInt 32 16
  let o30 := shl8 ||| shl12
  let or9 := shr3 ||| o30
  let or13 := or9 ||| BitVec.ofInt 32 224
  let shr14 := cp >>> BitVec.ofInt 32 18
  let and17 := shr3 <<< BitVec.ofInt 32 8
  let or18 := and17 &&& BitVec.ofInt 32 16128
  let shl19 := shr14 ||| or18
  let shl24 := or7 <<< BitVec.ofInt 32 16
  let or20 := shl19 ||| shl24
  let shl28 := or1 <<< BitVec.ofInt 32 24
  let or25 := or20 ||| shl28
  let or29 := or25 ||| BitVec.ofInt 32 33008
  let c1 := evalICmp .ugt cp (BitVec.ofInt 32 127)
  let c2 := evalICmp .ugt cp (BitVec.ofInt 32 2047)
  let c3 := evalICmp .ugt cp (BitVec.ofInt 32 65535)
  let z1 := BitVec.ofNat 64 c2.toNat
  let z3 := BitVec.ofNat 64 c3.toNat
  let a211 := udIfEnd32Adv cp
  let a44 := x + z1
  let a45 := a44 + a211
  let a125 := a45 + z3
  ("%add.i125", .int 64 a125) ::
    ("%add45.i", .int 64 a45) ::
    ("%add44.i", .int 64 a44) ::
    ("%add.ptr.i124", .ptr (dsta + k)) ::
    ("%add.i211", .int 64 a211) ::
    ("%cond43.i", .int 32 (udIfEnd32Word cp)) ::
    ("%cond38.i", .int 32 (udIfEnd32S2 cp)) ::
    ("%cond.i", .int 32 (udIfEnd32S1 cp)) ::
    ("%conv33.i", .int 64 z3) ::
    ("%cmp32.i", .int 1 c3) ::
    ("%conv31.i", .int 64 z1) ::
    ("%cmp30.i", .int 1 c2) ::
    ("%cmp.i210", .int 1 c1) ::
    ("%or29.i", .int 32 or29) ::
    ("%or25.i", .int 32 or25) ::
    ("%shl28.i", .int 32 shl28) ::
    ("%or20.i", .int 32 or20) ::
    ("%shl24.i", .int 32 shl24) ::
    ("%shl19.i", .int 32 shl19) ::
    ("%or18.i", .int 32 or18) ::
    ("%and17.i", .int 32 and17) ::
    ("%shr14.i", .int 32 shr14) ::
    ("%or13.i", .int 32 or13) ::
    ("%or9.i", .int 32 or9) ::
    ("%30", .int 32 o30) ::
    ("%shl12.i", .int 32 shl12) ::
    ("%shl8.i", .int 32 shl8) ::
    ("%or7.i", .int 32 or7) ::
    ("%and6.i", .int 32 and6) ::
    ("%shr3.i", .int 32 shr3) ::
    ("%or2.i", .int 32 or2) ::
    ("%or.i209", .int 32 or0) ::
    ("%shl.i", .int 32 shl) ::
    ("%or1.i", .int 32 or1) ::
    ("%and.i208", .int 32 m) ::
    ("%shr.i", .int 32 shr) ::
    ("%adv.1.i", .int 64 adv) ::
    ("%cp.i.3", .int 32 cp) :: env

/-- The state the block's store leaves: the packed word at `dst + k`, and nothing
else changed. -/
def udIfEnd32IWritten (s : State) (dsta k : Nat) (cp : BitVec 32) : State :=
  { s with mem := writeBytes s.mem (dsta + k) (natToBytes (udIfEnd32Word cp).toNat 4) }

theorem udIfEnd32I_denote (env : Env) (s : State) (prev : String) (opc opa : Operand)
    (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat)
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s) =
      some (withEnv (udIfEnd32IEnv env cp adv x dsta k) (udIfEnd32IWritten s dsta k cp))
  := by
  rw [udIfEnd32I_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (show evalInstr escapeCalls (withEnv env s)
      (.phi "%cp.i.3" (.int 32) udIfEnd32IIncomingCp) =
      some (withEnv (("%cp.i.3", .int 32 cp) :: env) s) from by
    rw [evalInstr_phi (s := withEnv env s) (d := "%cp.i.3") (ty := .int 32)
      (inc := udIfEnd32IIncomingCp) hpre hc hopc]; rfl)]
  rw [denoteCode_cons_of _ _ _ _ _ (show evalInstr escapeCalls
      (withEnv (("%cp.i.3", .int 32 cp) :: env) s)
      (.phi "%adv.1.i" (.int 64) udIfEnd32IIncomingAdv) =
      some (withEnv (("%adv.1.i", .int 64 adv) :: ("%cp.i.3", .int 32 cp) :: env) s)
      from by
    rw [evalInstr_phi (s := withEnv (("%cp.i.3", .int 32 cp) :: env) s) (d := "%adv.1.i")
      (ty := .int 64) (inc := udIfEnd32IIncomingAdv) hpre ha hopa]; rfl)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shr.i" "%cp.i.3" .lshr 32
    cp (BitVec.ofInt 32 6) (cp >>> BitVec.ofInt 32 6) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%and.i208" "%cp.i.3" .and 32
    cp (BitVec.ofInt 32 63) (cp &&& BitVec.ofInt 32 63) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or1.i" "%and.i208" .or 32
    (cp &&& BitVec.ofInt 32 63) (BitVec.ofInt 32 128)
    ((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shl.i" "%or1.i" .shl 32
    ((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) (BitVec.ofInt 32 8)
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or.i209" "%shr.i" "%shl.i" .or 32
    (cp >>> BitVec.ofInt 32 6)
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8)
    ((cp >>> BitVec.ofInt 32 6) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or2.i" "%or.i209" .or 32
    ((cp >>> BitVec.ofInt 32 6) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8))
    (BitVec.ofInt 32 192)
    (((cp >>> BitVec.ofInt 32 6) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 8)) |||
      BitVec.ofInt 32 192) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shr3.i" "%cp.i.3" .lshr 32
    cp (BitVec.ofInt 32 12) (cp >>> BitVec.ofInt 32 12) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%and6.i" "%shr.i" .and 32
    (cp >>> BitVec.ofInt 32 6) (BitVec.ofInt 32 63)
    ((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or7.i" "%and6.i" .or 32
    ((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) (BitVec.ofInt 32 128)
    (((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shl8.i" "%or7.i" .shl 32
    (((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128)
    (BitVec.ofInt 32 8)
    ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
      BitVec.ofInt 32 8) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shl12.i" "%or1.i" .shl 32
    ((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) (BitVec.ofInt 32 16)
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%30" "%shl8.i" "%shl12.i" .or 32
    ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
      BitVec.ofInt 32 8)
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16)
    (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 8) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or9.i" "%shr3.i" "%30" .or 32
    (cp >>> BitVec.ofInt 32 12)
    (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 8) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16))
    ((cp >>> BitVec.ofInt 32 12) |||
      (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
          BitVec.ofInt 32 8) |||
        (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16)))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or13.i" "%or9.i" .or 32
    ((cp >>> BitVec.ofInt 32 12) |||
      (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
          BitVec.ofInt 32 8) |||
        (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16)))
    (BitVec.ofInt 32 224)
    (((cp >>> BitVec.ofInt 32 12) |||
      (((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
          BitVec.ofInt 32 8) |||
        (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 16))) |||
      BitVec.ofInt 32 224) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shr14.i" "%cp.i.3" .lshr 32
    cp (BitVec.ofInt 32 18) (cp >>> BitVec.ofInt 32 18) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%and17.i" "%shr3.i" .shl 32
    (cp >>> BitVec.ofInt 32 12) (BitVec.ofInt 32 8)
    ((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or18.i" "%and17.i" .and 32
    ((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) (BitVec.ofInt 32 16128)
    (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%shl19.i" "%shr14.i" "%or18.i" .or 32
    (cp >>> BitVec.ofInt 32 18)
    (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)
    ((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shl24.i" "%or7.i" .shl 32
    (((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128)
    (BitVec.ofInt 32 16)
    ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
      BitVec.ofInt 32 16) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or20.i" "%shl19.i" "%shl24.i" .or 32
    ((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128))
    ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
      BitVec.ofInt 32 16)
    (((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
      ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 16))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%shl28.i" "%or1.i" .shl 32
    ((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) (BitVec.ofInt 32 24)
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24)
    rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_reg _ _ "%or25.i" "%or20.i" "%shl28.i" .or 32
    (((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
      ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 16))
    (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24)
    ((((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
      ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 16)) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24))
    rfl (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_binop_imm _ _ "%or29.i" "%or25.i" .or 32
    ((((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
      ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 16)) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24))
    (BitVec.ofInt 32 33008)
    (((((cp >>> BitVec.ofInt 32 18) |||
      (((cp >>> BitVec.ofInt 32 12) <<< BitVec.ofInt 32 8) &&& BitVec.ofInt 32 16128)) |||
      ((((cp >>> BitVec.ofInt 32 6) &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<<
        BitVec.ofInt 32 16)) |||
      (((cp &&& BitVec.ofInt 32 63) ||| BitVec.ofInt 32 128) <<< BitVec.ofInt 32 24)) |||
      BitVec.ofInt 32 33008) rfl (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp.i210" "%cp.i.3" .ugt 32
    cp (BitVec.ofInt 32 127) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp30.i" "%cp.i.3" .ugt 32
    cp (BitVec.ofInt 32 2047) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext1_64w _ _ "%conv31.i" "%cmp30.i"
    (evalICmp .ugt cp (BitVec.ofInt 32 2047)) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_imm _ _ "%cmp32.i" "%cp.i.3" .ugt 32
    cp (BitVec.ofInt 32 65535) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext1_64w _ _ "%conv33.i" "%cmp32.i"
    (evalICmp .ugt cp (BitVec.ofInt 32 65535)) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_i32 _ _ "%cond.i" "%cmp.i210"
    "%or2.i" "%cp.i.3" (evalICmp .ugt cp (BitVec.ofInt 32 127))
    (udIfEnd32Or2 cp)
    cp (by hex_lk) (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_i32 _ _ "%cond38.i" "%cmp30.i"
    "%or13.i" "%cond.i" (evalICmp .ugt cp (BitVec.ofInt 32 2047))
    (udIfEnd32Or13 cp) (udIfEnd32S1 cp)
    (by hex_lk) (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_i32 _ _ "%cond43.i" "%cmp32.i"
    "%or29.i" "%cond38.i" (evalICmp .ugt cp (BitVec.ofInt 32 65535))
    (udIfEnd32Or29 cp) (udIfEnd32S2 cp)
    (by hex_lk) (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_select_i64_op _ _ "%add.i211" "%cmp.i210"
    (.imm (.int 64 (BitVec.ofInt 64 2))) (.imm (.int 64 (BitVec.ofInt 64 1)))
    (evalICmp .ugt cp (BitVec.ofInt 32 127))
    (BitVec.ofInt 64 2) (BitVec.ofInt 64 1)
    (by hex_lk)
    (by exact evalOperand_lit_of _ 64 _)
    (by exact evalOperand_lit_of _ 64 _))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%add.ptr.i124" "%dst" "%add15"
    dsta x k (by hex_lk_h hdst) (by hex_lk_h hadd15) hk hpos)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%cond43.i" "%add.ptr.i124"
    (udIfEnd32Word cp) (dsta + k) (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add44.i" "%add15" "%conv31.i"
    x (BitVec.ofNat 64 (evalICmp .ugt cp (BitVec.ofInt 32 2047)).toNat)
    (by hex_lk_h hadd15) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add45.i" "%add44.i" "%add.i211"
    (x + BitVec.ofNat 64 (evalICmp .ugt cp (BitVec.ofInt 32 2047)).toNat)
    (udIfEnd32Adv cp)
    (by hex_lk) (by hex_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add.i125" "%add45.i" "%conv33.i"
    ((x + BitVec.ofNat 64 (evalICmp .ugt cp (BitVec.ofInt 32 2047)).toNat) +
      (if evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1) then
        (BitVec.ofInt 64 2) else (BitVec.ofInt 64 1)))
    (BitVec.ofNat 64 (evalICmp .ugt cp (BitVec.ofInt 32 65535)).toNat)
    (by hex_lk) (by hex_lk))]
  simp only [denoteCode, withEnv, udIfEnd32IEnv]
  try rfl

theorem udIfEnd32I_run (env : Env) (s : State) (prev : String) (opc opa : Operand)
    (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat)
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    Option.map State.mem (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)) =
        some (udIfEnd32IWritten s dsta k cp).mem ∧
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cond43.i") =
        some (.int 32 (udIfEnd32Word cp)) ∧
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i211") =
        some (.int 64 (udIfEnd32Adv cp)) ∧
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr.i124") =
        some (.ptr (dsta + k)) ∧
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%adv.1.i") = some (.int 64 adv) ∧
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i125") =
        some (.int 64 (x + BitVec.ofNat 64
            (evalICmp .ugt cp (BitVec.ofInt 32 2047)).toNat +
          (if evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1) then
            (BitVec.ofInt 64 2) else (BitVec.ofInt 64 1)) +
          BitVec.ofNat 64 (evalICmp .ugt cp (BitVec.ofInt 32 65535)).toNat)) := by
  rw [udIfEnd32I_denote env s prev opc opa cp adv x dsta k
    hpre hc ha hopc hopa hdst hadd15 hk hpos]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv, udIfEnd32IWritten]
  all_goals (simp only [Option.bind_some, withEnv, udIfEnd32IEnv] <;> hex_lk)

theorem udIfEnd32I_step (env : Env) (s : State) (prev : String) (opc opa : Operand)
    (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat)
    (hpc : s.pc = "if.end32.i")
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd32IEnv env cp adv x dsta k)
                (udIfEnd32IWritten s dsta k cp)) with
              pc := "cleanup32", pre := some "if.end32.i" } := by
  rw [udStep_of (withEnv env s) "if.end32.i" udIfEnd32I _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd32I
    (udIfEnd32I_denote env s prev opc opa cp adv x dsta k
      hpre hc ha hopc hopa hdst hadd15 hk hpos), udIfEnd32I_term]
  simp only [execTerm, withEnv, hpc, udIfEnd32IWritten]

/-! ### The store's frame

The block writes four bytes at its own address and nothing else, so every byte
outside that window is the caller's. -/

/-- **The frame of one store**, at whatever bytes it writes: a write at `a0` leaves
every byte outside its own range as it found it. -/
theorem writeBytes_frame (mem : Mem) (a0 : Nat) (bs : List UInt8) :
    UnchangedOutside mem (writeBytes mem a0 bs) [(a0, bs.length)] := by
  intro a ha
  apply readByte_writeBytes_outside
  by_cases h : a < a0
  · exact Or.inl h
  · right
    apply Nat.le_of_not_lt
    intro h4
    exact ha (a0, bs.length) (by simp) ⟨by omega, h4⟩

/-- A four-byte store leaves every byte outside its four bytes as it found it. -/
theorem store32_frame (mem : Mem) (a0 : Nat) (w : BitVec 32) :
    UnchangedOutside mem (writeBytes mem a0 (natToBytes w.toNat 4)) [(a0, 4)] := by
  rw [show (4 : Nat) = (natToBytes w.toNat 4).length from by rw [natToBytes_length]]
  exact writeBytes_frame mem a0 (natToBytes w.toNat 4)

/-- **The block's frame**: the run writes the four bytes of its packed word at
`%dst + %add15` and leaves every other byte of the caller's store as it was. -/
theorem udIfEnd32I_frame (env : Env) (s : State) (prev : String) (opc opa : Operand)
    (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat)
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    UnchangedOutside s.mem
      ((Option.map State.mem (denoteCode escapeCalls udIfEnd32I.instrs
        (withEnv env s))).getD s.mem) [(dsta + k, 4)] := by
  rw [(udIfEnd32I_run env s prev opc opa cp adv x dsta k
    hpre hc ha hopc hopa hdst hadd15 hk hpos).1]
  exact store32_frame s.mem (dsta + k) (udIfEnd32Word cp)

/-- A four-byte store at `dst + k` extends a prefix the caller already holds at
`dst` by the first `enc.length` bytes it writes. -/
theorem readBytes_writeBytes_extend {m : Mem} {dst k : Nat} {out enc : List UInt8}
    (w : Nat) (hout : readBytes m dst k = some out) (hlen : enc.length ≤ 4)
    (hw : (natToBytes w 4).take enc.length = enc) :
    readBytes (writeBytes m (dst + k) (natToBytes w 4)) dst (k + enc.length) =
      some (out ++ enc) := by
  have hbelow : readBytes (writeBytes m (dst + k) (natToBytes w 4)) dst k = some out := by
    rw [readBytes_writeBytes_below m (natToBytes w 4) k dst (dst + k) (by omega)]
    exact hout
  have hfull := readBytes_writeBytes_same m (natToBytes w 4) (addr := dst + k)
  have hsplit := readBytes_split (writeBytes m (dst + k) (natToBytes w 4)) (dst + k)
    enc.length (4 - enc.length)
    (by rw [show enc.length + (4 - enc.length) = 4 from by omega]; exact hfull)
  have hat : readBytes (writeBytes m (dst + k) (natToBytes w 4)) (dst + k) enc.length =
      some enc := by
    rw [hsplit.1, hw]
  exact JsonEntrySteps.readBytes_append (m := writeBytes m (dst + k) (natToBytes w 4))
    k dst out enc.length enc hbelow hat

/-- **The block's store, composed with the prefix and the frame.**  From a state
whose store already holds the decoded prefix `out` at `%dst`, the block leaves the
caller's prefix extended by the escape's encoding, and changes nothing outside the
four bytes it wrote.

`hword` is the bridge between the body's packed word and the specification's
encoding.  **It is proved, and an earlier revision of this comment said it was
not.**  The proof lives in `JsonEscapeEmitIdentities` — `udIfEnd32Word_toNat`,
beside `udIfEnd3I_highSurrogate_iff` and `udIfThen26I_pairValue` — and that module
imports this one, so the arithmetic cannot be stated where the step is.  What a
consumer of these steps must do is therefore **import `JsonEscapeEmitIdentities` and
hand the three equations to `udIfEnd32I_decode` and the emitter steps**; the
obligation is the import, not the arithmetic.

The earlier revision's account is kept rather than erased, because its history is
why the import is easy to forget — and because the route it called blocked is the
one that was taken: `Nat.lor_eq_add_of_and_eq_zero` *is* declared in this toolchain,
and the equation closes by splitting on the unit's range — `utf8Encode`'s own ranges
against `udIfEnd32Word`'s own selects — and reading each packed word as a sum of
bytes at disjoint shifts.  The four-byte range's 1 048 576 units are the reason
enumeration was refused, not a reason the equation is open. -/
theorem udIfEnd32I_decode (env : Env) (s : State) (prev : String) (opc opa : Operand)
    (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat) (out : List UInt8)
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63)
    (hkout : out.length = k)
    (hout : readBytes s.mem dsta out.length = some out)
    (hword : (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat))
    (hcp : cp.toNat < 0x110000) :
    readBytes ((Option.map State.mem
          (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s))).getD s.mem)
        dsta (out.length + (utf8Encode cp.toNat).length) =
      some (out ++ utf8Encode cp.toNat) ∧
    UnchangedOutside s.mem
      ((Option.map State.mem (denoteCode escapeCalls udIfEnd32I.instrs
        (withEnv env s))).getD s.mem) [(dsta + k, 4)] := by
  have hmem : (Option.map State.mem
      (denoteCode escapeCalls udIfEnd32I.instrs (withEnv env s))).getD s.mem =
      writeBytes s.mem (dsta + k) (natToBytes (udIfEnd32Word cp).toNat 4) := by
    rw [(udIfEnd32I_run env s prev opc opa cp adv x dsta k
      hpre hc ha hopc hopa hdst hadd15 hk hpos).1]
    rfl
  refine ⟨?_, udIfEnd32I_frame env s prev opc opa cp adv x dsta k
    hpre hc ha hopc hopa hdst hadd15 hk hpos⟩
  rw [hmem, hword, hkout]
  refine readBytes_writeBytes_extend (bytesToNat (utf8Encode cp.toNat)) ?_
    (utf8Encode_length_le_four _) (utf8Word_bytes cp.toNat hcp)
  rw [← hkout]
  exact hout

/-- **The two steps from `if.end32.i` to the loop head.**  The block's store and
cursor advance are exactly what `cleanup32` reads, so the pair of steps composes:
the run from the block's entry reaches `while.body6` with the advance `j`, and the
memory the store wrote is the memory the loop carries. -/
theorem udIfEnd32I_to_whileBody6 (env : Env) (s : State) (prev : String)
    (opc opa : Operand) (cp : BitVec 32) (adv x : BitVec 64) (dsta k : Nat)
    (j sub inc11 nxp : BitVec 64)
    (hpc : s.pc = "if.end32.i")
    (hpre : s.pre = some prev)
    (hc : phiIncoming prev udIfEnd32IIncomingCp = some opc)
    (ha : phiIncoming prev udIfEnd32IIncomingAdv = some opa)
    (hopc : evalOperand (withEnv env s) opc = some (.int 32 cp))
    (hopa : evalOperand (withEnv (("%cp.i.3", .int 32 cp) :: env) s) opa =
      some (.int 64 adv))
    (hdst : lookupName env "%dst" = some (.ptr dsta))
    (hadd15 : lookupName env "%add15" = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63)
    (hjv : lookupName (udIfEnd32IEnv env cp adv x dsta k) "%add.i125" =
      some (.int 64 j))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hcond : evalICmp .ult
        (inc11 + BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat) nxp =
        (1 : BitVec 1)) :
    ∀ m, runFuel escapeCalls (2 + m) usDecFunction (withEnv env s) =
      runFuel escapeCalls m usDecFunction
        { (withEnv (udCleanup32Env (udIfEnd32IEnv env cp adv x dsta k) j adv sub inc11 nxp)
            (udIfEnd32IWritten s dsta k cp)) with
          pc := "while.body6", pre := some "cleanup32" } := by
  intro m
  let s1 : State := { (withEnv (udIfEnd32IEnv env cp adv x dsta k)
      (udIfEnd32IWritten s dsta k cp)) with pc := "cleanup32", pre := some "if.end32.i" }
  have h1 : step escapeCalls usDecFunction (withEnv env s) = .jump s1 :=
    udIfEnd32I_step env s prev opc opa cp adv x dsta k hpc hpre hc ha hopc hopa
      hdst hadd15 hk hpos
  have hadv : lookupName
      (udIfEnd32IEnv env cp adv x dsta k) "%adv.1.i" = some (.int 64 adv) := by
    simp only [udIfEnd32IEnv]; hex_lk
  have h2 : step escapeCalls usDecFunction s1 =
      .jump { (withEnv (udCleanup32Env (udIfEnd32IEnv env cp adv x dsta k) j adv sub inc11 nxp)
                (udIfEnd32IWritten s dsta k cp)) with
              pc := "while.body6", pre := some "cleanup32" } :=
    udCleanup32_step (udIfEnd32IEnv env cp adv x dsta k)
      s1 "if.end32.i" (.reg "%add.i125") (.reg "%adv.1.i")
      j adv sub inc11 nxp rfl rfl (by decide) (by decide) hjv hadv
      (by simp only [udIfEnd32IEnv]; hex_lk_h hsub)
      (by simp only [udIfEnd32IEnv]; hex_lk_h hinc11)
      (by simp only [udIfEnd32IEnv]; hex_lk_h hnxp) hcond
  rw [show 2 + m = (1 + m) + 1 from by omega, udRun_jump h1]
  rw [show 1 + m = m + 1 from by omega, udRun_jump h2]

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement

/-! ### Axiom footprints: the hex reader's guard and its successors -/

/-- info: 'LeanLLVM.Refinement.getD?_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getD?_eq

/-- info: 'LeanLLVM.Refinement.bv1_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv1_cases

/-- info: 'LeanLLVM.Refinement.lane_test_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lane_test_eq

/-- info: 'LeanLLVM.Refinement.hexLanes_digit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexLanes_digit

/-- info: 'LeanLLVM.Refinement.hexLanes_letter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexLanes_letter

/-- info: 'LeanLLVM.Refinement.hexZipOr_map_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexZipOr_map_map

/-- info: 'LeanLLVM.Refinement.hexTestLanes_emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexTestLanes_emit

/-- info: 'LeanLLVM.Refinement.hexLanes_low_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexLanes_low_four

/-- info: 'LeanLLVM.Refinement.selectLanes_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms selectLanes_length

/-- info: 'LeanLLVM.Refinement.load_vec16_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms load_vec16_8

/-- info: 'LeanLLVM.Refinement.evalOperand_vector_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evalOperand_vector_of

/-- info: 'LeanLLVM.Refinement.b_binop_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_binop_imm

/-- info: 'LeanLLVM.Refinement.b_binop_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_binop_reg

/-- info: 'LeanLLVM.Refinement.b_icmp_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_imm

/-- info: 'LeanLLVM.Refinement.b_icmp_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_reg

/-- info: 'LeanLLVM.Refinement.b_select_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_select_reg

/-- info: 'LeanLLVM.Refinement.b_extract_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_extract_lane

/-- info: 'LeanLLVM.Refinement.b_binopVec_and_vec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_binopVec_and_vec

/-- info: 'LeanLLVM.Refinement.b_binopVec_add_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_binopVec_add_reg

/-- info: 'LeanLLVM.Refinement.b_select_vec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_select_vec

/-- info: 'LeanLLVM.Refinement.b_call_pmaddUbSw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_pmaddUbSw

/-- info: 'LeanLLVM.Refinement.b_call_pmaddWd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_pmaddWd

/-- info: 'LeanLLVM.Refinement.findBlock_udIfEnd3I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEnd3I

/-- info: 'LeanLLVM.Refinement.udIfEnd3I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd3I_instrs

/-- info: 'LeanLLVM.Refinement.udIfEnd3I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd3I_term

/-- info: 'LeanLLVM.Refinement.udIfEnd3I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd3I_denote

/-- info: 'LeanLLVM.Refinement.udIfEnd3I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd3I_run

/-- info: 'LeanLLVM.Refinement.udIfEnd3I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd3I_step

/-- info: 'LeanLLVM.Refinement.findBlock_udIfThen17I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen17I

/-- info: 'LeanLLVM.Refinement.udIfThen17I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen17I_instrs

/-- info: 'LeanLLVM.Refinement.udIfThen17I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen17I_term

/-- info: 'LeanLLVM.Refinement.udIfThen17I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen17I_denote

/-- info: 'LeanLLVM.Refinement.udIfThen17I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen17I_run

/-- info: 'LeanLLVM.Refinement.udIfThen17I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen17I_step

/-- info: 'LeanLLVM.Refinement.udIfThen17I_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen17I_step_zero

/-- info: 'LeanLLVM.Refinement.findBlock_udLandLhsTrue22I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udLandLhsTrue22I

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_instrs

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_term

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_denote

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_run

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_step

/-- info: 'LeanLLVM.Refinement.udLandLhsTrue22I_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandLhsTrue22I_step_zero

/-- info: 'LeanLLVM.Refinement.findBlock_udIfThen26I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen26I

/-- info: 'LeanLLVM.Refinement.udIfThen26I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen26I_instrs

/-- info: 'LeanLLVM.Refinement.udIfThen26I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen26I_term

/-- info: 'LeanLLVM.Refinement.udIfThen26I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen26I_denote

/-- info: 'LeanLLVM.Refinement.udIfThen26I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen26I_run

/-- info: 'LeanLLVM.Refinement.udIfThen26I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen26I_step

/-- info: 'LeanLLVM.Refinement.udCleanup32_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup32_instrs

/-- info: 'LeanLLVM.Refinement.udCleanup32_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup32_term

/-- info: 'LeanLLVM.Refinement.udCleanup32_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup32_denote

/-- info: 'LeanLLVM.Refinement.udCleanup32_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup32_run

/-- info: 'LeanLLVM.Refinement.udCleanup32_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup32_step

/-- info: 'LeanLLVM.Refinement.udCleanup32_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup32_step_zero

/-- info: 'LeanLLVM.Refinement.store32_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms store32_frame

/-- info: 'LeanLLVM.Refinement.b_select_i32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_select_i32

/-- info: 'LeanLLVM.Refinement.b_select_i64_op' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_select_i64_op

/-- info: 'LeanLLVM.Refinement.b_zext1_64w' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_zext1_64w

/-- info: 'LeanLLVM.Refinement.findBlock_udIfEnd32I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEnd32I

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd32I_instrs

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd32I_term

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_denote

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_run

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_step

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_frame

/-- info: 'LeanLLVM.Refinement.readBytes_writeBytes_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_extend

/-- info: 'LeanLLVM.Refinement.udIfEnd32I_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_decode


/-- info: 'LeanLLVM.Refinement.udIfEnd32I_to_whileBody6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32I_to_whileBody6


/-- info: 'LeanLLVM.Refinement.writeBytes_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeBytes_frame


end LeanLLVM.Refinement
