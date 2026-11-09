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
`while.body`, `while.end`, `while.body6`, `if.end`, `if.end.i`, `if.then6.i`, the
two refusals, `us_run.exit`, `us_run.exit112`, `cleanup41`, and the two
double-word copies with their tails
(`while.body.i91`/`us_run_long.exit99`/`if.then.i104` and
`while.body.i`/`us_run_long.exit`/`if.then.i109`).  Each block is a `denoteCode`
fact naming its memory expression and a run fact naming the cells its successors
read, and each branch is the `condbr` arm at the value the block computed.

The copies rest on one identity — `packLanes_copy32`, that a `<4 x i64>` load's
lanes stored back are the bytes it read — so a copy's memory is the bytes it moved
and not a lane term.  The blocks' steps take the sign extension's width equality as
a hypothesis (`(k.signExtend 64).toNat = k.toNat`) rather than proving it: the
core lemma that would prove it, `BitVec.toNat_signExtend`, is stated with
`Classical.choice`, and the trace's own pins stay at `[propext, Quot.sound]` while
the equality is a caller's.  Discharging it at the boundary is where a carrier, if
one is used, will appear, and it belongs to the assembly rather than to these
blocks.

What is not here yet is the rest of the walk: the hex reader (`if.end9.i`,
`if.end.i115`, `if.end3.i`), the pair and UTF-8 emitter (`if.then17.i`,
`land.lhs.true22.i`, `if.then26.i`, `if.end32.i`), `cleanup32`, and the assembly —
the budget term, the destination prefix, the frame per store, and
`escape_expand_satisfies` with its companion.  `cleanup32`'s block name and lookup
are stated so the next group starts there.

Every theorem is pinned where it is proved; the pins are the module's instrument.
-/
import LeanLLVM.Vellum.JsonEscapeExpandContract
import LeanLLVM.Vellum.JsonEscapeListRun
import LeanLLVM.Vellum.JsonEntrySteps

set_option maxRecDepth 8000
set_option autoImplicit false

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec

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

The bridge's signed comparison is where the one `Classical.choice` carrier of this
module enters: `BitVec.toInt` on an eight-bit word is a case split whose `Int`
arithmetic goes through the library's classical order lemmas.  The pin below names
it; the block lemmas do not use the bridge and stay at `[propext, Quot.sound]`. -/

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


end LeanLLVM.Vellum


namespace LeanLLVM.Vellum

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.udStep_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udStep_of

/-- info: 'LeanLLVM.Vellum.udRun_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRun_jump

/-- info: 'LeanLLVM.Vellum.udRun_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRun_ret

/-- info: 'LeanLLVM.Vellum.udCondbr_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCondbr_one

/-- info: 'LeanLLVM.Vellum.udCondbr_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCondbr_zero

/-- info: 'LeanLLVM.Vellum.b_icmp_ult64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult64

/-- info: 'LeanLLVM.Vellum.b_icmp_ult64_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult64_imm

/-- info: 'LeanLLVM.Vellum.b_sub64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_sub64

/-- info: 'LeanLLVM.Vellum.b_load32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load32

/-- info: 'LeanLLVM.Vellum.b_icmp_eq32_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_eq32_imm

/-- info: 'LeanLLVM.Vellum.udEntry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_denote

/-- info: 'LeanLLVM.Vellum.udEntry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_run

/-- info: 'LeanLLVM.Vellum.udEntry_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_cells

/-- info: 'LeanLLVM.Vellum.udEntry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_step

/-- info: 'LeanLLVM.Vellum.udEntry_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udEntry_step_zero

/-- info: 'LeanLLVM.Vellum.udWhileBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_denote

/-- info: 'LeanLLVM.Vellum.udWhileBody_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_run

/-- info: 'LeanLLVM.Vellum.udWhileBody_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_cells

/-- info: 'LeanLLVM.Vellum.udWhileBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_step

/-- info: 'LeanLLVM.Vellum.udWhileBody_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody_step_one

/-- info: 'LeanLLVM.Vellum.udWhileEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_denote

/-- info: 'LeanLLVM.Vellum.udWhileEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_run

/-- info: 'LeanLLVM.Vellum.udWhileEnd_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_cells

/-- info: 'LeanLLVM.Vellum.udWhileEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_step

/-- info: 'LeanLLVM.Vellum.udWhileEnd_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileEnd_step_one

/-- info: 'LeanLLVM.Vellum.udIfThen20_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_denote

/-- info: 'LeanLLVM.Vellum.udIfThen20_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_run

/-- info: 'LeanLLVM.Vellum.udIfThen20_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen20_step

/-- info: 'LeanLLVM.Vellum.udIfThen22_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_denote

/-- info: 'LeanLLVM.Vellum.udIfThen22_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_run

/-- info: 'LeanLLVM.Vellum.udIfThen22_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen22_step

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_denote

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_run

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_cells

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udUsRunExit112_step

/-- info: 'LeanLLVM.Vellum.udCleanup41_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_denote

/-- info: 'LeanLLVM.Vellum.udCleanup41_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_run

/-- info: 'LeanLLVM.Vellum.udCleanup41_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCleanup41_step





/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.b_gep8_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_gep8_reg

/-- info: 'LeanLLVM.Vellum.b_icmp_ugt64_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ugt64_imm

/-- info: 'LeanLLVM.Vellum.udLandRhs_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_denote

/-- info: 'LeanLLVM.Vellum.udLandRhs_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_run

/-- info: 'LeanLLVM.Vellum.udLandRhs_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_cells

/-- info: 'LeanLLVM.Vellum.udLandRhs_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_step

/-- info: 'LeanLLVM.Vellum.udLandRhs_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udLandRhs_step_zero

/-- info: 'LeanLLVM.Vellum.udWhileBody6_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_denote

/-- info: 'LeanLLVM.Vellum.udWhileBody6_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_run

/-- info: 'LeanLLVM.Vellum.udWhileBody6_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_step

/-- info: 'LeanLLVM.Vellum.udWhileBody6_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udWhileBody6_step_one

/-- info: 'LeanLLVM.Vellum.udIfEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_denote

/-- info: 'LeanLLVM.Vellum.udIfEnd_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_run

/-- info: 'LeanLLVM.Vellum.udIfEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_step

/-- info: 'LeanLLVM.Vellum.udIfEnd_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd_step_zero

end LeanLLVM.Vellum

namespace LeanLLVM.Vellum

/-! ### Axiom footprints: the copy and escape-byte blocks -/

/-- info: 'LeanLLVM.Vellum.b_load_vec4_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load_vec4_64

/-- info: 'LeanLLVM.Vellum.b_store_vec4_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store_vec4_64

/-- info: 'LeanLLVM.Vellum.packLanes_copy32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms packLanes_copy32

/-- info: 'LeanLLVM.Vellum.b_load8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load8

/-- info: 'LeanLLVM.Vellum.b_icmp_ult8_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_ult8_imm

/-- info: 'LeanLLVM.Vellum.udCopyBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_denote

/-- info: 'LeanLLVM.Vellum.udCopyBody_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_run

/-- info: 'LeanLLVM.Vellum.udCopyBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_step

/-- info: 'LeanLLVM.Vellum.udCopyBody_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBody_step_zero

/-- info: 'LeanLLVM.Vellum.udCopyTail_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_denote

/-- info: 'LeanLLVM.Vellum.udCopyTail_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_step

/-- info: 'LeanLLVM.Vellum.udCopyTail_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTail_step_zero

/-- info: 'LeanLLVM.Vellum.udCopyTailIf_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIf_denote

/-- info: 'LeanLLVM.Vellum.udCopyTailIf_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIf_step

/-- info: 'LeanLLVM.Vellum.udRunExit_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_denote

/-- info: 'LeanLLVM.Vellum.udRunExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_step

/-- info: 'LeanLLVM.Vellum.udRunExit_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_step_one

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_denote

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_run

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_step

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyBodyN_step_zero

/-- info: 'LeanLLVM.Vellum.udCopyTailN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_denote

/-- info: 'LeanLLVM.Vellum.udCopyTailN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_step

/-- info: 'LeanLLVM.Vellum.udCopyTailN_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailN_step_zero

/-- info: 'LeanLLVM.Vellum.udCopyTailIfN_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIfN_denote

/-- info: 'LeanLLVM.Vellum.udCopyTailIfN_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udCopyTailIfN_step

end LeanLLVM.Vellum

namespace LeanLLVM.Vellum

/-! ### Axiom footprints: the block shapes -/

/-- info: 'LeanLLVM.Vellum.findBlock_udEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udEntry

/-- info: 'LeanLLVM.Vellum.findBlock_udLandRhs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udLandRhs

/-- info: 'LeanLLVM.Vellum.findBlock_udWhileBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileBody

/-- info: 'LeanLLVM.Vellum.findBlock_udWhileEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileEnd

/-- info: 'LeanLLVM.Vellum.findBlock_udWhileBody6' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileBody6

/-- info: 'LeanLLVM.Vellum.findBlock_udIfEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEnd

/-- info: 'LeanLLVM.Vellum.findBlock_udIfThen20' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen20

/-- info: 'LeanLLVM.Vellum.findBlock_udIfThen22' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen22

/-- info: 'LeanLLVM.Vellum.findBlock_udCleanup32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCleanup32

/-- info: 'LeanLLVM.Vellum.findBlock_udUsRunExit112' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udUsRunExit112

/-- info: 'LeanLLVM.Vellum.findBlock_udCleanup41' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCleanup41

/-- info: 'LeanLLVM.Vellum.udEntry_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_instrs

/-- info: 'LeanLLVM.Vellum.udEntry_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udEntry_term

/-- info: 'LeanLLVM.Vellum.udWhileBody_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_instrs

/-- info: 'LeanLLVM.Vellum.udWhileBody_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody_term

/-- info: 'LeanLLVM.Vellum.udWhileEnd_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_instrs

/-- info: 'LeanLLVM.Vellum.udWhileEnd_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileEnd_term

/-- info: 'LeanLLVM.Vellum.udIfThen20_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen20_instrs

/-- info: 'LeanLLVM.Vellum.udIfThen20_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen20_term

/-- info: 'LeanLLVM.Vellum.udIfThen22_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen22_instrs

/-- info: 'LeanLLVM.Vellum.udIfThen22_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen22_term

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_instrs

/-- info: 'LeanLLVM.Vellum.udUsRunExit112_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udUsRunExit112_term

/-- info: 'LeanLLVM.Vellum.udCleanup41_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup41_instrs

/-- info: 'LeanLLVM.Vellum.udCleanup41_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCleanup41_term

/-- info: 'LeanLLVM.Vellum.udLandRhs_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_instrs

/-- info: 'LeanLLVM.Vellum.udLandRhs_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udLandRhs_term

/-- info: 'LeanLLVM.Vellum.udWhileBody6_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody6_instrs

/-- info: 'LeanLLVM.Vellum.udWhileBody6_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udWhileBody6_term

/-- info: 'LeanLLVM.Vellum.udIfEnd_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd_instrs

/-- info: 'LeanLLVM.Vellum.udIfEnd_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEnd_term

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyBody

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyTail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTail

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyTailIf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailIf

/-- info: 'LeanLLVM.Vellum.findBlock_udRunExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udRunExit

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyBodyN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyBodyN

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyTailN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailN

/-- info: 'LeanLLVM.Vellum.findBlock_udCopyTailIfN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCopyTailIfN

/-- info: 'LeanLLVM.Vellum.udCopyBody_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBody_instrs

/-- info: 'LeanLLVM.Vellum.udCopyBody_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBody_term

/-- info: 'LeanLLVM.Vellum.udCopyTail_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTail_instrs

/-- info: 'LeanLLVM.Vellum.udCopyTail_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTail_term

/-- info: 'LeanLLVM.Vellum.udCopyTailIf_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIf_instrs

/-- info: 'LeanLLVM.Vellum.udCopyTailIf_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIf_term

/-- info: 'LeanLLVM.Vellum.udRunExit_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udRunExit_instrs

/-- info: 'LeanLLVM.Vellum.udRunExit_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udRunExit_term

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBodyN_instrs

/-- info: 'LeanLLVM.Vellum.udCopyBodyN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyBodyN_term

/-- info: 'LeanLLVM.Vellum.udCopyTailN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailN_instrs

/-- info: 'LeanLLVM.Vellum.udCopyTailN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailN_term

/-- info: 'LeanLLVM.Vellum.udCopyTailIfN_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIfN_instrs

/-- info: 'LeanLLVM.Vellum.udCopyTailIfN_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udCopyTailIfN_term

end LeanLLVM.Vellum

namespace LeanLLVM.Vellum

/-! ### Axiom footprints: the escape table and its reader -/

/-- info: 'LeanLLVM.Vellum.unescapeTable_getElem?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unescapeTable_getElem?

/-- info: 'LeanLLVM.Vellum.simpleEscape_getD_highBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms simpleEscape_getD_highBit

/-- info: 'LeanLLVM.Vellum.evalICmp_sgt_negone_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_sgt_negone_one_iff

/-- info: 'LeanLLVM.Vellum.unescapeTable_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unescapeTable_test

/-- info: 'LeanLLVM.Vellum.b_zext8_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_zext8_64

/-- info: 'LeanLLVM.Vellum.b_store8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store8

/-- info: 'LeanLLVM.Vellum.b_icmp_sgt8_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_icmp_sgt8_imm

/-- info: 'LeanLLVM.Vellum.findBlock_udIfEndI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfEndI

/-- info: 'LeanLLVM.Vellum.findBlock_udIfThen6I' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udIfThen6I

/-- info: 'LeanLLVM.Vellum.udIfEndI_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEndI_instrs

/-- info: 'LeanLLVM.Vellum.udIfEndI_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfEndI_term

/-- info: 'LeanLLVM.Vellum.udIfEndI_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_denote

/-- info: 'LeanLLVM.Vellum.udIfEndI_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_run

/-- info: 'LeanLLVM.Vellum.udIfEndI_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_step

/-- info: 'LeanLLVM.Vellum.udIfEndI_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEndI_step_zero

/-- info: 'LeanLLVM.Vellum.udIfThen6I_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen6I_instrs

/-- info: 'LeanLLVM.Vellum.udIfThen6I_term' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udIfThen6I_term

/-- info: 'LeanLLVM.Vellum.udIfThen6I_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen6I_denote

/-- info: 'LeanLLVM.Vellum.udIfThen6I_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen6I_step

end LeanLLVM.Vellum
