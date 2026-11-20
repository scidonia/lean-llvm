/-
The contracted stage-1 block unit's block traces, at its pinned body.

`JsonS1BlocksIR` pins the nine-block body; `JsonS1BlocksSteps` states the loop's
word composition against the specification.  This module holds the execution: the
unit's call environment, and the trace of each block whose instructions are
integer or one intrinsic call, with the block's step in each arm of its
terminator.

The body block and the peeled tail are the classifier's vector arithmetic, and
their traces need the lane vocabulary (`<32 x i8>` table lookups, the two half
words, the shuffle order) that the mask unit's step corpus supplies.  They are
**not** in this module: what is here is what a caller can read without that
vocabulary — the entry test, the gate's test, the loop exit's carried values,
the latch's bound, and the done block's `ptestz` return.  The body, the peeled
tail, the two escape arms, the loop induction and the post assembly that consume
them are still owed.

Each block's instruction list is stated as a literal and pinned against the
fixture by a `rfl`, the way the numeric arms pin theirs: a trace is then a proof
about the literal list, and a change to either spelling fails the pin.

The call environment is `s1BlocksCalls`: the mask unit's `s1Calls`, whose two
intrinsics this body also calls, extended by the ASCII probe's lane test.  Nothing
else is bound: an unresolved symbol stays `ub`, so an emission this environment
does not describe fails rather than being read as something it is not.
-/
import LeanLLVM.Refinement.BlockEvalVector
import LeanLLVM.Refinement.JsonS1BlocksIR
import LeanLLVM.Refinement.JsonS1BlocksSteps
import LeanLLVM.Refinement.CallsFootprint

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls evalInstr_call evalInstr_icmp)
open LeanLLVM.Refinement.BitLanes (ptestz)

set_option autoImplicit false

/-! ### The call environment -/

/-- The unit's call environment: the mask unit's two intrinsics, and the ASCII
probe's 256-bit zero test. -/
def s1BlocksCalls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
        some { ret := .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
              (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
    | _, _ => s1Calls callee args mem next

/-- The probe's zero test: the two `<4 x i64>` operands packed little-endian into
one 256-bit word each, and `ptestz` read at that word. -/
theorem s1BlocksCalls_ptestz (a b : List (BitVec 64)) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.avx.ptestz.256" [.vec 4 64 a, .vec 4 64 b] mem next =
      some { ret := .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
            (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next } :=
  rfl

/-- The two table lookups are the mask unit's own arms. -/
theorem s1BlocksCalls_pshufb (table control : List (BitVec 8)) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.avx2.pshuf.b" [.vec 32 8 table, .vec 32 8 control] mem next =
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next } :=
  rfl

/-- The carry-less product at immediate zero is the mask unit's arm. -/
theorem s1BlocksCalls_pclmulqdq (a0 a1 b0 b1 : BitVec 64) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.pclmulqdq"
        [.vec 2 64 [a0, a1], .vec 2 64 [b0, b1], .int 8 (0 : BitVec 8)] mem next =
      some { ret := .vec 2 64 [Pclmul.clmul a0 b0, (0 : BitVec 64)],
             mem := mem, next := next } :=
  rfl

/-- **The unit's caller-visible footprint is empty.**  Every arm is a register
operation on its operands, so no address the caller holds moves across a call. -/
def s1BlocksCallsFootprint : CallsFootprint s1BlocksCalls :=
  CallsFootprint.pure s1BlocksCalls (by
    intro sym args mem next r h
    simp only [s1BlocksCalls] at h
    repeat' split at h
    all_goals (try (simp only [s1Calls] at h))
    all_goals (try (repeat' split at h))
    all_goals (try (cases h))
    all_goals rfl)

/-! ### A two-operand value call

`ptestz` takes two vector operands and returns an `i32`; the mask unit's calls take
three operands each, so the chain vocabulary has no step for this shape.  It is the
same step at two argument slots, and the operand types stay parameters because the
`call` instruction carries them. -/

theorem step_call2 (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (callee : String) (ty1 ty2 : Ty) (o1 o2 : Operand) {v1 v2 : Value}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.call d ty callee [(ty1, o1), (ty2, o2)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have ha : evalOperands (stateAt env s) [(ty1, o1), (ty2, o2)] = some [v1, v2] := by
    simp [evalOperands, h1, h2]
  rw [evalInstr_call (s := stateAt env s) ha hc]
  rfl

theorem denoteCode_call2 (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (callee : String) (ty1 ty2 : Ty) (o1 o2 : Operand) {v1 v2 : Value}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.call d ty callee [(ty1, o1), (ty2, o2)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_call2 calls env s d ty callee ty1 ty2 o1 o2
    h1 h2 hc)]

/-- `%d = icmp ne i32 %a, <c>`. -/
theorem step_icmp_ne_imm32 (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 32}
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr calls (stateAt env s) (.icmp d .ne 32 (.reg a) (.imm (.int 32 c))) =
      some (stateAt ((d, .int 1 (evalICmp .ne x c)) :: env) s) := by
  rw [evalInstr_icmp (s := stateAt env s)
    (ha := BlockEval.evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := BlockEval.evalOperand_lit_of _ 32 c)]
  simp only [stateAt, State.bind]

/-- One control step at a block the function pins: the block lookup, the
straight-line run, and the terminator. -/
theorem step_at {f : Function} {s s' : State} {b : Block} {c : Ctrl}
    (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode s1BlocksCalls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) :
    step s1BlocksCalls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A `condbr` at a condition the block computed to one. -/
theorem execTerm_condbr_one (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) (hbit : bit = 1) :
    execTerm s (.condbr (.reg c) t f) = .jump { s with pc := t, pre := some s.pc } := by
  subst hbit
  simp [execTerm, evalOperand, hc]

/-- A `condbr` at a condition the block computed to zero. -/
theorem execTerm_condbr_zero (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) (hbit : bit = 0) :
    execTerm s (.condbr (.reg c) t f) = .jump { s with pc := f, pre := some s.pc } := by
  subst hbit
  simp [execTerm, evalOperand, hc]

theorem denoteCode_icmp_ne_imm32 (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 32}
    (ha : lookupName env a = some (.int 32 x)) (is : List Instr) :
    denoteCode calls (.icmp d .ne 32 (.reg a) (.imm (.int 32 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ne x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_ne_imm32 calls env s d a ha)]

/-! ### `entry`: the block count and the partial-tail test -/

def entryInstrs : List Instr :=
  [ .binop "%shr" .lshr 64 (reg "%n") (lit 64 6),
    .binop "%and" .and 64 (reg "%n") (lit 64 63),
    .icmp "%cmp174.not" .ult 64 (reg "%n") (lit 64 64) ]

theorem entryInstrs_eq : entryInstrs = entryBlock.instrs := rfl

/-- `entry`'s environment: `%shr` is the block count, `%and` the leftover byte
count, and `%cmp174.not` the partial-tail test. -/
def entryEnv (env : Env) (n : BitVec 64) : Env :=
  ("%cmp174.not", .int 1 (evalICmp .ult n 64)) ::
  ("%and", .int 64 (n &&& 63)) ::
  ("%shr", .int 64 (n >>> 6)) :: env

theorem entry_denote (env : Env) (s : State) {n : BitVec 64}
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode s1BlocksCalls entryInstrs (stateAt env s) =
      some (stateAt (entryEnv env n) s) := by
  unfold entryInstrs
  simp only [reg, lit]
  block_eval

theorem findBlock_entry : s1BlocksFunction.findBlock "entry" = some entryBlock := by
  simp [s1BlocksFunction, entryBlock, preheaderBlock, cleanupBlock, bodyBlock,
    escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock,
    Function.findBlock, findBlockList]

/-- `entry`'s step, the test taken: the document has a partial tail. -/
theorem entry_step_tail (env : Env) (s : State) {n : BitVec 64}
    (hpc : s.pc = "entry") (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult n 64 = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (entryEnv env n)
        { s with pc := "for.cond.cleanup", pre := some "entry" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (entryEnv env n) s) (b := entryBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_entry
  · exact entry_denote env s hn
  · simp only [entryBlock, reg]
    rw [execTerm_condbr_one _ _ _ _
      (by simp only [stateAt, entryEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-- `entry`'s step, the test refused: the document is a whole number of blocks. -/
theorem entry_step_blocks (env : Env) (s : State) {n : BitVec 64}
    (hpc : s.pc = "entry") (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult n 64 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (entryEnv env n)
        { s with pc := "for.body.lr.ph", pre := some "entry" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (entryEnv env n) s) (b := entryBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_entry
  · exact entry_denote env s hn
  · simp only [entryBlock, reg]
    rw [execTerm_condbr_zero _ _ _ _
      (by simp only [stateAt, entryEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-! ### `for.cond.cleanup`: the loop exit's carried values

The cleanup carries the block index, the classifier's three words, the ASCII
accumulator and the previous block's top scalar lane out of the loop, then tests
the partial tail's presence: the loop leaves into `if.end58` when the document is
a whole number of blocks, and into the peeled tail otherwise. -/

def cleanupInstrs : List Instr :=
  [ .phi "%st.sroa.11.0.lcssa" (.int 64)
      [("entry", lit 64 0), ("if.end", reg "%shr.i")],
    .phi "%st.sroa.7.0.lcssa" (.int 64)
      [("entry", lit 64 0), ("if.end", reg "%conv13.i.i")],
    .phi "%st.sroa.0.0.lcssa" (.int 64)
      [("entry", lit 64 0), ("if.end", reg "%shr.i.i")],
    .phi "%ascii.0.lcssa" v4i64
      [("entry", .imm (.splat 4 64 (BitVec.ofInt 64 0))), ("if.end", reg "%or.i97")],
    .phi "%prevS.0.lcssa" (.int 64) [("entry", lit 64 0), ("if.end", reg "%shr16")],
    .icmp "%tobool19.not" .eq 64 (reg "%and") (lit 64 0) ]

theorem cleanupInstrs_eq : cleanupInstrs = cleanupBlock.instrs := rfl

/-- The cleanup's environment: the six `phi`s' cells and the partial-tail test. -/
def cleanupEnv (env : Env) (st11 st7 st0 prevS andW : BitVec 64)
    (ascii : List (BitVec 64)) : Env :=
  ("%tobool19.not", .int 1 (evalICmp .eq andW 0)) ::
  ("%prevS.0.lcssa", .int 64 prevS) ::
  ("%ascii.0.lcssa", .vec 4 64 ascii) ::
  ("%st.sroa.0.0.lcssa", .int 64 st0) ::
  ("%st.sroa.7.0.lcssa", .int 64 st7) ::
  ("%st.sroa.11.0.lcssa", .int 64 st11) :: env

theorem findBlock_cleanup :
    s1BlocksFunction.findBlock "for.cond.cleanup" = some cleanupBlock := by
  simp [s1BlocksFunction, entryBlock, preheaderBlock, cleanupBlock, bodyBlock,
    escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock,
    Function.findBlock, findBlockList]

/-- The cleanup entered from `entry`: every carried value is the loop's seed. -/
theorem cleanup_denote_entry (env : Env) (s : State) {andW : BitVec 64}
    (hpre : s.pre = some "entry") (hand : lookupName env "%and" = some (.int 64 andW)) :
    denoteCode s1BlocksCalls cleanupInstrs (stateAt env s) =
      some (stateAt (cleanupEnv env 0 0 0 0 andW (List.replicate 4 0)) s) := by
  unfold cleanupInstrs
  simp only [reg, lit]
  block_eval

/-- The cleanup entered from the latch: every carried value is the loop's own. -/
theorem cleanup_denote_loop (env : Env) (s : State) {st11 st7 st0 prevS andW : BitVec 64}
    {ascii : List (BitVec 64)}
    (hpre : s.pre = some "if.end")
    (h11 : lookupName env "%shr.i" = some (.int 64 st11))
    (h7 : lookupName env "%conv13.i.i" = some (.int 64 st7))
    (h0 : lookupName env "%shr.i.i" = some (.int 64 st0))
    (hascii : lookupName env "%or.i97" = some (.vec 4 64 ascii))
    (hprev : lookupName env "%shr16" = some (.int 64 prevS))
    (hand : lookupName env "%and" = some (.int 64 andW)) :
    denoteCode s1BlocksCalls cleanupInstrs (stateAt env s) =
      some (stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii) s) := by
  unfold cleanupInstrs
  simp only [reg, lit]
  block_eval

/-- The cleanup's step, the tail present: the run enters the peeled block. -/
theorem cleanup_step_tail (env : Env) (s : State) {st11 st7 st0 prevS andW : BitVec 64}
    {ascii : List (BitVec 64)} (hpc : s.pc = "for.cond.cleanup")
    (hden : denoteCode s1BlocksCalls cleanupInstrs (stateAt env s) =
      some (stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii) s))
    (hbit : evalICmp .eq andW 0 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii)
        { s with pc := "if.then20", pre := some "for.cond.cleanup" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii) s)
    (b := cleanupBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_cleanup
  · exact hden
  · simp only [cleanupBlock, reg]
    rw [execTerm_condbr_zero _ _ _ _
      (by simp only [stateAt, cleanupEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-- The cleanup's step, the tail absent: the run goes straight to the done block. -/
theorem cleanup_step_done (env : Env) (s : State) {st11 st7 st0 prevS andW : BitVec 64}
    {ascii : List (BitVec 64)} (hpc : s.pc = "for.cond.cleanup")
    (hden : denoteCode s1BlocksCalls cleanupInstrs (stateAt env s) =
      some (stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii) s))
    (hbit : evalICmp .eq andW 0 = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii)
        { s with pc := "if.end58", pre := some "for.cond.cleanup" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (cleanupEnv env st11 st7 st0 prevS andW ascii) s)
    (b := cleanupBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_cleanup
  · exact hden
  · simp only [cleanupBlock, reg]
    rw [execTerm_condbr_one _ _ _ _
      (by simp only [stateAt, cleanupEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-! ### `for.body.lr.ph`: the escape gate -/

def preheaderInstrs : List Instr :=
  [ .binop "%and17" .and 64 (reg "%arm") (lit 64 2),
    .icmp "%tobool.not" .eq 64 (reg "%and17") (lit 64 0) ]

theorem preheaderInstrs_eq : preheaderInstrs = preheaderBlock.instrs := rfl

/-- `for.body.lr.ph`'s environment: `%and17` is the gate's bit and `%tobool.not`
its refusal. -/
def preheaderEnv (env : Env) (arm : BitVec 64) : Env :=
  ("%tobool.not", .int 1 (evalICmp .eq (arm &&& 2) 0)) ::
  ("%and17", .int 64 (arm &&& 2)) :: env

theorem preheader_denote (env : Env) (s : State) {arm : BitVec 64}
    (ha : lookupName env "%arm" = some (.int 64 arm)) :
    denoteCode s1BlocksCalls preheaderInstrs (stateAt env s) =
      some (stateAt (preheaderEnv env arm) s) := by
  unfold preheaderInstrs
  simp only [reg, lit]
  block_eval

theorem findBlock_preheader :
    s1BlocksFunction.findBlock "for.body.lr.ph" = some preheaderBlock := by
  simp [s1BlocksFunction, entryBlock, preheaderBlock, cleanupBlock, bodyBlock,
    escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock,
    Function.findBlock, findBlockList]

theorem preheader_step (env : Env) (s : State) {arm : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph") (ha : lookupName env "%arm" = some (.int 64 arm)) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (preheaderEnv env arm)
        { s with pc := "for.body", pre := some "for.body.lr.ph" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (preheaderEnv env arm) s) (b := preheaderBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_preheader
  · exact preheader_denote env s ha
  · simp only [preheaderBlock, execTerm, stateAt, hpc]

/-! ### `if.end`: the latch's bound -/

def latchInstrs : List Instr :=
  [ .binop "%inc" .add 64 (reg "%i.0178") (lit 64 1),
    .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%shr") ]

theorem latchInstrs_eq : latchInstrs = latchBlock.instrs := rfl

/-- `if.end`'s environment: `%inc` is the next block index and `%exitcond.not` the
comparison with the block count. -/
def latchEnv (env : Env) (i w : BitVec 64) : Env :=
  ("%exitcond.not", .int 1 (evalICmp .eq (i + 1) w)) ::
  ("%inc", .int 64 (i + 1)) :: env

theorem latch_denote (env : Env) (s : State) {i w : BitVec 64}
    (hi : lookupName env "%i.0178" = some (.int 64 i))
    (hw : lookupName env "%shr" = some (.int 64 w)) :
    denoteCode s1BlocksCalls latchInstrs (stateAt env s) =
      some (stateAt (latchEnv env i w) s) := by
  unfold latchInstrs
  simp only [reg, lit]
  block_eval

theorem findBlock_latch : s1BlocksFunction.findBlock "if.end" = some latchBlock := by
  simp [s1BlocksFunction, entryBlock, preheaderBlock, cleanupBlock, bodyBlock,
    escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock,
    Function.findBlock, findBlockList]

/-- `if.end`'s step, the bound reached: the loop leaves for the cleanup. -/
theorem latch_step_exit (env : Env) (s : State) {i w : BitVec 64}
    (hpc : s.pc = "if.end") (hi : lookupName env "%i.0178" = some (.int 64 i))
    (hw : lookupName env "%shr" = some (.int 64 w))
    (hbit : evalICmp .eq (i + 1) w = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (latchEnv env i w)
        { s with pc := "for.cond.cleanup", pre := some "if.end" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (latchEnv env i w) s) (b := latchBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_latch
  · exact latch_denote env s hi hw
  · simp only [latchBlock, reg]
    rw [execTerm_condbr_one _ _ _ _
      (by simp only [stateAt, latchEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-- `if.end`'s step, the bound not reached: the loop re-enters the body. -/
theorem latch_step_loop (env : Env) (s : State) {i w : BitVec 64}
    (hpc : s.pc = "if.end") (hi : lookupName env "%i.0178" = some (.int 64 i))
    (hw : lookupName env "%shr" = some (.int 64 w))
    (hbit : evalICmp .eq (i + 1) w = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (latchEnv env i w)
        { s with pc := "for.body", pre := some "if.end" }) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (latchEnv env i w) s) (b := latchBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_latch
  · exact latch_denote env s hi hw
  · simp only [latchBlock, reg]
    rw [execTerm_condbr_zero _ _ _ _
      (by simp only [stateAt, latchEnv, lookupName_cons_self]) hbit]
    simp only [stateAt, hpc]

/-! ### `if.end58`: the ASCII probe's return

The block's `phi` carries the accumulator the loop or the peeled tail left; its
`ptestz` tests the high bit of every byte, and the block returns `0` or `1`
according to that test. -/

/-- `%ascii.1`'s incoming list, as the pinned `phi` spells it. -/
def doneIncoming : List (String × Operand) :=
  [("for.cond.cleanup", .reg "%ascii.0.lcssa"), ("if.then55", .reg "%or.i"),
   ("if.then20", .reg "%or.i")]

/-- The probe's mask: the high bit of every byte, as `<4 x i64>`. -/
def asciiMaskLanes : List (BitVec 64) :=
  List.replicate 4 (BitVec.ofInt 64 (-9187201950435737472))

/-- `if.end58`'s instructions after its `phi`: the probe, its test, and the
returned word. -/
def doneTailInstrs : List Instr :=
  [ .call "%73" (.int 32) "llvm.x86.avx.ptestz.256"
      [(v4i64, .reg "%ascii.1"),
       (v4i64, .imm (.splat 4 64 (BitVec.ofInt 64 (-9187201950435737472))))],
    .icmp "%cmp61" .ne 32 (reg "%73") (lit 32 0),
    .zext "%conv62" 1 64 (reg "%cmp61") ]

theorem doneInstrs_eq : doneBlock.instrs =
    .phi "%ascii.1" v4i64 doneIncoming :: doneTailInstrs := rfl

/-- The `phi`'s cell, over the caller's environment. -/
def donePhiEnv (env : Env) (l : List (BitVec 64)) : Env :=
  ("%ascii.1", .vec 4 64 l) :: env

/-- The tail's cells: the probe, its refusal, and the returned word. -/
def doneTailEnv (env : Env) (l : List (BitVec 64)) : Env :=
  ("%conv62", .int 64 (BitVec.ofNat 64 (evalICmp .ne
    (ptestz (BitVec.ofNat 256 (packLanes l))
      (BitVec.ofNat 256 (packLanes asciiMaskLanes))) 0).toNat)) ::
  ("%cmp61", .int 1 (evalICmp .ne
    (ptestz (BitVec.ofNat 256 (packLanes l))
      (BitVec.ofNat 256 (packLanes asciiMaskLanes))) (0 : BitVec 32))) ::
  ("%73", .int 32 (ptestz (BitVec.ofNat 256 (packLanes l))
    (BitVec.ofNat 256 (packLanes asciiMaskLanes)))) :: env

/-- `if.end58`'s environment: the carried accumulator and the tail's cells. -/
def doneEnv (env : Env) (l : List (BitVec 64)) : Env :=
  doneTailEnv (donePhiEnv env l) l

/-- The `phi`: the accumulator is the incoming value the edge delivered. -/
theorem done_phi_denote (env : Env) (s : State) {p : String} {op : Operand}
    {l : List (BitVec 64)} (hpre : s.pre = some p)
    (hinc : phiIncoming p doneIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 l)) :
    denoteCode s1BlocksCalls doneBlock.instrs (stateAt env s) =
      denoteCode s1BlocksCalls doneTailInstrs (stateAt (donePhiEnv env l) s) := by
  rw [doneInstrs_eq]
  exact denoteCode_phi s1BlocksCalls env s "%ascii.1" v4i64 doneIncoming hpre hinc hop
    doneTailInstrs (by decide)

/-- The tail: the probe, its test, and the returned word. -/
theorem done_tail_denote (env : Env) (s : State) {l : List (BitVec 64)}
    (ha : lookupName env "%ascii.1" = some (.vec 4 64 l)) :
    denoteCode s1BlocksCalls doneTailInstrs (stateAt env s) =
      some (stateAt (doneTailEnv env l) s) := by
  unfold doneTailInstrs doneTailEnv
  simp only [reg, lit]
  rw [denoteCode_call2 s1BlocksCalls env s "%73" (.int 32) "llvm.x86.avx.ptestz.256"
    v4i64 v4i64 (.reg "%ascii.1")
    (.imm (.splat 4 64 (BitVec.ofInt 64 (-9187201950435737472))))
    (by simp only [evalOperand, Const.toValue, stateAt, ha])
    (by simp only [evalOperand, Const.toValue, asciiMaskLanes])
    (s1BlocksCalls_ptestz l asciiMaskLanes s.mem s.next)]
  rw [denoteCode_icmp_ne_imm32 s1BlocksCalls _ s "%cmp61" "%73"
    (x := ptestz (BitVec.ofNat 256 (packLanes l))
      (BitVec.ofNat 256 (packLanes asciiMaskLanes)))
    (c := BitVec.ofInt 32 0)
    (by simp only [evalOperand, stateAt, lookupName_cons_self])]
  rw [denoteCode_zext s1BlocksCalls _ s "%conv62" "%cmp61" 1 64
    (x := evalICmp .ne
      (ptestz (BitVec.ofNat 256 (packLanes l))
        (BitVec.ofNat 256 (packLanes asciiMaskLanes)))
      (BitVec.ofInt 32 0))
    (by simp only [evalOperand, stateAt, lookupName_cons_self])]
  rfl

theorem done_denote (env : Env) (s : State) {p : String} {op : Operand}
    {l : List (BitVec 64)} (hpre : s.pre = some p)
    (hinc : phiIncoming p doneIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 l)) :
    denoteCode s1BlocksCalls doneBlock.instrs (stateAt env s) =
      some (stateAt (doneEnv env l) s) := by
  rw [done_phi_denote env s hpre hinc hop]
  have ha : lookupName (donePhiEnv env l) "%ascii.1" = some (.vec 4 64 l) :=
    lookupName_cons_self _ _ _
  rw [done_tail_denote (donePhiEnv env l) s ha]
  rfl

theorem findBlock_done : s1BlocksFunction.findBlock "if.end58" = some doneBlock := by
  simp [s1BlocksFunction, entryBlock, preheaderBlock, cleanupBlock, bodyBlock,
    escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock,
    Function.findBlock, findBlockList]

/-- `if.end58`'s step: the run returns the probe word. -/
theorem done_step (env : Env) (s : State) {p : String} {op : Operand}
    {l : List (BitVec 64)} (hpc : s.pc = "if.end58")
    (hpre : s.pre = some p) (hinc : phiIncoming p doneIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 l)) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .ret (some (.int 64 (BitVec.ofNat 64 (evalICmp .ne
        (ptestz (BitVec.ofNat 256 (packLanes l))
          (BitVec.ofNat 256 (packLanes asciiMaskLanes))) 0).toNat)))
        (stateAt (doneEnv env l) s) := by
  have hpc' : (stateAt env s).pc = s.pc := rfl
  refine step_at (f := s1BlocksFunction) (s := stateAt env s)
    (s' := stateAt (doneEnv env l) s) (b := doneBlock) ?_ ?_ ?_
  · simp only [hpc', hpc]
    exact findBlock_done
  · exact done_denote env s hpre hinc hop
  · simp only [doneBlock, reg, execTerm, evalOperand, stateAt, doneEnv, doneTailEnv,
      donePhiEnv, lookupName_cons_self]

end LeanLLVM.Refinement.JsonS1BlocksSteps
