/-
`num_fast_el1`'s refusal arm at the empty lexeme: the straight-line path
`entry` → `if.end` → `if.then5` → `cleanup300`, and the contract it satisfies.

**What this closes, and what it does not.**  Row f's two exits are the conversion
and the refusal offset.  The conversion arm is the inlined fast path and the
inlined `num_scan` — 178 of the body's 255 blocks carry an inlined suffix — and
it reads two `Operand.global`
tables, calls `num_d8_el1` and `num_el_el1` out of line, and produces the double
`numFastEmitted` models — a body-level proof of it is the decimal-to-binary64
equivalence `docs/contract.md` §8 names as out of scope for the first contract.
The refusal arm is straight-line, and this module proves it **for the empty
lexeme**: at any staging whose lexeme is empty the body runs to its return,
writes the offset the model's scan reports and returns `0`.  It is stated against
`JsonStage2Helpers`' own `s2NumFastPost` and `s2NumFastFoot`, not a restatement.

**Why the empty lexeme is the right first staging.**  It is the body's first
branch (`%cmp.not = (n = 0)`), it needs no byte read, and the model's scan is
`decide`-reducible there (`numLexScan [] = (0, false)`), so the post's refusing
arm is a computation rather than a case analysis.  It is a *class* rather than a
point: `n = 0` quantifies over every base, every slot and every memory.

**The blocks.**  Each block is one `step` read from its own `findBlock` pin — the
`decide`d equation `JsonStage2HelperIRNumFast` states, never a re-reading of
`numFastBody`'s block list.  The `denoteCode` chains are built from the single
instruction steps, because the empty lexeme's blocks hold only `alloca`, one
`icmp`, a two-member `phi` run and a `store`: the chains are computations and the
`phi`'s selected operand is the edge's immediate rather than a register read.
-/
import LeanLLVM.Refinement.JsonStage2NumFastScan

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### One control step, from a block's pin -/

/-- One control step from a block's run: `step` at a state whose program counter
finds `b`, whose instruction list denotes to `s'`, and whose terminator is `c`. -/
theorem numFast_step_at {calls : Calls} {f : Function} {s s' : State} {b : Block}
    {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) :
    step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A `condbr` at a condition the block computed to one. -/
theorem numFast_execTerm_condbr_one (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) (hbit : bit = 1) :
    execTerm s (.condbr (.reg c) t f) = .jump { s with pc := t, pre := some s.pc } := by
  subst hbit
  simp [execTerm, evalOperand, hc]

/-- A `condbr` at a condition the block computed to zero. -/
theorem numFast_execTerm_condbr_zero (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) (hbit : bit = 0) :
    execTerm s (.condbr (.reg c) t f) = .jump { s with pc := f, pre := some s.pc } := by
  subst hbit
  simp [execTerm, evalOperand, hc]

/-! ### The empty lexeme's blocks

The four blocks are read from their pins, and their `denoteCode` is the literal the
pin names.  The environment builders are the chains the blocks' instructions
produce, written out so the `denoteCode` equation ends at a named environment
rather than at a nest of conses. -/

/-- The extent each allocation in `entry` takes, at `Ty.sizeBytes`.  Four kernel
computations, so the chain's arithmetic is numerals rather than divisions. -/
theorem numFast_sb_array : (Ty.array 768 (Ty.int 8)).sizeBytes = 768 := by decide

theorem numFast_sb_stk : (Ty.struct "Stk" 1568).sizeBytes = 1568 := by decide

theorem numFast_sb_i32 : (Ty.int 32).sizeBytes = 4 := by decide

theorem numFast_sb_double : Ty.double.sizeBytes = 8 := by decide

/-- `entry`'s five allocations and its test, as the environment they build: the
allocator's cells in the order the block asks for them, and `%cmp.not`'s bit. -/
def numFastEntryEnv (env : Env) (nxt : Nat) (cmp : BitVec 1) : Env :=
  ("%cmp.not", .int 1 cmp) ::
  ("%d269", .ptr (nxt + 768 + 1568 + 4 + 4)) ::
  ("%v8101", .ptr (nxt + 768 + 1568 + 4)) ::
  ("%v8", .ptr (nxt + 768 + 1568)) ::
  ("%v.i.i", .ptr (nxt + 768)) ::
  ("%dig.i.i", .ptr nxt) :: env

/-- One `alloca`, as a chain step: the cell is the allocator's current address and
the allocator advances by the type's extent.  The state's `next` is a parameter
rather than `s.next`, so a chain of allocations writes the addresses as `nxt`,
`nxt + 768`, … instead of as projections on nested record updates. -/
theorem denoteCode_alloca_at (calls : Calls) (env : Env) (s : State) (nxt : Nat)
    (d : String) (ty : Ty) (al : Nat) (is : List Instr) :
    denoteCode calls (.alloca d ty al :: is) (stateAt env { s with next := nxt }) =
      denoteCode calls is (stateAt ((d, .ptr nxt) :: env)
        { s with next := nxt + ty.sizeBytes }) := by
  exact denoteCode_cons_of calls (.alloca d ty al) is (stateAt env { s with next := nxt })
    (stateAt ((d, .ptr nxt) :: env) { s with next := nxt + ty.sizeBytes })
    (by simp [evalInstr, stateAt])

/-- `%n` is behind `entry`'s five cells: the lookup a chain of allocations leaves
where it found it. -/
theorem numFast_lookup_n (env : Env) (nxt : Nat) (nv : BitVec 64)
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    lookupName
      (("%d269", .ptr (nxt + 768 + 1568 + 4 + 4)) ::
        ("%v8101", .ptr (nxt + 768 + 1568 + 4)) ::
        ("%v8", .ptr (nxt + 768 + 1568)) ::
        ("%v.i.i", .ptr (nxt + 768)) ::
        ("%dig.i.i", .ptr nxt) :: env) "%n" = some (.int 64 nv) := by
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hn

/-- `entry`'s run: the five cells, then the equality's bit at `%cmp.not`. -/
theorem numFast_entry_denote {calls : Calls} {env : Env} {s : State} {nxt : Nat}
    {nv : BitVec 64} (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastEntryInstrs (stateAt env { s with next := nxt }) =
      some (stateAt (numFastEntryEnv env nxt (evalICmp .eq nv 0x0000000000000000#64))
        { s with next := nxt + 768 + 1568 + 4 + 4 + 8 }) := by
  unfold numFastEntryInstrs
  rw [denoteCode_alloca_at, denoteCode_alloca_at, denoteCode_alloca_at,
    denoteCode_alloca_at, denoteCode_alloca_at]
  simp only [numFast_sb_array, numFast_sb_stk, numFast_sb_i32, numFast_sb_double]
  rw [denoteCode_icmp_eq_imm calls _ _ "%cmp.not" "%n"
      (numFast_lookup_n env nxt nv hn),
    denoteCode_nil]
  simp only [numFastEntryEnv, stateAt]

/-- `entry`'s step, at the empty lexeme's branch: the five allocations, the test,
and the jump to `if.end`. -/
theorem numFast_step_entry {env : Env} {s : State} {nv : BitVec 64}
    (hpc : s.pc = "entry") (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .eq nv 0x0000000000000000#64 = 1) :
    step s2HelperCalls numFastBody (stateAt env s) =
      .jump (stateAt (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64))
        { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.end",
                 pre := some "entry" }) := by
  refine numFast_step_at
    (s' := stateAt (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64))
      { s with next := s.next + 768 + 1568 + 4 + 4 + 8 })
    (b := ⟨"entry", numFastEntryInstrs,
      Term.condbr (.reg "%cmp.not") "if.end" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_entry
  · simpa only [denoteCode_nil, stateAt] using
      numFast_entry_denote (calls := s2HelperCalls) (env := env) (s := s) (nxt := s.next) hn
  · have hlk : lookupName
        (stateAt (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64))
          { s with next := s.next + 768 + 1568 + 4 + 4 + 8 }).env
        "%cmp.not" = some (.int 1 (evalICmp .eq nv 0x0000000000000000#64)) := by
      simp only [stateAt, numFastEntryEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp.not" "if.end" "land.lhs.true" hlk hbit]
    simp only [stateAt, hpc]



/-! ### `if.end`, `if.then5`, `cleanup300`

The three blocks of the empty lexeme's path after `entry`.  `if.end`'s two `phi`s
are the edge's immediates (the branch is the entry's, so the selected operands are
`true` and zero); `if.then5` writes the offset and `cleanup300` selects the
refusing form's zero through a thirteen-member `phi` run whose selected operand is
also an immediate. -/

/-- `if.end`'s environment: the two `phi` bindings and the equality's bit. -/
def numFastIfEndEnv (env : Env) (nv : BitVec 64) : Env :=
  ("%cmp3.not", .int 1 (evalICmp .ult 0 nv)) ::
  ("%i.0", .int 64 0) ::
  ("%tobool274.not", .int 1 1) :: env

/-- `if.end`'s run: the two `phi`s, then `%cmp3.not = %i.0 < %n`. -/
theorem numFast_ifEnd_denote {calls : Calls} {env : Env} {s : State} {nv : BitVec 64}
    (hpre : s.pre = some "entry") (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEndInstrs (stateAt env s) =
      some (stateAt (numFastIfEndEnv env nv) s) := by
  unfold numFastIfEndInstrs
  block_eval

/-- `if.end`'s step: the `n = 0` branch leaves for `if.then5`. -/
theorem numFast_step_ifEnd {env : Env} {s : State} {nv : BitVec 64}
    (hpc : s.pc = "if.end") (hpre : s.pre = some "entry")
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult 0 nv = 0) :
    step s2HelperCalls numFastBody (stateAt env s) =
      .jump (stateAt (numFastIfEndEnv env nv)
        { s with pc := "if.then5", pre := some "if.end" }) := by
  refine numFast_step_at
    (s' := stateAt (numFastIfEndEnv env nv) s)
    (b := ⟨"if.end", numFastIfEndInstrs,
      Term.condbr (.reg "%cmp3.not") "if.end6" "if.then5"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_end
  · simpa only [denoteCode_nil] using
      numFast_ifEnd_denote (calls := s2HelperCalls) (env := env) (s := s) hpre hn
  · have hlk : lookupName (numFastIfEndEnv env nv) "%cmp3.not"
        = some (.int 1 (evalICmp .ult 0 nv)) := by
      simp only [numFastIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp3.not" "if.end6" "if.then5" hlk hbit]
    simp only [stateAt, hpc]

/-- `if.then5`'s run: the offset's store at `%err`. -/
theorem numFast_ifThen5_denote {calls : Calls} {env : Env} {s : State} {err : Nat}
    (hi : lookupName env "%i.0" = some (.int 64 0))
    (herr : lookupName env "%err" = some (.ptr err)) :
    denoteCode calls numFastIfThen5Instrs (stateAt env s) =
      some (stateAt env { s with mem := writeBytes s.mem err (natToBytes 0 8) }) := by
  unfold numFastIfThen5Instrs
  rw [denoteCode_store64 calls env s "%i.0" "%err" hi herr, denoteCode_nil]
  rfl

/-- `if.then5`'s step: the store, then the jump to `cleanup300`. -/
theorem numFast_step_ifThen5 {env : Env} {s : State} {err : Nat}
    (hpc : s.pc = "if.then5") (hi : lookupName env "%i.0" = some (.int 64 0))
    (herr : lookupName env "%err" = some (.ptr err)) :
    step s2HelperCalls numFastBody (stateAt env s) =
      .jump (stateAt env
        { s with mem := writeBytes s.mem err (natToBytes 0 8),
                 pc := "cleanup300", pre := some "if.then5" }) := by
  refine numFast_step_at
    (s' := stateAt env { s with mem := writeBytes s.mem err (natToBytes 0 8) })
    (b := ⟨"if.then5", numFastIfThen5Instrs, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then5
  · simpa only [denoteCode_nil] using
      numFast_ifThen5_denote (calls := s2HelperCalls) (env := env) (s := s) hi herr
  · simp only [execTerm, stateAt, hpc]

/-- `cleanup300`'s environment: the return word's `phi`. -/
def numFastCleanup300Env (env : Env) : Env := ("%retval.8", .int 32 0) :: env

/-- `cleanup300`'s run: the thirteen-member `phi` and the return. -/
theorem numFast_cleanup300_denote {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "if.then5") :
    denoteCode calls numFastCleanup300Instrs (stateAt env s) =
      some (stateAt (numFastCleanup300Env env) s) := by
  unfold numFastCleanup300Instrs
  block_eval

/-- `cleanup300`'s step: the refusing form's zero returns. -/
theorem numFast_step_cleanup300 {env : Env} {s : State}
    (hpc : s.pc = "cleanup300") (hpre : s.pre = some "if.then5") :
    step s2HelperCalls numFastBody (stateAt env s) =
      .ret (some (.int 32 0)) (stateAt (numFastCleanup300Env env) s) := by
  refine numFast_step_at
    (s' := stateAt (numFastCleanup300Env env) s)
    (b := ⟨"cleanup300", numFastCleanup300Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_cleanup300
  · simpa only [denoteCode_nil] using
      numFast_cleanup300_denote (calls := s2HelperCalls) (env := env) (s := s) hpre
  · simp only [execTerm, evalOperand, stateAt, numFastCleanup300Env]
    rw [lookupName_cons_self]



/-! ### The empty lexeme's run and its contract

The four steps composed as run prefixes, and the contract's own post and footprint
read at the argument list `[.ptr p, .int 64 0, .ptr out, .ptr err]`.  The post's
refusing arm is the model's `numLexScan [] = (0, false)` — a computation — so the
statement is the contract instance's, not a restatement of it. -/

/-- `numFastBody`'s parameter list, so the staged environment is calculable. -/
theorem numFastBody_params :
    numFastBody.params =
      [("%p", Ty.ptr), ("%n", Ty.int 64), ("%out", Ty.ptr), ("%err", Ty.ptr)] := rfl

/-- The staged environment's `%n`. -/
theorem numFast_staged_n (p out err : Nat) (mem : Mem) (next : Nat) :
    lookupName
      (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next).env
      "%n" = some (.int 64 0) := by
  simp [stagedState, initState, numFastBody_params, List.zip, lookupName]

/-- The staged environment's `%err`. -/
theorem numFast_staged_err (p out err : Nat) (mem : Mem) (next : Nat) :
    lookupName
      (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next).env
      "%err" = some (.ptr err) := by
  simp [stagedState, initState, numFastBody_params, List.zip, lookupName]

/-- The staged state's program counter. -/
theorem numFast_staged_pc (p out err : Nat) (mem : Mem) (next : Nat) :
    (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next).pc
      = "entry" := rfl

/-- The staged state's predecessor is unset: the entry block has none. -/
theorem numFast_staged_pre (p out err : Nat) (mem : Mem) (next : Nat) :
    (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next).pre = none := rfl

/-- **The empty lexeme's run.**  Four control steps — `entry`, `if.end`,
`if.then5`, `cleanup300`'s return — leave the caller's memory with the offset
written at `err` and return `0`. -/
theorem numFast_run_empty (p out err : Nat) (mem : Mem) (next : Nat) :
    runFuel s2HelperCalls 4 numFastBody
      (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next) =
      some (.ret (some (.int 32 0)) (writeBytes mem err (natToBytes 0 8))) := by
  let env0 := (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next).env
  let s0 := stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next
  let s1 := stateAt (numFastEntryEnv env0 next (evalICmp .eq 0 0x0000000000000000#64))
    { s0 with next := next + 768 + 1568 + 4 + 4 + 8, pc := "if.end", pre := some "entry" }
  let s2 := stateAt (numFastIfEndEnv (numFastEntryEnv env0 next
      (evalICmp .eq 0 0x0000000000000000#64)) 0) { s1 with pc := "if.then5", pre := some "if.end" }
  let s3 := stateAt (numFastIfEndEnv (numFastEntryEnv env0 next
      (evalICmp .eq 0 0x0000000000000000#64)) 0)
    { s2 with mem := writeBytes s2.mem err (natToBytes 0 8), pc := "cleanup300",
              pre := some "if.then5" }
  have h1 : step s2HelperCalls numFastBody s0 = .jump s1 :=
    numFast_step_entry (env := env0) (s := s0) rfl (numFast_staged_n p out err mem next) rfl
  have h2 : step s2HelperCalls numFastBody s1 = .jump s2 :=
    numFast_step_ifEnd (env := _) (s := s1)
      (by simp [s1, s0, stateAt]) rfl
      (by simp only [numFastEntryEnv]; rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact numFast_staged_n p out err mem next)
      (by decide)
  have h3 : step s2HelperCalls numFastBody s2 = .jump s3 :=
    numFast_step_ifThen5 (env := _) (s := s2)
      (by simp [s2, s1, s0, stateAt]) rfl rfl
  have h4 : step s2HelperCalls numFastBody s3
      = .ret (some (.int 32 0)) (stateAt (numFastCleanup300Env _) s3) :=
    numFast_step_cleanup300 (env := _) (s := s3)
      (by simp [s3, s2, s1, s0, stateAt]) rfl
  have hr : runFuel s2HelperCalls 4 numFastBody s0 =
      some (.ret (some (.int 32 0)) (writeBytes mem err (natToBytes 0 8))) := by
    rw [show (4:ℕ) = 3 + 1 from rfl, runFuel.eq_2, h1]
    simp only []
    rw [show (3:ℕ) = 2 + 1 from rfl, runFuel.eq_2, h2]
    simp only []
    rw [show (2:ℕ) = 1 + 1 from rfl, runFuel.eq_2, h3]
    simp only []
    rw [show (1:ℕ) = 0 + 1 from rfl, runFuel.eq_2, h4]
    simp only [s3, s2, s1, s0, stateAt, stagedState, initState]
  exact hr



/-- **The contract at the empty lexeme.**  The body's run of the empty lexeme
satisfies `s2NumFastContract`'s post and footprint at the argument list
`[.ptr p, .int 64 0, .ptr out, .ptr err]`: the refusing arm, whose offset the
model's scan reports as zero and whose value slot the body never touches.  The
contract's `pre` holds there too — `readBytes mem p 0 = some []`, which is the
empty lexeme — so this is the instance's triple at a staging class, with the
lexeme fixed at the one the body's first branch handles. -/
theorem numFastBody_contract_empty (p out err : Nat) (mem : Mem) (next : Nat) :
    ∃ o : CallOutcome,
      runFuel s2HelperCalls 4 numFastBody
          (stagedState numFastBody [.ptr p, .int 64 0, .ptr out, .ptr err] mem next)
        = some (.ret (some o.ret) o.mem) ∧
      s2NumFastContract.post [.ptr p, .int 64 0, .ptr out, .ptr err] mem next o ∧
      UnchangedOutside mem o.mem
        (s2NumFastContract.foot [.ptr p, .int 64 0, .ptr out, .ptr err] mem next) := by
  refine ⟨⟨.int 32 0, writeBytes mem err (natToBytes 0 8), next⟩,
    numFast_run_empty p out err mem next, ?_, ?_⟩
  · simp only [s2NumFastContract, s2NumFastPost]
    refine ⟨[], rfl, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    all_goals
      first
      | rfl
      | decide
  · simp only [s2NumFastContract, s2NumFastFoot]
    refine UnchangedOutside.write_le (w := 8)
      (UnchangedOutside.refl' mem [(out, 8), (err, 8)])
      ⟨(err, 8), by simp, le_rfl, le_rfl⟩ ?_
    simp [natToBytes]

/-! ### Axiom footprints

The instance, the run and the contract statement, pinned with `#guard_msgs` so the
build checks the footprint rather than printing it.  The instrument is
`#print axioms`; a declaration proved with `sorry` prints `sorryAx` under the same
command, which is the control §7.6 records. -/

/-- info: 'LeanLLVM.Refinement.numFast_entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_entry_denote

/-- info: 'LeanLLVM.Refinement.numFast_run_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_run_empty

/-- info: 'LeanLLVM.Refinement.numFastBody_contract_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFastBody_contract_empty

end LeanLLVM.Refinement
