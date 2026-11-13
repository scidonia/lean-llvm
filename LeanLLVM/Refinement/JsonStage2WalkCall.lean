/-
The stage-2 walk's class F: the nineteen blocks whose instruction list calls out
of line.

`JsonStage2Helpers` states the six helpers' contracts at the walk's call
boundary, and `Stage2WalkObligation` fixes the selection those contracts are read
at: the six helpers fall through `stage2Calls` to the parameter `sub`, so a call
block's link is a contract question and the walk is a statement at
`stage2Calls stage2SubCalls`, the selection the six proved contracts are stated
at.

What a call block owes, and what this module supplies:

* **the step.**  `walkDenoteCode_call` and `walkDenoteCode_callVoid` are the
  `denoteCode` steps of a call at an arbitrary argument list — the shape
  `JsonS1MasksIR.evalInstr_call`'s `evalOperands` premise, not a per-call-arity
  lemma — and `walkArgs_*` are the argument lists the walk's six helpers are
  called at, read off the pinned body.
* **the memory.**  `HelperContract.resolves` gives the outcome, the post and the
  footprint at once.  A call whose callee writes nothing (`s2_value_pos`, and the
  two `llvm.lifetime` markers, which `stage2Calls` resolves itself) leaves the
  memory alone, so its link is `WalkLink.pureCore`/`pureJumpCore` with
  `hmem : r.mem = s.mem` — no new transfer.  `WalkLink.callQuiet` is the
  transfer for a call that writes inside the frame: the memory clauses are the
  caller's four hypotheses (presence over the staged extents, silence at the
  log's extent, silence at the event trace's bytes, and the composed frame), and
  the five log fields and the trace read across it.
* **the class.**  The census splits F's nineteen by what the callee writes: the
  three `s2_value_pos` callers and the eight `lifetime`-only blocks write
  nothing, `if.then413.i` is a fourth `s2_value_pos` caller whose own store
  writes the token's kind byte inside its staged extent, `if.else334.i` and `if.then447.i` (through
  `s2_after_value`), `if.then109.i` (the same call at the dispatch's own depth
  register, `JsonStage2WalkFinal`) and `if.then19.i` (through `num_fast_el1`) write
  inside the frame and not at any word the invariant reads, `if.end256.i`'s own zero store
  is at `%outn.i`'s slot, and three write a record a cursor names:
  `if.then328.i`'s thirteen-byte event record is proved as the carry's link
  (below, `WalkLink.if_then328_i`), and `if.then425.i`'s appended record is its
  contract-driven companion (`JsonStage2WalkFinal`'s
  `WalkLink.if_then425_i_emit`/`_refuse`), so those two links are the carry's,
  not the frame's; and `z_arena_reserve.exit`'s decoded prefix in the arena is the
  third (`WalkLink.z_arena_reserve_exit`), the reservation its carry records.  `s2ScalarValuePost`'s second conjunct names the appended record,
  so `if.then425.i`'s call does not hide the trace's step behind the model's
  equation.
* **the terminal step.**  Neither finalisation arm is a `WalkLink`: the exit's and
  the refusal copy's stores are the record's, outside the walk's frame by design
  (`err_not_in_walkFrame`).  They are `step` equations —
  `walkExitBlock_denote` at the five markers and the two cursor copies,
  `walkIfThenBlock_denote`/`walkIfThen_step` at the refusal arm's same prefix and
  three copies, and
  `walkIfEnd_step` at either arm's `phi` value — and `WalkChain.finalisation`
  composes a chain to `s2_walk.exit` with them into a completion.
-/
import LeanLLVM.Refinement.JsonStage2WalkRest
import LeanLLVM.Refinement.JsonStage2WalkStore
import LeanLLVM.Refinement.JsonStage2Helpers

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonS1MasksIR

namespace WalkScope

/-! ### The call step

`evalInstr_call` is the semantics' own rule: the argument list is read by
`evalOperands` and the selection answers the value, the memory and the cursor.
`Step` is the same at `denoteCode`, and it is the step a call block's trace takes
whatever the arity — the per-shape lemmas `denoteCode_call5` and
`denoteCode_callVoid3` in `BlockEval` are instances of it, and the walk's helpers
are called at four, three, eight and five arguments. -/

/-- A void call adopts the callee's memory and cursor and binds nothing. -/
theorem walkEvalInstr_callVoid {calls : Calls} {s : State} {callee : String}
    {args : List (Ty × Operand)} {vs : List Value} {r : CallOutcome}
    (ha : evalOperands s args = some vs)
    (hc : calls callee vs s.mem s.next = some r) :
    evalInstr calls s (.callVoid callee args) =
      some { s with mem := r.mem, next := r.next } := by
  simp only [evalInstr, ha, hc]

/-- **The value-returning call, as a chain step**, at an arbitrary argument
list. -/
theorem walkDenoteCode_call {calls : Calls} (env : Env) (s : State) (d callee : String)
    {ty : Ty} {args : List (Ty × Operand)} {vs : List Value} {r : CallOutcome}
    (ha : evalOperands (stateAt env s) args = some vs)
    (hc : calls callee vs s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.call d ty callee args :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_call (s := stateAt env s) ha hc)]
  simp only [stateAt]

/-- **The void call, as a chain step**, at an arbitrary argument list. -/
theorem walkDenoteCode_callVoid {calls : Calls} (env : Env) (s : State)
    (callee : String) {args : List (Ty × Operand)} {vs : List Value} {r : CallOutcome}
    (ha : evalOperands (stateAt env s) args = some vs)
    (hc : calls callee vs s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.callVoid callee args :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (walkEvalInstr_callVoid (s := stateAt env s) ha hc)]
  simp only [stateAt]

/-! ### The argument lists

Each of the walk's calls passes registers and literals, and the values are the
ones the block's own loads and the invariant's bindings hold.  The lemmas below
read the list the emitted call passes; each is one `evalOperands` unfolding with
its operand lookups. -/

/-- The `s2_value_pos` argument list: the depth, the root flag, the two stacks. -/
theorem walkArgs_valuePos (env : Env) (s : State) {sp rd : BitVec 32} {ct cs : Nat}
    {rdp : String}
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hrd : lookupName env rdp = some (.int 32 rd))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs)) :
    evalOperands (stateAt env s)
        [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg rdp),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")] =
      some [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] := by
  simp only [evalOperands, stateAt, evalOperand, hsp, hrd, hct, hcs]

/-- The `s2_after_value` argument list: the depth, the root slot, the stacks. -/
theorem walkArgs_afterValue (env : Env) (s : State) {sp : BitVec 32} {rd ct cs : Nat}
    {spv : String}
    (hsp : lookupName env spv = some (.int 32 sp))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs)) :
    evalOperands (stateAt env s)
        [(Ty.int 32, Operand.reg spv), (Ty.ptr, Operand.reg "%root_done.i"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")] =
      some [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] := by
  simp only [evalOperands, stateAt, evalOperand, hsp, hrd, hct, hcs]

/-- The `od_scalar_value` argument list: the cursor record, the token, the log. -/
theorem walkArgs_scalarValue (env : Env) (s : State) {c t o : Nat}
    (hc : lookupName env "%c.i" = some (.ptr c))
    (ht : lookupName env "%t352.i" = some (.ptr t))
    (ho : lookupName env "%z" = some (.ptr o)) :
    evalOperands (stateAt env s)
        [(Ty.ptr, Operand.reg "%c.i"), (Ty.ptr, Operand.reg "%t352.i"),
         (Ty.ptr, Operand.reg "%z")] =
      some [.ptr c, .ptr t, .ptr o] := by
  simp only [evalOperands, stateAt, evalOperand, hc, ht, ho]

/-- The `num_fast_el1` argument list: the lexeme, its length, the two slots. -/
theorem walkArgs_numFast (env : Env) (s : State) {p out err : Nat} {n : BitVec 64}
    (hp : lookupName env "%arrayidx10.i" = some (.ptr p))
    (hn : lookupName env "%sub.i99" = some (.int 64 n))
    (ho : lookupName env "%d.i" = some (.ptr out))
    (he : lookupName env "%ei.i" = some (.ptr err)) :
    evalOperands (stateAt env s)
        [(Ty.ptr, Operand.reg "%arrayidx10.i"), (Ty.int 64, Operand.reg "%sub.i99"),
         (Ty.ptr, Operand.reg "%d.i"), (Ty.ptr, Operand.reg "%ei.i")] =
      some [.ptr p, .int 64 n, .ptr out, .ptr err] := by
  simp only [evalOperands, stateAt, evalOperand, hp, hn, ho, he]

/-- The `llvm.lifetime` argument list: the extent and the object. -/
theorem walkArgs_lifetime (env : Env) (s : State) (size : Nat) {p : Nat}
    {obj : String}
    (hp : lookupName env obj = some (.ptr p)) :
    evalOperands (stateAt env s)
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 size))),
         (Ty.ptr, Operand.reg obj)] =
      some [.int 64 (BitVec.ofNat 64 size), .ptr p] := by
  simp only [evalOperands, stateAt, evalOperand, hp]
  rfl

/-! ## The two `s2_value_pos` callers that branch on the test

`s2_value_pos` writes nothing (`s2ValuePosFoot` is the empty list) and hands the
caller's memory back (`s2ValuePosPost`'s `r.mem = mem`), so a block that calls it
is a **pure run** for the invariant: the four memory clauses are the block's own
`hmem = rfl` at the post, and the walk's frame and presence clauses do not move.
The two blocks below are that observation at their own traces. -/

/-- `if.then.i`: the assignment path's value-position test, `%9` read from the
root slot and the test on the callee's word. -/
def walkIfThenI : Block :=
  { name := "if.then.i",
    instrs := [
      Instr.load "%9" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call14.i" (Ty.int 32) "s2_value_pos"
        [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%9"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")],
      Instr.icmp "%tobool15.not.i" IPred.eq 32 (Operand.reg "%call14.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%tobool15.not.i") "if.then16.i" "if.end.i" }

theorem walkIfThenI_find : stage2Body.findBlock "if.then.i" = some walkIfThenI := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThenI]

/-- The block's run, through the callee's answer. -/
theorem walkIfThenI_denote {sub : Calls} (env : Env) (s : State)
    {root : Nat} {rd sp : BitVec 32} {ct cs : Nat} {r : CallOutcome} {x : BitVec 32}
    (hroot : lookupName env "%root_done.i" = some (.ptr root))
    (hread : readBytes s.mem root 4 = some (natToBytes rd.toNat 4))
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] s.mem s.next = some r)
    (hret : r.ret = .int 32 x) :
    denoteCode (stage2Calls sub) walkIfThenI.instrs (stateAt env s) =
      some (stateAt (cells [("%tobool15.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
        ("%call14.i", .int 32 x), ("%9", .int 32 rd)] env)
        { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThenI]
  rw [denoteCode_load_i32 (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%9") (p := "%root_done.i") hroot hread]
  rw [walkDenoteCode_call (calls := stage2Calls sub)
    (env := ("%9", .int 32 rd) :: env) (s := s) (d := "%call14.i")
    (callee := "s2_value_pos") (ty := Ty.int 32)
    (args := [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%9"),
      (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs]) (r := r) ?_ hcall]
  · rw [hret]
    rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
      (env := ("%call14.i", .int 32 x) :: ("%9", .int 32 rd) :: env)
      (s := { s with mem := r.mem, next := r.next })
      (d := "%tobool15.not.i") (a := "%call14.i") (w := 32) (x := x)
      (c := BitVec.ofNat 32 0) (by rfl)]
    rfl
  · refine walkArgs_valuePos (("%9", .int 32 rd) :: env) s ?_ ?_ ?_ ?_
    · simpa [lookupName] using hsp
    · rfl
    · simpa [lookupName] using hct
    · simpa [lookupName] using hcs

/-- **`if.then.i` is a link**: from the invariant, the callee's answer, and the
root slot's four bytes.  `s2_value_pos` writes nothing, so the target carry is
the same one at `if.then16.i` or `if.end.i`, whichever the test names. -/
theorem WalkLink.if_then_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then.i")
    {root : Nat} {rd x : BitVec 32}
    (hroot : lookupName s.env "%root_done.i" = some (.ptr root))
    (hread : readBytes s.mem root 4 = some (natToBytes rd.toNat 4))
    (hpre : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (hx : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r → r.ret = .int 32 x) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
          then "if.then16.i" else "if.end.i") } s' := by
  obtain ⟨r, hcall, hpost, -⟩ :=
    s2ValuePosContract.resolves (next := s.next) hpre
  obtain ⟨v, -, hret, hmem, -⟩ := hpost
  have hret' : r.ret = .int 32 x := hx r hcall
  have hcall' : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r := hcall
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIfThenI) (by rw [hblock]; exact walkIfThenI_find)
    (s₁ := stateAt (cells [("%tobool15.not.i",
        .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
      ("%call14.i", .int 32 x), ("%9", .int 32 rd)] s.env)
      { s with mem := r.mem, next := r.next })
    (walkIfThenI_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (root := root) (rd := rd) (sp := BitVec.ofNat 32 C.sp)
      (ct := C.stage.ctype) (cs := C.stage.cst)
      (r := r) (x := x) hroot hread hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall' hret')
    (by unfold walkCarried; decide) (by simpa [stateAt] using hmem) rfl rfl
    (by simp [cells, stateAt, lookupName_cons_self])
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-! ## The transfer for a call that writes inside the frame

Most of class F's calls write bytes the invariant does not read: a container
stack's byte, the root slot, `num_fast_el1`'s two allocated slots, a stage
object's own field.  What such a link owes is the frame (silence outside the
write extents, including the callee's footprint), presence over the staged
extents, and the five log words and the event trace read across the call.  The
four are the caller's hypotheses: the callee's `foot` is read from the arguments,
so whether a word is outside it is a fact about the staging, not about the
callee.

The one thing `HelperContract` does not supply is presence: `framed` says the
callee left the caller's bytes alone *outside* its footprint, and says nothing
about the bytes inside.  A callee that writes a staged object therefore owes the
caller a presence fact at that object, which each instance reads off the model's
own post (`stage2AfterValue`'s two arms are `writeBytes`, so a write's monotonicity
gives it). -/

/-- **A `s2_value_pos` call at the carried depth answers with the maps' word.**
The link's `ret` premise is this theorem at its own call, so the two clauses the
carry keeps are what the block's edge is read against. -/
theorem walkValuePos_ret {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) {r : CallOutcome} {rd : BitVec 32}
    (hsp0 : C.sp ≠ 0)
    (hpre : s2ValuePosPre [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r) :
    r.ret = .int 32 (BitVec.ofNat 32
      (if (C.tyMap (C.sp - 1)).toNat = 1 then
        (if (C.stMap (C.sp - 1)).toNat = 2 then 1 else 0)
      else (if (C.stMap (C.sp - 1)).toNat = 0 ∨ (C.stMap (C.sp - 1)).toNat = 2 then 1 else 0))) := by
  obtain ⟨v, hv, hret, -, -⟩ := s2ValuePos_sound hpre hcall
  have hsp : (BitVec.ofNat 32 C.sp).toNat = C.sp := walkAfterValue_sp h
  rw [hsp] at hv
  have hE := walkValuePos_answer (G := G) (C := C) (s := s) h
    (sp := C.sp) (rd := rd.toNat) hsp0 h.sp_le_wlen
  rw [hE] at hv
  have hEq : (if (C.tyMap (C.sp - 1)).toNat = 1 then
        (if (C.stMap (C.sp - 1)).toNat = 2 then 1 else 0)
      else (if (C.stMap (C.sp - 1)).toNat = 0 ∨ (C.stMap (C.sp - 1)).toNat = 2 then 1 else 0))
      = v := Option.some.inj hv
  rw [hEq]
  exact hret

/-- **A call's link, `br` shape.**  The target carry differs from the source only
in its block, so every clause that speaks about the carry's numbers is the
source's. -/
theorem WalkLink.callQuiet {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode (stage2Calls stage2SubCalls) B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hpc₁ : s₁.pc = s.pc)
    (hframe : UnchangedOutside m0 s₁.mem (walkWide G C))
    (howned : ∀ r ∈ walkStaged G C, HasBytes s₁.mem r.1 r.2)
    (hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes s₁.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w)
    (hev : readBytes s₁.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length)
    {TM SM : Nat → UInt8}
    (hstTy : WalkStackBytes s₁.mem C.stage.ctype TM C.wlen)
    (hstSt : WalkStackBytes s₁.mem C.stage.cst SM C.wlen)
    {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s₁ with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := t, tyMap := TM, stMap := SM } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s'' : State := { s₁ with pc := t, pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s'' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s'']
    rw [hpc₁]
  refine ⟨s'', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by dsimp only [s'']; exact hstTy
      stBytes := by dsimp only [s'']; exact hstSt
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := howned
      frame := by dsimp only [s'']; exact hframe
      blockLocal := by dsimp only [s'']; exact hloc }
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s s₁ hden]
    exact hInv.blockIndex
  · dsimp only [s'']
    rw [hev]
    exact hInv.evBytes
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s s₁ hden]
    exact hInv.depth_reg
  · dsimp only [s'']
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s'']
    exact WalkRegs.of_run hInv.regs hfree hden
  · dsimp only [s'']
    exact WalkIter.of_run hInv.iter hfree hden
  · dsimp only [s'']
    rw [hlog 32 4 (by decide)]
    exact hInv.log_hash
  · dsimp only [s'']
    rw [hlog 8 8 (by decide)]
    exact hInv.log_len
  · dsimp only [s'']
    rw [hlog 16 8 (by decide)]
    exact hInv.log_cap
  · dsimp only [s'']
    rw [hlog 48 8 (by decide)]
    exact hInv.log_alen
  · dsimp only [s'']
    rw [hlog 56 8 (by decide)]
    exact hInv.log_acap

/-- **A call's link, `condbr` shape**: the branch is on a bit the run bound (the
callee's answer, usually) or on a carried register. -/
theorem WalkLink.callQuietBr {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode (stage2Calls stage2SubCalls) B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hpc₁ : s₁.pc = s.pc)
    (hframe : UnchangedOutside m0 s₁.mem (walkWide G C))
    (howned : ∀ r ∈ walkStaged G C, HasBytes s₁.mem r.1 r.2)
    (hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes s₁.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w)
    (hev : readBytes s₁.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length)
    {TM SM : Nat → UInt8}
    (hstTy : WalkStackBytes s₁.mem C.stage.ctype TM C.wlen)
    (hstSt : WalkStackBytes s₁.mem C.stage.cst SM C.wlen)
    {d tl fl : String} (hterm : B.term = Term.condbr (.reg d) tl fl)
    {bit : BitVec 1} (hbit : lookupName s₁.env d = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s₁ with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s₁ with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := (if bit = 1 then tl else fl), tyMap := TM, stMap := SM } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s'' : State := { s₁ with pc := (if bit = 1 then tl else fl), pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s'' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := d) (tl := tl) (fl := fl) (bit := bit) hbit]
    dsimp only [s'']
    rw [hpc₁]
  refine ⟨s'', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by dsimp only [s'']; exact hstTy
      stBytes := by dsimp only [s'']; exact hstSt
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := howned
      frame := by dsimp only [s'']; exact hframe
      blockLocal := ?_ }
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s s₁ hden]
    exact hInv.blockIndex
  · dsimp only [s'']
    rw [hev]
    exact hInv.evBytes
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s s₁ hden]
    exact hInv.depth_reg
  · dsimp only [s'']
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s'']
    exact WalkRegs.of_run hInv.regs hfree hden
  · dsimp only [s'']
    exact WalkIter.of_run hInv.iter hfree hden
  · dsimp only [s'']
    rw [hlog 32 4 (by decide)]
    exact hInv.log_hash
  · dsimp only [s'']
    rw [hlog 8 8 (by decide)]
    exact hInv.log_len
  · dsimp only [s'']
    rw [hlog 16 8 (by decide)]
    exact hInv.log_cap
  · dsimp only [s'']
    rw [hlog 48 8 (by decide)]
    exact hInv.log_alen
  · dsimp only [s'']
    rw [hlog 56 8 (by decide)]
    exact hInv.log_acap
  · dsimp only [s'']
    by_cases ht : bit = 1
    · rw [ite_eq_left ht]; exact hl
    · rw [ite_eq_right ht]; exact hf

/-- **The quiet block's step, with the record in flight replaced.**  `if.end256.i`
computes the token's entry position, its document extent and the arena offset the
body will be reserved at, so the block that makes those three numbers is where the
record enters the carry: `walkArenaReserve_clear` then reads the check's premises
of a `pending` some link actually set.  The shape is `callQuietBr`'s with the
target's `pending` replaced, and the three clauses that value owes supplied beside
it. -/
theorem WalkLink.callQuietBrPending {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode (stage2Calls stage2SubCalls) B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hpc₁ : s₁.pc = s.pc)
    (hframe : UnchangedOutside m0 s₁.mem (walkWide G C))
    (howned : ∀ r ∈ walkStaged G C, HasBytes s₁.mem r.1 r.2)
    (hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes s₁.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w)
    (hev : readBytes s₁.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length)
    {TM SM : Nat → UInt8}
    (hstTy : WalkStackBytes s₁.mem C.stage.ctype TM C.wlen)
    (hstSt : WalkStackBytes s₁.mem C.stage.cst SM C.wlen)
    {d tl fl : String} (hterm : B.term = Term.condbr (.reg d) tl fl)
    {bit : BitVec 1} (hbit : lookupName s₁.env d = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s₁ with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s₁ with pc := fl, pre := some s.pc })
    {p off ext : Nat} (hoff : off ≤ C.alen) (hpn : p < G.n)
    (hcur : C.alen ≤ G.ndst0 + p) (hlen : p + ext ≤ G.n) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := (if bit = 1 then tl else fl), pending := some (p, off, ext),
      tyMap := TM, stMap := SM } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s'' : State := { s₁ with pc := (if bit = 1 then tl else fl), pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s'' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := d) (tl := tl) (fl := fl) (bit := bit) hbit]
    dsimp only [s'']
    rw [hpc₁]
  refine ⟨s'', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := ?_
      pending_len := ?_
      pending_cursor := ?_
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by dsimp only [s'']; exact hstTy
      stBytes := by dsimp only [s'']; exact hstSt
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := howned
      frame := by dsimp only [s'']; exact hframe
      blockLocal := ?_ }
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s s₁ hden]
    exact hInv.blockIndex
  · dsimp only [s'']
    rw [hev]
    exact hInv.evBytes
  · intro p' off' len' hp'
    simp only [Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl, rfl⟩ := hp'
    exact ⟨hoff, hpn⟩
  · intro p' off' len' hp'
    simp only [Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl, rfl⟩ := hp'
    exact hlen
  · intro p' off' len' hp'
    simp only [Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl, rfl⟩ := hp'
    exact hcur
  · rw [denoteCode_lookupName (stage2Calls stage2SubCalls) B.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s s₁ hden]
    exact hInv.depth_reg
  · dsimp only [s'']
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s'']
    exact WalkRegs.of_run hInv.regs hfree hden
  · dsimp only [s'']
    exact WalkIter.of_run hInv.iter hfree hden
  · dsimp only [s'']
    rw [hlog 32 4 (by decide)]
    exact hInv.log_hash
  · dsimp only [s'']
    rw [hlog 8 8 (by decide)]
    exact hInv.log_len
  · dsimp only [s'']
    rw [hlog 16 8 (by decide)]
    exact hInv.log_cap
  · dsimp only [s'']
    rw [hlog 48 8 (by decide)]
    exact hInv.log_alen
  · dsimp only [s'']
    rw [hlog 56 8 (by decide)]
    exact hInv.log_acap
  · dsimp only [s'']
    by_cases ht : bit = 1
    · rw [ite_eq_left ht]; exact hl
    · rw [ite_eq_right ht]; exact hf

/-! ## The `llvm.lifetime` blocks

`stage2Calls` resolves the two markers itself — a live-range marker reads no
value and writes no byte — so a marker call is a step that returns the state it
was handed, and a block of nothing but markers is a pure run.  Six of class F's
nineteen are that shape, at the four `alloca`s and the three stage objects the
`entry` block's markers cover. -/

/-- **A lifetime marker's step**: the state it was handed. -/
theorem walkDenoteCode_lifetimeEnd {sub : Calls} (env : Env) (s : State)
    {size : Nat} {p : Nat} {obj : String}
    (hp : lookupName env obj = some (.ptr p)) (is : List Instr) :
    denoteCode (stage2Calls sub)
        (Instr.callVoid "llvm.lifetime.end.p0"
          [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 size))),
           (Ty.ptr, Operand.reg obj)] :: is) (stateAt env s) =
      denoteCode (stage2Calls sub) is (stateAt env s) := by
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := "llvm.lifetime.end.p0")
    (args := [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 size))),
      (Ty.ptr, Operand.reg obj)])
    (vs := [.int 64 (BitVec.ofNat 64 size), .ptr p])
    (r := ⟨.int 1 0, s.mem, s.next⟩)
    (walkArgs_lifetime env s size hp) rfl is]

/-- The same marker, under the `start` name. -/
theorem walkDenoteCode_lifetimeStart {sub : Calls} (env : Env) (s : State)
    {size : Nat} {p : Nat} {obj : String}
    (hp : lookupName env obj = some (.ptr p)) (is : List Instr) :
    denoteCode (stage2Calls sub)
        (Instr.callVoid "llvm.lifetime.start.p0"
          [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 size))),
           (Ty.ptr, Operand.reg obj)] :: is) (stateAt env s) =
      denoteCode (stage2Calls sub) is (stateAt env s) := by
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := "llvm.lifetime.start.p0")
    (args := [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 size))),
      (Ty.ptr, Operand.reg obj)])
    (vs := [.int 64 (BitVec.ofNat 64 size), .ptr p])
    (r := ⟨.int 1 0, s.mem, s.next⟩)
    (walkArgs_lifetime env s size hp) rfl is]

/-- `cleanup339.critedge.i`: the decoder's output slot is released on the path
that leaves the arena reserve. -/
def walkCleanup339 : Block :=
  { name := "cleanup339.critedge.i",
    instrs := [Instr.callVoid "llvm.lifetime.end.p0"
      [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 8))),
       (Ty.ptr, Operand.reg "%outn.i")]],
    term := Term.br "if.then" }

theorem walkCleanup339_find :
    stage2Body.findBlock "cleanup339.critedge.i" = some walkCleanup339 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCleanup339]

theorem WalkLink.cleanup339_critedge_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup339.critedge.i")
    (houtn : lookupName s.env "%outn.i" = some (.ptr (G.next0 + 20))) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "if.then" } s' := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkCleanup339.instrs (stateAt s.env s) =
      some (stateAt s.env s) := by
    simp only [walkCleanup339]
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 8) (obj := "%outn.i") houtn]
    rfl
  refine WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkCleanup339) (by rw [hblock]; exact walkCleanup339_find)
    (s₁ := stateAt s.env s) ?_ (by unfold walkCarried; decide) rfl rfl rfl
    (by simp [WalkLocal])
  rw [← stateAt_self s]
  exact hden

/-- `if.end67.critedge.i`: the number path's two allocated slots are released. -/
def walkIfEnd67Critedge : Block :=
  { name := "if.end67.critedge.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 8))),
         (Ty.ptr, Operand.reg "%ei.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 8))),
         (Ty.ptr, Operand.reg "%d.i")]],
    term := Term.br "if.end67.i" }

theorem walkIfEnd67Critedge_find :
    stage2Body.findBlock "if.end67.critedge.i" = some walkIfEnd67Critedge := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfEnd67Critedge]

theorem WalkLink.if_end67_critedge_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end67.critedge.i")
    (hei : lookupName s.env "%ei.i" = some (.ptr (G.next0 + 8)))
    (hd : lookupName s.env "%d.i" = some (.ptr C.stage.d)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "if.end67.i" } s' := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfEnd67Critedge.instrs
      (stateAt s.env s) = some (stateAt s.env s) := by
    simp only [walkIfEnd67Critedge]
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 8) (obj := "%ei.i") hei]
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 8) (obj := "%d.i") hd]
    rfl
  refine WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkIfEnd67Critedge) (by rw [hblock]; exact walkIfEnd67Critedge_find)
    (s₁ := stateAt s.env s) ?_ (by unfold walkCarried; decide) rfl rfl rfl
    (by simp [WalkLocal])
  rw [← stateAt_self s]
  exact hden

/-- `if.end473.i`: the scalar token is released after the extra-token scan. -/
def walkIfEnd473 : Block :=
  { name := "if.end473.i",
    instrs := [Instr.callVoid "llvm.lifetime.end.p0"
      [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
       (Ty.ptr, Operand.reg "%t352.i")]],
    term := Term.br "cleanup478.i" }

theorem walkIfEnd473_find : stage2Body.findBlock "if.end473.i" = some walkIfEnd473 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfEnd473]

theorem WalkLink.if_end473_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end473.i")
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "cleanup478.i" } s' := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfEnd473.instrs
      (stateAt s.env s) = some (stateAt s.env s) := by
    simp only [walkIfEnd473]
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 24) (obj := "%t352.i") htok]
    rfl
  refine WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkIfEnd473) (by rw [hblock]; exact walkIfEnd473_find)
    (s₁ := stateAt s.env s) ?_ (by unfold walkCarried; decide) rfl rfl rfl
    (by simp [WalkLocal])
  rw [← stateAt_self s]
  exact hden

/-- `cleanup474.i`: the scalar token is released on the refusal path. -/
def walkCleanup474 : Block :=
  { name := "cleanup474.i",
    instrs := [Instr.callVoid "llvm.lifetime.end.p0"
      [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
       (Ty.ptr, Operand.reg "%t352.i")]],
    term := Term.br "if.then" }

theorem walkCleanup474_find : stage2Body.findBlock "cleanup474.i" = some walkCleanup474 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCleanup474]

theorem WalkLink.cleanup474_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup474.i")
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "if.then" } s' := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkCleanup474.instrs
      (stateAt s.env s) = some (stateAt s.env s) := by
    simp only [walkCleanup474]
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 24) (obj := "%t352.i") htok]
    rfl
  refine WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkCleanup474) (by rw [hblock]; exact walkCleanup474_find)
    (s₁ := stateAt s.env s) ?_ (by unfold walkCarried; decide) rfl rfl rfl
    (by simp [WalkLocal])
  rw [← stateAt_self s]
  exact hden

/-! ## The second `s2_value_pos` caller

`if.then219.i` reads the root flag and calls the same test, but branches on the
depth rather than on the callee's word: the value-position test decides whether a
record is owed, and the depth decides whether one is in flight. -/

/-- `if.then219.i`: the record path's value-position test. -/
def walkIfThen219I : Block :=
  { name := "if.then219.i",
    instrs := [
      Instr.load "%26" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call222.i" (Ty.int 32) "s2_value_pos"
        [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%26"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")],
      Instr.icmp "%cmp223.not.i" IPred.eq 32 (Operand.reg "%sp.i.0248")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%cmp223.not.i") "if.end245.i" "land.lhs.true.i" }

theorem walkIfThen219I_find : stage2Body.findBlock "if.then219.i" = some walkIfThen219I := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen219I]

theorem walkIfThen219I_denote {sub : Calls} (env : Env) (s : State)
    {root ct cs : Nat} {rd sp : BitVec 32} {r : CallOutcome} {x : BitVec 32}
    (hroot : lookupName env "%root_done.i" = some (.ptr root))
    (hread : readBytes s.mem root 4 = some (natToBytes rd.toNat 4))
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_value_pos"
      [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] s.mem s.next = some r)
    (hret : r.ret = .int 32 x) :
    denoteCode (stage2Calls sub) walkIfThen219I.instrs (stateAt env s) =
      some (stateAt (cells [("%cmp223.not.i", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))),
        ("%call222.i", .int 32 x), ("%26", .int 32 rd)] env)
        { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen219I]
  rw [denoteCode_load_i32 (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%26") (p := "%root_done.i") hroot hread]
  rw [walkDenoteCode_call (calls := stage2Calls sub)
    (env := ("%26", .int 32 rd) :: env) (s := s) (d := "%call222.i")
    (callee := "s2_value_pos") (ty := Ty.int 32)
    (args := [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%26"),
      (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs]) (r := r) ?_ hcall]
  · rw [hret]
    rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
      (env := ("%call222.i", .int 32 x) :: ("%26", .int 32 rd) :: env)
      (s := { s with mem := r.mem, next := r.next })
      (d := "%cmp223.not.i") (a := "%sp.i.0248") (w := 32) (x := sp)
      (c := BitVec.ofNat 32 0) (by simpa [lookupName] using hsp)]
    rfl
  · refine walkArgs_valuePos (("%26", .int 32 rd) :: env) s ?_ ?_ ?_ ?_
    · simpa [lookupName] using hsp
    · rfl
    · simpa [lookupName] using hct
    · simpa [lookupName] using hcs

theorem WalkLink.if_then219_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then219.i")
    {root : Nat} {rd x : BitVec 32}
    (hroot : lookupName s.env "%root_done.i" = some (.ptr root))
    (hread : readBytes s.mem root 4 = some (natToBytes rd.toNat 4))
    (hpre : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (hx : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r → r.ret = .int 32 x) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1
          then "if.end245.i" else "land.lhs.true.i") } s' := by
  obtain ⟨r, hcall, hpost, -⟩ :=
    s2ValuePosContract.resolves (next := s.next) hpre
  obtain ⟨v, -, hret, hmem, -⟩ := hpost
  have hret' : r.ret = .int 32 x := hx r hcall
  have hcall' : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r := hcall
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIfThen219I) (by rw [hblock]; exact walkIfThen219I_find)
    (s₁ := stateAt (cells [("%cmp223.not.i",
        .int 1 (evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0))),
      ("%call222.i", .int 32 x), ("%26", .int 32 rd)] s.env)
      { s with mem := r.mem, next := r.next })
    (walkIfThen219I_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (root := root) (rd := rd) (sp := BitVec.ofNat 32 C.sp)
      (ct := C.stage.ctype) (cs := C.stage.cst)
      (r := r) (x := x) hroot hread hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall' hret')
    (by unfold walkCarried; decide) (by simpa [stateAt] using hmem) rfl rfl
    (by simp [cells, stateAt, lookupName_cons_self])
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-! ## `s2_after_value`: one flag or one stack byte

The callee's model writes one of two places — the root slot at depth zero and the
top container's state byte above it (`stage2AfterValue`) — and both are inside the
walk's frame: the root slot is the first allocated slot and the byte is inside
`%cst.i`'s staged extent.  What the link consumes is the model's own shape.

The helpers below are that shape's three facts: presence under either arm, and the
silence a single write inside a staged object leaves at the log and at the event
trace. -/

/-- The root slot is in the frame: it is the first allocated slot, four bytes
wide. -/
theorem walkWide_rootSlot {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} :
    ∃ w ∈ walkWide G C, w.1 ≤ G.next0 + 8 ∧ G.next0 + 8 + 4 ≤ w.1 + w.2 :=
  ⟨(G.next0 + 8, 4),
    by simp [walkWide, walkPresent, stage2ReportScratch, stage2AllocaWrites],
    le_rfl, le_rfl⟩

/-- A byte of the state stack is in the frame. -/
theorem walkWide_cst_byte {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {q : Nat}
    (hq : q + 1 ≤ stage2StackExtent) :
    ∃ w ∈ walkWide G C, w.1 ≤ C.stage.cst + q ∧ C.stage.cst + q + 1 ≤ w.1 + w.2 := by
  refine ⟨(C.stage.cst, stage2StackExtent),
    by simp [walkWide, walkPresent, stage2ReportScratch, stage2StagedWrites],
    by omega, ?_⟩
  have h520 : stage2StackExtent = 520 := rfl
  rw [h520] at hq ⊢
  omega

/-- **The carried depth's top byte is inside the state stack**, so the byte is a
stack byte and the stack's two separations apply to it. -/
theorem cstByte_le {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    (BitVec.ofNat 32 C.sp).toNat - 1 + 1 ≤ stage2StackExtent := by
  have hcap := hInv.depth_cap
  have h520 : stage2StackExtent = 520 := rfl
  rw [h520] at hcap ⊢
  have hle : (BitVec.ofNat 32 C.sp).toNat ≤ 520 := by
    rw [BitVec.toNat_ofNat]
    omega
  omega

/-- The state stack's top byte is separated from the log. -/
theorem cstByte_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) + 1 ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) := by
  have hsep := cst_log_sep hInv
  have hb := cstByte_le hInv
  simp only [stage2StackExtent, stage2LogExtent] at hsep
  rw [show stage2LogExtent = 64 from rfl]
  rcases hsep with hsep | hsep
  · left
    have : (BitVec.ofNat 32 C.sp).toNat - 1 + 1 ≤ 520 := hb
    omega
  · right
    have hle : C.stage.cst ≤ C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) :=
      Nat.le_add_right _ _
    omega

/-- The state stack's top byte is separated from the event stream. -/
theorem cstByte_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) + 1 ≤ G.ev ∨
      G.ev + G.evcap ≤ C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) := by
  have hsep := cst_ev_sep hInv
  have hb := cstByte_le hInv
  simp only [stage2StackExtent] at hsep
  rcases hsep with hsep | hsep
  · left
    have : (BitVec.ofNat 32 C.sp).toNat - 1 + 1 ≤ 520 := hb
    omega
  · right
    have hle : C.stage.cst ≤ C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1) :=
      Nat.le_add_right _ _
    omega

/-- The two arms of `stage2AfterValue`'s write. -/
theorem stage2AfterValue_form {mem m : Mem} {sp rd ct cs : Nat}
    (h : stage2AfterValue mem sp rd ct cs = some m) :
    m = writeBytes mem rd (wordBytes 4 1) ∨
      ∃ b : UInt8, m = writeBytes mem (cs + (sp - 1)) [b] := by
  unfold stage2AfterValue at h
  split at h
  · exact Or.inl (Option.some.inj h).symm
  · split at h
    · exact Or.inr ⟨_, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-- A write separated from the log leaves every read inside it alone. -/
theorem walkReadBytes_log_of_write {m : Mem} {z a w off w' : Nat} {bs : List UInt8}
    (hlen : bs.length ≤ w) (hsep : a + w ≤ z ∨ z + stage2LogExtent ≤ a)
    (hsub : off + w' ≤ stage2LogExtent) :
    readBytes (writeBytes m a bs) (z + off) w' = readBytes m (z + off) w' := by
  refine walkReadBytes_writeBytes_outside (start := a) ?_
  have hlen' : bs.length ≤ w := hlen
  rcases hsep with h | h
  · right; omega
  · left; omega

/-- A write separated from the event stream leaves a read of its written prefix
alone. -/
theorem walkReadBytes_ev_of_write {m : Mem} {ev a w N : Nat} {bs : List UInt8}
    (hlen : bs.length ≤ w) (hsep : a + w ≤ ev ∨ ev + N ≤ a) :
    readBytes (writeBytes m a bs) ev N = readBytes m ev N := by
  refine walkReadBytes_writeBytes_outside (start := a) ?_
  have hlen' : bs.length ≤ w := hlen
  rcases hsep with h | h
  · right; omega
  · left; omega

/-- `if.else334.i`: the container is closed on the refusal path. -/
def walkIfElse334 : Block :=
  { name := "if.else334.i",
    instrs := [Instr.callVoid "s2_after_value"
      [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.ptr, Operand.reg "%root_done.i"),
       (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")]],
    term := Term.br "cleanup478.i" }

theorem walkIfElse334_find : stage2Body.findBlock "if.else334.i" = some walkIfElse334 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfElse334]

theorem walkIfElse334_denote {sub : Calls} (env : Env) (s : State)
    {sp : BitVec 32} {rd ct cs : Nat} {r : CallOutcome}
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_after_value"
      [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] s.mem s.next = some r) :
    denoteCode (stage2Calls sub) walkIfElse334.instrs (stateAt env s) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfElse334]
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := "s2_after_value")
    (args := [(Ty.int 32, Operand.reg "%sp.i.0248"),
      (Ty.ptr, Operand.reg "%root_done.i"), (Ty.ptr, Operand.reg "%ctype.i"),
      (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 sp, .ptr rd, .ptr ct, .ptr cs]) (r := r)
    (walkArgs_afterValue env s hsp hrd hct hcs) hcall []]
  rfl

/-- **`s2_after_value`'s four memory facts**, at the walk's staging: the frame
across the write, presence over the staged extents, the five log words, and the
event trace.  The model's two arms are writes (`stage2AfterValue_form`), so
presence and the frame are `hasBytes_writeBytes` and the staging's separation; the
depth-zero arm's root slot is outside the log and the stream by the caller's two
facts (`hroot`, `hrootev`), because the staging does not place the seven appended
objects relative to the alloca cursor. -/
theorem walkAfterValue_facts {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s)
    {m : Mem}
    (hm : stage2AfterValue s.mem (BitVec.ofNat 32 C.sp).toNat (G.next0 + 8)
      C.stage.ctype C.stage.cst = some m)
    (hfr : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)) :
    UnchangedOutside m0 m (walkWide G C) ∧
      (∀ q ∈ walkStaged G C, HasBytes m q.1 q.2) ∧
      (∀ off w, off + w ≤ stage2LogExtent →
        readBytes m (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w) ∧
      readBytes m (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length =
        readBytes s.mem (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length := by
  have hroot : G.next0 + 8 + 4 ≤ C.stage.z ∨ C.stage.z + stage2LogExtent ≤ G.next0 + 8 :=
    C.stage.rootSlot_log
  have hrootev : G.next0 + 8 + 4 ≤ G.ev + G.nev0 ∨ G.ev + G.evcap ≤ G.next0 + 8 :=
    C.stage.rootSlot_ev
  have hsp0 : (BitVec.ofNat 32 C.sp).toNat = C.sp := by
    have hcap := hInv.depth_cap
    simp only [stage2StackExtent] at hcap
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfoot : s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next =
      (if (BitVec.ofNat 32 C.sp).toNat = 0 then [(G.next0 + 8, 4)]
       else [(C.stage.cst + ((BitVec.ofNat 32 C.sp).toNat - 1), 1)]) := by
    simp [s2AfterValueFoot]
  have hsub : ∀ q ∈ s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next,
      ∃ w ∈ walkWide G C, w.1 ≤ q.1 ∧ q.1 + q.2 ≤ w.1 + w.2 := by
    intro q hq
    rw [hfoot] at hq
    by_cases h0 : (BitVec.ofNat 32 C.sp).toNat = 0
    · rw [ite_eq_left h0] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact walkWide_rootSlot
    · rw [ite_eq_right h0] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact walkWide_cst_byte (q := (BitVec.ofNat 32 C.sp).toNat - 1) (cstByte_le hInv)
  have hevcap : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  have hframe : UnchangedOutside m0 m (walkWide G C) :=
    hInv.frame.trans' (UnchangedOutside.of_subset hfr hsub)
  have howned : ∀ q ∈ walkStaged G C, HasBytes m q.1 q.2 := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]; exact walkStaged_write rfl hInv.owned
    · rw [h1]; exact walkStaged_write rfl hInv.owned
  have hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes m (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w := by
    intro off w hsubw
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]
      refine walkReadBytes_log_of_write (w := 4) (by simp [wordBytes, natToBytes_length])
        ?_ hsubw
      simpa [wordBytes, natToBytes_length] using hroot
    · rw [h1]
      exact walkReadBytes_log_of_write (w := 1) (by simp) (cstByte_log_sep hInv) hsubw
  have hev : readBytes m (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]
      refine walkReadBytes_ev_of_write (w := 4) (by simp [wordBytes, natToBytes_length]) ?_
      rcases hrootev with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rw [h1]
      refine walkReadBytes_ev_of_write (w := 1) (by simp) ?_
      rcases cstByte_ev_sep hInv with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  exact ⟨hframe, howned, hlog, hev⟩

/-- **`if.else334.i` is a link**: the container's state advances and the walk
returns to the loop head. -/
theorem WalkLink.if_else334_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.else334.i")
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hpre : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := "cleanup478.i", stMap := walkAfterValueMap C } s' := by
  obtain ⟨r, hcall, hpost, hfr⟩ :=
    s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  have hfr' : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) := by
    rw [hmem] at hfr; exact hfr
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkAfterValue_facts (G := G) (C := C) (s := s) hInv hm hfr'
  have hstTy : WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen := by
    rw [hmem]
    exact walkAfterValue_tyBytesAt (G := G) (C := C) (s := s) hInv
      (sp := C.sp) hInv.depth_cap (walkAfterValue_sp hInv ▸ hm)
  have hstSt : WalkStackBytes r.mem C.stage.cst (walkAfterValueMap C) C.wlen := by
    rw [hmem]
    have hspw : C.sp = 0 ∨ C.sp - 1 < C.wlen := by
      by_cases h0 : C.sp = 0
      · exact Or.inl h0
      · exact Or.inr (by have := hInv.sp_le_wlen; omega)
    exact walkAfterValue_stBytesAt (G := G) (C := C) (s := s) hInv
      (sp := C.sp) hInv.depth_cap hspw (walkAfterValue_sp hInv ▸ hm)
  refine WalkLink.callQuiet (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := walkAfterValueMap C) (hstTy := hstTy) (hstSt := hstSt)
    (B := walkIfElse334) (by rw [hblock]; exact walkIfElse334_find)
    (s₁ := stateAt s.env { s with mem := r.mem, next := r.next })
    (walkIfElse334_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (sp := BitVec.ofNat 32 C.sp) (rd := G.next0 + 8)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r)
      hInv.depth_reg hrd (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall)
    (by unfold walkCarried; decide) rfl
    (by dsimp only [stateAt]; rw [hmem]; exact hframe)
    (by dsimp only [stateAt]; rw [hmem]; exact howned)
    (by dsimp only [stateAt]; rw [hmem]; exact hlog)
    (by dsimp only [stateAt]; rw [hmem]; exact hev)
    rfl (by simp [WalkLocal])
/-- `if.then447.i`: the string record is appended and the escape scan is entered
when the scan's counter is short of the bound. -/
def walkIfThen447I : Block :=
  { name := "if.then447.i",
    instrs := [
      Instr.callVoid "s2_after_value"
        [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.ptr, Operand.reg "%root_done.i"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")],
      Instr.icmp "%cmp451.i" IPred.ult 64 (Operand.reg "%ee.1.i") (Operand.reg "%cond350.i")],
    term := Term.condbr (Operand.reg "%cmp451.i") "land.rhs457.i" "if.end473.i" }

theorem walkIfThen447I_find : stage2Body.findBlock "if.then447.i" = some walkIfThen447I := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen447I]

theorem walkIfThen447I_denote {sub : Calls} (env : Env) (s : State)
    {sp : BitVec 32} {rd ct cs : Nat} {r : CallOutcome}
    {ei cd : Nat}
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_after_value"
      [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] s.mem s.next = some r)
    (hei : lookupName env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)))
    (hcd : lookupName env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd))) :
    denoteCode (stage2Calls sub) walkIfThen447I.instrs (stateAt env s) =
      some (stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult
        (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)))] env)
        { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen447I]
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := "s2_after_value")
    (args := [(Ty.int 32, Operand.reg "%sp.i.0248"),
      (Ty.ptr, Operand.reg "%root_done.i"), (Ty.ptr, Operand.reg "%ctype.i"),
      (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 sp, .ptr rd, .ptr ct, .ptr cs]) (r := r)
    (walkArgs_afterValue env s hsp hrd hct hcs) hcall]
  rw [denoteCode_icmp_reg_w (calls := stage2Calls sub)
    (env := env) (s := { s with mem := r.mem, next := r.next })
    (d := "%cmp451.i") (a := "%ee.1.i") (b := "%cond350.i") IPred.ult (w := 64)
    (x := BitVec.ofNat 64 ei) (y := BitVec.ofNat 64 cd) hei hcd]
  rfl

/-- **`if.then447.i` is a link**: the string record's container is closed and the
scan's next step is decided. -/
theorem WalkLink.if_then447_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then447.i")
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hpre : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {ei cd : Nat}
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hinner : cd - ei ≤ C.inner) (hlt : ei < cd)
    (hcd64 : cd < 2 ^ 64) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
          then "land.rhs457.i" else "if.end473.i"),
      stMap := walkAfterValueMap C } s' := by
  obtain ⟨r, hcall, hpost, hfr⟩ :=
    s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  have hfr' : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) := by
    rw [hmem] at hfr; exact hfr
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkAfterValue_facts (G := G) (C := C) (s := s) hInv hm hfr'
  have hstTy : WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen := by
    rw [hmem]
    exact walkAfterValue_tyBytesAt (G := G) (C := C) (s := s) hInv
      (sp := C.sp) hInv.depth_cap (walkAfterValue_sp hInv ▸ hm)
  have hstSt : WalkStackBytes r.mem C.stage.cst (walkAfterValueMap C) C.wlen := by
    rw [hmem]
    have hspw : C.sp = 0 ∨ C.sp - 1 < C.wlen := by
      by_cases h0 : C.sp = 0
      · exact Or.inl h0
      · exact Or.inr (by have := hInv.sp_le_wlen; omega)
    exact walkAfterValue_stBytesAt (G := G) (C := C) (s := s) hInv
      (sp := C.sp) hInv.depth_cap hspw (walkAfterValue_sp hInv ▸ hm)
  refine WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := walkAfterValueMap C) (hstTy := hstTy) (hstSt := hstSt)
    (B := walkIfThen447I) (by rw [hblock]; exact walkIfThen447I_find)
    (s₁ := stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult
        (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)))] s.env)
      { s with mem := r.mem, next := r.next })
    (walkIfThen447I_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (sp := BitVec.ofNat 32 C.sp) (rd := G.next0 + 8)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r) (ei := ei) (cd := cd)
      hInv.depth_reg hrd (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hei hcd)
    (by unfold walkCarried; decide) rfl
    (by dsimp only [stateAt]; rw [hmem]; exact hframe)
    (by dsimp only [stateAt]; rw [hmem]; exact howned)
    (by dsimp only [stateAt]; rw [hmem]; exact hlog)
    (by dsimp only [stateAt]; rw [hmem]; exact hev)
    rfl (by simp [cells, stateAt, lookupName_cons_self])
    (by
      right
      exact ⟨ei, cd, hinner, hlt, hcd64, by rw [hInv.pc_eq, hblock],
        by simpa [stateAt, cells, lookupName] using hei,
        by simpa [stateAt, cells, lookupName] using hcd⟩)
    (by simp [WalkLocal])


/-- **`if.then447.i`'s target, with the helper's answer named.**  The copy block's consumer:
`s2_after_value`'s contract resolves at the staging, and the link's target is the state the
block's `denoteCode` leaves — the test's cell at the answer's memory.  The carry changes
`stMap` (`walkAfterValueMap`), which the link's conclusion already names. -/
theorem walkIfThen447_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then447.i")
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hpre : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {ei cd : Nat}
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hinner : cd - ei ≤ C.inner) (hlt : ei < cd) (hcd64 : cd < 2 ^ 64) :
    ∃ (r : CallOutcome) (s' : State),
      stage2Calls stage2SubCalls "s2_after_value"
        [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r ∧
      WalkLink (stage2Calls stage2SubCalls) G C s
        { C with
          block := (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
            then "land.rhs457.i" else "if.end473.i")
          stMap := walkAfterValueMap C } s' ∧
      s' = TailS₃ s r ei cd := by
  obtain ⟨r, hcall, hpost, -⟩ := s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨s', hl⟩ := WalkLink.if_then447_i (G := G) (C := C) (s := s) hInv hblock hrd hpre
    hei hcd hinner hlt hcd64
  refine ⟨r, s', hcall, hl, ?_⟩
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen447I.instrs s =
      some (stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult (BitVec.ofNat 64 ei)
        (BitVec.ofNat 64 cd))) ] s.env) { s with mem := r.mem, next := r.next }) := by
    simpa only [stateAt] using (walkIfThen447I_denote (sub := stage2SubCalls) (env := s.env)
      (s := s) (sp := BitVec.ofNat 32 C.sp) (rd := G.next0 + 8) (ct := C.stage.ctype)
      (cs := C.stage.cst) (r := r) (ei := ei) (cd := cd) hInv.depth_reg hrd
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hei hcd)
  have hbit : lookupName (stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult
      (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd))) ] s.env)
      { s with mem := r.mem, next := r.next }).env "%cmp451.i" =
      some (.int 1 (evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd))) := by
    simp only [stateAt, cells, lookupName_cons_self]
  have hfind : stage2Body.findBlock s.pc = some walkIfThen447I := by
    rw [hInv.pc_eq, hblock]; exact walkIfThen447I_find
  have hterm : walkIfThen447I.term =
      Term.condbr (.reg "%cmp451.i") "land.rhs457.i" "if.end473.i" := rfl
  have hstep : step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump
      { stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult (BitVec.ofNat 64 ei)
          (BitVec.ofNat 64 cd))) ] s.env)
          { s with mem := r.mem, next := r.next } with
        pc := (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
          then "land.rhs457.i" else "if.end473.i")
        pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%cmp451.i") (tl := "land.rhs457.i") (fl := "if.end473.i")
      (bit := evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)) hbit]
    dsimp only [stateAt]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ## The arena reservation's block

`if.end256.i` is where a decoded body's room is checked: the token's extent
(`%sub260.i`, the entry's span less one), the decoder's slack and the arena's
cursor are summed and compared against the log's capacity word.  Its instance is
also where the two facts the exclusion needs are read — the log's `alen` and
`acap` words, at the addresses `%alen` and `%acap` the block loads them — so the
run is the last instruction shape class F adds to the step vocabulary:

* `walkDenoteCode_store64_imm` — a store of a literal, the zero `%outn.i`'s slot
  receives before the check.  `BlockEval`'s store steps all take a register, and
  the block's zero is an immediate;
* the two loads at `%alen`/`%acap`, which the invariant *does* bind
  (`log_alen`, `log_acap`) — the difference from class G's reads is that the
  words are the carried cursors, so the run reads them out of the invariant
  rather than from a caller's fact;
* the frame, presence, log and event facts, across the one store: the slot is
  `%outn.i`, the fourth `alloca` at `G.next0 + 20`, so the store is inside
  `walkWide`'s four stack objects and outside the log and the stream.

The branch's *taken* edge is the arena trap's exclusion (`walkArenaReserve_clear`)
read at the record in flight; the link states the branch at the bit the run
computed, so it composes with that verdict without assuming it.  This block is
also where the record in flight *enters* the carry: it is the first block that
has all three of the triple — the entry's position (`%idxprom.i`), the arena
offset it reserved (`%alen`'s word, which the carry's cursor bounds) and the
token's document extent (`%sub260.i`) — so the link sets `pending` to them and
the trap arm's premise is one the traversal actually supplies. -/

/-- **The check's two edges**, read at the word the block loads: the arena's trap
when the reservation does not fit, and the reservation's own block when it does. -/
def walkIfEnd256Next (A Cc cv ix : BitVec 64) : String :=
  if evalICmp .ugt (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
      + BitVec.ofNat 64 64 + A) Cc = 1 then "if.end.i83" else "z_arena_reserve.exit"

/-- **A store of a literal** at a register's address.  `%outn.i`'s zeroing before
the arena check is this instruction, and the tree's store steps all take a
register, so the literal is its own step. -/
theorem walkDenoteCode_store64_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 64) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hstep : evalInstr calls (stateAt env s)
      (.store (.int 64) (.imm (.int 64 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    simp [evalInstr, evalOperand, Const.toValue, stateAt, hp, storeValue]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
/-- `if.end256.i`: the arena's reservation for a decoded body. -/
def walkIfEnd256 : Block :=
  { name := "if.end256.i",
    instrs := [
      Instr.binop "%30" .xor 64 (.reg "%idxprom.i")
        (.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.binop "%sub260.i" .add 64 (.reg "%conv211.i") (.reg "%30"),
      Instr.callVoid "llvm.lifetime.start.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 8))), (.ptr, .reg "%outn.i")],
      Instr.store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%outn.i"),
      Instr.binop "%add.i" .add 64 (.reg "%sub260.i")
        (.imm (.int 64 (BitVec.ofNat 64 64))),
      Instr.load "%z.val36" (.int 64) (.reg "%alen"),
      Instr.load "%z.val37" (.int 64) (.reg "%acap"),
      Instr.binop "%add.i82" .add 64 (.reg "%add.i") (.reg "%z.val36"),
      Instr.icmp "%cmp.not.i" IPred.ugt 64 (.reg "%add.i82") (.reg "%z.val37")],
    term := Term.condbr (.reg "%cmp.not.i") "if.end.i83" "z_arena_reserve.exit" }

theorem walkIfEnd256_find : stage2Body.findBlock "if.end256.i" = some walkIfEnd256 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfEnd256]

/-- The block's run: the token's extent, the marker, the zero, the two log words
and the comparison.  The two reads are taken at the memory *after* the zero store,
so the caller supplies the separation that transports them
(`hsepA`, `hsepC`), which at the walk's staging is `WalkStage.sevenEnd`. -/
theorem walkIfEnd256_denote {sub : Calls} (env : Env) (s : State)
    {ix cv : BitVec 64} {ao al ac : Nat} {A C : BitVec 64}
    (hidx : lookupName env "%idxprom.i" = some (.int 64 ix))
    (hconv : lookupName env "%conv211.i" = some (.int 64 cv))
    (houtn : lookupName env "%outn.i" = some (.ptr ao))
    (halen : lookupName env "%alen" = some (.ptr al))
    (hacap : lookupName env "%acap" = some (.ptr ac))
    (hreadA : readBytes s.mem al 8 = some (natToBytes A.toNat 8))
    (hreadC : readBytes s.mem ac 8 = some (natToBytes C.toNat 8))
    (hsepA : al + 8 ≤ ao ∨ ao + 8 ≤ al)
    (hsepC : ac + 8 ≤ ao ∨ ao + 8 ≤ ac) :
    denoteCode (stage2Calls sub) walkIfEnd256.instrs (stateAt env s) =
      some (stateAt (cells [
        ("%cmp.not.i", .int 1 (evalICmp .ugt (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
          + BitVec.ofNat 64 64 + A) C)),
        ("%add.i82", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
          + BitVec.ofNat 64 64 + A)),
        ("%z.val37", .int 64 C),
        ("%z.val36", .int 64 A),
        ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
          + BitVec.ofNat 64 64)),
        ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))),
        ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615))] env)
        { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) }) := by
  have hreadA' : readBytes (writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8)) al 8 =
      some (natToBytes A.toNat 8) := by
    rw [walkReadBytes_writeBytes_outside (start := ao) (addr := al) (n := 8)
      (v := natToBytes (BitVec.ofNat 64 0).toNat 8)
      (by rw [natToBytes_length]; omega)]
    exact hreadA
  have hreadC' : readBytes (writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8)) ac 8 =
      some (natToBytes C.toNat 8) := by
    rw [walkReadBytes_writeBytes_outside (start := ao) (addr := ac) (n := 8)
      (v := natToBytes (BitVec.ofNat 64 0).toNat 8)
      (by rw [natToBytes_length]; omega)]
    exact hreadC
  simp only [walkIfEnd256]
  rw [denoteCode_xor_imm (calls := stage2Calls sub) (env := env) (s := s) (d := "%30")
    (a := "%idxprom.i") (x := ix) (c := BitVec.ofNat 64 18446744073709551615) hidx]
  rw [denoteCode_add_reg (calls := stage2Calls sub)
    (env := ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (d := "%sub260.i") (a := "%conv211.i") (b := "%30") hconv (by rfl)]
  rw [walkDenoteCode_lifetimeStart (sub := sub)
    (env := ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (size := 8) (obj := "%outn.i") (by simpa [lookupName] using houtn)]
  rw [walkDenoteCode_store64_imm (calls := stage2Calls sub)
    (env := ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (x := BitVec.ofNat 64 0) (p := "%outn.i") (a := ao)
    (by simpa [lookupName] using houtn)]
  rw [denoteCode_add_imm (calls := stage2Calls sub)
    (env := ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    (d := "%add.i") (a := "%sub260.i") (c := BitVec.ofNat 64 64)
    (x := cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))
    (by simp [lookupName])]
  rw [denoteCode_load64 (calls := stage2Calls sub) (s := { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    (env := ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64)) ::
      ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (d := "%z.val36") (p := "%alen") (a := al) (v := A)
    (by simpa [lookupName] using halen) hreadA']
  rw [denoteCode_load64 (calls := stage2Calls sub) (s := { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    (env := ("%z.val36", .int 64 A) ::
      ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64)) ::
      ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (d := "%z.val37") (p := "%acap") (a := ac) (v := C)
    (by simpa [lookupName] using hacap) hreadC']
  rw [denoteCode_add_reg (calls := stage2Calls sub) (s := { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    (env := ("%z.val37", .int 64 C) :: ("%z.val36", .int 64 A) ::
      ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64)) ::
      ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (d := "%add.i82") (a := "%add.i") (b := "%z.val36")
    (x := cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64) (y := A)
    (by simp [lookupName]) (by simp [lookupName])]
  rw [walkDenoteCode_icmp (calls := stage2Calls sub) (s := { s with mem := writeBytes s.mem ao (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    (env := ("%add.i82", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64 + A)) ::
      ("%z.val37", .int 64 C) :: ("%z.val36", .int 64 A) ::
      ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64)) ::
      ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (d := "%cmp.not.i") (w := 64) (p := IPred.ugt)
    (oa := .reg "%add.i82") (ob := .reg "%z.val37")
    (x := cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64 + A)
    (y := C) (by simp [evalOperand, stateAt, lookupName]) (by simp [evalOperand, stateAt, lookupName])]
  rfl

/-- **`if.end256.i` is a link.**  The one store is `%outn.i`'s zero, inside the
four stack objects; the two log words are the invariant's; and the edge is the
bit the run computed, so the trap's arm is taken only when
`walkArenaReserve_clear`'s hypothesis fails. -/
theorem WalkLink.if_end256_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.end256.i")
    {ix cv : BitVec 64} {A Cc : BitVec 64}
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (hconv : lookupName s.env "%conv211.i" = some (.int 64 cv))
    (houtn : lookupName s.env "%outn.i" = some (.ptr (G.next0 + 20)))
    (halen : lookupName s.env "%alen" = some (.ptr (C.stage.z + 48)))
    (hacap : lookupName s.env "%acap" = some (.ptr (C.stage.z + 56)))
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    (hC : natToBytes Cc.toNat 8 = wordBytes 8 G.dstcap)
    (ext : Nat) (hiv : ix.toNat < G.n)
    (hnext : cv.toNat = ix.toNat + ext + 1) (hpl : ix.toNat + ext ≤ G.n)
    (hcur : C.alen ≤ G.ndst0 + ix.toNat) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := walkIfEnd256Next A Cc cv ix, pending := some (ix.toNat, C.alen, ext) } s' := by
  have hz64 : C.stage.z + 64 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites])
    simp only [stage2LogExtent] at h
    exact h
  have hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8) := by
    rw [hC]; exact hInv.log_acap
  have hden := walkIfEnd256_denote (sub := stage2SubCalls) (env := s.env) (s := s)
    (ix := ix) (cv := cv) (ao := G.next0 + 20) (al := C.stage.z + 48)
    (ac := C.stage.z + 56) (A := A) (C := Cc)
    hidx hconv houtn halen hacap hreadA hreadC (by omega) (by omega)
  have hstTy : WalkStackBytes (writeBytes s.mem (G.next0 + 20)
      (natToBytes (BitVec.ofNat 64 0).toNat 8)) C.stage.ctype C.tyMap C.wlen := by
    refine hInv.tyBytes.write_outside (Or.inr ?_)
    have hwl : (natToBytes (BitVec.ofNat 64 0).toNat 8).length = 8 :=
      natToBytes_length _ _
    have hse := (stack_alloca_sep (G := G) (C := C) (s := s) hInv
      (a := G.next0 + 20) (by omega)).1
    omega
  have hstSt : WalkStackBytes (writeBytes s.mem (G.next0 + 20)
      (natToBytes (BitVec.ofNat 64 0).toNat 8)) C.stage.cst C.stMap C.wlen := by
    refine hInv.stBytes.write_outside (Or.inr ?_)
    have hwl : (natToBytes (BitVec.ofNat 64 0).toNat 8).length = 8 :=
      natToBytes_length _ _
    have hse := (stack_alloca_sep (G := G) (C := C) (s := s) hInv
      (a := G.next0 + 20) (by omega)).2
    omega
  refine WalkLink.callQuietBrPending (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := C.stMap) (hstTy := hstTy) (hstSt := hstSt)
    (p := ix.toNat) (off := C.alen) (ext := ext)
    (B := walkIfEnd256) (by rw [hblock]; exact walkIfEnd256_find)
    (s₁ := stateAt (cells [
      ("%cmp.not.i", .int 1 (evalICmp .ugt (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64 + A) Cc)),
      ("%add.i82", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64 + A)),
      ("%z.val37", .int 64 Cc),
      ("%z.val36", .int 64 A),
      ("%add.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
        + BitVec.ofNat 64 64)),
      ("%sub260.i", .int 64 (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615))),
      ("%30", .int 64 (ix ^^^ BitVec.ofNat 64 18446744073709551615))] s.env)
      { s with mem := writeBytes s.mem (G.next0 + 20) (natToBytes (BitVec.ofNat 64 0).toNat 8) })
    hden (by unfold walkCarried; decide) rfl
    (by
      dsimp only [stateAt]
      exact hInv.frame.write_inside (a := G.next0 + 20)
        (bs := natToBytes (BitVec.ofNat 64 0).toNat 8)
        (fun k hk => by
          rw [natToBytes_length] at hk
          exact ⟨(G.next0 + 20, 8), by simp [walkWide, walkPresent, stage2AllocaWrites],
            by omega, by omega⟩))
    (by dsimp only [stateAt]; exact walkStaged_write rfl hInv.owned)
    (by
      dsimp only [stateAt]
      intro off w hw
      have hw' : off + w ≤ 64 := hw
      refine walkReadBytes_writeBytes_outside (start := G.next0 + 20)
        (addr := C.stage.z + off) (n := w) (v := natToBytes (BitVec.ofNat 64 0).toNat 8) ?_
      rw [natToBytes_length]
      left
      omega)
    (by
      dsimp only [stateAt]
      have hsum : (C.events.map EventRecord.encodedSize).sum ≤ 13 * C.events.length := by
        have h := EventRecord.sum_encodedSize_le C.events
        simpa only [stage2RecordBytes] using h
      have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
          (C.events.map EventRecord.encodedSize).sum := by
        simp only [List.length_flatten, List.map_map]; rfl
      have hroom : G.nev0 + 13 * G.n ≤ G.evcap := by
        have h := G.evRoom
        simpa only [stage2RecordBytes] using h
      have hwm : G.ev + G.evcap ≤ G.next0 :=
        G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
      have h1 : C.events.length ≤ C.k := hInv.events_le
      have h2 : C.k ≤ G.nep := hInv.k_le
      have h3 : G.nep ≤ G.n := G.nep_le
      refine walkReadBytes_writeBytes_outside (start := G.next0 + 20)
        (addr := G.ev + G.nev0) (n := (C.events.map EventRecord.encodedBytes).flatten.length)
        (v := natToBytes (BitVec.ofNat 64 0).toNat 8) ?_
      rw [natToBytes_length]; left
      rw [hlen]; omega)
    rfl
    (by simp [cells, stateAt, lookupName_cons_self])
    (by simp [WalkLocal]) (by simp [WalkLocal])
    (Nat.le_refl _) hiv hcur hpl

/-! ### The reservation's completion block

`z_arena_reserve.exit` spends the reservation `if.end256.i` recorded: it loads
the arena's base word at `%z + 40` (`%ar`), forms the document's body pointer
(`%arrayidx10.i + 1`) and the arena's destination (`%ar + %z.val36`), calls
`@s2_string_body`, and hands the answer to `NodeBlock31`.

The block writes nothing of its own.  Everything the reservation is *about* is
the callee's: the cursor word at `%xj.i`, the decoded-length word at `%outn.i`
(the block zeroed it one block earlier, so the read-back is the decoded length on
the accepting arms), and the decoded prefix in a window `%sub260.i` wide at
`%ar + %z.val36`.  The window's start is the word `if.end256.i` loaded, which
`WalkInv.logArena_le` bounds by the carried cursor, so a carry that reserves
`alen + %sub260.i` at the cursor already covers the write: the reservation is
what the *carry* records at this block, and `if.else285.i` then only writes the
word back.  Its frame is `s2StringBodyFoot` widened to `walkWide` at the new
cursor, which is the composition `WalkInv.spans_end` and the relaxed
`WalkInv.log_alen` exist for.

This section pins the block and its run: the instruction list as the body has
it, and its `denoteCode` at an arbitrary outcome.  The link that carries the
invariant across it is the next statement owed here. -/

/-- `z_arena_reserve.exit`: the arena's base, the body's two pointers, and the
`@s2_string_body` call whose answer `NodeBlock31` tests. -/
def walkZArenaReserveExit : Block :=
  { name := "z_arena_reserve.exit",
    instrs := [
      Instr.load "%31" Ty.ptr (Operand.reg "%ar"),
      Instr.gep "%add.ptr.i" (Ty.int 8) (Operand.reg "%31") (Operand.reg "%z.val36"),
      Instr.gep "%add.ptr271.i" (Ty.int 8) (Operand.reg "%arrayidx10.i")
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.call "%call272.i" (Ty.int 32) "s2_string_body"
        [(Ty.ptr, Operand.reg "%c.i"), (Ty.ptr, Operand.reg "%add.ptr271.i"),
         (Ty.int 64, Operand.reg "%sub260.i"), (Ty.ptr, Operand.reg "%add.ptr.i"),
         (Ty.ptr, Operand.reg "%outn.i"), (Ty.ptr, Operand.reg "%xp"),
         (Ty.ptr, Operand.reg "%xj.i"), (Ty.int 64, Operand.reg "%nxp")]],
    term := Term.br "NodeBlock31" }

theorem walkZArenaReserveExit_find :
    stage2Body.findBlock "z_arena_reserve.exit" = some walkZArenaReserveExit := by
  simp [stage2Body, Function.findBlock, findBlockList, walkZArenaReserveExit]

/-- The `s2_string_body` argument list: the cursor record, the body's document
pointer and extent, the arena's destination, the output slot, the escape list
and its count. -/
theorem walkArgs_stringBody (env : Env) (s : State)
    {c p on xp xj : Nat} {dq : Nat} {A : BitVec 64} {ext nxp : Nat}
    (hc : lookupName env "%c.i" = some (.ptr c))
    (hp : lookupName env "%add.ptr271.i" = some (.ptr p))
    (hlen : lookupName env "%sub260.i" = some (.int 64 (BitVec.ofNat 64 ext)))
    (hdst : lookupName env "%add.ptr.i" = some (.ptr (dq + (A.signExtend 64).toNat)))
    (hon : lookupName env "%outn.i" = some (.ptr on))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj.i" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 nxp))) :
    evalOperands (stateAt env s)
        [(Ty.ptr, Operand.reg "%c.i"), (Ty.ptr, Operand.reg "%add.ptr271.i"),
         (Ty.int 64, Operand.reg "%sub260.i"), (Ty.ptr, Operand.reg "%add.ptr.i"),
         (Ty.ptr, Operand.reg "%outn.i"), (Ty.ptr, Operand.reg "%xp"),
         (Ty.ptr, Operand.reg "%xj.i"), (Ty.int 64, Operand.reg "%nxp")] =
      some [.ptr c, .ptr p, .int 64 (BitVec.ofNat 64 ext),
        .ptr (dq + (A.signExtend 64).toNat), .ptr on, .ptr xp, .ptr xj,
        .int 64 (BitVec.ofNat 64 nxp)] := by
  simp only [evalOperands, stateAt, evalOperand, hc, hp, hlen, hdst, hon, hxp, hxj, hnxp]

/-- **The reservation's block, as a run.**  The `%ar` word is the arena's base,
the second `gep`'s literal is the body's first document byte, and the call's
outcome is the selection's answer at the eight arguments the block passes. -/
theorem walkZArenaReserveExit_denote {sub : Calls} (env : Env) (s : State)
    {ar c dq pn on xp xj : Nat} {A : BitVec 64} {ext nxp : Nat} {r : CallOutcome}
    (har : lookupName env "%ar" = some (.ptr ar))
    (hreadAr : readBytes s.mem ar 8 = some (wordBytes 8 dq))
    (hdq : dq < 2 ^ 64)
    (hz36 : lookupName env "%z.val36" = some (.int 64 A))
    (hpos : (A.signExtend 64).toNat < 2 ^ 63)
    (haj : lookupName env "%arrayidx10.i" = some (.ptr pn))
    (hsub : lookupName env "%sub260.i" = some (.int 64 (BitVec.ofNat 64 ext)))
    (hc : lookupName env "%c.i" = some (.ptr c))
    (houtn : lookupName env "%outn.i" = some (.ptr on))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj.i" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 nxp)))
    (hcall : stage2Calls sub "s2_string_body"
      [.ptr c, .ptr (pn + 1), .int 64 (BitVec.ofNat 64 ext),
        .ptr (dq + (A.signExtend 64).toNat), .ptr on, .ptr xp, .ptr xj,
        .int 64 (BitVec.ofNat 64 nxp)] s.mem s.next = some r) :
    denoteCode (stage2Calls sub) walkZArenaReserveExit.instrs (stateAt env s) =
      some (stateAt (("%call272.i", r.ret) ::
        ("%add.ptr271.i", .ptr (pn + 1)) ::
        ("%add.ptr.i", .ptr (dq + (A.signExtend 64).toNat)) ::
        ("%31", .ptr dq) :: env) { s with mem := r.mem, next := r.next }) := by
  simp only [walkZArenaReserveExit]
  rw [walkDenoteCode_loadPtr (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%31") (p := "%ar") (a := ar) (q := dq) har hreadAr hdq]
  rw [denoteCode_gep8_reg (calls := stage2Calls sub)
    (env := ("%31", .ptr dq) :: env) (s := s)
    (d := "%add.ptr.i") (base := "%31") (off := "%z.val36") (a := dq) (idx := A)
    (by simp [lookupName]) (by simpa [lookupName] using hz36) hpos]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub)
    (env := ("%add.ptr.i", .ptr (dq + (A.signExtend 64).toNat)) ::
      ("%31", .ptr dq) :: env) (s := s)
    (d := "%add.ptr271.i") (base := "%arrayidx10.i") (a := pn) (w := 64)
    (n := BitVec.ofNat 64 1) (by simpa [lookupName] using haj) (by decide)]
  have hone : (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat = 1 := by decide
  rw [hone]
  rw [walkDenoteCode_call (calls := stage2Calls sub)
    (env := ("%add.ptr271.i", .ptr (pn + 1)) ::
      ("%add.ptr.i", .ptr (dq + (A.signExtend 64).toNat)) ::
      ("%31", .ptr dq) :: env) (s := s)
    (d := "%call272.i") (callee := "s2_string_body") (ty := .int 32)
    (walkArgs_stringBody _ s
      (by simpa [lookupName] using hc)
      (by simp [lookupName])
      (by simpa [lookupName] using hsub)
      (by simp [lookupName])
      (by simpa [lookupName] using houtn)
      (by simpa [lookupName] using hxp)
      (by simpa [lookupName] using hxj)
      (by simpa [lookupName] using hnxp))
    hcall]
  simp only [denoteCode_nil, stateAt]

/-- **`z_arena_reserve.exit` is a link.**  The reservation `if.end256.i` recorded
is *spent*: the carry's arena cursor advances by the token's document extent, the
window's extent is appended to the spans at the cursor the reservation was made
at, and the record in flight is cleared because the window it named is now the
carry's.  The three quantities land where `pending`'s own clauses need them —
`spans_end` from the cursor's monotonicity (`C.alen + ext`), `spans_inside` from
the window's document room, and `alen_le_sum` from the cursor's own bound — and
the reserved window covers the write the callee performs at `%ar + %z.val36`,
because `logArena_le` bounds that word by the carried cursor.

The four memory clauses are class F's own, as they are for `WalkLink.callQuiet`
and `WalkLink.if_then425_i_emit`: the callee's answer (`s2StringBodyPost`) names
the memory, and the frame read off `s2StringBody_framed` at
`s2StringBodyFoot` — widened to `walkWide` at the new cursor — is the caller's,
with the presence, log and event-read facts beside it. -/
theorem WalkLink.z_arena_reserve_exit {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "z_arena_reserve.exit")
    {p off ext : Nat} (hpend : C.pending = some (p, off, ext))
    {A : BitVec 64} (hz36 : lookupName s.env "%z.val36" = some (.int 64 A))
    (hpos : (A.signExtend 64).toNat < 2 ^ 63)
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    (har : lookupName s.env "%ar" = some (.ptr (C.stage.z + 40)))
    (hGdst : G.dst < 2 ^ 64)
    (hreadAr : readBytes s.mem (C.stage.z + 40) 8 = some (wordBytes 8 G.dst))
    (haj : lookupName s.env "%arrayidx10.i" = some (.ptr (G.b + p)))
    (hsub : lookupName s.env "%sub260.i" = some (.int 64 (BitVec.ofNat 64 ext)))
    (hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (houtn : lookupName s.env "%outn.i" = some (.ptr (G.next0 + 20)))
    (hxp : lookupName s.env "%xp" = some (.ptr G.xp))
    (hxj : lookupName s.env "%xj.i" = some (.ptr (G.next0 + 16)))
    (hnxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 G.nxp)))
    (hwin : C.alen + ext ≤ G.n)
    {r : CallOutcome}
    (hcall : stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 (BitVec.ofNat 64 ext),
        .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 16),
        .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r)
    (hframe : UnchangedOutside m0 r.mem (walkWide G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }))
    (howned : ∀ q ∈ walkStaged G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }, HasBytes r.mem q.1 q.2)
    (hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes r.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w)
    (hev : readBytes r.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length)
    (hstTy : WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen)
    (hstSt : WalkStackBytes r.mem C.stage.cst C.stMap C.wlen) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none } s' := by
  have hAle : A.toNat ≤ C.alen := hInv.logArena_le hreadA
  have hse : (A.signExtend 64).toNat = A.toNat := by simp
  have hcall' : stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 (BitVec.ofNat 64 ext),
        .ptr (G.dst + (A.signExtend 64).toNat), .ptr (G.next0 + 20), .ptr G.xp,
        .ptr (G.next0 + 16), .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r := by
    rw [hse]; exact hcall
  let s₁ : State := stateAt (("%call272.i", r.ret) ::
    ("%add.ptr271.i", .ptr (G.b + p + 1)) ::
    ("%add.ptr.i", .ptr (G.dst + (A.signExtend 64).toNat)) ::
    ("%31", .ptr G.dst) :: s.env) { s with mem := r.mem, next := r.next }
  have hden : denoteCode (stage2Calls stage2SubCalls) walkZArenaReserveExit.instrs s =
      some s₁ := by
    dsimp only [s₁]
    exact walkZArenaReserveExit_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (ar := C.stage.z + 40) (c := C.stage.c) (dq := G.dst) (pn := G.b + p)
      (on := G.next0 + 20) (xp := G.xp) (xj := G.next0 + 16) (A := A)
      (ext := ext) (nxp := G.nxp) (r := r)
      har hreadAr hGdst hz36 hpos haj hsub hc houtn hxp hxj hnxp hcall'
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfreeK : ∀ i ∈ walkZArenaReserveExit.instrs, i.dst? ≠ some "%k.0.i249" := by
    intro i hi
    simp only [walkZArenaReserveExit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hfreeSp : ∀ i ∈ walkZArenaReserveExit.instrs, i.dst? ≠ some "%sp.i.0248" := by
    intro i hi
    simp only [walkZArenaReserveExit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hfind : stage2Body.findBlock C.block = some walkZArenaReserveExit := by
    rw [hblock]; exact walkZArenaReserveExit_find
  let s' : State := { s₁ with pc := "NodeBlock31", pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hterm : walkZArenaReserveExit.term = Term.br "NodeBlock31" := rfl
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s', s₁, stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := ?_
      alen_ge := ?_
      spans_order := ?_
      spans_end := ?_
      spans_inside := ?_
      pending_at := ?_
      pending_cursor := ?_
      pending_len := ?_
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by dsimp only [s', s₁, stateAt]; exact hstTy
      stBytes := by dsimp only [s', s₁, stateAt]; exact hstSt
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := howned
      frame := hframe
      blockLocal := by simp [WalkLocal] }
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkZArenaReserveExit.instrs
      "%k.0.i249" hfreeK s s₁ hden]
    exact hInv.blockIndex
  · dsimp only [s', s₁, stateAt]
    rw [hev]
    exact hInv.evBytes
  · dsimp only
    rw [List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have := hInv.alen_le_sum
    omega
  · dsimp only
    have := hInv.alen_ge
    omega
  · dsimp only
    rw [List.pairwise_append]
    refine ⟨hInv.spans_order, ?_, ?_⟩
    · exact List.Pairwise.cons (by intro b hb; exact absurd hb (by simp)) List.Pairwise.nil
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact hInv.spans_end a ha
  · dsimp only
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with h | h
    · exact hInv.spans_inside r h
    · simp only [List.mem_singleton] at h
      subst h
      exact hwin
  · dsimp only
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with h | h
    · exact le_trans (hInv.spans_end r h) (by omega)
    · simp only [List.mem_singleton] at h
      subst h
      omega
  · intro p' off' len' hp
    exact absurd hp (by simp)
  · intro p' off' len' hp
    exact absurd hp (by simp)
  · intro p' off' len' hp
    exact absurd hp (by simp)
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkZArenaReserveExit.instrs
      "%sp.i.0248" hfreeSp s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · dsimp only [s', s₁, stateAt]
    rw [hlog 32 4 (by decide)]
    exact hInv.log_hash
  · dsimp only [s', s₁, stateAt]
    rw [hlog 8 8 (by decide)]
    exact hInv.log_len
  · dsimp only [s', s₁, stateAt]
    rw [hlog 16 8 (by decide)]
    exact hInv.log_cap
  · dsimp only [s', s₁, stateAt]
    obtain ⟨a, hge, ha, hr⟩ := hInv.log_alen
    exact ⟨a, hge, le_trans ha (by omega), Eq.trans (hlog 48 8 (by decide)) hr⟩
  · dsimp only [s', s₁, stateAt]
    rw [hlog 56 8 (by decide)]
    exact hInv.log_acap

/-! ## The event record's emission

`if.then328.i` is where the thirteen-byte key/string record is written at the
event stream's cursor, the cursor is advanced, and the log's `len` word is
rewritten with the new figure.  It is class F's cursor-moving shape: the record's
bytes are three stores at `%add.ptr297.i`, `%add.ptr302.i` and `%add.ptr304.i`,
the cursor advance is `%add.i84`'s store at `%len`, and the `llvm.lifetime.end`
marker closes `%outn.i`'s live range.  The target carry is the record appended to
the trace and the cursor moved, so the invariant's three trace clauses are the
work: `evlen_eq` reads the appended record's size, `evBytes` the appended bytes,
and the frame grows with `walkWide_grow`.

The log's `%len` word is rewritten in the same block, and the first field of
`%z` is read by the block's own load `%33 = load ptr, ptr %z`, which is the
address the record is written at: `walkDenoteCode_loadPtr`
(`JsonStage2WalkStore`) is that load, and the word it reads is the invariant's
`evBytes`-side cursor.  The four log reads the target carry owes are the write at
`%z + 8` and the record's own bytes, both outside every other field
(`walkReadBytes_log_of_log_write`, `walkReadBytes_ev_of_log_write`).

The block's `%key.1.i` bit decides the arm: the key record and the string record
are the same thirteen bytes with different tags, so the branch's bit is the
record's `key` field and the edge names its successor. -/


/-- Appending a written list to a readable prefix. -/
theorem walkReadBytes_writeBytes_append {m : Mem} {a N : Nat} {flat rec : List UInt8}
    (h : readBytes m a N = some flat) :
    readBytes (writeBytes m (a + N) rec) a (N + rec.length) = some (flat ++ rec) := by
  have h1 : readBytes (writeBytes m (a + N) rec) a N = some flat := by
    rw [walkReadBytes_writeBytes_outside (start := a + N) (addr := a) (n := N) (v := rec)
      (by left; omega)]
    exact h
  have h2 : readBytes (writeBytes m (a + N) rec) (a + N) rec.length = some rec :=
    readBytes_writeBytes_same m rec (addr := a + N)
  exact JsonEntrySteps.readBytes_append (writeBytes m (a + N) rec) N a flat rec.length rec h1 h2

/-- `walkSetMem`: the target state of a store run. -/
def walkSetMem (s : State) (m : Mem) : State := { s with mem := m }

/-- `if.then328.i`: the thirteen-byte key/string record and the cursor's advance. -/
def walkIfThen328 : Block :=
  { name := "if.then328.i",
    instrs := [
      Instr.trunc "%conv286.i.sink" 64 32 (.reg "%conv286.i.sink.in"),
      Instr.load "%33" .ptr (.reg "%z"),
      Instr.gep "%add.ptr297.i" (.int 8) (.reg "%33") (.reg "%z.val"),
      Instr.select "%conv300.i" (.int 8) (.reg "%key.1.i")
        (.imm (.int 8 (BitVec.ofNat 8 5))) (.imm (.int 8 (BitVec.ofNat 8 6))),
      Instr.store (.int 8) (.reg "%conv300.i") (.reg "%add.ptr297.i"),
      Instr.gep "%add.ptr302.i" (.int 8) (.reg "%add.ptr297.i")
        (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.store (.int 32) (.reg "%conv286.i.sink") (.reg "%add.ptr302.i"),
      Instr.gep "%add.ptr304.i" (.int 8) (.reg "%add.ptr297.i")
        (.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.store (.int 64) (.reg "%.sink") (.reg "%add.ptr304.i"),
      Instr.store (.int 64) (.reg "%add.i84") (.reg "%len"),
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 8))), (.ptr, .reg "%outn.i")]],
    term := Term.condbr (.reg "%key.1.i") "if.then330.i" "if.else334.i" }

theorem walkIfThen328_find : stage2Body.findBlock "if.then328.i" = some walkIfThen328 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen328]

theorem walkIfThen328_denote {sub : Calls} (env : Env) (s : State)
    {sinkIn : BitVec 64} {q evlen : Nat} {keyBit : BitVec 1} {span : BitVec 64}
    {ao z : Nat}
    (hsink : lookupName env "%conv286.i.sink.in" = some (.int 64 sinkIn))
    (hz : lookupName env "%z" = some (.ptr z))
    (hread : readBytes s.mem z 8 = some (wordBytes 8 q)) (hq : q < 2 ^ 64)
    (hlenv : lookupName env "%z.val" = some (.int 64 (BitVec.ofNat 64 evlen)))
    (hev63 : evlen < 2 ^ 63)
    (hkey : lookupName env "%key.1.i" = some (.int 1 keyBit))
    (hspan : lookupName env "%.sink" = some (.int 64 span))
    (hnew : lookupName env "%add.i84" = some (.int 64 (BitVec.ofNat 64 (evlen + 13))))
    (hnew64 : evlen + 13 < 2 ^ 64)
    (hlen : lookupName env "%len" = some (.ptr (z + 8)))
    (houtn : lookupName env "%outn.i" = some (.ptr ao)) :
    denoteCode (stage2Calls sub) walkIfThen328.instrs (stateAt env s) =
      some (stateAt (cells [
        ("%add.ptr304.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat)),
        ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)),
        ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)),
        ("%add.ptr297.i", .ptr (q + evlen)),
        ("%33", .ptr q),
        ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) ] env)
        (walkSetMem s (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes s.mem (q + evlen)
                  (natToBytes (if keyBit = 1 then (BitVec.ofNat 8 5)
                    else (BitVec.ofNat 8 6)).toNat 1))
                (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)
                (natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4))
              (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat)
              (natToBytes span.toNat 8))
            (z + 8) (wordBytes 8 (evlen + 13))) )) := by
  simp only [walkIfThen328]
  rw [denoteCode_trunc (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%conv286.i.sink") (v := "%conv286.i.sink.in") (wIn := 64) (wOut := 32)
    (x := sinkIn) hsink]
  rw [walkDenoteCode_loadPtr (calls := stage2Calls sub)
    (env := ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env) (s := s) (d := "%33") (p := "%z") (a := z) (q := q)
    (by simpa [lookupName] using hz) hread hq]
  rw [denoteCode_gep8_ofNat (calls := stage2Calls sub) (s := _)
    (env := ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (d := "%add.ptr297.i") (base := "%33") (off := "%z.val") (a := q) (j := evlen)
    (by simp [lookupName]) (by simpa [lookupName] using hlenv) hev63]
  rw [denoteCode_select_bit_imm_imm_w (calls := stage2Calls sub) (s := _)
    (env := ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (d := "%conv300.i") (c := "%key.1.i") (w := 8)
    (bb := keyBit) (x := BitVec.ofNat 8 5) (y := BitVec.ofNat 8 6)
    (by simpa [lookupName] using hkey)]
  rw [denoteCode_store8 (calls := stage2Calls sub) (s := _)
    (env := ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (v := "%conv300.i") (p := "%add.ptr297.i") (a := q + evlen)
    (x := (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6))
    (by simp [lookupName]) (by simp [lookupName])]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (s := _)
    (env := ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (d := "%add.ptr302.i") (base := "%add.ptr297.i") (a := q + evlen) (w := 64)
    (n := BitVec.ofNat 64 1) (by simp [lookupName]) (by decide)]
  rw [denoteCode_store32 (calls := stage2Calls sub) (s := _)
    (env := ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)) :: ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (v := "%conv286.i.sink") (p := "%add.ptr302.i") (a := q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)
    (x := BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))
    (by simp [lookupName]) (by simp [lookupName])]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (s := _)
    (env := ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)) :: ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (d := "%add.ptr304.i") (base := "%add.ptr297.i") (a := q + evlen) (w := 64)
    (n := BitVec.ofNat 64 5) (by simp [lookupName]) (by decide)]
  rw [denoteCode_store64 (calls := stage2Calls sub) (s := _)
    (env := ("%add.ptr304.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat)) :: ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)) :: ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (v := "%.sink") (p := "%add.ptr304.i") (a := q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat) (x := span)
    (by simpa [lookupName] using hspan) (by simp [lookupName])]
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub) (s := _)
    (env := ("%add.ptr304.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat)) :: ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)) :: ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (v := "%add.i84") (p := "%len") (a := z + 8) (j := evlen + 13)
    (by simpa [lookupName] using hnew) hnew64 (by simpa [lookupName] using hlen)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (s := _)
    (env := ("%add.ptr304.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat)) :: ("%add.ptr302.i", .ptr (q + evlen + (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat)) :: ("%conv300.i", .int 8 (if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6)) :: ("%add.ptr297.i", .ptr (q + evlen)) :: ("%33", .ptr q) :: ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32))) :: env)
    (size := 8) (obj := "%outn.i") (p := ao) (by simpa [lookupName] using houtn)]
  dsimp only [walkSetMem, denoteCode]
  rfl

/-- **`if.then328.i` is a link**: the thirteen-byte key/string record at the
event stream's cursor, the cursor's advance, and the termination marker. -/
theorem WalkLink.if_then328_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then328.i")
    {sinkIn : BitVec 64} {keyBit : BitVec 1} {span : BitVec 64}
    (hsink : lookupName s.env "%conv286.i.sink.in" = some (.int 64 sinkIn))
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hzread : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hlenv : lookupName s.env "%z.val" = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hev63 : C.evlen < 2 ^ 63)
    (hkey : lookupName s.env "%key.1.i" = some (.int 1 keyBit))
    (hspan : lookupName s.env "%.sink" = some (.int 64 span))
    (hnew : lookupName s.env "%add.i84" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 13))))
    (hnew64 : C.evlen + 13 < 2 ^ 64)
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (houtn : lookupName s.env "%outn.i" = some (.ptr (G.next0 + 20)))
    (hev64 : G.ev < 2 ^ 64)
    (hlt : C.events.length < C.k) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if keyBit = 1 then "if.then330.i" else "if.else334.i"),
               evlen := C.evlen + 13,
               events := C.events ++ [EventRecord.str (keyBit = 1) (sinkIn.toNat % 2 ^ 32) span.toNat] } s' := by
  let o1 : Nat := (BitVec.signExtend 64 (BitVec.ofNat 64 1)).toNat
  let o5 : Nat := (BitVec.signExtend 64 (BitVec.ofNat 64 5)).toNat
  let tagv : BitVec 8 := if keyBit = 1 then BitVec.ofNat 8 5 else BitVec.ofNat 8 6
  let recBytes : List UInt8 :=
    (EventRecord.str (keyBit = 1) (sinkIn.toNat % 2 ^ 32) span.toNat).encodedBytes
  let m1 : Mem := writeBytes s.mem (G.ev + C.evlen) (natToBytes tagv.toNat 1)
  let m2 : Mem := writeBytes m1 (G.ev + C.evlen + o1)
    (natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4)
  let m3 : Mem := writeBytes m2 (G.ev + C.evlen + o5) (natToBytes span.toNat 8)
  let m4 : Mem := writeBytes m3 (C.stage.z + 8) (wordBytes 8 (C.evlen + 13))
  let envF : Env := cells [
    ("%add.ptr304.i", .ptr (G.ev + C.evlen + o5)),
    ("%add.ptr302.i", .ptr (G.ev + C.evlen + o1)),
    ("%conv300.i", .int 8 tagv),
    ("%add.ptr297.i", .ptr (G.ev + C.evlen)),
    ("%33", .ptr G.ev),
    ("%conv286.i.sink", .int 32 (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)))] s.env
  let s₁ : State := stateAt envF (walkSetMem s m4)
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen328.instrs s =
      some s₁ := by
    dsimp only [s₁, envF, m4, m3, m2, m1, recBytes, tagv, o1, o5, walkSetMem]
    exact walkIfThen328_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (sinkIn := sinkIn) (q := G.ev) (evlen := C.evlen) (keyBit := keyBit)
      (span := span) (ao := G.next0 + 20) (z := C.stage.z)
      hsink hz hzread hev64 hlenv hev63 hkey hspan hnew hnew64 hlen houtn
  have hEvLen2 : (C.events.map EventRecord.encodedBytes).flatten.length =
      (C.events.map EventRecord.encodedSize).sum := by
    simp only [List.length_flatten, List.map_map]; rfl
  have hevroom : C.evlen + 13 ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hreg : C.evlen = G.nev0 +
        (C.events.map EventRecord.encodedBytes).flatten.length := by
      rw [hInv.evlen_eq, hEvLen2]
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hlt
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s₁ with
    pc := (if keyBit = 1 then "if.then330.i" else "if.else334.i"),
    pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hfind : stage2Body.findBlock s.pc = some walkIfThen328 := by
      rw [hpc, hblock]; exact walkIfThen328_find
    have hterm : walkIfThen328.term =
        Term.condbr (Operand.reg "%key.1.i") "if.then330.i" "if.else334.i" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%key.1.i") (tl := "if.then330.i")
      (fl := "if.else334.i") (bit := keyBit)
      (by dsimp only [s₁, envF]; simpa [stateAt, walkSetMem, cells, lookupName] using hkey)]
    dsimp only [s', s₁, envF, walkSetMem, stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  -- the invariant at the target
  have hEvLen : (C.events.map EventRecord.encodedBytes).flatten.length =
      (C.events.map EventRecord.encodedSize).sum := by
    simp only [List.length_flatten, List.map_map]; rfl
  have hrecLen : recBytes.length = 13 := by
    dsimp only [recBytes]
    simp [EventRecord.encodedSize, EventRecord.encodedBytes, wordBytes, natToBytes_length]
  have htag : natToBytes tagv.toNat 1 =
      [UInt8.ofNat (if keyBit = 1 then EventRecord.tagKey else EventRecord.tagStr)] := by
    dsimp only [tagv]
    split <;> decide
  have ho1 : o1 = 1 := by decide
  have ho5 : o5 = 5 := by decide
  have hw2 : natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4 =
      wordBytes 4 (sinkIn.toNat % 2 ^ 32) := by
    rw [wordBytes, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  have hw3 : natToBytes span.toNat 8 = wordBytes 8 span.toNat := rfl
  have hrec : recBytes =
      [UInt8.ofNat (if keyBit = 1 then EventRecord.tagKey else EventRecord.tagStr)]
        ++ wordBytes 4 (sinkIn.toNat % 2 ^ 32) ++ wordBytes 8 span.toNat := by
    dsimp only [recBytes, EventRecord.encodedBytes]
    simp
  have hm3 : m3 = writeBytes s.mem (G.ev + C.evlen) recBytes := by
    dsimp only [m3, m2, m1]
    rw [ho1, ho5, htag, hw2, hw3]
    rw [show G.ev + C.evlen + 1 = G.ev + C.evlen +
        ([UInt8.ofNat (if keyBit = 1 then EventRecord.tagKey else EventRecord.tagStr)]).length
      from by simp]
    rw [← writeBytes_append]
    rw [show G.ev + C.evlen + 5 = G.ev + C.evlen +
        ([UInt8.ofNat (if keyBit = 1 then EventRecord.tagKey else EventRecord.tagStr)]
          ++ wordBytes 4 (sinkIn.toNat % 2 ^ 32)).length
      from by simp [wordBytes, natToBytes_length]]
    rw [← writeBytes_append, ← hrec]
  have hmemEq : m4 = writeBytes (writeBytes s.mem (G.ev + C.evlen) recBytes)
      (C.stage.z + 8) (wordBytes 8 (C.evlen + 13)) := by
    dsimp only [m4]
    rw [hm3]
  have hzev := walkLog_ev_sep hInv
  have hNev : G.nev0 + ((C.events.map EventRecord.encodedBytes).flatten.length + 13) ≤
      G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hlt; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hEvLen]
    omega
  have hsepRec : G.ev + C.evlen + recBytes.length ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ G.ev + C.evlen := by
    rcases hzev with h | h
    · right; omega
    · left; rw [hrecLen]
      have hcap : C.evlen + 13 ≤ G.evcap := by
        rw [show C.evlen = G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length
          from by rw [hInv.evlen_eq, hEvLen]]
        omega
      omega
  have hflat : ((C.events ++ [EventRecord.str (keyBit = 1) (sinkIn.toNat % 2 ^ 32)
      span.toNat]).map EventRecord.encodedBytes).flatten =
      (C.events.map EventRecord.encodedBytes).flatten ++ recBytes := by
    rw [List.map_append, List.flatten_append]
    rfl
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := ?_
      evlen_eq := ?_
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by
        dsimp only [s', s₁, envF, walkSetMem, stateAt, m4, m3, m2, m1]
        have ho1 : o1 = 1 := by decide
        have ho5 : o5 = 5 := by decide
        have htag : (natToBytes tagv.toNat 1).length = 1 := natToBytes_length _ _
        have hs1 : (natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4).length
            = 4 := natToBytes_length _ _
        have hs2 : (natToBytes span.toNat 8).length = 8 := natToBytes_length _ _
        have hL : stage2LogExtent = 64 := rfl
        have hwz : (wordBytes 8 (C.evlen + 13)).length = 8 := by
          simp [wordBytes, natToBytes_length]
        have hcap := hInv.wlen_cap
        have hS : stage2StackExtent = 520 := rfl
        simp only [stage2StackExtent] at hcap
        refine (((hInv.tyBytes.write_outside ?_).write_outside ?_).write_outside ?_).write_outside ?_
        · rcases ctype_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases ctype_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases ctype_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases ctype_log_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
      stBytes := by
        dsimp only [s', s₁, envF, walkSetMem, stateAt, m4, m3, m2, m1]
        have ho1 : o1 = 1 := by decide
        have ho5 : o5 = 5 := by decide
        have htag : (natToBytes tagv.toNat 1).length = 1 := natToBytes_length _ _
        have hs1 : (natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4).length
            = 4 := natToBytes_length _ _
        have hs2 : (natToBytes span.toNat 8).length = 8 := natToBytes_length _ _
        have hL : stage2LogExtent = 64 := rfl
        have hwz : (wordBytes 8 (C.evlen + 13)).length = 8 := by
          simp [wordBytes, natToBytes_length]
        have hcap := hInv.wlen_cap
        have hS : stage2StackExtent = 520 := rfl
        simp only [stage2StackExtent] at hcap
        refine (((hInv.stBytes.write_outside ?_).write_outside ?_).write_outside ?_).write_outside ?_
        · rcases cst_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases cst_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases cst_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases cst_log_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := ?_
      frame := ?_
      blockLocal := by
        dsimp only [s']
        by_cases hk : keyBit = 1
        · rw [if_pos hk]; simp [WalkLocal]
        · rw [if_neg hk]; simp [WalkLocal] }
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    simpa [cells, lookupName] using hInv.blockIndex
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · dsimp only [s', s₁, envF]
    rw [hInv.evlen_eq]
    simp only [List.map_append, List.sum_append, EventRecord.encodedSize_str,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq, hflat]
    simp only [List.length_append, List.length_cons, List.length_nil]
    have haddr : G.ev + C.evlen = (G.ev + G.nev0) +
        (C.events.map EventRecord.encodedBytes).flatten.length := by
      rw [hInv.evlen_eq, hEvLen]; omega
    have h1 : readBytes (writeBytes (writeBytes s.mem (G.ev + C.evlen) recBytes)
        (C.stage.z + 8) (wordBytes 8 (C.evlen + 13))) (G.ev + G.nev0)
        ((C.events.map EventRecord.encodedBytes).flatten.length + recBytes.length) =
        readBytes (writeBytes s.mem (G.ev + C.evlen) recBytes) (G.ev + G.nev0)
          ((C.events.map EventRecord.encodedBytes).flatten.length + recBytes.length) := by
      refine walkReadBytes_ev_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) recBytes)
        (z := C.stage.z) (ev := G.ev) (evcap := G.evcap) (nev0 := G.nev0)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length + recBytes.length)
        (off := 8) (v := wordBytes 8 (C.evlen + 13)) hzev ?_ hNev
      simp only [wordBytes, natToBytes_length, stage2LogExtent]
      omega
    rw [h1, haddr]
    exact walkReadBytes_writeBytes_append (m := s.mem) (a := G.ev + G.nev0)
      (N := (C.events.map EventRecord.encodedBytes).flatten.length)
      (flat := (C.events.map EventRecord.encodedBytes).flatten) (rec := recBytes)
      hInv.evBytes
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    simpa [cells, lookupName] using hInv.depth_reg
  · dsimp only [s', s₁, envF]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    rw [walkReadBytes_log_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) recBytes)
      (z := C.stage.z) (off := 8) (off' := 32) (N := 4)
      (v := wordBytes 8 (C.evlen + 13))
      (by right; simp only [wordBytes, natToBytes_length]; omega)]
    rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
      (a := G.ev + C.evlen) (w := recBytes.length) (off := 32) (w' := 4)
      (bs := recBytes) (by rw [hrecLen]) hsepRec (by decide)]
    exact hInv.log_hash
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    exact readBytes_writeBytes_same _ _
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    rw [walkReadBytes_log_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) recBytes)
      (z := C.stage.z) (off := 8) (off' := 16) (N := 8)
      (v := wordBytes 8 (C.evlen + 13))
      (by right; simp only [wordBytes, natToBytes_length]; omega)]
    rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
      (a := G.ev + C.evlen) (w := recBytes.length) (off := 16) (w' := 8)
      (bs := recBytes) (by rw [hrecLen]) hsepRec (by decide)]
    exact hInv.log_cap
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    rw [walkReadBytes_log_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) recBytes)
      (z := C.stage.z) (off := 8) (off' := 48) (N := 8)
      (v := wordBytes 8 (C.evlen + 13))
      (by right; simp only [wordBytes, natToBytes_length]; omega)]
    rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
      (a := G.ev + C.evlen) (w := recBytes.length) (off := 48) (w' := 8)
      (bs := recBytes) (by rw [hrecLen]) hsepRec (by decide)]
    exact hInv.log_alen
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    rw [walkReadBytes_log_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) recBytes)
      (z := C.stage.z) (off := 8) (off' := 56) (N := 8)
      (v := wordBytes 8 (C.evlen + 13))
      (by right; simp only [wordBytes, natToBytes_length]; omega)]
    rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
      (a := G.ev + C.evlen) (w := recBytes.length) (off := 56) (w' := 8)
      (bs := recBytes) (by rw [hrecLen]) hsepRec (by decide)]
    exact hInv.log_acap
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    exact walkStaged_write (m' := m4) (m := m3) (a := C.stage.z + 8)
      (bs := wordBytes 8 (C.evlen + 13)) rfl
      (walkStaged_write (m' := m3) (m := m2) (a := G.ev + C.evlen + o5)
        (bs := natToBytes span.toNat 8) rfl
        (walkStaged_write (m' := m2) (m := m1) (a := G.ev + C.evlen + o1)
          (bs := natToBytes (BitVec.ofNat 32 (sinkIn.toNat % 2 ^ 32)).toNat 4) rfl
          (walkStaged_write (m' := m1) (m := s.mem) (a := G.ev + C.evlen)
            (bs := natToBytes tagv.toNat 1) rfl hInv.owned)))
  · dsimp only [s', s₁, envF, walkSetMem, stateAt]
    rw [hmemEq]
    let C' : WalkCarry G := { C with evlen := C.evlen + 13, events := C.events ++ [EventRecord.str (keyBit = 1) (sinkIn.toNat % 2 ^ 32) span.toNat], block := (if keyBit = 1 then "if.then330.i" else "if.else334.i") }
    change UnchangedOutside m0 (writeBytes (writeBytes s.mem (G.ev + C.evlen) recBytes)
      (C.stage.z + 8) (wordBytes 8 (C.evlen + 13))) (walkWide G C')
    refine UnchangedOutside.write_grow (R := walkWide G C') (R' := walkWide G C')
      (a := C.stage.z + 8) (bs := wordBytes 8 (C.evlen + 13)) ?_ ?_ ?_
    · refine UnchangedOutside.write_grow (R := walkWide G C) (R' := walkWide G C')
        (a := G.ev + C.evlen) (bs := recBytes) hInv.frame ?_ ?_
      · intro r hr
        exact walkWide_grow (C' := C') (Nat.le_refl C.alen) (by simp only [C']; omega) rfl r hr
      · refine ⟨(G.ev, C.evlen + 13), by simp [walkWide, walkPresent, C'], by omega, ?_⟩
        rw [hrecLen]; omega
    · intro r hr
      exact ⟨r, hr, le_rfl, le_rfl⟩
    · refine ⟨(C.stage.z, stage2LogExtent), ?_, by omega, ?_⟩
      · show (C.stage.z, stage2LogExtent) ∈ walkWide G C'
        simp [walkWide, walkPresent, stage2ReportScratch, stage2StagedWrites, C']
      · simp only [wordBytes, natToBytes_length, stage2LogExtent, C']; omega
/-- The token and the log are separate regions of the staging. -/
theorem tok_z_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.tok + stage2TokenExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.tok := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 11 13 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h' 

/-- The token and the event stream are separate regions of the staging. -/
theorem tok_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.tok + stage2TokenExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.tok := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 11 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- The refusal arm's exit: the five live-range ends and the three copies into
the record's slots. -/
def walkIfThenBlock : Block :=
  { name := "if.then",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 8))), (.ptr, .reg "%xj.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 4))), (.ptr, .reg "%root_done.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%cst.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%ctype.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 1192))), (.ptr, .reg "%c.i")],
      Instr.load "%51" (.int 64) (.reg "%alen"),
      Instr.store (.int 64) (.reg "%51") (.reg "%ndst"),
      Instr.load "%52" (.int 64) (.reg "%len"),
      Instr.store (.int 64) (.reg "%52") (.reg "%nev"),
      Instr.gep "%off" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.load "%53" (.int 64) (.reg "%off"),
      Instr.store (.int 64) (.reg "%53") (.reg "%err")],
    term := Term.br "if.end" }

theorem walkIfThenBlock_find : stage2Body.findBlock "if.then" = some walkIfThenBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThenBlock]

/-- The refusal arm's output, named: the record's three slots written and the
four cells the block's loads and `gep` leave, over the block's writes.  The state
`walkIfThenBlock_denote` concludes to, spelled once here so a consumer can name it
instead of printing a term whose own elaboration the module option cannot afford. -/
def walkIfThenBlockState (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) : State :=
  stateAt
    (cells [("%53", .int 64 E), ("%off", .ptr (e + 8)),
      ("%52", .int 64 L), ("%51", .int 64 A)] env)
    (walkSetMem s (writeBytes (writeBytes (writeBytes s.mem nd
      (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat)) err (wordBytes 8 E.toNat)))

/-- **The refusal arm's copy.**  The same live-range prefix as `s2_walk.exit`,
then the arena's cursor, the event stream's, and the error's offset into the
record's three slots. -/
theorem walkIfThenBlock_denote {sub : Calls} (env : Env) (s : State)
    {a : Nat} {A : BitVec 64} {l : Nat} {L : BitVec 64}
    {xj rd cst ctp c e nd nv err : Nat} {E : BitVec 64}
    (hxj : lookupName env "%xj.i" = some (.ptr xj))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hcst : lookupName env "%cst.i" = some (.ptr cst))
    (hctp : lookupName env "%ctype.i" = some (.ptr ctp))
    (hc : lookupName env "%c.i" = some (.ptr c))
    (halen : lookupName env "%alen" = some (.ptr a))
    (hnd : lookupName env "%ndst" = some (.ptr nd))
    (hlen : lookupName env "%len" = some (.ptr l))
    (hnev : lookupName env "%nev" = some (.ptr nv))
    (he : lookupName env "%e" = some (.ptr e))
    (herr : lookupName env "%err" = some (.ptr err))
    (hA : readBytes s.mem a 8 = some (natToBytes A.toNat 8))
    (hL : readBytes s.mem l 8 = some (natToBytes L.toNat 8))
    (hE : readBytes s.mem (e + 8) 8 = some (natToBytes E.toNat 8))
    (hsep : nd + 8 ≤ l ∨ l + 8 ≤ nd)
    (hsepE1 : nd + 8 ≤ e + 8 ∨ e + 8 + 8 ≤ nd)
    (hsepE2 : nv + 8 ≤ e + 8 ∨ e + 8 + 8 ≤ nv) :
    denoteCode (stage2Calls sub) walkIfThenBlock.instrs (stateAt env s) =
      some (stateAt
        (cells [("%53", .int 64 E), ("%off", .ptr (e + 8)),
          ("%52", .int 64 L), ("%51", .int 64 A)] env)
        (walkSetMem s (writeBytes (writeBytes (writeBytes s.mem nd
          (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat)) err (wordBytes 8 E.toNat)))) := by
  simp only [walkIfThenBlock]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 8) (obj := "%xj.i") (p := xj) (by simpa [lookupName] using hxj)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 4) (obj := "%root_done.i") (p := rd) (by simpa [lookupName] using hrd)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 520) (obj := "%cst.i") (p := cst) (by simpa [lookupName] using hcst)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 520) (obj := "%ctype.i") (p := ctp) (by simpa [lookupName] using hctp)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 1192) (obj := "%c.i") (p := c) (by simpa [lookupName] using hc)]
  have hL' : readBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) l 8 =
      some (natToBytes L.toNat 8) := by
    rw [walkReadBytes_writeBytes_outside (start := nd) (addr := l) (n := 8)
      (v := wordBytes 8 A.toNat) (by
        rw [wordBytes, natToBytes_length]
        rcases hsep with h | h
        · right; exact h
        · left; exact h)]
    exact hL
  have hE' : readBytes (writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv
      (wordBytes 8 L.toNat)) (e + 8) 8 = some (natToBytes E.toNat 8) := by
    rw [walkReadBytes_writeBytes_outside (start := nv) (addr := e + 8) (n := 8)
      (v := wordBytes 8 L.toNat) (by
        rw [wordBytes, natToBytes_length]
        rcases hsepE2 with h | h
        · right; exact h
        · left; exact h)]
    rw [walkReadBytes_writeBytes_outside (start := nd) (addr := e + 8) (n := 8)
      (v := wordBytes 8 A.toNat) (by
        rw [wordBytes, natToBytes_length]
        rcases hsepE1 with h | h
        · right; exact h
        · left; exact h)]
    exact hE
  rw [denoteCode_load64 (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%51") (p := "%alen") (a := a) (v := A)
    (by simpa [lookupName] using halen) hA]
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub)
    (env := ("%51", .int 64 A) :: env) (s := s)
    (v := "%51") (p := "%ndst") (a := nd) (j := A.toNat)
    (by simp [lookupName]) A.isLt (by simpa [lookupName] using hnd)]
  rw [denoteCode_load64 (calls := stage2Calls sub)
    (env := ("%51", .int 64 A) :: env)
    (s := { s with mem := writeBytes s.mem nd (wordBytes 8 A.toNat) })
    (d := "%52") (p := "%len") (a := l) (v := L)
    (by simpa [lookupName] using hlen) hL']
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub)
    (env := ("%52", .int 64 L) :: ("%51", .int 64 A) :: env)
    (s := { s with mem := writeBytes s.mem nd (wordBytes 8 A.toNat) })
    (v := "%52") (p := "%nev") (a := nv) (j := L.toNat)
    (by simp [lookupName]) L.isLt (by simpa [lookupName] using hnev)]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub)
    (env := ("%52", .int 64 L) :: ("%51", .int 64 A) :: env)
    (s := { s with mem := writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat) })
    (d := "%off") (base := "%e") (a := e) (w := 64) (n := BitVec.ofNat 64 8)
    (by simpa [lookupName] using he) (by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofNat 64 8)).toNat = 8 from by decide]
  rw [denoteCode_load64 (calls := stage2Calls sub)
    (env := ("%off", .ptr (e + 8)) :: ("%52", .int 64 L) :: ("%51", .int 64 A) :: env)
    (s := { s with mem := writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat) })
    (d := "%53") (p := "%off") (a := e + 8) (v := E)
    (by simp [lookupName]) hE']
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub)
    (env := ("%53", .int 64 E) :: ("%off", .ptr (e + 8)) ::
      ("%52", .int 64 L) :: ("%51", .int 64 A) :: env)
    (s := { s with mem := writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat) })
    (v := "%53") (p := "%err") (a := err) (j := E.toNat)
    (by simp [lookupName]) E.isLt (by simpa [lookupName] using herr)]
  dsimp only [walkSetMem]
  rfl

/-- The refusal arm's copy, in the named state: the same premise set concluding to
`walkIfThenBlockState`, so a consumer never prints the copied state's term. -/
theorem walkIfThenBlock_denote_named {sub : Calls} (env : Env) (s : State)
    {a : Nat} {A : BitVec 64} {l : Nat} {L : BitVec 64}
    {xj rd cst ctp c e nd nv err : Nat} {E : BitVec 64}
    (hxj : lookupName env "%xj.i" = some (.ptr xj))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hcst : lookupName env "%cst.i" = some (.ptr cst))
    (hctp : lookupName env "%ctype.i" = some (.ptr ctp))
    (hc : lookupName env "%c.i" = some (.ptr c))
    (halen : lookupName env "%alen" = some (.ptr a))
    (hnd : lookupName env "%ndst" = some (.ptr nd))
    (hlen : lookupName env "%len" = some (.ptr l))
    (hnev : lookupName env "%nev" = some (.ptr nv))
    (he : lookupName env "%e" = some (.ptr e))
    (herr : lookupName env "%err" = some (.ptr err))
    (hA : readBytes s.mem a 8 = some (natToBytes A.toNat 8))
    (hL : readBytes s.mem l 8 = some (natToBytes L.toNat 8))
    (hE : readBytes s.mem (e + 8) 8 = some (natToBytes E.toNat 8))
    (hsep : nd + 8 ≤ l ∨ l + 8 ≤ nd)
    (hsepE1 : nd + 8 ≤ e + 8 ∨ e + 8 + 8 ≤ nd)
    (hsepE2 : nv + 8 ≤ e + 8 ∨ e + 8 + 8 ≤ nv) :
    denoteCode (stage2Calls sub) walkIfThenBlock.instrs (stateAt env s) =
      some (walkIfThenBlockState env nd nv err e A L E s) := by
  simpa only [walkIfThenBlockState]
    using walkIfThenBlock_denote (sub := sub) env s hxj hrd hcst hctp hc halen hnd
      hlen hnev he herr hA hL hE hsep hsepE1 hsepE2

/-- **The refusal arm's step**: `if.then` jumps to the return. -/
theorem walkIfThen_step {sub : Calls} (s : State) (hpc : s.pc = "if.then")
    {s₁ : State}
    (hden : denoteCode (stage2Calls sub) walkIfThenBlock.instrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls sub) stage2Body s =
      .jump { s₁ with pc := "if.end", pre := some s.pc } := by
  have hfind : stage2Body.findBlock s.pc = some walkIfThenBlock := by
    rw [hpc]; exact walkIfThenBlock_find
  simp only [LeanLLVM.step, hfind, hden]
  dsimp only [walkIfThenBlock, execTerm]
  rw [hpc₁]

/-! ## The refusal arm's copy

`if.then` is the walk's other finalisation arm: the same five live-range ends as
`s2_walk.exit`, then the arena's cursor, the event stream's and the error's offset
copied into the record's three slots.  Its stores are the record's, outside the
walk's frame (`err_not_in_walkFrame`), so it is the terminal step's second
refusal arm and not a link: `walkIfThenBlock_denote` is the copy and
`walkIfThen_step` the jump to `if.end`, which `WalkChain.finalisation` composes
with the chain in the same way as the exit's. -/

/-! ## The error offset's computed store

`if.then25.i` stores the number's length plus its entry index at `%e + 8` and
closes the two live ranges `num_fast_el1` opened.  The stored value is computed
from the number path's output slot `%ei.i` (one of the four allocas, at the
allocator's cursor), so the run's own load is the slot's eight bytes, and the
store is the refusal offset's only *computed* value: the eighteen class C stores
write a register the invariant binds, this one an addition of two.  The write is
inside the error object's staged extent (`eoff_inside`), so the frame, presence
and the two streams' reads are the refusal store's four facts
(`walkReadBytes_log_of_eoff_write`, `walkReadBytes_ev_of_eoff_write`), and the
carry is unchanged: the walk itself never reads the refusal slot. -/

/-- `if.then25.i`: the number's length stored as the error offset, and the two
live-range ends. -/
def walkIfThen25I : Block :=
  { name := "if.then25.i",
    instrs := [
      Instr.load "%43" (Ty.int 64) (Operand.reg "%ei.i"),
      Instr.binop "%add.i100" BinOp.add 64 (Operand.reg "%43") (Operand.reg "%idxprom.i"),
      Instr.gep "%off1.i.i101" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%add.i100") (Operand.reg "%off1.i.i101"),
      Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 8))), (Ty.ptr, Operand.reg "%ei.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 8))), (Ty.ptr, Operand.reg "%d.i")]],
    term := Term.br "cleanup474.i" }

theorem walkIfThen25I_find : stage2Body.findBlock "if.then25.i" = some walkIfThen25I := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen25I]

theorem walkIfThen25I_denote {sub : Calls} (env : Env) (s : State)
    {v ix : BitVec 64} {ei e dp : Nat}
    (hei : lookupName env "%ei.i" = some (.ptr ei))
    (hread : readBytes s.mem ei 8 = some (natToBytes v.toNat 8))
    (hidx : lookupName env "%idxprom.i" = some (.int 64 ix))
    (he : lookupName env "%e" = some (.ptr e))
    (hd : lookupName env "%d.i" = some (.ptr dp)) :
    denoteCode (stage2Calls sub) walkIfThen25I.instrs (stateAt env s) =
      some (stateAt (cells [("%off1.i.i101", .ptr (e + 8)),
        ("%add.i100", .int 64 (v + ix)), ("%43", .int 64 v)] env)
        { s with mem := writeBytes s.mem (e + 8) (natToBytes (v + ix).toNat 8) }) := by
  simp only [walkIfThen25I]
  rw [denoteCode_load64 (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%43") (p := "%ei.i") (a := ei) (v := v) (by simpa using hei) hread]
  rw [denoteCode_add_reg (calls := stage2Calls sub)
    (env := ("%43", .int 64 v) :: env) (s := s) (d := "%add.i100")
    (a := "%43") (b := "%idxprom.i") (x := v) (y := ix)
    (by simp [lookupName]) (by simpa [lookupName] using hidx)]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub)
    (env := ("%add.i100", .int 64 (v + ix)) :: ("%43", .int 64 v) :: env) (s := s)
    (d := "%off1.i.i101") (base := "%e") (a := e) (w := 64) (n := BitVec.ofNat 64 8)
    (by simpa [lookupName] using he) (by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofNat 64 8)).toNat = 8 from by decide]
  rw [denoteCode_store64 (calls := stage2Calls sub)
    (env := ("%off1.i.i101", .ptr (e + 8)) :: ("%add.i100", .int 64 (v + ix)) ::
      ("%43", .int 64 v) :: env) (s := s)
    (v := "%add.i100") (p := "%off1.i.i101") (x := v + ix) (a := e + 8)
    (by simp [lookupName]) (by simp [lookupName])]
  rw [walkDenoteCode_lifetimeEnd (sub := sub)
    (env := ("%off1.i.i101", .ptr (e + 8)) :: ("%add.i100", .int 64 (v + ix)) ::
      ("%43", .int 64 v) :: env)
    (s := { s with mem := writeBytes s.mem (e + 8) (natToBytes (v + ix).toNat 8) })
    (size := 8) (obj := "%ei.i") (p := ei) (by simpa [lookupName] using hei)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub)
    (env := ("%off1.i.i101", .ptr (e + 8)) :: ("%add.i100", .int 64 (v + ix)) ::
      ("%43", .int 64 v) :: env)
    (s := { s with mem := writeBytes s.mem (e + 8) (natToBytes (v + ix).toNat 8) })
    (size := 8) (obj := "%d.i") (p := dp) (by simpa [lookupName] using hd)]
  rfl

/-- **`if.then25.i` is a link**: the number's length plus its entry index is
stored as the error's offset, and the two live-range ends close `%ei.i` and
`%d.i`.  The carry is unchanged: the block's store is the report's, and the walk
does not read the refusal slot. -/
theorem WalkLink.if_then25_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then25.i")
    {v ix : BitVec 64}
    (hei : lookupName s.env "%ei.i" = some (.ptr G.next0))
    (hread : readBytes s.mem G.next0 8 = some (natToBytes v.toNat 8))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hd : lookupName s.env "%d.i" = some (.ptr (G.next0 + 12))) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := "cleanup474.i" } s' := by
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    rw [hlen]; omega
  have hstTy : WalkStackBytes (writeBytes s.mem (C.stage.e + 8)
      (natToBytes (v + ix).toNat 8)) C.stage.ctype C.tyMap C.wlen := by
    refine hInv.tyBytes.write_outside ?_
    have hwl : (natToBytes (v + ix).toNat 8).length = 8 := natToBytes_length _ _
    have hx : stage2ErrorExtent = 24 := rfl
    rcases (stack_e_sep hInv).1 with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hstSt : WalkStackBytes (writeBytes s.mem (C.stage.e + 8)
      (natToBytes (v + ix).toNat 8)) C.stage.cst C.stMap C.wlen := by
    refine hInv.stBytes.write_outside ?_
    have hwl : (natToBytes (v + ix).toNat 8).length = 8 := natToBytes_length _ _
    have hx : stage2ErrorExtent = 24 := rfl
    rcases (stack_e_sep hInv).2 with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  refine WalkLink.callQuiet (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := C.stMap) (hstTy := hstTy) (hstSt := hstSt)
    (B := walkIfThen25I) (by rw [hblock]; exact walkIfThen25I_find)
    (s₁ := stateAt (cells [("%off1.i.i101", .ptr (C.stage.e + 8)),
      ("%add.i100", .int 64 (v + ix)), ("%43", .int 64 v)] s.env)
      { s with mem := writeBytes s.mem (C.stage.e + 8) (natToBytes (v + ix).toNat 8) })
    (walkIfThen25I_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (v := v) (ix := ix) (ei := G.next0) (e := C.stage.e) (dp := G.next0 + 12)
      hei hread hidx he hd)
    (by unfold walkCarried; decide) rfl
    (by
      dsimp only [stateAt]
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      rw [natToBytes_length] at hk
      exact walkWide_of_seven
        (eoff_inside (c := C.stage.c) (ctype := C.stage.ctype) (cst := C.stage.cst)
          (tok := C.stage.tok) (s := C.stage.s) (z := C.stage.z) (e := C.stage.e)
          (k := k) (by omega)))
    (by
      dsimp only [stateAt]
      exact walkStaged_write (m := s.mem) (a := C.stage.e + 8)
        (bs := natToBytes (v + ix).toNat 8) rfl hInv.owned)
    (by
      dsimp only [stateAt]
      intro off w hw
      have hoff : off + w ≤ stage2LogExtent := hw
      rw [show natToBytes (v + ix).toNat 8 = wordBytes 8 (v + ix).toNat from rfl]
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z)
        (off := off) (j := (v + ix).toNat) (N := w) (e_z_sep hInv) hoff])
    (by
      dsimp only [stateAt]
      rw [show natToBytes (v + ix).toNat 8 = wordBytes 8 (v + ix).toNat from rfl]
      rw [walkReadBytes_ev_of_eoff_write (e := C.stage.e) (ev := G.ev)
        (evcap := G.evcap) (nev0 := G.nev0) (j := (v + ix).toNat) (e_ev_sep hInv) hN])
    rfl (by simp [WalkLocal])

/-! ## The kind byte

`if.then413.i` writes the scalar's kind byte at `%kind404.i` (`%t352.i + 16`,
inside the token's staged extent), reads the root flag from `%root_done.i`, and
asks `s2_value_pos` for the container's depth verdict.  Its run is also the
dispatch's one five-way `phi` over immediate operands: the kind is a literal on
every incoming edge, so the `phi` step is `denoteCode_phi` at the operand its
predecessor names, and the block's own store is the first thing the verdict is
read against.  The call writes nothing, so the link is the in-frame store's four
memory facts plus the call's contract; the store and the token are separated from
the log and the event stream by `tok_z_sep`/`tok_ev_sep` (above). -/

/-- `if.then413.i`: the kind byte, the root flag, and `s2_value_pos`'s verdict. -/
def walkIfThen413I : Block :=
  { name := "if.then413.i",
    instrs := [
      Instr.phi "%.sink372" (Ty.int 32)
        [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
         ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
         ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
         ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
         ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))],
      Instr.store (Ty.int 32) (Operand.reg "%.sink372") (Operand.reg "%kind404.i"),
      Instr.load "%38" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call416.i" (Ty.int 32) "s2_value_pos"
        [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%38"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")],
      Instr.icmp "%tobool417.not.i" IPred.eq 32 (Operand.reg "%call416.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%tobool417.not.i") "if.then418.i" "if.then425.i" }

theorem walkIfThen413I_find : stage2Body.findBlock "if.then413.i" = some walkIfThen413I := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen413I]

theorem walkIfThen413I_denote {sub : Calls} (env : Env) (s : State)
    {p reg : String} {c : BitVec 32} {kind root : Nat} {rdv : BitVec 32}
    {sp : BitVec 32} {ct cs : Nat} {r : CallOutcome} {x : BitVec 32} {op : Operand}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 c))
    (hkind : lookupName env "%kind404.i" = some (.ptr kind))
    (hroot : lookupName env "%root_done.i" = some (.ptr root))
    (hread : readBytes (writeBytes s.mem kind (natToBytes c.toNat 4)) root 4 =
      some (natToBytes rdv.toNat 4))
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 sp))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_value_pos"
      [.int 32 sp, .int 32 rdv, .ptr ct, .ptr cs]
      (writeBytes s.mem kind (natToBytes c.toNat 4)) s.next = some r)
    (hret : r.ret = .int 32 x) :
    denoteCode (stage2Calls sub) walkIfThen413I.instrs (stateAt env s) =
      some (stateAt
        (cells [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
          ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
          ("%.sink372", .int 32 c)] env)
        { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen413I]
  rw [denoteCode_phi (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%.sink372") (ty := .int 32)
    (inc := [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
      ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
      ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
      ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
      ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))])
    (p := p) (op := op) (v := .int 32 c) hpre hinc hop _ (by decide)]
  rw [denoteCode_store32 (calls := stage2Calls sub)
    (env := ("%.sink372", .int 32 c) :: env) (s := s) (v := "%.sink372")
    (p := "%kind404.i") (x := c) (a := kind)
    (by simp [lookupName]) (by simpa [lookupName] using hkind)]
  rw [denoteCode_load_i32 (calls := stage2Calls sub)
    (env := ("%.sink372", .int 32 c) :: env)
    (s := { s with mem := writeBytes s.mem kind (natToBytes c.toNat 4) })
    (d := "%38") (p := "%root_done.i") (a := root) (v := rdv)
    (by simpa [lookupName] using hroot) hread]
  rw [walkDenoteCode_call (calls := stage2Calls sub)
    (env := ("%38", .int 32 rdv) :: ("%.sink372", .int 32 c) :: env)
    (s := { s with mem := writeBytes s.mem kind (natToBytes c.toNat 4) })
    (d := "%call416.i") (ty := Ty.int 32) (callee := "s2_value_pos")
    (args := [(Ty.int 32, Operand.reg "%sp.i.0248"), (Ty.int 32, Operand.reg "%38"),
      (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 sp, .int 32 rdv, .ptr ct, .ptr cs]) (r := r) ?_ hcall]
  · rw [hret]
    rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
      (env := ("%call416.i", .int 32 x) :: ("%38", .int 32 rdv) ::
        ("%.sink372", .int 32 c) :: env)
      (s := { s with mem := r.mem, next := r.next })
      (d := "%tobool417.not.i") (a := "%call416.i") (w := 32)
      (x := x) (c := BitVec.ofNat 32 0) (by simp [lookupName])]
    rfl
  · refine walkArgs_valuePos (("%38", .int 32 rdv) :: ("%.sink372", .int 32 c) :: env) s
      ?_ ?_ ?_ ?_
    · simpa [lookupName] using hsp
    · rfl
    · simpa [lookupName] using hct
    · simpa [lookupName] using hcs

/-- **`if.then413.i` is a link**: the kind byte is written inside the token's
staged extent, and `s2_value_pos`'s verdict decides the arm. -/
theorem WalkLink.if_then413_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p reg : String} {c : BitVec 32} {op : Operand} {rdv : BitVec 32} {x : BitVec 32}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 c))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre' : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next)
    (hx : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
          then "if.then418.i" else "if.then425.i") } s' := by
  obtain ⟨r, hcall, hpost, -⟩ := s2ValuePosContract.resolves (next := s.next) hpre'
  obtain ⟨v, -, hret, hmem, -⟩ := hpost
  have hret' : r.ret = .int 32 x := hx r hcall
  have hstTy : WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen := by
    rw [hmem]
    refine hInv.tyBytes.write_outside ?_
    have hwl : (natToBytes c.toNat 4).length = 4 := natToBytes_length _ _
    have htok : stage2TokenExtent = 24 := rfl
    rcases (stack_tok_sep hInv).1 with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hstSt : WalkStackBytes r.mem C.stage.cst C.stMap C.wlen := by
    rw [hmem]
    refine hInv.stBytes.write_outside ?_
    have hwl : (natToBytes c.toNat 4).length = 4 := natToBytes_length _ _
    have htok : stage2TokenExtent = 24 := rfl
    rcases (stack_tok_sep hInv).2 with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  refine WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := C.stMap) (hstTy := hstTy) (hstSt := hstSt)
    (B := walkIfThen413I) (by rw [hblock]; exact walkIfThen413I_find)
    (s₁ := stateAt
      (cells [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
        ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
        ("%.sink372", .int 32 c)] s.env)
      { s with mem := r.mem, next := r.next })
    (walkIfThen413I_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (p := p) (reg := reg) (c := c) (kind := C.stage.tok + 16)
      (root := G.next0 + 8) (rdv := rdv) (sp := BitVec.ofNat 32 C.sp)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r) (x := x) (op := op)
      hpre hinc hop hkind hrd hread hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hret')
    (by unfold walkCarried; decide) rfl
    (by
      dsimp only [stateAt]; rw [hmem]
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      rw [natToBytes_length] at hk
      refine walkWide_of_seven
        ⟨(C.stage.tok, stage2TokenExtent), by simp [stage2StagedWrites],
          by omega, by simp only [stage2TokenExtent]; omega⟩)
    (by
      dsimp only [stateAt]; rw [hmem]
      exact walkStaged_write (m := s.mem) (a := C.stage.tok + 16)
        (bs := natToBytes c.toNat 4) rfl hInv.owned)
    (by
      dsimp only [stateAt]; rw [hmem]
      intro off w hw
      refine walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
        (addr := C.stage.z + off) (n := w) (v := natToBytes c.toNat 4) ?_
      rw [natToBytes_length]
      rcases tok_z_sep hInv with h | h
      · right
        have h' : C.stage.tok + 24 ≤ C.stage.z := by
          simpa [stage2TokenExtent] using h
        omega
      · left
        have hz : C.stage.z + 64 ≤ C.stage.tok := by
          simpa [stage2LogExtent] using h
        omega)
    (by
      dsimp only [stateAt]; rw [hmem]
      refine walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
        (addr := G.ev + G.nev0)
        (n := (C.events.map EventRecord.encodedBytes).flatten.length)
        (v := natToBytes c.toNat 4) ?_
      rw [natToBytes_length]
      rcases tok_ev_sep hInv with h | h
      · right
        have h' : C.stage.tok + 24 ≤ G.ev := by
          simpa [stage2TokenExtent] using h
        omega
      · left
        have hroom : G.nev0 + 13 * G.n ≤ G.evcap := by
          simpa [stage2RecordBytes] using G.evRoom
        have hsum : (C.events.map EventRecord.encodedSize).sum ≤
            13 * C.events.length := by
          simpa [stage2RecordBytes] using EventRecord.sum_encodedSize_le C.events
        have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
            (C.events.map EventRecord.encodedSize).sum := by
          simp only [List.length_flatten, List.map_map]; rfl
        have h1 := hInv.events_le
        have h2 := hInv.k_le
        have h3 := G.nep_le
        rw [hlen]
        omega)
    rfl
    (by simp [cells, stateAt, lookupName_cons_self])
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-! ## The token's entry

`cond.end349.i` is where the scalar token is filled in before the record it
describes is written: the switch's bound `phi`, the token's own live-range
marker, the token's position and its one-byte gap flag.  It is class F's
store-only shape — no call, but two stores whose addresses the invariant does not
bind — and it is the block `if.then328.i` reads the token at, so its facts are the
record's vertex.

The two stores are at the token's first eight bytes and at `%gap.i`
(`%t352.i + 20`), both inside the token's staged extent, so the frame, presence
and the two streams' reads are the same four facts every in-frame store uses. -/


/-- **`if.then413.i`'s target, with the helper's answer named.**  The consumer's shape: the
call resolves at the staging (the `s2_value_pos` contract's own `resolves`), and the link's
target is the state the block's `denoteCode` leaves — the four cells at the call's result.

The result is exposed rather than hidden because the *next* block reads the memory the call
left: naming it is what makes a store-then-read junction composable. -/
theorem walkIfThen413_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p reg : String} {c : BitVec 32} {op : Operand} {rdv : BitVec 32} {x : BitVec 32}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 c))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre' : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next)
    (hx : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x) :
    ∃ (r : CallOutcome) (s' : State),
      stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
         .ptr C.stage.ctype, .ptr C.stage.cst]
        (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r ∧
      WalkLink (stage2Calls stage2SubCalls) G C s
        { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
            then "if.then418.i" else "if.then425.i") } s' ∧
      s' = TailS₁ s r c rdv x := by
  obtain ⟨r, hcall, hpost, -⟩ := s2ValuePosContract.resolves (next := s.next) hpre'
  obtain ⟨-, -, hret, -, -⟩ := hpost
  obtain ⟨s', hl⟩ := WalkLink.if_then413_i (G := G) (C := C) (s := s) (p := p) (reg := reg)
    hInv hblock hpre hinc hop hkind hrd hread hpre' hx
  refine ⟨r, s', hcall, hl, ?_⟩
  have hret' : r.ret = .int 32 x := hx r hcall
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen413I.instrs s =
      some (stateAt
        (cells [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
          ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
          ("%.sink372", .int 32 c)] s.env)
        { s with mem := r.mem, next := r.next }) := by
    simpa only [stateAt] using (walkIfThen413I_denote (sub := stage2SubCalls) (env := s.env) (s := s)
    (p := p) (reg := reg) (c := c) (kind := C.stage.tok + 16) (root := G.next0 + 8)
    (rdv := rdv) (sp := BitVec.ofNat 32 C.sp) (ct := C.stage.ctype) (cs := C.stage.cst)
    (r := r) (x := x) (op := op) hpre hinc hop hkind hrd hread hInv.depth_reg
    (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hret')
  have hbit : lookupName (stateAt
      (cells [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
        ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
        ("%.sink372", .int 32 c)] s.env) { s with mem := r.mem, next := r.next }).env
      "%tobool417.not.i" = some (.int 1 (evalICmp .eq x (BitVec.ofNat 32 0))) := by
    simp only [stateAt, cells, lookupName_cons_self]
  have hfind : stage2Body.findBlock s.pc = some walkIfThen413I := by
    rw [hInv.pc_eq, hblock]; exact walkIfThen413I_find
  have hterm : walkIfThen413I.term =
      Term.condbr (.reg "%tobool417.not.i") "if.then418.i" "if.then425.i" := rfl
  have hstep : step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump
      { stateAt
          (cells [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
            ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
            ("%.sink372", .int 32 c)] s.env)
          { s with mem := r.mem, next := r.next } with
        pc := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
          then "if.then418.i" else "if.then425.i")
        pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool417.not.i") (tl := "if.then418.i")
      (fl := "if.then425.i") (bit := evalICmp .eq x (BitVec.ofNat 32 0)) hbit]
    dsimp only [stateAt]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **A store of a literal at 32 bits**, the token's gap flag.  `BlockEval`'s
store steps take a register and a 64-bit width; this is the 32-bit literal. -/
theorem walkDenoteCode_store32_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 32) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.imm (.int 32 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hstep : evalInstr calls (stateAt env s)
      (.store (.int 32) (.imm (.int 32 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [evalInstr, evalOperand, Const.toValue, stateAt, hp, storeValue]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- `cond.end349.i`: the switch's bound and the scalar token's two fields. -/
def walkCondEnd349 : Block :=
  { name := "cond.end349.i",
    instrs := [
      Instr.phi "%cond350.i" (.int 64) [("cond.true345.i", .reg "%conv347.i"),
        ("sw.default.i", .reg "%4")],
      Instr.callVoid "llvm.lifetime.start.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 24))), (.ptr, .reg "%t352.i")],
      Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%t352.i"),
      Instr.store (.int 32) (.imm (.int 32 (BitVec.ofNat 32 1))) (.reg "%gap.i"),
      Instr.icmp "%cmp355.i" IPred.ugt 64 (.reg "%cond350.i") (.reg "%idxprom.i")],
    term := Term.condbr (.reg "%cmp355.i") "land.lhs.true357.i" "if.end372.i" }

theorem walkCondEnd349_find : stage2Body.findBlock "cond.end349.i" = some walkCondEnd349 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCondEnd349]

/-- The block's run: the bound's `phi`, the token's marker, its position, its gap
flag and the comparison the scan's first test reads. -/
theorem walkCondEnd349_denote {sub : Calls} (env : Env) (s : State)
    {c ix : BitVec 64} {tk gap : Nat} {reg p : String}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav : lookupName env reg = some (.int 64 c))
    (htok : lookupName env "%t352.i" = some (.ptr tk))
    (hidx : lookupName env "%idxprom.i" = some (.int 64 ix))
    (hgap : lookupName env "%gap.i" = some (.ptr gap)) :
    denoteCode (stage2Calls sub) walkCondEnd349.instrs (stateAt env s) =
      some (stateAt (cells [("%cmp355.i", .int 1 (evalICmp .ugt c ix)),
        ("%cond350.i", .int 64 c)] env)
        { s with mem := writeBytes (writeBytes s.mem tk (natToBytes ix.toNat 8)) gap (natToBytes (BitVec.ofNat 32 1).toNat 4) }) := by
  simp only [walkCondEnd349]
  rw [denoteCode_phi (calls := stage2Calls sub) (env := env) (s := s) (d := "%cond350.i")
    (ty := .int 64)
    (inc := [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")])
    (p := p) (op := .reg reg) (v := .int 64 c)
    hpre hinc (by simpa [evalOperand, stateAt] using hav) _ (by decide)]
  rw [walkDenoteCode_lifetimeStart (sub := sub)
    (env := ("%cond350.i", .int 64 c) :: env) (s := s) (size := 24) (obj := "%t352.i")
    (by simpa [lookupName] using htok)]
  rw [denoteCode_store64 (calls := stage2Calls sub)
    (env := ("%cond350.i", .int 64 c) :: env) (s := s) (v := "%idxprom.i")
    (p := "%t352.i") (x := ix) (a := tk)
    (by simpa [lookupName] using hidx) (by simpa [lookupName] using htok)]
  rw [walkDenoteCode_store32_imm (calls := stage2Calls sub)
    (env := ("%cond350.i", .int 64 c) :: env)
    (s := { s with mem := writeBytes s.mem tk (natToBytes ix.toNat 8) })
    (x := BitVec.ofNat 32 1) (p := "%gap.i") (a := gap)
    (by simpa [lookupName] using hgap)]
  rw [walkDenoteCode_icmp (calls := stage2Calls sub)
    (env := ("%cond350.i", .int 64 c) :: env)
    (s := { s with mem := writeBytes (writeBytes s.mem tk (natToBytes ix.toNat 8)) gap (natToBytes (BitVec.ofNat 32 1).toNat 4) })
    (d := "%cmp355.i") (w := 64) (p := IPred.ugt)
    (oa := .reg "%cond350.i") (ob := .reg "%idxprom.i") (x := c) (y := ix)
    (by simp [evalOperand, stateAt, lookupName])
    (by simpa [evalOperand, stateAt, lookupName] using hidx)]
  rfl

/-- **`cond.end349.i` is a link.**  The token's two stores are inside its staged
extent, so the frame, presence and the two streams' reads are the in-frame store's
four facts, and the token's position and gap flag are what the record's write
reads next. -/
theorem WalkLink.cond_end349_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "cond.end349.i")
    {ix : BitVec 64} {c : BitVec 64} {reg p : String}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav : lookupName s.env reg = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .ugt c ix = 1 then "land.lhs.true357.i" else "if.end372.i") } s' := by
  have hden := walkCondEnd349_denote (sub := stage2SubCalls) (env := s.env) (s := s)
    (c := c) (ix := ix) (tk := C.stage.tok) (gap := C.stage.tok + 20)
    (reg := reg) (p := p) hpre hinc hav htok hidx hgap
  have hsepZ : C.stage.tok + stage2TokenExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.tok := tok_z_sep hInv
  have hsepEv : C.stage.tok + stage2TokenExtent ≤ G.ev ∨
      G.ev + G.evcap ≤ C.stage.tok := tok_ev_sep hInv
  have hsep24 : stage2TokenExtent = 24 := rfl
  have hinside : ∀ k, k < 8 → inRegions (walkWide G C) (C.stage.tok + k) := by
    intro k hk
    exact walkWide_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr)
      ⟨(C.stage.tok, stage2TokenExtent), by simp [stage2StagedWrites, hsep24], by omega,
        by omega⟩)
  have hstTy : WalkStackBytes (writeBytes (writeBytes s.mem C.stage.tok
      (natToBytes ix.toNat 8)) (C.stage.tok + 20)
      (natToBytes (BitVec.ofNat 32 1).toNat 4)) C.stage.ctype C.tyMap C.wlen := by
    refine (hInv.tyBytes.write_outside ?_).write_outside ?_
    · have hwl : (natToBytes ix.toNat 8).length = 8 := natToBytes_length _ _
      have hx : stage2TokenExtent = 24 := rfl
      rcases (stack_tok_sep hInv).1 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · have hwl : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 :=
        natToBytes_length _ _
      have hx : stage2TokenExtent = 24 := rfl
      rcases (stack_tok_sep hInv).1 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  have hstSt : WalkStackBytes (writeBytes (writeBytes s.mem C.stage.tok
      (natToBytes ix.toNat 8)) (C.stage.tok + 20)
      (natToBytes (BitVec.ofNat 32 1).toNat 4)) C.stage.cst C.stMap C.wlen := by
    refine (hInv.stBytes.write_outside ?_).write_outside ?_
    · have hwl : (natToBytes ix.toNat 8).length = 8 := natToBytes_length _ _
      have hx : stage2TokenExtent = 24 := rfl
      rcases (stack_tok_sep hInv).2 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · have hwl : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 :=
        natToBytes_length _ _
      have hx : stage2TokenExtent = 24 := rfl
      rcases (stack_tok_sep hInv).2 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  refine WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
    (TM := C.tyMap) (SM := C.stMap) (hstTy := hstTy) (hstSt := hstSt)
    (B := walkCondEnd349) (by rw [hblock]; exact walkCondEnd349_find)
    (s₁ := stateAt (cells [("%cmp355.i", .int 1 (evalICmp .ugt c ix)),
      ("%cond350.i", .int 64 c)] s.env)
      { s with mem := writeBytes (writeBytes s.mem C.stage.tok (natToBytes ix.toNat 8)) (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4) })
    hden (by unfold walkCarried; decide) rfl
    (by
      dsimp only [stateAt]
      refine (hInv.frame.write_inside (a := C.stage.tok) (bs := natToBytes ix.toNat 8)
        (fun k hk => by
          rw [natToBytes_length] at hk
          exact walkWide_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr)
            ⟨(C.stage.tok, stage2TokenExtent), by simp [stage2StagedWrites, hsep24],
              by omega, by omega⟩))).write_inside
        (a := C.stage.tok + 20) (bs := natToBytes (BitVec.ofNat 32 1).toNat 4)
        (fun k hk => by
          rw [natToBytes_length] at hk
          exact walkWide_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr)
            ⟨(C.stage.tok, stage2TokenExtent), by simp [stage2StagedWrites, hsep24],
              by omega, by omega⟩)))
    (by dsimp only [stateAt]; exact walkStaged_write rfl (walkStaged_write rfl hInv.owned))
    (by
      dsimp only [stateAt]
      intro off w hw
      have hw' : off + w ≤ 64 := hw
      rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
        (addr := C.stage.z + off) (n := w)
        (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
        (addr := C.stage.z + off) (n := w) (v := natToBytes ix.toNat 8)
        (by rw [natToBytes_length]; omega)])
    (by
      dsimp only [stateAt]
      have hsum : (C.events.map EventRecord.encodedSize).sum ≤ 13 * C.events.length := by
        have h := EventRecord.sum_encodedSize_le C.events
        simpa only [stage2RecordBytes] using h
      have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
          (C.events.map EventRecord.encodedSize).sum := by
        simp only [List.length_flatten, List.map_map]; rfl
      have hroom : G.nev0 + 13 * G.n ≤ G.evcap := by
        have h := G.evRoom
        simpa only [stage2RecordBytes] using h
      have hwm : G.ev + G.evcap ≤ G.next0 :=
        G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
      have h1 : C.events.length ≤ C.k := hInv.events_le
      have h2 : C.k ≤ G.nep := hInv.k_le
      have h3 : G.nep ≤ G.n := G.nep_le
      have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
        rw [hlen]; omega
      rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
        (addr := G.ev + G.nev0) (n := (C.events.map EventRecord.encodedBytes).flatten.length)
        (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
        (addr := G.ev + G.nev0) (n := (C.events.map EventRecord.encodedBytes).flatten.length)
        (v := natToBytes ix.toNat 8) (by rw [natToBytes_length]; omega)])
    rfl
    (by simp [cells, stateAt, lookupName_cons_self])
    (by simp [WalkLocal]) (by simp [WalkLocal])


/-- The `if.end` block's `tobool` phi. -/
def walkIfEndIncoming : List (String × Operand) :=
  [("if.then", .imm (.int 64 (BitVec.ofNat 64 0))),
   ("s2_walk.exit", .imm (.int 64 (BitVec.ofNat 64 1)))]

/-- `s2_walk.exit`: the five live-range ends and the two cursor copies. -/
def walkExitBlock : Block :=
  { name := "s2_walk.exit",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 8))), (.ptr, .reg "%xj.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 4))), (.ptr, .reg "%root_done.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%cst.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%ctype.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 1192))), (.ptr, .reg "%c.i")],
      Instr.load "%49" (.int 64) (.reg "%alen"),
      Instr.store (.int 64) (.reg "%49") (.reg "%ndst"),
      Instr.load "%50" (.int 64) (.reg "%len"),
      Instr.store (.int 64) (.reg "%50") (.reg "%nev")],
    term := Term.br "if.end" }

theorem walkExitBlock_find : stage2Body.findBlock "s2_walk.exit" = some walkExitBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkExitBlock]

theorem walkExitBlock_denote {sub : Calls} (env : Env) (s : State)
    {a : Nat} {A : BitVec 64} {l : Nat} {L : BitVec 64}
    {xj rd cst ctp c nd nv : Nat}
    (hxj : lookupName env "%xj.i" = some (.ptr xj))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hcst : lookupName env "%cst.i" = some (.ptr cst))
    (hctp : lookupName env "%ctype.i" = some (.ptr ctp))
    (hc : lookupName env "%c.i" = some (.ptr c))
    (halen : lookupName env "%alen" = some (.ptr a))
    (hnd : lookupName env "%ndst" = some (.ptr nd))
    (hlen : lookupName env "%len" = some (.ptr l))
    (hnev : lookupName env "%nev" = some (.ptr nv))
    (hA : readBytes s.mem a 8 = some (natToBytes A.toNat 8))
    (hL : readBytes s.mem l 8 = some (natToBytes L.toNat 8))
    (hsep : nd + 8 ≤ l ∨ l + 8 ≤ nd) :
    denoteCode (stage2Calls sub) walkExitBlock.instrs (stateAt env s) =
      some (stateAt (cells [("%50", .int 64 L), ("%49", .int 64 A)] env)
        (walkSetMem s (writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv
          (wordBytes 8 L.toNat)))) := by
  rw [show walkExitBlock.instrs = [Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 8))), (.ptr, .reg "%xj.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 4))), (.ptr, .reg "%root_done.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%cst.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 520))), (.ptr, .reg "%ctype.i")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 1192))), (.ptr, .reg "%c.i")],
      Instr.load "%49" (.int 64) (.reg "%alen"),
      Instr.store (.int 64) (.reg "%49") (.reg "%ndst"),
      Instr.load "%50" (.int 64) (.reg "%len"),
      Instr.store (.int 64) (.reg "%50") (.reg "%nev")] from rfl]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 8) (obj := "%xj.i") (p := xj) (by simpa [lookupName] using hxj)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 4) (obj := "%root_done.i") (p := rd) (by simpa [lookupName] using hrd)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 520) (obj := "%cst.i") (p := cst) (by simpa [lookupName] using hcst)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 520) (obj := "%ctype.i") (p := ctp) (by simpa [lookupName] using hctp)]
  rw [walkDenoteCode_lifetimeEnd (sub := sub) (env := env) (s := s)
    (size := 1192) (obj := "%c.i") (p := c) (by simpa [lookupName] using hc)]
  have hL' : readBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) l 8 =
      some (natToBytes L.toNat 8) := by
    rw [walkReadBytes_writeBytes_outside (start := nd) (addr := l) (n := 8)
      (v := wordBytes 8 A.toNat) (by
        rw [wordBytes, natToBytes_length]
        rcases hsep with h | h
        · right; exact h
        · left; exact h)]
    exact hL
  rw [denoteCode_load64 (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%49") (p := "%alen") (a := a) (v := A)
    (by simpa [lookupName] using halen) hA]
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub)
    (env := ("%49", .int 64 A) :: env) (s := s)
    (v := "%49") (p := "%ndst") (a := nd) (j := A.toNat)
    (by simp [lookupName]) A.isLt (by simpa [lookupName] using hnd)]
  rw [denoteCode_load64 (calls := stage2Calls sub)
    (env := ("%49", .int 64 A) :: env)
    (s := { s with mem := writeBytes s.mem nd (wordBytes 8 A.toNat) })
    (d := "%50") (p := "%len") (a := l) (v := L)
    (by simpa [lookupName] using hlen) hL']
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub)
    (env := ("%50", .int 64 L) :: ("%49", .int 64 A) :: env)
    (s := { s with mem := writeBytes s.mem nd (wordBytes 8 A.toNat) })
    (v := "%50") (p := "%nev") (a := nv) (j := L.toNat)
    (by simp [lookupName]) L.isLt (by simpa [lookupName] using hnev)]
  dsimp only [walkSetMem]
  rfl


/-- The `if.end` block: the `tobool` phi, the three markers, and the return. -/
def walkIfEndBlock : Block :=
  { name := "if.end",
    instrs := [
      Instr.phi "%tobool.not151" (.int 64) walkIfEndIncoming,
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 24))), (.ptr, .reg "%e")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 64))), (.ptr, .reg "%z")],
      Instr.callVoid "llvm.lifetime.end.p0"
        [(.int 64, .imm (.int 64 (BitVec.ofNat 64 120))), (.ptr, .reg "%s")]],
    term := Term.ret (.int 64) (some (.reg "%tobool.not151")) }

theorem walkIfEndBlock_find : stage2Body.findBlock "if.end" = some walkIfEndBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfEndBlock, walkIfEndIncoming]

/-- The `if.end` return, at the arm's own bit: `s2_walk.exit` selects `1` and
`if.then` selects `0`.  The markers bind nothing, so they do not move the cell. -/
theorem walkIfEnd_step {sub : Calls} (s : State)
    (hpc : s.pc = "if.end") {p : String} {v : BitVec 64} {bit : BitVec 64}
    {pe pz ps : Nat}
    (he : lookupName s.env "%e" = some (.ptr pe))
    (hz : lookupName s.env "%z" = some (.ptr pz))
    (hs : lookupName s.env "%s" = some (.ptr ps))
    (hpre : s.pre = some p) (hphi : phiIncoming p walkIfEndIncoming = some (Operand.imm (Const.int 64 bit)))
    (hv : bit = v) :
    step (stage2Calls sub) stage2Body s =
      .ret (some (.int 64 v)) (stateAt (("%tobool.not151", .int 64 bit) :: s.env) s) := by
  have hden : denoteCode (stage2Calls sub) walkIfEndBlock.instrs s =
      some (stateAt (("%tobool.not151", .int 64 bit) :: s.env) s) := by
    rw [show walkIfEndBlock.instrs =
      [{ dst := "%tobool.not151", ty := Ty.int 64, incoming := walkIfEndIncoming }].map
          PhiSpec.instr ++
        [Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 24))), (.ptr, .reg "%e")],
         Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 64))), (.ptr, .reg "%z")],
         Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 120))), (.ptr, .reg "%s")]] from rfl]
    rw [denoteCode_phiRun (specs :=
        [{ dst := "%tobool.not151", ty := Ty.int 64, incoming := walkIfEndIncoming }])
      (vs := [("%tobool.not151", .int 64 bit)])
      (rest := [Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 24))), (.ptr, .reg "%e")],
         Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 64))), (.ptr, .reg "%z")],
         Instr.callVoid "llvm.lifetime.end.p0"
          [(.int 64, .imm (.int 64 (BitVec.ofNat 64 120))), (.ptr, .reg "%s")]])
      hpre (PhiSelects.cons hphi (by rfl) PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%tobool.not151", .int 64 bit)] =
      stateAt (("%tobool.not151", .int 64 bit) :: s.env) s from rfl]
    rw [walkDenoteCode_lifetimeEnd (sub := sub)
      (env := ("%tobool.not151", .int 64 bit) :: s.env) (s := s)
      (size := 24) (obj := "%e") (p := pe) (by simpa [lookupName] using he)]
    rw [walkDenoteCode_lifetimeEnd (sub := sub)
      (env := ("%tobool.not151", .int 64 bit) :: s.env) (s := s)
      (size := 64) (obj := "%z") (p := pz) (by simpa [lookupName] using hz)]
    rw [walkDenoteCode_lifetimeEnd (sub := sub)
      (env := ("%tobool.not151", .int 64 bit) :: s.env) (s := s)
      (size := 120) (obj := "%s") (p := ps) (by simpa [lookupName] using hs)]
    rfl
  have hterm : walkIfEndBlock.term =
      Term.ret (.int 64) (some (.reg "%tobool.not151")) := rfl
  simp only [LeanLLVM.step, hpc, walkIfEndBlock_find, hden, hterm, execTerm, evalOperand,
    stateAt, lookupName_cons_self, hv]

/-- **The chain's terminal step.**  A chain whose tail is at `s2_walk.exit`,
followed by the two finalisation blocks, completes the run.  The finalisation is
two control steps: the exit to `if.end` and `if.end`'s return.  It is not a
`WalkLink` pair, because the exit's stores are the record's, outside the walk's
frame by design (`err_not_in_walkFrame`). -/
theorem WalkChain.finalisation {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' s'' sret : State} {v : Value}
    (h : WalkChain calls G C s C' s')
    (hstep1 : step calls stage2Body s' = .jump s'')
    (hret : step calls stage2Body s'' = .ret v sret) :
    ∃ k, runFuel calls k stage2Body s = some (.ret v sret.mem) := by
  obtain ⟨k, hk⟩ := h.steps
  refine ⟨k + 2, ?_⟩
  rw [hk 2]
  simp only [runFuel, hstep1, hret]

/-- **The trace completes within a budget.**  `WalkChain.steps` names the count
and `WalkChain.finalisation` the completion; this states them together: the chain's
step count `k` plus the two finalisation steps, and the run's outcome at *any*
budget at least that.  This is where the count is spent — the obligation's
remaining conjunct is the numeric comparison `k + 2 ≤ stage2Budget args mem` at the
chain the seed produces, and `runFuel_mono_le` is what turns it into the
completion. -/
theorem WalkChain.completesWithin {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' s'' sret : State} {v : Value}
    (h : WalkChain calls G C s C' s')
    (hstep1 : step calls stage2Body s' = .jump s'')
    (hret : step calls stage2Body s'' = .ret v sret) :
    ∃ k, (∀ n, runFuel calls (k + n) stage2Body s = runFuel calls n stage2Body s') ∧
      ∀ N, k + 2 ≤ N → runFuel calls N stage2Body s = some (.ret v sret.mem) := by
  obtain ⟨k, hk⟩ := h.steps
  refine ⟨k, hk, fun N hN => ?_⟩
  have h1 : runFuel calls (k + 2) stage2Body s = some (.ret v sret.mem) := by
    rw [hk 2]
    simp only [runFuel, hstep1, hret]
  exact runFuel_mono_le hN h1

/-! ### The instrument

The module's axis: the step machinery (the call's `denoteCode` step and the
class transfer) and one instance of each shape, measured rather than asserted. -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.callQuiet
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.callQuietBr
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.callQuietBrPending
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_call
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_else334_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then447_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cleanup474_i
#print axioms LeanLLVM.Refinement.WalkScope.walkZArenaReserveExit_find
#print axioms LeanLLVM.Refinement.WalkScope.walkZArenaReserveExit_denote
#print axioms LeanLLVM.Refinement.WalkScope.walkArgs_stringBody
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_store64_imm
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end256_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.z_arena_reserve_exit
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_writeBytes_append
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen328_find
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen328_denote
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then328_i
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen413I_find
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen413I_denote
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then413_i
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen25I_find
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen25I_denote
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then25_i
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThenBlock_find
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThenBlock_denote
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen_step
#print axioms LeanLLVM.Refinement.WalkScope.tok_z_sep
#print axioms LeanLLVM.Refinement.WalkScope.tok_ev_sep
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_store32_imm
#print axioms LeanLLVM.Refinement.WalkScope.walkCondEnd349_find
#print axioms LeanLLVM.Refinement.WalkScope.walkCondEnd349_denote
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_end349_i
#print axioms LeanLLVM.Refinement.WalkStage.rootSlot_log
#print axioms LeanLLVM.Refinement.WalkStage.rootSlot_ev
#print axioms LeanLLVM.Refinement.WalkScope.walkExitBlock_denote
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd_step
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.finalisation
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.completesWithin

/-! ## The four traps

The body's four `unreachable` arms are `@llvm.trap` calls, and `stage2Calls`
answers `none` there — the semantics' `ub` — so no link enters one: an arm whose
step is `ub` cannot be a `WalkLink`'s target.  What a trap verdict owes is
therefore not a link but an exclusion: the guard in front of each trap is clear at
the invariant, so the branch it feeds takes the other successor.

Three of the four are the event stream's reserves, and their arithmetic is
`walkEventReserve_clear` (`JsonStage2WalkRest`): the cursor is the trace's width
sum, one record per entry consumed, and the widest record leaves twelve bytes of
slack at the loop head's strictness.  The fourth is the arena's reserve,
`if.end256.i`'s check `alen + len + 64 > dstcap`, and its exclusion reads the
carry's three pending clauses: `pending_at` bounds the record's arena offset by the
cursor, `pending_cursor` bounds the cursor by the staging's offset plus the
record's entry position, and `pending_len` places the entry's position and the
token's extent inside the document.  The token's own extent is the one number the
exclusion also needs, and it is not derived from the other two: `len`, the
in-flight token's document extent, is a fact about the entry stream, so the
verdict carries `p + len ≤ n` in the carry rather than recomputing it per arm.
The clause set now has a producer: `WalkLink.if_end256_i` sets `pending` to the
triple at the check that reads it, and `WalkLink.if_else285_i` clears it once the
reserved window has been decoded, so a traversal supplies the premise instead of
leaving it empty. -/

/-- A trap arm, at the name the census gives it.  The four are the same block: one
`@llvm.trap` call and `unreachable`. -/
def walkTrapBlock (t : String) : Block :=
  { name := t, instrs := [Instr.callVoid "llvm.trap" []], term := Term.unreachable }

/-- The four trap arms' pins. -/
theorem walkTrapBlock_find {t : String}
    (ht : t = "if.end.i83" ∨ t = "if.end.i.i.i" ∨ t = "if.end.i.i.i64" ∨ t = "if.end.i86") :
    stage2Body.findBlock t = some (walkTrapBlock t) := by
  rcases ht with rfl | rfl | rfl | rfl <;>
    simp [stage2Body, Function.findBlock, findBlockList, walkTrapBlock]

/-- **A trap arm's step is `ub`**: the selection answers `none` at `llvm.trap`, so
the block's `denoteCode` has no value to hand the terminator. -/
theorem step_ub_of_trap (s : State) (hp : s.pc = "if.end.i83" ∨ s.pc = "if.end.i.i.i"
    ∨ s.pc = "if.end.i.i.i64" ∨ s.pc = "if.end.i86") :
    LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = .ub := by
  have hden : denoteCode (stage2Calls stage2SubCalls)
      [Instr.callVoid "llvm.trap" []] s = none := rfl
  rw [LeanLLVM.step, walkTrapBlock_find (t := s.pc) hp]
  dsimp only [walkTrapBlock]
  rw [hden]

/-- **No link enters a trap arm.** -/
theorem walkTrap_noStep (s : State) (hpc : s.pc = "if.end.i83" ∨ s.pc = "if.end.i.i.i"
    ∨ s.pc = "if.end.i.i.i64" ∨ s.pc = "if.end.i86") :
    ¬ ∃ s', LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = .jump s' := by
  rintro ⟨s', hs⟩
  rw [step_ub_of_trap s hpc] at hs
  exact Ctrl.noConfusion hs

/-- **The arena reserve's check is clear** at the invariant: the record in flight
names its entry position, its reservation and its document extent, and the three
clauses `pending_at`, `pending_cursor` and `pending_len` give the check's
conclusion — the cursor is at most the staging's offset plus the entry position,
the position plus the extent is inside the document, and the arena's room covers
the document and the decoder's slack.  Nothing is taken beside the invariant. -/
theorem walkArenaReserve_clear {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {p off len : Nat}
    (hpend : C.pending = some (p, off, len)) :
    C.alen + len + 64 ≤ G.dstcap := by
  have hcur : C.alen ≤ G.ndst0 + p := hInv.pending_cursor p off len hpend
  have hplen : p + len ≤ G.n := hInv.pending_len p off len hpend
  have hroom : G.ndst0 + G.n + stage2ArenaReserve ≤ G.dstcap := G.arenaRoom
  simp only [stage2ArenaReserve] at hroom
  omega

#print axioms LeanLLVM.Refinement.WalkScope.walkTrap_noStep
#print axioms LeanLLVM.Refinement.WalkScope.walkArenaReserve_clear

end WalkScope

end LeanLLVM.Refinement
