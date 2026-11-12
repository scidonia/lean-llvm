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
  nothing, `if.then109.i`, `if.else334.i`, `if.then447.i` (through
  `s2_after_value`) and `if.then19.i` (through `num_fast_el1`) write inside the
  frame and not at any word the invariant reads, `if.end256.i`'s own zero store
  is at `%outn.i`'s slot, and three — `z_arena_reserve.exit` (the decoded body's
  prefix in the arena), `if.then328.i` (a thirteen-byte event record) and
  `if.then425.i` (`od_scalar_value`'s appended record) — move a cursor the carry
  names, so their links are the carry's, not the frame's.  `s2ScalarValuePost`'s
  second conjunct names the appended record, so `if.then425.i`'s call does not
  hide the trace's step behind the model's equation.
* **the terminal step.**  `s2_walk.exit`'s jump and `if.end`'s return are not
  `WalkLink`s: the exit's stores are the record's, outside the walk's frame by
  design (`err_not_in_walkFrame`).  They are `step` equations —
  `walkExitBlock_denote` at the five markers and the two cursor copies, and
  `walkIfEnd_step` at either arm's `phi` value — and `WalkChain.finalisation`
  composes a chain to `s2_walk.exit` with them into a completion.
-/
import LeanLLVM.Refinement.JsonStage2WalkRest
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
    {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s₁ with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := t } s' := by
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
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
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
    {d tl fl : String} (hterm : B.term = Term.condbr (.reg d) tl fl)
    {bit : BitVec 1} (hbit : lookupName s₁.env d = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s₁ with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s₁ with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if bit = 1 then tl else fl) } s' := by
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
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
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
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "cleanup478.i" } s' := by
  obtain ⟨r, hcall, hpost, hfr⟩ :=
    s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  have hfr' : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) := by
    rw [hmem] at hfr; exact hfr
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkAfterValue_facts (G := G) (C := C) (s := s) hInv hm hfr'
  refine WalkLink.callQuiet (G := G) (C := C) (s := s) hInv
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
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
          then "land.rhs457.i" else "if.end473.i") } s' := by
  obtain ⟨r, hcall, hpost, hfr⟩ :=
    s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  have hfr' : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) := by
    rw [hmem] at hfr; exact hfr
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkAfterValue_facts (G := G) (C := C) (s := s) hInv hm hfr'
  refine WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
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
computed, so it composes with that verdict without assuming it: a caller that has
`pending` at the record takes `z_arena_reserve.exit`, and the trap arm is
unreachable (`step_ub_of_trap`). -/

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
    (hA : natToBytes A.toNat 8 = wordBytes 8 C.alen)
    (hC : natToBytes Cc.toNat 8 = wordBytes 8 G.dstcap) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .ugt (cv + (ix ^^^ BitVec.ofNat 64 18446744073709551615)
          + BitVec.ofNat 64 64 + A) Cc = 1 then "if.end.i83" else "z_arena_reserve.exit") } s' := by
  have hz64 : C.stage.z + 64 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites])
    simp only [stage2LogExtent] at h
    exact h
  have hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8) := by
    rw [hA]; exact hInv.log_alen
  have hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8) := by
    rw [hC]; exact hInv.log_acap
  have hden := walkIfEnd256_denote (sub := stage2SubCalls) (env := s.env) (s := s)
    (ix := ix) (cv := cv) (ao := G.next0 + 20) (al := C.stage.z + 48)
    (ac := C.stage.z + 56) (A := A) (C := Cc)
    hidx hconv houtn halen hacap hreadA hreadC (by omega) (by omega)
  refine WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
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

/-- `walkSetMem`: the target state of a store run. -/
def walkSetMem (s : State) (m : Mem) : State := { s with mem := m }

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

/-! ### The instrument

The module's axis: the step machinery (the call's `denoteCode` step and the
class transfer) and one instance of each shape, measured rather than asserted. -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.callQuiet
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.callQuietBr
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_call
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_else334_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then447_i
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cleanup474_i
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_store64_imm
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end256_i
#print axioms LeanLLVM.Refinement.WalkStage.rootSlot_log
#print axioms LeanLLVM.Refinement.WalkStage.rootSlot_ev
#print axioms LeanLLVM.Refinement.WalkScope.walkExitBlock_denote
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd_step
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.finalisation

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
carry's two pending clauses: `pending_at` fixes the record's arena offset at the
cursor and `pending_cursor` bounds the cursor by the staging's offset plus the
record's entry position.  The token's own extent is the one number the exclusion
also needs, and it is not in the carry's vocabulary: `len`, the in-flight token's
document extent, is a fact about the scan that produced it, so the verdict is
stated with `p + len ≤ n` beside it.  That is the exact missing conjunct of the
arena trap, and its producer is the same one `pending_cursor` owes: no link sets
`pending` to `some` yet, so the two clauses are vacuously true and the exclusion is
stated rather than consumed. -/

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
