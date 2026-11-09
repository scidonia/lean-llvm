/-
The list body's traces at its **call** environment, and the fuel its run spends.

The record's theorem is not stated here.  `escape_positions_satisfies` needs the
whole body's run under `escapeListCalls Γ_xl_batch` — the environment that resolves
`@xl_batch` through `envForUnit` — while every block trace below `JsonEscapeListRun`
is stated at the bare intrinsic environment `escapeCalls`.  This module carries the
call environment through those traces; assembling the record's completion and its
`post` on top of the result is the remaining step, and nothing here claims them.

What is stated:

* **The lift.**  `escapeListCalls` differs from `escapeCalls` on exactly one
  callee, `@xl_batch`, so a block whose calls are all at other callees evaluates
  the same instructions at either environment, and `step` at either is the same
  step.  The nine blocks that make no `@xl_batch` call are lifted this way — one
  lemma per block, each from the block's own step lemma — and the writer's head
  block's trace is already at the call environment (`JsonEscapeListWriter`).

* **The run's stages at the call environment.**  The seed chain (`LRunC`, with its
  composition and its `runFuel` reading), the lanes loop as a `CarriedLoop`
  instance and its two bound lemmas, and one continuation lemma per block from
  `xl_lanes.exit` to the emitter's exit.  `writer_at` composes the remaining-block
  writer with the return: nine control steps plus the emitter's own.

* **The writer's entry.**  The inlined batch's claimed stream reads back as the
  position list's first eight entries, and its count cell reads back as the count.
  These are the two read facts `ListLoopInv` is stated over; stating the writer's
  invariant at a state whose memory is the batch's expression makes elaboration
  time out at `whnf`, so the entry needs those facts and the expression derives
  them.
-/
import LeanLLVM.Vellum.JsonEscapeListRun
import LeanLLVM.Vellum.JsonEscapeListWriter

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonB8Steps

/-! ### The call environment at a callee other than `@xl_batch`

`escapeListCalls` answers what `escapeCalls` answers whenever the latter answers at
all, and falls through to the batch's arm only when it does not.  A callee that is
not `@xl_batch` therefore falls through to nothing, and the two environments agree
there without a hypothesis. -/

theorem escapeListCalls_of_ne_xlBatch {Γ : MemContract} {callee : String}
    (hne : callee ≠ "xl_batch") (args : List Value) (mem : Mem) (next : Nat) :
    escapeListCalls Γ callee args mem next = escapeCalls callee args mem next := by
  unfold escapeListCalls
  split
  · rename_i r h
    rw [h]
  · rename_i h
    rw [h]
    unfold envForUnit
    rw [if_neg hne]

/-- An instruction whose call — if it makes one — is at a callee other than
`@xl_batch`, so the two environments evaluate it identically. -/
def noBatchCall : Instr → Bool
  | .call _ _ c _ => c != "xl_batch"
  | .callVoid c _ => c != "xl_batch"
  | _ => true

theorem noBatchCall_of_all {l : List Instr} (h : l.all noBatchCall = true) :
    ∀ i ∈ l, noBatchCall i = true :=
  List.all_eq_true.mp h

/-- A single instruction evaluates the same at either environment, provided its
call is not at `@xl_batch`.  Every non-call constructor reads no environment at
all, so only the two call arms need the agreement. -/
theorem evalInstr_escapeListCalls {Γ : MemContract} (s : State) (i : Instr)
    (h : noBatchCall i = true) :
    evalInstr (escapeListCalls Γ) s i = evalInstr escapeCalls s i := by
  cases i with
  | call d ty c args =>
      simp only [noBatchCall, bne_iff_ne, ne_eq] at h
      simp only [evalInstr]
      cases hm : evalOperands s args with
      | none => rfl
      | some vs =>
          dsimp only
          rw [escapeListCalls_of_ne_xlBatch h]
  | callVoid c args =>
      simp only [noBatchCall, bne_iff_ne, ne_eq] at h
      simp only [evalInstr]
      cases hm : evalOperands s args with
      | none => rfl
      | some vs =>
          dsimp only
          rw [escapeListCalls_of_ne_xlBatch h]
  | binop _ _ _ _ _ => rfl
  | icmp _ _ _ _ _ => rfl
  | icmpPtr _ _ _ _ => rfl
  | select _ _ _ _ _ => rfl
  | trunc _ _ _ _ => rfl
  | zext _ _ _ _ => rfl
  | sext _ _ _ _ => rfl
  | alloca _ _ _ => rfl
  | load _ _ _ => rfl
  | store _ _ _ => rfl
  | gep _ _ _ _ => rfl
  | icmpVec _ _ _ _ _ _ => rfl
  | binopVec _ _ _ _ _ _ => rfl
  | bitcastMask _ _ _ => rfl
  | extractelement _ _ _ _ _ => rfl
  | insertelement _ _ _ _ _ _ => rfl
  | shuffleVec _ _ _ _ _ _ => rfl
  | vecBitcast _ _ _ _ _ _ => rfl
  | phi _ _ _ => rfl

/-- A straight-line instruction sequence evaluates the same at either environment
when none of its instructions calls `@xl_batch`. -/
theorem denoteCode_escapeListCalls {Γ : MemContract} (instrs : List Instr) (s : State)
    (h : ∀ i ∈ instrs, noBatchCall i = true) :
    denoteCode (escapeListCalls Γ) instrs s = denoteCode escapeCalls instrs s := by
  induction instrs generalizing s with
  | nil => rfl
  | cons i is ih =>
      have hi : noBatchCall i = true := h i List.mem_cons_self
      have htail : ∀ j ∈ is, noBatchCall j = true :=
        fun j hj => h j (List.mem_cons_of_mem i hj)
      cases hm : evalInstr escapeCalls s i with
      | none =>
          rw [denoteCode, denoteCode, evalInstr_escapeListCalls s i hi, hm]
      | some s' =>
          rw [denoteCode, denoteCode, evalInstr_escapeListCalls s i hi, hm]
          exact ih s' htail

/-- **One control step is the same at either environment**, at a block that makes
no `@xl_batch` call. -/
theorem step_escapeListCalls {Γ : MemContract} {f : Function} {s : State} {b : Block}
    (hfind : f.findBlock s.pc = some b)
    (h : ∀ i ∈ b.instrs, noBatchCall i = true) :
    step (escapeListCalls Γ) f s = step escapeCalls f s := by
  cases hm : f.findBlock s.pc with
  | none => simp only [step, hm]
  | some b' =>
      have hb' : b' = b := Option.some.inj (hm.symm.trans hfind)
      rw [← hb'] at h
      simp only [step, hm, denoteCode_escapeListCalls b'.instrs s h]

/-- The frame of a run at the call environment: a `runFuel` stated at
`escapeCalls` is the same run at `escapeListCalls`, from a state whose blocks are
all call-free.  Stated as the congruence it is, so a caller supplies the block
hypothesis once per state rather than re-deriving the trace. -/
theorem step_escapeListCalls_at {Γ : MemContract} {f : Function} {s : State}
    {name : String} {b : Block} (hpc : s.pc = name)
    (hfind : f.findBlock name = some b)
    (h : ∀ i ∈ b.instrs, noBatchCall i = true) :
    step (escapeListCalls Γ) f s = step escapeCalls f s := by
  rw [step_escapeListCalls (b := b) (by rw [hpc]; exact hfind) h]

/-! ### The blocks that make no `@xl_batch` call

Nine of the body's ten blocks are call-free at `@xl_batch`: the three seed blocks,
the lanes loop's body, its exit, the inlined batch, the two writer preheaders and
the emitter's exit.  The tenth, `while.body.i.i`, is the writer's head, and its
trace is already stated at the call environment. -/

theorem lstEntry_noBatch : lstEntry.instrs.all noBatchCall = true := by decide
theorem lstIfThen_noBatch : lstIfThen.instrs.all noBatchCall = true := by decide
theorem lstIfEnd_noBatch : lstIfEnd.instrs.all noBatchCall = true := by decide
theorem lanesBody_noBatch : lanesBodyBlock.instrs.all noBatchCall = true := by decide
theorem lstLanesExit_noBatch : lstLanesExit.instrs.all noBatchCall = true := by decide
theorem lstIfEnd4_noBatch : lstIfEnd4.instrs.all noBatchCall = true := by decide
theorem lstForPre_noBatch : lstForPre.instrs.all noBatchCall = true := by decide
theorem lstWhilePre_noBatch : lstWhilePre.instrs.all noBatchCall = true := by decide
theorem lstEmitExit_noBatch : lstEmitExit.instrs.all noBatchCall = true := by decide

/-! ### The seed blocks, lifted

Each is its block lemma with the step transported; the hypotheses and the
conclusion's successor state are the block lemma's own. -/

theorem entry_step_calls {Γ : MemContract} (env : Env) (s : State) (pre : Option String)
    (bs w0 : BitVec 64) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld : readBytes s.mem carry 8 = some (natToBytes w0.toNat 8)) :
    step (escapeListCalls Γ) escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs w0 carry) s
        (if ((bs &&& (BitVec.ofInt 64 1)) &&& w0) = (0 : BitVec 64)
          then "if.end.i" else "if.then.i")
        (some "entry")) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "entry") (b := lstEntry) (by rfl)
    findBlock_entry (noBatchCall_of_all lstEntry_noBatch)]
  exact entry_step env s pre bs w0 carry hbs hcarry hld

theorem ifThen_step_calls {Γ : MemContract} (env : Env) (s : State) (pre : Option String)
    (bs w1 andI : BitVec 64) (a : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (handI : lookupName env "%and.i" = some (.int 64 andI))
    (harr : lookupName env "%arrayidx1" = some (.ptr a))
    (hld : readBytes s.mem a 8 = some (natToBytes w1.toNat 8)) :
    step (escapeListCalls Γ) escapeListFunction (site env s "if.then.i" pre) =
      .jump (site (ifThenEnv env bs w1 andI) s "if.end.i" (some "if.then.i")) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "if.then.i") (b := lstIfThen) (by rfl)
    findBlock_ifThen (noBatchCall_of_all lstIfThen_noBatch)]
  exact ifThen_step env s pre bs w1 andI a hbs handI harr hld

theorem ifEnd_step_calls {Γ : MemContract} (env : Env) (s : State) (pre : Option String)
    (bs e0 : BitVec 64) (p : String) (op : Operand)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hshl : lookupName env "%shl.i" = some (.int 64 (bs <<< 1)))
    (hpre : pre = some p)
    (hinc : phiIncoming p [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")] = some op)
    (hop : evalOperand (site env s "if.end.i" pre) op = some (.int 64 e0)) :
    step (escapeListCalls Γ) escapeListFunction (site env s "if.end.i" pre) =
      .jump (site (ie13 env bs e0) s
        (if em11 bs e0 = (0 : BitVec 64) then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "if.end.i") (b := lstIfEnd) (by rfl)
    findBlock_ifEnd (noBatchCall_of_all lstIfEnd_noBatch)]
  exact ifEnd_step env s pre bs e0 p op hbs hshl hpre hinc hop

/-! ### `do.body.i` lifted, at the loop's call environment -/

theorem lstDoBody_step_calls {Γ : MemContract} (env : Env) (s : State) (bs w : BitVec 64)
    (p : String) (op : Operand) (env0 : Env)
    (hpc : (withEnv env s).pc = "do.body.i")
    (hpre : (withEnv env s).pre = some p)
    (hinc : phiIncoming p lstDoBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hmask : lookupName env "%and7.i" = some (.int 64 (stepMask bs)))
    (hkeeps : lstLanesKeeps env0 env) :
    step (escapeListCalls Γ) escapeListFunction (withEnv env s) =
      .jump (withEnv (ld5 env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) ∧
    lstLanesKeeps env0 (ld5 env bs w) ∧
    lookupName (ld5 env bs w) "%and7.i" = some (.int 64 (stepMask bs)) ∧
    lookupName (ld5 env bs w) "%e.1.i" = some (.int 64 w) ∧
    lookupName (ld5 env bs w) "%or23.i" = some (.int 64 (stepWord bs w)) := by
  obtain ⟨hstep, rest⟩ := lstDoBody_step env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
  exact ⟨by
    rw [step_escapeListCalls_at (Γ := Γ) (name := "do.body.i") (b := lanesBodyBlock) hpc
      lanes_findBlock_body (noBatchCall_of_all lanesBody_noBatch)]
    exact hstep, rest⟩

/-! ### The lanes loop at the call environment

The same `CarriedLoop` instance as `JsonEscapeListLoop`'s, at `escapeListCalls`: the
fields are the lifted head block's two arms, and they are the only place the loop
consumes a step. -/

def lstLanesLoopCalls (Γ : MemContract) (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) :
    CarriedLoop (escapeListCalls Γ) escapeListFunction where
  head := "do.body.i"
  exitBlock := "xl_lanes.exit"
  map := stepWord bs
  seed := escapeSeed bs prevb prevs
  N := 32
  Inv := lstLanesInv bs prevb prevs env0
  ExitWord := lstLanesExitWord env0
  step_exit := by
    intro i s w h hfix
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, _hiter, _hbound, hkeeps⟩ := h
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre hop ⊢
    obtain ⟨hstep, hkeeps', _hmask', he, _hor⟩ :=
      lstDoBody_step_calls s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    exact ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, he, hkeeps'⟩
  step_loop := by
    intro i s w h hfix
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, hiter, hbound, hkeeps⟩ := h
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre hop ⊢
    obtain ⟨hstep, hkeeps', hmask', he, hor⟩ :=
      lstDoBody_step_calls s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    refine ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, ?_⟩
    have hi32 : i ≠ 32 := by
      intro h32
      refine hfix ?_
      rw [hiter, h32]
      exact stepN_32_is_fixed bs prevb prevs
    refine ⟨by simp only [hfix]; rfl, hmask', ⟨"do.body.i", .reg "%or23.i", rfl, ?_, ?_⟩,
      ?_, by omega, hkeeps'⟩
    · decide
    · show evalOperand (withEnv (ld5 s.env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) (.reg "%or23.i") = some (.int 64 (stepWord bs w))
      simpa only [withEnv, evalOperand] using hor
    · rw [hiter, stepN_succ]
  word_iterate := by
    intro i s w h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := h
    rw [hiter, stepN_eq_iter]
  bound := by
    intro i s w h
    exact h.2.2.2.2.1
  fixed := by
    intro s w h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := h
    rw [hiter]
    exact stepN_32_is_fixed bs prevb prevs

theorem lanes_run_calls {Γ : MemContract} (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env)
    (i : Nat) (σ : State) (w : BitVec 64)
    (hinv : lstLanesInv bs prevb prevs env0 i σ w) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 32 - i + 1 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitWord env0 e (specRunStarts bs (prevb && prevs)) ∧
      runFuel (escapeListCalls Γ) (j + k) escapeListFunction σ =
        runFuel (escapeListCalls Γ) k escapeListFunction e := by
  obtain ⟨e, j, d, hj, _hd, hpc, hexit, _hfix, hrun⟩ :=
    (lstLanesLoopCalls Γ bs prevb prevs env0).run_from (32 - i) i σ w hinv rfl
  obtain hrun := hrun k
  refine ⟨e, j, hj, hpc, ?_, hrun⟩
  have hword : iter (stepWord bs) d (escapeSeed bs prevb prevs) =
      specRunStarts bs (prevb && prevs) := by
    rw [← stepN_eq_iter]
    exact stepN_fixed_eq_specRunStarts bs prevb prevs d (by rwa [stepN_eq_iter])
  have hexit' : lstLanesExitWord env0 e
      (iter (stepWord bs) d (escapeSeed bs prevb prevs)) := hexit
  rw [hword] at hexit'
  exact hexit'

theorem lanes_run_at_calls {Γ : MemContract} (bs : BitVec 64) (prevb prevs : Bool)
    (σ : State) (k : Nat)
    (hinv : lstLanesInv bs prevb prevs σ.env 2 σ (stepN bs 2 (escapeSeed bs prevb prevs)))
    {o : Outcome}
    (hcont : ∀ (e : State) (_j : Nat), e.pc = "xl_lanes.exit" →
      lstLanesExitWord σ.env e (specRunStarts bs (prevb && prevs)) →
      runFuel (escapeListCalls Γ) k escapeListFunction e = some o) :
    runFuel (escapeListCalls Γ) (31 + k) escapeListFunction σ = some o := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ :=
    lanes_run_calls bs prevb prevs σ.env 2 σ _ hinv k
  have hone : runFuel (escapeListCalls Γ) (j + k) escapeListFunction σ = some o := by
    rw [hrun]
    exact hcont e j hpc hexit
  exact runFuel_mono_le (by omega) hone

/-! ### `xl_lanes.exit`, `if.end.i4`, the two preheaders and the emitter's exit -/

theorem lstLanesExit_step_calls {Γ : MemContract} (env : Env) (s : State)
    (bs ctl im blk0 w : BitVec 64) (carry : Nat) (p : String) (op : Operand)
    (hpc : (withEnv env s).pc = "xl_lanes.exit")
    (hpre : (withEnv env s).pre = some p) (hinc : phiIncoming p lstExitIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8))) :
    step (escapeListCalls Γ) escapeListFunction (withEnv env s) =
      .jump (withEnv (lx9 env bs ctl im w blk0)
        { s with mem := lxMem2 s.mem bs w carry,
                 pc := lxNext ctl im w,
                 pre := some "xl_lanes.exit" }) ∧
      lookupName (lx9 env bs ctl im w blk0) "%and31.i" = some (.int 64 (lxWord ctl im w)) ∧
      lookupName (lx9 env bs ctl im w blk0) "%conv" = some (.int 32 (lxBase blk0)) ∧
      lookupName (lx9 env bs ctl im w blk0) "%xp" = lookupName env "%xp" ∧
      lookupName (lx9 env bs ctl im w blk0) "%xn" = lookupName env "%xn" ∧
      lookupName (lx9 env bs ctl im w blk0) "%carry" = lookupName env "%carry" ∧
      lookupName (lx9 env bs ctl im w blk0) "%arrayidx1" = lookupName env "%arrayidx1" := by
  obtain ⟨hstep, rest⟩ := lstLanesExit_step env s bs ctl im blk0 w carry p op hpc hpre hinc
    hop hbs hctl him hblk hcarry harr
  refine ⟨?_, rest⟩
  rw [step_escapeListCalls_at (Γ := Γ) (name := "xl_lanes.exit") (b := lstLanesExit) hpc
    findBlock_lanesExit (noBatchCall_of_all lstLanesExit_noBatch)]
  exact hstep

theorem lstIfEnd4_step_calls {Γ : MemContract} (env : Env) (s : State)
    (esc : BitVec 64) (base : BitVec 32) (xp xn c0 : Nat)
    (hpc : (withEnv env s).pc = "if.end.i4")
    (hes : lookupName env "%and31.i" = some (.int 64 esc))
    (hconv : lookupName env "%conv" = some (.int 32 base))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hc0 : c0 < 2 ^ 63)
    (hld : readBytes s.mem xn 8 = some (natToBytes c0 8)) :
    ∃ (e : State), step (escapeListCalls Γ) escapeListFunction (withEnv env s) = .jump e ∧
      e.pc = lstIfEnd4Next esc ∧
      e.mem = lstIfEnd4Mem base esc (xp + c0 * 4) xn (lstIfEnd4Count c0 esc) s.mem ∧
      lstWriterKeeps env e.env ∧
      lookupName e.env "%add.ptr.i.i" = some (.ptr (xp + c0 * 4)) ∧
      lookupName e.env "%add.i.i" = some (.int 64 (lstIfEnd4CellCount c0 esc)) ∧
      lookupName e.env "%cmp.i.i" = some (.int 1
        (evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8))) := by
  obtain ⟨e, hstep, rest⟩ := lstIfEnd4_step env s esc base xp xn c0 hpc hes hconv hxp hxn hc0 hld
  exact ⟨e, by
    rw [step_escapeListCalls_at (Γ := Γ) (name := "if.end.i4") (b := lstIfEnd4) hpc
      findBlock_ifEnd4 (noBatchCall_of_all lstIfEnd4_noBatch)]
    exact hstep, rest⟩

theorem lstForPre_step_calls {Γ : MemContract} (env : Env) (s : State) (esc : BitVec 64)
    (hpc : (withEnv env s).pc = "for.body.preheader.i.i")
    (hesc : lookupName env "%and31.i" = some (.int 64 esc)) :
    step (escapeListCalls Γ) escapeListFunction (withEnv env s) =
      .jump (fpSucc env s esc) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "for.body.preheader.i.i") (b := lstForPre) hpc
    findBlock_forPre (noBatchCall_of_all lstForPre_noBatch)]
  exact lstForPre_step env s esc hpc hesc

theorem lstWhilePre_step_calls {Γ : MemContract} (env : Env) (s : State) (o : Nat)
    (hpc : (withEnv env s).pc = "while.body.preheader.i.i")
    (ho : lookupName env "%add.ptr.i.i" = some (.ptr o)) :
    step (escapeListCalls Γ) escapeListFunction (withEnv env s) =
      .jump (wpSucc env s o) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "while.body.preheader.i.i") (b := lstWhilePre)
    hpc findBlock_whilePre (noBatchCall_of_all lstWhilePre_noBatch)]
  exact lstWhilePre_step env s o hpc ho

theorem lstEmitExit_step_calls {Γ : MemContract} (env : Env) (s : State)
    (hpc : (withEnv env s).pc = "xl_emit.exit") :
    step (escapeListCalls Γ) escapeListFunction (withEnv env s) = .ret none (withEnv env s) := by
  rw [step_escapeListCalls_at (Γ := Γ) (name := "xl_emit.exit") (b := lstEmitExit) hpc
    findBlock_emitExit (noBatchCall_of_all lstEmitExit_noBatch)]
  exact lstEmitExit_step env s hpc

/-! ### The seed chain at the call environment

`LRun` is stated at `escapeCalls`, so the chain is restated here at `escapeListCalls`
with the lifted steps.  The relation, its composition and its `runFuel` reading are
the same three lines as the intrinsic version, at the call environment. -/

inductive LRunC (calls : Calls) (f : Function) : Nat → State → State → Prop
  | zero (s : State) : LRunC calls f 0 s s
  | succ {n : Nat} {s s' t : State} :
      step calls f s = .jump s' → LRunC calls f n s' t → LRunC calls f (n + 1) s t

theorem LRunC.comp {calls : Calls} {f : Function} :
    ∀ {a : Nat} {s t u : State}, LRunC calls f a s t → LRunC calls f b t u →
      LRunC calls f (a + b) s u
  | 0, s, t, u, h1, h2 => by
      cases h1 with
      | zero => simpa using h2
  | a + 1, s, t, u, h1, h2 => by
      cases h1 with
      | succ hstep hrest =>
          rw [show a + 1 + b = (a + b) + 1 from by omega]
          exact LRunC.succ hstep (LRunC.comp hrest h2)

theorem LRunC.runFuel {calls : Calls} {f : Function} :
    ∀ {n : Nat} {s t : State}, LRunC calls f n s t →
      ∀ m, runFuel calls (n + m) f s = runFuel calls m f t
  | 0, s, t, h, m => by cases h with | zero => rw [Nat.zero_add]
  | n + 1, s, t, h, m => by
      cases h with
      | succ hstep hrest =>
          rw [show n + 1 + m = (n + m) + 1 from by omega, runFuel_jump_calls hstep,
            LRunC.runFuel hrest m]

theorem seed_then_run_calls {Γ : MemContract} (env : Env) (s : State) (pre : Option String)
    (bs : BitVec 64) (prevb prevs : Bool) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld0 : readBytes s.mem carry 8 =
      some (natToBytes (prevBackslashWord prevb).toNat 8))
    (hld1 : readBytes s.mem (carry + 8) 8 =
      some (natToBytes (prevBackslashWord prevs).toNat 8))
    (hne : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) ≠ (0 : BitVec 64)) :
    LRunC (escapeListCalls Γ) escapeListFunction 3 (site env s "entry" pre)
      (site (ie13 (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (prevBackslashWord prevs)
          (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
        bs (escapeSeed bs prevb prevs)) s
        (if em11 bs (escapeSeed bs prevb prevs) = (0 : BitVec 64)
          then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  have h1 : step (escapeListCalls Γ) escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.then.i"
        (some "entry")) := by
    rw [entry_step_calls env s pre bs (prevBackslashWord prevb) carry hbs hcarry hld0,
      ite_eq_right hne]
  have h2 : step (escapeListCalls Γ) escapeListFunction
      (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.then.i"
        (some "entry")) =
      .jump (site (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (prevBackslashWord prevs)
          (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) s "if.end.i"
        (some "if.then.i")) :=
    ifThen_step_calls (entryEnv env bs (prevBackslashWord prevb) carry) s (some "entry") bs
      (prevBackslashWord prevs)
      (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))) (carry + 8)
      (by env_simp; lk)
      (entry_cells env bs (prevBackslashWord prevb) carry).1
      (entry_cells env bs (prevBackslashWord prevb) carry).2.2.2.2 hld1
  refine LRunC.succ h1 (LRunC.succ h2 (LRunC.succ ?_ (LRunC.zero _)))
  rw [← seed_then_word bs prevb prevs hne]
  exact ifEnd_step_calls
    (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
      (prevBackslashWord prevs) (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
    s (some "if.then.i") bs
    (ifThenCond bs (prevBackslashWord prevs) |||
      (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
    "if.then.i" (.reg "%or5.i")
    (by env_simp; lk)
    (by env_simp; lk)
    rfl (by decide)
    (by
      show lookupName (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
        (prevBackslashWord prevs)
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) "%or5.i" = _
      env_simp; lk)

theorem seed_entry_run_calls {Γ : MemContract} (env : Env) (s : State) (pre : Option String)
    (bs : BitVec 64) (prevb prevs : Bool) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld0 : readBytes s.mem carry 8 =
      some (natToBytes (prevBackslashWord prevb).toNat 8))
    (hz : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) = (0 : BitVec 64)) :
    LRunC (escapeListCalls Γ) escapeListFunction 2 (site env s "entry" pre)
      (site (ie13 (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (escapeSeed bs prevb prevs)) s
        (if em11 bs (escapeSeed bs prevb prevs) = (0 : BitVec 64)
          then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  have h1 : step (escapeListCalls Γ) escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.end.i"
        (some "entry")) := by
    rw [entry_step_calls env s pre bs (prevBackslashWord prevb) carry hbs hcarry hld0,
      ite_eq_left hz]
  refine LRunC.succ h1 (LRunC.succ ?_ (LRunC.zero _))
  rw [← seed_entry_word bs prevb prevs hz]
  exact ifEnd_step_calls (entryEnv env bs (prevBackslashWord prevb) carry) s (some "entry") bs
    (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))
    "entry" (.reg "%and.i")
    (by env_simp; lk)
    (by env_simp; lk)
    rfl (by decide)
    (by
      show lookupName (entryEnv env bs (prevBackslashWord prevb) carry) "%and.i" = _
      env_simp; lk)

/-! ### The seed blocks' environment, and the cells the rest of the body reads

`entryEnv`, `ifThenEnv` and the `ie*` chain extend the caller's environment with
new names only, so every cell the exit block and the writer read is the caller's.
The two arms of the seed differ in the extension, so the cells are stated twice —
once per arm — and each is a walk over a cons chain. -/

theorem seedExit_entry_cells (env : Env) (bs w0 e0 : BitVec 64) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarr : lookupName env "%carry" = some (.ptr carry)) :
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%bs" = some (.int 64 bs) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%ctl" = some (.int 64 ctl) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%im" = some (.int 64 im) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%blk0" = some (.int 64 blk0) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%xp" = some (.ptr xp) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%xn" = some (.ptr xn) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%carry" = some (.ptr carry) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%and7.i" =
      some (.int 64 (stepMask bs)) ∧
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%or13.i" = some (.int 64 (em7 bs e0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ie_simp; env_simp; try lk; try rfl)

theorem seedExit_then_cells (env : Env) (bs w0 w1 e0 andI : BitVec 64) (a : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarr : lookupName env "%carry" = some (.ptr carry)) :
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%bs" =
      some (.int 64 bs) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%ctl" =
      some (.int 64 ctl) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%im" =
      some (.int 64 im) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%blk0" =
      some (.int 64 blk0) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%xp" =
      some (.ptr xp) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%xn" =
      some (.ptr xn) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%carry" =
      some (.ptr carry) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%and7.i" =
      some (.int 64 (stepMask bs)) ∧
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 a) bs w1 andI) bs e0) "%or13.i" =
      some (.int 64 (em7 bs e0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ie_simp; env_simp; try lk; try rfl)

/-! ### Spending fuel on one step

The two shapes a control step has, as `runFuel` prefixes at an arbitrary call
environment.  `runFuel_jump_calls` is the jump; the return needs the extra fact
that the run ends at the memory the returned state holds. -/

theorem run_one_jump {calls : Calls} {f : Function} {s s' : State}
    (h : step calls f s = .jump s') (k : Nat) :
    runFuel calls (1 + k) f s = runFuel calls k f s' := by
  rw [show 1 + k = k + 1 from by omega, runFuel_jump_calls h]

theorem run_one_ret {calls : Calls} {f : Function} {s s' : State} {v : Option Value}
    {n : Nat} (h : step calls f s = .ret v s') :
    runFuel calls (n + 1) f s = some (.ret v s'.mem) := by
  simp only [runFuel, h]

/-- `xl_emit.exit` at the call environment: the entry point's `void` return, at any
state that stands at that block. -/
theorem emit_exit_at {Γ : MemContract} (e : State) (hpc : e.pc = "xl_emit.exit") :
    runFuel (escapeListCalls Γ) 1 escapeListFunction e = some (.ret none e.mem) := by
  have h := lstEmitExit_step_calls (Γ := Γ) e.env e (by rw [withEnv_self]; exact hpc)
  rw [withEnv_self] at h
  exact run_one_ret (n := 0) h

/-- **`xl_lanes.exit`'s one step and its continuation.** -/
theorem emit_at {Γ : MemContract} (env : Env) (s : State)
    (bs ctl im blk0 w : BitVec 64) (carry : Nat) (p : String) (op : Operand)
    (hpc : (withEnv env s).pc = "xl_lanes.exit")
    (hpre : (withEnv env s).pre = some p) (hinc : phiIncoming p lstExitIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hcarr : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8)))
    (k : Nat) {o : Outcome}
    (hcont : runFuel (escapeListCalls Γ) k escapeListFunction
      (withEnv (lx9 env bs ctl im w blk0)
        { s with mem := lxMem2 s.mem bs w carry,
                 pc := lxNext ctl im w,
                 pre := some "xl_lanes.exit" }) = some o) :
    runFuel (escapeListCalls Γ) (1 + k) escapeListFunction (withEnv env s) = some o := by
  obtain ⟨hstep, _⟩ := lstLanesExit_step_calls env s bs ctl im blk0 w carry p op hpc hpre
    hinc hop hbs hctl him hblk hcarr harr
  exact (run_one_jump hstep k).trans hcont

/-- **`if.end.i4`'s one step and its continuation.**  The successor is handed to the
continuation with the facts the writer's entry reads. -/
theorem batch_at {Γ : MemContract} (env : Env) (s : State) (esc : BitVec 64)
    (base : BitVec 32) (xp xn c0 : Nat)
    (hpc : (withEnv env s).pc = "if.end.i4")
    (hes : lookupName env "%and31.i" = some (.int 64 esc))
    (hconv : lookupName env "%conv" = some (.int 32 base))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hc0 : c0 < 2 ^ 63)
    (hld : readBytes s.mem xn 8 = some (natToBytes c0 8))
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = lstIfEnd4Next esc →
      e.mem = lstIfEnd4Mem base esc (xp + c0 * 4) xn (lstIfEnd4Count c0 esc) s.mem →
      lstWriterKeeps env e.env →
      lookupName e.env "%add.ptr.i.i" = some (.ptr (xp + c0 * 4)) →
      lookupName e.env "%add.i.i" = some (.int 64 (lstIfEnd4CellCount c0 esc)) →
      runFuel (escapeListCalls Γ) k escapeListFunction e = some o) :
    runFuel (escapeListCalls Γ) (1 + k) escapeListFunction (withEnv env s) = some o := by
  obtain ⟨e, hstep, hpcE, hmemE, hkeeps, haddr, hcount, _hcmp⟩ :=
    lstIfEnd4_step_calls env s esc base xp xn c0 hpc hes hconv hxp hxn hc0 hld
  exact (run_one_jump hstep k).trans (hcont e hpcE hmemE hkeeps haddr hcount)

/-- **`for.body.preheader.i.i`'s one step and its continuation.** -/
theorem forPre_at {Γ : MemContract} (env : Env) (s : State) (esc : BitVec 64)
    (hpc : (withEnv env s).pc = "for.body.preheader.i.i")
    (hesc : lookupName env "%and31.i" = some (.int 64 esc))
    (k : Nat) {o : Outcome}
    (hcont : runFuel (escapeListCalls Γ) k escapeListFunction (fpSucc env s esc) = some o) :
    runFuel (escapeListCalls Γ) (1 + k) escapeListFunction (withEnv env s) = some o := by
  have hstep := lstForPre_step_calls (Γ := Γ) env s esc hpc hesc
  exact (run_one_jump hstep k).trans hcont

/-- **`while.body.preheader.i.i`'s one step and its continuation.** -/
theorem whilePre_at {Γ : MemContract} (env : Env) (s : State) (o : Nat)
    (hpc : (withEnv env s).pc = "while.body.preheader.i.i")
    (ho : lookupName env "%add.ptr.i.i" = some (.ptr o))
    (k : Nat) {o' : Outcome}
    (hcont : runFuel (escapeListCalls Γ) k escapeListFunction (wpSucc env s o) = some o') :
    runFuel (escapeListCalls Γ) (1 + k) escapeListFunction (withEnv env s) = some o' := by
  have hstep := lstWhilePre_step_calls (Γ := Γ) env s o hpc ho
  exact (run_one_jump hstep k).trans hcont

/-- **The writer loop and the emitter's exit.**  From the writer's head the run
reaches the entry point's return within nine control steps plus the exit block's
own, and leaves the count and the position stream `lstWriterExit` names. -/
theorem writer_at (blk0 : BitVec 64) (xp xn xn0 : Nat)
    (position : List Nat) (base : BitVec 32) (used o : Nat) (s : State) (w : BitVec 64)
    (hinv : lstWriterInv blk0 xp xn xn0 position base used o s w) :
    ∃ (e : State), runFuel (escapeListCalls Γ_xl_batch) 10 escapeListFunction s =
        some (.ret none e.mem) ∧ lstWriterExit blk0 xp xn xn0 position e := by
  have hct : ctpop w ≤ 8 * 8 := by
    obtain ⟨_hpc, ⟨_p, _oo, _oc, _hpre, _hoo, _hoc, _hvo, _hvc, _hocv⟩, hLLI, _hcur,
      _hkeep, _hconv, _hxn, hpair, hplt, _hbase, _hcap⟩ := hinv
    obtain ⟨hlanes, _hprefix, _hcount, _husedle, hplen⟩ := hLLI
    have hbridge := setLanes_eq_drop_of_inv hpair hplt hlanes
    rw [ctpop_eq_setLanes_length, hbridge]
    have := List.length_drop (i := used) (l := position)
    omega
  obtain ⟨e, j, hj, hexit, hrun⟩ := lstWriter_run blk0 xp xn xn0 position base 8 used o s w
    hinv hct
  have hret : runFuel (escapeListCalls Γ_xl_batch) 1 escapeListFunction e =
      some (.ret none e.mem) :=
    emit_exit_at e hexit.1
  have h1 : runFuel (escapeListCalls Γ_xl_batch) (j + 1) escapeListFunction s =
      some (.ret none e.mem) := by
    rw [hrun 1]
    exact hret
  exact ⟨e, runFuel_mono_le (by omega) h1, hexit⟩

/-! ### The inline batch's prefix readback

`if.end.i4` writes its eight entries with `or`, and the record reads the stream at
`xp + 4 * xn0`.  The prefix of `k` entries is the position stream's first `k`
entries: entry `i` is the base plus the `i`-th set lane, which is the batch's entry
formula on the lanes the batch claims.

The block's memory is `inlWrites` followed by the count's eight bytes, so the
prefix read is unaffected by the count store while the count's slot is outside the
batch's thirty-two bytes. -/

theorem lstIfEnd4Mem_read_entries (base : BitVec 32) (esc : BitVec 64) (o xn count : Nat)
    (mem : Mem) (k : Nat) (hk8 : k ≤ 8) (hdisj : xn + 8 ≤ o ∨ o + 32 ≤ xn) :
    readBytes (lstIfEnd4Mem base esc o xn count mem) o (4 * k) =
      readBytes (inlWrites base esc o 8 mem) o (4 * k) := by
  unfold lstIfEnd4Mem
  rcases hdisj with h | h
  · rw [readBytes_writeBytes_above _ (natToBytes count 8) (4 * k) o xn
      (by rw [natToBytes_length]; omega)]
  · rw [readBytes_writeBytes_below _ (natToBytes count 8) (4 * k) o xn (by omega)]

theorem inlWrites_readBytes_prefix (blk0 : BitVec 64) (esc : BitVec 64) (o : Nat)
    (hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32) (mem : Mem) :
    ∀ k, k ≤ min (ctpop esc) 8 →
      readBytes (inlWrites (lxBase blk0) esc o 8 mem) o (4 * k) =
        some (batchEntries (lxBase blk0) esc k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [show 4 * (k + 1) = 4 * k + 4 from by omega]
      rw [LeanLLVM.Vellum.JsonEntrySteps.readBytes_append
        (inlWrites (lxBase blk0) esc o 8 mem) (4 * k) o
        (batchEntries (lxBase blk0) esc k) 4 (inlBytes (lxBase blk0) esc k)
        (ih (by omega))
        (inlWrites_readBytes_entry (lxBase blk0) esc o 8 k
          (by have := Nat.lt_of_succ_le hk; omega) mem)]
      rw [inlBytes_eq_batchBytes blk0 esc (Nat.lt_of_succ_le hk) hcap]
      rfl

/-- **The inline batch's claimed stream.**  At a base that is a multiple of
sixty-four within the address space, the first `k` entries read back as the first
`k` positions of the block's set-lane list, lifted by the base. -/
theorem lstIfEnd4Mem_positions (blk0 : BitVec 64) (esc : BitVec 64) (o xn count : Nat)
    (mem : Mem) (k : Nat) (hk : k ≤ min (ctpop esc) 8)
    (hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32)
    (hdisj : xn + 8 ≤ o ∨ o + 32 ≤ xn) :
    readBytes (lstIfEnd4Mem (lxBase blk0) esc o xn count mem) o (4 * k) =
      some (positionsBytes 4 ((setLanes esc).take k |>.map
        fun lane => (lxBase blk0).toNat + lane)) := by
  rw [lstIfEnd4Mem_read_entries (lxBase blk0) esc o xn count mem k (by omega) hdisj]
  rw [inlWrites_readBytes_prefix blk0 esc o hcap mem k hk]
  exact congrArg some (batchEntries_positions (lxBase blk0) esc k hk hcap)

/-- A set lane reads out of its own membership. -/
theorem getLsbD_eq_decide_mem_setLanes {w : Nat} {m : BitVec w} {k : Nat} (hk : k < w) :
    m.getLsbD k = decide (k ∈ setLanes m) := by
  by_cases h : m.getLsbD k = true
  · rw [decide_eq_true (mem_setLanes.mpr ⟨hk, h⟩)]
    exact h
  · have hf : m.getLsbD k = false := by
      cases hm : m.getLsbD k
      · rfl
      · exact absurd hm h
    rw [hf, decide_eq_false (fun hm => by
      have h2 := (mem_setLanes.mp hm).2
      exact absurd h2 (by rw [hf]; simp))]

/-! ### The writer's entry state

The preheaders and the first batch lift the state into the writer's invariant.  The
state that arrives at `while.body.i.i` is the batch's memory, the loop's eight
cleared lanes, and the cursor the inlined batch left, thirty-two bytes on. -/

/-- The cells the writer's invariant reads past the two preheaders: they are the
caller's, because neither preheader binds either name. -/
theorem writerEntry_conv (env : Env) (esc : BitVec 64) (o : Nat) (base : BitVec 32)
    (h : lookupName env "%conv" = some (.int 32 base)) :
    lookupName (wpEnv (fp17 env esc) o) "%conv" = some (.int 32 base) := by
  simp only [wpEnv, fp17, fp16, fp15, fp14, fp13, fp12, fp11, fp10, fp9, fp8, fp7, fp6,
    fp5, fp4, fp3, fp2, fp1, List.cons_append]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem writerEntry_xn (env : Env) (esc : BitVec 64) (o xn : Nat)
    (h : lookupName env "%xn" = some (.ptr xn)) :
    lookupName (wpEnv (fp17 env esc) o) "%xn" = some (.ptr xn) := by
  simp only [wpEnv, fp17, fp16, fp15, fp14, fp13, fp12, fp11, fp10, fp9, fp8, fp7, fp6,
    fp5, fp4, fp3, fp2, fp1, List.cons_append]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem writerEntry_and7 (env : Env) (esc : BitVec 64) (o : Nat) :
    lookupName (wpEnv (fp17 env esc) o) "%and.7.i.i" = some (.int 64 (clearLow esc 8)) := by
  simp only [wpEnv, fp17, fp16, fp15, fp14, fp13, fp12, fp11, fp10, fp9, fp8, fp7, fp6,
    fp5, fp4, fp3, fp2, fp1, List.cons_append]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]
  show some (Value.int 64 (cSt8 esc)) = some (Value.int 64 (clearLow esc 8))
  rw [cSt8_eq_clearLow]

theorem writerEntry_ptr (env : Env) (esc : BitVec 64) (o : Nat) :
    lookupName (wpEnv (fp17 env esc) o) "%add.ptr5.i.i" = some (.ptr (o + 32)) := by
  simp only [wpEnv]
  exact lookupName_cons_self _ _ _

/-! ### The writer's invariant at its entry

The batch's memory and the two preheaders' cells are the invariant at `used = 8`:
the residual word is the position word's lanes past the inlined batch, the store is
the inlined batch's claimed stream, and the count is the caller's plus eight. -/

/-- The count's cell of the inline batch's memory: the store is the last write, so
the cell reads back as the count. -/
theorem lstIfEnd4Mem_count (blk0 : BitVec 64) (esc : BitVec 64) (o xn count : Nat)
    (mem0 : Mem) :
    readBytes (lstIfEnd4Mem (lxBase blk0) esc o xn count mem0) xn 8 =
      some (wordBytes 8 count) := by
  unfold lstIfEnd4Mem
  have h := readBytes_writeBytes_same (inlWrites (lxBase blk0) esc o 8 mem0)
    (natToBytes count 8) (addr := xn)
  rw [natToBytes_length] at h
  rw [h]
  rfl

/-! ### Axiom footprints

Three carry `Classical.choice`, and its carrier is `Nat.mod_mul_right_div_self`
— the division lemma `natToBytes_mod_pow` uses, the carrier the writer's own
lemmas already name.  Each of the three consumes the inline batch's or the
writer's step lemma, so it inherits exactly that footprint and nothing else. -/

/-- info: 'LeanLLVM.Vellum.escapeListCalls_of_ne_xlBatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeListCalls_of_ne_xlBatch

/-- info: 'LeanLLVM.Vellum.evalInstr_escapeListCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalInstr_escapeListCalls

/-- info: 'LeanLLVM.Vellum.denoteCode_escapeListCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denoteCode_escapeListCalls

/-- info: 'LeanLLVM.Vellum.step_escapeListCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_escapeListCalls

/-- info: 'LeanLLVM.Vellum.step_escapeListCalls_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_escapeListCalls_at

/-- info: 'LeanLLVM.Vellum.lstEntry_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstEntry_noBatch

/-- info: 'LeanLLVM.Vellum.lstIfThen_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstIfThen_noBatch

/-- info: 'LeanLLVM.Vellum.lstIfEnd_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstIfEnd_noBatch

/-- info: 'LeanLLVM.Vellum.lanesBody_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lanesBody_noBatch

/-- info: 'LeanLLVM.Vellum.lstLanesExit_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstLanesExit_noBatch

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstIfEnd4_noBatch

/-- info: 'LeanLLVM.Vellum.lstForPre_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstForPre_noBatch

/-- info: 'LeanLLVM.Vellum.lstWhilePre_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstWhilePre_noBatch

/-- info: 'LeanLLVM.Vellum.lstEmitExit_noBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lstEmitExit_noBatch

/-- info: 'LeanLLVM.Vellum.entry_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_step_calls

/-- info: 'LeanLLVM.Vellum.ifThen_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifThen_step_calls

/-- info: 'LeanLLVM.Vellum.ifEnd_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_step_calls

/-- info: 'LeanLLVM.Vellum.lstDoBody_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstDoBody_step_calls

/-- info: 'LeanLLVM.Vellum.lstLanesLoopCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesLoopCalls

/-- info: 'LeanLLVM.Vellum.lanes_run_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_run_calls

/-- info: 'LeanLLVM.Vellum.lanes_run_at_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_run_at_calls

/-- info: 'LeanLLVM.Vellum.lstLanesExit_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesExit_step_calls

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_step_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_step_calls

/-- info: 'LeanLLVM.Vellum.lstForPre_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstForPre_step_calls

/-- info: 'LeanLLVM.Vellum.lstWhilePre_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstWhilePre_step_calls

/-- info: 'LeanLLVM.Vellum.lstEmitExit_step_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstEmitExit_step_calls

/-- info: 'LeanLLVM.Vellum.LRunC.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LRunC.comp

/-- info: 'LeanLLVM.Vellum.LRunC.runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LRunC.runFuel

/-- info: 'LeanLLVM.Vellum.seed_then_run_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_then_run_calls

/-- info: 'LeanLLVM.Vellum.seed_entry_run_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_entry_run_calls

/-- info: 'LeanLLVM.Vellum.run_one_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_one_jump

/-- info: 'LeanLLVM.Vellum.run_one_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_one_ret

/-- info: 'LeanLLVM.Vellum.emit_exit_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit_exit_at

/-- info: 'LeanLLVM.Vellum.emit_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit_at

/-- info: 'LeanLLVM.Vellum.batch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_at

/-- info: 'LeanLLVM.Vellum.forPre_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forPre_at

/-- info: 'LeanLLVM.Vellum.whilePre_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whilePre_at

/-- info: 'LeanLLVM.Vellum.writer_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms writer_at

/-- info: 'LeanLLVM.Vellum.lstIfEnd4Mem_read_entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4Mem_read_entries

/-- info: 'LeanLLVM.Vellum.inlWrites_readBytes_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inlWrites_readBytes_prefix

/-- info: 'LeanLLVM.Vellum.lstIfEnd4Mem_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4Mem_positions

/-- info: 'LeanLLVM.Vellum.getLsbD_eq_decide_mem_setLanes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms getLsbD_eq_decide_mem_setLanes

/-- info: 'LeanLLVM.Vellum.writerEntry_conv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerEntry_conv

/-- info: 'LeanLLVM.Vellum.writerEntry_xn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerEntry_xn

/-- info: 'LeanLLVM.Vellum.writerEntry_and7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerEntry_and7

/-- info: 'LeanLLVM.Vellum.writerEntry_ptr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerEntry_ptr

/-- info: 'LeanLLVM.Vellum.lstIfEnd4Mem_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4Mem_count

