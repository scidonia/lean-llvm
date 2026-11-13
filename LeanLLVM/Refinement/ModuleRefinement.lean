/-
Contextual replacement across two call environments.

`Frames.RefinesWithin` compares a target and a source under a single `Calls`, so
it cannot say what a module replacement says: the same caller text observed
under two different selections of an external body.  This module states that
relation — `RefinesWithinAcross` — and proves it composed from the directional
environment relation `CallRefines`: replacing the external call environment
preserves the caller's behaviour at the framed relation.

`Calls` now carries a memory channel — an entry returns the value, the memory
and the allocator state the callee leaves behind — so a call's result includes
the memory the caller adopts, and a callee that writes is inside the model.
`CallRefines` demands *complete* agreement of the two outcomes, memory and
allocator included, so for that hypothesis the two runs agree on memory exactly
as they agree on value, and this module's statements hold at every frame.  The
conclusion is a directed inclusion, not an equality of behaviours:
`Beh_calls_refines` matches each target outcome with the same source outcome,
and the source may also exhibit outcomes (such as `ub`) that the target does
not.  The frame is carried because the memory-effectful form of the relation —
one that permits the callee's memory to differ inside the footprint — needs it;
the load-bearing hypothesis here is the environment relation, and the negative
controls in `LeanLLVMTest/Refinement.lean` show that it can fail and that the
conclusion fails with it.

That memory-effectful form is `CallRefinesWithin`, and the two sections after
the exact-level theorems state it for the loop's selections: the caller's
`caller_replaces_loop_within` at the loop's own band, and `memCaller`'s at the
band the shared allocator seeds the body at, when the caller allocates before
calling.  Both consult `loop_seam_within_refines`, the relation at every
allocator base, whose base-`1` memory clause is the loop's certified
`loop_refines_candidate_within`.
-/
import LeanLLVM.Semantics
import LeanLLVM.Frames
import LeanLLVM.CallRefinement
import LeanLLVM.Refinement.SeamContext
import LeanLLVM.Refinement.CommaMaskLoop

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.SeamContext   -- envFor, seamSymbol, callerFunction, caller_beh
open LeanLLVM.Refinement.CommaMaskLoop -- loopFunction, candidateFunction, loop_returns_spec
open LeanLLVM.Refinement.CommaMaskIR   -- candidate_beh_int

/-! ### The two-environment relation -/

/-- Framed refinement across *two* call environments: `target` under `calls'`
is matched by `source` under `calls`, outside `frame`.  This is the relation
`RefinesWithin` would be if it took two environments; it is what a module
replacement actually compares. -/
def RefinesWithinAcross (calls' calls : Calls) (target source : Function)
    (frame : Nat → Prop) : Prop :=
  BehsWithin (Beh calls' target) (Beh calls source) frame

/-- `replaceFunction_sound`.  Replacing the seam — a change of call
environment, not of the caller's text — preserves the caller's behaviour, at
the framed relation, under the directional environment refinement `h`.  `h` is
the load-bearing hypothesis: the conclusion relates `calls'` to `calls`, and
fails when `h` fails (the adversarial example in `LeanLLVMTest/Refinement.lean`).
`CallRefines` demands complete agreement of the returned outcome, memory and
allocator included, so the matched outcomes carry the same memory and the frame
in the conclusion is inert for this hypothesis. -/
theorem replaceFunction_sound
    {calls' calls : Calls} {C : Function} {frame : Nat → Prop}
    (h : ∀ sym, CallRefines calls' calls sym) :
    RefinesWithinAcross calls' calls C C frame :=
  fun args o ho => ⟨o, Beh_calls_refines h C args o ho, Outcome.agreesOutside_refl o frame⟩

/-! ### A caller with its own footprint -/

/-- A caller with its own scratch local: allocate one `i64`, call the seam,
store the result, load it back, return it.  The `alloca` and the `store` are the
caller's own memory effects, so the caller has a footprint of its own to name.
The two selections it is compared under return the caller's memory unchanged, so
the callee's memory here is the caller's own; a callee that writes inside this
footprint is what the memory-effectful form of the relation exists to permit. -/
def memCaller : Function :=
  { name := "leanllvm_mem_caller", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .alloca "%buf" (.int 64) 8,
          .call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")],
          .store (.int 64) (.reg "%r") (.reg "%buf"),
          .load "%out" (.int 64) (.reg "%buf") ],
        term := .ret (.int 64) (some (.reg "%out")) } ] }

/-- The caller's footprint: the one `i64` local its `alloca` hands out, from the
reserved address `1`.  Read off the allocator it is
`AllocFrame (initState memCaller args) s₁ = Band 1 9`: `initState` starts the
allocator at address `1`, and the `alloca` of an `i64` advances it by eight
bytes, so the state after the entry block's instructions allocates exactly
`[1, 9)`.  As `loopFrame_eq` does for the loop, the band is written as the
computed value rather than kept as an `AllocFrame` expression. -/
def callerFrame : Nat → Prop := Band 1 9

/-! ### The two seam selections -/

-- Value-level justification of the environments (the frame is inert here; see
-- the module header):
--   loop_returns_spec  (`CommaMaskLoop`): the loop body returns `spec x`.
--   candidate_beh_int  (`CommaMaskIR`): the candidate returns `byteLoop x`.
--   byteLoop_eq_spec   (`CommaMaskKernel`): `byteLoop x = spec x`.
/-- The two seam selections are pointwise-related environments: the loop's
selection (`spec`) and the candidate's (`byteLoop`) agree because their values
agree, and both leave the caller's memory and allocator untouched. -/
theorem loop_seam_callRefines :
    ∀ sym, CallRefines (envFor spec) (envFor byteLoop) sym := by
  intro sym args mem next
  right
  by_cases h : sym = seamSymbol
  · subst h
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | cons b rest => simp [envFor]
      | nil =>
        cases a with
        | int w x =>
          by_cases hw : w = 64
          · subst hw
            simp [envFor, (byteLoop_eq_spec x).symm]
          · simp [envFor, hw]
        | ptr a => simp [envFor]
        | vec n' w' lanes => simp [envFor]
        | float b => simp [envFor]
  · simp [envFor, h]

/-- The contextual replacement: the caller under the memory-backed loop's
selection refines the caller under the unrolled candidate's selection, at the
caller's own footprint.  Because `envFor spec = envFor byteLoop` follows from
`byteLoop_eq_spec`, this instance's `h` is a value equality and its conclusion
follows by reflexivity (through `replaceFunction_sound`); the load-bearing
witness for the general theorem is the negative control
`caller_not_refined_by_undefined_env` in `LeanLLVMTest/Refinement.lean`, not this
instance.  The instance is stated because it records the value-level content of
the two selections (`loop_returns_spec`, `candidate_beh_int`) and gives the
milestone a caller with a footprint of its own. -/
theorem memCaller_replaces_loop :
    RefinesWithinAcross (envFor spec) (envFor byteLoop) memCaller memCaller callerFrame :=
  replaceFunction_sound loop_seam_callRefines

/-! ### The memory-aware environment relation

`CallRefinesWithin` relates two selections outside a band that starts at the
caller's allocator base.  The loop's two locals sit at `base` and `base + 8` and
its allocator advances to `base + 16`, so the loop's selection and the
candidate's are related at `ReserveFrame 16`; the candidate leaves the incoming
memory and allocator untouched.  The callers below consult that relation at the
base their own allocation leaves behind: `callerFunction` at `1`, `memCaller` at
`9` because its `alloca` runs before the call.

Each caller theorem is proved directly, from the caller's behaviour and the
relation at the base the call is reached at, rather than through a schema whose
premise would demand one frame from every base: a callee's band is
base-dependent, so no frame tight for the loop is available from every base. -/

/-- The candidate leaves any incoming memory and allocator state exactly as it
found them: it allocates nothing and executes no store, so `runFuel` returns the
incoming memory.  Both are parameters, because `envForBody` seeds the body at the
caller's `next` and `loop_seam_within_refines` must hold at base `9` as well as
base `1`; `initState` would fix `next := 1`.  `candidate_beh_int` states this
only from `initState`, where the memory is `[]` and the base is `1`. -/
theorem candidate_run_mem_eq (x : BitVec 64) (mem : Mem) (next : Nat) :
    ∃ mem', runFuel noCalls 10000 candidateFunction
        { (initState candidateFunction [.int 64 x]) with mem := mem, next := next } =
      some (.ret (some (.int 64 (byteLoop x))) mem') ∧ mem' = mem := by
  let s : State := { (initState candidateFunction [.int 64 x]) with mem := mem, next := next }
  have h0 : lookupName s.env "%arg" = some (.int 64 x) :=
    lookupName_initState_candidate x
  have hstep : step noCalls candidateFunction s =
      .ret (some (.int 64 (byteLoop x))) (candidateRun s x) :=
    candidate_step_body noCalls s x h0 rfl
  show ∃ mem', runFuel noCalls 10000 candidateFunction s =
    some (.ret (some (.int 64 (byteLoop x))) mem') ∧ mem' = mem
  refine ⟨mem, ?_, rfl⟩
  simp only [runFuel, hstep, candidateRun_mem]
  rfl

/-- The candidate's selection refuses an argument list whose first value is not
an `i64`: its first instruction reads `%arg` at width 64, so the run reaches `ub`
before touching the incoming memory or the allocator, and the selection is
undefined. -/
theorem candidate_envForBody_none_of_head (a : Value) (rest : List Value) (mem : Mem)
    (next : Nat) (hne : ∀ y, a ≠ .int 64 y) :
    envForBody 10000 16 candidateFunction seamSymbol (a :: rest) mem next = none := by
  obtain ⟨w, v⟩ | ⟨p⟩ | ⟨n', w', lanes⟩ | ⟨bits⟩ := a
  · have hw : w ≠ 64 := by
      intro hw
      subst hw
      exact hne v rfl
    simp [envForBody, runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
      candidateInstrs, evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c,
      argName, hw]
  · simp [envForBody, runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
      candidateInstrs, evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c,
      argName]
  · simp [envForBody, runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
      candidateInstrs, evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c,
      argName]

  · simp [envForBody, runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
      candidateInstrs, evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c,
      argName]

/-- The candidate's selection refuses the empty argument list in the same way:
its parameter is unbound, so the first instruction is undefined. -/
theorem candidate_envForBody_none_nil (mem : Mem) (next : Nat) :
    envForBody 10000 16 candidateFunction seamSymbol [] mem next = none := by
  simp [envForBody, runFuel, step, candidateFunction, candidateBody, Function.findBlock,
    findBlockList, Function.entry?, List.zip, denoteCode, denoteRun, State.bindAll, candidateInstrs, evalInstr,
    evalOperand, Const.toValue, lit, c, argName]

/-- The environment relation the module theorem consumes: the loop and the
candidate are related at every allocator base, outside the band the loop's two
locals occupy at that base.  At base `1` with the candidate's memory the memory
clause is **`loop_refines_candidate_within`'s conclusion** with
`loopFrame x = Band 1 17` (`loopFrame_eq`); at any other base it is
`loop_run_at_base`'s agreement against `candidate_run_mem_eq`'s unchanged memory.
The value clause is `loop_returns_spec` / `candidate_beh_int` /
`byteLoop_eq_spec` in both cases, and `r'.next = r.next` holds because both
selections declare `reserve := 16`, while `next ≤ r.next` follows from
`next + 16 ≥ next`. -/
theorem loop_seam_within_refines (x : BitVec 64) :
    CallRefinesWithin (envForBody 10000 16 loopFunction)
      (envForBody 10000 16 candidateFunction) seamSymbol (ReserveFrame 16) := by
  intro args mem next
  match args with
  | [] => exact Or.inl (candidate_envForBody_none_nil mem next)
  | a :: rest =>
    match a with
    | .int w v =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨memL, hagreeL, hrunL⟩ := loop_run_at_base v next mem
        obtain ⟨memC, hrunC, hmemC⟩ := candidate_run_mem_eq v mem next
        have hLrun : runFuel noCalls 10000 loopFunction
            { env := (loopFunction.params.zip (.int 64 v :: rest)).map fun p => (p.1.1, p.2)
              mem := mem, next := next, pc := loopFunction.entry?.getD "", pre := none } =
            some (.ret (some (.int 64 (spec v))) memL) := by
          simpa [initState, loopFunction] using
            runFuel_mono_le (by decide : 19 ≤ 10000) hrunL
        have hCrun : runFuel noCalls 10000 candidateFunction
            { env := (candidateFunction.params.zip (.int 64 v :: rest)).map
                fun p => (p.1.1, p.2)
              mem := mem, next := next, pc := candidateFunction.entry?.getD "",
              pre := none } =
            some (.ret (some (.int 64 (byteLoop v))) memC) := by
          simpa [initState, candidateFunction] using hrunC
        refine Or.inr
          ⟨{ ret := .int 64 (spec v), mem := memL, next := next + 16 },
           { ret := .int 64 (byteLoop v), mem := memC, next := next + 16 },
           ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [envForBody, hLrun]
        · simp [envForBody, hCrun]
        · rw [byteLoop_eq_spec]
        · show next ≤ next + 16
          omega
        · rfl
        · by_cases hb : next = 1 ∧ mem = []
          · obtain ⟨hnext, hmem⟩ := hb
            subst hnext
            subst hmem
            subst hmemC
            have ho : Beh noCalls loopFunction [.int 64 v]
                (.ret (some (.int 64 (spec v))) memL) :=
              Or.inr ⟨19, hrunL⟩
            obtain ⟨o', ho', hagree⟩ := loop_refines_candidate_within v _ ho
            have ho'eq : o' = .ret (some (.int 64 (byteLoop v))) [] :=
              (candidate_beh_int noCalls v [] o').1 ho'
            subst ho'eq
            exact hagree.2
          · rw [hmemC]
            exact hagreeL
      · exact Or.inl (candidate_envForBody_none_of_head _ rest mem next (by
          intro y hy
          injection hy with hw' _
          exact hw hw'))
    | .ptr p =>
      exact Or.inl (candidate_envForBody_none_of_head (.ptr p) rest mem next (by
        intro y hy
        cases hy))
    | .vec n' w' lanes =>
      exact Or.inl (candidate_envForBody_none_of_head (.vec n' w' lanes) rest mem next (by
        intro y hy
        cases hy))

    | .float bits =>
      exact Or.inl (candidate_envForBody_none_of_head (.float bits) rest mem next (by
        intro y hy
        cases hy))

/-- The emitted caller (`probes/install/ir/caller.ll`, `SeamContext.callerFunction`)
observes the loop's selection at the loop's own footprint.  Its call is its first
instruction, so it is reached at allocator base `1` with empty memory
(`initState`, `Semantics.lean:312-315`; `caller_beh_body`), and the band the
loop's reservations cover from base `1` is `Band 1 17 = loopFrame x`
(`CommaMaskLoop.lean:607`).  The returned memory is the callee's memory — the
channel the base model did not have.

Proved directly rather than through a schema whose premise requires one frame
from every base: `Band 1 17` is the loop's band only at base `1`.  The proof
consults `caller_beh_body`, collapses each side to its single behaviour, and then
consults `CallRefinesWithin` at base `1`, which is `loop_seam_within_refines`
instantiated where `loop_refines_candidate_within` supplies the memory clause.
No `load` is executed by `callerFunction` (`SeamContext.lean:55-57`), so there is
no caller-side read obligation to discharge. -/
theorem caller_replaces_loop_within (x : BitVec 64) :
    RefinesWithinAcross (envForBody 10000 16 loopFunction)
      (envForBody 10000 16 candidateFunction)
      callerFunction callerFunction (loopFrame x) := by
  intro args o ho
  match args with
  | [] =>
    exact ⟨o, caller_beh_nil 10000 16 candidateFunction o, Outcome.agreesOutside_refl o _⟩
  | a :: rest =>
    match a with
    | .int w v =>
      by_cases hw : w = 64
      · subst hw
        have ho1 : Beh (envForBody 10000 16 loopFunction) callerFunction
            [.int 64 v] o := by
          have h : Beh (envForBody 10000 16 loopFunction) callerFunction
              (.int 64 v :: rest) o := ho
          simp only [Beh, initState_cons_caller] at h ⊢
          exact h
        -- the candidate resolves the call at base `1`, so the relation's `none`
        -- branch is excluded and the two outcomes and their agreement are its
        -- witnesses
        obtain ⟨memC, hrunC, _⟩ := candidate_run_mem_eq v [] 1
        have hCrun : runFuel noCalls 10000 candidateFunction
            { env := (candidateFunction.params.zip [.int 64 v]).map fun p => (p.1.1, p.2)
              mem := [], next := 1, pc := candidateFunction.entry?.getD "", pre := none } =
            some (.ret (some (.int 64 (byteLoop v))) memC) := by
          simpa [initState] using hrunC
        have hC : envForBody 10000 16 candidateFunction seamSymbol [.int 64 v] [] 1 =
            some { ret := .int 64 (byteLoop v), mem := memC, next := 17 } := by
          simp [envForBody, hCrun]
        rcases loop_seam_within_refines x [.int 64 v] [] 1 with
          hnone | ⟨r', r, hL, hC', hret, _hle, _hnext, hmem⟩
        · rw [hC] at hnone
          cases hnone
        · have ho' : o = .ret (some r'.ret) r'.mem :=
            (caller_beh_body 10000 16 loopFunction v hL o).1 ho1
          refine ⟨.ret (some r.ret) r.mem,
            (caller_beh_body 10000 16 candidateFunction v hC' _).2 rfl, ?_⟩
          rw [ho']
          exact ⟨by rw [hret], hmem⟩
      · exact ⟨o, caller_beh_of_unresolved 10000 16 candidateFunction (.int w v) rest o
          (candidate_envForBody_none_of_head (.int w v) rest [] 1 (by
            intro y hy
            injection hy with hw' _
            exact hw hw')), Outcome.agreesOutside_refl o _⟩
    | .ptr p =>
      exact ⟨o, caller_beh_of_unresolved 10000 16 candidateFunction (.ptr p) rest o
        (candidate_envForBody_none_of_head (.ptr p) rest [] 1 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩
    | .vec n' w' lanes =>
      exact ⟨o, caller_beh_of_unresolved 10000 16 candidateFunction (.vec n' w' lanes) rest o
        (candidate_envForBody_none_of_head (.vec n' w' lanes) rest [] 1 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩

    | .float bits =>
      exact ⟨o, caller_beh_of_unresolved 10000 16 candidateFunction (.float bits) rest o
        (candidate_envForBody_none_of_head (.float bits) rest [] 1 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩

/-! ### A caller with its own local -/

/-- A longer argument list binds the same parameter: `memCaller` has one
parameter, so `zip` truncates at it and every run is about `initState memCaller
[a]`. -/
theorem initState_cons_memCaller (a : Value) (rest : List Value) :
    initState memCaller (a :: rest) = initState memCaller [a] := rfl

/-- `memCaller`'s entry block under a selection that resolves its call at
allocator base `9`: the `alloca` hands `%buf` the address `1` and advances the
allocator to `9`, the call returns `r`, the store writes `r`'s value — which the
hypothesis pins to `v` — at `%buf`, and the load reads it back, so the block
returns `v` and its memory is the callee's plus those eight bytes at address
`1`. -/
theorem memCaller_step (calls : Calls) (x : BitVec 64) {r : CallOutcome} (v : BitVec 64)
    (h : calls seamSymbol [.int 64 x] [] 9 = some r) (hr : r.ret = .int 64 v) :
    step calls memCaller (initState memCaller [.int 64 x]) =
      .ret (some (.int 64 v))
        { env := [("%out", .int 64 v), ("%r", r.ret), ("%buf", .ptr 1),
                  ("%arg", .int 64 x)]
          mem := writeBytes r.mem 1 (natToBytes v.toNat 8), next := r.next, pc := "entry",
          pre := none } := by
  have hload : loadValue (writeBytes r.mem 1 (natToBytes v.toNat 8)) (.int 64) 1 =
      some (.int 64 v) :=
    (loadValue_storeValue_64 ⟨[], r.mem, r.next, "entry", none⟩ v 1).2
  simp [step, memCaller, Function.findBlock, findBlockList, Function.entry?, List.head?,
    Option.getD, Option.map, initState, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
    evalInstr, evalOperands, evalOperand, execTerm, Ty.sizeBytes, State.bind, lookupName,
    storeValue, h, hr, hload]

/-- `memCaller`'s run under a selection that resolves its call at base `9`
returns `v` after one step, with the callee's memory and the eight bytes the
caller stored at address `1`. -/
theorem memCaller_runFuel (calls : Calls) (x : BitVec 64) {r : CallOutcome} (v : BitVec 64)
    (h : calls seamSymbol [.int 64 x] [] 9 = some r) (hr : r.ret = .int 64 v) :
    ∀ n, runFuel calls (n + 1) memCaller (initState memCaller [.int 64 x]) =
      some (.ret (some (.int 64 v)) (writeBytes r.mem 1 (natToBytes v.toNat 8))) := by
  intro n
  simp only [runFuel, memCaller_step calls x v h hr]

theorem memCaller_runFuel_none_or (calls : Calls) (x : BitVec 64) {r : CallOutcome}
    (v : BitVec 64) (h : calls seamSymbol [.int 64 x] [] 9 = some r)
    (hr : r.ret = .int 64 v) :
    ∀ n, runFuel calls n memCaller (initState memCaller [.int 64 x]) = none ∨
      runFuel calls n memCaller (initState memCaller [.int 64 x]) =
        some (.ret (some (.int 64 v)) (writeBytes r.mem 1 (natToBytes v.toNat 8))) := by
  intro n
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (memCaller_runFuel calls x v h hr k)

/-- A caller with its own local has exactly one behaviour under a selection that
resolves its call at base `9`: the value it stored, with the callee's memory and
its own eight bytes at address `1`.  The single behaviour is what the framed
relation compares, and its memory is what the frame then hides the callee's band
inside. -/
theorem memCaller_beh (calls : Calls) (x : BitVec 64) {r : CallOutcome} (v : BitVec 64)
    (h : calls seamSymbol [.int 64 x] [] 9 = some r) (hr : r.ret = .int 64 v)
    (o : Outcome) :
    Beh calls memCaller [.int 64 x] o ↔
      o = .ret (some (.int 64 v)) (writeBytes r.mem 1 (natToBytes v.toNat 8)) := by
  constructor
  · intro hb
    rcases hb with ⟨n, hn⟩ | ⟨n, hn⟩
    · rcases memCaller_runFuel_none_or calls x v h hr n with h' | h' <;>
        rw [h'] at hn <;> simp at hn
    · rcases memCaller_runFuel_none_or calls x v h hr n with h' | h' <;>
        rw [h'] at hn
      · simp at hn
      · exact (Option.some.inj hn).symm
  · intro ho
    subst ho
    exact Or.inr ⟨1, memCaller_runFuel calls x v h hr 0⟩

/-- The caller with its own local reaches `ub` at its call when the selection
leaves that call undefined, so every outcome is one of its behaviours. -/
theorem memCaller_beh_of_unresolved (calls : Calls) (a : Value) (rest : List Value)
    (o : Outcome) (h : calls seamSymbol [a] [] 9 = none) :
    Beh calls memCaller (a :: rest) o := by
  refine Or.inl ⟨1, ?_⟩
  have hstep : step calls memCaller (initState memCaller (a :: rest)) = .ub := by
    simp only [initState_cons_memCaller]
    simp [step, memCaller, Function.findBlock, findBlockList, Function.entry?, List.head?,
      Option.getD, Option.map, initState, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
      evalInstr, evalOperands, evalOperand, Ty.sizeBytes, lookupName, h]
  simp only [runFuel, hstep]

/-- With no argument the caller's parameter is unbound, so its call is undefined
and every outcome is a behaviour. -/
theorem memCaller_beh_nil (calls : Calls) (o : Outcome) :
    Beh calls memCaller [] o := by
  refine Or.inl ⟨1, ?_⟩
  have hstep : step calls memCaller (initState memCaller ([] : List Value)) = .ub := by
    simp [step, memCaller, Function.findBlock, findBlockList, Function.entry?, List.head?,
      Option.getD, Option.map, initState, List.zip, denoteCode, denoteRun, State.bindAll, evalInstr, evalOperands,
      evalOperand, Ty.sizeBytes, lookupName]
  simp only [runFuel, hstep]

/-- A caller with its own local observes the loop's selection outside the
callee's band.  Its `alloca` precedes the call, so the shared allocator seeds the
body at address `9` and the loop's two locals occupy `Band 9 25`; the caller's
own local at `Band 1 9` is written identically on both sides, and its one `load`
is at address `1`, outside `Band 9 25`, so it reads back what the store wrote
rather than the callee's band.  The call is at base `9`, so the proof consults
`CallRefinesWithin` at base `9` in the form `loop_seam_within_refines`, where the
memory clause is `loop_run_at_base`'s agreement `Band 9 25`. -/
theorem memCaller_replaces_loop_within (x : BitVec 64) :
    RefinesWithinAcross (envForBody 10000 16 loopFunction)
      (envForBody 10000 16 candidateFunction)
      memCaller memCaller (Band 9 25) := by
  intro args o ho
  match args with
  | [] =>
    exact ⟨o, memCaller_beh_nil (envForBody 10000 16 candidateFunction) o,
      Outcome.agreesOutside_refl o _⟩
  | a :: rest =>
    match a with
    | .int w v =>
      by_cases hw : w = 64
      · subst hw
        -- the candidate resolves the call at base `9`, so the relation's `none`
        -- branch is excluded; the loop's own run and the candidate's pin the two
        -- outcomes, and the relation supplies their agreement at `Band 9 25`
        obtain ⟨memC, hrunC, hmemC⟩ := candidate_run_mem_eq v [] 9
        have hCrun : runFuel noCalls 10000 candidateFunction
            { env := (candidateFunction.params.zip [.int 64 v]).map fun p => (p.1.1, p.2)
              mem := [], next := 9, pc := candidateFunction.entry?.getD "", pre := none } =
            some (.ret (some (.int 64 (byteLoop v))) memC) := by
          simpa [initState] using hrunC
        have hC : envForBody 10000 16 candidateFunction seamSymbol [.int 64 v] [] 9 =
            some { ret := .int 64 (byteLoop v), mem := memC, next := 25 } := by
          simp [envForBody, hCrun]
        obtain ⟨memL, _hagreeL, hrunL⟩ := loop_run_at_base v 9 []
        have hLrun : runFuel noCalls 10000 loopFunction
            { env := (loopFunction.params.zip [.int 64 v]).map fun p => (p.1.1, p.2)
              mem := [], next := 9, pc := loopFunction.entry?.getD "", pre := none } =
            some (.ret (some (.int 64 (spec v))) memL) := by
          simpa [initState] using runFuel_mono_le (by decide : 19 ≤ 10000) hrunL
        have hL : envForBody 10000 16 loopFunction seamSymbol [.int 64 v] [] 9 =
            some { ret := .int 64 (spec v), mem := memL, next := 25 } := by
          simp [envForBody, hLrun]
        rcases loop_seam_within_refines x [.int 64 v] [] 9 with
          hnone | ⟨r', r, hL', hC', _hret, _hle, _hnext, hmem⟩
        · rw [hC] at hnone
          cases hnone
        · have hr' : r' = { ret := .int 64 (spec v), mem := memL, next := 25 } :=
            Option.some.inj (hL'.symm.trans hL)
          have hr : r = { ret := .int 64 (byteLoop v), mem := memC, next := 25 } :=
            Option.some.inj (hC'.symm.trans hC)
          subst hr'
          subst hr
          have ho1 : Beh (envForBody 10000 16 loopFunction) memCaller [.int 64 v] o := by
            have h : Beh (envForBody 10000 16 loopFunction) memCaller
                (.int 64 v :: rest) o := ho
            simp only [Beh, initState_cons_memCaller] at h ⊢
            exact h
          have ho' : o = .ret (some (.int 64 (spec v)))
              (writeBytes memL 1 (natToBytes (spec v).toNat 8)) :=
            (memCaller_beh (envForBody 10000 16 loopFunction) v
              (r := { ret := .int 64 (spec v), mem := memL, next := 25 })
              (v := spec v) hL rfl o).1 ho1
          refine ⟨.ret (some (.int 64 (byteLoop v)))
              (writeBytes memC 1 (natToBytes (byteLoop v).toNat 8)), ?_, ?_⟩
          · exact (memCaller_beh (envForBody 10000 16 candidateFunction) v
              (r := { ret := .int 64 (byteLoop v), mem := memC, next := 25 })
              (v := byteLoop v) hC rfl _).2 rfl
          · have hmem' : AgreesOutsideMem memL [] (Band 9 25) := by
              rw [hmemC] at hmem
              exact hmem
            rw [ho', hmemC, byteLoop_eq_spec]
            exact ⟨rfl, AgreesOutsideMem.writeBytes_same hmem' 1 _⟩
      · exact ⟨o, memCaller_beh_of_unresolved (envForBody 10000 16 candidateFunction)
          (.int w v) rest o
          (candidate_envForBody_none_of_head (.int w v) rest [] 9 (by
            intro y hy
            injection hy with hw' _
            exact hw hw')), Outcome.agreesOutside_refl o _⟩
    | .ptr p =>
      exact ⟨o, memCaller_beh_of_unresolved (envForBody 10000 16 candidateFunction)
        (.ptr p) rest o
        (candidate_envForBody_none_of_head (.ptr p) rest [] 9 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩
    | .vec n' w' lanes =>
      exact ⟨o, memCaller_beh_of_unresolved (envForBody 10000 16 candidateFunction)
        (.vec n' w' lanes) rest o
        (candidate_envForBody_none_of_head (.vec n' w' lanes) rest [] 9 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩

    | .float bits =>
      exact ⟨o, memCaller_beh_of_unresolved (envForBody 10000 16 candidateFunction)
        (.float bits) rest o
        (candidate_envForBody_none_of_head (.float bits) rest [] 9 (by
          intro y hy
          cases hy)), Outcome.agreesOutside_refl o _⟩

end LeanLLVM.Refinement
