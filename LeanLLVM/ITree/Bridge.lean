/-
The executable side of the directed relation, for handled trees.

`simtt` is a coinductive statement about bare handled trees; `HandledExec` is
the canonical resolution of one such tree: a `tau` is followed, a visible
`ObsEv` load or store is consumed as the acknowledgement it carries, a call is
resolved by the call environment, `ObsEv.ub` ends in `some .ub` and
`ObsEv.timeout` in `none`.

Two theorems connect the two.

* `handled_runFuel` is the correspondence that makes `runHandled` executable:
  the handler's memory equals the semantics' `State.mem` at every point of the
  run, so the canonical resolution of `runHandled calls frame n f s` is exactly
  `runFuel calls n f s`.  Its local form is `handled_codeT`/`handled_termT`, and
  the memory agreement is `storeValue_mem` (a store advances `State.mem` as
  `storeMem` does) together with the fact that every other instruction and
  terminator leaves the memory alone.  This is why the handler may replace a
  leaf's recorded memory: for a `runT` tree it replaces it with the same memory.
* `simtt_exec_some` eliminates the relation against a completed target run: if
  the target resolves to a defined outcome and the two handled trees are
  related, the source either resolves to undefined behaviour or to an actual
  return that `post` accepts.  Because the trees are bare, the elimination is by
  induction on the target's finite resolution and the relation is unfolded one
  clause at a time.

`_exec_runT` from `Interpret` is unchanged and remains the canonical resolution
of the *unhandled* tree.  Nothing here redefines `Beh`, `Refines` or
`RefinesWithin`: the consequences at the framed and exact posts are corollaries,
and the tree relation is taken between the two `runHandled` trees.
-/
import LeanLLVM.ITree.Simtt
import LeanLLVM.Frames

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree

/-! ### The canonical resolution of a handled tree -/

/-- `HandledExec calls t r` says: following the responses the machine gives — a
visible load or store consumed as acknowledgement, a call resolved by `calls` —
the handled tree `t` ends in `r`.  `r = none` is an exhausted budget and
`some .ub` is undefined behaviour. -/
inductive HandledExec (calls : Calls) : OTree → Option Outcome → Prop where
  | retLeaf {o : Outcome} : HandledExec calls (ret o) (some o)
  | tauStep {t : OTree} {r : Option Outcome} :
      HandledExec calls t r → HandledExec calls (tau t) r
  | load {addr : Nat} {ty : Ty} {resp : Option Value} {k : Unit → OTree}
      {r : Option Outcome} :
      HandledExec calls (k ()) r →
      HandledExec calls (vis (ObsEv.load addr ty resp) k) r
  | store {addr : Nat} {ty : Ty} {v : Value} {k : Unit → OTree}
      {r : Option Outcome} :
      HandledExec calls (k ()) r → HandledExec calls (vis (ObsEv.store addr ty v) k) r
  | call {callee : String} {args : List Value} {k : Option Value → OTree}
      {r : Option Outcome} :
      HandledExec calls (k (calls callee args)) r →
      HandledExec calls (vis (ObsEv.call callee args) k) r
  | ub {k : Empty → OTree} : HandledExec calls (vis ObsEv.ub k) (some Outcome.ub)
  | timeout {k : Empty → OTree} : HandledExec calls (vis ObsEv.timeout k) none

/-! ### Inverting a canonical resolution

As with `Exec`, the tree constructors are definitions over the coinductive
carrier, so the inversion keeps the tree a variable and reports the constructor
it must have come from. -/

theorem HandledExec_inv {calls : Calls} {t : OTree} {r : Option Outcome}
    (h : HandledExec calls t r) :
    (∃ o : Outcome, t = ret o ∧ r = some o) ∨
    (∃ t' : OTree, t = tau t' ∧ HandledExec calls t' r) ∨
    (∃ (addr : Nat) (ty : Ty) (resp : Option Value) (k : Unit → OTree),
      t = vis (ObsEv.load addr ty resp) k ∧ HandledExec calls (k ()) r) ∨
    (∃ (addr : Nat) (ty : Ty) (v : Value) (k : Unit → OTree),
      t = vis (ObsEv.store addr ty v) k ∧ HandledExec calls (k ()) r) ∨
    (∃ (callee : String) (args : List Value) (k : Option Value → OTree),
      t = vis (ObsEv.call callee args) k ∧ HandledExec calls (k (calls callee args)) r) ∨
    (∃ k : Empty → OTree, t = vis ObsEv.ub k ∧ r = some Outcome.ub) ∨
    (∃ k : Empty → OTree, t = vis ObsEv.timeout k ∧ r = none) := by
  cases h with
  | retLeaf => exact Or.inl ⟨_, rfl, rfl⟩
  | tauStep h' => exact Or.inr (Or.inl ⟨_, rfl, h'⟩)
  | load h' => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, h'⟩))
  | store h' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, h'⟩)))
  | call h' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, h'⟩))))
  | ub => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))
  | timeout => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩)))))

theorem HandledExec.ret_inv {calls : Calls} {o : Outcome} {r : Option Outcome}
    (h : HandledExec calls (ret o) r) : r = some o := by
  rcases HandledExec_inv h with ⟨o', ht, hr⟩ | ⟨t', ht, _⟩ | ⟨a, ty, rp, k, ht, _⟩ |
    ⟨a, ty, v, k, ht, _⟩ | ⟨c, args, k, ht, _⟩ | ⟨k, ht, _⟩ | ⟨k, ht, _⟩
  · rw [← ret_inj ht] at hr
    exact hr
  · exact absurd ht ret_ne_tau
  · exact absurd ht (ret_ne_vis (ObsEv.load a ty rp) k)
  · exact absurd ht (ret_ne_vis (ObsEv.store a ty v) k)
  · exact absurd ht (ret_ne_vis (ObsEv.call c args) k)
  · exact absurd ht (ret_ne_vis ObsEv.ub k)
  · exact absurd ht (ret_ne_vis ObsEv.timeout k)

theorem HandledExec.tau_inv {calls : Calls} {t : OTree} {r : Option Outcome}
    (h : HandledExec calls (tau t) r) : HandledExec calls t r := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, he⟩ | ⟨a, ty, rp, k, ht, _⟩ |
    ⟨a, ty, v, k, ht, _⟩ | ⟨c, args, k, ht, _⟩ | ⟨k, ht, _⟩ | ⟨k, ht, _⟩
  · exact absurd ht (ret_ne_tau (v := o) (t := t)).symm
  · rw [tau_inj ht]
    exact he
  · exact absurd ht (tau_ne_vis (ObsEv.load a ty rp) k)
  · exact absurd ht (tau_ne_vis (ObsEv.store a ty v) k)
  · exact absurd ht (tau_ne_vis (ObsEv.call c args) k)
  · exact absurd ht (tau_ne_vis ObsEv.ub k)
  · exact absurd ht (tau_ne_vis ObsEv.timeout k)

theorem HandledExec.vis_load_inv {calls : Calls} {addr : Nat} {ty : Ty}
    {resp : Option Value} {k : Unit → OTree} {r : Option Outcome}
    (h : HandledExec calls (vis (ObsEv.load addr ty resp) k) r) :
    HandledExec calls (k ()) r := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', rp, k', ht, he⟩ |
    ⟨a, ty', v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ret_ne_vis (ObsEv.load addr ty resp) k).symm
  · exact absurd ht (tau_ne_vis (ObsEv.load addr ty resp) k).symm
  · obtain ⟨hEv, hk⟩ := vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht (vis_load_ne_store)
  · exact absurd ht (vis_load_ne_call)
  · exact absurd ht (vis_ub_ne_load k' addr ty resp k).symm
  · exact absurd ht (vis_timeout_ne_load k' addr ty resp k).symm

theorem HandledExec.vis_store_inv {calls : Calls} {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → OTree} {r : Option Outcome}
    (h : HandledExec calls (vis (ObsEv.store addr ty v) k) r) :
    HandledExec calls (k ()) r := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', rp, k', ht, _⟩ |
    ⟨a, ty', v', k', ht, he⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ret_ne_vis (ObsEv.store addr ty v) k).symm
  · exact absurd ht (tau_ne_vis (ObsEv.store addr ty v) k).symm
  · exact absurd ht (vis_load_ne_store).symm
  · obtain ⟨hEv, hk⟩ := vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht vis_store_ne_call
  · exact absurd ht (vis_ub_ne_store _ addr ty v k).symm
  · exact absurd ht (vis_timeout_ne_store _ addr ty v k).symm

theorem HandledExec.vis_call_inv {calls : Calls} {callee : String} {args : List Value}
    {k : Option Value → OTree} {r : Option Outcome}
    (h : HandledExec calls (vis (ObsEv.call callee args) k) r) :
    HandledExec calls (k (calls callee args)) r := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', rp, k', ht, _⟩ |
    ⟨a, ty', v, k', ht, _⟩ | ⟨c, args', k', ht, he⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ret_ne_vis (ObsEv.call callee args) k).symm
  · exact absurd ht (tau_ne_vis (ObsEv.call callee args) k).symm
  · exact absurd ht (vis_load_ne_call).symm
  · exact absurd ht (vis_store_ne_call).symm
  · obtain ⟨hEv, hk⟩ := vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht (vis_ub_ne_call _ callee args k).symm
  · exact absurd ht (vis_timeout_ne_call _ callee args k).symm

theorem HandledExec.vis_ub_inv {calls : Calls} {k : Empty → OTree} {r : Option Outcome}
    (h : HandledExec calls (vis ObsEv.ub k) r) : r = some Outcome.ub := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty, rp, k', ht, _⟩ |
    ⟨a, ty, v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, hr⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ret_ne_vis ObsEv.ub k).symm
  · exact absurd ht (tau_ne_vis ObsEv.ub k).symm
  · exact absurd ht (vis_ub_ne_load k a ty rp k')
  · exact absurd ht (vis_ub_ne_store k a ty v k')
  · exact absurd ht (vis_ub_ne_call k c args k')
  · exact hr
  · exact absurd ht (vis_ub_ne_timeout k k')

theorem HandledExec.vis_timeout_inv {calls : Calls} {k : Empty → OTree}
    {r : Option Outcome} (h : HandledExec calls (vis ObsEv.timeout k) r) : r = none := by
  rcases HandledExec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty, rp, k', ht, _⟩ |
    ⟨a, ty, v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, hr⟩
  · exact absurd ht (ret_ne_vis ObsEv.timeout k).symm
  · exact absurd ht (tau_ne_vis ObsEv.timeout k).symm
  · exact absurd ht (vis_timeout_ne_load k a ty rp k')
  · exact absurd ht (vis_timeout_ne_store k a ty v k')
  · exact absurd ht (vis_timeout_ne_call k c args k')
  · exact absurd ht (vis_ub_ne_timeout k' k).symm
  · exact hr

/-! ### Commuting a resolution through silent steps -/

/-- A silent step does not change what a resolution ends in. -/
theorem HandledExec.silentStep {calls : Calls} {p p' : OTree} {r : Option Outcome}
    (hs : SilentStep p p') (he : HandledExec calls p r) : HandledExec calls p' r := by
  obtain ⟨t, hp, hq⟩ := SilentStep_inv hs
  subst hq
  exact HandledExec.tau_inv (hp ▸ he)

/-- The same for a finite silent closure. -/
theorem HandledExec.silentHead {calls : Calls} {p q : OTree} {r : Option Outcome}
    (hs : SilentHead p q) : HandledExec calls p r → HandledExec calls q r := by
  induction hs with
  | refl => exact id
  | tail _ hstep ih => exact fun he => HandledExec.silentStep hstep (ih he)

/-- A resolution that reaches undefined behaviour ends in it. -/
theorem handled_reachesUb {calls : Calls} {t : OTree} {r : Option Outcome}
    (h : HandledExec calls t r) (hu : ReachesUb t) : r = some Outcome.ub := by
  cases hu with
  | retLeaf h' => exact HandledExec.ret_inv (HandledExec.silentHead h' h)
  | ubNode h' => exact HandledExec.vis_ub_inv (HandledExec.silentHead h' h)

/-- A resolution that reaches a timeout ends in `none`. -/
theorem handled_timeoutReachable {calls : Calls} {t : OTree} {r : Option Outcome}
    (h : HandledExec calls t r) (ht : TimeoutReachable t) : r = none := by
  obtain ⟨q, hq, k, hk⟩ := ht
  have h' := HandledExec.silentHead hq h
  rw [hk] at h'
  exact HandledExec.vis_timeout_inv h'

/-! ### Correspondence with `runFuel`

The general facts the coherence needs: a `ret` terminator and a jump leave the
memory alone, and a store advances it exactly as the handler does. -/

/-- A `ret` terminator keeps the memory. -/
theorem execTerm_ret_mem (s : State) (t : Term) (v : Option Value) (s' : State)
    (h : execTerm s t = .ret v s') : s'.mem = s.mem := by
  match t with
  | .br dest => simp only [execTerm] at h; cases h
  | .unreachable => simp only [execTerm] at h; cases h
  | .condbr c tb fb =>
      simp only [execTerm] at h
      repeat' (split at h)
      all_goals (cases h)
  | .ret ty w =>
      cases ty with
      | void =>
          cases w with
          | none => simp only [execTerm] at h; cases h; rfl
          | some o => simp only [execTerm] at h; cases h
      | int n =>
          cases w with
          | none => simp only [execTerm] at h; cases h
          | some o =>
              simp only [execTerm] at h
              split at h
              · cases h; rfl
              · cases h
      | ptr =>
          cases w with
          | none => simp only [execTerm] at h; cases h
          | some o =>
              simp only [execTerm] at h
              split at h
              · cases h; rfl
              · cases h

/-- `handle` of an undefined-behaviour node resolves to `some .ub`. -/
theorem handled_ubT (calls : Calls) (frame : Nat → Prop) (m : Mem) :
    HandledExec calls (handle frame m ubT) (some Outcome.ub) := by
  unfold handle
  rw [ubT]
  rw [Effect.interp_vis_right (memoryHandler frame) finishOutcome m Ev.ub Empty.elim ObsEv.ub
    (fun e => (Empty.elim e, m)) (memoryHandler_ub (frame := frame) (m := m))]
  exact HandledExec.ub

/-- `handle` of a timeout node resolves to `none`. -/
theorem handled_timeoutT (calls : Calls) (frame : Nat → Prop) (m : Mem) :
    HandledExec calls (handle frame m timeoutT) none := by
  unfold handle
  rw [timeoutT]
  rw [Effect.interp_vis_right (memoryHandler frame) finishOutcome m Ev.timeout Empty.elim
    ObsEv.timeout (fun e => (Empty.elim e, m))
    (memoryHandler_timeout (frame := frame) (m := m))]
  exact HandledExec.timeout

/-- An instruction with no event leaves the memory alone and resolves as its
continuation does. -/
theorem handled_pureInstrT (calls : Calls) (frame : Nat → Prop) (s : State) (i : Instr)
    (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hmem : ∀ s', evalInstr calls s i = some s' → s'.mem = s.mem)
    (hok : ∀ s', evalInstr calls s i = some s' →
      HandledExec calls (handle frame s'.mem (k s')) r)
    (hub : evalInstr calls s i = none → r = some Outcome.ub) :
    HandledExec calls (handle frame s.mem (pureInstrT calls s i k)) r := by
  cases hE : evalInstr calls s i with
  | none =>
      rw [hub hE]
      simp only [pureInstrT, hE]
      exact handled_ubT calls frame s.mem
  | some s' =>
      simp only [pureInstrT, hE]
      have h := hok s' hE
      rwa [hmem s' hE] at h

/-- A load resolves as its continuation does: privately (silent, memory
unchanged) or visibly (annotated with the value the handler computed). -/
theorem handled_instrT_load (calls : Calls) (frame : Nat → Prop) (s : State) (d : String)
    (ty : Ty) (p : Operand) (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.load d ty p) = some s' →
      HandledExec calls (handle frame s'.mem (k s')) r)
    (hub : evalInstr calls s (.load d ty p) = none → r = some Outcome.ub) :
    HandledExec calls (handle frame s.mem (instrT calls s (.load d ty p) k)) r := by
  cases hOp : evalOperand s p with
  | none =>
      have hE : evalInstr calls s (.load d ty p) = none := by simp [evalInstr, hOp]
      rw [hub hE]
      simp only [instrT, hOp]
      exact handled_ubT calls frame s.mem
  | some v =>
      cases v with
      | int w x =>
          have hE : evalInstr calls s (.load d ty p) = none := by simp [evalInstr, hOp]
          rw [hub hE]
          simp only [instrT, hOp]
          exact handled_ubT calls frame s.mem
      | ptr addr =>
          cases hL : loadValue s.mem ty addr with
          | none =>
              have hE : evalInstr calls s (.load d ty p) = none := by
                simp [evalInstr, hOp, hL]
              rw [hub hE]
              simp only [instrT, hOp]
              rw [handle_load_none hL]
              exact HandledExec.load (handled_ubT calls frame s.mem)
          | some val =>
              have hE : evalInstr calls s (.load d ty p) = some (s.bind d val) := by
                simp [evalInstr, hOp, hL]
              simp only [instrT, hOp]
              by_cases hf : InFrame frame addr ty
              · rw [handle_load_private hf hL]
                exact HandledExec.tauStep (hok (s.bind d val) hE)
              · rw [handle_load_out hf hL]
                exact HandledExec.load (hok (s.bind d val) hE)

/-- A store resolves as its continuation does; the handler's memory after it is
`storeMem`, which is the semantics' own `s'.mem`. -/
theorem handled_instrT_store (calls : Calls) (frame : Nat → Prop) (s : State) (ty : Ty)
    (v p : Operand) (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.store ty v p) = some s' →
      HandledExec calls (handle frame s'.mem (k s')) r)
    (hub : evalInstr calls s (.store ty v p) = none → r = some Outcome.ub) :
    HandledExec calls (handle frame s.mem (instrT calls s (.store ty v p) k)) r := by
  cases hv : evalOperand s v with
  | none =>
      have hE : evalInstr calls s (.store ty v p) = none := by simp [evalInstr, hv]
      rw [hub hE]
      simp only [instrT, hv]
      exact handled_ubT calls frame s.mem
  | some vv =>
      cases hp : evalOperand s p with
      | none =>
          have hE : evalInstr calls s (.store ty v p) = none := by
            simp [evalInstr, hv, hp]
          rw [hub hE]
          simp only [instrT, hv, hp]
          exact handled_ubT calls frame s.mem
      | some pv =>
          cases pv with
          | int w x =>
              have hE : evalInstr calls s (.store ty v p) = none := by
                simp [evalInstr, hv, hp]
              rw [hub hE]
              simp only [instrT, hv, hp]
              exact handled_ubT calls frame s.mem
          | ptr addr =>
              cases hS : storeValue s ty vv addr with
              | none =>
                  have hE : evalInstr calls s (.store ty v p) = none := by
                    simp [evalInstr, hv, hp, hS]
                  rw [hub hE]
                  simp only [instrT, hv, hp]
                  by_cases hf : InFrame frame addr ty
                  · rw [handle_store_private hf]
                    simp only [hS]
                    exact HandledExec.tauStep (handled_ubT calls frame (storeMem s.mem ty vv addr))
                  · rw [handle_store_visible hf]
                    simp only [hS]
                    exact HandledExec.store
                      (handled_ubT calls frame (storeMem s.mem ty vv addr))
              | some s' =>
                  have hE : evalInstr calls s (.store ty v p) = some s' := by
                    simp [evalInstr, hv, hp, hS]
                  have hmem : s'.mem = storeMem s.mem ty vv addr :=
                    storeValue_mem s ty vv addr s' hS
                  simp only [instrT, hv, hp]
                  by_cases hf : InFrame frame addr ty
                  · rw [handle_store_private hf, ← hmem]
                    simp only [hS]
                    exact HandledExec.tauStep (hok s' hE)
                  · rw [handle_store_visible hf, ← hmem]
                    simp only [hS]
                    exact HandledExec.store (hok s' hE)

/-- A call re-emits its event and resolves as its continuation does on the
environment's response. -/
theorem handled_instrT_call (calls : Calls) (frame : Nat → Prop) (s : State) (d : String)
    (retTy : Ty) (callee : String) (args : List (Ty × Operand)) (k : State → Tree Ev Outcome)
    (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.call d retTy callee args) = some s' →
      HandledExec calls (handle frame s'.mem (k s')) r)
    (hub : evalInstr calls s (.call d retTy callee args) = none → r = some Outcome.ub) :
    HandledExec calls (handle frame s.mem (instrT calls s (.call d retTy callee args) k)) r := by
  cases ha : evalOperands s args with
  | none =>
      have hE : evalInstr calls s (.call d retTy callee args) = none := by
        simp [evalInstr, ha]
      rw [hub hE]
      simp only [instrT, ha]
      exact handled_ubT calls frame s.mem
  | some vs =>
      cases hC : calls callee vs with
      | none =>
          have hE : evalInstr calls s (.call d retTy callee args) = none := by
            simp [evalInstr, ha, hC]
          rw [hub hE]
          simp only [instrT, ha]
          rw [handle_call]
          refine HandledExec.call ?_
          rw [hC]
          exact handled_ubT calls frame s.mem
      | some val =>
          have hE : evalInstr calls s (.call d retTy callee args) = some (s.bind d val) := by
            simp [evalInstr, ha, hC]
          simp only [instrT, ha]
          rw [handle_call]
          refine HandledExec.call ?_
          rw [hC]
          exact hok (s.bind d val) hE

/-- Straight-line code: the handler's memory tracks the state `denoteCode`
reaches. -/
theorem handled_codeT (calls : Calls) (frame : Nat → Prop) :
    ∀ (is : List Instr) (s : State) (k : State → Tree Ev Outcome) (r : Option Outcome),
      (∀ s', denoteCode calls is s = some s' →
        HandledExec calls (handle frame s'.mem (k s')) r) →
      (denoteCode calls is s = none → r = some Outcome.ub) →
      HandledExec calls (handle frame s.mem (codeT calls is s k)) r
  | [], s, k, r, hok, _ => hok s rfl
  | i :: is, s, k, r, hok, hub => by
      have hokK : ∀ s1, evalInstr calls s i = some s1 →
          HandledExec calls (handle frame s1.mem (codeT calls is s1 k)) r := by
        intro s1 h1
        exact handled_codeT calls frame is s1 k r
          (fun s' h2 => hok s' (by simp [denoteCode, h1, h2]))
          (fun h2 => hub (by simp [denoteCode, h1, h2]))
      have hubK : evalInstr calls s i = none → r = some Outcome.ub := by
        intro h1
        exact hub (by simp [denoteCode, h1])
      show HandledExec calls
        (handle frame s.mem (instrT calls s i (fun s1 => codeT calls is s1 k))) r
      cases i with
      | load d ty p => exact handled_instrT_load calls frame s d ty p _ r hokK hubK
      | store ty v p => exact handled_instrT_store calls frame s ty v p _ r hokK hubK
      | call d rt c args => exact handled_instrT_call calls frame s d rt c args _ r hokK hubK
      | binop d op w a b =>
          exact handled_pureInstrT calls frame s (.binop d op w a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | icmp d pr w a b =>
          exact handled_pureInstrT calls frame s (.icmp d pr w a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | select d ty c a b =>
          exact handled_pureInstrT calls frame s (.select d ty c a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | trunc d wi wo v =>
          exact handled_pureInstrT calls frame s (.trunc d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | zext d wi wo v =>
          exact handled_pureInstrT calls frame s (.zext d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | sext d wi wo v =>
          exact handled_pureInstrT calls frame s (.sext d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | alloca d ty al =>
          exact handled_pureInstrT calls frame s (.alloca d ty al) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK

/-- A terminator resolves as its continuation does on a jump, and its own memory
is the handler's: a `ret` or a jump leaves the memory alone, and `ub` is a `ub`
node. -/
theorem handled_termT (calls : Calls) (frame : Nat → Prop) (n : Nat) (f : Function)
    (s : State) (t : Term) (next : State → Tree Ev Outcome)
    (hnext : ∀ s', execTerm s t = .jump s' →
      HandledExec calls (handle frame s.mem (next s')) (runFuel calls n f s')) :
    HandledExec calls (handle frame s.mem (termT s next t))
      (match execTerm s t with
       | .ub => some Outcome.ub
       | .ret v s' => some (.ret v s'.mem)
       | .jump s' => runFuel calls n f s') := by
  cases h : execTerm s t with
  | ub =>
      simp only [termT, h]
      exact handled_ubT calls frame s.mem
  | ret v s' =>
      simp only [termT, h]
      rw [handle_ret]
      simp only [finishOutcome]
      rw [← execTerm_ret_mem s t v s' h]
      exact HandledExec.retLeaf
  | jump s' =>
      simp only [termT, h]
      exact hnext s' h

/-- The handler's memory is the semantics' memory: the canonical resolution of
`runHandled` is `runFuel`. -/
theorem handled_runFuel (calls : Calls) (frame : Nat → Prop) :
    ∀ (n : Nat) (f : Function) (s : State),
      HandledExec calls (runHandled calls frame n f s) (runFuel calls n f s)
  | 0, f, s => by
      rw [runHandled, handle, runT_zero, runFuel]
      exact handled_timeoutT calls frame s.mem
  | n + 1, f, s => by
      rw [runHandled, handle, runT_succ, runFuel_succ, step_unfold]
      cases hfind : f.findBlock s.pc with
      | none =>
          dsimp only
          exact handled_ubT calls frame s.mem
      | some b =>
          dsimp only
          have hcont : ∀ (s0 : State), HandledExec calls
              (handle frame s0.mem
                (termT s0 (fun s'' => tau (runT calls n f s'')) b.term))
              (match execTerm s0 b.term with
               | .ub => some Outcome.ub
               | .ret v s'' => some (.ret v s''.mem)
               | .jump s'' => runFuel calls n f s'') := by
            intro s0
            exact handled_termT calls frame n f s0 b.term _
              (fun s'' hj => by
                rw [handle_tau, ← execTerm_jump_mem s0 b.term s'' hj]
                exact HandledExec.tauStep (handled_runFuel calls frame n f s''))
          cases hD : denoteCode calls b.instrs s with
          | none =>
              dsimp only
              exact handled_codeT calls frame b.instrs s _ (some Outcome.ub)
                (fun s0 h0 => by rw [hD] at h0; exact absurd h0 (by simp))
                (fun _ => rfl)
          | some s' =>
              cases hT : execTerm s' b.term with
              | ub =>
                  simp only [hT]
                  exact handled_codeT calls frame b.instrs s _ (some Outcome.ub)
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun _ => rfl)
              | ret v s'' =>
                  simp only [hT]
                  exact handled_codeT calls frame b.instrs s _ (some (.ret v s''.mem))
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun h0 => by rw [hD] at h0; exact absurd h0 (by simp))
              | jump s'' =>
                  simp only [hT]
                  exact handled_codeT calls frame b.instrs s _ (runFuel calls n f s'')
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun h0 => by rw [hD] at h0; exact absurd h0 (by simp))

/-! ### Eliminating the relation against a completed run -/

/-- The auxiliary elimination is read over the target's resolution, so a
resolution that starts at a later state is a strictly shorter derivation. -/
theorem simtt_exec_aux {calls : Calls} {post : Outcome → Outcome → Prop} :
    ∀ {tT : OTree} {rT : Option Outcome}, HandledExec calls tT rT →
    ∀ {tS : OTree}, simtt post tT tS →
    ∀ {rS : Option Outcome}, HandledExec calls tS rS →
      rS = some .ub ∨ (rT = none ∧ rS = none) ∨
        ∃ vT vS memT memS, rT = some (.ret vT memT) ∧ rS = some (.ret vS memS) ∧
          post (.ret vT memT) (.ret vS memS) := by
  intro tT rT hT
  induction hT with
  /- A `ret` leaf: its closure is empty, so the target's result is that leaf. -/
  | retLeaf =>
      rename_i o
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          have ho : Outcome.ret _ _ = o := ret_inj (SilentHead_ret_self h1)
          exact Or.inr (Or.inr ⟨_, _, _, _, by rw [← ho],
            HandledExec.ret_inv (HandledExec.silentHead h2 hs), hp⟩)
      | right_ub_ret h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | ub h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | timeout k1 k2 h1 h2 =>
          exact absurd (SilentHead_ret_self h1) (ret_ne_vis ObsEv.timeout k1).symm
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_ret
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_ret
      | vis_load addr ty r k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_ret_self h1) (ret_ne_vis (ObsEv.load addr ty r) k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_ret_self h1) (ret_ne_vis (ObsEv.store addr ty v) k1).symm
      | vis_call callee args k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_ret_self h1) (ret_ne_vis (ObsEv.call callee args) k1).symm
  /- A `tau`: the relation absorbs it. -/
  | tauStep h' ih =>
      rename_i t0 r0
      intro tS he rS hs
      exact ih (simtt_tau_left he) hs
  /- A visible load: the relation's load clause annotates both sides with the
  same response. -/
  | load h' ih =>
      rename_i addr ty resp k r0
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis (ObsEv.load addr ty resp) k)
      | right_ub_ret h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | ub h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | timeout k1 k2 h1 h2 =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_load k1 addr ty resp k)
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_vis (ObsEv.load addr ty resp) k)
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_vis (ObsEv.load addr ty resp) k)
      | vis_load addr' ty' r' k1 k2 h1 h2 hs' =>
          obtain ⟨hev, hk⟩ := vis_inj (SilentHead_vis_self h1)
          obtain ⟨rfl, rfl, rfl⟩ := obs_load_inj hev
          rw [hk] at hs'
          exact ih hs' (HandledExec.vis_load_inv (HandledExec.silentHead h2 hs))
      | vis_store addr' ty' v k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_load_ne_store).symm
      | vis_call callee args k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_load_ne_call).symm
  /- A visible store. -/
  | store h' ih =>
      rename_i addr ty v k r0
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis (ObsEv.store addr ty v) k)
      | right_ub_ret h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | ub h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | timeout k1 k2 h1 h2 =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_store k1 addr ty v k)
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_vis (ObsEv.store addr ty v) k)
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_vis (ObsEv.store addr ty v) k)
      | vis_load addr' ty' r k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) vis_load_ne_store
      | vis_store addr' ty' v' k1 k2 h1 h2 hs' =>
          obtain ⟨hev, hk⟩ := vis_inj (SilentHead_vis_self h1)
          obtain ⟨rfl, rfl, rfl⟩ := obs_store_inj hev
          rw [hk] at hs'
          exact ih hs' (HandledExec.vis_store_inv (HandledExec.silentHead h2 hs))
      | vis_call callee args k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_store_ne_call).symm
  /- A call: the environment's response is passed to the continuation. -/
  | call h' ih =>
      rename_i callee args k r0
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis (ObsEv.call callee args) k)
      | right_ub_ret h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | ub h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | timeout k1 k2 h1 h2 =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_call k1 callee args k)
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_vis (ObsEv.call callee args) k)
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_vis (ObsEv.call callee args) k)
      | vis_load addr' ty' r k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) vis_load_ne_call
      | vis_store addr' ty' v k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) vis_store_ne_call
      | vis_call callee' args' k1 k2 h1 h2 hs' =>
          obtain ⟨hev, hk⟩ := vis_inj (SilentHead_vis_self h1)
          have hc := (obs_call_inj hev).1
          have ha := (obs_call_inj hev).2
          simp only [hc, ha] at *
          rw [hk] at hs'
          exact ih (hs' (calls callee args))
            (HandledExec.vis_call_inv (HandledExec.silentHead h2 hs))
  /- An undefined-behaviour node. -/
  | ub =>
      rename_i k0
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis ObsEv.ub k0)
      | right_ub_ret h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | ub h1 h2 => exact Or.inl (handled_reachesUb hs h2)
      | timeout k1 k2 h1 h2 =>
          exact absurd (SilentHead_vis_self h1) (vis_ub_ne_timeout k0 k1).symm
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_ub
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_ub
      | vis_load addr ty r k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_ub_ne_load k0 addr ty r k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_ub_ne_store k0 addr ty v k1).symm
      | vis_call callee args k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_ub_ne_call k0 callee args k1).symm
  /- An exhausted budget. -/
  | timeout =>
      rename_i k0
      intro tS he rS hs
      have hF := (simtt_iff post _ _).mp he
      cases hF with
      | ret_ret h1 h2 hp =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis ObsEv.timeout k0)
      | right_ub_ret h1 h2 =>
          exact absurd (SilentHead_vis_self h1) (ret_ne_vis ObsEv.timeout k0)
      | ub h1 h2 => exact absurd h1 not_reachesUb_timeout
      | timeout k1 k2 h1 h2 =>
          exact Or.inr (Or.inl ⟨rfl, handled_timeoutReachable hs ⟨_, h2, k2, rfl⟩⟩)
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_timeout
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_timeout
      | vis_load addr ty r k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_load k0 addr ty r k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_store k0 addr ty v k1).symm
      | vis_call callee args k1 k2 h1 h2 hs' =>
          exact absurd (SilentHead_vis_self h1) (vis_timeout_ne_call k0 callee args k1).symm

/-- A completed target return transports: the source either runs into undefined
behaviour or returns an outcome the postcondition accepts. -/
theorem simtt_exec_some {calls : Calls} {post : Outcome → Outcome → Prop}
    {tT tS : OTree} {oT : Outcome}
    (he : simtt post tT tS) {rS : Option Outcome} (ht : HandledExec calls tT (some oT))
    (hs : HandledExec calls tS rS) :
    rS = some .ub ∨
      ∃ vT vS memT memS, oT = .ret vT memT ∧ rS = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS) := by
  rcases simtt_exec_aux ht he hs with hub | ⟨hnoneT, hnoneS⟩ | ⟨vT, vS, memT, memS, hrT, hrS, hp⟩
  · exact Or.inl hub
  · cases hnoneT
  · exact Or.inr ⟨vT, vS, memT, memS, Option.some.inj hrT, hrS, hp⟩

/-- A relation between two handled trees transports a completed target run: the
source either runs into undefined behaviour at its own budget or returns an
outcome the postcondition accepts.  The budgets are separate, and a budget that
exhausts is not a completed outcome. -/
theorem simtt_runFuel_some (calls : Calls) (frame : Nat → Prop)
    (post : Outcome → Outcome → Prop) (target source : Function)
    (args : List Value) (nT nS : Nat) (oT : Outcome)
    (he : simtt post
      (runHandled calls frame nT target (initState target args))
      (runHandled calls frame nS source (initState source args)))
    (ht : runFuel calls nT target (initState target args) = some oT) :
    runFuel calls nS source (initState source args) = some .ub ∨
      ∃ vT vS memT memS,
        oT = .ret vT memT ∧
        runFuel calls nS source (initState source args) = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS) := by
  have hT : HandledExec calls (runHandled calls frame nT target (initState target args))
      (some oT) := ht ▸ handled_runFuel calls frame nT target (initState target args)
  have hS : HandledExec calls (runHandled calls frame nS source (initState source args))
      (runFuel calls nS source (initState source args)) :=
    handled_runFuel calls frame nS source (initState source args)
  exact simtt_exec_some he hT hS

/-- Every observable target behaviour is transported, with its own budget on
each side: a target run that succeeds at some budget is matched by undefined
behaviour on the source or by an actual source return the postcondition
accepts.  A target that never finishes has no behaviour, so no budget of the
target is silently treated as one. -/
theorem simtt_beh_inclusion (calls : Calls) (frame : Nat → Prop)
    (post : Outcome → Outcome → Prop) (target source : Function)
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, simtt post
        (runHandled calls frame nT target (initState target args))
        (runHandled calls frame nS source (initState source args))) :
    ∀ args oT, Beh calls target args oT →
      (∃ nS, runFuel calls nS source (initState source args) = some .ub) ∨
      (∃ nS vT vS memT memS,
        oT = .ret vT memT ∧
        runFuel calls nS source (initState source args) = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS)) := by
  intro args oT ho
  rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨nS, he⟩ := hsim args n .ub hn
    rcases simtt_runFuel_some calls frame post target source args n nS .ub he hn with
      hub | ⟨vT, vS, memT, memS, hEq⟩
    · exact Or.inl ⟨nS, hub⟩
    · exact nomatch hEq
  · obtain ⟨nS, he⟩ := hsim args n oT hn
    rcases simtt_runFuel_some calls frame post target source args n nS oT he hn with
      hub | ⟨vT, vS, memT, memS, hEq, hrS, hp⟩
    · exact Or.inl ⟨nS, hub⟩
    · exact Or.inr ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩

/-- The framed refinement relation follows from a tree relation available for
every completed target run, in the target-to-source direction.  A source that
runs into undefined behaviour is a behaviour for every outcome, so the target's
own outcome is matched by itself; otherwise the matched return is the witness.
The two returned memories are each tree's own handled final memory. -/
theorem refinesWithin_of_simtt {calls : Calls} {target source : Function}
    {frame : Nat → Prop}
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, simtt (Outcome.AgreesOutside frame)
        (runHandled calls frame nT target (initState target args))
        (runHandled calls frame nS source (initState source args))) :
    RefinesWithin calls target source frame := by
  intro args o ho
  rcases simtt_beh_inclusion calls frame (Outcome.AgreesOutside frame) target source hsim args o ho
    with ⟨nS, hub⟩ | ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩
  · exact ⟨o, Or.inl ⟨nS, hub⟩, Outcome.agreesOutside_refl o frame⟩
  · exact ⟨.ret vS memS, Or.inr ⟨nS, hrS⟩, by rw [hEq]; exact hp⟩

/-- Exact refinement follows the same way at the equality postcondition, through
handled trees at the empty frame. -/
theorem refines_of_simtt {calls : Calls} {target source : Function}
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, simtt Eq
        (runHandled calls (fun _ => False) nT target (initState target args))
        (runHandled calls (fun _ => False) nS source (initState source args))) :
    Refines calls target source := by
  intro args o ho
  rcases simtt_beh_inclusion calls (fun _ => False) Eq target source hsim args o ho with
    ⟨nS, hub⟩ | ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩
  · exact Or.inl ⟨nS, hub⟩
  · rw [hEq]
    exact Or.inr ⟨nS, by rw [hp]; exact hrS⟩

end LeanLLVM.ITree
