/-
The executable side of the directed relation.

`eutt` is a coinductive statement about trees; `Exec` is the canonical
resolution of one tree against a memory: following the responses the machine
itself gives, the tree ends in an outcome, `none` for an exhausted budget and
`some .ub` for undefined behaviour.

This module proves that a completed target resolution transports through the
relation.  A target return that is definitely defined (`some (.ret v m)`) is
answered either by undefined behaviour on the source or by an actual source
return that `post` accepts; a target timeout is answered by a source timeout.
The budget-explicit and behaviour-level corollaries specialise this to
`runFuel` and `Beh`, and the loop instance derives one fixed-budget
consequence from it.

Nothing here redefines `Beh`, `Refines` or `RefinesWithin`: the consequences at
the framed and exact posts are corollaries, and no pass or route reasons
through the tree layer.
-/
import LeanLLVM.ITree.Eutt
import LeanLLVM.Frames

namespace LeanLLVM.ITree

open LeanLLVM
open ITree

/-! ### Inverting a canonical resolution

`Exec` is indexed by the tree, and the tree constructors are definitions over
the coinductive carrier, so `cases` on `Exec` at a literal tree would have to
eliminate a coinductive index.  The inversion below keeps the tree a variable
and reports the constructor it must have come from; every later step reads a
tree's shape off the equality in its disjunct.
-/

theorem Exec_inv {calls : Calls} {t : ITree Ev Outcome} {m : Mem} {r : Option Outcome}
    (h : Exec calls t m r) :
    (∃ o : Outcome, t = ITree.ret o ∧ r = some o) ∨
    (∃ t' : ITree Ev Outcome, t = ITree.tau t' ∧ Exec calls t' m r) ∨
    (∃ (addr : Nat) (ty : Ty) (k : Option Value → ITree Ev Outcome),
      t = ITree.vis (Ev.load addr ty) k ∧ Exec calls (k (loadValue m ty addr)) m r) ∨
    (∃ (addr : Nat) (ty : Ty) (v : Value) (k : Unit → ITree Ev Outcome),
      t = ITree.vis (Ev.store addr ty v) k ∧ Exec calls (k ()) (storeMem m ty v addr) r) ∨
    (∃ (callee : String) (args : List Value) (k : Option Value → ITree Ev Outcome),
      t = ITree.vis (Ev.call callee args) k ∧ Exec calls (k (calls callee args)) m r) ∨
    (∃ k : Empty → ITree Ev Outcome, t = ITree.vis Ev.ub k ∧ r = some Outcome.ub) ∨
    (∃ k : Empty → ITree Ev Outcome, t = ITree.vis Ev.timeout k ∧ r = none) := by
  cases h with
  | ret => exact Or.inl ⟨_, rfl, rfl⟩
  | tau h' => exact Or.inr (Or.inl ⟨_, rfl, h'⟩)
  | load h' => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, h'⟩))
  | store h' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, h'⟩)))
  | call h' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, h'⟩))))
  | ub => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))
  | timeout => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩)))))

/-! ### Distinct visible events

The same pair of events can only be matched when their response types and
constructors agree, so a closure that ends at one event cannot be read as a
closure to another.
-/

/-- A load and a call share the response type `Option Value`, so their
disjointness is at the event and not at the response type. -/
theorem ev_load_ne_call (addr : Nat) (ty : Ty) (callee : String) (args : List Value) :
    (Ev.load addr ty : Ev (Option Value)) ≠ Ev.call callee args := by
  intro h
  cases h

theorem vis_load_ne_vis_store {addr : Nat} {ty : Ty} {addr' : Nat} {ty' : Ty}
    {v : Value} {k : Option Value → ITree Ev Outcome}
    {k' : Unit → ITree Ev Outcome} :
    (ITree.vis (Ev.load addr ty) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.store addr' ty' v) k' :=
  ITree.vis_ne_of_type_ne (h := option_value_ne_unit)

theorem vis_load_ne_vis_call {addr : Nat} {ty : Ty} {callee : String}
    {args : List Value} {k k' : Option Value → ITree Ev Outcome} :
    (ITree.vis (Ev.load addr ty) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.call callee args) k' := by
  intro h
  exact ev_load_ne_call addr ty callee args (ITree.vis_inj h).1

theorem vis_load_ne_vis_ub {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.load addr ty) k : ITree Ev Outcome) ≠ ITree.vis Ev.ub k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value.symm)

theorem vis_load_ne_vis_timeout {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.load addr ty) k : ITree Ev Outcome) ≠ ITree.vis Ev.timeout k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value.symm)

theorem vis_store_ne_vis_load {addr : Nat} {ty : Ty} {v : Value} {addr' : Nat}
    {ty' : Ty} {k : Unit → ITree Ev Outcome} {k' : Option Value → ITree Ev Outcome} :
    (ITree.vis (Ev.store addr ty v) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.load addr' ty') k' :=
  ITree.vis_ne_of_type_ne (h := option_value_ne_unit.symm)

theorem vis_store_ne_vis_call {addr : Nat} {ty : Ty} {v : Value} {callee : String}
    {args : List Value} {k : Unit → ITree Ev Outcome}
    {k' : Option Value → ITree Ev Outcome} :
    (ITree.vis (Ev.store addr ty v) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.call callee args) k' :=
  ITree.vis_ne_of_type_ne (h := option_value_ne_unit.symm)

theorem vis_store_ne_vis_ub {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.store addr ty v) k : ITree Ev Outcome) ≠ ITree.vis Ev.ub k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_unit.symm)

theorem vis_store_ne_vis_timeout {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.store addr ty v) k : ITree Ev Outcome) ≠ ITree.vis Ev.timeout k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_unit.symm)

theorem vis_call_ne_vis_load {callee : String} {args : List Value} {addr : Nat}
    {ty : Ty} {k k' : Option Value → ITree Ev Outcome} :
    (ITree.vis (Ev.call callee args) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.load addr ty) k' := by
  intro h
  exact (ev_load_ne_call addr ty callee args).symm (ITree.vis_inj h).1

theorem vis_call_ne_vis_store {callee : String} {args : List Value} {addr : Nat}
    {ty : Ty} {v : Value} {k : Option Value → ITree Ev Outcome}
    {k' : Unit → ITree Ev Outcome} :
    (ITree.vis (Ev.call callee args) k : ITree Ev Outcome) ≠
      ITree.vis (Ev.store addr ty v) k' :=
  ITree.vis_ne_of_type_ne (h := option_value_ne_unit)

theorem vis_call_ne_vis_ub {callee : String} {args : List Value}
    {k : Option Value → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.call callee args) k : ITree Ev Outcome) ≠ ITree.vis Ev.ub k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value.symm)

theorem vis_call_ne_vis_timeout {callee : String} {args : List Value}
    {k : Option Value → ITree Ev Outcome} {k' : Empty → ITree Ev Outcome} :
    (ITree.vis (Ev.call callee args) k : ITree Ev Outcome) ≠ ITree.vis Ev.timeout k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value.symm)

/-! ### Shape-specific inversions

Each of these reads the one constructor a resolution at a tree of known shape
can have used. -/

theorem Exec.ret_inv {calls : Calls} {o : Outcome} {m : Mem} {r : Option Outcome}
    (h : Exec calls (ITree.ret o) m r) : r = some o := by
  rcases Exec_inv h with ⟨o', ht, hr⟩ | ⟨t', ht, _⟩ | ⟨a, ty, k, ht, _⟩ |
    ⟨a, ty, v, k, ht, _⟩ | ⟨c, args, k, ht, _⟩ | ⟨k, ht, _⟩ | ⟨k, ht, _⟩
  · rw [← ITree.ret_inj ht] at hr
    exact hr
  · exact absurd ht ITree.ret_ne_tau
  · exact absurd ht (ITree.ret_ne_vis (Ev.load a ty) k)
  · exact absurd ht (ITree.ret_ne_vis (Ev.store a ty v) k)
  · exact absurd ht (ITree.ret_ne_vis (Ev.call c args) k)
  · exact absurd ht (ITree.ret_ne_vis Ev.ub k)
  · exact absurd ht (ITree.ret_ne_vis Ev.timeout k)

theorem Exec.tau_inv {calls : Calls} {t : ITree Ev Outcome} {m : Mem}
    {r : Option Outcome} (h : Exec calls (ITree.tau t) m r) : Exec calls t m r := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, he⟩ | ⟨a, ty, k, ht, _⟩ |
    ⟨a, ty, v, k, ht, _⟩ | ⟨c, args, k, ht, _⟩ | ⟨k, ht, _⟩ | ⟨k, ht, _⟩
  · exact absurd ht (ITree.ret_ne_tau (v := o) (t := t)).symm
  · rw [ITree.tau_inj ht]
    exact he
  · exact absurd ht (ITree.tau_ne_vis (Ev.load a ty) k)
  · exact absurd ht (ITree.tau_ne_vis (Ev.store a ty v) k)
  · exact absurd ht (ITree.tau_ne_vis (Ev.call c args) k)
  · exact absurd ht (ITree.tau_ne_vis Ev.ub k)
  · exact absurd ht (ITree.tau_ne_vis Ev.timeout k)

theorem Exec.vis_load_inv {calls : Calls} {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {m : Mem} {r : Option Outcome}
    (h : Exec calls (ITree.vis (Ev.load addr ty) k) m r) :
    Exec calls (k (loadValue m ty addr)) m r := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', k', ht, he⟩ |
    ⟨a, ty', v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ITree.ret_ne_vis (Ev.load addr ty) k).symm
  · exact absurd ht (ITree.tau_ne_vis (Ev.load addr ty) k).symm
  · obtain ⟨hEv, hk⟩ := ITree.vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht vis_load_ne_vis_store
  · exact absurd ht vis_load_ne_vis_call
  · exact absurd ht vis_load_ne_vis_ub
  · exact absurd ht vis_load_ne_vis_timeout

theorem Exec.vis_store_inv {calls : Calls} {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → ITree Ev Outcome} {m : Mem} {r : Option Outcome}
    (h : Exec calls (ITree.vis (Ev.store addr ty v) k) m r) :
    Exec calls (k ()) (storeMem m ty v addr) r := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', k', ht, _⟩ |
    ⟨a, ty', v', k', ht, he⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ITree.ret_ne_vis (Ev.store addr ty v) k).symm
  · exact absurd ht (ITree.tau_ne_vis (Ev.store addr ty v) k).symm
  · exact absurd ht vis_store_ne_vis_load
  · obtain ⟨hEv, hk⟩ := ITree.vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht vis_store_ne_vis_call
  · exact absurd ht vis_store_ne_vis_ub
  · exact absurd ht vis_store_ne_vis_timeout

theorem Exec.vis_call_inv {calls : Calls} {callee : String} {args : List Value}
    {k : Option Value → ITree Ev Outcome} {m : Mem} {r : Option Outcome}
    (h : Exec calls (ITree.vis (Ev.call callee args) k) m r) :
    Exec calls (k (calls callee args)) m r := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty', k', ht, _⟩ |
    ⟨a, ty', v, k', ht, _⟩ | ⟨c, args', k', ht, he⟩ | ⟨k', ht, _⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ITree.ret_ne_vis (Ev.call callee args) k).symm
  · exact absurd ht (ITree.tau_ne_vis (Ev.call callee args) k).symm
  · exact absurd ht vis_call_ne_vis_load
  · exact absurd ht vis_call_ne_vis_store
  · obtain ⟨hEv, hk⟩ := ITree.vis_inj ht
    cases hEv
    rw [hk]
    exact he
  · exact absurd ht vis_call_ne_vis_ub
  · exact absurd ht vis_call_ne_vis_timeout

theorem Exec.vis_ub_inv {calls : Calls} {k : Empty → ITree Ev Outcome} {m : Mem}
    {r : Option Outcome} (h : Exec calls (ITree.vis Ev.ub k) m r) :
    r = some Outcome.ub := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty, k', ht, _⟩ |
    ⟨a, ty, v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, hr⟩ | ⟨k', ht, _⟩
  · exact absurd ht (ITree.ret_ne_vis Ev.ub k).symm
  · exact absurd ht (ITree.tau_ne_vis Ev.ub k).symm
  · exact absurd ht (vis_load_ne_vis_ub (k' := k)).symm
  · exact absurd ht (vis_store_ne_vis_ub (k' := k)).symm
  · exact absurd ht (vis_call_ne_vis_ub (k' := k)).symm
  · exact hr
  · exact absurd ht (vis_ub_ne_timeout k k')

theorem Exec.vis_timeout_inv {calls : Calls} {k : Empty → ITree Ev Outcome}
    {m : Mem} {r : Option Outcome} (h : Exec calls (ITree.vis Ev.timeout k) m r) :
    r = none := by
  rcases Exec_inv h with ⟨o, ht, _⟩ | ⟨t', ht, _⟩ | ⟨a, ty, k', ht, _⟩ |
    ⟨a, ty, v, k', ht, _⟩ | ⟨c, args, k', ht, _⟩ | ⟨k', ht, _⟩ | ⟨k', ht, hr⟩
  · exact absurd ht (ITree.ret_ne_vis Ev.timeout k).symm
  · exact absurd ht (ITree.tau_ne_vis Ev.timeout k).symm
  · exact absurd ht (vis_load_ne_vis_timeout (k' := k)).symm
  · exact absurd ht (vis_store_ne_vis_timeout (k' := k)).symm
  · exact absurd ht (vis_call_ne_vis_timeout (k' := k)).symm
  · exact absurd ht (vis_ub_ne_timeout k' k).symm
  · exact hr

/-! ### Commuting a resolution through silent steps -/

/-- A private step does not change what a resolution ends in: the resolution
follows the same tree the step does. -/
theorem Exec.silentStep {calls : Calls} {frame : Nat → Prop} {p p' : TS}
    {r : Option Outcome} (hs : SilentStep frame p p') (he : Exec calls p.1 p.2 r) :
    Exec calls p'.1 p'.2 r := by
  rcases SilentStep_inv hs with ⟨t, m, hp, hq⟩ | ⟨a, ty, k, m, v, hv, hf, hp, hq⟩ |
    ⟨a, ty, v, k, m, hf, hp, hq⟩
  · subst hp
    subst hq
    exact Exec.tau_inv he
  · subst hp
    rw [hq]
    have h' := Exec.vis_load_inv he
    rw [hv] at h'
    exact h'
  · subst hp
    rw [hq]
    exact Exec.vis_store_inv he

/-- The same for a finite silent closure. -/
theorem Exec.silentHead {calls : Calls} {frame : Nat → Prop} {p q : TS}
    {r : Option Outcome} (hs : SilentHead frame p q) :
    Exec calls p.1 p.2 r → Exec calls q.1 q.2 r := by
  induction hs with
  | refl => exact id
  | tail _ hstep ih => exact fun he => Exec.silentStep hstep (ih he)

/-! ### Silent steps of a tree of known shape -/

theorem SilentStep.tau_shape {frame : Nat → Prop} {t : ITree Ev Outcome} {m : Mem}
    {q : TS} (h : SilentStep frame (ITree.tau t, m) q) : q = (t, m) := by
  rcases SilentStep_inv h with ⟨t', m', hp, hq⟩ | ⟨a, ty, k, m', v, hv, hf, hp, hq⟩ |
    ⟨a, ty, v, k, m', hf, hp, hq⟩
  · obtain ⟨hτ, hm⟩ := Prod.mk.inj hp
    subst hq
    have ht : t = t' := ITree.tau_inj hτ
    subst ht
    subst hm
    rfl
  · exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.load a ty) k)
  · exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.store a ty v) k)

theorem SilentStep.load_shape {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentStep frame (ITree.vis (Ev.load addr ty) k, m) q) :
    ∃ v : Value, loadValue m ty addr = some v ∧ q = (k v, m) := by
  rcases SilentStep_inv h with ⟨t, m', hp, hq⟩ | ⟨a, ty', k', m', v, hv, hf, hp, hq⟩ |
    ⟨a, ty', v, k', m', hf, hp, hq⟩
  · exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.load addr ty) k).symm
  · obtain ⟨hT, hM⟩ := Prod.mk.inj hp
    obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
    subst hq
    cases hEv
    subst hk
    subst hM
    exact ⟨v, hv, rfl⟩
  · exact absurd (Prod.mk.inj hp).1 vis_load_ne_vis_store

theorem SilentStep.store_shape {frame : Nat → Prop} {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentStep frame (ITree.vis (Ev.store addr ty v) k, m) q) :
    ∃ _hf : InFrame frame addr ty, q = (k (), storeMem m ty v addr) := by
  rcases SilentStep_inv h with ⟨t, m', hp, hq⟩ | ⟨a, ty', k', m', v', hv, hf, hp, hq⟩ |
    ⟨a, ty', v', k', m', hf, hp, hq⟩
  · exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.store addr ty v) k).symm
  · exact absurd (Prod.mk.inj hp).1 vis_store_ne_vis_load
  · obtain ⟨hT, hM⟩ := Prod.mk.inj hp
    obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
    subst hq
    cases hEv
    subst hk
    subst hM
    exact ⟨hf, rfl⟩

theorem call_no_step {frame : Nat → Prop} {callee : String} {args : List Value}
    {k : Option Value → ITree Ev Outcome} {m : Mem} :
    ∀ q : TS, ¬ SilentStep frame (ITree.vis (Ev.call callee args) k, m) q := by
  intro q h
  rcases SilentStep_inv h with ⟨t, m', hp, _⟩ | ⟨a, ty, k', m', v, hv, hf, hp, _⟩ |
    ⟨a, ty, v, k', m', hf, hp, _⟩
  · exact ITree.tau_ne_vis (Ev.call callee args) k ((Prod.mk.inj hp).1).symm
  · exact vis_call_ne_vis_load (Prod.mk.inj hp).1
  · exact absurd (Prod.mk.inj hp).1 vis_call_ne_vis_store

/-- A call node has no silent step, so every closure from one is empty. -/
theorem SilentHead.call_self {frame : Nat → Prop} {callee : String} {args : List Value}
    {k : Option Value → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.vis (Ev.call callee args) k, m) q) :
    q = (ITree.vis (Ev.call callee args) k, m) :=
  SilentHead.eq_of_no_step call_no_step h

/-! ### Stripping a step from a silent closure -/

/-- A closure from a `tau` state is empty only at that state itself; everywhere
else its first step is the `tau`, and the rest is a closure from the successor. -/
theorem SilentHead.tau_strip {frame : Nat → Prop} {t : ITree Ev Outcome} {m : Mem}
    {q : TS} (h : SilentHead frame (ITree.tau t, m) q)
    (hne : q ≠ (ITree.tau t, m)) : SilentHead frame (t, m) q := by
  rcases SilentHead_inv h with hpq | ⟨p', hstep, hrest⟩
  · exact absurd hpq.symm hne
  · rw [SilentStep.tau_shape hstep] at hrest
    exact hrest

theorem SilentHead.load_strip {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.vis (Ev.load addr ty) k, m) q)
    (hne : q ≠ (ITree.vis (Ev.load addr ty) k, m)) :
    ∃ v : Value, loadValue m ty addr = some v ∧ SilentHead frame (k v, m) q := by
  rcases SilentHead_inv h with hpq | ⟨p', hstep, hrest⟩
  · exact absurd hpq.symm hne
  · obtain ⟨v, hv, hq⟩ := SilentStep.load_shape hstep
    subst hq
    exact ⟨v, hv, hrest⟩

theorem SilentHead.store_strip {frame : Nat → Prop} {addr : Nat} {ty : Ty} {v : Value}
    {k : Unit → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.vis (Ev.store addr ty v) k, m) q)
    (hne : q ≠ (ITree.vis (Ev.store addr ty v) k, m)) :
    SilentHead frame (k (), storeMem m ty v addr) q := by
  rcases SilentHead_inv h with hpq | ⟨p', hstep, hrest⟩
  · exact absurd hpq.symm hne
  · obtain ⟨hf, hq⟩ := SilentStep.store_shape hstep
    subst hq
    exact hrest

/-! ### Silent divergence and completion cannot coexist -/

theorem SilentDiverges.tau_strip {frame : Nat → Prop} {t : ITree Ev Outcome} {m : Mem} :
    SilentDiverges frame (ITree.tau t, m) → SilentDiverges frame (t, m) := by
  intro h
  have h' : DivF frame (SilentDiverges frame) (ITree.tau t, m) :=
    (congrFun (SilentDiverges.eq_1 frame) _).mp h
  cases h' with
  | step hstep hs =>
      rw [SilentStep.tau_shape hstep] at hs
      exact hs

theorem ReachesUb.tau_strip {frame : Nat → Prop} {t : ITree Ev Outcome} {m : Mem} :
    ReachesUb frame (ITree.tau t, m) → ReachesUb frame (t, m) := by
  intro h
  cases h with
  | ret h' =>
      exact ReachesUb.ret (SilentHead.tau_strip h'
        (by intro hh; exact ITree.ret_ne_tau (Prod.mk.inj hh).1))
  | vis h' =>
      exact ReachesUb.vis (SilentHead.tau_strip h'
        (by
          intro hh
          exact (ITree.tau_ne_vis Ev.ub _) ((Prod.mk.inj hh).1).symm))

/-- A completed resolution has no silent divergence behind it: the resolution
follows the tree's own steps, and a silently diverging tree never reaches a
terminal. -/
theorem not_silentDiverges_of_exec {calls : Calls} {frame : Nat → Prop}
    {t : ITree Ev Outcome} {m : Mem} {r : Option Outcome} (he : Exec calls t m r) :
    ¬ SilentDiverges frame (t, m) := by
  induction he with
  | ret => exact not_silentDiverges_ret
  | tau _ ih => exact fun h => ih (SilentDiverges.tau_strip h)
  | load _ ih =>
      intro h
      have h' := (congrFun (SilentDiverges.eq_1 frame) _).mp h
      cases h' with
      | step hstep hs =>
          obtain ⟨v, hv, hq⟩ := SilentStep.load_shape hstep
          subst hq
          exact ih (hv.symm ▸ hs)
  | store _ ih =>
      intro h
      have h' := (congrFun (SilentDiverges.eq_1 frame) _).mp h
      cases h' with
      | step hstep hs =>
          obtain ⟨hf, hq⟩ := SilentStep.store_shape hstep
          subst hq
          exact ih hs
  | call _ ih =>
      intro h
      have h' := (congrFun (SilentDiverges.eq_1 frame) _).mp h
      cases h' with
      | step hstep _ => exact call_no_step _ hstep
  | ub => exact not_silentDiverges_ub
  | timeout => exact not_silentDiverges_timeout

/-- A completed resolution has no timeout behind it either. -/
theorem exec_timeoutReachable {calls : Calls} {frame : Nat → Prop} {p : TS}
    {r : Option Outcome} (ht : TimeoutReachable frame p) (he : Exec calls p.1 p.2 r) :
    r = none := by
  obtain ⟨q, hq, k, hk⟩ := ht
  have h := Exec.silentHead hq he
  rw [hk] at h
  exact Exec.vis_timeout_inv h

/-- A resolution that reaches undefined behaviour ends in it. -/
theorem exec_reachesUb {calls : Calls} {frame : Nat → Prop} {p : TS}
    {r : Option Outcome} (hu : ReachesUb frame p) (he : Exec calls p.1 p.2 r) :
    r = some Outcome.ub := by
  cases hu with
  | ret h => exact Exec.ret_inv (Exec.silentHead h he)
  | vis h => exact Exec.vis_ub_inv (Exec.silentHead h he)

/-- A `tau` on the left of the relation can be read off its closure, so the
relation also holds one step later. -/
theorem eutt_tau_left {frame : Nat → Prop} {post : Outcome → Outcome → Prop}
    {t : ITree Ev Outcome} {m : Mem} {q : TS}
    (h : eutt frame post (ITree.tau t, m) q) : eutt frame post (t, m) q := by
  have hF := (eutt_iff frame post _ _).mp h
  refine (eutt_iff frame post _ _).mpr ?_
  cases hF with
  | ret h1 h2 hp =>
      exact EuttF.ret (SilentHead.tau_strip h1
        (by intro hh; exact ITree.ret_ne_tau (Prod.mk.inj hh).1)) h2 hp
  | right_ub_ret h1 h2 =>
      exact EuttF.right_ub_ret (SilentHead.tau_strip h1
        (by intro hh; exact ITree.ret_ne_tau (Prod.mk.inj hh).1)) h2
  | ub h1 h2 => exact EuttF.ub (ReachesUb.tau_strip h1) h2
  | timeout k1 k2 h1 h2 =>
      exact EuttF.timeout k1 k2 (SilentHead.tau_strip h1
        (by
          intro hh
          exact (ITree.tau_ne_vis Ev.timeout k1) ((Prod.mk.inj hh).1).symm)) h2
  | left_diverges hdiv hnt => exact EuttF.left_diverges (SilentDiverges.tau_strip hdiv) hnt
  | right_diverges hdiv2 hdiv1 =>
      exact EuttF.right_diverges hdiv2 (SilentDiverges.tau_strip hdiv1)
  | vis_load addr ty k1 k2 h1 h2 hm hs =>
      exact EuttF.vis_load addr ty k1 k2 (SilentHead.tau_strip h1
        (by
          intro hh
          exact (ITree.tau_ne_vis (Ev.load addr ty) k1) ((Prod.mk.inj hh).1).symm)) h2 hm hs
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact EuttF.vis_store addr ty v k1 k2 (SilentHead.tau_strip h1
        (by
          intro hh
          exact (ITree.tau_ne_vis (Ev.store addr ty v) k1) ((Prod.mk.inj hh).1).symm)) h2 hs
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact EuttF.vis_call callee args k1 k2 (SilentHead.tau_strip h1
        (by
          intro hh
          exact (ITree.tau_ne_vis (Ev.call callee args) k1) ((Prod.mk.inj hh).1).symm)) h2 hs

/-! ### Eliminating the coinductive relation against a completed run

The auxiliary statement is read over the target's resolution, so a resolution
that starts at a later state is a strictly shorter derivation.  A private step
of the target is either an in-frame access, whose continuation the relation
hands over directly, or a `tau`, which the relation's closure absorbs
(`eutt_tau_left`); a visible event advances the relation to the two
continuations' matching states.
-/

theorem eutt_exec_aux {calls : Calls} {frame : Nat → Prop}
    {post : Outcome → Outcome → Prop} :
    ∀ {tT : ITree Ev Outcome} {mT : Mem} {rT : Option Outcome},
      Exec calls tT mT rT →
    ∀ {tS : ITree Ev Outcome} {mS : Mem}, eutt frame post (tT, mT) (tS, mS) →
    ∀ {rS : Option Outcome}, Exec calls tS mS rS →
      rS = some .ub ∨ (rT = none ∧ rS = none) ∨
        ∃ vT vS memT memS, rT = some (.ret vT memT) ∧ rS = some (.ret vS memS) ∧
          post (.ret vT memT) (.ret vS memS) := by
  intro tT mT rT hT
  induction hT with
  /- A `ret` leaf: the closure is empty, so the target's result is that leaf. -/
  | ret =>
      rename_i o m'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          have ho : Outcome.ret _ _ = o := ITree.ret_inj (Prod.mk.inj (SilentHead_ret_self h1)).1
          exact Or.inr (Or.inr ⟨_, _, _, _, by rw [← ho],
            Exec.ret_inv (Exec.silentHead h2 hs), hp⟩)
      | right_ub_ret h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | ub h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | timeout k1 k2 h1 h2 =>
          exact absurd (Prod.mk.inj (SilentHead_ret_self h1)).1
            (ITree.ret_ne_vis Ev.timeout k1).symm
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_ret
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_ret
      | vis_load addr ty k1 k2 h1 h2 hm hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ret_self h1)).1
            (ITree.ret_ne_vis (Ev.load addr ty) k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ret_self h1)).1
            (ITree.ret_ne_vis (Ev.store addr ty v) k1).symm
      | vis_call callee args k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ret_self h1)).1
            (ITree.ret_ne_vis (Ev.call callee args) k1).symm
  /- A `tau`: the relation absorbs it, and the continuation is one step shorter. -/
  | tau h' ih =>
      rename_i t0 m0 rT'
      intro tS mS he rS hs
      exact ih (eutt_tau_left he) hs
  /- A visible load: the relation advances to the responses of the two memories,
  which agree by the load clause. -/
  | load h' ih =>
      rename_i addr ty k m' rT'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          obtain ⟨v, hv, h1'⟩ := SilentHead.load_strip h1
            (by intro hh; exact ITree.ret_ne_vis (Ev.load addr ty) k (Prod.mk.inj hh).1)
          have hsub : Exec calls (k v) m' rT' := hv ▸ h'
          exact Or.inr (Or.inr ⟨_, _, _, _, Exec.ret_inv (Exec.silentHead h1' hsub),
            Exec.ret_inv (Exec.silentHead h2 hs), hp⟩)
      | right_ub_ret h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | ub h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | timeout k1 k2 h1 h2 =>
          obtain ⟨v, hv, h1'⟩ := SilentHead.load_strip h1
            (by
              intro hh
              exact (vis_load_ne_vis_timeout (k := k) (k' := k1)).symm (Prod.mk.inj hh).1)
          have hsub : Exec calls (k v) m' rT' := hv ▸ h'
          have hrT : rT' = none := Exec.vis_timeout_inv (Exec.silentHead h1' hsub)
          have hrS : rS = none := Exec.vis_timeout_inv (Exec.silentHead h2 hs)
          exact Or.inr (Or.inl ⟨hrT, hrS⟩)
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_of_exec
            (Exec.load (addr := addr) (ty := ty) (k := k) (m := m') (r := rT') h'))
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_of_exec
            (Exec.load (addr := addr) (ty := ty) (k := k) (m := m') (r := rT') h'))
      | vis_load addr' ty' k1 k2 h1 h2 hm hsc =>
          rename_i m1 m2
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · obtain ⟨hT, hM⟩ := Prod.mk.inj hpq
            obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
            subst hk
            rw [← hM] at hsc hm
            cases hEv
            refine ih ?_ (Exec.vis_load_inv (Exec.silentHead h2 hs))
            rw [hm]
            exact hsc (loadValue m2 ty addr)
          · obtain ⟨v, hv, hq⟩ := SilentStep.load_shape hstep
            subst hq
            have hrel : eutt frame post (k v, m') (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_load addr' ty' k1 k2 hrest h2 hm hsc)
            have hrel' : eutt frame post (k (loadValue m' ty addr), m') (tS, mS) := by
              rw [hv]
              exact hrel
            exact ih hrel' hs
      | vis_store addr' ty' v k1 k2 h1 h2 hsc =>
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · exact absurd (Prod.mk.inj hpq).1 vis_load_ne_vis_store
          · obtain ⟨v0, hv0, hq⟩ := SilentStep.load_shape hstep
            subst hq
            have hrel : eutt frame post (k v0, m') (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_store addr' ty' v k1 k2 hrest h2 hsc)
            have hrel' : eutt frame post (k (loadValue m' ty addr), m') (tS, mS) := by
              rw [hv0]
              exact hrel
            exact ih hrel' hs
      | vis_call callee args k1 k2 h1 h2 hsc =>
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · exact absurd (Prod.mk.inj hpq).1 vis_load_ne_vis_call
          · obtain ⟨v0, hv0, hq⟩ := SilentStep.load_shape hstep
            subst hq
            have hrel : eutt frame post (k v0, m') (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_call callee args k1 k2 hrest h2 hsc)
            have hrel' : eutt frame post (k (loadValue m' ty addr), m') (tS, mS) := by
              rw [hv0]
              exact hrel
            exact ih hrel' hs
  /- A visible store: the clause advances both memories, so the continuation is
  the target's own next state. -/
  | store h' ih =>
      rename_i addr ty v k m' rT'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          have h1' := SilentHead.store_strip h1
            (by intro hh; exact ITree.ret_ne_vis (Ev.store addr ty v) k (Prod.mk.inj hh).1)
          exact Or.inr (Or.inr ⟨_, _, _, _, Exec.ret_inv (Exec.silentHead h1' h'),
            Exec.ret_inv (Exec.silentHead h2 hs), hp⟩)
      | right_ub_ret h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | ub h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | timeout k1 k2 h1 h2 =>
          have h1' := SilentHead.store_strip h1
            (by
              intro hh
              exact (vis_store_ne_vis_timeout (k := k) (k' := k1)).symm (Prod.mk.inj hh).1)
          have hrT : rT' = none := Exec.vis_timeout_inv (Exec.silentHead h1' h')
          have hrS : rS = none := Exec.vis_timeout_inv (Exec.silentHead h2 hs)
          exact Or.inr (Or.inl ⟨hrT, hrS⟩)
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_of_exec
            (Exec.store (addr := addr) (ty := ty) (v := v) (k := k) (m := m') (r := rT') h'))
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_of_exec
            (Exec.store (addr := addr) (ty := ty) (v := v) (k := k) (m := m') (r := rT') h'))
      | vis_load addr' ty' k1 k2 h1 h2 hm hsc =>
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · exact absurd (Prod.mk.inj hpq).1 vis_store_ne_vis_load
          · obtain ⟨hf, hq⟩ := SilentStep.store_shape hstep
            subst hq
            have hrel : eutt frame post (k (), storeMem m' ty v addr) (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_load addr' ty' k1 k2 hrest h2 hm hsc)
            exact ih hrel hs
      | vis_store addr' ty' v' k1 k2 h1 h2 hsc =>
          rename_i m1 m2
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · obtain ⟨hT, hM⟩ := Prod.mk.inj hpq
            obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
            subst hk
            rw [← hM] at hsc
            cases hEv
            exact ih hsc (Exec.vis_store_inv (Exec.silentHead h2 hs))
          · obtain ⟨hf, hq⟩ := SilentStep.store_shape hstep
            subst hq
            have hrel : eutt frame post (k (), storeMem m' ty v addr) (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_store addr' ty' v' k1 k2 hrest h2 hsc)
            exact ih hrel hs
      | vis_call callee args k1 k2 h1 h2 hsc =>
          rcases SilentHead_inv h1 with hpq | ⟨p', hstep, hrest⟩
          · exact absurd (Prod.mk.inj hpq).1 vis_store_ne_vis_call
          · obtain ⟨hf, hq⟩ := SilentStep.store_shape hstep
            subst hq
            have hrel : eutt frame post (k (), storeMem m' ty v addr) (tS, mS) :=
              (eutt_iff frame post _ _).mpr (EuttF.vis_call callee args k1 k2 hrest h2 hsc)
            exact ih hrel hs
  /- A call: the node has no silent step, so its closure is empty. -/
  | call h' ih =>
      rename_i callee args k m' rT'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          exact absurd (Prod.mk.inj (SilentHead.call_self h1)).1
            (ITree.ret_ne_vis (Ev.call callee args) k)
      | right_ub_ret h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | ub h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | timeout k1 k2 h1 h2 =>
          exact absurd (Prod.mk.inj (SilentHead.call_self h1)).1
            (vis_call_ne_vis_timeout (k := k) (k' := k1)).symm
      | left_diverges hdiv hnt =>
          exact absurd hdiv (not_silentDiverges_of_exec
            (Exec.call (callee := callee) (args := args) (k := k) (m := m') (r := rT') h'))
      | right_diverges hdiv2 hdiv1 =>
          exact absurd hdiv1 (not_silentDiverges_of_exec
            (Exec.call (callee := callee) (args := args) (k := k) (m := m') (r := rT') h'))
      | vis_load addr' ty' k1 k2 h1 h2 hm hsc =>
          exact absurd (Prod.mk.inj (SilentHead.call_self h1)).1 vis_call_ne_vis_load.symm
      | vis_store addr' ty' v' k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead.call_self h1)).1 vis_call_ne_vis_store.symm
      | vis_call callee' args' k1 k2 h1 h2 hsc =>
          rename_i m1 m2
          obtain ⟨hT, hM⟩ := Prod.mk.inj (SilentHead.call_self h1)
          obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
          subst hk
          rw [hM] at hsc
          cases hEv
          refine ih ?_ (Exec.vis_call_inv (Exec.silentHead h2 hs))
          exact hsc (calls callee args)
  /- An undefined-behaviour node resolves to `ub`; the source side is forced to
  reach one too. -/
  | ub =>
      rename_i k0 m'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          exact absurd (Prod.mk.inj (SilentHead_ub_self h1)).1
            (ITree.ret_ne_vis Ev.ub k0)
      | right_ub_ret h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | ub h1 h2 => exact Or.inl (exec_reachesUb h2 hs)
      | timeout k1 k2 h1 h2 =>
          exact absurd (Prod.mk.inj (SilentHead_ub_self h1)).1
            (vis_ub_ne_timeout k0 k1).symm
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_ub
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_ub
      | vis_load addr ty k1 k2 h1 h2 hm hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ub_self h1)).1
            (vis_ub_ne_load k0 addr ty k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ub_self h1)).1
            (vis_ub_ne_store k0 addr ty v k1).symm
      | vis_call callee args k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_ub_self h1)).1
            (vis_ub_ne_call k0 callee args k1).symm
  /- An exhausted budget resolves to `none`, and so does the source. -/
  | timeout =>
      rename_i k0 m'
      intro tS mS he rS hs
      have hF := (eutt_iff frame post _ _).mp he
      cases hF with
      | ret h1 h2 hp =>
          exact absurd (Prod.mk.inj (SilentHead_timeout_self h1)).1
            (ITree.ret_ne_vis Ev.timeout k0)
      | right_ub_ret h1 h2 =>
          exact absurd (Prod.mk.inj (SilentHead_timeout_self h1)).1
            (ITree.ret_ne_vis Ev.timeout k0)
      | ub h1 h2 => exact absurd h1 not_reachesUb_timeout
      | timeout k1 k2 h1 h2 =>
          exact Or.inr (Or.inl ⟨rfl,
            Exec.vis_timeout_inv (Exec.silentHead h2 hs)⟩)
      | left_diverges hdiv hnt => exact absurd hdiv not_silentDiverges_timeout
      | right_diverges hdiv2 hdiv1 => exact absurd hdiv1 not_silentDiverges_timeout
      | vis_load addr ty k1 k2 h1 h2 hm hsc =>
          exact absurd (Prod.mk.inj (SilentHead_timeout_self h1)).1
            (vis_timeout_ne_load k0 addr ty k1).symm
      | vis_store addr ty v k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_timeout_self h1)).1
            (vis_timeout_ne_store k0 addr ty v k1).symm
      | vis_call callee args k1 k2 h1 h2 hsc =>
          exact absurd (Prod.mk.inj (SilentHead_timeout_self h1)).1
            (vis_timeout_ne_call k0 callee args k1).symm

/-- A completed target return transports: the source either runs into undefined
behaviour or returns an outcome the postcondition accepts. -/
theorem eutt_exec_some {calls : Calls} {frame : Nat → Prop}
    {post : Outcome → Outcome → Prop} {tT tS : ITree Ev Outcome}
    {mT mS : Mem} {oT : Outcome}
    (he : eutt frame post (tT, mT) (tS, mS))
    {rS : Option Outcome} (ht : Exec calls tT mT (some oT))
    (hs : Exec calls tS mS rS) :
    rS = some .ub ∨
      ∃ vT vS memT memS, oT = .ret vT memT ∧ rS = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS) := by
  rcases eutt_exec_aux ht he hs with hub | ⟨hnoneT, hnoneS⟩ | ⟨vT, vS, memT, memS, hrT, hrS, hp⟩
  · exact Or.inl hub
  · cases hnoneT
  · exact Or.inr ⟨vT, vS, memT, memS, Option.some.inj hrT, hrS, hp⟩

/-- A relation at two explicit budgets transports a completed target run: the
source either runs into undefined behaviour at its own budget or returns an
outcome the postcondition accepts.  The budgets are separate, and a budget that
exhausts is not a completed outcome. -/
theorem eutt_runFuel_some (calls : Calls) (frame : Nat → Prop)
    (post : Outcome → Outcome → Prop) (target source : Function)
    (args : List Value) (nT nS : Nat) (oT : Outcome)
    (he : eutt frame post
      (runT calls nT target (initState target args), (initState target args).mem)
      (runT calls nS source (initState source args), (initState source args).mem))
    (ht : runFuel calls nT target (initState target args) = some oT) :
    runFuel calls nS source (initState source args) = some .ub ∨
      ∃ vT vS memT memS,
        oT = .ret vT memT ∧
        runFuel calls nS source (initState source args) = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS) := by
  have hT : Exec calls (runT calls nT target (initState target args))
      (initState target args).mem (some oT) := ht ▸ exec_runT calls nT target (initState target args)
  have hS : Exec calls (runT calls nS source (initState source args))
      (initState source args).mem (runFuel calls nS source (initState source args)) :=
    exec_runT calls nS source (initState source args)
  exact eutt_exec_some he hT hS

/-- Every observable target behaviour is transported, with its own budget on
each side: a target run that succeeds at some budget is matched by undefined
behaviour on the source or by an actual source return the postcondition
accepts.  A target that never finishes has no behaviour, so no budget of the
target is silently treated as one. -/
theorem eutt_beh_inclusion (calls : Calls) (frame : Nat → Prop)
    (post : Outcome → Outcome → Prop) (target source : Function)
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, eutt frame post
        (runT calls nT target (initState target args), (initState target args).mem)
        (runT calls nS source (initState source args), (initState source args).mem)) :
    ∀ args oT, Beh calls target args oT →
      (∃ nS, runFuel calls nS source (initState source args) = some .ub) ∨
      (∃ nS vT vS memT memS,
        oT = .ret vT memT ∧
        runFuel calls nS source (initState source args) = some (.ret vS memS) ∧
        post (.ret vT memT) (.ret vS memS)) := by
  intro args oT ho
  rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨nS, he⟩ := hsim args n .ub hn
    rcases eutt_runFuel_some calls frame post target source args n nS .ub he hn with hub | ⟨vT, vS, memT, memS, hEq⟩
    · exact Or.inl ⟨nS, hub⟩
    · exact nomatch hEq
  · obtain ⟨nS, he⟩ := hsim args n oT hn
    rcases eutt_runFuel_some calls frame post target source args n nS oT he hn with hub | ⟨vT, vS, memT, memS, hEq, hrS, hp⟩
    · exact Or.inl ⟨nS, hub⟩
    · exact Or.inr ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩

/-- The framed refinement relation follows from a tree simulation available for
every completed target run, in the target-to-source direction.  A source that
runs into undefined behaviour is a behaviour for every outcome, so the target's
own outcome is matched by itself; otherwise the matched return is the witness. -/
theorem refinesWithin_of_eutt {calls : Calls} {target source : Function}
    {frame : Nat → Prop}
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, eutt frame (Outcome.AgreesOutside frame)
        (runT calls nT target (initState target args), (initState target args).mem)
        (runT calls nS source (initState source args), (initState source args).mem)) :
    RefinesWithin calls target source frame := by
  intro args o ho
  rcases eutt_beh_inclusion calls frame (Outcome.AgreesOutside frame) target source hsim args o ho with
    ⟨nS, hub⟩ | ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩
  · exact ⟨o, Or.inl ⟨nS, hub⟩, Outcome.agreesOutside_refl o frame⟩
  · exact ⟨.ret vS memS, Or.inr ⟨nS, hrS⟩, by rw [hEq]; exact hp⟩

/-- Exact refinement follows the same way at the equality postcondition. -/
theorem refines_of_eutt {calls : Calls} {target source : Function}
    (hsim : ∀ args nT oT, runFuel calls nT target (initState target args) = some oT →
      ∃ nS, eutt (fun _ => False) Eq
        (runT calls nT target (initState target args), (initState target args).mem)
        (runT calls nS source (initState source args), (initState source args).mem)) :
    Refines calls target source := by
  intro args o ho
  rcases eutt_beh_inclusion calls (fun _ => False) Eq target source hsim args o ho with
    ⟨nS, hub⟩ | ⟨nS, vT, vS, memT, memS, hEq, hrS, hp⟩
  · exact Or.inl ⟨nS, hub⟩
  · rw [hEq]
    exact Or.inr ⟨nS, by rw [hp]; exact hrS⟩

/-- A load whose byte span is not in the frame is not a silent step, so every
closure from it is empty. -/
theorem load_no_step_of_notInFrame {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {k : Option Value → ITree Ev Outcome} {m : Mem} (hout : ¬ InFrame frame addr ty) :
    ∀ q : TS, ¬ SilentStep frame (ITree.vis (Ev.load addr ty) k, m) q := by
  intro q h
  rcases SilentStep_inv h with ⟨t, m', hp, _⟩ | ⟨a, ty', k', m', v, hv, hf, hp, _⟩ |
    ⟨a, ty', v, k', m', hf, hp, _⟩
  · exact (ITree.tau_ne_vis (Ev.load addr ty) k) ((Prod.mk.inj hp).1).symm
  · obtain ⟨hT, _⟩ := Prod.mk.inj hp
    obtain ⟨hEv, _⟩ := ITree.vis_inj hT
    cases hEv
    exact hout hf
  · exact absurd (Prod.mk.inj hp).1 vis_load_ne_vis_store

/-- The load clause bite: when the load is visible (its span is outside the
frame) and the two memories give different canonical responses, the relation
refuses the pair.  Every other clause of `EuttF` needs a silent closure from the
load node, and an out-of-frame load has none. -/
theorem not_eutt_load_of_disagree {frame : Nat → Prop} {post : Outcome → Outcome → Prop}
    {addr : Nat} {ty : Ty} {k k2 : Option Value → ITree Ev Outcome}
    {m1 m2 : Mem} (hout : ¬ InFrame frame addr ty)
    (hne : loadValue m1 ty addr ≠ loadValue m2 ty addr) :
    ¬ eutt frame post (ITree.vis (Ev.load addr ty) k, m1)
      (ITree.vis (Ev.load addr ty) k2, m2) := by
  intro h
  have hF := (eutt_iff frame post _ _).mp h
  have hno := load_no_step_of_notInFrame (frame := frame) (addr := addr) (ty := ty) (k := k) (m := m1) hout
  cases hF with
  | ret h1 h2 hp =>
      exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h1)).1
        (ITree.ret_ne_vis (Ev.load addr ty) k)
  | right_ub_ret h1 h2 =>
      exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h1)).1
        (ITree.ret_ne_vis (Ev.load addr ty) k)
  | ub h1 h2 =>
      cases h1 with
      | ret h' =>
          exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h')).1
            (ITree.ret_ne_vis (Ev.load addr ty) k)
      | vis h' =>
          exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h')).1
            (vis_load_ne_vis_ub (k := k)).symm
  | timeout k1 k2 h1 h2 =>
      exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h1)).1
        (vis_load_ne_vis_timeout (k := k)).symm
  | left_diverges hdiv hnt =>
      have h' := (congrFun (SilentDiverges.eq_1 frame) _).mp hdiv
      cases h' with
      | step hstep _ => exact hno _ hstep
  | right_diverges hdiv2 hdiv1 =>
      have h' := (congrFun (SilentDiverges.eq_1 frame) _).mp hdiv1
      cases h' with
      | step hstep _ => exact hno _ hstep
  | vis_load addr' ty' kc1 kc2 h1 h2 hm hsc =>
      obtain ⟨hT, hM⟩ := Prod.mk.inj (SilentHead.eq_of_no_step hno h1)
      obtain ⟨_, hM2⟩ := Prod.mk.inj (SilentHead.eq_of_no_step
        (load_no_step_of_notInFrame (frame := frame) (addr := addr) (ty := ty)
          (k := k2) (m := m2) hout) h2)
      obtain ⟨hEv, hk⟩ := ITree.vis_inj hT
      rw [hM] at hm
      rw [hM2] at hm
      cases hEv
      exact hne hm
  | vis_store addr' ty' v kc1 kc2 h1 h2 hsc =>
      exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h1)).1 vis_store_ne_vis_load
  | vis_call callee args kc1 kc2 h1 h2 hsc =>
      exact absurd (Prod.mk.inj (SilentHead.eq_of_no_step hno h1)).1 vis_call_ne_vis_load

end LeanLLVM.ITree
