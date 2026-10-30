/-
Memory as an effect.

`Ev` is the source protocol: loads, stores, calls, and the two stuck nodes.
This module folds that protocol into a single stateful handler over the host
semantics' `Mem`, so that the memory a tree reads and writes stops being a
separate index of the relation and becomes part of the tree:

* a **defined in-frame load** and **any in-frame store** are answered privately,
  which the generic fold performs as a `tau` and which advances the handler's
  own memory;
* every other access stays **visible**, annotated with the response the handler
  itself computed from its current memory (`loadValue m ty addr` for a load, and
  the stored address/type/value for a store), so an out-of-frame access or an
  undefined load is never discarded;
* a **call** is re-emitted unchanged, so its response type survives and the
  response is what a later resolution supplies;
* `ub` and `timeout` stay distinct stuck nodes with empty response types.

`handle frame m t` is the handled tree and `runHandled calls frame n f s` its
specialisation to `runT`.  Both are `noncomputable`: `frame` is an arbitrary
proposition-valued predicate with no decider in the existing API, so the
handler's branch is decided by `Classical.propDecidable`.  This is a
proof-facing tree producer, not a new executable route — `runFuel`, `runT`,
`Beh` and the routes that use them are untouched, and a computable handler would
need a decidable frame representation or an explicit `DecidablePred` contract.

The final memory of a handled tree is the handler's, so `finishOutcome` replaces
whatever memory a leaf recorded.  For a tree produced by `runT` the handler's
memory always equals the semantics' own `State.mem` (proved in `Bridge`), which
is what makes the replacement innocuous there; for an arbitrary synthetic tree
it is a deliberate change of the leaf.
-/
import LeanLLVM.ITree.Interpret
import ITree.Effect

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open Classical

/-- The events a handled tree can still show.  A visible load carries the
handler-computed response, so two visible loads are comparable only when their
annotations agree. -/
inductive ObsEv : Type → Type where
  /-- A load that was not answered privately, annotated with its response. -/
  | load (addr : Nat) (ty : Ty) (response : Option Value) : ObsEv Unit
  /-- A store outside the frame: its address, type and value. -/
  | store (addr : Nat) (ty : Ty) (v : Value) : ObsEv Unit
  /-- A call, with the response type a resolution supplies. -/
  | call (callee : String) (args : List Value) : ObsEv (Option Value)
  /-- Undefined behaviour, as a completed stuck node. -/
  | ub : ObsEv Empty
  /-- An exhausted budget, as a stuck node with no continuation. -/
  | timeout : ObsEv Empty

/-- The trees the handled relation compares: bare trees over `ObsEv`. -/
abbrev OTree := Tree ObsEv Outcome

/-- The whole byte span of a typed access lies in the frame. -/
def InFrame (frame : Nat → Prop) (addr : Nat) (ty : Ty) : Prop :=
  ∀ k, k < ty.sizeBytes → frame (addr + k)

/-- The handler's final state is the one a leaf reports. -/
def finishOutcome (o : Outcome) (m : Mem) : Outcome :=
  match o with
  | .ret v _ => .ret v m
  | .ub => .ub

/-! ### The handler

Each constructor proves its own tag: `Ev.ub ↦ ObsEv.ub` and
`Ev.timeout ↦ ObsEv.timeout`, so an event cannot become an empty-response
terminal merely because the generic handler type would allow it.
-/

/-- The memory handler.  `frame` selects the private accesses; the in-frame
decision is classical, so this is proof-facing. -/
noncomputable def memoryHandler (frame : Nat → Prop) : Effect.Handler Ev ObsEv Mem :=
  fun {α} m e =>
    match e with
    | Ev.load addr ty =>
        match loadValue m ty addr with
        | some v =>
            if InFrame frame addr ty then
              Sum.inl (some v, m)
            else
              Sum.inr ⟨Unit, ObsEv.load addr ty (some v), fun () => (some v, m)⟩
        | none =>
            Sum.inr ⟨Unit, ObsEv.load addr ty none, fun () => (none, m)⟩
    | Ev.store addr ty v =>
        if InFrame frame addr ty then
          Sum.inl ((), storeMem m ty v addr)
        else
          Sum.inr ⟨Unit, ObsEv.store addr ty v, fun () => ((), storeMem m ty v addr)⟩
    | Ev.call callee args =>
        Sum.inr ⟨Option Value, ObsEv.call callee args, fun r => (r, m)⟩
    | Ev.ub =>
        Sum.inr ⟨Empty, ObsEv.ub, fun e => (Empty.elim e, m)⟩
    | Ev.timeout =>
        Sum.inr ⟨Empty, ObsEv.timeout, fun e => (Empty.elim e, m)⟩

/-- The handled tree: `Ev` folded into `ObsEv` from memory `m`. -/
noncomputable def handle (frame : Nat → Prop) (m : Mem) (t : Tree Ev Outcome) : OTree :=
  Effect.interp (memoryHandler frame) finishOutcome m t

/-- The handled tree of a budgeted run, from the run's initial memory. -/
noncomputable def runHandled (calls : Calls) (frame : Nat → Prop) (n : Nat)
    (f : Function) (s : State) : OTree :=
  handle frame s.mem (runT calls n f s)

/-! ### The handler's decisions

These are the equations the unfolding lemmas are applied with; each is a
`simp`-closable evaluation of the branch `memoryHandler` takes. -/

theorem memoryHandler_load_private {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {m : Mem} {v : Value} (hf : InFrame frame addr ty)
    (hv : loadValue m ty addr = some v) :
    memoryHandler frame m (Ev.load addr ty) = Sum.inl (some v, m) := by
  simp only [memoryHandler, hv, ite_eq_left hf]

theorem memoryHandler_load_visible {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {m : Mem} {v : Value} (hf : ¬ InFrame frame addr ty)
    (hv : loadValue m ty addr = some v) :
    memoryHandler frame m (Ev.load addr ty) =
      Sum.inr ⟨Unit, ObsEv.load addr ty (some v), fun () => (some v, m)⟩ := by
  simp only [memoryHandler, hv, ite_eq_right hf]

theorem memoryHandler_load_none {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {m : Mem} (hv : loadValue m ty addr = none) :
    memoryHandler frame m (Ev.load addr ty) =
      Sum.inr ⟨Unit, ObsEv.load addr ty none, fun () => (none, m)⟩ := by
  simp only [memoryHandler, hv]

theorem memoryHandler_store_private {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {v : Value} {m : Mem} (hf : InFrame frame addr ty) :
    memoryHandler frame m (Ev.store addr ty v) = Sum.inl ((), storeMem m ty v addr) := by
  simp only [memoryHandler, ite_eq_left hf]

theorem memoryHandler_store_visible {frame : Nat → Prop} {addr : Nat} {ty : Ty}
    {v : Value} {m : Mem} (hf : ¬ InFrame frame addr ty) :
    memoryHandler frame m (Ev.store addr ty v) =
      Sum.inr ⟨Unit, ObsEv.store addr ty v, fun () => ((), storeMem m ty v addr)⟩ := by
  simp only [memoryHandler, ite_eq_right hf]

theorem memoryHandler_call {frame : Nat → Prop} {callee : String} {args : List Value}
    {m : Mem} :
    memoryHandler frame m (Ev.call callee args) =
      Sum.inr ⟨Option Value, ObsEv.call callee args, fun r => (r, m)⟩ := rfl

theorem memoryHandler_ub {frame : Nat → Prop} {m : Mem} :
    memoryHandler frame m Ev.ub =
      Sum.inr ⟨Empty, ObsEv.ub, fun e => (Empty.elim e, m)⟩ := rfl

theorem memoryHandler_timeout {frame : Nat → Prop} {m : Mem} :
    memoryHandler frame m Ev.timeout =
      Sum.inr ⟨Empty, ObsEv.timeout, fun e => (Empty.elim e, m)⟩ := rfl

/-! ### Handling equations

Each is the generic unfolding equation applied at the host handler, so the
handler's branch is what selects the shape. -/

theorem handle_ret {frame : Nat → Prop} {m : Mem} {o : Outcome} :
    handle frame m (ret o) = ret (finishOutcome o m) :=
  Effect.interp_ret _ _ _ o

theorem handle_tau {frame : Nat → Prop} {m : Mem} {t : Tree Ev Outcome} :
    handle frame m (tau t) = tau (handle frame m t) :=
  Effect.interp_tau _ _ _ t

/-- A defined in-frame load is silent and leaves the memory alone. -/
theorem handle_load_private {frame : Nat → Prop} {addr : Nat} {ty : Ty} {m : Mem}
    {v : Value} {k : Option Value → Tree Ev Outcome} (hf : InFrame frame addr ty)
    (hv : loadValue m ty addr = some v) :
    handle frame m (vis (Ev.load addr ty) k) =
      tau (handle frame m (k (some v))) :=
  Effect.interp_vis_left _ _ _ _ _ _ _ (memoryHandler_load_private hf hv)

/-- An undefined in-frame load stays visible, annotated `none`, and the
continuation receives `none`. -/
theorem handle_load_none {frame : Nat → Prop} {addr : Nat} {ty : Ty} {m : Mem}
    {k : Option Value → Tree Ev Outcome} (hv : loadValue m ty addr = none) :
    handle frame m (vis (Ev.load addr ty) k) =
      vis (ObsEv.load addr ty none) (fun () => handle frame m (k none)) :=
  Effect.interp_vis_right _ _ _ _ _ _ _ (memoryHandler_load_none hv)

/-- A defined out-of-frame load is visible, annotated with the value the handler
computed from its own memory. -/
theorem handle_load_out {frame : Nat → Prop} {addr : Nat} {ty : Ty} {m : Mem}
    {v : Value} {k : Option Value → Tree Ev Outcome} (hf : ¬ InFrame frame addr ty)
    (hv : loadValue m ty addr = some v) :
    handle frame m (vis (Ev.load addr ty) k) =
      vis (ObsEv.load addr ty (some v)) (fun () => handle frame m (k (some v))) :=
  Effect.interp_vis_right _ _ _ _ _ _ _ (memoryHandler_load_visible hf hv)

/-- An in-frame store is silent and advances the handler's memory. -/
theorem handle_store_private {frame : Nat → Prop} {addr : Nat} {ty : Ty} {v : Value}
    {m : Mem} {k : Unit → Tree Ev Outcome} (hf : InFrame frame addr ty) :
    handle frame m (vis (Ev.store addr ty v) k) =
      tau (handle frame (storeMem m ty v addr) (k ())) :=
  Effect.interp_vis_left _ _ _ _ _ _ _ (memoryHandler_store_private hf)

/-- An out-of-frame store emits its address, type and value, and resumes after
the write. -/
theorem handle_store_visible {frame : Nat → Prop} {addr : Nat} {ty : Ty} {v : Value}
    {m : Mem} {k : Unit → Tree Ev Outcome} (hf : ¬ InFrame frame addr ty) :
    handle frame m (vis (Ev.store addr ty v) k) =
      vis (ObsEv.store addr ty v) (fun () => handle frame (storeMem m ty v addr) (k ())) :=
  Effect.interp_vis_right _ _ _ _ _ _ _ (memoryHandler_store_visible hf)

/-- A call is re-emitted and its response is passed to the source continuation
unchanged; the memory is untouched and no environment is consulted. -/
theorem handle_call {frame : Nat → Prop} {callee : String} {args : List Value} {m : Mem}
    {k : Option Value → Tree Ev Outcome} :
    handle frame m (vis (Ev.call callee args) k) =
      vis (ObsEv.call callee args) (fun r => handle frame m (k r)) :=
  Effect.interp_vis_right _ _ _ _ _ _ _ (memoryHandler_call (frame := frame) (m := m))

/-! ### The raw private steps

`RawSilentStep` is the *source-side* private step — a `tau`, a defined in-frame
load, or an in-frame store — kept only to transport the loop's finite derivation
through the handler.  It is not a second relation: `Simtt` proves that a raw
closure maps to a silent closure of the handled trees, and nothing else uses it.
-/

/-- A tree together with the memory its events read and write.  Raw-source
bookkeeping for the transport; not the relation's carrier. -/
abbrev RawTS := Tree Ev Outcome × Mem

/-- One private step of a raw source tree. -/
inductive RawSilentStep (frame : Nat → Prop) : RawTS → RawTS → Prop where
  | step (t : Tree Ev Outcome) (m : Mem) :
      RawSilentStep frame (tau t, m) (t, m)
  | load (addr : Nat) (ty : Ty) (k : Option Value → Tree Ev Outcome) (m : Mem)
      (v : Value) (hv : loadValue m ty addr = some v) (hf : InFrame frame addr ty) :
      RawSilentStep frame (vis (Ev.load addr ty) k, m) (k v, m)
  | store (addr : Nat) (ty : Ty) (v : Value) (k : Unit → Tree Ev Outcome) (m : Mem)
      (hf : InFrame frame addr ty) :
      RawSilentStep frame (vis (Ev.store addr ty v) k, m)
        (k (), storeMem m ty v addr)

/-- Finitely many raw private steps.  It is inductive, so it never witnesses
divergence. -/
def RawSilentHead (frame : Nat → Prop) : RawTS → RawTS → Prop :=
  Relation.ReflTransGen (RawSilentStep frame)

theorem RawSilentHead.refl (frame) (p : RawTS) : RawSilentHead frame p p :=
  Relation.ReflTransGen.refl

theorem RawSilentHead.trans {frame} {p q r : RawTS}
    (h1 : RawSilentHead frame p q) (h2 : RawSilentHead frame q r) : RawSilentHead frame p r :=
  Relation.ReflTransGen.trans h1 h2

theorem RawSilentHead.step {frame} {p q r : RawTS} (h1 : RawSilentStep frame p q)
    (h2 : RawSilentHead frame q r) : RawSilentHead frame p r :=
  Relation.ReflTransGen.head h1 h2

end LeanLLVM.ITree
