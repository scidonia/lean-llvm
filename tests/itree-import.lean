/-
The public surface of the generic library: a client imports `ITree` only.

This file declares its own event signature and its own handler, so it is a check
that the public entrypoint is self-sufficient: the constructors, the one-step
interpreter and its unfolding equations, and the coinduction layer are all
reachable without importing an `Internal` module and without importing anything
from the LLVM instantiation.

Elaborated by `lake env lean tests/itree-import.lean`.
-/
import ITree

namespace ITreeImportCheck

open ITree

/-- A two-event signature, declared here rather than taken from an instance. -/
inductive Tick : Type → Type where
  /-- An observable poke. -/
  | unit : Tick Unit
  /-- A silent question. -/
  | ask : Tick Nat

/-! ### The one-step interpreter

`ask` is answered privately, so it becomes a silent step; `unit` is re-emitted
with its response mapped back into the source continuation. -/
def handler : Effect.Handler Tick Tick Nat :=
  fun {_} m e =>
    match e with
    | Tick.unit => Sum.inr ⟨Unit, Tick.unit, fun () => ((), m + 1)⟩
    | Tick.ask => Sum.inl (m, m + 1)

/-- A tree with both events. -/
def sample : ITree.Tree Tick Nat :=
  ITree.vis Tick.ask (fun n => ITree.tau (ITree.vis Tick.unit (fun _ => ITree.ret (n + 1))))

/-- The interpreted tree. -/
def interpreted : ITree.Tree Tick Nat :=
  Effect.interp handler (fun r _ => r) 0 sample

/-- A returned leaf is finished with the handler's state. -/
example : Effect.interp handler (fun (r : Nat) (m : Nat) => r + m) 7 (ITree.ret 3) =
    ITree.ret 10 := by
  rw [Effect.interp_ret]

/-- A source `tau` stays a `tau`. -/
example (t : ITree.Tree Tick Nat) :
    Effect.interp handler (fun r _ => r) 0 (ITree.tau t) =
      ITree.tau (Effect.interp handler (fun r _ => r) 0 t) :=
  Effect.interp_tau _ _ _ t

/-- A privately answered event is silent, and the state advances. -/
example : Effect.interp handler (fun r _ => r) 0 (ITree.vis Tick.ask (fun n => ITree.ret n)) =
    ITree.tau (ITree.ret 0) := by
  rw [Effect.interp_vis_left handler (fun r _ => r) 0 Tick.ask (fun n => ITree.ret n) 0 1 rfl]
  rw [Effect.interp_ret]

/-- A re-emitted event is observable, its response is mapped back into the
source continuation, and the continuation starts from the new state. -/
example : Effect.interp handler (fun r _ => r) 3 (ITree.vis Tick.unit (fun _ => ITree.ret 9)) =
    ITree.vis Tick.unit (fun () => ITree.ret 9) := by
  rw [Effect.interp_vis_right handler (fun r _ => r) 3 Tick.unit (fun _ => ITree.ret 9)
    Tick.unit (fun () => ((), 4)) rfl]
  rw [Effect.interp_ret]

/-! ### The public tree API -/

/-- `tauN` and `trigger` are part of the public surface. -/
example : (ITree.tauN 2 (ITree.ret 5) : ITree.Tree Tick Nat) =
    ITree.tau (ITree.tau (ITree.ret 5)) := rfl

example : (ITree.trigger Tick.ask : ITree.Tree Tick Nat) =
    ITree.vis Tick.ask (fun n => ITree.ret n) := rfl

/-- The constructors are distinguishable, which is what the relation's terminal
cases use. -/
example : (ITree.ret 5 : ITree.Tree Tick Nat) ≠ ITree.tau (ITree.ret 5) :=
  ITree.ret_ne_tau

/-- `infTau` unfolds to a `tau` of itself. -/
example : (ITree.infTau : ITree.Tree Tick Nat) = ITree.tau ITree.infTau :=
  ITree.infTau_eq

/-! ### The coinduction layer -/

#check @plfp
#check @uplfp
#check @plfp_unfold
#check @plfp_acc

end ITreeImportCheck
