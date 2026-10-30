# `ITree`: a generic interaction-tree library

This library is the generic interaction-tree layer of the package, built as its
own Lake library target (`ITree`) beside `LeanLLVM`.  It knows nothing about
LLVM: no module here imports a `LeanLLVM` module, directly or through another
module of this library.

The LLVM instantiation — a memory-effect handler over the host semantics, a
directed relation on the resulting trees and a loop/candidate instance — lives
in `LeanLLVM/ITree/` and is recorded in that directory's README.

## Public surface

Public clients import `ITree` (or the two modules they need):

| Module | Contents |
| --- | --- |
| `ITree/Core.lean` | the tree type `Tree`, the constructors `ret`, `tau`, `vis`, `tauN`, `trigger`, `infTau`, their injectivity and disjointness, and the `dMatchOn` eliminator |
| `ITree/Effect.lean` | the one-step `Handler` and its computable interpreter `interp`, with `interp_ret`, `interp_tau` and the two handler-conditional event equations |
| `ITree/Coinduction.lean` | the parameterised-fixpoint layer (`plfp`, `uplfp`, `plfp_unfold`, `plfp_acc` and its tactics), the same source the branch relation is built on |

`ITree/Internal/{PFunctor,Basic}.lean` are **unsupported implementation modules
by convention**, not by access control: Lean's namespaces are open, so a client
can still reach their declarations transitively.  Import `ITree`,
`ITree.Core` or `ITree.Coinduction`; do not import an `Internal` module and do
not name `PFunctor.M` in a client.

## Import boundary

Exactly one module imports mathlib directly:

* `ITree/Internal/PFunctor.lean` — `Mathlib.Data.QPF.Univariate.Basic` and
  `Mathlib.Data.Vector3`, plus the `Vector3`/`Fin2` helpers the encoding needs.

Every other module in the package, generic or host, reaches mathlib through it.
No generic module imports anything outside `ITree.*`, `Mathlib.*` (only the
adapter) and Lean's own core libraries.  `tests/itree-boundary.sh` checks those
claims against the actual `import` declarations, with a positive control on the
same detector before each absence claim; `tests/itree-import.lean` elaborates a
client that imports `ITree` only.

All libraries live in this one root package: this is a separate Lake *library
target*, not a separate package, and the mathlib pin, `lean-toolchain` and the
flake remain shared.

## The one-step handler

```lean
abbrev Handler (ε δ : Type → Type) (σ : Type) :=
  ∀ {α}, σ → ε α → Sum (α × σ) (Σ β, δ β × (β → α × σ))

def interp (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) (t : Tree ε ρ) : Tree δ γ
```

For one source event the handler either answers privately — a left branch,
performed as a silent step, with the state advanced — or re-emits exactly one
observable event whose response is mapped back to a source response and a state.
A source `tau` stays a `tau`, and a returned `r` becomes `ret (finish r m)`, so
the handler's final state reaches the leaves.

Two limits belong to this API:

* the handler is **one step**: one source event produces either silence or one
  observable event, never a tree of them;
* this is **not** upstream `lean4-itree`'s `EffectAlgebra.interp`, which is
  monadic and needs the `Monad`, `IEq` and effect-algebra instances this port
  does not vendor.  A tree-valued handler — one that emits several effects for a
  single source event — would have to run its own tree against the source
  continuation, which needs `bind` on `Tree ε` with lawful `Functor` and
  `Monad` (and `MonadIter`) instances, plus the congruence relation `IEq` and
  its compatibility lemmas; the one-step `Handler` below cannot express it.
  None of those instances are present, so the fold stays one-step and no
  partial `Monad` instance is given here.

`interp` itself is computable: the whole decision is the handler's, and the
iteration is `PFunctor.M.corec'` over the source's destructor.  A handler that
needs a decision the kernel cannot compute — an arbitrary `Prop`-valued frame,
say — is noncomputable at the handler, not at the library.

## Provenance and deviations

The tree core is adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b`:

* `ITree/Internal/PFunctor.lean` adapts `ITree/Utils.lean`;
* `ITree/Internal/Basic.lean` adapts `ITree/Basic.lean`;
* `ITree/Coinduction.lean` is the upstream `Paco/PacoDefs.lean` vendored whole
  (its `plfp`/`uplfp` definitions, unfolding and accumulator lemmas, and
  tactics).

The upstream MIT licence is reproduced in `ITree/LICENSE`.  Local deviations:

* the upstream exact-equality relation `IEq`, its `IEqF` functional and the
  library's monad/effect-algebra instances are not vendored; `IEq` is a
  congruence relation the current developments do not need, and the instances
  would have to be lawful and complete to be worth adding;
* `Handler` and `interp` are new here, and are the one-step, computable fold
  described above rather than upstream's monadic interpreter;
* declarations are placed under the `ITree` namespace, and the mathlib
  dependency is funnelled through the single adapter.

The read-only VeLLVM reference subtree under `reference/vellvm/` is unrelated to
this library.
