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
| `ITree/Coinduction.lean` | the parameterised-fixpoint layer (`plfp`, `uplfp`, `plfp_unfold`, `plfp_acc` and its tactics), the same source the branch relation is built on |
| `ITree/IEq.lean` | the exact-equality relation `IEq`/`IEqF`, `ieq_iff_eq` identifying it with strict equality, its equivalence, and the reflexivity lemma the law proofs close on |
| `ITree/Monad.lean` | `map` and `bind` with lawful `Functor`/`Monad` instances (`LawfulFunctor`, all seven `LawfulMonad` fields) at strict equality, plus `map`/`bind` compatibility with `IEq` |
| `ITree/TauClosure.lean` | the first-class delay `TauClosure`: `now`/`later`/`forever`, inductive `Finite`, coinductive `Infinite`, their disjointness `Finite.not_infinite`, the positive guard `FiniteLater`, guarded `flatten` into a tree, result transport along `map`, and the `tauN` tower lemmas that move both principles and `flatten` across further `later`s |
| `ITree/MonadIter.lean` | the ported monadic iterator: `IterState`, `MonadIter`, `iter`, `bindStep`, its five exact equations and the `FiniteLater` witnesses of the initial and `.recur` transitions |
| `ITree/EffectAlgebra.lean` | the tree-valued `Handler` and its directly guarded interpreter `interp`, with the five exact ret/tau/vis/bind/composition laws, handler composition and the transition guards |
| `ITree/Effect.lean` | the **other** interpreter: the one-step `Handler` and its computable `interp`, with `interp_ret`, `interp_tau` and the two handler-conditional event equations |

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

## Two interpreters

There are two interpreters in this library, and they are deliberately different
functions.

`ITree.EffectAlgebra.interp` is the compositional one.  A tree-valued handler
`Handler ε δ = ∀ {α}, ε α → Tree δ α` answers one source event with a tree of
target events, and the interpreter runs that tree against the source
continuation by directly guarded coiteration over two seed modes (source tree,
and handler tree with the source continuation).  Its exact laws, at strict tree
equality, are

```lean
interp h (ret r)      = ret r
interp h (tau t)      = tau (interp h t)
interp h (vis e k)    = bind (h e) (fun a => tau (interp h (k a)))
interp h (bind t f)   = bind (interp h t) (fun a => interp h (f a))
interp g (interp h t) = interp (comp h g) t
```

A return is not delayed, a source `tau` is emitted once, and a handled event
costs exactly one completion `tau`.  An identity-trigger handler is therefore
**not** the identity tree, and no such law is claimed.  This is intentionally
not pinned upstream's `EffectAlgebra.interp`, which routes through `iter` and
emits an initial `tau` even for a return; see the deviations below.

`ITree.Effect.interp` is the host-facing one-step fold: one source event becomes
either silence or exactly one observable event, and the handler's final state
reaches the leaves.  It remains computable and is what `LeanLLVM/ITree/` uses.

The recursive-fixpoint operation `mfix` is **not** part of this library.  A later
general loop rule will have to supply a positive `TauClosure.FiniteLater`
witness for each recursive backedge — the same guard the iterator and the
interpreter expose — rather than an arbitrary recursive tree.

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
  observable event, never a tree of them — a tree-valued handler is
  `ITree.EffectAlgebra.Handler`, above;
* it is the computable, state-threading fold, not the monadic interpreter.

`interp` itself is computable: the whole decision is the handler's, and the
iteration is `PFunctor.M.corec'` over the source's destructor.  A handler that
needs a decision the kernel cannot compute — an arbitrary `Prop`-valued frame,
say — is noncomputable at the handler, not at the library.

## Axiom footprint

The generic carrier's floor is `[propext, Classical.choice, Quot.sound]`, and
it comes from mathlib rather than from this library: `PFunctor.M`'s destructors
(`dest`/`children`) already depend on those axioms at this revision, so every
statement whose proof reaches the tree destructor carries them — including
`ITree.dest_ret`, an `rfl` lemma already present in the base revision.  No
generic proof introduces a classical decision of its own, so no theorem here
adds a fourth axiom.  The delay's constructor-level lemmas are narrower:
`TauClosure.finite_now`, `finite_later`, `FiniteLater.finite`,
`finiteLater_later` and `finite_tauN` are `[propext]` only, as are `IEqF_inv`
and `IEqF_monotone`.  Per-theorem pins, including those narrower cases, are in
`tests/itree-import.lean`, which elaborates a client that imports `ITree` alone.
The host handler's `Classical.propDecidable` frame decision belongs to
`LeanLLVM/ITree/`; it is host-side and not part of this floor.

## Provenance and deviations

The tree core is adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b`:

* `ITree/Internal/PFunctor.lean` adapts `ITree/Utils.lean`;
* `ITree/Internal/Basic.lean` adapts `ITree/Basic.lean`;
* `ITree/Coinduction.lean` is the upstream `Paco/PacoDefs.lean` vendored whole
  (its `plfp`/`uplfp` definitions, unfolding and accumulator lemmas, and
  tactics).

The upstream MIT licence is reproduced in `ITree/LICENSE`.  Local deviations:

* `ITree/IEq.lean` and `ITree/Monad.lean` adapt upstream's `IEqF`/`IEq`,
  `ieq_iff_eq` and its monad instances; upstream's `MonadIter` and `iter` are
  adapted in `ITree/MonadIter.lean`, namespaced under `ITree` and with the
  unused `Add`/`Coe` instances and `StateT` lifting omitted;
* `TauClosure`, `EffectAlgebra` (its two seed modes, `interp` and the five laws)
  and the delay witnesses are **not** ports: pinned upstream has no delay object,
  its finite closure is `Relation.ReflTransGen`, its divergence a coinductive
  predicate, and its monadic `interp` is the `iter`-based one described above;
* `ITree.Effect.Handler` and its `interp` are new here, and are the one-step,
  computable fold described above rather than upstream's monadic interpreter;
* declarations are placed under the `ITree` namespace, and the mathlib
  dependency is funnelled through the single adapter.

The read-only VeLLVM reference subtree under `reference/vellvm/` is unrelated to
this library.
