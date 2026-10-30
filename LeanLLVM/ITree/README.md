# `LeanLLVM.ITree`: interaction trees and a postcondition-indexed simulation

This directory is a second Lake library, `LeanLLVM.ITree`, built beside
`LeanLLVM`.  It carries the interaction-tree layer used to relate two programs
by their memory interactions rather than by whole-outcome equality.

## Dependency and import boundary

The tree carrier is mathlib's coinductive polynomial functor `PFunctor.M`.
The dependency is pinned in `lakefile.toml` at mathlib
`3dfb8e22b67042b31fac228dee0e1169a1a7820f`; the package builds at Lean
`v4.36.0-rc1`.

Exactly one module imports mathlib directly:

* `Internal/PFunctor.lean` — `Mathlib.Data.QPF.Univariate.Basic` and
  `Mathlib.Data.Vector3`, plus the `Vector3`/`PFunctor.M` utilities the tree
  encoding needs.

Every other module, here and in `LeanLLVM/`, reaches mathlib only through that
adapter.  `Internal/Basic.lean` defines the coinductive tree; `Internal/Paco.lean`
is the vendored parameterised-fixpoint layer; `Core.lean` is the public
constructor/observer surface; `Interpret.lean` interprets `LeanLLVM`'s fuel
semantics; `Simtt.lean` is the relation; `Bridge.lean` takes that relation to the
canonical resolution.

## Modules

* `Core.lean` — `Tree`, `ret`, `tau`, `vis`, `tauN`, `trigger`, `infTau`,
  constructor injectivity, the disjointness of `ret`/`tau`/`vis`, and the
  `dMatchOn` eliminator.  Clients name trees through this API and never spell
  out `PFunctor.M`/`MIntl`/`CofixA`.
* `Interpret.lean` — the `Ev` signature (`load`, `store`, `call`, `ub`,
  `timeout`), the fuel-indexed tree of a function (`runT`), and the canonical
  resolution relation `Exec` with the forward theorem `exec_runT`: every
  `runFuel` outcome is a leaf of the tree.  `ub` and `timeout` are distinct:
  `ub` is a completed semantic outcome, `timeout` a finite-budget artifact.
  `Simtt.lean` — the directed relation.  `simtt` is a directed simulation up
  to taus, where the silent steps are `tau` and private in-frame loads/stores;
  it is not the symmetric equivalence-up-to-taus relation of the ITree
  literature (`InteractionTrees`).  Left is the target, right the source.
  `SilentStep` is a `tau`, a defined in-frame load, or an in-frame store; for a
  load the memory must define the value, while a store's event is private as
  soon as its span is in the frame.  `SilentHead` is its inductive
  reflexive-transitive closure; `SilentDiverges` is the greatest fixed point of
  the silent step.  `SimttF` relates, after finite silent closure on both sides:
  `ret` leaves carrying defined outcomes through `post` — `post` sees only
  `.ret`-valued outcomes and never `ub`; `timeout` only to `timeout`; a left
  silent divergence as the bottom against a right side that cannot silently
  reach `timeout`; a right silent divergence only to a left one; and the same
  visible event with its response threaded into the continuations (stores
  advance both memories).  A visible load also requires that the two memories
  give the same canonical response, `loadValue m₁ ty addr = loadValue m₂ ty
  addr`: two equal values or two undefined loads are related, a defined answer
  against an undefined load is not.

  A UB terminal is either a `ret` leaf carrying `Outcome.ub` or a `vis Ev.ub`
  node (`UbTerminal`), and `ReachesUb` is the silent closure to one.  The two
  shapes are one class in both directions, so neither can slip past the
  left-UB rule through `post`: a left UB terminal is related only to a right
  UB terminal, while a right UB terminal admits any completed left return,
  defined or `ub`, without consulting `post`.

  `simtt` is Paco's parameterised least fixed point `plfp (SimttF frame post) top`
  of the one-step functional, with the reverse-implication order on
  propositions.  `simtt_eq_plfp` records the definition, `simtt_unfold` is
  Paco's `plfp_unfold` with the inert top assumption removed, and `simtt.coind`
  is Paco's `plfp_init` together with Park induction.  The finite-stutter
  lemmas, return inversion and the terminal mismatch rules are the rest of the
  public surface.
* `Bridge.lean` — the executable side of the relation.  `Exec_inv` and the
  shape-specific inversions read a canonical resolution's constructor off the
  tree, `Exec.silentStep`/`Exec.silentHead` commute a resolution through silent
  steps, and `simtt_exec_some` is the elimination: a *completed* target run
  (`some` outcome) is answered by the source either with undefined behaviour or
  with an actual return the postcondition accepts.  The budget-explicit
  `simtt_runFuel_some` and the quantified `simtt_beh_inclusion` specialise it to
  `runFuel` and `Beh`, with a separate budget on each side, and
  `refinesWithin_of_simtt`/`refines_of_simtt` are corollaries at the framed and
  exact posts.  This transport is one-directional, from target to source, and
  conditional on a tree relation being available for every completed target
  run; the module installs nothing and defines no relation of its own.
  `not_simtt_load_of_disagree` is the negative side of the load clause: a visible
  load whose two memories disagree is refused.
* `LoopInstance.lean` — the repository's concrete fixture: for every
  `x : BitVec 64`, the parsed loop as left target is related to the unrolled
  candidate as right source by
  `simtt (loopFrame x) (Outcome.AgreesOutside (loopFrame x))`
  on `(loopTree x, [])` and `(candidateTree x, [])`, where the postcondition
  compares the actual returned values and memories outside the band the loop's
  own allocations cover.  The proof walks the loop's own blocks and the
  candidate's single block; it is not a general loop rule, and the module
  installs nothing.  A returned memory that differs at address `0` is rejected
  by the same postcondition.  `loop_candidate_beh_bridge` is the one behaviour
  statement derived from the bridge for this pair: budget uniqueness pins the
  loop's outcome to its 19-step return, the fixed 19/10000 tree relation
  transports it, and the result is a candidate behaviour agreeing outside the
  band.  It covers `x : BitVec 64` only and says nothing about arbitrary
  argument lists or other loops.

## Provenance and deviations

The tree core is adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b`:

* `Internal/PFunctor.lean` adapts `ITree/Utils.lean`;
* `Internal/Basic.lean` adapts `ITree/Basic.lean`;
* `Internal/Paco.lean` is the upstream `Paco/PacoDefs.lean` vendored whole
  (its `plfp`/`uplfp` definitions, unfolding/accumulator lemmas and tactics).

The upstream MIT licence is reproduced in `LICENSE`.  Local deviations:

* the upstream exact-equality relation `IEq`, its `IEqF` functional and the
  library's monad/effect-algebra instances are not vendored; this library
  needs the tree constructors, destructors and coinductive fixpoints only;
* names are placed under `LeanLLVM.ITree` (`Shape`, `P`, `ITree`) and the
  imports are the single adapter above rather than `Mathlib` in each file;
* `ret`/`tau`/`vis` constructor disjointness, the `Ev` signature, the
  interpretation, `Exec`, the relation and its instance are new here.

The read-only VeLLVM reference subtree under `reference/vellvm/` is a separate
thing and is not this library.
