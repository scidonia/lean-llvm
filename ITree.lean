/-
The interaction-tree library.

`ITree.Core` is the tree API (constructors, observers and the destructor-based
eliminator); `ITree.Coinduction` is the parameterised-fixpoint layer; `IEq` is
exact tree equality and `Monad` its lawful `Functor`/`Monad` instances;
`TauClosure` is the finite/infinite silent-delay object its recursive guards are
witnessed by; `MonadIter` is the ported monadic iterator; `EffectAlgebra` is the
tree-valued handler and its directly guarded interpreter; `ITree.Effect` is the
host's computable one-step handler and fold.

`ITree/Internal/{PFunctor,Basic}.lean` are implementation modules by convention:
public clients import `ITree` (or `ITree.Core`, `ITree.Coinduction`, `ITree.IEq`,
`ITree.Monad`, `ITree.TauClosure`, `ITree.MonadIter` and `ITree.EffectAlgebra`),
never an `Internal` module.

The library has no dependency on the LLVM instantiation: no `ITree` or
`ITree/**.lean` module imports a `LeanLLVM` module.  `ITree/README.md` records
the import boundary, the two interpreters, the upstream provenance and the
still-open recursive-fixpoint obligation.
-/
import ITree.Core
import ITree.Coinduction
import ITree.IEq
import ITree.Monad
import ITree.TauClosure
import ITree.MonadIter
import ITree.EffectAlgebra
import ITree.Effect
