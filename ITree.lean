/-
The interaction-tree library.

`ITree.Core` is the tree API (constructors, observers and the destructor-based
eliminator); `ITree.Effect` is a one-step event handler and its computable
interpreter; `ITree.Coinduction` is the parameterised-fixpoint layer the branch
relation is built on.  `ITree/Internal/{PFunctor,Basic}.lean` are implementation
modules by convention: public clients import `ITree` (or `ITree.Core` and
`ITree.Coinduction`), never an `Internal` module.

The library has no dependency on the LLVM instantiation: no `ITree` or
`ITree/**.lean` module imports a `LeanLLVM` module.  `ITree/README.md` records
the import boundary, the one-step limit of `Effect.interp` and the upstream
provenance.
-/
import ITree.Core
import ITree.Effect
import ITree.Coinduction
