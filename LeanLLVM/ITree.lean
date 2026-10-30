/-
The interaction-tree layer of this repository.

`Interpret` is the interpretation of the fuel semantics as an `Ev` tree;
`MemoryEffect` folds `Ev` through the memory handler, so memory becomes an
effect and the handled tree is a bare `ObsEv` tree; `Simtt` is the
postcondition-indexed directed relation on those bare trees; `Bridge` is the
elimination of that relation against a completed run, together with the
correspondence that makes `runHandled` executable; `LoopInstance` is the
repository's concrete loop/candidate instance, its behaviour corollary and its
addressing counterexample.

The generic tree library is the separate `ITree` library (`ITree.lean`), which
has no dependency on any module here.
-/
import ITree
import LeanLLVM.ITree.Interpret
import LeanLLVM.ITree.MemoryEffect
import LeanLLVM.ITree.Simtt
import LeanLLVM.ITree.Bridge
import LeanLLVM.ITree.LoopInstance
