/-
The interaction-tree library boundary.

`Core` is the tree API, `Interpret` the fuel-semantics interpretation, `Eutt`
the postcondition-indexed directed simulation on Paco's parameterised least
fixed point, and `LoopInstance` the repository's concrete loop/candidate
instance and its addressing counterexample.
-/
import LeanLLVM.ITree.Core
import LeanLLVM.ITree.Interpret
import LeanLLVM.ITree.Eutt
import LeanLLVM.ITree.LoopInstance
