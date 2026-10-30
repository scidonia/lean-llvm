/-
The interaction-tree library boundary.

`Core` is the tree API, `Interpret` the fuel-semantics interpretation, `Eutt`
the postcondition-indexed directed simulation on Paco's parameterised least
fixed point, `Bridge` the elimination of that relation against a completed run
and its fuel- and behaviour-level consequences, and `LoopInstance` the
repository's concrete loop/candidate instance, its behaviour corollary and its
addressing counterexample.
-/
import LeanLLVM.ITree.Core
import LeanLLVM.ITree.Interpret
import LeanLLVM.ITree.Eutt
import LeanLLVM.ITree.Bridge
import LeanLLVM.ITree.LoopInstance
