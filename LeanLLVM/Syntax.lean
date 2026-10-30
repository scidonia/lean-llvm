/-
The internal IR: instructions, terminators, basic blocks, functions and modules.

This is the form the semantics and the certified passes work on.  It is
deliberately smaller than the textual LLVM grammar.  The parser refuses what it
knows it does not model rather than approximating it: instructions, block
structure, and a function definition's return attribute before the return type
and function attribute after the parameter list are all checked, so a `Function`
that reaches the driver has a defined meaning.  A `declare` header is not
checked for attributes yet, so attributes on a declaration are outside that
guarantee.
-/
import LeanLLVM.Basic

namespace LeanLLVM

/-- A non-terminating instruction. -/
inductive Instr where
  | binop (dst : String) (op : BinOp) (w : Nat) (lhs rhs : Operand)
  | icmp (dst : String) (pred : IPred) (w : Nat) (lhs rhs : Operand)
  | select (dst : String) (ty : Ty) (cond lhs rhs : Operand)
  | trunc (dst : String) (wIn wOut : Nat) (v : Operand)
  | zext (dst : String) (wIn wOut : Nat) (v : Operand)
  | sext (dst : String) (wIn wOut : Nat) (v : Operand)
  | alloca (dst : String) (ty : Ty) (align : Nat)
  | load (dst : String) (ty : Ty) (ptr : Operand)
  | store (ty : Ty) (val ptr : Operand)
  /-- A call instruction.  The result is bound to `dst` as `retTy`; the callee
  is resolved by the semantics' call environment, not by the function itself. -/
  | call (dst : String) (retTy : Ty) (callee : String) (args : List (Ty × Operand))
  deriving DecidableEq, Repr

/-- The register an instruction defines, if any. -/
def Instr.dst? : Instr → Option String
  | .binop d _ _ _ _ => some d
  | .icmp d _ _ _ _ => some d
  | .select d _ _ _ _ => some d
  | .trunc d _ _ _ => some d
  | .zext d _ _ _ => some d
  | .sext d _ _ _ => some d
  | .alloca d _ _ => some d
  | .load d _ _ => some d
  | .store _ _ _ => none
  | .call d _ _ _ => some d

/-- Registers read by an instruction. -/
def Instr.uses : Instr → List String
  | .binop _ _ _ a b => a.regs ++ b.regs
  | .icmp _ _ _ a b => a.regs ++ b.regs
  | .select _ _ c a b => c.regs ++ a.regs ++ b.regs
  | .trunc _ _ _ v => v.regs
  | .zext _ _ _ v => v.regs
  | .sext _ _ _ v => v.regs
  | .alloca _ _ _ => []
  | .load _ _ p => p.regs
  | .store _ v p => v.regs ++ p.regs
  | .call _ _ _ args => (args.map (·.2.regs)).flatten

/-- Instructions with no memory effect.  `alloca` moves the allocation pointer
and `store` writes memory; both stay out of the pure set.  A `load` reads
memory but has no effect, so it is pure in this sense as well. -/
def Instr.isPure : Instr → Bool
  | .binop .. => true
  | .icmp .. => true
  | .select .. => true
  | .trunc .. => true
  | .zext .. => true
  | .sext .. => true
  | .alloca .. => false
  | .load .. => true
  | .store .. => false
  | .call .. => false

/-- A terminator.  `ret void` carries `none`. -/
inductive Term where
  | ret (ty : Ty) (v : Option Operand)
  | br (dest : String)
  | condbr (cond : Operand) (thenBlock elseBlock : String)
  | unreachable
  deriving DecidableEq, Repr

/-- Registers read by a terminator. -/
def Term.uses : Term → List String
  | .ret _ (some v) => v.regs
  | .ret _ none => []
  | .br _ => []
  | .condbr c _ _ => c.regs
  | .unreachable => []

/-- Successor block names. -/
def Term.targets : Term → List String
  | .ret .. => []
  | .br d => [d]
  | .condbr _ t f => [t, f]
  | .unreachable => []

/-- A basic block. -/
structure Block where
  name : String
  instrs : List Instr
  term : Term
  deriving DecidableEq, Repr

/-- A function definition.  The entry block is the first block of `blocks`. -/
structure Function where
  name : String
  retTy : Ty
  params : List (String × Ty)
  blocks : List Block
  deriving DecidableEq, Repr

/-- An external declaration: a symbol the module calls but does not define. -/
structure Decl where
  name : String
  retTy : Ty
  params : List Ty
  deriving DecidableEq, Repr

/-- A module: declarations followed by function definitions.  Declarations are not modelled
yet; the parser refuses a module that calls a function, so a declaration would
be unreachable. -/
structure Module where
  decls : List Decl
  functions : List Function
  deriving DecidableEq, Repr

/-- The entry block, when the function has one. -/
def Function.entry? (f : Function) : Option String :=
  f.blocks.head?.map (·.name)

/-- Find a block by name in a block list. -/
def findBlockList : List Block → String → Option Block
  | [], _ => none
  | b :: bs, name => if b.name = name then some b else findBlockList bs name

/-- Find a block by name. -/
def Function.findBlock (f : Function) (name : String) : Option Block :=
  findBlockList f.blocks name

/-- Every register read anywhere in the function. -/
def Function.usedNames (f : Function) : List String :=
  f.blocks.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses

/-- Every register defined anywhere in the function. -/
def Function.definedNames (f : Function) : List String :=
  f.blocks.flatMap fun b => b.instrs.filterMap Instr.dst?

/-- Block names in definition order. -/
def Function.blockNames (f : Function) : List String :=
  f.blocks.map (·.name)

/-- A cheap structural well-formedness condition: block names are unique and
every branch target is a defined block.  The parser produces functions that
satisfy it; passes preserve it. -/
def Function.wf (f : Function) : Bool :=
  let names := f.blockNames
  let nodup := names.eraseDups.length == names.length
  let targetsOk := f.blocks.all fun b =>
    b.term.targets.all fun t => names.contains t
  nodup && targetsOk && !names.isEmpty

end LeanLLVM
