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
  /-- A pointer offset: `getelementptr [inbounds] i8, ptr %base, iN %off`.  The
  element type is `i8`, so the index is a byte count and the result is a `ptr`.
  The index's own width is not a field: the semantics sign-extends whatever
  integer value it reads to 64 bits, so an `iN` in the text is a shape the
  parser checks, not state the instruction keeps.  `inbounds` is not a field
  either — the printer emits it and no semantics here reads it. -/
  | gep (dst : String) (base : Operand) (off : Operand)
  /-- A lane-wise integer comparison: each lane of the result is the predicate's
  one-bit result on the two operands' lane at that position.  The lane count and
  width are the operands' vector type, `<n x iw>`. -/
  | icmpVec (dst : String) (pred : IPred) (n w : Nat) (lhs rhs : Operand)
  /-- A lane-wise binary integer operation on vectors of `<n x iw>`. -/
  | binopVec (dst : String) (op : BinOp) (n w : Nat) (lhs rhs : Operand)
  /-- Pack a `<n x i1>` mask into an `n`-bit integer, lane `k` to bit `k`. -/
  | bitcastMask (dst : String) (n : Nat) (v : Operand)
  /-- A call instruction.  The result is bound to `dst` as `retTy`; the callee
  is resolved by the semantics' call environment, not by the function itself. -/
  | call (dst : String) (retTy : Ty) (callee : String) (args : List (Ty × Operand))
  /-- A call whose result has no name in the caller: `call void @f(...)`.  It
  binds nothing, so there is no destination and no name a later instruction could
  read, and it has no return type field because the only accepted form returns
  `void` — the parser refuses a discarded non-`void` result rather than print it
  back as a `void` call.  Its effect is the call environment's: the value the
  callee leaves is discarded, its memory and allocator state are adopted. -/
  | callVoid (callee : String) (args : List (Ty × Operand))
  /-- A `phi`: one incoming value per predecessor block, selected at entry by the
  block the edge came from.  The type is the instruction's result type, which
  LLVM's text requires because an incoming value carries none; the parser refuses
  an incoming operand whose type disagrees with it, and the semantics does not
  consult it — the selected operand evaluates to its own value, exactly as
  `select`'s result type is not consulted.  The predecessor is read from
  `State.pre`, which only a jump writes. -/
  | phi (dst : String) (ty : Ty) (incoming : List (String × Operand))
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
  | .gep d _ _ => some d
  | .icmpVec d _ _ _ _ _ => some d
  | .binopVec d _ _ _ _ _ => some d
  | .bitcastMask d _ _ => some d
  | .call d _ _ _ => some d
  | .callVoid _ _ => none
  | .phi d _ _ => some d

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
  | .gep _ base off => base.regs ++ off.regs
  | .icmpVec _ _ _ _ a b => a.regs ++ b.regs
  | .binopVec _ _ _ _ a b => a.regs ++ b.regs
  | .bitcastMask _ _ v => v.regs
  | .call _ _ _ args => (args.map (·.2.regs)).flatten
  | .callVoid _ args => (args.map (·.2.regs)).flatten
  | .phi _ _ incoming => (incoming.map (fun kv => kv.2.regs)).flatten

/-- Instructions with no memory effect.  `alloca` moves the allocation pointer
and `store` writes memory; both stay out of the pure set.  A `load` reads
memory but has no effect, so it is pure in this sense as well.  A `phi` reads
the predecessor field of the state and no memory, so it is pure here too. -/
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
  | .gep .. => true
  | .icmpVec .. => true
  | .binopVec .. => true
  | .bitcastMask .. => true
  | .call .. => false
  | .callVoid .. => false
  | .phi .. => true

/-- Whether an instruction is a `phi`, the one constructor that reads the
state's predecessor field.  The non-interference theorem is stated for functions
in which no instruction is a `phi`. -/
def Instr.isPhi : Instr → Bool
  | .phi .. => true
  | _ => false

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

/-- A module: declarations followed by function definitions.  A `declare` line is
parsed into `decls`, and a `call` instruction names its callee as a symbol that
the environment resolves, not one the module defines — so declarations are
modelled, and the JSON caller fixture's pin compares them. -/
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

/-- A block found by name is a block of the function. -/
theorem findBlockList_mem {bs : List Block} {n : String} {b : Block}
    (h : findBlockList bs n = some b) : b ∈ bs := by
  induction bs with
  | nil => simp [findBlockList] at h
  | cons b' rest ih =>
      simp only [findBlockList] at h
      split at h
      · cases h
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- Every register read anywhere in the function. -/
def Function.usedNames (f : Function) : List String :=
  f.blocks.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses

/-- Every register defined anywhere in the function. -/
def Function.definedNames (f : Function) : List String :=
  f.blocks.flatMap fun b => b.instrs.filterMap Instr.dst?

/-- Block names in definition order. -/
def Function.blockNames (f : Function) : List String :=
  f.blocks.map (·.name)

/-- The incoming operand a `phi` selects for the block `p`: the entry whose label
is `p`, searched in list order.  `none` means the incoming list has no entry for
that predecessor, which the step transition reads as undefined behaviour. -/
def phiIncoming (p : String) : List (String × Operand) → Option Operand
  | [] => none
  | (l, op) :: rest => if l = p then some op else phiIncoming p rest

/-- Rewriting the operands of an incoming list rewrites the operand the selector
returns, any predecessor and any list.  The labels are untouched, so selection
is unaffected. -/
theorem phiIncoming_map (p : String) (inc : List (String × Operand))
    (f : Operand → Operand) :
    phiIncoming p (inc.map fun kv => (kv.1, f kv.2)) = (phiIncoming p inc).map f := by
  induction inc with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨l, op⟩ := kv
      by_cases h : l = p <;> simp [phiIncoming, h, ih]

/-- A function in which no block holds a `phi`.  The predicate the
non-interference theorem is stated at. -/
def Function.phiFree (f : Function) : Bool :=
  f.blocks.all fun b => b.instrs.all fun i => !i.isPhi

/-- A `phi`-free function's blocks hold no `phi`: the form the instruction-level
proofs consume. -/
theorem Function.phiFree_block {f : Function} (h : f.phiFree = true) {b : Block}
    (hb : b ∈ f.blocks) : ∀ i ∈ b.instrs, i.isPhi = false := by
  have h' : ∀ (x : Block), x ∈ f.blocks → ∀ i ∈ x.instrs, i.isPhi = false := by
    simpa [Function.phiFree] using h
  exact h' b hb


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
