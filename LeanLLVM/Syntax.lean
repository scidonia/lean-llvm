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
  /-- A pointer comparison: the operands' addresses are compared as unsigned
  naturals.  It is a separate constructor from `icmp` because a pointer has no
  integer width; the signed order is defined by LLVM over its 64-bit pointer but
  is not representable over this model's unbounded `Nat` address, and the
  semantics refuses one (see `evalICmpPtr`).  The operand type is not a field:
  every accepted operand is a pointer, which the parser checks against the
  function's register types, so the printer emits `ptr`. -/
  | icmpPtr (dst : String) (pred : IPred) (lhs rhs : Operand)
  /-- A selection.  Two forms share this constructor, distinguished by the
  result type `ty` and by the condition's value:

  * a scalar select, `select i1 %c, iw %a, iw %b`, takes a whole value from
    one operand and has `ty` a scalar type;
  * a vector select, `select <n x i1> %c, <n x iw> %a, <n x iw> %b`, takes
    **lane `j`** from `a` when the condition's lane `j` is set and from `b`
    when it is clear, and has `ty` the operand type `<n x iw>`.  The condition's
    type is not a field: it is `<n x i1>` whenever `ty` is a vector, which is
    what the printer emits and what the parser checks.  LLVM's `select` on a
    vector condition is vectorised — element-wise by construction — not a
    uniform test of the whole mask, so there is no all-lanes reading here.

  The element type of a vector operand is an integer lane width, because that
  is the only vector element type `Value` carries; a `ty` of any other shape has
  no vector reading and the semantics refuses it. -/
  | select (dst : String) (ty : Ty) (cond lhs rhs : Operand)
  | trunc (dst : String) (wIn wOut : Nat) (v : Operand)
  | zext (dst : String) (wIn wOut : Nat) (v : Operand)
  | sext (dst : String) (wIn wOut : Nat) (v : Operand)
  | alloca (dst : String) (ty : Ty) (align : Nat)
  | load (dst : String) (ty : Ty) (ptr : Operand)
  /-- A memory write of a scalar or a vector of integer lanes.  A vector value is
  written as its lanes packed little-endian, lane `k` to bits
  `[k * w, (k + 1) * w)` and `n * w / 8` bytes in all, so the admitted widths are
  exactly those whose total width is a whole number of bytes; a `<n x i1>` mask
  store is that rule at `w = 1`, not a rule of its own.  A vector whose total
  width is not a whole number of bytes has no byte layout and is refused by name.
  The parser also checks a value operand that the function defines against the
  written type, because the operand grammar reads a register without consulting
  its type; an undefined register has no type and stays accepted, and the
  semantics' type-mismatch arm is the hand-built-AST case. -/
  | store (ty : Ty) (val ptr : Operand)
  /-- A pointer offset: `getelementptr [inbounds] <elemTy>, ptr %base, iN %off`.
  The element type is a field, because the step scales the index by the element
  type's size: an `i32` element type adds `4 * off` bytes and an `i8` element
  type adds `off`, which is the byte count the earlier form expressed.  The
  parser admits exactly the element types `Ty.gepElemAdmitted` names below — the
  seven integer widths, and a vector of integer lanes whose lane width is a
  whole number of bytes and whose packed size is a power of two (`w % 8 = 0` and
  `n * w / 8` a power of two, hence at least 1) — and refuses
  the rest by name; the field itself is any `Ty`, and the step reads its
  `sizeBytes`.  A vector element type is admitted because it keeps the byte
  offset of a packed row (`<8 x i32>`, 32 bytes) expressible with no index
  arithmetic added.  A mask vector as a `getelementptr` element type is a
  different rule over a different quantity from a mask *store*: the GEP scales by
  the size LLVM allocates, which is why `<8 x i1>` is refused there.  The index's
  own width is not a field: the semantics sign-extends whatever integer value it
  reads to 64 bits, so an `iN` in the text is a shape the parser checks, not
  state the instruction keeps.  It is read as **signed**, and that is how a body
  spells `p - 1`: a sign-extended value below `2 ^ 63` is added, and one at or
  above it is subtracted.  That subtraction's magnitude is `2 ^ 64 - v` and its
  displacement is that magnitude scaled by the element type's size, so the bound
  is on the address rather than on the index — it is defined only while the
  displacement does not exceed the base, and refused above it, since the result
  would leave the address space below zero.  `inbounds` is not a field either —
  the parser accepts and drops it, the printer writes an ordinary `getelementptr`
  without it, and no semantics here reads it. -/
  | gep (dst : String) (elemTy : Ty) (base : Operand) (off : Operand)
  /-- A lane-wise integer comparison: each lane of the result is the predicate's
  one-bit result on the two operands' lane at that position.  The lane count and
  width are the operands' vector type, `<n x iw>`. -/
  | icmpVec (dst : String) (pred : IPred) (n w : Nat) (lhs rhs : Operand)
  /-- A lane-wise binary integer operation on vectors of `<n x iw>`. -/
  | binopVec (dst : String) (op : BinOp) (n w : Nat) (lhs rhs : Operand)
  /-- Pack a `<n x i1>` mask into an `n`-bit integer, lane `k` to bit `k`. -/
  | bitcastMask (dst : String) (n : Nat) (v : Operand)
  /-- A lane read: `extractelement <n x iw> <vec>, iN <idx>` binds the lane at
  `idx`.  The vector's shape is a field because it is what the read checks the
  value against; the index's own width is not, because the value the index
  operand reads supplies it and the model reads the index as an unsigned count —
  the width the text writes is a shape the parser checks and drops.

  An index outside `[0, n)` is **poison** in LLVM and **`ub`** here.  The model
  has no poison: `Const.toValue` answers a `poison` literal the same way, and
  `ub` is the chosen over-approximation of it.  That is an over-approximation
  and not a refinement-direction guarantee — `Beh` has a run that reaches `ub`
  admit every outcome, so where LLVM's poison is never observed this model is
  more permissive, not less.  The LLVM side is measured, not assumed: `opt
  -passes=instcombine` (LLVM 21.1.8, this repository's toolchain) folds an
  out-of-range lane read of a constant vector to `poison`, and the write below to
  `poison` too.  The parser does not evaluate the index — a literal and a
  register index are both admitted — so the bound is checked at run time. -/
  | extractelement (dst : String) (n w : Nat) (v : Operand) (idx : Operand)
  /-- A lane write: `insertelement <n x iw> <vec>, iw <elt>, iN <idx>` binds a
  vector that is `vec` with lane `idx` replaced by `elt`.  The element operand is
  written with the vector's element type, which the parser checks; the index's
  width is not a field for the reason given at `extractelement`.

  An index outside `[0, n)` is poison in LLVM and `ub` here, exactly as the lane
  read's is.  An operand whose value is not a vector of the instruction's shape,
  or an element that does not read as an `iw` integer, is `ub` as well — that is
  the hand-built-AST case, since the parser fixes both from the text. -/
  | insertelement (dst : String) (n w : Nat) (v : Operand) (elt : Operand)
      (idx : Operand)
  /-- A two-source static permutation, LLVM's
  `shufflevector <n x iw> %a, <n x iw> %b, <m x i32> <i32 k₀, …, i32 k₍m₋₁₎>`.
  The result has `mask.length` lanes of the operands' element width; entry `k`
  selects lane `k` of the first operand when `k < n` and lane `k - n` of the
  second when `n ≤ k < 2n`.  The permutation is static, which is why the mask is
  a list of naturals rather than an operand: no register supplies it, and the
  mask's length is the result's lane count by construction.

  An entry at or past `2n` is poison in LLVM and `ub` here, and `undef`/`poison`
  entries have no representation in this field at all; the parser refuses both
  spellings by name, because the model has no poison. -/
  | shuffleVec (dst : String) (n w : Nat) (a b : Operand) (mask : List Nat)
  /-- A vector reinterpretation at equal total bit width:
  `bitcast <n x iw> %v to <m x jw>` with `n * w = m * jw`.  Lane order is
  little-endian — lane 0 holds the least significant `w` bits of the packed
  value — so result lane `k` is bits `[k * jw, (k + 1) * jw)` of the source
  lanes packed in order.

  The mask pack `<n x i1>` → `iN` stays `bitcastMask`; this constructor is the
  vector-to-vector case (including a mask vector to a wider lane type), where
  the element size may change but the total width must not.  Any other pair,
  scalar-to-vector and vector-to-scalar included, has no field here and the
  parser refuses it by name. -/
  | vecBitcast (dst : String) (n w m jw : Nat) (v : Operand)
  /-- A call instruction.  The result is bound to `dst` as `retTy`; the callee
  is resolved by the semantics' call environment, not by the function itself.
  The intrinsic spellings the fragment models are the exception the parser
  validates at symbol, arity and operand type: the five the classifier's body
  calls, `llvm.ctpop.i32`, `llvm.ctpop.i64` and `llvm.cttz.i64` for the entry
  kernels, and `llvm.usub.sat.v32i8` and `llvm.x86.avx.ptestz.256` for the
  UTF-8 stage. -/
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

/-- Whether `n` is a positive power of two: the packed-size test a vector
`getelementptr` element type must pass.  `1 ≤ n` is part of the test and not a
remark — `0` is not a power of two, and a `n &&& (n - 1) = 0` test written
without it would admit `0`. -/
def isPowerOfTwo (n : Nat) : Bool :=
  decide (1 ≤ n) && (n &&& (n - 1) == 0)

/-- The `getelementptr` element types this model admits: the widths and the
vector shapes it **pins** as having the same **allocated** size on the modelled
datalayout as the **stored** size `Ty.sizeBytes` computes.

`sizeBytes` is a store size — `(w + 7) / 8`, and `n * ((w + 7) / 8)` for a
vector — while LLVM scales a `getelementptr` by the type's *allocated* size,
which rounds the store size up to the type's ABI alignment.  The two agree on
the seven integer widths this model admits and diverge on others.  Measured with
`opt -passes=instcombine` here, under the datalayout this repository records
(`target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"`),
it folds `getelementptr i24, ptr null, i64 1` to 4 while `sizeBytes i24` is 3,
`i33` to 8 while it is 5, `i48` to 8 while it is 6, and `i96` to 16 while it is
12.  The datalayout matters: without one, `opt` uses LLVM's default layout and
folds `i96` to 12 instead, which is why every number here is qualified by the
layout it was read under.  A step scaled by the stored size would therefore name
one address in this model and another in LLVM, so the parser refuses such a width
by name instead of approximating it, and admits only `i1`, `i7`, `i8`, `i16`,
`i32`, `i64` and `i128`, whose allocated size is 1, 1, 1, 2, 4, 8 and 16 bytes on
the same datalayout.

A **vector** of integer lanes is admitted under one condition: the lane width is
a whole number of bytes (`w % 8 = 0`) **and** the packed size `n * w / 8` is a
power of two, hence at least 1.  The first clause excludes the packing
divergence — `sizeBytes` of a vector is `n * ((w + 7) / 8)` while the memory
model packs and stores it at `n * w / 8`, and the two agree only for whole-byte
lanes, so `<8 x i1>` (packed 1, `sizeBytes` 8) steps eight times too far.  The
second excludes the allocation divergence — LLVM's vector stride is the store
size rounded up to its next power of two, so a packed size that is not a power of
two steps further than `sizeBytes`: `<3 x i32>` and `<4 x i24>` both pack 12 and
LLVM steps 16.  The guarantee is relative to the pinned datalayout: on the layout
recorded above a vector's ABI alignment is `PowerOf2Ceil(storeSize)`, so a
power-of-two packed size *is* the stored size; a layout that raised a vector's
alignment above its size (`v64:128` would do it to `<2 x i32>`) would break the
equality without touching either clause, so a change to the recorded layout
reopens this admission rather than passing silently.

This is an allowlist rather than a computation of the allocated size: the model
has no use for one yet, and it does not characterise which other types would also
agree (`i2` is allocated 1 for a stored 1 and is refused as policy; `<1 x i7>`
and `<2 x i7>` pack and step alike and fail the whole-byte clause, exactly as
`i2` is refused by the integer list).

Two limits of the resulting guarantee belong with it.  First, the admitted set is
what the model *establishes* and pins by measurement, not every type whose two
sizes happen to agree, so an unlisted agreeing type is refused as policy.
Second, the step bounds the index below `2 ^ 63` in the forward direction and the
address below in the backward one, and it does not bound the **address** above: an
`i128` element type multiplies an index below `2 ^ 63` by 16, so the model can
compute an address at or above `2 ^ 64`.  This model's address is an unbounded
`Nat` while LLVM's pointer index is 64 bits, so what LLVM makes of an address at
or above `2 ^ 64` is outside what this model pins; the printed form carries no
`inbounds`, so it adds no in-allocation promise of its own.  A bound tying the
index to the element width would close the address-width gap, and is not added
here. -/
def Ty.gepElemAdmitted : Ty → Bool
  | .int 1 | .int 7 | .int 8 | .int 16 | .int 32 | .int 64 | .int 128 => true
  | .vec n (.int w) => w % 8 == 0 && isPowerOfTwo (n * w / 8)
  | _ => false

/-- The register an instruction defines, if any. -/
def Instr.dst? : Instr → Option String
  | .binop d _ _ _ _ => some d
  | .icmp d _ _ _ _ => some d
  | .icmpPtr d _ _ _ => some d
  | .select d _ _ _ _ => some d
  | .trunc d _ _ _ => some d
  | .zext d _ _ _ => some d
  | .sext d _ _ _ => some d
  | .alloca d _ _ => some d
  | .load d _ _ => some d
  | .store _ _ _ => none
  | .gep d _ _ _ => some d
  | .icmpVec d _ _ _ _ _ => some d
  | .binopVec d _ _ _ _ _ => some d
  | .bitcastMask d _ _ => some d
  | .extractelement d _ _ _ _ => some d
  | .insertelement d _ _ _ _ _ => some d
  | .shuffleVec d _ _ _ _ _ => some d
  | .vecBitcast d _ _ _ _ _ => some d
  | .call d _ _ _ => some d
  | .callVoid _ _ => none
  | .phi d _ _ => some d

/-- Registers read by an instruction. -/
def Instr.uses : Instr → List String
  | .binop _ _ _ a b => a.regs ++ b.regs
  | .icmp _ _ _ a b => a.regs ++ b.regs
  | .icmpPtr _ _ a b => a.regs ++ b.regs
  | .select _ _ c a b => c.regs ++ a.regs ++ b.regs
  | .trunc _ _ _ v => v.regs
  | .zext _ _ _ v => v.regs
  | .sext _ _ _ v => v.regs
  | .alloca _ _ _ => []
  | .load _ _ p => p.regs
  | .store _ v p => v.regs ++ p.regs
  | .gep _ _ base off => base.regs ++ off.regs
  | .icmpVec _ _ _ _ a b => a.regs ++ b.regs
  | .binopVec _ _ _ _ a b => a.regs ++ b.regs
  | .bitcastMask _ _ v => v.regs
  | .extractelement _ _ _ v idx => v.regs ++ idx.regs
  | .insertelement _ _ _ v elt idx => v.regs ++ elt.regs ++ idx.regs
  | .shuffleVec _ _ _ a b _ => a.regs ++ b.regs
  | .vecBitcast _ _ _ _ _ v => v.regs
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
  | .icmpPtr .. => true
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
  | .extractelement .. => true
  | .insertelement .. => true
  | .shuffleVec .. => true
  | .vecBitcast .. => true
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
