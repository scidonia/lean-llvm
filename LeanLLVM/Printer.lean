/-
Pretty-printing the internal IR back to textual LLVM IR.

The printer emits canonical syntax: one instruction per line, the instruction
type on the first operand, and `align` on every `alloca`.  The output is meant
to be consumed by `llvm-as`/`opt`/`llc` downstream.
-/
import LeanLLVM.Syntax

namespace LeanLLVM

def Ty.render : Ty → String
  | .int w => s!"i{w}"
  | .ptr => "ptr"
  | .void => "void"
  | .vec n elem => s!"<{n} x {elem.render}>"

/-- A literal, without its type: an integer is its unsigned value, as LLVM
prints it.  A splat is `splat (<elem> <value>)` — the lane count is omitted
because the operand's vector type supplies it on re-parse, and the element width
comes from the value itself.  A lane list is `<i8 34, i8 92>`, each lane written
with its width the way LLVM prints a vector constant.  Every splat has a printed
form, because a splat carries an integer.  A lane list with no lanes prints
`<>`, which the parser does not read back: the parser requires at least one lane,
so a zero-lane literal can only be built directly in an AST. -/
def Const.render : Const → String
  | .int _ v => toString v.toNat
  | .null => "null"
  | .undef => "undef"
  | .poison => "poison"
  | .splat _ w v => s!"splat (i{w} {v.toNat})"
  | .vector w lanes =>
      "<" ++ String.intercalate ", " (lanes.map fun v => s!"i{w} {v.toNat}") ++ ">"

/-- Render an operand that carries no type prefix of its own. -/
def Operand.token : Operand → String
  | .reg n => n
  | .imm c => Const.render c

/-- Render an operand with its type, as LLVM does where the type cannot be
inferred from position. -/
def Operand.render (ty : Ty) : Operand → String
  | .reg n => s!"{ty.render} {n}"
  | .imm c => s!"{ty.render} {Const.render c}"

def BinOp.render : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .udiv => "udiv" | .sdiv => "sdiv" | .urem => "urem" | .srem => "srem"
  | .and => "and" | .or => "or" | .xor => "xor"
  | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr"

def IPred.render : IPred → String
  | .eq => "eq" | .ne => "ne"
  | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

/-- The index type a `getelementptr` prints.  An integer literal carries its own
width; a register carries none in the instruction, so the canonical form is
`i64` — the width the semantics sign-extends the index to.  Those are the two
forms the parser produces, and each re-parses to the instruction it was printed
from: the index width is checked and dropped on the way in, and recovered here.
A register index therefore prints as `i64` whatever width its definition has, so
a body whose printed text must also pass `opt` uses an `i64` index register or a
literal — the parser accepts a narrower index, and the printer cannot recover it.

The element type is a field of the instruction, so it is printed as it was
parsed: the canonical text of a `getelementptr i32` is still `i32`, and the
printed form re-parses to the same instruction. -/
def gepIndexTy : Operand → String
  | .imm (.int w _) => s!"i{w}"
  | _ => "i64"

/-- A call's argument list, as the parenthesised text its printer emits. -/
def callArgs (args : List (Ty × Operand)) : String :=
  String.intercalate ", " (args.map fun (ty, op) => s!"{ty.render} {op.token}")

/-- The index type a lane instruction prints.  An integer literal carries its
own width; a register carries none in the instruction, so the canonical form is
`i32` — the width those instructions are usually written at, and the one the
parser checks and drops.  Both forms re-parse to the instruction they were
printed from, because the index width is not part of the instruction.

A register index therefore prints as `i32` whatever width its definition has, so
a body whose printed text must also pass `opt`/`llvm-as` uses an `i32` index
register or a literal: the parser accepts an index written at another width, and
the printer cannot recover it.  Measured here with `llvm-as`: a function whose
`%k` is `i64 %k` prints `insertelement … i32 %k`, which the assembler refuses
with `'%k' defined with type 'i64' but expected 'i32'`.  This is the same
limitation `gepIndexTy` records, for the same reason. -/
def laneIndexTy : Operand → String
  | .imm (.int w _) => s!"i{w}"
  | _ => "i32"

def Instr.render : Instr → String
  | .binop d op w a b =>
      s!"  {d} = {op.render} i{w} {a.token}, {b.token}"
  | .icmp d pred w a b =>
      s!"  {d} = icmp {pred.render} i{w} {a.token}, {b.token}"
  | .icmpPtr d pred a b =>
      s!"  {d} = icmp {pred.render} ptr {a.token}, {b.token}"
  | .select d ty c a b =>
      -- The condition's type is not a field: a vector result `<n x iw>` takes a
      -- `<n x i1>` condition and a scalar result an `i1`.  Emitting it from the
      -- result type is what makes the printed form re-parse to the same
      -- instruction, because the parser checks the condition against the same
      -- rule.
      let condTy : Ty := match ty with
        | .vec n _ => .vec n (.int 1)
        | _ => .int 1
      s!"  {d} = select {condTy.render} {c.token}, {a.render ty}, {b.render ty}"
  | .trunc d wIn wOut v =>
      s!"  {d} = trunc i{wIn} {v.token} to i{wOut}"
  | .zext d wIn wOut v =>
      s!"  {d} = zext i{wIn} {v.token} to i{wOut}"
  | .sext d wIn wOut v =>
      s!"  {d} = sext i{wIn} {v.token} to i{wOut}"
  | .alloca d ty align =>
      if align = 0 then s!"  {d} = alloca {ty.render}"
      else s!"  {d} = alloca {ty.render}, align {align}"
  | .load d ty p =>
      s!"  {d} = load {ty.render}, ptr {p.token}"
  | .store ty v p =>
      s!"  store {v.render ty}, ptr {p.token}"
  | .gep d elemTy base off =>
      s!"  {d} = getelementptr inbounds {elemTy.render}, ptr {base.token}, {gepIndexTy off} {off.token}"
  | .icmpVec d pred n w a b =>
      let ty := Ty.vec n (.int w)
      s!"  {d} = icmp {pred.render} {ty.render} {a.token}, {b.token}"
  | .binopVec d op n w a b =>
      let ty := Ty.vec n (.int w)
      s!"  {d} = {op.render} {ty.render} {a.token}, {b.token}"
  | .bitcastMask d n v =>
      let ty := Ty.vec n (.int 1)
      s!"  {d} = bitcast {ty.render} {v.token} to i{n}"
  | .extractelement d n w v idx =>
      s!"  {d} = extractelement <{n} x i{w}> {v.token}, {laneIndexTy idx} {idx.token}"
  | .insertelement d n w v elt idx =>
      s!"  {d} = insertelement <{n} x i{w}> {v.token}, i{w} {elt.token}, {laneIndexTy idx} {idx.token}"
  | .shuffleVec d n w a b mask =>
      let ty := s!"<{n} x i{w}>"
      let entries := String.intercalate ", " (mask.map fun k => s!"i32 {k}")
      s!"  {d} = shufflevector {ty} {a.token}, {ty} {b.token}, <{mask.length} x i32> <{entries}>"
  | .vecBitcast d n w m jw v =>
      s!"  {d} = bitcast <{n} x i{w}> {v.token} to <{m} x i{jw}>"
  | .call d retTy callee args =>
      s!"  {d} = call {retTy.render} @{callee}({callArgs args})"
  | .callVoid callee args =>
      -- No destination and no return type: the instruction binds no name, and
      -- the only accepted form returns `void`.
      s!"  call void @{callee}({callArgs args})"
  | .phi d ty incoming =>
      -- LLVM writes the incoming values untyped — the instruction's type prefix
      -- supplies it — so the printer emits a register bare and a literal without
      -- a type, and the parser reads both back at the phi's type.
      let entries := incoming.map fun kv => s!"[ {kv.2.token}, %{kv.1} ]"
      s!"  {d} = phi {ty.render} {String.intercalate ", " entries}"

def Term.render : Term → String
  | .ret .void none => "  ret void"
  | .ret .void (some _) => "  ret void"
  | .ret _ none => "  ret void"
  | .ret ty (some v) => s!"  ret {ty.render} {v.token}"
  | .br dest => s!"  br label %{dest}"
  | .condbr c t f => s!"  br i1 {c.token}, label %{t}, label %{f}"
  | .unreachable => "  unreachable"

def Block.render (b : Block) : String :=
  let instrs := b.instrs.map Instr.render
  String.intercalate "\n" ([b.name ++ ":"] ++ instrs ++ [b.term.render])

def Function.render (f : Function) : String :=
  let params := String.intercalate ", " (f.params.map fun (n, ty) => s!"{ty.render} {n}")
  let body := String.intercalate "\n\n" (f.blocks.map Block.render)
  "define " ++ f.retTy.render ++ " @" ++ f.name ++ "(" ++ params ++ ") {\n" ++ body ++ "\n}"

def Decl.render (d : Decl) : String :=
  let params := String.intercalate ", " (d.params.map Ty.render)
  s!"declare {d.retTy.render} @{d.name}({params})"

def Module.render (m : Module) : String :=
  let decls := m.decls.map Decl.render
  String.intercalate "\n\n" (decls ++ m.functions.map Function.render) ++ "\n"

end LeanLLVM
