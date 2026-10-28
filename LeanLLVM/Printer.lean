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

def Const.render : Const → String
  | .int _ v => toString v.toNat
  | .null => "null"
  | .undef => "undef"
  | .poison => "poison"

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

def Instr.render : Instr → String
  | .binop d op w a b =>
      s!"  {d} = {op.render} i{w} {a.token}, {b.token}"
  | .icmp d pred w a b =>
      s!"  {d} = icmp {pred.render} i{w} {a.token}, {b.token}"
  | .select d ty c a b =>
      s!"  {d} = select i1 {c.token}, {a.render ty}, {b.render ty}"
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
  | .call d retTy callee args =>
      let rendered :=
        String.intercalate ", " (args.map fun (ty, op) => s!"{ty.render} {op.token}")
      s!"  {d} = call {retTy.render} @{callee}({rendered})"

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
