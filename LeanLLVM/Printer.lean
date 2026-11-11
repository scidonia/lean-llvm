/-
Pretty-printing the internal IR back to textual LLVM IR.

The printer emits canonical syntax: one instruction per line, the instruction
type on the first operand, and `align` on every `alloca`.  The output is meant
to be consumed by `llvm-as`/`opt`/`llc` downstream.

Three pieces of real LLVM meaning the AST does not carry are settled here
instead of being invented:

* `getelementptr` is printed **without** `inbounds`.  The flag promises that the
  offset stays inside the object it started in, the parser drops it, and no
  semantics here reads it; printing it would add a promise the source did not
  make, so the printed form is an ordinary `getelementptr`.
* an index written as a register is printed at the width that register's own
  definition binds it at, read from the function being printed.  LLVM checks the
  written operand type against the definition, so a fixed `i64` (or `i32` for a
  lane index) makes otherwise-valid text fail to assemble: `'%k' defined with
  type 'i32' but expected 'i64'`.
* a `load` or `store` is printed with `align 1`.  The AST has no field for a
  load/store alignment, and **omitting** it is not "no requirement": LLVM
  substitutes the type's ABI alignment, which is a promise the model has not
  proved.  `align 1` is the weakest alignment LLVM admits and assumes nothing
  about the address, so the printed text promises no more than the model does.
  An `alloca`'s alignment *is* a field and is printed exactly as parsed.
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

/-- The type an instruction's destination is bound at, when it binds one.
`store` and a `void` call bind nothing, so they have none.  The printer reads
this to write a register operand at its definition's width, and the parser's
`phi`, pointer-comparison and store checks read the same table. -/
def Instr.resultTy : Instr → Option Ty
  | .binop _ _ w _ _ => some (.int w)
  | .icmp .. => some (.int 1)
  | .icmpPtr .. => some (.int 1)
  | .select _ ty _ _ _ => some ty
  | .trunc _ _ wOut _ => some (.int wOut)
  | .zext _ _ wOut _ => some (.int wOut)
  | .sext _ _ wOut _ => some (.int wOut)
  | .alloca .. => some .ptr
  | .load _ ty _ => some ty
  | .store .. => none
  | .gep .. => some .ptr
  | .icmpVec _ _ n _ _ _ => some (.vec n (.int 1))
  | .binopVec _ _ n w _ _ => some (.vec n (.int w))
  | .bitcastMask _ n _ => some (.int n)
  | .extractelement _ _ w _ _ => some (.int w)
  | .insertelement _ n w _ _ _ => some (.vec n (.int w))
  | .shuffleVec _ _ w _ _ mask => some (.vec mask.length (.int w))
  | .vecBitcast _ _ _ m jw _ => some (.vec m (.int jw))
  | .call _ retTy _ _ => some retTy
  | .callVoid _ _ => none
  | .phi _ ty _ => some ty

/-- Every register a function binds, with its type: the parameters first, then
each instruction's destination in program order.  A parsed function binds a name
at most once (`checkDefinitions` refuses a repeat), so the first entry for a name
is the only one, and the table agrees with the reading `lookupName` gives. -/
def Function.regTypes (f : Function) : List (String × Ty) :=
  f.params ++ f.blocks.flatMap (fun b =>
    b.instrs.filterMap fun i =>
      match i.dst? with
      | some d => i.resultTy.map fun ty => (d, ty)
      | none => none)

/-- The type a register is bound at in a function: its parameter type or the
result type of its definition.  A name the function neither takes as a parameter
nor defines has no type here. -/
def Function.regType (f : Function) (n : String) : Option Ty :=
  lookupName f.regTypes n

/-- The index type a `getelementptr` prints, read from the register table of the
function being printed.  An integer literal carries its own width in the AST; a
register is written at the width its own definition binds it at, because that is
the type LLVM checks the operand against — printing a fixed `i64` for an `i32`
index register is an assembler error (`'%k' defined with type 'i32' but expected
'i64'`).  The element type is a field of the instruction, so it is printed as it
was parsed.

A register the function neither takes nor defines has no recoverable width, and
neither does a literal with no integer type (`undef`, `poison`, `null`, a splat);
those print the canonical 64-bit form.  Such text is already not LLVM-valid for
another reason — the register is undefined, or the constant is not an integer —
so no assembler-valid input reaches that fallback. -/
def gepIndexTy (regTy : String → Option Ty) : Operand → String
  | .imm (.int w _) => s!"i{w}"
  | .reg n => match regTy n with
      | some (.int w) => s!"i{w}"
      | _ => "i64"
  | _ => "i64"

/-- A call's argument list, as the parenthesised text its printer emits. -/
def callArgs (args : List (Ty × Operand)) : String :=
  String.intercalate ", " (args.map fun (ty, op) => s!"{ty.render} {op.token}")

/-- The index type a lane instruction prints, read from the register table of the
function being printed for the same reason `gepIndexTy` gives: LLVM checks the
written index type against the register's definition, so a fixed `i32` for an
`i64` index register is refused with `'%k' defined with type 'i64' but expected
'i32'`.  An integer literal carries its own width; a register the function
neither takes nor defines, and a literal with no integer type, have no
recoverable width and print the canonical 32-bit form, whose text is already not
LLVM-valid for the same reasons as in `gepIndexTy`. -/
def laneIndexTy (regTy : String → Option Ty) : Operand → String
  | .imm (.int w _) => s!"i{w}"
  | .reg n => match regTy n with
      | some (.int w) => s!"i{w}"
      | _ => "i32"
  | _ => "i32"

/-- Render an instruction inside the function whose register table is `regTy`.
A register operand that carries a type of its own — a `getelementptr` or lane
index — is written at the type that register is defined at; the rest are written
at the instruction's own type, as LLVM does. -/
def Instr.renderWith (regTy : String → Option Ty) : Instr → String
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
      -- `align 1` rather than no alignment: omission means the type's ABI
      -- alignment, a promise the AST does not carry and the model has not
      -- proved.  One byte is the weakest alignment LLVM admits.
      s!"  {d} = load {ty.render}, ptr {p.token}, align 1"
  | .store ty v p =>
      s!"  store {v.render ty}, ptr {p.token}, align 1"
  | .gep d elemTy base off =>
      -- No `inbounds`: the parser drops the source's flag and no semantics here
      -- reads it, so printing it would add a promise the source did not make.
      s!"  {d} = getelementptr {elemTy.render}, ptr {base.token}, {gepIndexTy regTy off} {off.token}"
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
      s!"  {d} = extractelement <{n} x i{w}> {v.token}, {laneIndexTy regTy idx} {idx.token}"
  | .insertelement d n w v elt idx =>
      s!"  {d} = insertelement <{n} x i{w}> {v.token}, i{w} {elt.token}, {laneIndexTy regTy idx} {idx.token}"
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

/-- Render one instruction with no function around it, so no register has a
definition to read.  `gepIndexTy` and `laneIndexTy` document the canonical width
such an index falls back to; text that carries the register's real width comes
from `Function.render`, which has the function. -/
def Instr.render : Instr → String := Instr.renderWith (fun _ => none)

def Term.render : Term → String
  | .ret .void none => "  ret void"
  | .ret .void (some _) => "  ret void"
  | .ret _ none => "  ret void"
  | .ret ty (some v) => s!"  ret {ty.render} {v.token}"
  | .br dest => s!"  br label %{dest}"
  | .condbr c t f => s!"  br i1 {c.token}, label %{t}, label %{f}"
  | .unreachable => "  unreachable"

def Block.renderWith (regTy : String → Option Ty) (b : Block) : String :=
  let instrs := b.instrs.map (Instr.renderWith regTy)
  String.intercalate "\n" ([b.name ++ ":"] ++ instrs ++ [b.term.render])

def Block.render (b : Block) : String := Block.renderWith (fun _ => none) b

def Function.render (f : Function) : String :=
  let params := String.intercalate ", " (f.params.map fun (n, ty) => s!"{ty.render} {n}")
  let body := String.intercalate "\n\n" (f.blocks.map (Block.renderWith f.regType))
  "define " ++ f.retTy.render ++ " @" ++ f.name ++ "(" ++ params ++ ") {\n" ++ body ++ "\n}"

def Decl.render (d : Decl) : String :=
  let params := String.intercalate ", " (d.params.map Ty.render)
  s!"declare {d.retTy.render} @{d.name}({params})"

def Module.render (m : Module) : String :=
  let decls := m.decls.map Decl.render
  String.intercalate "\n\n" (decls ++ m.functions.map Function.render) ++ "\n"

end LeanLLVM
