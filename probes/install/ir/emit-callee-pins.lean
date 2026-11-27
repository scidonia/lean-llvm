import LeanLLVM.Parser

/- Emit the Lean literal, the per-block instruction lists and the `findBlock` pins
of one captured callee fixture, so a module's pinned body is the parse of the
shipped text rather than a transcription of it.

  lake env lean --run probes/install/ir/emit-callee-pins.lean <fixture> <symbol> <prefix>

`<symbol>` is checked against the fixture's first function; `<prefix>` is the
module's own prefix for the generated names (`numD8`, `stkMul`, …).  The output
is the text the module holds: the caller pastes it in and the module's `#guard`
holds it to the fixture on every build. -/

open LeanLLVM

namespace Gen

def hexOf (w : Nat) (v : BitVec w) : String :=
  let digits := (w + 3) / 4
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  "0x" ++ String.ofList (List.replicate (digits - s.length) '0') ++ s ++ "#" ++ toString w

partial def tyStr : Ty → String
  | .int w => s!"(Ty.int {w})"
  | .ptr => "Ty.ptr"
  | .void => "Ty.void"
  | .double => "Ty.double"
  | .vec n e => s!"(Ty.vec {n} {tyStr e})"
  | .array n e => s!"(Ty.array {n} {tyStr e})"
  | .struct n b => s!"(Ty.struct \"{n}\" {b})"

def constStr : Const → String
  | .int w v => s!"(Const.int {w} {hexOf w v})"
  | .null => "Const.null" | .undef => "Const.undef" | .poison => "Const.poison"
  | .splat n w v => s!"(Const.splat {n} {w} {hexOf w v})"
  | .vector w lanes => s!"(Const.vector {w} [{String.intercalate ", " (lanes.map (hexOf w))}])"
  | .float b => s!"(Const.float {hexOf 64 b})"

def opStr : Operand → String
  | .reg n => s!"(Operand.reg \"{n}\")"
  | .global n => s!"(Operand.global \"{n}\")"
  | .imm c => s!"(Operand.imm {constStr c})"

def predStr : IPred → String
  | .eq => "IPred.eq" | .ne => "IPred.ne" | .ult => "IPred.ult" | .ule => "IPred.ule"
  | .ugt => "IPred.ugt" | .uge => "IPred.uge" | .slt => "IPred.slt" | .sle => "IPred.sle"
  | .sgt => "IPred.sgt" | .sge => "IPred.sge"

def binStr : BinOp → String
  | .add => "BinOp.add" | .sub => "BinOp.sub" | .mul => "BinOp.mul" | .udiv => "BinOp.udiv"
  | .sdiv => "BinOp.sdiv" | .urem => "BinOp.urem" | .srem => "BinOp.srem" | .and => "BinOp.and"
  | .or => "BinOp.or" | .xor => "BinOp.xor" | .shl => "BinOp.shl" | .lshr => "BinOp.lshr"
  | .ashr => "BinOp.ashr"

def argsStr (args : List (Ty × Operand)) : String :=
  "[" ++ String.intercalate ",\n                             "
    (args.map fun (t, o) => s!"({tyStr t}, {opStr o})") ++ "]"

def instrStr : Instr → String
  | .binop d op w a b => s!"Instr.binop \"{d}\" ({binStr op}) {w} {opStr a} {opStr b}"
  | .icmp d p w a b => s!"Instr.icmp \"{d}\" ({predStr p}) {w} {opStr a} {opStr b}"
  | .icmpPtr d p a b => s!"Instr.icmpPtr \"{d}\" ({predStr p}) {opStr a} {opStr b}"
  | .select d t c a b => s!"Instr.select \"{d}\" {tyStr t} {opStr c} {opStr a} {opStr b}"
  | .trunc d wi wo v => s!"Instr.trunc \"{d}\" {wi} {wo} {opStr v}"
  | .zext d wi wo v => s!"Instr.zext \"{d}\" {wi} {wo} {opStr v}"
  | .sext d wi wo v => s!"Instr.sext \"{d}\" {wi} {wo} {opStr v}"
  | .ptrtoint d v => s!"Instr.ptrtoint \"{d}\" {opStr v}"
  | .inttoptr d v => s!"Instr.inttoptr \"{d}\" {opStr v}"
  | .uitofp d w v => s!"Instr.uitofp \"{d}\" {w} {opStr v}"
  | .fmul d a b => s!"Instr.fmul \"{d}\" {opStr a} {opStr b}"
  | .fdiv d a b => s!"Instr.fdiv \"{d}\" {opStr a} {opStr b}"
  | .fneg d v => s!"Instr.fneg \"{d}\" {opStr v}"
  | .fcmp d p a b => s!"Instr.fcmp \"{d}\" (FPred.oeq) {opStr a} {opStr b}"
  | .bitcastToInt d v => s!"Instr.bitcastToInt \"{d}\" {opStr v}"
  | .bitcastToDouble d v => s!"Instr.bitcastToDouble \"{d}\" {opStr v}"
  | .alloca d t al => s!"Instr.alloca \"{d}\" {tyStr t} {al}"
  | .load d t p => s!"Instr.load \"{d}\" {tyStr t} {opStr p}"
  | .store t v p => s!"Instr.store {tyStr t} {opStr v} {opStr p}"
  | .gep d t b o => s!"Instr.gep \"{d}\" {tyStr t} {opStr b} {opStr o}"
  | .icmpVec d p n w a b => s!"Instr.icmpVec \"{d}\" ({predStr p}) {n} {w} {opStr a} {opStr b}"
  | .binopVec d op n w a b => s!"Instr.binopVec \"{d}\" ({binStr op}) {n} {w} {opStr a} {opStr b}"
  | .bitcastMask d n v => s!"Instr.bitcastMask \"{d}\" {n} {opStr v}"
  | .extractelement d n w v i => s!"Instr.extractelement \"{d}\" {n} {w} {opStr v} {opStr i}"
  | .insertelement d n w v e i => s!"Instr.insertelement \"{d}\" {n} {w} {opStr v} {opStr e} {opStr i}"
  | .shuffleVec d n w a b m => s!"Instr.shuffleVec \"{d}\" {n} {w} {opStr a} {opStr b} {m}"
  | .vecBitcast d n w m jw v => s!"Instr.vecBitcast \"{d}\" {n} {w} {m} {jw} {opStr v}"
  | .call d t c args => s!"Instr.call \"{d}\" {tyStr t} \"{c}\" {argsStr args}"
  | .callVoid c args => s!"Instr.callVoid \"{c}\" {argsStr args}"
  | .phi d t inc =>
      s!"Instr.phi \"{d}\" {tyStr t} [" ++ String.intercalate ",\n                                       "
        (inc.map fun (b, o) => s!"(\"{b}\", {opStr o})") ++ "]"

def termStr : Term → String
  | .ret t (some v) => s!"Term.ret {tyStr t} (some {opStr v})"
  | .ret t none => s!"Term.ret {tyStr t} none"
  | .br d => s!"Term.br \"{d}\""
  | .condbr c t f => s!"Term.condbr {opStr c} \"{t}\" \"{f}\""
  | .unreachable => "Term.unreachable"

def blockStr (b : Block) : String :=
  "\n    { name := \"" ++ b.name ++ "\",\n      instrs := [\n" ++
    String.intercalate ",\n" (b.instrs.map fun i => "        " ++ instrStr i) ++
    "\n      ],\n      term := " ++ termStr b.term ++ " }"

def fnStr (f : Function) : String :=
  "{ name := \"" ++ f.name ++ "\",\n  retTy := " ++ tyStr f.retTy ++ ",\n  params := [" ++
    String.intercalate ",\n             " (f.params.map fun (n, t) => s!"(\"{n}\", {tyStr t})") ++
    "],\n  blocks := [" ++ String.intercalate "," (f.blocks.map blockStr) ++ "] }"

def sanitize (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isAlphanum then c else '_')

def camel (s : String) : String :=
  let parts := (s.splitOn ".").filter (· ≠ "")
  String.join (parts.map fun p =>
    match p.toList with
    | [] => ""
    | c :: rest => String.singleton c.toUpper ++ String.ofList rest)

def defOf (pre : String) (b : Block) : String :=
  "def " ++ pre ++ camel b.name ++ "Instrs : List Instr :=\n  [\n" ++
    String.intercalate ",\n" (b.instrs.map fun i => "    " ++ instrStr i) ++ "]\n"

def pin (pre : String) (b : Block) (lhs : String) : String :=
  "theorem " ++ pre ++ "_findBlock_" ++ sanitize b.name ++ " :\n    " ++ pre ++
    "Body.findBlock \"" ++ b.name ++
    "\" = some ⟨\"" ++ b.name ++ "\", " ++ lhs ++ ", " ++ termStr b.term ++ "⟩ := by decide\n"

end Gen

open Gen

def main (args : List String) : IO Unit := do
  let (path, sym, pre) ← match args with
    | [p, s, x] => pure (p, s, x)
    | _ => do
        IO.eprintln "usage: emit-callee-pins.lean <fixture> <symbol> <prefix>"
        IO.Process.exit 2
  let src ← IO.FS.readFile path
  match parseModuleWith [] src with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 3
  | .ok m =>
    match m.functions.head? with
    | none => IO.eprintln "ERROR: no function"; IO.Process.exit 3
    | some f =>
      if f.name ≠ sym then
        IO.eprintln s!"ERROR: the fixture's function is {f.name}"; IO.Process.exit 3
      IO.println "-- § the body literal"
      IO.println ("def " ++ pre ++ "Body : Function :=\n" ++ fnStr f)
      IO.println "-- § the instruction lists"
      for b in f.blocks do IO.print (defOf pre b ++ "\n")
      IO.println "-- § the pins"
      for b in f.blocks do IO.print (pin pre b (pre ++ camel b.name ++ "Instrs"))
      IO.eprintln s!"emitted the literal and pins for {f.blocks.length} blocks, {(f.blocks.flatMap (·.instrs)).length} instructions"
