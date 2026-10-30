/-
A parser for the subset of textual LLVM IR that the semantics models.

The parser is line oriented: one instruction per line, one label per block.
Unmodelled instructions and block structure are refused with a message naming
the construct, rather than being approximated: `phi`, `getelementptr`,
aggregates and floating point are not accepted yet.  A function definition's
header is checked for attributes the semantics does not model: a return
attribute before the return type and a function attribute after the parameter
list are both refused.  A `declare` header is not checked: unmodelled tokens in
a declaration's parameter list or after its closing parenthesis are still
accepted.
-/
import LeanLLVM.Syntax

namespace LeanLLVM

/-! ### Lexing -/

/-- Characters that always stand alone as a token. -/
def isPunct (c : Char) : Bool :=
  "(){}[],=:*<>".toList.contains c

/-- Split one line into tokens, dropping a `;` comment. -/
def tokenize (line : String) : List String :=
  let cs := line.toList.takeWhile (· ≠ ';')
  let rec go : List Char → List Char → List String → List String
    | [], cur, out =>
        let out := if cur.isEmpty then out else String.ofList cur.reverse :: out
        out.reverse
    | c :: rest, cur, out =>
        if c.isWhitespace then
          if cur.isEmpty then go rest [] out
          else go rest [] (String.ofList cur.reverse :: out)
        else if isPunct c then
          let out := if cur.isEmpty then out else String.ofList cur.reverse :: out
          go rest [] (String.singleton c :: out)
        else
          go rest (c :: cur) out
  go cs [] []

/-- Tokenise a source file into non-empty lines of tokens. -/
def tokenLines (src : String) : List (List String) :=
  (src.splitOn "\n").map tokenize |>.filter (fun l => !l.isEmpty)

/-! ### A small parser monad over a token list -/

/-- A parser consumes tokens from the front and either fails or returns a value
and the remaining tokens. -/
abbrev P (α : Type) : Type := List String → Except String (α × List String)

namespace P

def bind (p : P α) (f : α → P β) : P β := fun ts =>
  match p ts with
  | .error e => .error e
  | .ok (a, rest) => f a rest

instance : Monad P where
  pure a := fun ts => .ok (a, ts)
  bind := bind

def fail {α} (msg : String) : P α := fun _ => .error msg

def next : P String := fun ts =>
  match ts with
  | [] => .error "unexpected end of line"
  | t :: rest => .ok (t, rest)

def peek : P (Option String) := fun ts => .ok (ts.head?, ts)

def expect (s : String) : P Unit := do
  let t ← next
  if t = s then pure () else fail s!"expected '{s}', got '{t}'"

def optional (s : String) : P Bool := do
  let t ← peek
  match t with
  | some t =>
      if t = s then
        let _ ← next
        pure true
      else pure false
  | none => pure false

/-- Run a parser and refuse trailing tokens. -/
def runExact {α} (p : P α) (ts : List String) : Except String α :=
  match p ts with
  | .error e => .error e
  | .ok (a, []) => .ok a
  | .ok (_, rest) => .error s!"unexpected trailing tokens: {String.intercalate " " rest}"

end P

/-! ### Types and literals -/

def parseTy (s : String) : Except String Ty :=
  if s = "void" then .ok .void
  else if s = "ptr" then .ok .ptr
  else if s.startsWith "i" then
    match (s.drop 1).toString.toNat? with
    | some w =>
        if 0 < w then .ok (.int w) else .error s!"invalid integer width in '{s}'"
    | none => .error s!"unsupported type '{s}'"
  else .error s!"unsupported type '{s}'"

def expectTy : P Ty := do
  let t ← P.next
  match parseTy t with
  | .ok ty => pure ty
  | .error e => P.fail e

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

/-- Parse a decimal or `0x`-prefixed natural. -/
def parseNat (s : String) : Option Nat :=
  if s.startsWith "0x" || s.startsWith "0X" then
    let ds := (s.drop 2).toString.toList
    ds.foldl (fun acc c => acc.bind fun a => (hexVal c).map fun v => a * 16 + v) (some 0)
  else
    s.toNat?

/-- Parse a signed integer literal. -/
def parseInt (s : String) : Option Int :=
  if s.startsWith "-" then (parseNat (s.drop 1).toString).map fun n => -(n : Int)
  else (parseNat s).map fun n => (n : Int)

/-- A constant of the given type.  Register operands are parsed by
`parseOperand`. -/
def parseConst (ty : Ty) (t : String) : Except String Const :=
  match ty with
  | .int w =>
      if t = "undef" then .ok .undef
      else if t = "poison" then .ok .poison
      else if t = "true" then
        if w = 1 then .ok (.int 1 (BitVec.ofNat 1 1)) else .error "true used at a width other than 1"
      else if t = "false" then
        if w = 1 then .ok (.int 1 (BitVec.ofNat 1 0)) else .error "false used at a width other than 1"
      else
        match parseInt t with
        | some n => .ok (.int w (BitVec.ofInt w n))
        | none => .error s!"invalid integer literal '{t}'"
  | .ptr =>
      if t = "null" then .ok .null
      else .error s!"only the 'null' pointer constant is supported, got '{t}'"
  | .void => .error "void operand"

/-- Parse an operand at a known type: a register `%x` or a literal. -/
def parseOperand (ty : Ty) : P Operand := do
  let t ← P.next
  if t.startsWith "%" then pure (.reg t)
  else
    match parseConst ty t with
    | .ok c => pure (.imm c)
    | .error e => P.fail e

/-- Parse `<ty> <operand>`. -/
def parseTypedOperand : P (Ty × Operand) := do
  let ty ← expectTy
  let o ← parseOperand ty
  pure (ty, o)

/-! ### Instructions -/

inductive Stmt where
  | instr (i : Instr)
  | term (t : Term)

def parseBinop (dst : String) (bop : BinOp) : P Stmt := do
  let ty ← expectTy
  let w ← match ty with
    | .int w => pure w
    | _ => P.fail "binary operation on a non-integer type"
  let a ← parseOperand ty
  P.expect ","
  let b ← parseOperand ty
  pure (.instr (.binop dst bop w a b))

def parseIPred (s : String) : Except String IPred :=
  match s with
  | "eq" => .ok .eq | "ne" => .ok .ne
  | "ult" => .ok .ult | "ule" => .ok .ule | "ugt" => .ok .ugt | "uge" => .ok .uge
  | "slt" => .ok .slt | "sle" => .ok .sle | "sgt" => .ok .sgt | "sge" => .ok .sge
  | _ => .error s!"unsupported comparison predicate '{s}'"

/-- Consume tokens up to and including `stop`, returning those before it. -/
def P.takeUntil (stop : String) : P (List String) := fun ts =>
  let rec go : List String → List String → Except String (List String × List String)
    | [], _ => .error s!"expected '{stop}'"
    | t :: rest, acc =>
        if t = stop then .ok (acc.reverse, rest) else go rest (t :: acc)
  go ts []

/-- Build one argument from the tokens between two commas. -/
def finishCallArg (cur : List String) (acc : List (Ty × Operand)) :
    Except String (List (Ty × Operand)) :=
  match parseTypedOperand cur.reverse with
  | .error e => .error e
  | .ok (a, []) => .ok (a :: acc)
  | .ok (_, _ :: _) => .error "trailing tokens in a call argument"

/-- Parse a call's argument list from the tokens between the parentheses. -/
def parseCallArgs (toks : List String) : Except String (List (Ty × Operand)) :=
  let step : Option (List (Ty × Operand) × List String) →
      String → Option (List (Ty × Operand) × List String)
    | none, _ => none
    | some (acc, cur), t =>
        if t = "," then
          match finishCallArg cur acc with
          | .error _ => none
          | .ok acc' => some (acc', [])
        else some (acc, t :: cur)
  let init : Option (List (Ty × Operand) × List String) := some ([], [])
  match toks.foldl step init with
  | none => .error "malformed call argument list"
  | some (acc, []) => .ok acc.reverse
  | some (acc, cur) =>
      match finishCallArg cur acc with
      | .error e => .error e
      | .ok acc' => .ok acc'.reverse

def parseValueInstr (dst : String) : P Stmt := do
  let op ← P.next
  match op with
  | "add" => parseBinop dst .add
  | "sub" => parseBinop dst .sub
  | "mul" => parseBinop dst .mul
  | "udiv" => parseBinop dst .udiv
  | "sdiv" => parseBinop dst .sdiv
  | "urem" => parseBinop dst .urem
  | "srem" => parseBinop dst .srem
  | "and" => parseBinop dst .and
  | "or" => parseBinop dst .or
  | "xor" => parseBinop dst .xor
  | "shl" => parseBinop dst .shl
  | "lshr" => parseBinop dst .lshr
  | "ashr" => parseBinop dst .ashr
  | "icmp" =>
      let predTok ← P.next
      let pred ← match parseIPred predTok with
        | .ok p => pure p
        | .error e => P.fail e
      let ty ← expectTy
      let w ← match ty with
        | .int w => pure w
        | _ => P.fail "icmp on a non-integer type"
      let a ← parseOperand ty
      P.expect ","
      let b ← parseOperand ty
      pure (.instr (.icmp dst pred w a b))
  | "select" =>
      let (condTy, c) ← parseTypedOperand
      P.expect ","
      let (ty, a) ← parseTypedOperand
      P.expect ","
      let (_, b) ← parseTypedOperand
      if condTy ≠ .int 1 then P.fail "select condition must be i1" else
        pure (.instr (.select dst ty c a b))
  | "trunc" => parseCast dst fun d wi wo v => .trunc d wi wo v
  | "zext" => parseCast dst fun d wi wo v => .zext d wi wo v
  | "sext" => parseCast dst fun d wi wo v => .sext d wi wo v
  | "alloca" =>
      let ty ← expectTy
      let align ← do
        let more ← P.optional ","
        if more then do
          let kw ← P.next
          if kw = "align" then
            let n ← P.next
            match n.toNat? with
            | some k => pure k
            | none => P.fail s!"invalid alignment '{n}'"
          else P.fail "expected 'align' after ','"
        else pure 0
      pure (.instr (.alloca dst ty align))
  | "load" =>
      let ty ← expectTy
      P.expect ","
      let (_, p) ← parseTypedOperand
      pure (.instr (.load dst ty p))
  | "getelementptr" => P.fail "getelementptr is not modelled yet"
  | "call" =>
      let retTy ← expectTy
      let id ← P.next
      let callee := if id.startsWith "@" then (id.drop 1).toString else id
      P.expect "("
      let toks ← P.takeUntil ")"
      match parseCallArgs toks with
      | .error e => P.fail e
      | .ok args => pure (.instr (.call dst retTy callee args))
  | "phi" => P.fail "phi is not modelled yet"
  | other => P.fail s!"unsupported instruction '{other}'"
where
  parseCast (dst : String) (mk : String → Nat → Nat → Operand → Instr) : P Stmt := do
    let tyIn ← expectTy
    let wIn ← match tyIn with
      | .int w => pure w
      | _ => P.fail "cast source must be an integer type"
    let v ← parseOperand tyIn
    P.expect "to"
    let tyOut ← expectTy
    let wOut ← match tyOut with
      | .int w => pure w
      | _ => P.fail "cast result must be an integer type"
    pure (.instr (mk dst wIn wOut v))

def parseSimple : P Stmt := do
  let op ← P.next
  match op with
  | "ret" =>
      let t ← P.next
      if t = "void" then pure (.term (.ret .void none))
      else
        match parseTy t with
        | .error e => P.fail e
        | .ok ty =>
            let v ← parseOperand ty
            pure (.term (.ret ty (some v)))
  | "br" =>
      let t ← P.next
      if t = "label" then
        let d ← P.next
        let dest := if d.startsWith "%" then (d.drop 1).toString else d
        pure (.term (.br dest))
      else
        match parseTy t with
        | .error e => P.fail e
        | .ok ty =>
            let c ← parseOperand ty
            P.expect ","
            P.expect "label"
            let tb ← P.next
            let thenBlock := if tb.startsWith "%" then (tb.drop 1).toString else tb
            P.expect ","
            P.expect "label"
            let fb ← P.next
            let elseBlock := if fb.startsWith "%" then (fb.drop 1).toString else fb
            pure (.term (.condbr c thenBlock elseBlock))
  | "unreachable" => pure (.term .unreachable)
  | "store" =>
      let (ty, v) ← parseTypedOperand
      P.expect ","
      let (_, p) ← parseTypedOperand
      pure (.instr (.store ty v p))
  | other => P.fail s!"unsupported instruction '{other}'"

/-- Parse one instruction or terminator line. -/
def parseStmtLine (toks : List String) : Except String Stmt :=
  match toks with
  | [] => .error "empty instruction"
  | dst :: "=" :: rest =>
      if dst.startsWith "%" then P.runExact (parseValueInstr dst) rest
      else .error s!"expected a register before '=', got '{dst}'"
  | _ => P.runExact parseSimple toks

/-! ### Blocks, functions, modules -/

def isLabel (toks : List String) : Bool :=
  match toks with
  | [_, ":"] => true
  | _ => false

def parseBlockBody (name : String) (ls : List (List String)) :
    Except String (Block × List (List String)) := do
  let rec collect (ls : List (List String)) (acc : List Instr) :
      Except String (List Instr × Term × List (List String)) :=
    match ls with
    | [] => .error s!"block '{name}' has no terminator"
    | l :: rest =>
        match parseStmtLine l with
        | .error e => .error s!"in block '{name}': {e}"
        | .ok (.instr i) => collect rest (i :: acc)
        | .ok (.term t) => .ok (acc.reverse, t, rest)
  let (instrs, term, rest) ← collect ls []
  .ok (⟨name, instrs, term⟩, rest)

/-- Parse the body of a function: a sequence of labelled blocks.  The fuel is
the number of lines, so each recursion consumes one line even when a block body
is length-checked by the parser rather than by the recursion. -/
def parseBlocks (ls : List (List String)) : Except String (List Block) :=
  let rec go : Nat → List (List String) → List Block → Except String (List Block)
    | 0, _, _ => .error "internal parser error: block fuel exhausted"
    | _ + 1, [], acc => .ok acc.reverse
    | fuel + 1, l :: rest, acc =>
        match l with
        | [name, ":"] =>
            match parseBlockBody name rest with
            | .error e => .error e
            | .ok (b, rest') => go fuel rest' (b :: acc)
        | _ => .error s!"expected a block label, got '{String.intercalate " " l}'"
  go (ls.length + 1) ls []

/-- Find the `@name` token, returning the token before it (the return type),
the name and the tokens after it. -/
def findAt (prev : Option String) : List String → Option (Option String × String × List String)
  | [] => none
  | t :: rest =>
      if t.startsWith "@" then some (prev, t, rest) else findAt (some t) rest

def parseParamsFrom (ts : List String) :
    Except String (List (String × Ty) × List String) :=
  match ts with
  | ")" :: rest => .ok ([], rest)
  | "(" :: rest => parseParamsFrom rest
  | tyTok :: nameTok :: rest =>
      match parseTy tyTok with
      | .error e => .error e
      | .ok ty =>
          if nameTok.startsWith "%" then
            match rest with
            | "," :: rest' =>
                match parseParamsFrom rest' with
                | .error e => .error e
                | .ok (ps, rest'') => .ok ((nameTok, ty) :: ps, rest'')
            | ")" :: rest' => .ok ([(nameTok, ty)], rest')
            | _ => .error "expected ',' or ')' after a parameter"
          else .error s!"expected a parameter name, got '{nameTok}'"
  | _ => .error "malformed parameter list"

def parseParams : P (List (String × Ty)) := fun ts =>
  match parseParamsFrom ts with
  | .error e => .error e
  | .ok (ps, rest) => .ok (ps, rest)

/-- Collect the body lines up to the closing `}`. -/
def takeBody : List (List String) → Except String (List (List String) × List (List String))
  | [] => .error "unterminated function: missing '}'"
  | l :: rest =>
      if l = ["}"] then .ok ([], rest)
      else do
        let (body, rest') ← takeBody rest
        .ok (l :: body, rest')

def parseFunction (header : List String) (rest : List (List String)) :
    Except String (Function × List (List String)) := do
  let (retTok?, nameTok, afterName) ←
    match findAt none header with
    | some x => .ok x
    | none => .error "function header without a name"
  let retTok ← match retTok? with
    | some t => .ok t
    | none => .error "function header without a return type"
  let name := (nameTok.drop 1).toString
  -- A return attribute stands between `define` and the return type.  It
  -- constrains the value the function returns, so it is part of the function's
  -- contract: parsing past it and printing the function without it would accept
  -- a wider contract than the pipeline was given.
  let beforeName := header.takeWhile (· ≠ nameTok)
  let returnAttrs := (beforeName.drop 1).dropLast
  if !returnAttrs.isEmpty then
    throw s!"unsupported return attribute '{String.intercalate " " returnAttrs}' before the return type of @{name}"
  let retTy ← parseTy retTok
  let (params, afterParams) ←
    match parseParams afterName with
    | .ok pr => .ok pr
    | .error e => .error s!"in parameters of @{name}: {e}"
  -- A function attribute stands between the parameter list and the body, and
  -- changes what the function promises its caller; it is refused for the same
  -- reason.
  let (functionAttrs, hasBody) :=
    match afterParams.reverse with
    | "{" :: rev => (rev.reverse, true)
    | _ => (afterParams, false)
  if !functionAttrs.isEmpty then
    throw s!"unsupported function attribute '{String.intercalate " " functionAttrs}' after the parameter list of @{name}"
  if !hasBody then
    throw s!"malformed function header of @{name}: expected an opening brace after the parameter list"
  let (body, rest') ← takeBody rest
  let blocks ← parseBlocks body
  .ok (⟨name, retTy, params, blocks⟩, rest')

/-- Build one parameter from the tokens between two commas. -/
def finishDeclParam (cur : List String) (acc : List Ty) : Except String (List Ty) :=
  match cur.reverse with
  | [] => .error "empty declaration parameter"
  | tyTok :: _ =>
      match parseTy tyTok with
      | .error e => .error e
      | .ok ty => .ok (ty :: acc)

/-- Parse a declaration's parameter types from the tokens between the
parentheses.  A parameter name, if present, is dropped. -/
def parseDeclParams (toks : List String) : Except String (List Ty) :=
  let step : Option (List Ty × List String) → String → Option (List Ty × List String)
    | none, _ => none
    | some (acc, cur), t =>
        if t = "," then
          match finishDeclParam cur acc with
          | .error _ => none
          | .ok acc' => some (acc', [])
        else some (acc, t :: cur)
  let init : Option (List Ty × List String) := some ([], [])
  match toks.foldl step init with
  | none => .error "malformed declaration parameter list"
  | some (acc, []) => .ok acc.reverse
  | some (acc, cur) =>
      match finishDeclParam cur acc with
      | .error e => .error e
      | .ok acc' => .ok acc'.reverse

/-- Parse a `declare ret @name(types)` line. -/
def parseDecl (l : List String) : Except String Decl := do
  match l with
  | "declare" :: retTok :: nameTok :: "(" :: rest =>
      let retTy ← parseTy retTok
      let name := if nameTok.startsWith "@" then (nameTok.drop 1).toString else nameTok
      let params ← parseDeclParams (rest.takeWhile (· ≠ ")"))
      .ok { name := name, retTy := retTy, params := params }
  | _ => .error s!"malformed declaration '{String.intercalate " " l}'"

/-- Parse a module: declarations, then function definitions. -/
def parseModule (src : String) : Except String Module := do
  let rec go : Nat → List (List String) → List Decl → List Function →
      Except String Module
    | 0, _, _, _ => .error "internal parser error: module fuel exhausted"
    | _ + 1, [], decls, acc => .ok ⟨decls.reverse, acc.reverse⟩
    | fuel + 1, l :: rest, decls, acc =>
        match l with
        | "declare" :: _ =>
            match parseDecl l with
            | .error e => .error e
            | .ok d => go fuel rest (d :: decls) acc
        | "define" :: _ =>
            match parseFunction l rest with
            | .error e => .error e
            | .ok (f, rest') => go fuel rest' decls (f :: acc)
        | ["}"] => go fuel rest decls acc
        | _ => .error s!"expected 'define' or 'declare', got '{String.intercalate " " l}'"
  let lines := tokenLines src
  go (lines.length + 1) lines [] []

end LeanLLVM
