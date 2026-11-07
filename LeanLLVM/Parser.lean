/-
A parser for the subset of textual LLVM IR that the semantics models.

The parser is line oriented: one instruction per line, one label per block.
Unmodelled instructions and block structure are refused with a message naming
the construct, rather than being approximated: aggregates other than the
fixed-length vector, and floating point, are not accepted yet.  Of the pointer
arithmetic the modelled part is the byte offset an emitted body contains —
`getelementptr [inbounds] i8, ptr X, iN Y` with one index no wider than 64 bits
— and every other `getelementptr` shape is refused by name: a different element
type, a base that is not a `ptr`, a second index, a wider index, and the
`inrange`/`nuw`/`nusw` modifiers.  `inbounds` is accepted and dropped, because
the instruction has no field for it.  Of the vector fragment the modelled part
is the one an emitted body contains — `load` of `<n x i8>`, the lane-wise
`icmp`, the lane-wise `or`/`and`/`xor`/`add`/`sub`, the mask `bitcast`, the lane
accesses `extractelement` and `insertelement`, and both literal forms a vector
constant takes: the `splat` and the lane list `<i32 1, i32 2>`, with
`zeroinitializer` read as the splat of zero — and the rest of the vector grammar
is refused by name.  A lane access's index is read as an unsigned count and its
width is checked and dropped; an index outside the vector's lane range is not
refused here (it is not a syntax error) and is undefined behaviour at run time,
which is what LLVM's poison becomes in this model.  A
function definition's header is checked for attributes the semantics does not
model: a return attribute before the return type and a function attribute after
the parameter list are both refused.  A `declare` header is not checked:
unmodelled tokens in a declaration's parameter list or after its closing
parenthesis are still accepted.

A call is written `[<dst> =] [tail] call <ty> [<function type>]
@<callee>(<args>)`, where the function type may be omitted.  `tail` is
accepted and dropped: the model has no ABI, no stack discipline and no caller or
callee frame — a call's meaning is entirely the `Calls` environment's, which
receives the symbol, the argument values, the caller's memory and the allocator
cursor — so the marker has nothing here to affect.  A call with no destination is
the `void` form and binds nothing; a discarded non-`void` result and a
destination on a `void` call are both refused by name.  A written callee function
type is checked positionally against the call's arguments, a final `...` allowing
further arguments; a disagreement, a non-final `...`, and a type the model does
not read are refused by name.  The written type has no field of its own, because
a symbol is resolved by the environment rather than by the module, so the call's
*result kind* is not checked against the module: `call void @f` naming a callee
that returns a value is accepted and the value is discarded, and `%d = call i32
@g` naming a callee that returns nothing is accepted with `%d` bound to whatever
the environment's outcome carries — `CallOutcome.ret` is a value, so an
environment that models a returning-nothing callee must still supply one, and
nothing here can tell that it did.

A pointer comparison is written `icmp <pred> ptr <a>, <b>`.  It compares the two
addresses as unsigned naturals: `eq` and `ne` are address equality, and
`ult`/`ule`/`ugt`/`uge` the unsigned order.  LLVM also defines the signed order
over its 64-bit pointer value, but this model's address is an unbounded `Nat`
with no sign, so the signed reading is not representable here: `slt`, `sle`,
`sgt` and `sge` on pointers are refused by name as a fragment restriction.  An
operand the function's register table says is not a pointer is refused by name
too — the mixed comparison LLVM's verifier also refuses.

An argument list is read to the `)` that closes it, counting the groups nested
inside, and split at the commas that are not inside one, so a `splat (i8 1)` and
a `<4 x i32>` literal neither end the list nor split an argument.  Each argument
is then read by the operand grammar; an argument attribute (`range(...)`,
`noundef`, …) has no modelled value and is refused by name, with the argument's
position, and a literal vector argument is read at the type its position writes.

A function definition's header may carry linkage, a preemption or visibility
specifier, a DLL storage class and a calling convention before its return type,
named or numbered; those are accepted and dropped, because the model has no
linkage or calling-convention semantics — the `Calls` environment decides which
definition answers and how the call is made.  A return attribute stands in the
same position and is refused.  `icmp`'s `samesign` flag is accepted and dropped:
the modelled predicate is the plain one, and the flag can only *exclude* inputs,
so dropping it models a superset of the text's defined inputs rather than a
narrowing of them.

`phi` is modelled, in the two shapes an emitted body writes: `%d = phi <ty> [
<value>, %<block> ], ...` with at least one entry.  Its type token is required
and compared with every incoming value — a literal is read at that type, and a
register is looked up among the function's parameters and definitions once the
blocks are known — so the type is not decoration.  A `phi` that is not at the head
of its block is refused.  A function that binds one register name twice is
refused too, and so is one that defines a name one of its parameters already
holds: the semantics binds a later definition over an earlier one while the `phi`
type check reads the first, so a module that reused a name would get a defined
meaning from the two readings disagreeing.  The rest is stated where it is met
rather than silently approximated: a `phi` in the entry block is accepted and
selects nothing at run time (the entry block has no predecessor, so the parser is
not asked to play verifier); and an incoming label is not compared with the
function's block list, so an entry naming a block that is not a predecessor is
simply never selected and one naming a block that does not exist is never
selected either.

A predecessor label listed twice is accepted only when both entries write the
same value the same way, and otherwise refused by name.  Identical entries are
the shape clang emits when it merges `switch` arms: both select the same operand,
so first-match — which is what the semantics does — lands on the value the text
gives, and accepting them narrows nothing.  Entries that differ are the other
case: deciding that two different spellings denote one value is not a check this
parser makes, so selecting the first would give a *defined* meaning to text whose
reading depends on that equality.  The criterion is therefore the spelling, and
the refusal names the instruction, the label and both spellings.  By contrast a
label that names no real predecessor is accepted, because selecting nothing is
`ub`, which widens the model's permitted behaviours rather than narrowing them.
-/
import LeanLLVM.Syntax
import LeanLLVM.Printer

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

/-- Parse a type from the token stream: a scalar type token, or `<n x elem>` for
a vector.  The element type is one scalar token, because only integer lanes are
modelled; any other element type is refused by name.  `Ty.render` is the one
type speller, and the refusals name a type the way the printer would write it. -/
def expectTy : P Ty := do
  let o ← P.peek
  match o with
  | some "<" =>
      let _ ← P.next
      let nTok ← P.next
      let n ← match nTok.toNat? with
        | some n => if n = 0 then P.fail "a vector needs at least one lane" else pure n
        | none => P.fail s!"invalid vector lane count '{nTok}'"
      P.expect "x"
      let elemTok ← P.next
      let elem ← match parseTy elemTok with
        | .ok ty => pure ty
        | .error e => P.fail e
      P.expect ">"
      match elem with
      | .int _ => pure (.vec n elem)
      | _ => P.fail s!"vector element type '{elemTok}' is not modelled"
  | _ =>
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
`parseOperand`.  A vector constant has two literal forms: a lane list, which
`parseOperand` reads because it spans several tokens, and `zeroinitializer`,
which is the all-zero vector — the splat of zero exactly, so it is read as one
and the spelling is not kept.  `undef` and `poison` are literals no type
parameter constrains: the constructor carries no type, and `Const.toValue`
refuses both, so reading one at a vector type gives the model no value and is
`ub`. -/
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
  | .vec n (.int w) =>
      if t = "zeroinitializer" then .ok (.splat n w (BitVec.ofNat w 0))
      else if t = "undef" then .ok .undef
      else if t = "poison" then .ok .poison
      else .error s!"unsupported vector constant '{t}': a splat, a lane list or 'zeroinitializer' is read"
  | .vec _ _ =>
      if t = "undef" then .ok .undef
      else if t = "poison" then .ok .poison
      else .error s!"unsupported vector constant '{t}': only integer lanes are modelled"
  | .void => .error "void operand"

/-- The lane value of a splat: an integer literal of exactly width `w`.  `none`
means the token is not such a literal (`undef`, `poison`, `zeroinitializer`, a
register, a malformed literal), which the caller refuses by name.  It reuses
`parseConst`, so a splat accepts the same **integer**-literal grammar a scalar
operand does: `undef` and `poison` are literals a scalar operand accepts and a
splat refuses, because the narrowed constructor cannot hold them.  The width is
recovered because `parseConst` at `.int w` only ever builds an `.int w`. -/
def parseSplatValue (w : Nat) (t : String) : Option (BitVec w) :=
  match parseConst (.int w) t with
  | .ok (.int w' v) => if h : w' = w then some (h ▸ v) else none
  | _ => none

/-- The lanes of a literal vector constant `<i8 34, i8 92, …>`.  The tokens are
the ones after the opening `<`; each lane is written with its element type and
then its integer value, lanes are separated by `,`, and the list is closed by
`>`.  The operand's vector type sizes the list: a lane written at another width
is refused by name, and so is a list that does not write exactly the type's lane
count.  A lane is an integer literal, so `undef` and `poison` in a lane position
are refused by name rather than given a lane value.

The fuel is the number of tokens left, so a malformed list is refused instead of
being recursed into; every step consumes at least one token. -/
def vectorLanes (ty : Ty) (n w : Nat) : Nat → List (BitVec w) → List String →
    Except String (List (BitVec w) × List String)
  | 0, _, _ => .error "internal parser error: vector literal fuel exhausted"
  | _ + 1, _, [] => .error "unterminated vector literal: expected '>'"
  | f + 1, acc, elemTok :: litTok :: rest =>
      match parseTy elemTok with
      | .ok (.int w') =>
          if w' = w then
            match parseSplatValue w litTok with
            | none => .error s!"a vector literal lane must be an integer literal, got '{litTok}'"
            | some v =>
                let acc := v :: acc
                match rest with
                | "," :: more => vectorLanes ty n w f acc more
                | ">" :: more =>
                    if acc.length = n then .ok (acc.reverse, more)
                    else
                      .error s!"a vector literal writes {acc.length} lane(s), but its \
                          operand type {ty.render} has {n}"
                | [] => .error "unterminated vector literal: expected '>'"
                | t :: _ => .error s!"expected ',' or '>' in a vector literal, got '{t}'"
          else
            .error s!"a vector literal lane is written i{w'}, but the operand type's \
                element width is i{w}"
      | .ok _ =>
          .error s!"a vector literal lane must be written with an integer type, got '{elemTok}'"
      | .error _ =>
          .error s!"a vector literal lane must be written with an integer type, got '{elemTok}'"
  | _ + 1, _, _ => .error "incomplete vector literal lane: expected '<type> <literal>'"

/-- Parse an operand at a known type: a register `%x`, a literal, or a `splat`
of a literal at a vector type.  A splat's lane count comes from the operand's
vector type, because the printed form omits it and LLVM's grammar supplies it
from that position.

A lane list `<i8 34, i8 92, …>` is read at a vector operand type too: it spans
several tokens, so it is read here rather than by `parseConst`, and its lane
count and lane width are checked against the operand's type. -/
def parseOperand (ty : Ty) : P Operand := do
  let t ← P.next
  if t.startsWith "%" then pure (.reg t)
  else if t = "splat" then
    let (n, w) ← match ty with
      | .vec n (.int w) => pure (n, w)
      | _ => P.fail "a splat operand requires a vector operand type"
    P.expect "("
    let elemTok ← P.next
    -- One shared refusal for the element type position: whatever the token is
    -- (`ptr`, `void`, a malformed width, `undef` written in place of a type),
    -- the message names it.
    let w' ← match parseTy elemTok with
      | .ok (.int w') => pure w'
      | _ => P.fail s!"a splat element must be an integer type, got '{elemTok}'"
    if w' ≠ w then
      P.fail s!"splat element width i{w'} disagrees with the operand type's element width i{w}"
    else
      let lit ← P.next
      -- One shared refusal for the element value position: a literal that is
      -- not an integer (`undef`, `poison`, `zeroinitializer`, a register, …)
      -- is named, rather than being approximated by a default.
      let v ← match parseSplatValue w lit with
        | some v => pure v
        | none => P.fail s!"a splat element must be an integer literal, got '{lit}'"
      P.expect ")"
      pure (.imm (.splat n w v))
  else if t = "<" then
    -- A literal vector constant, whose operand type supplies the lane count and
    -- the element width.  The refusal for a non-vector type is separate from the
    -- lane reader's, so a `<…>` written where a scalar belongs names that.
    let (n, w) ← match ty with
      | .vec n (.int w) => pure (n, w)
      | _ =>
          P.fail s!"a vector literal operand requires an integer-lane vector operand \
              type, got {ty.render}"
    let ls ← fun ts => vectorLanes ty n w (ts.length + 1) [] ts
    pure (.imm (.vector w ls))
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

/-- A binary operation.  The vector form is lane-wise and is modelled only for
the operations the classifier is emitted with; the rest are refused on vectors
by name. -/
def parseBinop (dst : String) (bop : BinOp) : P Stmt := do
  let ty ← expectTy
  match ty with
  | .int w =>
      let a ← parseOperand ty
      P.expect ","
      let b ← parseOperand ty
      pure (.instr (.binop dst bop w a b))
  | .vec n (.int w) =>
      match bop with
      | .or | .and | .xor | .add | .sub | .shl | .lshr =>
          let a ← parseOperand ty
          P.expect ","
          let b ← parseOperand ty
          pure (.instr (.binopVec dst bop n w a b))
      | _ => P.fail s!"'{bop.render}' on a vector type is not modelled"
  | _ => P.fail "binary operation on a non-integer type"

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

/-- Consume a call's arguments up to the `)` that closes the group already open,
counting the groups nested inside it: an argument may write a `splat (i8 1)` or a
`<4 x i32>` vector literal, and each of those carries its own closer.  Reading to
the first `)` instead would end the list inside such an argument and report the
rest as trailing tokens, which names nothing the reader can act on. -/
def P.takeCallArgs : P (List String) := fun ts =>
  let rec go : List String → Nat → List String →
      Except String (List String × List String)
    | [], _, _ => .error "unterminated call argument list: expected ')'"
    | ")" :: rest, 0, acc => .ok (acc.reverse, rest)
    | ")" :: rest, n + 1, acc => go rest n (")" :: acc)
    | "(" :: rest, n, acc => go rest (n + 1) ("(" :: acc)
    | "<" :: rest, n, acc => go rest (n + 1) ("<" :: acc)
    | ">" :: rest, n + 1, acc => go rest n (">" :: acc)
    | t :: rest, n, acc => go rest n (t :: acc)
  go ts 0 []

/-- The token sequences between the commas of a call's argument list, skipping
the commas that are inside a nested group: a vector literal writes `<i8 1, i8 2>`
and an attribute writes `range(i64 0, 65)`, and neither comma separates
arguments. -/
def splitCallArgs (toks : List String) : List (List String) :=
  let step : Nat × List (List String) × List String → String →
      Nat × List (List String) × List String
    | (d, acc, cur), t =>
        if t = "," ∧ d = 0 then (d, cur.reverse :: acc, [])
        else
          let d :=
            if t = "(" ∨ t = "<" ∨ t = "[" then d + 1
            else if t = ")" ∨ t = ">" ∨ t = "]" then (if d = 0 then 0 else d - 1)
            else d
          (d, acc, t :: cur)
  match toks.foldl step (0, [], []) with
  | (_, acc, cur) => (cur.reverse :: acc).reverse

/-- Tokens that introduce a call argument's attribute, as in `ptr noundef %p` or
`i64 range(i64 0, 65) %n`.  An attribute constrains the argument's value and no
field here reads the constraint, so it is refused by name rather than dropped.
The set is closed; a token outside it reaches the operand grammar, which names
whatever it could not read. -/
def callArgAttributes : List String :=
  ["noundef", "nonnull", "align", "dereferenceable", "dereferenceable_or_null",
   "range", "signext", "zeroext", "inreg", "byval", "byref", "preallocated",
   "sret", "elementtype", "noalias", "nocapture", "immarg", "returned",
   "swiftself", "swiftasync", "nofpclass", "allocalign", "allocptr",
   "alignstack", "inalloca", "nest"]

/-- Parse one argument of a call from the tokens between two commas.  A failure
names the argument's position, and an attribute names itself and says what it
constrains. -/
def parseCallArg (idx : Nat) (toks : List String) : Except String (Ty × Operand) :=
  match toks with
  | [] => .error s!"argument {idx} of a call is empty"
  | _ =>
      match toks.find? (fun t => callArgAttributes.contains t) with
      | some a =>
          .error s!"argument {idx} of a call carries the attribute '{a}', which is \
              not modelled: it constrains the argument's value and no field here \
              reads the constraint"
      | none =>
          match P.runExact parseTypedOperand toks with
          | .ok a => .ok a
          | .error e => .error s!"in call argument {idx}: {e}"

/-- Parse a call's argument list from the tokens between the parentheses.  The
positions in a refusal are 1-based, so they count the way the text does. -/
def parseCallArgs (toks : List String) : Except String (List (Ty × Operand)) :=
  let chunks := match splitCallArgs toks with
    | [[]] => []   -- `()`
    | chunks => chunks
  let rec go : Nat → List (List String) → Except String (List (Ty × Operand))
    | _, [] => .ok []
    | i, c :: cs =>
        match parseCallArg i c with
        | .error e => .error e
        | .ok a =>
            match go (i + 1) cs with
            | .error e => .error e
            | .ok rest => .ok (a :: rest)
  go 1 chunks

/-- Read a written callee function type's parameter list into types and a
variadic flag.  The tokens are the ones between the type's parentheses, and a
`...` is a variadic marker that must be last.  The list is read rather than
dropped because it is checked against the call's arguments; a type the model
does not read is refused by name, which is the only way the written type can
still make the text unreadable. -/
def parseCallParamTypes (toks : List String) : Except String (List Ty × Bool) :=
  let chunks := match splitCallArgs toks with
    | [[]] => []   -- `()`
    | chunks => chunks
  let rec go : List (List String) → Except String (List Ty × Bool)
    | [] => .ok ([], false)
    | ["..."] :: [] => .ok ([], true)
    | ["..."] :: _ :: _ =>
        .error "a variadic marker '...' must be the last parameter type of a \
            written callee signature"
    | c :: cs =>
        match P.runExact expectTy c with
        | .error e => .error s!"in the written callee type: {e}"
        | .ok ty =>
            match go cs with
            | .error e => .error e
            | .ok (tys, variadic) => .ok (ty :: tys, variadic)
  go chunks

/-- Check a written callee function type against the call's argument types,
positionally.  A final `...` admits any number of further arguments past the
fixed prefix.  The check refuses only text LLVM's verifier also refuses, so it
cannot narrow the fragment: it keeps a written type that disagrees with the
arguments from being read as if the model had silently retyped the call. -/
def checkCallParamTypes (callee : String) (sig : List Ty × Bool)
    (args : List (Ty × Operand)) : Except String Unit :=
  let written := sig.1.length
  let rec go : Nat → List Ty → List (Ty × Operand) → Except String Unit
    | _, [], [] => .ok ()
    | _, [], _ :: _ =>
        if sig.2 then .ok ()
        else .error s!"@{callee} writes {written} parameter type(s) but the call \
            passes {args.length} argument(s)"
    | _, _ :: _, [] =>
        .error s!"@{callee} writes {written} parameter type(s) but the call passes \
            {args.length} argument(s)"
    | i, ty :: rest, (aty, _) :: arest =>
        if ty = aty then go (i + 1) rest arest
        else .error s!"argument {i} of the call to @{callee} is written {aty.render}, \
            but the callee's written function type gives {ty.render} at that position"
  go 1 sig.1 args

/-- The five intrinsic spellings the fragment models, checked at the symbol,
arity, operand-type and immediate positions.

The generic `call` path checks none of these: it reads any callee name and any
argument list, so without this check a three-argument `pshuf.b`, a `pclmulqdq`
at an immediate other than 0, a `pext.32` and a `ctlz` with the flag `i1 true`
would all parse while meaning nothing here.  Each refusal names the intrinsic it
refused, and the accepted form is the one the emission uses:

* `llvm.x86.avx2.pshuf.b`: `<32 x i8> (<32 x i8>, <32 x i8>)` — two operands,
  the table then the control;
* `llvm.x86.pclmulqdq`: `<2 x i64> (<2 x i64>, <2 x i64>, i8 0)`;
* `llvm.x86.bmi.pext.64` and `llvm.x86.bmi.pdep.64`: `i64 (i64, i64)`;
* `llvm.ctlz.i64`: `i64 (i64, i1 false)`.

A call to any other symbol is not this check's business: a callee's meaning is
the `Calls` environment's, and the fixture's own opcode-and-call-target
inventory is what records an unmodelled intrinsic reaching the text.  The
families that do have a modelled reading are refused at every other width or
suffix, by name, rather than left to that record. -/
def checkIntrinsicShape (callee : String) (retTy : Ty)
    (args : List (Ty × Operand)) : Except String Unit :=
  let argTys : List Ty := args.map fun a => a.1
  let shape (n : Nat) (res : Ty) (tys : List Ty) : Except String Unit :=
    if retTy ≠ res then
      .error s!"the intrinsic @{callee} is modelled only at result type \
          {res.render}, got {retTy.render}"
    else if args.length ≠ n then
      .error s!"the intrinsic @{callee} takes exactly {n} argument(s) in the \
          modelled form, got {args.length}"
    else if argTys ≠ tys then
      .error s!"the intrinsic @{callee} is modelled only with the operand types \
          {String.intercalate ", " (tys.map Ty.render)}, got \
          {String.intercalate ", " (args.map fun a => a.1.render)}"
    else .ok ()
  match callee with
  | "llvm.x86.avx2.pshuf.b" =>
      shape 2 (.vec 32 (.int 8)) [.vec 32 (.int 8), .vec 32 (.int 8)]
  | "llvm.x86.pclmulqdq" =>
      match shape 3 (.vec 2 (.int 64))
          [.vec 2 (.int 64), .vec 2 (.int 64), .int 8] with
      | .error e => .error e
      | .ok _ =>
          match args with
          | [(_, _), (_, _), (_, .imm (.int 8 v))] =>
              if v.toNat = 0 then .ok ()
              else
                .error s!"the intrinsic @llvm.x86.pclmulqdq is modelled only at \
                    immediate 0, got i8 {v.toNat}: the model pins lane 0's \
                    product and lane 1 as zero, which is the imm-0 case only"
          | _ =>
              .error "the intrinsic @llvm.x86.pclmulqdq's third argument must be \
                  the immediate i8 0"
  | "llvm.x86.bmi.pext.64" =>
      shape 2 (.int 64) [.int 64, .int 64]
  | "llvm.x86.bmi.pdep.64" =>
      shape 2 (.int 64) [.int 64, .int 64]
  | "llvm.ctlz.i64" =>
      match shape 2 (.int 64) [.int 64, .int 1] with
      | .error e => .error e
      | .ok _ =>
          match args with
          | [(_, _), (_, .imm (.int 1 f))] =>
              if f.toNat = 0 then .ok ()
              else
                .error "the intrinsic @llvm.ctlz.i64 is modelled only with the \
                    flag i1 false: the flag i1 true promises an undefined result \
                    at zero, and this model has no poison"
          | _ =>
              .error "the intrinsic @llvm.ctlz.i64's second argument must be the \
                  immediate i1 false"
  | s =>
      if s.startsWith "llvm.x86.bmi.pext." then
        .error s!"the intrinsic @{s} is not modelled: the pext model is the \
            64-bit reading, @llvm.x86.bmi.pext.64"
      else if s.startsWith "llvm.x86.bmi.pdep." then
        .error s!"the intrinsic @{s} is not modelled: the pdep model is the \
            64-bit reading, @llvm.x86.bmi.pdep.64"
      else if s.startsWith "llvm.ctlz." then
        .error s!"the intrinsic @{s} is not modelled: only @llvm.ctlz.i64 with \
            the flag i1 false is"
      else if s.startsWith "llvm.x86.avx2.pshuf." then
        .error s!"the intrinsic @{s} is not modelled: only \
            @llvm.x86.avx2.pshuf.b is"
      else .ok ()

/-- The call instruction, with or without a destination register:
`[<dst> =] [tail] call <retTy> [<function type>] @<callee>(<args>)`.

`tail` is accepted and dropped.  It asserts something about the caller's frame —
that the callee may reuse it — and the model has none of the machinery it is
about: no ABI, no stack discipline, no caller or callee frame.  A call's meaning
here is entirely the `Calls` environment's: it receives the callee's symbol, the
argument values, the caller's memory and the allocator cursor, and returns what
the callee leaves.  The marker changes none of those, so there is nothing for it
to affect.

A call written without a destination binds no register: `call void @f(...)` is
the `void` form, and the instruction carries no destination and no name a later
instruction could read.  A discarded non-`void` result is refused by name — the
text would name no place for a value the call still produces, and the model has
no constructor that discards a typed result.  The other direction is refused too:
`%d = call void @f(...)` names a value a `void` call does not produce.

LLVM writes a callee's function type between the return type and the symbol, as
in `call i32 (i32) @g(i32 1)`, and a variadic callee is one instance of it.  The
type has no field in the AST — the callee is resolved by the environment, which
keys on the symbol and carries no type — but it is not ignored: its parameter
list is checked positionally against the call's arguments, with a final `...`
admitting any number of further arguments.  A disagreement, a non-final `...`,
and a type the model does not read are all refused by name.  The check refuses
only text LLVM's verifier refuses, so accepting the type does not widen what the
model reads, and it keeps a written type that disagrees with the arguments from
silently retyping the call in the reader's mind.

The return type is the call's own `retTy` and is used: it is the type the
destination is bound at, which is what `Instr.resultTy` reports to the `phi`
check and to `Function.regType`.

The callee's **result kind** is not checked against the module, because a symbol
is resolved by the environment rather than by the module.  Two consequences,
stated rather than implied: `call void @f` naming a callee that returns a value
is accepted and the value is discarded; and `%d = call i32 @g` naming a callee
that returns nothing is accepted with `%d` bound to whatever the environment's
outcome carries — `CallOutcome.ret` is a value, so an environment that models a
callee returning nothing must still supply one, and nothing here can tell that
it did.

The five intrinsic symbols the fragment models are the exception to that
openness: `checkIntrinsicShape` validates each one's symbol, arity, operand
types and immediate, so a `pshuf.b` of the wrong arity, a `pclmulqdq` at an
immediate other than 0, a `pext.32`, a `pdep.32` and a `ctlz` with the flag
`i1 true` are refused by name instead of reaching the semantics as calls no
environment can resolve meaningfully.  Any other callee is still resolved by
the environment alone. -/
def parseCall (dst : Option String) : P Stmt := do
  let retTy ← expectTy
  let first ← P.next
  let (callee, writtenSig) ←
    if first = "(" then
      let tyToks ← P.takeUntil ")"
      let sig ← match parseCallParamTypes tyToks with
        | .ok s => pure s
        | .error e => P.fail e
      let nameTok ← P.next
      if nameTok.startsWith "@" then
        pure ((nameTok.drop 1).toString, some sig)
      else
        P.fail s!"expected the callee's symbol after its written function type, \
            got '{nameTok}'"
    else pure ((if first.startsWith "@" then (first.drop 1).toString else first), none)
  P.expect "("
  let toks ← P.takeCallArgs
  match parseCallArgs toks with
  | .error e => P.fail s!"in the arguments of @{callee}: {e}"
  | .ok args =>
      let _ ←
        match writtenSig with
        | some sig =>
            match checkCallParamTypes callee sig args with
            | .error e => P.fail e
            | .ok u => pure u
        | none => pure ()
      let _ ←
        match checkIntrinsicShape callee retTy args with
        | .error e => P.fail e
        | .ok u => pure u
      match dst with
      | some d =>
          if retTy = .void then
            P.fail s!"a call of void has no result for '{d}' to name"
          else pure (.instr (.call d retTy callee args))
      | none =>
          if retTy = .void then pure (.instr (.callVoid callee args))
          else
            P.fail s!"a call with no destination register is accepted only when it \
                returns void; this one returns {retTy.render}"

/-- One incoming entry of a `phi` as the parser reads it: the predecessor label,
the operand, and the tokens the value was written with.  The tokens are kept
because a repeated label is accepted only when both entries spell the same value
the same way, and the parsed operand cannot tell `5` from `0x5`. -/
structure PhiEdge where
  /-- The predecessor block name, with its `%` stripped. -/
  label : String
  /-- The incoming operand, read at the instruction's type. -/
  value : Operand
  /-- The value's tokens, in the order they were written. -/
  spelled : List String

/-- Parse one `phi` incoming entry: `[ <value>, %<block> ]`.  The value is read
at the instruction's type, because LLVM's text leaves it untyped there; the
label is a block name with its `%` stripped, as branch targets are.

The entry is split at the comma that separates the value from the label, not at
the first comma: a literal vector value writes its own commas
(`<i64 1, i64 2>`), and splitting at the first one would report a well-formed
entry as malformed.  The splitter is the call-argument one, which already skips
the commas inside `(`, `<` and `[`. -/
def parsePhiEntry (ty : Ty) : P PhiEdge := do
  P.expect "["
  let toks ← P.takeUntil "]"
  match splitCallArgs toks with
  | [vToks, [labelTok]] =>
      let label := if labelTok.startsWith "%" then (labelTok.drop 1).toString else labelTok
      match P.runExact (parseOperand ty) vToks with
      | .error e => P.fail s!"in a phi incoming value: {e}"
      | .ok v => pure ⟨label, v, vToks⟩
  | _ => P.fail "a phi incoming entry must be written '[ <value>, %<block> ]'"

/-- The incoming entries of a `phi`, in order.  The fuel is the token count, so
each recursion consumes a token even when an entry is length-checked rather than
recursed into. -/
def phiEntries (ty : Ty) (fuel : Nat) (acc : List PhiEdge) (ts : List String) :
    Except String (List PhiEdge × List String) :=
  match fuel with
  | 0 => .error "internal parser error: phi incoming fuel exhausted"
  | n + 1 =>
      match parsePhiEntry ty ts with
      | .error e => .error e
      | .ok (e, rest) =>
          match rest with
          | "," :: rest' => phiEntries ty n (e :: acc) rest'
          | _ => .ok ((e :: acc).reverse, rest)

/-- Accept a `phi` that names a predecessor block twice only when both entries
write the same value the same way, and refuse the rest by name.  The check is
local to the incoming list and needs no environment.

A repeated label whose entries are identical is the shape clang emits when it
merges `switch` arms: the entries select the same operand, so taking the first —
which is what the semantics does — lands on the value the text gives, and
accepting the text does not narrow the model.  Entries that differ are not that
case: this parser does not decide that two different spellings denote one value,
and selecting the first would give a defined meaning to text whose reading
depends on that equality, which is the one direction the model must not take.  So
the refusal names the instruction, the label and both spellings.

A label naming no block at all is not checked here — it is simply never selected,
and the step is `ub`, which is conservative. -/
def checkPhiDuplicates (d : String) : List PhiEdge → Except String Unit
  | [] => .ok ()
  | e :: rest =>
      match rest.find? (fun e' => e'.label = e.label) with
      | none => checkPhiDuplicates d rest
      | some e' =>
          if e'.spelled = e.spelled then checkPhiDuplicates d rest
          else
            .error s!"phi {d} lists block '{e.label}' more than once with different \
                incoming values ('{String.intercalate " " e.spelled}' and \
                '{String.intercalate " " e'.spelled}'): a repeated predecessor is \
                accepted only when both entries write the same value the same way, \
                since this parser does not decide that two spellings denote one value"

/-- Parse a `phi`'s incoming list.  At least one entry is required: LLVM's
grammar has no empty incoming list. -/
def parsePhiIncoming (ty : Ty) : P (List PhiEdge) := fun ts =>
  match phiEntries ty (ts.length + 1) [] ts with
  | .error e => .error e
  | .ok r => .ok r

/-- The type an instruction's destination is bound at, when it binds one.  This
is what lets the parser compare a `phi`'s type with a register its incoming list
names; `store` and a `void` call bind nothing, so they have no type here. -/
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

/-- The type a register is bound at in a function: its parameter type, or the
result type of the first instruction that defines it.  A name is bound at most
once, because `checkDefinitions` refuses a repeat, so the first definition is the
only one and this table agrees with the semantics' reading of the environment
(`State.bind` prepends and `lookupName` reads the head, so the last binding is the
one in force — the two coincide only while no name is bound twice).  A name the
function neither takes as a parameter nor defines has no type here. -/
def Function.regType (f : Function) (n : String) : Option Ty :=
  match lookupName f.params n with
  | some ty => some ty
  | none =>
      let rec go : List Block → Option Ty
        | [] => none
        | b :: bs =>
            match (b.instrs.filterMap fun i =>
                match i.dst? with
                | some d => if d = n then i.resultTy else none
                | none => none).head? with
            | some ty => some ty
            | none => go bs
      go f.blocks

/-- Compare a `phi`'s type with every incoming operand.  A literal has already
been read at that type by the operand grammar; a register is looked up among the
function's parameters and definitions, and one bound at another type — or bound
at no type at all — is refused by name. -/
def checkPhiIncoming (f : Function) (blockName d : String) (ty : Ty) :
    List (String × Operand) → Except String Bool
  | [] => .ok true
  | (_, .imm _) :: rest => checkPhiIncoming f blockName d ty rest
  | (_, .reg n) :: rest =>
      match f.regType n with
      | some ty' =>
          if ty' = ty then checkPhiIncoming f blockName d ty rest
          else .error s!"phi {d} in block '{blockName}' has type {ty.render} but its \
              incoming value {n} has type {ty'.render}"
      | none =>
          .error s!"phi {d} in block '{blockName}' reads {n}, which @{f.name} neither \
              takes as a parameter nor defines"

/-- Refuse a function that binds one register name twice: a definition repeated
anywhere, or a definition reusing a parameter's name.

This is the duplicate-labelled-edge problem in another costume, and it is
refused for the same reason.  The semantics binds a *later* definition over an
earlier one (`State.bind` prepends and `lookupName` reads the head), while the
`phi` type check above reads the *first* definition in program order; a module
that reused a name — which SSA forbids and LLVM's verifier rejects — would
therefore get a defined meaning from the disagreement between the two readings,
which is the one direction the model must not take.  A name that is bound once is
read the same way by both, so refusing repeats keeps them in step. -/
def checkDefinitions (f : Function) : Except String Unit :=
  let rec go : List String → Except String Unit
    | [] => .ok ()
    | n :: rest =>
        if rest.contains n then
          .error s!"@{f.name} defines {n} more than once: a register name must be \
              bound once, since a later binding would shadow the earlier one"
        else if f.params.any fun p => p.1 = n then
          .error s!"@{f.name} defines {n}, which is also one of its parameters: a \
              parameter and a definition may not share a name"
        else go rest
  go f.definedNames

/-- Check every `phi` of a function.  The parser does not build a full type
environment, so this runs once the blocks are known; it is the check that makes
the instruction's type field mean something rather than decorate the text. -/
def checkPhiTypes (f : Function) : Except String Unit :=
  match f.blocks.allM fun b =>
      b.instrs.allM fun i =>
        match i with
        | .phi d ty inc => checkPhiIncoming f b.name d ty inc
        | _ => .ok true with
  | .error e => .error e
  | .ok _ => .ok ()

/-- Check one operand of a pointer comparison: it must be a pointer.  The
instruction's type says `ptr`, and the function's register table says what a
named operand is bound at; the pointer grammar admits only the `null` literal as
an immediate.  A mixed comparison is refused here, by name, because LLVM's
verifier refuses the same module — and accepting it would leave the semantics'
`none` to stand for a text the parser could have judged. -/
def checkICmpPtrOperand (f : Function) (d pos : String) : Operand → Except String Bool
  | .imm .null => .ok true
  | .imm _ =>
      .error s!"icmp {d} compares a pointer with an integer literal: a pointer and \
          an integer are not comparable"
  | .reg n =>
      match f.regType n with
      | some .ptr => .ok true
      | some ty =>
          .error s!"icmp {d} has type ptr but its {pos} operand {n} has type \
              {ty.render}: a pointer and an integer are not comparable"
      | none =>
          .error s!"icmp {d} reads {n}, which @{f.name} neither takes as a \
              parameter nor defines"

/-- Check every pointer comparison of a function.  This runs once the blocks and
the register table are known, like the `phi` type check. -/
def checkICmpPtrTypes (f : Function) : Except String Unit :=
  match f.blocks.allM fun b =>
      b.instrs.allM fun i =>
        match i with
        | .icmpPtr d _ a b => do
            let _ ← checkICmpPtrOperand f d "left" a
            checkICmpPtrOperand f d "right" b
        | _ => .ok true with
  | .error e => .error e
  | .ok _ => .ok ()

/-- The entry list of a `shufflevector` mask, read after its opening `<`: one
`i32 <literal>` per entry, the list closed by `>`.  An entry is a decimal or
`0x` integer naming a source lane, so `undef` and `poison` are refused by name —
the model has no poison and the mask field is a list of naturals — and an entry
at or past `2n` is refused with the bound it crossed.  The caller checks the
entry count against the mask type's lane count. -/
def shuffleMaskEntries (n : Nat) : P (List Nat) := fun ts =>
  let rec go (acc : List Nat) : List String → Except String (List Nat × List String)
    | [] => .error "unterminated shufflevector mask: expected '>'"
    | ">" :: rest => .ok (acc.reverse, rest)
    | elemTok :: litTok :: rest =>
        match parseTy elemTok with
        | .ok (.int 32) =>
            let entry : Except String Nat :=
              if litTok = "undef" || litTok = "poison" then
                .error s!"a shufflevector mask entry '{litTok}' is not modelled: \
                    the model has no poison, so every entry must name a source lane"
              else
                match parseNat litTok with
                | some k =>
                    if k < 2 * n then .ok k
                    else
                      .error s!"a shufflevector mask entry {k} is at or past \
                          2n = {2 * n}, the lane count of the two {n}-lane \
                          operands: the model has no poison to give that entry"
                | none =>
                    .error s!"a shufflevector mask entry must be an i32 integer \
                        literal or undef, got '{litTok}'"
            match entry with
            | .error e => .error e
            | .ok k =>
                match rest with
                | "," :: more => go (k :: acc) more
                | ">" :: more => .ok ((k :: acc).reverse, more)
                | [] => .error "unterminated shufflevector mask: expected '>'"
                | t :: _ =>
                    .error s!"expected ',' or '>' in a shufflevector mask, got '{t}'"
        | _ =>
            .error s!"a shufflevector mask entry must be written with i32, got \
                '{elemTok}'"
    | [_] => .error "incomplete shufflevector mask entry: expected '<i32> <value>'"
  go [] ts

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
      -- `samesign` is accepted and dropped.  The modelled predicate is the plain
      -- one, and the flag can only *exclude* inputs — a comparison whose operands
      -- differ in sign is poison under it — so dropping it models a superset of
      -- the text's defined inputs rather than a narrowing of them.  No theorem
      -- here hypothesises the flag: `evalICmp` has no field for it, so every
      -- statement about `icmp` is about the plain predicate it reduces to.
      let _ ← P.optional "samesign"
      let predTok ← P.next
      let pred ← match parseIPred predTok with
        | .ok p => pure p
        | .error e => P.fail e
      let ty ← expectTy
      match ty with
      | .int w =>
          let a ← parseOperand ty
          P.expect ","
          let b ← parseOperand ty
          pure (.instr (.icmp dst pred w a b))
      | .vec n (.int w) =>
          -- Only the two predicates the classifier is emitted with are
          -- modelled lane-wise; the signed and remaining unsigned predicates
          -- are refused by name.
          match pred with
          | .eq | .ult =>
              let a ← parseOperand ty
              P.expect ","
              let b ← parseOperand ty
              pure (.instr (.icmpVec dst pred n w a b))
          | _ => P.fail s!"icmp {predTok} on a vector type is not modelled"
      | .ptr =>
          -- A pointer is compared by address.  Equality and the unsigned order
          -- are modelled; the signed order is defined by LLVM over the 64-bit
          -- pointer value but is not representable over this model's unbounded
          -- `Nat` address, which has no sign, so `slt`, `sle`, `sgt` and `sge`
          -- are refused by name as a fragment restriction.  Whether both
          -- operands really are pointers is checked once the function's
          -- register types are known.
          match pred with
          | .eq | .ne | .ult | .ule | .ugt | .uge =>
              let a ← parseOperand ty
              P.expect ","
              let b ← parseOperand ty
              pure (.instr (.icmpPtr dst pred a b))
          | _ =>
              P.fail s!"icmp {predTok} on a pointer type is not modelled: the \
                  model's address is an unbounded Nat with no sign, so the signed \
                  order over a 64-bit pointer is not representable here; only eq, \
                  ne, ult, ule, ugt and uge are modelled on pointers"
      | .void => P.fail "icmp on a void type is not modelled"
      | .vec _ _ => P.fail "icmp on a vector of non-integer lanes is not modelled"
  | "select" =>
      let (condTy, c) ← parseTypedOperand
      P.expect ","
      let (ty, a) ← parseTypedOperand
      P.expect ","
      let (_, b) ← parseTypedOperand
      if condTy ≠ .int 1 then P.fail "select condition must be i1"
      else if let .vec _ _ := ty then P.fail "select of a vector value is not modelled"
      else pure (.instr (.select dst ty c a b))
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
      if let .vec _ _ := ty then P.fail "alloca of a vector type is not modelled"
      else pure (.instr (.alloca dst ty align))
  | "load" =>
      let ty ← expectTy
      P.expect ","
      let (_, p) ← parseTypedOperand
      pure (.instr (.load dst ty p))
  | "bitcast" =>
      -- Two modelled reinterpretations.  A mask pack is `<n x i1>` to the
      -- `n`-bit integer whose bit `k` is lane `k`; a vector reinterpretation is
      -- any `<n x iw>` to `<m x jw>` at equal total width, which is how the
      -- emission widens `<4 x i64>` to `<32 x i8>`.  Any other pair is refused
      -- with both types named, because a cast the semantics does not model must
      -- not be approximated by a scalar one.
      let tyIn ← expectTy
      let v ← parseOperand tyIn
      P.expect "to"
      let tyOut ← expectTy
      match tyIn, tyOut with
      | .vec n (.int 1), .int m =>
          if m = n then pure (.instr (.bitcastMask dst n v))
          else P.fail s!"bitcast from {tyIn.render} to {tyOut.render} is not modelled"
      | .vec n (.int w), .vec m (.int jw) =>
          if n * w = m * jw then pure (.instr (.vecBitcast dst n w m jw v))
          else
            P.fail s!"bitcast from {tyIn.render} to {tyOut.render} is not \
                modelled: the total bit widths {n * w} and {m * jw} disagree"
      | _, _ => P.fail s!"bitcast from {tyIn.render} to {tyOut.render} is not modelled"
  | "extractelement" =>
      -- `%d = extractelement <n x iw> <vec>, iN <idx>`.  The vector type is the
      -- operand's and fixes the result's element type; the index is read at its
      -- own written integer type, which the instruction does not keep — the
      -- value it reads supplies the count, and the bound is a run-time check.
      -- An index outside the lane range is not a syntax error: LLVM calls it
      -- poison and the model reads it as `ub`.
      let vTy ← expectTy
      let (n, w) ← match vTy with
        | .vec n (.int w) => pure (n, w)
        | _ =>
            P.fail s!"extractelement requires an integer-lane vector operand type, \
                got {vTy.render}"
      let v ← parseOperand vTy
      P.expect ","
      let idxTy ← expectTy
      match idxTy with
      | .int _ => pure ()
      | _ =>
          P.fail s!"extractelement index type '{idxTy.render}' is not modelled: the \
              index must be an integer type"
      let idx ← parseOperand idxTy
      pure (.instr (.extractelement dst n w v idx))
  | "insertelement" =>
      -- `%d = insertelement <n x iw> <vec>, iw <elt>, iN <idx>`.  The element
      -- operand is written with the vector's element type, which is checked
      -- here; the index is read as in `extractelement`, and an index outside the
      -- lane range is `ub` there too.
      let vTy ← expectTy
      let (n, w) ← match vTy with
        | .vec n (.int w) => pure (n, w)
        | _ =>
            P.fail s!"insertelement requires an integer-lane vector operand type, \
                got {vTy.render}"
      let v ← parseOperand vTy
      P.expect ","
      let eltTy ← expectTy
      if eltTy ≠ .int w then
        P.fail s!"insertelement's element operand is written {eltTy.render}, but the \
            vector's element type is i{w}"
      else
        let elt ← parseOperand eltTy
        P.expect ","
        let idxTy ← expectTy
        match idxTy with
        | .int _ => pure ()
        | _ =>
            P.fail s!"insertelement index type '{idxTy.render}' is not modelled: the \
                index must be an integer type"
        let idx ← parseOperand idxTy
        pure (.instr (.insertelement dst n w v elt idx))
  | "shufflevector" =>
      -- `%d = shufflevector <n x iw> %a, <n x iw> %b, <m x i32> <...>`.  The
      -- result has the mask's lane count at the operands' element width; both
      -- operands are written with the same type, and every mask entry is read
      -- by `shuffleMaskEntries`, which refuses an out-of-range or
      -- `undef`/`poison` entry by name.
      let vTy ← expectTy
      let (n, w) ← match vTy with
        | .vec n (.int w) => pure (n, w)
        | _ =>
            P.fail s!"shufflevector requires an integer-lane vector operand type, \
                got {vTy.render}"
      let a ← parseOperand vTy
      P.expect ","
      let vTyB ← expectTy
      if vTyB ≠ vTy then
        P.fail s!"shufflevector's operands must have one type: the first is \
            written {vTy.render}, the second {vTyB.render}"
      else
        let b ← parseOperand vTyB
        P.expect ","
        let maskTy ← expectTy
        let m ← match maskTy with
          | .vec m (.int 32) => pure m
          | _ =>
              P.fail s!"shufflevector's mask must be an '<m x i32>' vector type, \
                  got {maskTy.render}"
        P.expect "<"
        let entries ← shuffleMaskEntries n
        if entries.length ≠ m then
          P.fail s!"a shufflevector mask writes {entries.length} entr(ies), but \
              its mask type {maskTy.render} has {m} lane(s)"
        else
          pure (.instr (.shuffleVec dst n w a b entries))
  | "getelementptr" =>
      -- `getelementptr [inbounds] <elemTy>, ptr %base, iN %off`: one index and an
      -- element type whose allocated size is the stored size the step scales by.
      -- The element token is read as a type first, so an aggregate (`[N x T]`), a
      -- named struct (`%struct.P`) or a vector (`<n x iW>`) is refused by
      -- `parseTy` before this branch decides anything, and that message names
      -- the first token it read (`[`, `%struct.P`, `<`) rather than a whole
      -- type; this branch's non-integer arm therefore sees only `ptr` and
      -- `void`.  An integer width outside `Ty.gepElemAdmitted` is refused here,
      -- by name and with the allocated-versus-stored-size reason: the step
      -- scales by the stored size, so a width where the two differ would give
      -- this model one address and LLVM another.  The other excluded shapes —
      -- the modifiers other than `inbounds`, a base that is not a `ptr`, a
      -- second index, and an index type that is not an integer no wider than 64
      -- bits — are refused by name too.  `inbounds` itself is accepted and
      -- dropped: the instruction has no field for it, and the printer emits it
      -- again.
      let _ ← gepModifiers
      let elemTok ← P.next
      let elemTy ← match parseTy elemTok with
        | .ok ty@(.int w) =>
            if ty.gepElemAdmitted then pure ty
            else
              P.fail s!"getelementptr element width i{w} is not admitted: the step \
                scales by the stored size, and only i1, i7, i8, i16, i32, i64 and \
                i128 are admitted — the widths the model pins as having the same \
                allocated and stored size. A width where the two differ would be \
                given one address here and another by LLVM, and a width the model \
                does not pin is not characterised here; both are refused"
        | .ok _ =>
            P.fail s!"getelementptr element type '{elemTok}' is not modelled: a \
              pointer or void element type has no integer size to scale the index by"
        | .error e => P.fail e
      P.expect ","
      let baseTyTok ← P.next
      if baseTyTok ≠ "ptr" then
        P.fail s!"getelementptr base type '{baseTyTok}' is not modelled: the base must be a ptr"
      let base ← parseOperand .ptr
      P.expect ","
      let idxTok ← P.next
      let w ← match parseTy idxTok with
        | .ok (.int w) => pure w
        | _ => P.fail s!"getelementptr index type '{idxTok}' is not modelled: the index must be an integer type"
      if w > 64 then
        P.fail s!"getelementptr index width i{w} is not modelled: an index wider than 64 bits is refused rather than truncated"
      let off ← parseOperand (.int w)
      match (← P.peek) with
      | some "," => P.fail "getelementptr with more than one index is not modelled"
      | _ => pure ()
      pure (.instr (.gep dst elemTy base off))
  | "call" => parseCall (some dst)
  | "tail" => do
      P.expect "call"
      parseCall (some dst)
  | "phi" =>
      -- `%d = phi <ty> [ <val>, %<block> ], ...`.  LLVM's grammar requires the
      -- type token because an incoming value carries none; the values are read
      -- at that type, so a literal is sized by it and a splat must agree with
      -- its lane width.  A `void` phi has no value and is refused; the function
      -- level type check below compares the type with every incoming register.
      let ty ← expectTy
      if ty = .void then P.fail "a phi of void has no value to select"
      else
        let incoming ← parsePhiIncoming ty
        match checkPhiDuplicates dst incoming with
        | .error e => P.fail e
        | .ok _ =>
            pure (.instr (.phi dst ty (incoming.map fun e => (e.label, e.value))))
  | other => P.fail s!"unsupported instruction '{other}'"
where
  /-- Consume a `getelementptr`'s modifiers.  `inbounds` is accepted and
  dropped, because the instruction has no field for it; `inrange`, `nuw` and
  `nusw` constrain the offset and are refused by name, because no semantics here
  reads them and dropping one would model more programs than the text defines. -/
  gepModifiers : P Unit
    | "inbounds" :: rest => gepModifiers rest
    | f :: rest =>
        if f = "inrange" || f = "nuw" || f = "nusw" then
          .error s!"getelementptr modifier '{f}' is not modelled"
        else .ok ((), f :: rest)
    | [] => .ok ((), [])
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
      -- The modelled vector store is a packed mask: `<n x i1>` whose total
      -- width is a whole number of bytes, the shape the classifier body stores
      -- its comparison result at.  Any other vector value is refused by name,
      -- mask or not — `<32 x i8>` has no byte-packing rule here even though its
      -- total width is whole — and a mask whose width is not whole bytes has no
      -- byte layout at all.
      let (ty, v) ← parseTypedOperand
      P.expect ","
      let (_, p) ← parseTypedOperand
      match ty with
      | .vec n (.int 1) =>
          if n % 8 = 0 then pure (.instr (.store ty v p))
          else
            P.fail s!"store of {ty.render} is not modelled: a mask store's total \
                width of {n} bit(s) is not a whole number of bytes"
      | .vec _ _ =>
          P.fail s!"store of the vector value {ty.render} is not modelled: the \
              modelled vector store is an '<n x i1>' mask whose total width is a \
              whole number of bytes"
      | _ => pure (.instr (.store ty v p))
  | "call" => parseCall none
  | "tail" => do
      P.expect "call"
      parseCall none
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
  -- `seen` records whether a non-`phi` instruction has already been read in this
  -- block.  LLVM requires `phi` nodes to be the first instructions of a basic
  -- block; a `phi` after one has no defined meaning in the model either, because
  -- the block's entry is the only point at which the predecessor is known.
  let rec collect (ls : List (List String)) (acc : List Instr) (seen : Bool) :
      Except String (List Instr × Term × List (List String)) :=
    match ls with
    | [] => .error s!"block '{name}' has no terminator"
    | l :: rest =>
        match parseStmtLine l with
        | .error e => .error s!"in block '{name}': {e}"
        | .ok (.instr i) =>
            if i.isPhi && seen then
              .error s!"in block '{name}': a phi must be the first instructions of its \
                  block, and this one follows a non-phi instruction"
            else collect rest (i :: acc) (seen || !i.isPhi)
        | .ok (.term t) => .ok (acc.reverse, t, rest)
  let (instrs, term, rest) ← collect ls [] false
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

/-- Header tokens a function definition may carry before its return type and the
model does not represent: linkage, the preemption and visibility specifiers, the
DLL storage class, and a calling convention.  They say which definition the
linker picks and how the call is made; the model's `Calls` environment decides
both from outside the module, and there is no linkage or calling-convention
semantics inside it, so dropping them leaves nothing to affect.  The set is
closed: a token outside it is refused, and a return attribute is reported as one.

Every named calling convention clang can emit is here, including the
target-specific ones (`win64cc`, `x86_stdcallcc`, `aarch64_vector_pcs`, …): they
are the same kind of token as `fastcc`, and the reason they are droppable is the
same one — no calling convention is modelled — so leaving a spelling out would
mislabel a call ABI as a property of the returned value.

`cc` is here because a calling convention can be written as a number; the
consumer drops the number with it. -/
def isHeaderSurface (t : String) : Bool :=
  ["private", "internal", "available_externally", "linkonce", "weak", "common",
   "appending", "extern_weak", "linkonce_odr", "weak_odr", "external",
   "dso_local", "dso_preemptable", "default", "hidden", "protected",
   "dllimport", "dllexport",
   "ccc", "fastcc", "coldcc", "tailcc", "swiftcc", "swifttailcc",
   "preserve_mostcc", "preserve_allcc", "preserve_nonecc", "webkit_jscc",
   "anyregcc", "cfguard_checkcc", "ghccc", "cxx_fast_tlscc",
   "x86_stdcallcc", "x86_fastcallcc", "x86_thiscallcc", "x86_vectorcallcc",
   "x86_regcallcc", "x86_64_sysvcc", "win64cc",
   "arm_apcscc", "arm_aapcscc", "arm_aapcs_vfpcc",
   "aarch64_vector_pcs", "aarch64_sve_vector_pcs",
   "aarch64_sme_preservemost_from_x0", "aarch64_sme_preservemost_from_x2",
   "riscv_vector_cc", "msp430_intrcc", "avr_intrcc", "avr_signalcc",
   "ptx_kernel", "ptx_device", "spir_func", "spir_kernel", "intel_ocl_bicc",
   "xcore_call", "hhvmcc", "hhvm_ccc",
   "amdgpu_kernel", "amdgpu_vs", "amdgpu_gs", "amdgpu_ps", "amdgpu_cs",
   "amdgpu_hs", "amdgpu_gfx", "amdgpu_cs_chain", "amdgpu_cs_chain_preserve",
   "amdgpu_gfx_whole_wave"].contains t

/-- Drop the leading header tokens the model does not represent.  What is left is
a return attribute, which the caller refuses by name. -/
def dropHeaderSurface : List String → List String
  | [] => []
  | "cc" :: n :: rest =>
      if (parseNat n).isSome then dropHeaderSurface rest else "cc" :: n :: rest
  | t :: rest => if isHeaderSurface t then dropHeaderSurface rest else t :: rest

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
  -- Linkage, visibility and a calling convention stand between `define` and the
  -- return type and are dropped; a return attribute stands in the same place and
  -- is refused, because it constrains the value the function returns — it is part
  -- of the function's contract, and parsing past it and printing the function
  -- without it would accept a wider contract than the pipeline was given.
  let beforeName := header.takeWhile (· ≠ nameTok)
  let returnAttrs := dropHeaderSurface ((beforeName.drop 1).dropLast)
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
  let f : Function := ⟨name, retTy, params, blocks⟩
  match checkDefinitions f with
  | .error e => throw e
  | .ok _ =>
      match checkPhiTypes f with
      | .error e => throw e
      | .ok _ =>
          match checkICmpPtrTypes f with
          | .error e => throw e
          | .ok _ => .ok (f, rest')

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
