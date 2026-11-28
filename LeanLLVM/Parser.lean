/-
A parser for the subset of textual LLVM IR that the semantics models.

The parser is line oriented: one instruction per line, one label per block.
Unmodelled instructions and block structure are refused with a message naming
the construct, rather than being approximated: aggregates other than the
fixed-length vector, the fixed-length array and the named struct with a declared
extent, and floating point, are not accepted yet.  Of the pointer
arithmetic the modelled part is one index no wider than 64 bits over an element
type whose allocated size is the stored size the step scales by —
`getelementptr [inbounds] <elemTy>, ptr X, iN Y`, with `<elemTy>` one of the
seven integer widths `Ty.gepElemAdmitted` names, a vector of integer lanes
under that predicate's one condition, or a named struct whose extent the
declared `Layout` gives (the `[N x T]` two-index form reduces to the same step
at `T`) — and every other `getelementptr` shape is
refused by name: an element type outside that admission, a base that is not a
`ptr`, a second index, a wider index, and the `inrange`/`nusw` modifiers.
`inbounds` and `nuw` are accepted and dropped, because the instruction has no
field for either and a flag that can only exclude inputs models a superset when
dropped; the printer emits neither, so a parse/print round trip does not add
them.  `nusw` is the signed-wrap flag and stays refused: the model's address
arithmetic is unsigned, so there is nothing for the exclusion to be about.
Of the vector fragment the modelled part is the one an emitted body contains —
`load` of `<n x i8>` and of integer lanes, a `store` of integer lanes whose total
width is a whole number of bytes (the mask store's `<n x i1>` rule at `w = 1`),
the lane-wise `icmp`, the lane-wise `or`/`and`/`xor`/`add`/`sub`, the mask
`bitcast`, the lane accesses `extractelement` and `insertelement`, and both
literal forms a vector constant takes: the `splat` and the lane list
`<i32 1, i32 2>`, with `zeroinitializer` read as the splat of zero, and a lane
list `poison` lane kept in place as the per-lane `vectorPoison` form (a lane
write over it recovers a value; any other use is `ub`) — and the rest of the
vector grammar is refused by name.  A `store`'s value operand is compared
with the written type once the function's register table is known, so a defined
register of another type is refused by name while an undefined one stays
accepted and is `ub` when read.  A lane access's index is read as an unsigned
count and its width is checked and dropped; an index outside the vector's lane
range is not refused here (it is not a syntax error) and is undefined behaviour
at run time, which is what LLVM's poison becomes in this model.  An entry block
may be written without a label — the shape clang emits — and is given one the
body's own tokens do not use; every other block must carry its label.  A
function header — a definition's or a declaration's — is checked for attributes
the semantics does not model.  A *definition's* return attribute before the
return type is read, checked for the shape its name requires and dropped: it can
only exclude return values, so dropping it widens — the reading `icmp`'s
`samesign` gets — and the returned value is the `Calls` environment's outcome,
which the module's text does not fix.  A *declaration's* return attribute is
refused with the rest of its non-modelled header surface, because `Decl` is the
module's own statement of that symbol's interface — its return and parameter
types — so a constraint dropped from it would leave the interface claiming more
than the text does.  The two headers therefore differ on this one attribute,
deliberately: the asymmetry is recorded rather than closed, and
`LeanLLVMTest/Core.lean` pins both sides.  A definition's function-attribute
tail after the parameter list is read attribute by attribute: `local_unnamed_addr`
/ `unnamed_addr` and a function `align N` are dropped, a group reference `#N` is
resolved to its `attributes #N = { ... }` line and every member of the group is
classified the same way, and an attribute the reader has no reading for —
`noreturn` among them — is refused by name.  The three-way split and each
member's reason are at `checkFunctionAttrs`.  A declaration's function-attribute
tail, and a parameter attribute on a declaration, are refused by name too.  A
definition's parameter list is
read as a type, the attributes in front of the name, and the name: an attribute
here is a *caller* obligation rather than a constraint on a result, and the
compiler may have optimised the body on it, so `parseParamAttrs` drops only the
closed set whose obligation the model already reads or whose members are claims
about the emitted body rather than caller obligations, and refuses the caller
obligations it cannot carry
(`nonnull`, `align`, `dereferenceable`, `range`, `nofpclass`, `noalias`), naming
the obligation.  That split, with its reasons, is at `parseParamAttrs`; a
declaration's parameters are read as types, with a parameter name dropped
because `Decl` carries none.  A declaration's variable argument list is refused
by name.  Linkage, visibility and a calling convention before the return type
are accepted and dropped on both, because the model has none of their semantics.

A module's header — `source_filename`, `target datalayout`, `target triple`,
named `%name = type` definitions, globals, attribute groups and metadata nodes —
is read, checked for shape and dropped, because `Module` has no field for any of
it.  One piece is read rather than dropped: a named struct's byte extent is
computed from its fields and the target data layout, because the model carries a
struct's extent and nothing else; where the caller also declares an extent the
two must agree.  A struct may name one defined later in the same header.  The
arithmetic overflow flags `nuw`/`nsw` are accepted and dropped on `add`, `sub`,
`mul` and `shl`, and refused everywhere else, for the same reason a return
attribute is: an operation that wraps under a flag is poison, so dropping it
models a superset of the text's defined inputs.

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
same position and is read, checked and dropped by `checkReturnAttrs`, for the
reason recorded there: it can only exclude return values, so dropping it widens.
`icmp`'s `samesign` flag is accepted and dropped:
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
import LeanLLVM.Binary64
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
  else if s = "double" then .ok .double
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

/-- A declared layout for named structs: the byte extent the target datalayout
gives each `%struct.<name>`.  A caller may supply one; the module's own
`%struct.X = type { ... }` definitions are read too, and their extents are
computed from the fields and the target data layout (see "The module header"
below).  Where both give a name they must agree.  Every access inside a struct
is a byte `getelementptr` at a constant offset, so nothing in the model needs the
fields; a struct with no entry from either source is refused by name. -/
abbrev Layout := List (String × Nat)

/-- Resolve a named struct type to its declared extent.  `t` is the token the
caller already read, `%struct.<name>`; the entry is looked up in the effective
`layout`, and a name with no entry is refused by name rather than given a
guessed extent.  This is the one resolver: `alloca`, an array element and a
`getelementptr` element type all take a struct's extent from it, so the three
readers cannot disagree about what a struct is worth. -/
def resolveStruct (layout : Layout) (t : String) : Except String Ty :=
  let name := (t.drop 8).toString
  match lookupName layout name with
  | some bytes => .ok (.struct name bytes)
  | none =>
      .error s!"named struct '{t}' has no byte extent: the module defines no \
          '%struct.{name} = type' line for it, and the declared layout does not \
          give one either"

/-- Read a named struct type from the token stream.  The token is consumed here
and resolved by `resolveStruct`. -/
def expectStructTy (layout : Layout) : P Ty := do
  let t ← P.next
  match resolveStruct layout t with
  | .ok ty => pure ty
  | .error e => P.fail e

/-- Parse an array type `[N x T]`.  `N` is a positive decimal, and `T` is one
scalar type token — or a named struct, which `resolveStruct` reads against the
declared `layout`.  Either way the element must pass `Ty.gepElemAdmitted`,
because an array's allocated size is its element count times the element's
allocated size, and a disagreement in the element would be a disagreement in the
array.  A nested aggregate is not a single token and is refused by the token
reader that meets it: `[` for a nested array, and anything else `parseTy` does
not read. -/
def expectArrayTy (layout : Layout) : P Ty := do
  P.expect "["
  let nTok ← P.next
  if nTok = "[" then P.fail "a nested array type is not modelled"
  let n ← match nTok.toNat? with
    | some n => if n = 0 then P.fail "an array needs at least one element" else pure n
    | none => P.fail s!"invalid array element count '{nTok}'"
  P.expect "x"
  let elemTok ← P.next
  let elem :=
    if elemTok.startsWith "%struct." then resolveStruct layout elemTok
    else parseTy elemTok
  match elem with
  | .error e => P.fail e
  | .ok elem =>
      P.expect "]"
      if elem.gepElemAdmitted then pure (.array n elem)
      else
        P.fail s!"array element type '{elemTok}' is not admitted: an array's allocated \
            size is its element count times the element's allocated size, so its element \
            must be a type whose allocated and stored sizes agree — the set \
            `Ty.gepElemAdmitted` pins (the integer widths i1, i7, i8, i16, i32, i64 and \
            i128, a whole-byte vector whose packed size is a power of two, and a named \
            struct resolved from the effective layout)"

/-- Parse the type an `alloca` allocates: an array, a named struct resolved from
the effective `layout`, or any scalar type `expectTy` reads.  A named struct
reaches an instruction's type field only as an allocation, an array element or a
`getelementptr` element type; a load, a store, a parameter and a comparison
operand type is still read by `expectTy`, which refuses it, and this reader, the
array reader and the `getelementptr` branch are the three that resolve the name.
The effective layout is the caller's declared one merged with the extents the
module's own `%struct.X = type` definitions compute. -/
def expectAllocaTy (layout : Layout) : P Ty := do
  match (← P.peek) with
  | some "[" => expectArrayTy layout
  | some t =>
      if t.startsWith "%struct." then expectStructTy layout
      else expectTy
  | none => P.fail "unexpected end of line"

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

/-- Split a decimal literal's characters at its exponent marker: the mantissa's
characters and the exponent.  A malformed exponent yields `none`. -/
def splitDecimalExp (cs : List Char) : Option (List Char × Int) :=
  match cs with
  | [] => some ([], 0)
  | c :: rest =>
      if c = 'e' || c = 'E' then
        let es := String.ofList rest
        let es := if es.startsWith "+" then (es.drop 1).toString else es
        match parseInt es with
        | some e => some ([], e)
        | none => none
      else
        match splitDecimalExp rest with
        | none => none
        | some (m, e) => some (c :: m, e)

/-- Read `digits[.digits]` as a significand and the power of ten it is scaled by:
`12.5` is `125` at `-1`. -/
def parseMantissa (cs : List Char) : Option (Nat × Int) :=
  let rec go (cs : List Char) (n : Nat) (scale : Int) (dot : Bool) : Option (Nat × Int) :=
    match cs with
    | [] => some (n, scale)
    | '.' :: rest => if dot then none else go rest n scale true
    | c :: rest =>
        if c.isDigit then
          go rest (n * 10 + (c.toNat - '0'.toNat)) (if dot then scale - 1 else scale) dot
        else none
  go cs 0 0 false

/-- Parse a binary64 literal: a 16-digit `0x` pattern, or a decimal that denotes
an exactly representable binary64.

The pattern is exact for every value, so it is the spelling a refusal names.  A
decimal is read as the exact rational `m * 10 ^ e`, rounded once by `roundMag`;
it is admitted only when that rounding is the identity, because a decimal the
model would have to round is a value the text does not pin to one pattern. -/
def parseDoubleLit (t : String) : Except String (BitVec 64) :=
  if t.startsWith "0x" || t.startsWith "0X" then
    match parseNat t with
    | some n =>
        if n < 2 ^ 64 then .ok (BitVec.ofNat 64 n)
        else .error s!"the hexadecimal literal '{t}' does not fit a binary64 pattern"
    | none => .error s!"invalid hexadecimal floating-point literal '{t}'"
  else
    let neg := t.startsWith "-"
    let body := if neg then (t.drop 1).toString else t
    match splitDecimalExp body.toList with
    | none => .error s!"invalid floating-point literal '{t}': write a decimal or a 0x pattern"
    | some (mcs, e) =>
      match parseMantissa mcs with
      | none => .error s!"invalid floating-point literal '{t}': write a decimal or a 0x pattern"
      | some (m, scale) =>
        let e := e + scale
        if e > 400 || e < -1200 then
          .error s!"the decimal '{t}' is not a finite binary64: write its bit pattern as 0x…"
        else
          let P := if e ≥ 0 then m * 10 ^ e.toNat * 2 ^ 1074 else m * 2 ^ 1074
          let d := if e ≥ 0 then 1 else 10 ^ (-e).toNat
          match roundMag P d with
          | .inf =>
              .error s!"the decimal '{t}' is not a finite binary64: write its bit pattern as 0x…"
          | .fin c =>
              if c.ticks * d = P then .ok (packMag (.fin c) neg)
              else
                .error s!"the decimal '{t}' is not exactly a binary64: write its bit                     pattern as 0x…"

/-- A constant of the given type.  Register operands are parsed by
`parseOperand`.  A vector constant has two literal forms: a lane list, which
`parseOperand` reads because it spans several tokens, and `zeroinitializer`,
which is the all-zero vector — the splat of zero exactly, so it is read as one
and the spelling is not kept.  `undef` and `poison` are literals no type
parameter constrains: the constructor carries no type, and `Const.toValue`
refuses both, so reading one at a vector type gives the model no value and is
`ub`.  A `poison` **lane** of a lane list is the separate `vectorPoison` form,
which keeps the per-lane placement; a lane list with no poison lane is the
`vector` form. -/
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
  | .double =>
      match parseDoubleLit t with
      | .ok b => .ok (.float b)
      | .error e => .error e
  | .array _ _ => .error "an array constant is not modelled"
  | .struct _ _ => .error "a struct constant is not modelled"
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

/-- A vector literal lane value: `none` for the token `poison`, `some v` for an
integer literal of exactly width `w`.  `undef` and every other non-integer token
are refused by name: the model has no nondeterministic value, and no lane write
recovers an `undef` lane as it does a poison one. -/
def parseVectorLane (w : Nat) (t : String) : Except String (Option (BitVec w)) :=
  if t = "poison" then .ok none
  else
    match parseSplatValue w t with
    | some v => .ok (some v)
    | none =>
        .error s!"a vector literal lane must be an integer literal or 'poison', got '{t}'"

/-- The lanes of a literal vector constant `<i8 34, i8 92, …>`.  The tokens are
the ones after the opening `<`; each lane is written with its element type and
then its value, lanes are separated by `,`, and the list is closed by `>`.  The
operand's vector type sizes the list: a lane written at another width is refused
by name, and so is a list that does not write exactly the type's lane count.

A lane value is an integer literal or the token `poison`, which is `none` in the
returned list.  `undef` is refused by name: LLVM gives it a value the compiler
may choose, and this model has no nondeterministic value, while `poison` is
carried because a lane write can cover it (the production stage-2 body writes
over the one poison lane immediately) and the model's lane rule is exactly that
recovery.

The surface admits a poison lane anywhere a vector constant is read, not only
under `insertelement`.  The model gives the two uses different answers: a lane
write that covers the poison lane produces a defined vector (the eight
`insertelement` sites, `probes/install/ir/stage2.production.ll:527` and
siblings), and every other use of the literal is `ub` (`Const.toValue` has no
value-level poison).  The `ub` answer is LLVM's own reading of a poison value
observed, and it is conservative: a path through such an operand proves less,
never something false.  The module's remaining poison lanes are the operands of
`llvm.x86.ssse3.pmadd.ub.sw.128` / `llvm.x86.sse2.pmadd.wd` in the fast decimal
ingest (`:549-550`, `:561-562`, `:664-665`, `:676-677`, `:1201-1202`,
`:1213-1214`, `:1315-1316`, `:1327-1328`, in blocks 316/326, 403/413, 771/781,
857/867).  None of those blocks is reached by the `[1]` certificate: the fast
path requires an eight-byte all-digit window and `[1]` has `]` at its second
byte, so block 296 branches to the slow loop at 338; every pmadd block is
downstream of a successful eight- or sixteen-digit test.  The `insertelement` at
:527 in block 296 is on that path, and its poison lane is overwritten by the
instruction before any read.

The fuel is the number of tokens left, so a malformed list is refused instead of
being recursed into; every step consumes at least one token. -/
def vectorLanes (ty : Ty) (n w : Nat) : Nat → List (Option (BitVec w)) → List String →
    Except String (List (Option (BitVec w)) × List String)
  | 0, _, _ => .error "internal parser error: vector literal fuel exhausted"
  | _ + 1, _, [] => .error "unterminated vector literal: expected '>'"
  | f + 1, acc, elemTok :: litTok :: rest =>
      match parseTy elemTok with
      | .ok (.int w') =>
          if w' = w then
            match parseVectorLane w litTok with
            | .error e => .error e
            | .ok v? =>
                let acc := v? :: acc
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
count and lane width are checked against the operand's type.  A list with no
`poison` lane is the `vector` form; one with a poison lane is `vectorPoison`,
which keeps the lane's position. -/
def parseOperand (ty : Ty) : P Operand := do
  let t ← P.next
  if t.startsWith "%" then pure (.reg t)
  else if t.startsWith "@" then
    -- A global symbol is an address, so it has type `ptr` and nowhere else.
    -- The parser does not ask the module whether the symbol is declared: the
    -- text that names a symbol is not the text that assigns its address, and a
    -- captured `define` block carries the use without the module's global
    -- declarations — the same arrangement `call`'s callee has, which the
    -- environment resolves rather than the module.
    if t.length = 1 then
      P.fail "a global symbol needs a name after '@'"
    else if ty = .ptr then pure (.global t)
    else
      P.fail (s!"a global symbol's value is an address, so it has type ptr: " ++
        s!"'{t}' is written here at type {ty.render}")
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
    if ls.all (fun l => l.isSome) then
      pure (.imm (.vector w (ls.map (fun l => l.getD 0))))
    else pure (.imm (.vectorPoison w ls))
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

/-- Drop the arithmetic overflow flags written before an operation's type.  The
model's arithmetic is wrapping, and either flag can only *exclude* inputs — a
wrap under it is poison — so dropping it models a superset of the text's defined
inputs rather than a narrowing of them.  Only `add`, `sub`, `mul` and `shl` take
the flags; every other operation is read without them and still refuses them as
a type it cannot read. -/
def dropOverflowFlags (fuel : Nat) (ts : List String) : List String :=
  match fuel with
  | 0 => ts
  | fuel + 1 =>
      match ts with
      | "nuw" :: rest => dropOverflowFlags fuel rest
      | "nsw" :: rest => dropOverflowFlags fuel rest
      | _ => ts

/-- Consume and drop the `nuw`/`nsw` flags written before a binary operation's
type. -/
def parseOverflowFlags : P Unit := fun ts =>
  match ts with
  | "nuw" :: rest => .ok ((), dropOverflowFlags 1 rest)
  | "nsw" :: rest => .ok ((), dropOverflowFlags 1 rest)
  | _ => .ok ((), ts)

/-- A binary operation.  The vector form is lane-wise and is modelled only for
the operations the classifier is emitted with; the rest are refused on vectors
by name.  `overflow` says whether the operation is one of the four that take
`nuw`/`nsw`; the flags are read and dropped there and nowhere else. -/
def parseBinop (dst : String) (bop : BinOp) (overflow : Bool) : P Stmt := do
  if overflow then parseOverflowFlags else pure ()
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

/-- The token sequences between the top-level commas of a parenthesised list,
skipping the commas that are inside a nested group: a vector literal writes
`<i8 1, i8 2>` and an attribute writes `range(i64 0, 65)`, and neither comma
separates entries.  A call's argument list, a written callee type, a phi entry
and a declaration's parameter list all read their entries this way. -/
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

/-- The intrinsic spellings the fragment models, checked at the symbol, arity,
operand-type and immediate positions.

The generic `call` path checks none of these: it reads any callee name and any
argument list, so without this check a three-argument `pshuf.b`, a `pclmulqdq`
at an immediate other than 0, a `pext.32`, a `ctpop.i16` and a `ctlz` with the
flag `i1 true` would all parse while meaning nothing here.  Each refusal names
the intrinsic it refused, and the accepted form is the one the emission uses:

* `llvm.x86.avx2.pshuf.b`: `<32 x i8> (<32 x i8>, <32 x i8>)` — two operands,
  the table then the control;
* `llvm.usub.sat.v32i8`: `<32 x i8> (<32 x i8>, <32 x i8>)` — lane-wise
  unsigned saturating subtract, two operands and no flag;
* `llvm.x86.avx.ptestz.256`: `i32 (<4 x i64>, <4 x i64>)` — one when no bit is
  set in both operands, two operands and no flag;
* `llvm.x86.pclmulqdq`: `<2 x i64> (<2 x i64>, <2 x i64>, i8 0)`;
* `llvm.x86.bmi.pext.64` and `llvm.x86.bmi.pdep.64`: `i64 (i64, i64)`;
* `llvm.ctlz.i64`: `i64 (i64, i1 false)`;
* `llvm.ctpop.i32`: `i32 (i32)` and `llvm.ctpop.i64`: `i64 (i64)` — one operand
  and no flag;
* `llvm.cttz.i64`: `i64 (i64, i1 <flag>)`, at **both** flag values.  The flag is
  a literal, not a register, and unlike `ctlz` the `i1 true` value is admitted:
  it promises poison at the zero word, and `BitLanes.cttz`'s docstring states the
  bound that makes the model's determined value there admissible.  `ctlz … i1
  true` has no such bound and stays refused, so the asymmetry is the admission
  rule and not an inconsistency: a spelling is admitted with an obligation that
  bounds its poison, and that one has none;
* `llvm.umin.i32`: `i32 (i32, i32)` — the unsigned minimum, two operands and no
  flag;
* `llvm.x86.sse2.pmadd.wd`: `<4 x i32> (<8 x i16>, <8 x i16>)` — signed word
  multiply-add, two operands and no flag;
* `llvm.x86.ssse3.pmadd.ub.sw.128`: `<8 x i16> (<16 x i8>, <16 x i8>)` —
  unsigned-byte times signed-byte multiply-add, the products summed and widened
  to words, two operands and no flag.

`usub.sat.v32i8` and `ptestz.256` are exact: each states its whole meaning at
the symbol and operand types, and neither carries a flag or poison.  The
poison-flag rule above is therefore not invoked for them — it exists for
`cttz`'s `i1`, and these two spellings have none to bound.

A call to any other symbol is not this check's business: a callee's meaning is
the `Calls` environment's, and the fixture's own opcode-and-call-target
inventory is what records an unmodelled intrinsic reaching the text.  The
families listed above are refused at every other width or suffix, by name, rather
than left to that record.

`umax` at every width is bound by no environment in the tree and called by no
capture under `probes/`, so a call to one is `ub`; the shape check has no rule for
`umax`, so it is unresolved rather than refused by name.  `umin` at any width
other than `i32` is refused by name, and `llvm.umin.i32`,
`llvm.x86.sse2.pmadd.wd` and `llvm.x86.ssse3.pmadd.ub.sw.128` are refused by the
shape rule at another arity, another operand type or another result type. -/
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
  | "llvm.usub.sat.v32i8" =>
      shape 2 (.vec 32 (.int 8)) [.vec 32 (.int 8), .vec 32 (.int 8)]
  | "llvm.x86.avx.ptestz.256" =>
      shape 2 (.int 32) [.vec 4 (.int 64), .vec 4 (.int 64)]
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
  | "llvm.ctpop.i32" =>
      shape 1 (.int 32) [.int 32]
  | "llvm.ctpop.i64" =>
      shape 1 (.int 64) [.int 64]
  | "llvm.cttz.i64" =>
      match shape 2 (.int 64) [.int 64, .int 1] with
      | .error e => .error e
      | .ok _ =>
          match args with
          | [(_, _), (_, .imm (.int 1 _))] => .ok ()
          | _ =>
              .error "the intrinsic @llvm.cttz.i64's second argument must be the \
                  immediate i1 true or i1 false: the flag is a literal, not a \
                  register, and both values are modelled"
  | "llvm.umin.i32" =>
      shape 2 (.int 32) [.int 32, .int 32]
  | "llvm.x86.sse2.pmadd.wd" =>
      shape 2 (.vec 4 (.int 32)) [.vec 8 (.int 16), .vec 8 (.int 16)]
  | "llvm.x86.ssse3.pmadd.ub.sw.128" =>
      shape 2 (.vec 8 (.int 16)) [.vec 16 (.int 8), .vec 16 (.int 8)]
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
      else if s.startsWith "llvm.ctpop." then
        .error s!"the intrinsic @{s} is not modelled: only @llvm.ctpop.i32 and \
            @llvm.ctpop.i64 are, each at its own width and with one operand"
      else if s.startsWith "llvm.cttz." then
        .error s!"the intrinsic @{s} is not modelled: only @llvm.cttz.i64 is, \
            with an immediate i1 flag"
      else if s.startsWith "llvm.x86.avx2.pshuf." then
        .error s!"the intrinsic @{s} is not modelled: only \
            @llvm.x86.avx2.pshuf.b is"
      else if s.startsWith "llvm.usub.sat" then
        .error s!"the intrinsic @{s} is not modelled: the saturating subtract \
            is @llvm.usub.sat.v32i8, at <32 x i8> with two operands"
      else if s.startsWith "llvm.x86.avx.ptest" then
        .error s!"the intrinsic @{s} is not modelled: the zero test is \
            @llvm.x86.avx.ptestz.256, at <4 x i64> with two operands and an \
            i32 result"
      else if s.startsWith "llvm.umin." then
        .error s!"the intrinsic @{s} is not modelled: the unsigned minimum is \
            @llvm.umin.i32, at i32 with two operands"
      else if s.startsWith "llvm.x86.sse2.pmadd." then
        .error s!"the intrinsic @{s} is not modelled: the signed multiply-add \
            is @llvm.x86.sse2.pmadd.wd, at <8 x i16> with two operands and a \
            <4 x i32> result"
      else if s.startsWith "llvm.x86.ssse3.pmadd." then
        .error s!"the intrinsic @{s} is not modelled: the unsigned-byte times \
            signed-byte multiply-add is @llvm.x86.ssse3.pmadd.ub.sw.128, at \
            <16 x i8> with two operands and a <8 x i16> result"
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

The intrinsic symbols the fragment models are the exception to that
openness: `checkIntrinsicShape` validates each one's symbol, arity, operand
types and immediate, so a `pshuf.b` of the wrong arity, a `pclmulqdq` at an
immediate other than 0, a `pext.32`, a `pdep.32`, a `ctpop.i16`, a `cttz` whose
flag is not an immediate `i1`, a `ctlz` with the flag `i1 true`, a
`usub.sat.v16i8` (or a `usub.sat` of the wrong arity or operand types), a
`ptest.256` or a `ptestz.128`, an `umin.i64`, and an `umin.i32`, `pmadd.wd` or
`pmadd.ub.sw.128` at another arity, another operand type or another result type
are refused by name instead of reaching the semantics as calls no environment can
resolve meaningfully.  Any other callee is
still resolved by the environment alone; that fall-through is deliberate, and a
call target no environment resolves is `ub` rather than silently read. -/
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

/-- Compare a `phi`'s type with every incoming operand.  A literal has already
been read at that type by the operand grammar; a register is looked up among the
function's parameters and definitions, and one bound at another type — or bound
at no type at all — is refused by name. -/
def checkPhiIncoming (f : Function) (blockName d : String) (ty : Ty) :
    List (String × Operand) → Except String Bool
  | [] => .ok true
  | (_, .imm _) :: rest => checkPhiIncoming f blockName d ty rest
  -- A global symbol is read at `ptr` by the operand grammar, which is the
  -- check's own gate: an incoming value written at any other type never became
  -- one.
  | (_, .global _) :: rest => checkPhiIncoming f blockName d ty rest
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
  -- A global symbol is an address, and `icmpPtr` compares addresses, so this is
  -- the operand's own type rather than a conversion.
  | .global _ => .ok true
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

/-- Check a `ptrtoint`'s source operand against the function's register table: it
must be bound at `ptr`.  The operand grammar reads a register without consulting
its type, so without this check `ptrtoint ptr %q to i64` with `%q` an `i64`
parsed.  A literal is read at the written type by the grammar, and an undefined
register has no type and stays accepted — it is `ub` when read, as everywhere
else. -/
def checkPtrToIntOperand (f : Function) (d : String) : Operand → Except String Bool
  | .imm _ => .ok true
  -- A global symbol's value is an address, so it is a pointer already.
  | .global _ => .ok true
  | .reg n =>
      match f.regType n with
      | some .ptr => .ok true
      | some ty =>
          .error s!"ptrtoint {d} converts {n}, which has type {ty.render}: only a \
              pointer converts to an integer"
      | none => .ok true

/-- Check an `inttoptr`'s source operand: it must be bound at `i64`. -/
def checkIntToPtrOperand (f : Function) (d : String) : Operand → Except String Bool
  | .imm _ => .ok true
  -- Unreachable from text: the operand grammar admits a global symbol only at
  -- `ptr`, so an `i64` source never became one.  A hand-built AST that puts one
  -- here is refused by the semantics' own value-shape test, as a non-integer is.
  | .global _ => .ok true
  | .reg n =>
      match f.regType n with
      | some (.int 64) => .ok true
      | some ty =>
          .error s!"inttoptr {d} converts {n}, which has type {ty.render}: only an \
              i64 converts to an address"
      | none => .ok true

/-- Check one operand of a floating-point instruction against the type the
instruction reads it at.  A literal is read at the written type by the operand
grammar; a register is read without consulting its type, so the check is this
function's job, as it is for `icmp ptr` and `store`. -/
def checkFPOperand (f : Function) (d : String) (expect : Ty) :
    Operand → Except String Bool
  | .imm _ => .ok true
  | .global _ => .ok true
  | .reg n =>
      match f.regType n with
      | some ty =>
          if ty = expect then .ok true
          else
            .error s!"{d} reads {n} at {expect.render}, but {n} has type {ty.render}"
      | none => .ok true

/-- Check every address conversion and floating-point instruction of a function.
This runs once the blocks and the register table are known, like the `phi`,
`icmp ptr` and `store` checks. -/
def checkCastTypes (f : Function) : Except String Unit :=
  match f.blocks.allM fun b =>
      b.instrs.allM fun i =>
        match i with
        | .ptrtoint d v => checkPtrToIntOperand f d v
        | .inttoptr d v => checkIntToPtrOperand f d v
        | .uitofp d wIn v => checkFPOperand f d (.int wIn) v
        | .fmul d a b =>
            match checkFPOperand f d .double a with
            | .error e => .error e
            | .ok _ => checkFPOperand f d .double b
        | .fdiv d a b =>
            match checkFPOperand f d .double a with
            | .error e => .error e
            | .ok _ => checkFPOperand f d .double b
        | .fcmp d _ a b =>
            match checkFPOperand f d .double a with
            | .error e => .error e
            | .ok _ => checkFPOperand f d .double b
        | .fneg d v => checkFPOperand f d .double v
        | .bitcastToInt d v => checkFPOperand f d .double v
        | .bitcastToDouble d v => checkFPOperand f d (.int 64) v
        | _ => .ok true with
  | .error e => .error e
  | .ok _ => .ok ()

/-- Check a `store`'s value operand against the written type, when the operand
names a register the function defines.

The operand grammar reads a register without consulting its type, so before this
check `store i32 %q, ptr %p` with `%q` an `i64` parsed — and the vector widening
would have accepted `store <8 x i32> %q` with `%q` an `i64` and `store <8 x
i64> %v` with `%v` an `<8 x i32>` as well, since their total widths are whole
bytes.  A register bound at another type is refused by name, with both types.

An **undefined** register has no type, so it is not refused here: the run is
`ub` when it is read, which is the model's existing reading of a name the
function neither binds nor takes as a parameter.  A literal is read at the
written type by the operand grammar, so it has no separate type to compare. -/
def checkStoreValue (f : Function) (written : Ty) : Operand → Except String Bool
  | .imm _ => .ok true
  -- The operand grammar admits a global symbol only at `ptr`, and the value
  -- operand is read at the written type, so one that reaches this check is
  -- already the written type's: the check has nothing to add.
  | .global _ => .ok true
  | .reg n =>
      match f.regType n with
      | some ty' =>
          if ty' = written then .ok true
          else
            .error s!"store writes {written.render} but its value operand {n} has \
                type {ty'.render}: a store's value must have the written type"
      | none => .ok true

/-- Check every `store` of a function.  This runs once the blocks and the
register table are known, like the `phi` and `icmp ptr` type checks. -/
def checkStoreValues (f : Function) : Except String Unit :=
  match f.blocks.allM fun b =>
      b.instrs.allM fun i =>
        match i with
        | .store ty v _ => checkStoreValue f ty v
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

/-- Read an optional `, align N` after an instruction's operands, returning the
written alignment or `none` when the text ends there.  The value is checked to be
a decimal natural and then dropped by `alloca` only when it is absent; `load` and
`store` have no field for it, so they accept and discard it — the printer writes
`align 1` for them, the weakest alignment, rather than leave the ABI default to
be assumed (see `LeanLLVM/Printer.lean`).  Any other trailing attribute is
refused by name rather than parsed past. -/
def parseAlignOpt : P (Option Nat) := do
  let more ← P.optional ","
  if more then do
    let kw ← P.next
    if kw = "align" then
      let n ← P.next
      match n.toNat? with
      | some k => pure (some k)
      | none => P.fail s!"invalid alignment '{n}'"
    else P.fail s!"expected 'align' after ',', got '{kw}': an alignment is the \
        only trailing attribute modelled here"
  else pure none

/-- Refuse a fast-math flag by name.  The model's floating point is IEEE 754
binary64 with no flags: a flag permits a transformation the model's arithmetic
does not make, and the capture's `strip_body` does not remove one from an
instruction line, so a flagged instruction reaches the parser and must be named
rather than silently accepted. -/
def noFastMath : P Unit := do
  match (← P.peek) with
  | some t =>
      if t = "fast" || t = "nnan" || t = "ninf" || t = "nsz" || t = "arcp" ||
         t = "contract" || t = "afn" || t = "reassoc" then
        P.fail s!"the fast-math flag '{t}' is not modelled: the model's floating \
            point is IEEE 754 binary64 with no flags"
      else pure ()
  | none => pure ()

/-- Read the type token of a floating-point instruction: `double`, and nothing
else, because binary64 is the only floating-point type modelled. -/
def expectDouble : P Unit := do
  let t ← P.next
  if t = "double" then pure ()
  else
    P.fail s!"'{t}' is not modelled: the only floating-point type read is double \
        (IEEE 754 binary64)"

def parseValueInstr (layout : Layout) (dst : String) : P Stmt := do
  let op ← P.next
  match op with
  | "add" => parseBinop dst .add true
  | "sub" => parseBinop dst .sub true
  | "mul" => parseBinop dst .mul true
  | "udiv" => parseBinop dst .udiv false
  | "sdiv" => parseBinop dst .sdiv false
  | "urem" => parseBinop dst .urem false
  | "srem" => parseBinop dst .srem false
  | "and" => parseBinop dst .and false
  | "or" => parseBinop dst .or false
  | "xor" => parseBinop dst .xor false
  | "shl" => parseBinop dst .shl true
  | "lshr" => parseBinop dst .lshr false
  | "ashr" => parseBinop dst .ashr false
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
      | .array _ _ => P.fail "icmp on an array type is not modelled"
      | .struct _ _ => P.fail "icmp on a struct type is not modelled"
      | .double =>
          P.fail "icmp on a floating-point type is not modelled: a binary64 value \
              is compared with fcmp, whose only modelled predicate is oeq"
  | "select" =>
      -- Two forms share one constructor.  A scalar `i1` condition selects a
      -- whole value; a `<n x i1>` condition selects lane by lane from two
      -- operands of one `<n x iw>` type.  The condition's type is not a field,
      -- because it is exactly `<n x i1>` for a vector result and `i1` for a
      -- scalar one, so the parser reads it and checks it against that rule —
      -- which is what makes the printer's emission re-parse.
      let (condTy, c) ← parseTypedOperand
      P.expect ","
      let (ty, a) ← parseTypedOperand
      P.expect ","
      let (rhsTy, b) ← parseTypedOperand
      match condTy with
      | .int 1 =>
          if let .vec _ _ := ty then
            P.fail "select of a vector value with a scalar i1 condition is not \
                modelled: a vector select needs a <n x i1> condition"
          else if ty ≠ rhsTy then
            P.fail s!"select operands must have the same type, got {ty.render} \
                and {rhsTy.render}"
          else pure (.instr (.select dst ty c a b))
      | .vec n (.int 1) =>
          match ty, rhsTy with
          | .vec m (.int w), .vec m' (.int w') =>
              if m ≠ n then
                P.fail s!"select condition has {n} lanes but its operands have \
                    {m}: a vector select's lane counts must agree"
              else if m' ≠ m then
                P.fail s!"select operands have different lane counts, {m} and \
                    {m'}: a vector select's operands must have the same type"
              else if w' ≠ w then
                P.fail s!"select operands must have the same type, got \
                    <{m} x i{w}> and <{m'} x i{w'}>"
              else pure (.instr (.select dst ty c a b))
          | _, _ =>
              P.fail "select with a <n x i1> condition requires vector operands \
                  of the same lane count"
      | .vec _ _ =>
          P.fail s!"select condition must be <n x i1>, got {condTy.render}: a \
              vector condition's element type must be i1"
      | _ =>
          P.fail s!"select condition must be i1, got {condTy.render}"
  | "trunc" => parseCast dst fun d wi wo v => .trunc d wi wo v
  | "zext" => parseCast dst fun d wi wo v => .zext d wi wo v
  | "sext" => parseCast dst fun d wi wo v => .sext d wi wo v
  | "ptrtoint" =>
      -- `%d = ptrtoint ptr %v to i64`.  The model's pointer is 64 bits, so this
      -- is the one width at which the conversion is exact; the destination is
      -- read and checked rather than kept, because the instruction has no field
      -- for it and the printer emits `i64`.  Any other integer width is refused
      -- by name: a narrower destination truncates an address the model keeps as
      -- an unbounded `Nat`, and a wider one zero-extends a value that is already
      -- 64 bits.
      let tyIn ← expectTy
      if tyIn ≠ .ptr then
        P.fail s!"ptrtoint's source must be ptr, got {tyIn.render}: only an \
            address converts to an integer"
      else
        let v ← parseOperand .ptr
        P.expect "to"
        let tyOut ← expectTy
        match tyOut with
        | .int 64 => pure (.instr (.ptrtoint dst v))
        | .int w =>
            P.fail s!"ptrtoint to i{w} is not modelled: the model's pointer is 64 \
                bits, so an address converts exactly at i64 only"
        | _ =>
            P.fail s!"ptrtoint's result must be an integer type, got {tyOut.render}"
  | "inttoptr" =>
      -- `%d = inttoptr i64 %v to ptr`, the inverse at the same width, with the
      -- same refusal for a source of another width.
      let tyIn ← expectTy
      match tyIn with
      | .int 64 =>
          let v ← parseOperand tyIn
          P.expect "to"
          let tyOut ← expectTy
          if tyOut ≠ .ptr then
            P.fail s!"inttoptr's result must be ptr, got {tyOut.render}: only an \
                integer converts to an address"
          else pure (.instr (.inttoptr dst v))
      | .int w =>
          P.fail s!"inttoptr from i{w} is not modelled: the model's pointer is 64 \
              bits, so the conversion is modelled at i64 only"
      | _ =>
          P.fail s!"inttoptr's source must be an integer type, got {tyIn.render}"
  | "uitofp" =>
      noFastMath
      -- `%d = uitofp iW %v to double`.  The source width is read and kept,
      -- because it is what the run checks the value against; the result type is
      -- fixed, so a written one that is not `double` is refused by name.
      let tyIn ← expectTy
      let wIn ← match tyIn with
        | .int w => pure w
        | _ => P.fail s!"uitofp's source must be an integer type, got {tyIn.render}"
      let v ← parseOperand tyIn
      P.expect "to"
      let tyOut ← expectTy
      if tyOut ≠ .double then
        P.fail s!"uitofp's result must be double, got {tyOut.render}: the only \
            floating-point type modelled is binary64"
      else pure (.instr (.uitofp dst wIn v))
  | "fmul" | "fdiv" =>
      noFastMath
      let _ ← expectDouble
      let a ← parseOperand .double
      P.expect ","
      let b ← parseOperand .double
      pure (.instr (if op = "fmul" then .fmul dst a b else .fdiv dst a b))
  | "fneg" =>
      noFastMath
      let _ ← expectDouble
      let v ← parseOperand .double
      pure (.instr (.fneg dst v))
  | "fcmp" =>
      noFastMath
      let p ← P.next
      let pred ← match p with
        | "oeq" => pure .oeq
        | "false" | "true" | "ord" | "uno" | "ueq" | "une" | "ogt" | "oge"
        | "olt" | "ole" | "one" | "ugt" | "uge" | "ult" | "ule" =>
            P.fail s!"fcmp predicate '{p}' is not modelled: the one predicate read \
                is 'oeq' (ordered and equal)"
        | _ => P.fail s!"unknown fcmp predicate '{p}'"
      let _ ← expectDouble
      let a ← parseOperand .double
      P.expect ","
      let b ← parseOperand .double
      pure (.instr (.fcmp dst pred a b))
  | "alloca" =>
      let ty ← expectAllocaTy layout
      let align ← match (← parseAlignOpt) with
        | some k => pure k
        | none => pure 0
      if let .vec _ _ := ty then P.fail "alloca of a vector type is not modelled"
      else pure (.instr (.alloca dst ty align))
  | "load" =>
      -- `load <ty>, ptr <p>[, align N]`: the alignment is read, checked and
      -- dropped like the `getelementptr` index width, because the instruction
      -- has no field for it.
      let ty ← expectTy
      P.expect ","
      let (_, p) ← parseTypedOperand
      let _ ← parseAlignOpt
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
      | .double, .int 64 => pure (.instr (.bitcastToInt dst v))
      | .int 64, .double => pure (.instr (.bitcastToDouble dst v))
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
      -- The element type is read by `expectTy`, so a vector element type
      -- (`<n x iW>`) is read as the vector it is rather than refused as a token,
      -- and a named struct (`%struct.P`) is resolved by `expectStructTy` from the
      -- declared layout — its extent is both its allocated and stored size, so
      -- the step scales by exactly that number.  An aggregate (`[N x T]`) in
      -- this position still fails in the type reader with `unsupported type`,
      -- naming the token it read (`[`): it is a whole array, and the aggregate
      -- arm below is where an array element is stepped.  `Ty.gepElemAdmitted` is
      -- the admission: the seven integer widths, a vector of integer lanes whose
      -- lane width is a whole
      -- number of bytes and whose packed size is a power of two (`w % 8 = 0` and
      -- `n * w / 8` a power of two, hence at least 1), and a struct resolved
      -- from the declared layout.  A refused
      -- integer width and a refused vector are each refused here, by name and
      -- with the reason — a step scaled by the stored size would give this model
      -- one address and LLVM another, whether the divergence is in the packing
      -- (`<8 x i1>`) or in the allocation (`<4 x i24>`, `<3 x i32>`) — while the
      -- scalar non-integer arm sees only `ptr` and `void`.  The other excluded
      -- shapes — the modifiers other than `inbounds`, a base that is not a
      -- `ptr`, a second index, and an index type that is not an integer no wider
      -- than 64 bits — are refused by name too.  `inbounds` itself is accepted
      -- and dropped: the instruction has no field for it, and the printer emits
      -- an ordinary `getelementptr`, so the round trip adds no promise.
      let _ ← gepModifiers
      -- Two admitted shapes.  The scalar/vector/struct form is the one-index
      -- step whose scale is the element type's size.  The aggregate form is
      -- LLVM's two-index step over `[N x T]`: with a literal 0 leading index its
      -- first term is zero and the second scales by `T`, so the address is the
      -- one-index step at `T`.  The reduction is what the model can express, and
      -- the printer emits the reduced one-index form, which re-parses to the
      -- same AST — including a `[N x %struct.P]` step, whose reduced form is the
      -- struct's own one-index step and which re-parses through this branch's
      -- struct reader.  The leading index is not decoration: a nonzero one has a
      -- whole-array stride this instruction has no term for, so it is refused.
      match (← P.peek) with
      | some "[" =>
          let arr ← expectArrayTy layout
          let elemTy ← match arr with
            | .array _ elem => pure elem
            | _ => P.fail "internal parser error: an array reader returned another type"
          P.expect ","
          let baseTyTok ← P.next
          if baseTyTok ≠ "ptr" then
            P.fail s!"getelementptr base type '{baseTyTok}' is not modelled: the base must be a ptr"
          let base ← parseOperand .ptr
          P.expect ","
          let leadTyTok ← P.next
          let wLead ← match parseTy leadTyTok with
            | .ok (.int w) => pure w
            | _ => P.fail s!"getelementptr leading index type '{leadTyTok}' is not modelled: the index must be an integer type"
          let lead ← parseOperand (.int wLead)
          match lead with
          | .imm (.int _ v) =>
              if v.toNat = 0 then pure ()
              else
                P.fail s!"getelementptr over '{arr.render}' is modelled only with a literal 0 \
                    leading index, got {v.toNat}: the model's step has one index and no term \
                    for a whole-array stride"
          | _ =>
              P.fail s!"getelementptr over '{arr.render}' is modelled only with a literal 0 \
                  leading index: the model's step has one index and no term for a \
                  whole-array stride"
          P.expect ","
          let idxTok ← P.next
          let w ← match parseTy idxTok with
            | .ok (.int w) => pure w
            | _ => P.fail s!"getelementptr index type '{idxTok}' is not modelled: the index must be an integer type"
          if w > 64 then
            P.fail s!"getelementptr index width i{w} is not modelled: an index wider than 64 bits is refused rather than truncated"
          let off ← parseOperand (.int w)
          match (← P.peek) with
          | some "," => P.fail "getelementptr with more than two indices is not modelled"
          | _ => pure ()
          pure (.instr (.gep dst elemTy base off))
      | _ =>
            let elemTy ←
              match (← P.peek) with
              | some t => if t.startsWith "%struct." then expectStructTy layout else expectTy
              | none => P.fail "unexpected end of line"
            if elemTy.gepElemAdmitted then pure ()
            else
              match elemTy with
              | .int w =>
                  P.fail s!"getelementptr element width i{w} is not admitted: the step \
                    scales by the stored size, and only i1, i7, i8, i16, i32, i64 and \
                    i128 are admitted — the widths the model pins as having the same \
                    allocated and stored size. A width where the two differ would be \
                    given one address here and another by LLVM, and a width the model \
                    does not pin is not characterised here; both are refused"
              | .vec n (.int w) =>
                  -- The two divergence classes are named separately, because the
                  -- condition has two clauses and a rule that kept only one would admit
                  -- the input class the other excludes.
                  let stored := n * ((w + 7) / 8)
                  let packed := n * w / 8
                  if w % 8 ≠ 0 then
                    P.fail s!"getelementptr element type '{elemTy.render}' is not admitted: \
                      a lane width of i{w} is not a whole number of bytes, so the packed \
                      size n * w / 8 = {packed} is not the n * ((w + 7) / 8) = {stored} \
                      bytes this step would scale by, and LLVM steps the packed size \
                      rounded up to its next power of two"
                  else
                    P.fail s!"getelementptr element type '{elemTy.render}' is not admitted: \
                      its packed size n * w / 8 = {packed} is not a power of two, so LLVM \
                      steps the next power of two above it while sizeBytes is {stored}. \
                      A vector element type is admitted under one condition — w % 8 = 0 \
                      and n * w / 8 a power of two, hence at least 1 — because the step \
                      scales by the size LLVM allocates"
              | _ =>
                  P.fail s!"getelementptr element type '{elemTy.render}' is not modelled: a \
                    pointer or void element type has no integer size to scale the index by"
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
  dropped, because the instruction has no field for it.  `nuw` is accepted and
  dropped for the reason `samesign` is: it can only *exclude* inputs — a
  computation that wraps under it is poison — so dropping it models a superset
  of the text's defined inputs.  `inrange` and `nusw` are refused by name: the
  first promises the result lies inside an allocation, which the model's byte
  step has no term for, and the second is the signed-wrap flag, and the model's
  address arithmetic is unsigned, so neither is a constraint the model can drop
  without also dropping what it was about. -/
  gepModifiers : P Unit
    | "inbounds" :: rest => gepModifiers rest
    | "nuw" :: rest => gepModifiers rest
    | f :: rest =>
        if f = "inrange" || f = "nusw" then
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
      -- A vector value is written as its lanes packed little-endian, lane `k` to
      -- bits `[k * w, (k + 1) * w)` and `n * w / 8` bytes in all, so a vector
      -- store is admitted exactly when its total width is a whole number of
      -- bytes.  A `<n x i1>` mask store is that rule at `w = 1`, not a rule of
      -- its own: the classifier's mask store and the entry body's `<8 x i32>`
      -- row store are the same admission at two lane widths.  A total width that
      -- is not whole bytes has no byte layout and is refused by name.  The value
      -- operand's type is checked against the written type once the function is
      -- known (`checkStoreValues`), because `parseOperand` returns a register
      -- without consulting its type.
      let (ty, v) ← parseTypedOperand
      P.expect ","
      let (_, p) ← parseTypedOperand
      -- `store <ty> <v>, ptr <p>[, align N]`: the alignment is read, checked
      -- and dropped, because the instruction has no field for it.
      let _ ← parseAlignOpt
      match ty with
      | .vec n (.int w) =>
          if n * w % 8 = 0 then pure (.instr (.store ty v p))
          else
            P.fail s!"store of {ty.render} is not modelled: a vector store's total \
                width of {n * w} bit(s) is not a whole number of bytes, so the \
                value has no byte layout"
      | _ => pure (.instr (.store ty v p))
  | "call" => parseCall none
  | "tail" => do
      P.expect "call"
      parseCall none
  | other => P.fail s!"unsupported instruction '{other}'"

/-- Parse one instruction or terminator line. -/
def parseStmtLine (layout : Layout) (toks : List String) : Except String Stmt :=
  match toks with
  | [] => .error "empty instruction"
  | dst :: "=" :: rest =>
      if dst.startsWith "%" then P.runExact (parseValueInstr layout dst) rest
      else .error s!"expected a register before '=', got '{dst}'"
  | _ => P.runExact parseSimple toks

/-! ### Blocks, functions, modules -/

def isLabel (toks : List String) : Bool :=
  match toks with
  | [_, ":"] => true
  | _ => false

def parseBlockBody (layout : Layout) (name : String) (ls : List (List String)) :
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
        match parseStmtLine layout l with
        | .error e => .error s!"in block '{name}': {e}"
        | .ok (.instr i) =>
            if i.isPhi && seen then
              .error s!"in block '{name}': a phi must be the first instructions of its \
                  block, and this one follows a non-phi instruction"
            else collect rest (i :: acc) (seen || !i.isPhi)
        | .ok (.term t) => .ok (acc.reverse, t, rest)
  let (instrs, term, rest) ← collect ls [] false
  .ok (⟨name, instrs, term⟩, rest)

/-- A label for a block that carries none: the smallest decimal that appears
neither as a label nor as a `%`-prefixed name anywhere in the body.  LLVM lets
only a function's entry block stand unlabelled and gives it no predecessors, so
well-formed text never jumps to it; choosing a name from outside the body's own
tokens therefore cannot capture a jump the parser would otherwise leave
undefined.  The label is written by the printer, and the printed module re-parses
to the same blocks. -/
def freshBlockLabel (body : List (List String)) : String :=
  let toks := body.flatten
  let rec go (fuel n : Nat) : String :=
    match fuel with
    | 0 => toString n
    | fuel + 1 =>
        let s := toString n
        if toks.contains s || toks.contains ("%" ++ s) then go fuel (n + 1) else s
  go (toks.length + 1) 0

/-- Parse the body of a function: a sequence of labelled blocks, the first of
which may stand unlabelled — the shape clang emits for an entry block, which is
the only block LLVM allows that way.  The fuel is the number of lines, so each
recursion consumes one line even when a block body is length-checked by the
parser rather than by the recursion. -/
def parseBlocks (layout : Layout) (ls : List (List String)) : Except String (List Block) :=
  let rec go : Nat → List (List String) → List Block → Except String (List Block)
    | 0, _, _ => .error "internal parser error: block fuel exhausted"
    | _ + 1, [], acc => .ok acc.reverse
    | fuel + 1, l :: rest, acc =>
        match l with
        | [name, ":"] =>
            match parseBlockBody layout name rest with
            | .error e => .error e
            | .ok (b, rest') => go fuel rest' (b :: acc)
        | _ =>
            if acc.isEmpty then
              let name := freshBlockLabel (l :: rest)
              match parseBlockBody layout name (l :: rest) with
              | .error e => .error e
              | .ok (b, rest') => go fuel rest' [b]
            else .error s!"expected a block label, got '{String.intercalate " " l}'"
  go (ls.length + 1) ls []

/-- Find the `@name` token, returning the token before it (the return type),
the name and the tokens after it. -/
def findAt (prev : Option String) : List String → Option (Option String × String × List String)
  | [] => none
  | t :: rest =>
      if t.startsWith "@" then some (prev, t, rest) else findAt (some t) rest

/-! ### A definition's parameter attributes

A parameter attribute is not a return attribute.  A return attribute can only
*exclude* the values a function returns, and this model takes the returned value
from the `Calls` environment, so dropping one widens the values the model admits
without adding a run.  A parameter attribute instead states something the
*caller* must guarantee, and the compiler may have used it to justify a
transformation of this body: on an argument that violates it LLVM's behaviour is
undefined, while this model executes the transformed body on that argument.
Dropping such an attribute would therefore widen the argument set on which the
imported body is claimed to implement its source, past the arguments the source
defines — an unsound claim — so the reader splits the attributes three ways.

* **Dropped, because the model already reads the obligation or there is none.**
  `noundef` says the caller passes a value whose representation has no undefined
  bits, and the predicate that states it is `Value.defined`: an integer, a
  pointer, a plain vector lane and a binary64 pattern are defined by
  construction, `poison` is not, and a `vecPoison` is defined only when every
  lane is `some`.  The last clause is why the obligation is not the inequality
  `v ≠ Value.poison`: a vector with one poisoned lane is a distinct value that
  satisfies the inequality and fails `noundef`, and a modelled `call` forwards
  what it reads.  A parsed definition's parameter is one type token, so a vector
  parameter is refused by the type grammar before an attribute is read; the
  predicate's vector case is what a hand-built `Function` with a vector parameter
  is held to, which is the form the refinement modules construct.  The one place
  an argument list is not a read — the denotation
  entry `Beh`/`run` — takes its premise from the theorem, recorded here as
  `ArgsDefined args`, rather than in `Function`, which has no field for it; the
  executable entry `runDefined` applies the same predicate.  A `call` whose
  operand reads are defined forwards an `ArgsDefined` list to the `Calls`
  environment (`ArgsDefined.of_evalOperands`), so the environment is asked only
  about the class the attribute admits.  A vector literal that still carries a
  poison lane is outside that class; the lane write that covers every poison
  lane produces a plain vector, which is inside it
  (`evalInstr_insertelement_poison_lane`).  The other dropped tokens are not
  caller obligations: `zeroext`, `signext`, `noext` and `inreg` are ABI sign and
  register properties, and the model's typed values have no upper bits for an
  extension to occupy; `readonly`, `writeonly` and `readnone` state the callee's
  own memory effect through the pointer; `captures`, `nocapture` and `nofree` are
  promises the callee makes about capturing or freeing the pointer; and
  `returned` is a promise about the callee's own result.  Each of those is a
  claim about the body the compiler emitted — importing its text already takes
  that claim as true of it — not a constraint whose violation makes the caller's
  argument undefined, so none narrows or widens the argument list a theorem must
  quantify over.

* **Refused, as a caller obligation that changes definedness.**  `nonnull`,
  `align N`, `dereferenceable(N)`, `dereferenceable_or_null(N)`, `range(...)`,
  `nofpclass(...)` and `noalias` each make a violating argument undefined
  behaviour, and the model neither checks the attribute nor reproduces the
  assumption: a `.ptr 0` is a value `icmp` may read, memory has no alignment
  rule, a value's range is not a constraint the model reads, and nothing records
  that the body was optimised on the strength of the attribute.  The module has
  no field to carry the obligation as a hypothesis, so the definition is refused
  by name with the obligation in the message, rather than imported on a wider
  argument set.

* **Refused, as a change to how the argument is passed.**  `sret`, `byval`,
  `byref`, `inalloca`, `preallocated`, `elementtype`, `alignstack`, `allocalign`,
  `allocptr`, `immarg`, `nest`, `swiftself` and `swiftasync` name a hidden
  argument or a calling-convention detail the model has no field for; they are
  refused as unmodelled, the reading a linkage or calling convention gets.

Any other token is not an attribute the reader knows; the parameter-name check
names it.  The same reading is also why a *declaration*'s parameter attribute
stays refused even when a definition would drop it: `Decl` is the module's
statement of a symbol's interface, and dropping a constraint from it would
publish a wider interface than the text makes. -/

/-- The parameter attributes a definition's header may carry that the reader
checks the shape of and drops.  The reason each is droppable is in the section
comment above; the set is closed, and a token outside it is not an attribute. -/
def isDroppedParamAttr (t : String) : Bool :=
  ["noundef", "zeroext", "signext", "noext", "inreg",
   "readonly", "writeonly", "readnone",
   "nocapture", "nofree", "returned"].contains t

/-- The `captures` attribute's argument vocabulary: the five spellings LLVM 21
accepts.  Each says which parts of the pointer the callee may capture; all are
promises about the callee's own use, so the reader checks the spelling and drops
it. -/
def isCapturesArg (t : String) : Bool :=
  ["none", "address", "address_is_null", "provenance", "read_provenance"].contains t

/-- Parameter attributes whose violation is a caller obligation that changes
definedness.  `align` is refused together with the number after it, so the
message names the whole attribute; the rest are bare or parenthesised and are
refused at the name. -/
def isObligationParamAttr (t : String) : Bool :=
  ["nonnull", "dereferenceable", "dereferenceable_or_null", "range",
   "nofpclass", "noalias"].contains t

/-- Parameter attributes that change the call's shape: a hidden argument (a
return slot, a by-value copy, an allocator hint), a calling-convention detail, or
a requirement on the argument's form (`immarg`).  The model has no calling
convention and no field for any of them, so they are refused as unmodelled. -/
def isCallShapeParamAttr (t : String) : Bool :=
  ["sret", "byval", "byref", "inalloca", "preallocated", "elementtype",
   "alignstack", "allocalign", "allocptr", "immarg", "nest", "swiftself",
   "swiftasync"].contains t

/-- The refusal an attribute in the caller-obligation group gets.  It names the
attribute and the obligation rather than the parser's inability, because the
definition is well formed and the model is the part that cannot carry it. -/
def obligationRefusal (idx : Nat) (shown : String) : String :=
  s!"parameter {idx} carries the attribute '{shown}', which is not modelled: \
      it is a caller obligation whose violation is undefined behaviour, the compiled \
      body may have been optimised on the assumption, and the module has no field to \
      carry the obligation as a hypothesis"

/-- Read the attributes in front of a definition parameter's name, checking each
shape and either dropping it or refusing it for the reason the section comment
gives.  The first token that is not an attribute is returned with the tokens
after it; the caller requires it to be the parameter's `%`-name. -/
def parseParamAttrs (idx : Nat) : List String → Except String (List String)
  | [] => .error s!"parameter {idx} has no name: expected a parameter name after its type"
  | t :: rest =>
      if isDroppedParamAttr t then parseParamAttrs idx rest
      else if t = "captures" then
        match rest with
        | "(" :: arg :: ")" :: rest' =>
            if isCapturesArg arg then parseParamAttrs idx rest'
            else .error s!"the parameter attribute 'captures({arg})' is not modelled: \
                its argument is one of none, address, address_is_null, provenance or \
                read_provenance"
        | _ => .error "malformed parameter attribute 'captures': expected one \
            parenthesised argument, as in 'captures(none)'"
      else if t = "align" then
        match rest with
        | n :: _ => .error (obligationRefusal idx s!"align {n}")
        | [] => .error s!"parameter {idx} carries the attribute 'align' without its alignment"
      else if isObligationParamAttr t then .error (obligationRefusal idx t)
      else if isCallShapeParamAttr t then
        .error s!"parameter {idx} carries the attribute '{t}', which is not modelled: \
            it changes the call's shape or the argument's form and the model has \
            no field for it"
      else .ok (t :: rest)

/-- Read a definition's parameter list from the tokens between its parentheses,
with a fuel budget and the 1-based position of the parameter being read.  A
parameter is a type, the attributes the section above describes, and a
`%`-name.  The budget is the list's length plus one: every parameter consumes at
least its own tokens, and the `(` that opens the list consumes one before the
first parameter. -/
def parseParamsFrom (fuel : Nat) (idx : Nat) (ts : List String) :
    Except String (List (String × Ty) × List String) :=
  match fuel with
  | 0 => .error "internal parser error: parameter fuel exhausted"
  | fuel + 1 =>
    match ts with
    | ")" :: rest => .ok ([], rest)
    | "(" :: rest => parseParamsFrom fuel idx rest
    | tyTok :: rest =>
        match parseTy tyTok with
        | .error e => .error e
        | .ok ty =>
            match parseParamAttrs idx rest with
            | .error e => .error e
            | .ok l =>
                match l with
                | nameTok :: rest' =>
                    if nameTok.startsWith "%" then
                      match rest' with
                      | "," :: rest'' =>
                          match parseParamsFrom fuel (idx + 1) rest'' with
                          | .error e => .error e
                          | .ok (ps, rest''') => .ok ((nameTok, ty) :: ps, rest''')
                      | ")" :: rest'' => .ok ([(nameTok, ty)], rest'')
                      | _ => .error s!"expected ',' or ')' after parameter {idx}"
                    else .error s!"expected a parameter name, got '{nameTok}'"
                | [] =>
                    .error s!"parameter {idx} has no name: expected a parameter name \
                        after its type"
    | _ => .error "malformed parameter list"

def parseParams : P (List (String × Ty)) := fun ts =>
  match parseParamsFrom (ts.length + 1) 1 ts with
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

/-! ### The module header

A production emission is not one `define` after another.  It opens with
`source_filename`, `target datalayout` and `target triple`, defines named struct
types, then writes globals, attribute groups and metadata nodes, and puts the
functions after them.  `Module` has no field for any of it, so each is read for
the shape it must have and dropped.  Two pieces are more than dropped: a named
struct's byte extent is computed from its fields and the target data layout,
because `Ty.struct` carries an extent that a body's `alloca` needs and the
declared `Layout` may not supply it; and that extent is checked against a
declared one when the caller gives both.

The extent rule is the target's, not a field sum: fields are laid out on their
allocated sizes and alignments, and a struct's size is rounded up to its largest
field alignment.  Only the data-layout specs that rule reads are recorded — the
integer, floating-point, pointer and vector alignments — while the rest are
checked for shape and dropped.  A spec the reader has no rule for, and an
aggregate-alignment spec (which would move a byte the rule has no term for), are
refused by name rather than skipped.  On the pinned stage-2 emission this
computes `%struct.Stk` as 1568 bytes, `%struct.StkBn` as 776 and `%struct.EPow`
as 24 — clang's own record layout for the target.

A printed module does not carry the definition, because `Module` has no field for
it: the extent lives in the `Ty.struct` an `alloca` carries, so reparsing a
printed struct `alloca` needs the extent from a declared `Layout` again.  That is
the one place a parse/print round trip is not closed by this reader, and it is
`Ty.struct`'s existing limit rather than a surface this grammar drops.
-/

/-- Round `n` up to a multiple of `a`, left unchanged when `a` is zero. -/
def alignUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

/-- The smallest power of two that is at least `n`. -/
def pow2Ceil (n : Nat) : Nat :=
  let rec go (fuel p : Nat) : Nat :=
    match fuel with
    | 0 => p
    | fuel + 1 => if p ≥ n then p else go fuel (2 * p)
  go 64 1

/-- One recorded data-layout spec.  `width` is the integer or floating-point
width in bits, a vector's size in bits, or a pointer's address space; `size` and
`align` are the stored size and ABI alignment the spec gives, in bits. -/
structure TargetSpec where
  width : Nat
  size : Nat
  align : Nat

/-- The parts of a target data layout a named struct's extent reads.  A pointer
in address space 0 is `ptrSize` and `ptrAlign`; one in another address space is
in `ptrs`. -/
structure TargetLayout where
  ints : List TargetSpec := []
  floats : List TargetSpec := []
  vecs : List TargetSpec := []
  ptrs : List TargetSpec := []
  ptrSize : Nat := 64
  ptrAlign : Nat := 64

/-- Parse a `:`-separated run of decimals. -/
def parseNatRun (s : String) : Option (List Nat) :=
  let rec go : List String → Option (List Nat)
    | [] => some []
    | p :: rest => do
        let n ← parseNat p
        let ns ← go rest
        pure (n :: ns)
  go (s.splitOn ":")

/-- Read the specs of a `target datalayout` string.  The ones that determine a
field's size or alignment are recorded; the ones the model's extent rule never
reads — the endianness, the name mangling, the native widths, the stack
alignment — are checked for shape and dropped.  A spec outside the ones below,
and an aggregate-alignment spec, are refused by name: a dropped spec that could
move a byte would make an extent silently wrong, and one that cannot is what the
rule is allowed not to read. -/
def parseDataLayout (text : String) : Except String TargetLayout :=
  let rec go : List String → TargetLayout → Except String TargetLayout
    | [], t => .ok t
    | spec :: rest, t =>
        if spec.isEmpty then go rest t
        else
          let head := match spec.toList with
            | [] => ""
            | c :: _ => String.singleton c
          let body := match spec.toList with
            | [] => ""
            | _ :: cs => String.ofList cs
          match head with
          | "e" | "E" =>
              if body.isEmpty then go rest t
              else .error s!"data layout spec '{spec}' is not modelled"
          | "m" =>
              if body.startsWith ":" && body.length > 1 then go rest t
              else .error s!"data layout spec '{spec}' is not modelled: expected a mangling"
          | "n" | "S" =>
              match parseNatRun body with
              | some _ => go rest t
              | none => .error s!"data layout spec '{spec}' is not modelled: expected decimal widths"
          | "p" =>
              match body.splitOn ":" with
              | asTok :: sizeTok :: abiTok :: _ => do
                  let as ← if asTok.isEmpty then pure 0 else
                    match parseNat asTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': address space '{asTok}' is not a decimal"
                  let size ← match parseNat sizeTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': pointer size '{sizeTok}' is not a decimal"
                  let abi ← match parseNat abiTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': pointer alignment '{abiTok}' is not a decimal"
                  if size = 0 || abi = 0 || size % 8 ≠ 0 || abi % 8 ≠ 0 then
                    throw s!"data layout spec '{spec}' is not modelled: a pointer's size and alignment must be whole bytes"
                  if as = 0 then
                    go rest { t with ptrSize := size, ptrAlign := abi }
                  else
                    go rest { t with ptrs :=
                      ({ width := as, size := size, align := abi } : TargetSpec) :: t.ptrs }
              | _ => .error s!"data layout spec '{spec}' is not modelled: expected [<address space>:]<size>:<alignment>"
          | "i" =>
              match body.splitOn ":" with
              | wTok :: ws => do
                  let w ← match parseNat wTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': integer width '{wTok}' is not a decimal"
                  let size ← match ws with
                    | [] => pure w
                    | s0 :: _ => match parseNat s0 with
                        | some n => pure n
                        | none => throw s!"data layout spec '{spec}': integer size '{s0}' is not a decimal"
                  let abi ← match ws with
                    | _ :: s0 :: _ => match parseNat s0 with
                        | some n => pure n
                        | none => throw s!"data layout spec '{spec}': integer alignment '{s0}' is not a decimal"
                    | _ => pure size
                  if w = 0 || abi = 0 || abi % 8 ≠ 0 then
                    throw s!"data layout spec '{spec}' is not modelled: an alignment must be whole bytes"
                  go rest { t with ints :=
                    ({ width := w, size := size, align := abi } : TargetSpec) :: t.ints }
              | [] => .error s!"data layout spec '{spec}' is not modelled"
          | "f" =>
              match body.splitOn ":" with
              | wTok :: ws => do
                  let w ← match parseNat wTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': floating-point width '{wTok}' is not a decimal"
                  let size ← match ws with
                    | [] => pure w
                    | s0 :: _ => match parseNat s0 with
                        | some n => pure n
                        | none => throw s!"data layout spec '{spec}': floating-point size '{s0}' is not a decimal"
                  let abi ← match ws with
                    | _ :: s0 :: _ => match parseNat s0 with
                        | some n => pure n
                        | none => throw s!"data layout spec '{spec}': floating-point alignment '{s0}' is not a decimal"
                    | _ => pure size
                  if w = 0 || abi = 0 || abi % 8 ≠ 0 then
                    throw s!"data layout spec '{spec}' is not modelled: an alignment must be whole bytes"
                  go rest { t with floats :=
                    ({ width := w, size := size, align := abi } : TargetSpec) :: t.floats }
              | [] => .error s!"data layout spec '{spec}' is not modelled"
          | "v" =>
              match body.splitOn ":" with
              | sizeTok :: ws => do
                  let size ← match parseNat sizeTok with
                    | some n => pure n
                    | none => throw s!"data layout spec '{spec}': vector size '{sizeTok}' is not a decimal"
                  let abi ← match ws with
                    | [] => pure size
                    | s0 :: _ => match parseNat s0 with
                        | some n => pure n
                        | none => throw s!"data layout spec '{spec}': vector alignment '{s0}' is not a decimal"
                  if size = 0 || abi = 0 || size % 8 ≠ 0 || abi % 8 ≠ 0 then
                    throw s!"data layout spec '{spec}' is not modelled: a vector's size and alignment must be whole bytes"
                  go rest { t with vecs :=
                    ({ width := size, size := size, align := abi } : TargetSpec) :: t.vecs }
              | [] => .error s!"data layout spec '{spec}' is not modelled"
          | "a" | "A" =>
              .error s!"data layout spec '{spec}' is not modelled: an aggregate-alignment spec would move a struct's byte"
          | _ => .error s!"data layout spec '{spec}' is not modelled"
  go (text.splitOn "-") {}

/-- A field of a named struct's definition, read from the definition's own
tokens.  The model keeps no aggregate type with fields — a named struct's extent
is all `Ty.struct` carries — so this reading exists only to compute that extent
and is dropped with the definition. -/
inductive FieldTy where
  | int (w : Nat)
  | float (w : Nat)
  | ptr (as : Nat)
  | array (n : Nat) (elem : FieldTy)
  | vec (n : Nat) (elem : FieldTy)
  | named (key : String)
  | inline (fields : List FieldTy) (packed : Bool)

/-- Read one field type from the tokens of a struct definition, returning it and
the remaining tokens.  A nested aggregate is read rather than refused, because a
production emission's own type definitions write them (`[96 x i64]`); a named
type is read as a reference to be resolved through the module's definitions,
which is why a forward reference works.  A type outside the set below is
refused by name. -/
def parseFieldTy (fuel : Nat) (toks : List String) : Except String (FieldTy × List String) :=
  match fuel with
  | 0 => .error "internal parser error: field type fuel exhausted"
  | fuel + 1 =>
      -- The fields between an inline struct's braces, read by the same reader:
      -- the recursion is on the enclosing function's fuel and on this loop's
      -- own, so both are structurally decreasing.
      let rec goFields (moreFuel : Nat) (ts : List String) :
          Except String (List FieldTy × List String) :=
        match moreFuel with
        | 0 => .error "internal parser error: field list fuel exhausted"
        | moreFuel + 1 =>
            match ts with
            | "}" :: rest => pure ([], rest)
            | _ => do
                let (f, rest) ← parseFieldTy fuel ts
                match rest with
                | "," :: rest' => do
                    let (fs, rest'') ← goFields moreFuel rest'
                    pure (f :: fs, rest'')
                | "}" :: rest' => pure ([f], rest')
                | _ => throw "a struct's field list needs ',' or '}' after a field type"
      match toks with
      | [] => .error "unexpected end of line in a struct field type"
      | "[" :: nTok :: "x" :: rest => do
          let n ← match nTok.toNat? with
            | some n =>
                if 0 < n then pure n else throw "a struct field's array needs at least one element"
            | none => throw s!"invalid array element count '{nTok}' in a struct field"
          let (elem, rest) ← parseFieldTy fuel rest
          match rest with
          | "]" :: more => pure (.array n elem, more)
          | _ => throw "a struct field's array type needs a closing ']'"
      | "<" :: nTok :: "x" :: rest => do
          let n ← match nTok.toNat? with
            | some n =>
                if 0 < n then pure n else throw "a struct field's vector needs at least one lane"
            | none => throw s!"invalid vector lane count '{nTok}' in a struct field"
          let (elem, rest) ← parseFieldTy fuel rest
          let elem ← match elem with
            | .int w => pure (.int w)
            | .float w => pure (.float w)
            | _ => throw "a struct field's vector element is not modelled"
          match rest with
          | ">" :: more => pure (.vec n elem, more)
          | _ => throw "a struct field's vector type needs a closing '>'"
      | "<" :: "{" :: rest => do
          let (fields, rest) ← goFields fuel rest
          match rest with
          | ">" :: more => pure (.inline fields true, more)
          | _ => throw "a packed struct field needs a closing '>'"
      | "{" :: rest => do
          let (fields, rest) ← goFields fuel rest
          pure (.inline fields false, rest)
      | "ptr" :: "addrspace" :: "(" :: nTok :: ")" :: rest => do
          let as ← match nTok.toNat? with
            | some n => pure n
            | none => throw s!"invalid address space '{nTok}' in a struct field"
          pure (.ptr as, rest)
      | "ptr" :: rest => pure (.ptr 0, rest)
      | t :: rest =>
          if t = "double" then pure (.float 64, rest)
          else if t = "float" then pure (.float 32, rest)
          else if t = "half" then pure (.float 16, rest)
          else if t = "x86_fp80" then pure (.float 80, rest)
          else if t = "fp128" || t = "ppc_fp128" then pure (.float 128, rest)
          else if t.startsWith "%" then
            let raw := (t.drop 1).toString
            pure (.named (if raw.startsWith "struct." then (raw.drop 7).toString else raw), rest)
          else
            match (t.drop 1).toString.toNat? with
            | some w =>
                if t.startsWith "i" && 0 < w then pure (.int w, rest)
                else throw s!"unsupported struct field type '{t}'"
            | none => throw s!"unsupported struct field type '{t}'"

/-- A field type's size and alignment: `store` is the size the value occupies,
`alloc` the size it is allocated (the stored size rounded up to the alignment),
and `align` the alignment itself.  A struct is laid out field by field on `alloc`
and rounded to the largest `align`; a packed struct is laid out on `store` with
alignment 1. -/
structure FieldExtent where
  store : Nat
  alloc : Nat
  align : Nat

/-- A named struct definition, as the extent rule reads it.  `tokens` is the
number of tokens its body was read from, which bounds the nesting the reader has
to follow. -/
structure StructDef where
  key : String
  fields : List FieldTy
  packed : Bool
  tokens : Nat

/-- The extent of one field type.  `known` holds the extents of the struct
definitions already laid out, and a named field that is not there is reported as
one the module's header cannot reach — `resolveNamedTypes` lays definitions out
in dependency order and turns that report into the refusal naming the circular
or missing definition.  A struct's own fields reach this reader as an inline
struct, so one function is the whole layout. -/
def fieldExtent (dl : TargetLayout) (known : List (String × FieldExtent))
    (fuel : Nat) (ft : FieldTy) : Except String FieldExtent :=
  match fuel with
  | 0 => .error "internal parser error: struct extent fuel exhausted"
  | fuel + 1 =>
      let rec goFields (moreFuel : Nat) (fs : List FieldTy) (off mx : Nat) (packed : Bool) :
          Except String (Nat × Nat) :=
        match moreFuel with
        | 0 => .error "internal parser error: field list fuel exhausted"
        | moreFuel + 1 =>
            match fs with
            | [] => pure (off, mx)
            | f :: rest => do
                let e ← fieldExtent dl known fuel f
                let off' := if packed then off + e.store else alignUp off e.align + e.alloc
                goFields moreFuel rest off' (if packed then mx else max mx e.align) packed
      match ft with
      | .int w =>
          let alignBits := match dl.ints.find? (fun s => s.width = w) with
            | some s => s.align
            | none => 8 * min 16 (pow2Ceil ((w + 7) / 8))
          let align := alignBits / 8
          let store := (w + 7) / 8
          pure { store := store, alloc := alignUp store align, align := align }
      | .float w =>
          let spec := dl.floats.find? (fun s => s.width = w)
          let alignBits := match spec with
            | some s => s.align
            | none => 8 * min 16 (pow2Ceil ((w + 7) / 8))
          let storeBits := match spec with
            | some s => s.size
            | none => w
          let align := alignBits / 8
          let store := (storeBits + 7) / 8
          pure { store := store, alloc := alignUp store align, align := align }
      | .ptr as => do
          let (bytes, align) ←
            if as = 0 then pure (dl.ptrSize / 8, dl.ptrAlign / 8)
            else match dl.ptrs.find? (fun s => s.width = as) with
              | some s => pure (s.size / 8, s.align / 8)
              | none => throw s!"a struct field names address space {as}, which the target data layout gives no pointer spec for"
          pure { store := bytes, alloc := alignUp bytes align, align := align }
      | .array n elem => do
          let e ← fieldExtent dl known fuel elem
          pure { store := n * e.store, alloc := n * e.alloc, align := e.align }
      | .vec n elem => do
          let bits ← match elem with
            | .int w => pure (n * w)
            | .float w => pure (n * w)
            | _ => throw "a struct field's vector element is not modelled"
          let alignBits := match dl.vecs.find? (fun s => s.width = bits) with
            | some s => s.align
            | none => 8 * min 16 (pow2Ceil ((bits + 7) / 8))
          let align := alignBits / 8
          let store := (bits + 7) / 8
          pure { store := store, alloc := alignUp store align, align := align }
      | .named key =>
          match lookupName known key with
          | some e => pure e
          | none => .error s!"'%struct.{key}' has no byte extent the module's header can reach"
      | .inline fields packed => do
          let (stop, mx) ← goFields fuel fields 0 1 packed
          let align := max mx 1
          let store := if packed then stop else alignUp stop align
          pure { store := store, alloc := store, align := align }

/-- Lay out one struct definition: its fields are read by the same reader as an
inline struct, with the extents of the definitions already laid out supplied. -/
def structExtent (dl : TargetLayout) (known : List (String × FieldExtent))
    (fuel : Nat) (d : StructDef) : Except String FieldExtent :=
  fieldExtent dl known fuel (.inline d.fields d.packed)

/-- One `%name = type` definition.  `key` is the name the layout uses — a named
struct's without the `struct.` prefix — and `fields` is `none` when the body is
not a struct. -/
structure NamedType where
  key : String
  fields : Option (List FieldTy) := none
  packed : Bool := false
  tokens : Nat := 0

/-- Read one `%name = type <body>` definition.  A struct body — plain, packed,
or inline — yields its fields; any other body (`opaque`, a scalar, an array, a
vector) is read for shape and dropped, because the model's only reader of a
named type is `alloca`'s and it resolves `%struct.*` alone. -/
def parseNamedType (name : String) (body : List String) : Except String NamedType := do
  let raw := (name.drop 1).toString
  let isStructName := raw.startsWith "struct."
  let key := if isStructName then (raw.drop 7).toString else raw
  if key.isEmpty then throw s!"malformed type definition '{name}': a type needs a name"
  let fuel := body.length + 2
  let finish (fields : Option (List FieldTy)) (packed : Bool) : NamedType :=
    { key := key, fields := fields, packed := packed, tokens := body.length }
  match body with
  | "{" :: _ => do
      let (ft, rest) ← parseFieldTy fuel body
      match ft, rest with
      | .inline fields false, [] => pure (finish (some fields) false)
      | _, _ => throw s!"malformed type definition of '%{raw}': tokens after the field list"
  | "<" :: "{" :: _ => do
      let (ft, rest) ← parseFieldTy fuel body
      match ft, rest with
      | .inline fields true, [] => pure (finish (some fields) true)
      | _, _ => throw s!"malformed type definition of '%{raw}': a packed struct needs a closing '>'"
  | ["opaque"] => pure (finish none false)
  | _ => do
      if isStructName then
        throw s!"malformed type definition of '%{raw}': a named struct's body must be a struct type"
      else do
        let (_, rest) ← parseFieldTy fuel body
        if rest.isEmpty then pure (finish none false)
        else throw s!"malformed type definition of '%{raw}': tokens after the type"

/-- The text of one quoted string, read from the tokens the `=` leaves.  The
tokenizer splits on `:`, so a data layout's quoted text arrives in several
tokens (`"e-m`, `:`, `e-p270`, …); they are joined with no separator, which is
exact for a quoted string that contains no whitespace — the one thing the
tokenizer cannot tell a quoted string from — and the surrounding quotes are then
stripped. -/
def stringLiteral (toks : List String) : Except String String :=
  match toks with
  | [] => throw "expected a quoted string"
  | first :: _ =>
      let joined := String.intercalate "" toks
      if !(first.startsWith "\"") then
        throw s!"expected a quoted string, got '{joined}'"
      else
        match joined.toList with
        | '"' :: body =>
            match body.reverse with
            | '"' :: revBody =>
                if revBody.isEmpty then throw s!"expected a quoted string, got '{joined}'"
                else pure (String.ofList revBody.reverse)
            | _ => throw s!"expected a quoted string, got '{joined}'"
        | _ => throw s!"expected a quoted string, got '{joined}'"

/-- Count the occurrences of one token. -/
def countToken (t : String) : List String → Nat
  | [] => 0
  | x :: xs => (if x = t then 1 else 0) + countToken t xs

/-- An attribute group's contents, keyed by its `#N` spelling.  A `define` may
refer to a group the module declares later, so the groups are collected from the
whole header before any function is read. -/
abbrev AttributeGroups := List (String × List String)

/-- Read an `attributes #N = { ... }` line: its id and the tokens inside the
braces.  Only the outer shape is checked here.  The members are classified where
the group is used — a `define`'s tail or another reference — because a group's
contents say nothing until a header refers to it, and an unused group must not
decide the module. -/
def attributeGroupOf (l : List String) : Except String (String × List String) :=
  match l with
  | "attributes" :: id :: "=" :: "{" :: body =>
      if !id.startsWith "#" || (parseNat (id.drop 1).toString).isNone then
        .error s!"malformed attribute group: '{id}' is not an attribute-group number"
      else match body.reverse with
        | "}" :: revInner =>
            if revInner.contains "{" || revInner.contains "}" then
              .error s!"malformed attribute group {id}: a nested brace is not modelled"
            else .ok (id, revInner.reverse)
        | _ => .error s!"malformed attribute group {id}: expected '}'"
  | _ => .error s!"malformed attribute group line '{String.intercalate " " l}'"

/-- The data layout, the named type definitions and the attribute groups of a
module, read from its module-level lines and not from the lines of a body — the
tokenizer drops indentation, so a body is skipped by counting braces: a
definition's own braces balance on its line, while a body opens on its `define`
and closes on its `}`.  Everything else at module level is left to the reader
that walks the lines in order, so a malformed global is reported where it
stands. -/
def scanHeader (lines : List (List String)) :
    Except String (TargetLayout × List NamedType × AttributeGroups) :=
  let rec go : List (List String) → Nat → TargetLayout → List NamedType →
      AttributeGroups → Except String (TargetLayout × List NamedType × AttributeGroups)
    | [], _, dl, ts, gs => .ok (dl, ts.reverse, gs.reverse)
    | l :: rest, depth, dl, ts, gs =>
        let opens := countToken "{" l
        let closes := countToken "}" l
        let depth' := if closes ≤ depth + opens then depth + opens - closes else 0
        if depth = 0 then
          match l with
          | "target" :: "datalayout" :: "=" :: value => do
              let text ← stringLiteral value
              let dl' ← parseDataLayout text
              go rest depth' dl' ts gs
          | name :: "=" :: "type" :: body =>
              if name.startsWith "%" then do
                let nt ← parseNamedType name body
                go rest depth' dl (nt :: ts) gs
              else go rest depth' dl ts gs
          | "attributes" :: _ => do
              let g ← attributeGroupOf l
              go rest depth' dl ts (g :: gs)
          | _ => go rest depth' dl ts gs
        else go rest depth' dl ts gs
  go lines 0 {} [] []

/-- Resolve every struct definition the module makes into the byte extents a
body's `alloca` reads, and merge them with the caller's declared `Layout`.  A
definition is laid out once every struct it names has been, so a header's
forward references work; a round that lays out nothing leaves only definitions
that contain themselves by value or name a struct the module does not define,
and that set is refused by name.  Where the caller declares an extent it must
agree with the module's, because the model's byte step has one extent and two
texts would then mean two different instructions. -/
def resolveNamedTypes (declared : Layout) (dl : TargetLayout) (types : List NamedType) :
    Except String Layout := do
  let defs := types.filterMap fun nt => nt.fields.map fun fs =>
    ({ key := nt.key, fields := fs, packed := nt.packed, tokens := nt.tokens } : StructDef)
  let rec rounds (fuel : Nat) (known : List (String × FieldExtent)) (pending : List StructDef) :
      Except String (List (String × FieldExtent)) :=
    match fuel with
    | 0 => .error "internal parser error: struct layout did not converge"
    | fuel + 1 =>
        match pending with
        | [] => pure known
        | _ =>
            let rec pass (remaining : List StructDef) (known : List (String × FieldExtent))
                (blocked : List StructDef) : List StructDef × List (String × FieldExtent) :=
              match remaining with
              | [] => (blocked.reverse, known)
              | d :: rest =>
                  match structExtent dl known (d.tokens + 2) d with
                  | .ok e => pass rest ((d.key, e) :: known) blocked
                  | .error _ => pass rest known (d :: blocked)
            let (blocked, known') := pass pending known []
            if blocked.length = pending.length then
              throw s!"the module's struct definitions cannot be laid out: \
                  {String.intercalate ", " (blocked.map fun d => "'%struct." ++ d.key ++ "'")} \
                  contains itself by value, or names a struct the module does not define"
            else rounds fuel known' blocked
  let known ← rounds (defs.length + 1) [] defs
  defs.foldlM (fun out d =>
    match lookupName known d.key with
    | none => pure out
    | some e =>
        match lookupName out d.key with
        | some bytes =>
            if bytes = e.alloc then pure out
            else throw s!"'%struct.{d.key}' is {e.alloc} bytes in the module, but the declared layout gives it {bytes}"
        | none => pure (out ++ [(d.key, e.alloc)])) declared

/-- The return-value attributes with no argument.  Each constrains the value a
function returns, and in this model that value is whatever the `Calls`
environment's outcome carries, so there is no field for the constraint. -/
def isBareReturnAttr (t : String) : Bool :=
  ["zeroext", "signext", "noext", "inreg", "noalias", "nonnull", "noundef"].contains t

/-- The return-value attributes whose argument is parenthesised.  `nofpclass` is
deliberately absent: its argument names a vocabulary of floating-point classes
(`nan`, `inf`, `zero`, …) that the model has no reading of, and an attribute
whose argument cannot be checked is refused by name rather than accepted on its
syntax alone. -/
def isParenReturnAttr (t : String) : Bool :=
  ["dereferenceable", "dereferenceable_or_null", "range",
   "sret", "byval", "byref", "inalloca", "preallocated"].contains t

/-- Read one parenthesised attribute argument: the tokens between `(` and its
`)`.  No attribute argument the reader admits nests, and a nested `(` is refused
by name rather than counted. -/
def takeParenArg : List String → Except String (List String × List String)
  | [] => .error "unterminated attribute argument: expected ')'"
  | ")" :: rest => .ok ([], rest)
  | "(" :: _ => .error "a nested '(' in a return attribute's argument is not modelled"
  | t :: rest => do
      let (arg, rest) ← takeParenArg rest
      .ok (t :: arg, rest)

/-- Whether `s` is an integer literal, with an optional leading minus. -/
def isIntLit (s : String) : Bool :=
  (parseNat s).isSome || (s.startsWith "-" && (parseNat (s.drop 1).toString).isSome)

/-- Check one return attribute's parenthesised argument for the shape its name
requires: a range is an integer type and two integer bounds, a dereferenceable
count is a decimal, and a type argument is a type. -/
def checkReturnAttrArg (name : String) (arg : List String) : Except String Unit :=
  if arg.isEmpty then .error s!"the return attribute '{name}' has an empty argument"
  else match name with
  | "range" =>
      match arg with
      | [tyTok, lo, ",", hi] =>
          match parseTy tyTok with
          | .ok (.int _) =>
              if isIntLit lo && isIntLit hi then .ok ()
              else .error s!"the return attribute 'range' needs two integer bounds, got '{lo}' and '{hi}'"
          | .ok _ => .error s!"the return attribute 'range' needs an integer type, got '{tyTok}'"
          | .error e => .error e
      | _ => .error s!"the return attribute 'range' needs a type and two bounds, got '{String.intercalate " " arg}'"
  | "dereferenceable" | "dereferenceable_or_null" =>
      match arg with
      | [n] => if (parseNat n).isSome then .ok ()
          else .error s!"the return attribute '{name}' needs a decimal byte count, got '{n}'"
      | _ => .error s!"the return attribute '{name}' needs one byte count, got '{String.intercalate " " arg}'"
  | _ =>
      match parseFieldTy (arg.length + 2) arg with
      | .ok (_, []) => .ok ()
      | .ok (_, extra) => .error s!"the return attribute '{name}' has tokens after its type: '{String.intercalate " " extra}'"
      | .error e => .error e

/-- Read a function definition's return attributes: each is checked for the shape
its name requires and then dropped.  The model has no field for a constraint on
the returned value — the caller's `Calls` environment supplies it — and every
attribute here can only *exclude* return values (a violating one is poison), so
dropping it models a superset of the text's defined values rather than a
narrowing of them, the reading `icmp`'s `samesign` gets.  A token the reader has
no rule for is refused by name, so the header is still checked rather than
parsed past. -/
def checkReturnAttrs (name : String) (toks : List String) : Except String Unit :=
  let rec go : Nat → List String → Except String Unit
    | 0, _ => .error "internal parser error: return attribute fuel exhausted"
    | _, [] => .ok ()
    | fuel + 1, "align" :: n :: rest =>
        if (parseNat n).isSome then go fuel rest
        else .error s!"the return attribute 'align' needs a decimal alignment, got '{n}'"
    | _, ["align"] =>
        .error "the return attribute 'align' needs a decimal alignment"
    | fuel + 1, t :: rest =>
        if isBareReturnAttr t then go fuel rest
        else if isParenReturnAttr t then
          match rest with
          | "(" :: inner => do
              let (arg, rest) ← takeParenArg inner
              checkReturnAttrArg t arg
              go fuel rest
          | _ => .error s!"malformed return attribute '{t}': expected '('"
        else .error s!"unsupported return attribute '{t}' before the return type of @{name}"
  go (toks.length + 1) toks

/-- Check a `source_filename = "..."` line and drop it: `Module` has no field
for the source the text came from. -/
def checkSourceFilename (l : List String) : Except String Unit :=
  match l with
  | "source_filename" :: "=" :: rest =>
      let text := String.intercalate " " rest
      match text.toList with
      | '"' :: body =>
          match body.reverse with
          | '"' :: revBody =>
              if revBody.isEmpty then .error "malformed source_filename: an empty string"
              else .ok ()
          | _ => .error s!"malformed source_filename: expected a quoted string, got '{text}'"
      | _ => .error s!"malformed source_filename: expected a quoted string, got '{text}'"
  | _ => .error s!"malformed source_filename line '{String.intercalate " " l}'"

/-- Check a `target datalayout` or `target triple` line and drop it: the model
has no target identity, and the extents a layout does determine are computed
where a struct definition is read. -/
def checkTargetLine (l : List String) : Except String Unit :=
  match l with
  | "target" :: "datalayout" :: "=" :: value =>
      match stringLiteral value with
      | .ok text =>
          match parseDataLayout text with
          | .ok _ => .ok ()
          | .error e => .error e
      | .error e => .error e
  | "target" :: "triple" :: "=" :: value =>
      match stringLiteral value with
      | .ok text => if text.isEmpty then .error "malformed target triple: an empty string" else .ok ()
      | .error e => .error e
  | "target" :: key :: _ => .error s!"unsupported target declaration 'target {key}'"
  | _ => .error s!"malformed target line '{String.intercalate " " l}'"

/-- Check an `attributes #N = { ... }` line and drop it.  The group's members
are classified where a header refers to them (`checkFunctionAttrs`); here only
the `attributes #N = { ... }` shape and its brace balance are checked, so an
unused group cannot decide the module. -/
def checkAttributeGroup (l : List String) : Except String Unit := do
  let _ ← attributeGroupOf l
  pure ()

/-- Check a global's definition line and drop it.  The model has no global
table: a symbol operand's value is the address the run binds to the symbol, so
the initializer has nothing here to affect, and only the `@<name> =` shape is
checked.  The value is not read — it is a constant grammar of its own, and the
model's reader of a symbol is `Operand.global`, which consults the run rather
than the module. -/
def checkGlobalLine (l : List String) : Except String Unit :=
  match l with
  | name :: "=" :: value =>
      if name.length ≤ 1 || !name.startsWith "@" then
        .error s!"malformed global definition '{name}': a global needs a name after '@'"
      else if value.isEmpty then
        .error s!"malformed global definition '{name}': expected a value"
      else .ok ()
  | _ => .error s!"malformed global line '{String.intercalate " " l}'"

/-- Check a metadata definition line and drop it.  `!`-names and `!{...}`
values are a sub-grammar of their own (`metadata`, `token` and specialized
types) that the model has no reader for, so only the
`<name> = [distinct] !<value>` shape is checked. -/
def checkMetadataLine (l : List String) : Except String Unit :=
  match l with
  | name :: rest =>
      if !name.startsWith "!" then
        .error s!"malformed metadata line '{String.intercalate " " l}'"
      else match rest with
        | "=" :: value :: more =>
            if value.startsWith "!" then .ok ()
            else if value = "distinct" then
              match more with
              | v :: _ =>
                  if v.startsWith "!" then .ok ()
                  else .error s!"malformed metadata definition '{name}': expected a metadata value after 'distinct'"
              | [] => .error s!"malformed metadata definition '{name}': expected a metadata value after 'distinct'"
            else .error s!"malformed metadata definition '{name}': expected a metadata value"
        | _ => .error s!"malformed metadata definition '{name}': expected '= [!distinct] !<value>'"
  | [] => .error "malformed metadata line"

/-- Header tokens a function header — a definition's or a declaration's — may
carry before its return type and the model does not represent: linkage, the
preemption and visibility specifiers, the DLL storage class, and a calling
convention.  They say which definition the linker picks and how the call is
made; the model's `Calls` environment decides both from outside the module, and
there is no linkage or calling-convention semantics inside it, so dropping
them leaves nothing to affect.  The set is
closed: a token outside it is left in place, and the return-attribute reader
names it if it is not a return attribute either.

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
a return attribute: a definition's is read, checked and dropped by
`checkReturnAttrs`, and a declaration's is refused by name. -/
def dropHeaderSurface : List String → List String
  | [] => []
  | "cc" :: n :: rest =>
      if (parseNat n).isSome then dropHeaderSurface rest else "cc" :: n :: rest
  | t :: rest => if isHeaderSurface t then dropHeaderSurface rest else t :: rest

/-- The tokens between a `(` already consumed and the `)` that matches it, with
the tokens after the close.  The depth counts the groups opened inside, so a
nested group is kept whole and does not end the parameter list early: a
parameter's attribute (`range(i64 0, 65)`) has its own argument list, and the
`,` that follows it separates parameters rather than trailing the list. -/
def takeParenGroup (toks : List String) : Except String (List String × List String) :=
  let rec go (depth : Nat) (acc : List String) :
      List String → Except String (List String × List String)
    | [] => .error "unterminated parameter list: expected ')'"
    | ")" :: rest =>
        if depth = 0 then .ok (acc.reverse, rest)
        else go (depth - 1) (")" :: acc) rest
    | "(" :: rest => go (depth + 1) ("(" :: acc) rest
    | t :: rest => go depth (t :: acc) rest
  go 0 [] toks

/-! ### A definition's function attributes

A definition's header may carry attributes between the parameter list and the
body.  They are classified the same three ways the parameter attributes are,
because the same question decides each: does dropping it accept a caller
argument, a returned outcome, or a successor that the text makes undefined?

* **Dropped, because it constrains no caller and the model has no field.**
  `local_unnamed_addr` and `unnamed_addr` say the definition's address is not
  significant — a linker may merge it with another — and the model gives a
  symbol its value from the run's environment (`Calls`, `Operand.global`), with
  no address identity, no merge, and no comparison between definitions.  A
  function `align N` states the alignment of that same emitted function symbol;
  the model's addresses are untyped naturals and no call, load or store reads a
  function's alignment, so the attribute has nothing here to affect.  `nounwind`
  says this body does not unwind, and the model has no unwinding outcome at all —
  a call's outcome is the environment's value — so there is nothing to forbid.
  `mustprogress`, `willreturn`, `norecurse`, `nocallback`, `nofree`, `nosync`,
  `cold`, `speculatable` and `memory(...)` are claims about the emitted body's
  own control flow and memory effect, the reading the parameter list gives
  `readonly`, `nocapture` and `returned`: importing the body already takes them
  as true of it, and none constrains an argument or the returned outcome.
  `ssp`, `sspreq`, `sspstrong`, `uwtable` (with its optional `(sync)`/`(async)`
  argument) and the target/codegen string attributes (`"frame-pointer"`,
  `"min-legal-vector-width"`, `"no-trapping-math"`, `"probe-stack"`,
  `"stack-protector-buffer-size"`, `"target-cpu"`, `"target-features"`,
  `"zero-call-used-regs"`) select or record code generation for the emitted
  body; the model has no target, no frame and no stack protector, so it has no
  field for them.

* **Refused, because it changes what a call promises and a violation is
  undefined behaviour.**  `noreturn` says a call to this function has no
  successor; a body that returns violates it, and LLVM makes the caller's
  continuation undefined.  The model's `Calls` environment can still supply a
  returning outcome, so dropping the attribute would accept a control flow the
  text forbids.  `Function` has no field for the promise, so the definition is
  refused by name.

* **Refused, as unmodelled.**  Any other token, and a `#N` reference whose
  `attributes #N` line the module does not declare, is refused by name: the
  reader has no rule for it, and accepting it on syntax alone would publish a
  promise nothing here reads.  A group is resolved member by member rather than
  refused as a reference; a reference to another group from inside a group is
  refused as unmodelled.

The module's groups are collected before its functions are read, because a
`define` may refer to a group declared later in the file (the production
emission does). -/

/-- Function attributes that are claims about the emitted body or about the
definition's own address, with no caller obligation and no field in the model.
The reason for each group is in the section comment above. -/
def isDroppedFunctionAttr (t : String) : Bool :=
  ["nounwind", "mustprogress", "willreturn", "norecurse", "nocallback",
   "nofree", "nosync", "cold", "speculatable",
   "ssp", "sspreq", "sspstrong", "uwtable",
   "local_unnamed_addr", "unnamed_addr"].contains t

/-- The target and code-generation string attribute keys the reader knows.  The
set is closed: an unknown key is refused rather than dropped, because a string
attribute the reader has no rule for could change code generation in a way
nothing here reads. -/
def isDroppedStringAttrKey (t : String) : Bool :=
  ["frame-pointer", "min-legal-vector-width", "no-trapping-math",
   "probe-stack", "stack-protector-buffer-size", "target-cpu",
   "target-features", "zero-call-used-regs"].contains t

/-- Whether a token is one quoted string, as the tokenizer leaves it. -/
def isQuotedToken (t : String) : Bool :=
  match t.toList with
  | '"' :: _ => t.length ≥ 2 && t.toList.getLast? = some '"'
  | _ => false

/-- A quoted token's text without its surrounding quotes. -/
def unquoteToken (t : String) : String :=
  String.ofList ((t.toList.drop 1).dropLast)

/-- Consume a string attribute's value, which the tokenizer splits at the commas
inside it: the value ends at the first token that closes the quote. -/
def takeQuotedValue : List String → Except String (List String)
  | [] => .error "an attribute value opens a quote that is not closed"
  | t :: rest =>
      if t.toList.getLast? = some '"' then .ok rest else takeQuotedValue rest

/-- The memory locations and access kinds of `memory(...)`. -/
def isMemoryLocation (t : String) : Bool := ["argmem", "inaccessiblemem"].contains t
def isMemoryEffect (t : String) : Bool := ["none", "read", "write", "readwrite"].contains t

/-- Check a `memory(...)` argument: `none`, or comma-separated
`<location> : <effect>` groups. -/
def checkMemoryAttrArg (arg : List String) : Except String Unit :=
  if arg = ["none"] then .ok ()
  else
    let chunks := splitCallArgs arg
    if chunks.isEmpty then .error "the function attribute 'memory' has an empty argument"
    else chunks.foldlM (fun _ c =>
      match c with
      | [loc, ":", eff] =>
          if isMemoryLocation loc && isMemoryEffect eff then .ok ()
          else .error s!"the function attribute 'memory' names an unknown location or \
              effect: '{String.intercalate " " c}'"
      | _ => .error s!"the function attribute 'memory' needs a location, ':' and an \
          effect, got '{String.intercalate " " c}'") ()

/-- Look an attribute group up by its `#N` spelling. -/
def lookupAttributeGroup (groups : AttributeGroups) (id : String) : Option (List String) :=
  (groups.find? (fun g => g.1 = id)).map (fun g => g.2)

/-- Read a definition's attribute tail, resolving a `#N` reference to the
group's own members and classifying each one.  The reasons are in the section
comment above.  A group's members are spliced in front of the tail, so the walk
stays structurally recursive on its fuel; a group may not refer to another
group, which bounds the splice. -/
def checkFunctionAttrs (name : String) (groups : AttributeGroups)
    (toks : List String) : Except String Unit :=
  let fuel := toks.length + (groups.foldl (fun acc g => acc + g.2.length + 1) 0) + 1
  let rec go : Nat → List String → Except String Unit
    | 0, _ => .error "internal parser error: function attribute fuel exhausted"
    | _, [] => .ok ()
    | fuel + 1, t :: rest =>
        if t.startsWith "#" then
          match lookupAttributeGroup groups t with
          | none =>
              .error s!"unsupported attribute group '{t}' after the parameter list of \
                  @{name}: the module declares no 'attributes {t}' line"
          | some body =>
              if body.any (fun b => b.startsWith "#") then
                .error s!"unsupported nested attribute group reference in '{t}' after the \
                    parameter list of @{name}: a group that refers to another group is not \
                    modelled"
              else go fuel (body ++ rest)
        else if t = "align" then
          match rest with
          | n :: rest' =>
              if (parseNat n).isSome then go fuel rest'
              else .error s!"the function attribute 'align' needs a decimal alignment, \
                  got '{n}'"
          | [] => .error s!"the function attribute 'align' after the parameter list of \
              @{name} needs a decimal alignment"
        else if t = "noreturn" then
          .error s!"unsupported function attribute 'noreturn' after the parameter list of \
              @{name}: it promises that a call has no successor, a returning body makes the \
              caller's continuation undefined behaviour, and the model has no field to carry \
              the promise"
        else if t = "memory" then
          match rest with
          | "(" :: more => do
              let (arg, rest') ← takeParenGroup more
              checkMemoryAttrArg arg
              go fuel rest'
          | _ => .error s!"malformed function attribute 'memory' after the parameter list \
              of @{name}: expected a parenthesised argument"
        else if t = "uwtable" then
          match rest with
          | "(" :: arg :: ")" :: rest' =>
              if arg = "sync" || arg = "async" then go fuel rest'
              else .error s!"the function attribute 'uwtable' takes 'sync' or 'async', \
                  got '{arg}'"
          | _ => go fuel rest
        else if isDroppedFunctionAttr t then go fuel rest
        else if t.startsWith "\"" then
          match rest with
          | "=" :: v :: more =>
              if !isQuotedToken t then
                .error s!"malformed function attribute '{t}' after the parameter list \
                    of @{name}"
              else if !isDroppedStringAttrKey (unquoteToken t) then
                .error s!"unsupported string function attribute '{t}' after the parameter \
                    list of @{name}: the reader has no rule for it"
              else if !v.startsWith "\"" then
                .error s!"the function attribute '{t}' needs a quoted value, got '{v}'"
              else do
                let rest' ← takeQuotedValue (v :: more)
                go fuel rest'
          | _ => .error s!"malformed function attribute '{t}' after the parameter list of \
              @{name}: expected '=' and a quoted value"
        else
          .error s!"unsupported function attribute '{t}' after the parameter list of @{name}"
  go fuel toks

def parseFunction (layout : Layout) (groups : AttributeGroups) (header : List String)
    (rest : List (List String)) :
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
  -- is read, checked for the shape its name requires, and dropped.  It can only
  -- *exclude* return values — a violating value is poison — so dropping it
  -- models a superset of the text's defined values; the reason is with
  -- `checkReturnAttrs`.
  let beforeName := header.takeWhile (· ≠ nameTok)
  let returnAttrs := dropHeaderSurface ((beforeName.drop 1).dropLast)
  checkReturnAttrs name returnAttrs
  let retTy ← parseTy retTok
  let (params, afterParams) ←
    match parseParams afterName with
    | .ok pr => .ok pr
    | .error e => .error s!"in parameters of @{name}: {e}"
  -- A function attribute stands between the parameter list and the body.  It is
  -- read and classified by `checkFunctionAttrs`, whose section comment gives the
  -- three-way split and each reason.
  let (functionAttrs, hasBody) :=
    match afterParams.reverse with
    | "{" :: rev => (rev.reverse, true)
    | _ => (afterParams, false)
  if !hasBody then
    throw s!"malformed function header of @{name}: expected an opening brace after the parameter list"
  checkFunctionAttrs name groups functionAttrs
  let (body, rest') ← takeBody rest
  let blocks ← parseBlocks layout body
  let f : Function := ⟨name, retTy, params, blocks⟩
  match checkDefinitions f with
  | .error e => throw e
  | .ok _ =>
      match checkPhiTypes f with
      | .error e => throw e
      | .ok _ =>
          match checkICmpPtrTypes f with
          | .error e => throw e
          | .ok _ =>
              match checkStoreValues f with
              | .error e => throw e
              | .ok _ =>
                  match checkCastTypes f with
                  | .error e => throw e
                  | .ok _ => .ok (f, rest')

/-- Read one declaration parameter from the tokens between two commas: its type
and, optionally, a `%name`.  `Decl` carries parameter types and no names, so a
name is dropped.  An attribute constrains the parameter's value and no field
here reads the constraint, so it is refused by name with the parameter's
position; the attribute set is the call argument one, because LLVM writes the
same attribute grammar in both places. -/
def parseDeclParam (fn : String) (idx : Nat) (toks : List String) :
    Except String Ty :=
  match toks with
  | [] => .error s!"parameter {idx} of @{fn} is empty"
  | tyTok :: rest =>
      if callArgAttributes.contains tyTok then
        .error s!"parameter {idx} of @{fn} carries the attribute '{tyTok}', which is \
            not modelled: it constrains the parameter's value and no field here \
            reads the constraint"
      else
        match parseTy tyTok with
        | .error e => .error s!"in parameter {idx} of @{fn}: {e}"
        | .ok ty =>
            match rest with
            | [] => .ok ty
            | [nameTok] =>
                if nameTok.startsWith "%" then .ok ty
                else .error s!"parameter {idx} of @{fn} carries the attribute \
                    '{nameTok}', which is not modelled: it constrains the \
                    parameter's value and no field here reads the constraint"
            | attr :: _ =>
                .error s!"parameter {idx} of @{fn} carries the attribute '{attr}', \
                    which is not modelled: it constrains the parameter's value and \
                    no field here reads the constraint"

/-- Parse a `declare ret @name(types)` line.  The header is checked the way a
function definition's is: linkage, visibility and a calling convention before
the return type are accepted and dropped because the model has none of their
semantics, a return attribute in that position is refused, and every token
after the closing parenthesis — a function attribute, an attribute group
reference, `unnamed_addr`, an address space, a section, an alignment, a
metadata attachment — is refused, because none has a field here and dropping it
would accept a wider promise than the text makes.  A parameter's type is read
and a parameter name is dropped; a parameter attribute and a variable argument
list are refused by name. -/
def parseDecl (l : List String) : Except String Decl := do
  match l with
  | "declare" :: rest =>
      let (retTok?, nameTok, afterName) ←
        match findAt none rest with
        | some x => .ok x
        | none => .error s!"malformed declaration '{String.intercalate " " l}'"
      let retTok ← match retTok? with
        | some t => .ok t
        | none => .error s!"declaration of '{String.intercalate " " l}' has \
            no return type"
      let name := (nameTok.drop 1).toString
      -- A return attribute stands where a definition's does and is refused for
      -- the same reason: it constrains the value the declared function returns,
      -- which no field here reads.
      let beforeName := rest.takeWhile (· ≠ nameTok)
      let returnAttrs := dropHeaderSurface beforeName.dropLast
      if !returnAttrs.isEmpty then
        throw s!"unsupported return attribute '{String.intercalate " " returnAttrs}' \
            before the return type of @{name}"
      let retTy ← parseTy retTok
      let (paramToks, trailing) ←
        match afterName with
        | "(" :: ts => takeParenGroup ts
        | _ => .error s!"expected '(' after @{name} in the declaration"
      if !trailing.isEmpty then
        let joined := String.intercalate " " trailing
        if trailing.head!.startsWith "#" then
          throw s!"unsupported attribute group '{joined}' after the parameter \
              list of @{name}"
        else
          throw s!"unsupported token(s) '{joined}' after the parameter list of \
              @{name}"
      let chunks := match splitCallArgs paramToks with
        | [[]] => []
        | cs => cs
      let rec readParams (idx : Nat) :
          List (List String) → Except String (List Ty)
        | [] => .ok []
        | ["..."] :: _ =>
            .error s!"variable argument list '...' in the declaration of @{name} \
                is not modelled"
        | c :: cs => do
            let ty ← parseDeclParam name idx c
            let rest ← readParams (idx + 1) cs
            .ok (ty :: rest)
      let params ← readParams 1 chunks
      .ok { name := name, retTy := retTy, params := params }
  | _ => .error s!"malformed declaration '{String.intercalate " " l}'"

/-- Parse a module: its header, then its declarations, then its function
definitions.  The header — `source_filename`, the two `target` lines, named type
definitions, globals, attribute groups and metadata nodes — is read, checked for
the shape it must have, and dropped, because `Module` has no field for any of it.
A named struct definition is not merely dropped: its byte extent is computed from
its fields and the target data layout, because a body's `alloca` needs an extent
and the declared `Layout` may not carry it.  The lines are read twice: a first
pass collects the data layout and the type definitions (a body's braces are
skipped by depth, since the tokenizer drops indentation), so a struct may name
one defined later in the same header, and the second walks the module in order.
-/
def parseModuleWith (layout : Layout) (src : String) : Except String Module := do
  let lines := tokenLines src
  let (dl, types, groups) ← scanHeader lines
  let effective ← resolveNamedTypes layout dl types
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
            match parseFunction effective groups l rest with
            | .error e => .error e
            | .ok (f, rest') => go fuel rest' decls (f :: acc)
        | ["}"] => go fuel rest decls acc
        | "source_filename" :: _ =>
            match checkSourceFilename l with
            | .error e => .error e
            | .ok _ => go fuel rest decls acc
        | "target" :: _ =>
            match checkTargetLine l with
            | .error e => .error e
            | .ok _ => go fuel rest decls acc
        | "attributes" :: _ =>
            match checkAttributeGroup l with
            | .error e => .error e
            | .ok _ => go fuel rest decls acc
        | name :: "=" :: "type" :: _ =>
            if name.startsWith "%" then go fuel rest decls acc
            else .error s!"expected a module declaration, 'define' or 'declare', got '{String.intercalate " " l}'"
        | name :: "=" :: _ =>
            if name.startsWith "@" then
              match checkGlobalLine l with
              | .error e => .error e
              | .ok _ => go fuel rest decls acc
            else if name.startsWith "!" then
              match checkMetadataLine l with
              | .error e => .error e
              | .ok _ => go fuel rest decls acc
            else .error s!"expected a module declaration, 'define' or 'declare', got '{String.intercalate " " l}'"
        | t :: _ =>
            if t.startsWith "!" then
              match checkMetadataLine l with
              | .error e => .error e
              | .ok _ => go fuel rest decls acc
            else .error s!"expected a module declaration, 'define' or 'declare', got '{String.intercalate " " l}'"
        | [] => go fuel rest decls acc
  go (lines.length + 1) lines [] []


/-- Parse a module with no declared struct layouts: the entry point every
existing caller uses.  A named struct's extent, when its text carries one, is
computed from the module's own `%struct.X = type` definition and the target data
layout; a text that carries none is refused by name when an `alloca` names a
struct, which is the same refusal a declared layout's absence gives. -/
def parseModule (src : String) : Except String Module := parseModuleWith [] src

end LeanLLVM
