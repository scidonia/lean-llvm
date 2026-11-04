/-
The scalar reference parser: recursive descent over bytes, well founded on the
bytes it consumes.

There is no step budget.  `parseValue` consumes a container's opening delimiter
itself and parses a first element, key or member at a strictly greater index; the
tails are entered at the raw cursor after a value and compute `skipFrom`
themselves before looking for a separator.  Every recursive call therefore starts
at a strictly greater index, the measure `bs.length - i` decreases on every edge,
and the progress fields (`Parsed.consumed`, `ArrayTail.moved`,
`ObjectTail.moved`) carry the decrease that a caller cannot otherwise prove.

The parser mentions neither `RfcText` nor `StrictText`: it is written against
bytes and the scanners, and the relation to the grammar is established only by
the theorems in `Correct`.
-/
import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Tape

namespace LeanLLVM.JSON

/-- Resource limits for one parse.  A limit is a policy bound on one call, not an
allocation strategy: exceeding one is reported as a limit outcome and says
nothing about whether the input is valid JSON.  RFC 8259 §9 (size, nesting depth)
and §6 (numeric range and precision) are the clauses that permit them. -/
structure Limits where
  maxInput : Nat
  maxDepth : Nat
  maxTokens : Nat
deriving DecidableEq, Repr

/-- The J1 defaults: 1 MiB, 128 levels, 1 Mi tokens. -/
def Limits.default : Limits :=
  { maxInput := 1048576, maxDepth := 128, maxTokens := 1048576 }

/-- Why a syntax check failed.  These name the construct that was refused; the
exact reason, its position and any text rendered from them are diagnostic and no
theorem depends on which one is chosen. -/
inductive Reject where
  | unexpectedEnd (pos : Nat)
  | unexpectedByte (pos : Nat) (found : UInt8)
  | badLiteral (pos : Nat) (lit : Bytes)
  | badNumber (pos : Nat)
  | unterminatedString (pos : Nat)
  | badEscape (pos : Nat)
  | badUTF8 (pos : Nat)
  | unpairedSurrogate (pos : Nat)
  | noncharacter (pos : Nat)
  | controlCharacter (pos : Nat)
  | expectedColon (pos : Nat)
  | expectedComma (pos : Nat)
  | expectedCloseBracket (pos : Nat)
  | expectedCloseBrace (pos : Nat)
  | trailingData (pos : Nat)
  | byteOrderMark
deriving DecidableEq, Repr

/-- The four contract outcomes.  They are separate constructors, so no value is
both a syntax rejection and a limit exhaustion, and `invalid` is the only one that
carries a validity claim (`parseRef_sound`).  `unpairedSurrogate` and
`noncharacter` are `Policy` refusals: their input *is* an RFC text, and the
outcome says which restriction refused it. -/
inductive ParseError where
  | invalid (reason : Reject)
  | inputTooLong
  | depthExceeded
  | outOfCapacity
deriving DecidableEq, Repr

inductive ParseResult where
  | ok (tape : Tape)
  | error (error : ParseError)
deriving DecidableEq, Repr

/-- The recursive core's outcome: a result, or the refusal with its reason.  There
is no exhausted case: the recursion is well founded on the bytes consumed, so
nothing can run out. -/
inductive Step (α : Type) where
  | done (a : α)
  | fail (e : ParseError)

/-- One parsed value, indexed by the index it started at.  `consumed` is not
commentary: an element tail's continuation calls the tail at the index a value
ended at, and that call's decreasing obligation needs `src < next` for the value
it just parsed, which cannot be proved from the value parser's code without being
circular.  Carrying the proof in the result is what makes the measure work. -/
structure Parsed (src : Nat) where
  tokens : List Token
  value : Value
  next : Nat
  consumed : src < next

/-- An array's element tail, entered at the raw cursor after a value.  `moved`
records that the tail never moves backwards, which is what the member/element
recursion needs at its continuation. -/
structure ArrayTail (src : Nat) where
  tokens : List Token
  values : List Value
  next : Nat
  moved : src ≤ next

/-- An object's member tail. -/
structure ObjectTail (src : Nat) where
  tokens : List Token
  members : List (List Nat × Value)
  next : Nat
  moved : src ≤ next

/-- The three literal keywords, so `parseLiteral` is told which one it is
parsing rather than recovering it from the value. -/
inductive LitTag where
  | null | true | false
deriving DecidableEq, Repr

/-- A parsed object key: its token, the decoded name, the index past the closing
quote, and the proof it consumed.  Separate from `Parsed` because the object
branch needs the name itself, not a `Value` it would have to take apart. -/
structure Key (src : Nat) where
  token : Token
  name : List Nat
  next : Nat
  consumed : src < next

/-- An index that is known to be inside the input, from a successful lookup. -/
theorem length_gt_of_get? {bs : Bytes} {i : Nat} {b : UInt8} (h : bs[i]? = some b) :
    i < bs.length := by
  have h' : bs.toList[i]? = some b := by
    rw [ByteString.toList_getElem?_eq_getElem?]
    exact h
  have := (List.getElem?_eq_some_iff.mp h').1
  rw [ByteString.length_eq_size, ← ByteString.toList_length]
  exact this

/-- The one place a `ScanError` becomes a `Reject`.  `ended` is why
`Reject.unterminatedString` is reachable at all. -/
def rejectOf (i : Nat) : ScanError → Reject
  | .ended => .unterminatedString i
  | .badEscape k => .badEscape (i + 1 + k)
  | .badUTF8 k => .badUTF8 (i + 1 + k)
  | .controlCharacter k => .controlCharacter (i + 1 + k)
  | .unpairedSurrogate k => .unpairedSurrogate (i + 1 + k)
  | .noncharacter k => .noncharacter (i + 1 + k)


/-- `string` as RFC 8259 §7 defines it: a quote, a body, a quote.  `scanCharsEnd`
is given the index of the body's first byte and returns the index past the
closing quote, so the scan reads the caller's buffer at a position and copies
neither the body's suffix nor the bytes past its end. -/
def parseKey (bs : Bytes) (i : Nat) : Step (Key i) :=
  match hb : bs[i]? with
  | some 0x22 =>
      match hs : scanCharsEnd bs (i + 1) 0 with
      | .error e => .fail (.invalid (rejectOf i e))
      | .ok (cs, stop) =>
          .done { token := .string ⟨i, stop.val⟩, name := cs, next := stop.val,
                  consumed := by
                    obtain ⟨rest, hrest, hdrop⟩ := scanCharsEnd_sound hs
                    have hok : scanChars (bs.drop (i + 1)) = .ok (cs, rest) := by
                      rw [scanChars_eq]; exact hrest
                    have hstr := (scanChars_iff _ _ _).mp hok
                    have hlt := strChars_suffix_lt hstr
                    rw [ByteString.length_drop] at hlt
                    have hlen : (bs.drop stop.val).length = bs.length - stop.val :=
                      ByteString.length_drop bs stop.val
                    rw [hdrop] at hlen
                    have hi : i < bs.length := length_gt_of_get? hb
                    have hle := stop.2
                    omega }
  | _ => .fail (.invalid (.unexpectedByte i (bs[i]?.getD 0)))

/-- `parseString` is `parseKey` with the name kept as a value. -/
def parseString (bs : Bytes) (i : Nat) : Step (Parsed i) :=
  match parseKey bs i with
  | .fail e => .fail e
  | .done k =>
      .done { tokens := [k.token], value := .string k.name, next := k.next,
              consumed := k.consumed }

/-- `number`: the maximal run of number constituents, validated by the grammar.
A run that is not a number is refused here; a run that is a number but ends where
the enclosing production cannot use it is refused by the caller, which is why the
soundness lemma carries the boundary condition. -/
def parseNumber (bs : Bytes) (i : Nat) : Step (Parsed i) :=
  let lex := numRunFrom bs i
  if h : numLexB lex then
    .done { tokens := [.number ⟨i, i + lex.length⟩], value := .number lex,
            next := i + lex.length,
            consumed := by
              have hpos := numLexB_nonempty lex h
              have hlen := numRunFrom_length_le bs i
              omega }
  else .fail (.invalid (.badNumber i))

/-- `literal`: the keyword is given, so the parse is a prefix test and a span. -/
def parseLiteral (bs : Bytes) (i : Nat) (lit : Bytes) (tag : LitTag)
    (hlit : 0 < lit.length) : Step (Parsed i) :=
  match hl : HasPrefixB bs i lit with
  | true =>
      let s : Span := ⟨i, i + lit.length⟩
      .done { tokens := [match tag with
                         | .null => .null s
                         | .true => .bool true s
                         | .false => .bool false s]
              value := match tag with
                       | .null => .null
                       | .true => .bool true
                       | .false => .bool false
              next := i + lit.length
              consumed := by omega }
  | false => .fail (.invalid (.badLiteral i lit))

mutual

/-- Parse one value at `i`.  A container's opening delimiter is consumed here, and
its first element, key or member is parsed at a strictly greater index. -/
def parseValue (bs : Bytes) (i depth : Nat) : Step (Parsed i) :=
  match hb : bs[i]? with
  | none => .fail (.invalid (.unexpectedEnd i))
  | some 0x5B =>
      if depth = 0 then .fail .depthExceeded
      else
        have hi : i < bs.length := length_gt_of_get? hb
        let first := skipFrom bs (i + 1)
        have hfirst : i < first := by have := skipFrom_ge bs (i + 1); omega
        if decide (bs[first]? = some 0x5D) then
          .done { tokens := [.punct .openBracket ⟨i, i + 1⟩,
                             .punct .closeBracket ⟨first, first + 1⟩]
                  value := .array []
                  next := first + 1
                  consumed := by omega }
        else
          match parseValue bs first (depth - 1) with
          | .fail e => .fail e
          | .done pv =>
            have hnext : i < pv.next := by have := pv.consumed; omega
            match parseElemsTail bs pv.next (depth - 1) with
            | .fail e => .fail e
            | .done t =>
              if decide (bs[t.next]? = some 0x5D) then
                .done { tokens := .punct .openBracket ⟨i, i + 1⟩ ::
                                   pv.tokens ++ t.tokens ++
                                   [.punct .closeBracket ⟨t.next, t.next + 1⟩]
                        value := .array (pv.value :: t.values)
                        next := t.next + 1
                        consumed := by
                          have := t.moved
                          omega }
              else .fail (.invalid (.expectedCloseBracket t.next))
  | some 0x7B =>
      if depth = 0 then .fail .depthExceeded
      else
        have hi : i < bs.length := length_gt_of_get? hb
        let first := skipFrom bs (i + 1)
        have hfirst : i < first := by have := skipFrom_ge bs (i + 1); omega
        if decide (bs[first]? = some 0x7D) then
          .done { tokens := [.punct .openBrace ⟨i, i + 1⟩,
                             .punct .closeBrace ⟨first, first + 1⟩]
                  value := .object []
                  next := first + 1
                  consumed := by omega }
        else
          match parseKey bs first with
          | .fail e => .fail e
          | .done k =>
            have hknext : i < k.next := by have := k.consumed; omega
            have hcolon : i < skipFrom bs k.next := by
              have h1 := skipFrom_ge bs k.next; omega
            if !decide (bs[skipFrom bs k.next]? = some 0x3A) then
              .fail (.invalid (.expectedColon (skipFrom bs k.next)))
            else
              have hcolonpos : i < skipFrom bs (skipFrom bs k.next + 1) := by
                have h1 := skipFrom_ge bs (skipFrom bs k.next + 1)
                omega
              match parseValue bs (skipFrom bs (skipFrom bs k.next + 1)) (depth - 1) with
              | .fail e => .fail e
              | .done pv =>
                have hpos : i < pv.next := by
                  have h1 := skipFrom_ge bs (skipFrom bs k.next + 1)
                  have h2 := pv.consumed
                  omega
                match parseMembersTail bs pv.next (depth - 1) with
                | .fail e => .fail e
                | .done t =>
                  if decide (bs[t.next]? = some 0x7D) then
                    .done { tokens := .punct .openBrace ⟨i, i + 1⟩ :: k.token ::
                                       [.punct .colon ⟨skipFrom bs k.next,
                                                       skipFrom bs k.next + 1⟩] ++
                                       pv.tokens ++ t.tokens ++
                                       [.punct .closeBrace ⟨t.next, t.next + 1⟩]
                            value := .object ((k.name, pv.value) :: t.members)
                            next := t.next + 1
                            consumed := by
                              have := t.moved
                              omega }
                  else .fail (.invalid (.expectedCloseBrace t.next))
  | some 0x22 => parseString bs i
  | some 0x74 => parseLiteral bs i (ByteString.literal [0x74, 0x72, 0x75, 0x65]) .true (by decide)
  | some 0x66 =>
      parseLiteral bs i (ByteString.literal [0x66, 0x61, 0x6C, 0x73, 0x65]) .false (by decide)
  | some 0x6E =>
      parseLiteral bs i (ByteString.literal [0x6E, 0x75, 0x6C, 0x6C]) .null (by decide)
  | some b =>
      if decide (b = 0x2D) || IsDigitB b then parseNumber bs i
      else .fail (.invalid (.unexpectedByte i b))
termination_by bs.length - i
decreasing_by all_goals omega

/-- The element tail, entered at the raw cursor after a value: skip whitespace,
then a comma and the next element, or stop.  Every recursive call starts at a
strictly greater index, which is why the measure needs no budget. -/
def parseElemsTail (bs : Bytes) (i depth : Nat) : Step (ArrayTail i) :=
  match hc : bs[skipFrom bs i]? with
  | some 0x2C =>
      have hcomma : skipFrom bs i < bs.length := length_gt_of_get? hc
      have hi : i < bs.length := by have := skipFrom_ge bs i; omega
      have hpos : i < skipFrom bs (skipFrom bs i + 1) := by
        have h1 := skipFrom_ge bs i
        have h2 := skipFrom_ge bs (skipFrom bs i + 1)
        omega
      match parseValue bs (skipFrom bs (skipFrom bs i + 1)) depth with
      | .fail e => .fail e
      | .done pv =>
        have hnext : i < pv.next := by have := pv.consumed; omega
        match parseElemsTail bs pv.next depth with
        | .fail e => .fail e
        | .done t =>
          .done { tokens := .punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ ::
                             pv.tokens ++ t.tokens
                  values := pv.value :: t.values
                  next := t.next
                  moved := by have := t.moved; omega }
  | _ => .done { tokens := [], values := [], next := skipFrom bs i,
                 moved := by have := skipFrom_ge bs i; omega }
termination_by bs.length - i
decreasing_by all_goals omega

/-- The member tail.  The key/colon/value code is repeated from `parseValue`'s
object branch rather than shared, because a helper taking the matched head and
the tail apart is called with a token list of the same length, which breaks no
termination here but does duplicate nothing worth a lemma. -/
def parseMembersTail (bs : Bytes) (i depth : Nat) : Step (ObjectTail i) :=
  match hc : bs[skipFrom bs i]? with
  | some 0x2C =>
      have hcomma : skipFrom bs i < bs.length := length_gt_of_get? hc
      have hi : i < bs.length := by have := skipFrom_ge bs i; omega
      have hpos : i < skipFrom bs (skipFrom bs i + 1) := by
        have h1 := skipFrom_ge bs i
        have h2 := skipFrom_ge bs (skipFrom bs i + 1)
        omega
      match parseKey bs (skipFrom bs (skipFrom bs i + 1)) with
      | .fail e => .fail e
      | .done k =>
        have hknext : i < k.next := by have := k.consumed; omega
        have hcolon : i < skipFrom bs k.next := by
          have h1 := skipFrom_ge bs k.next; omega
        if !decide (bs[skipFrom bs k.next]? = some 0x3A) then
          .fail (.invalid (.expectedColon (skipFrom bs k.next)))
        else
          have hcolonpos : i < skipFrom bs (skipFrom bs k.next + 1) := by
            have h1 := skipFrom_ge bs (skipFrom bs k.next + 1)
            omega
          match parseValue bs (skipFrom bs (skipFrom bs k.next + 1)) depth with
          | .fail e => .fail e
          | .done pv =>
            have hnext : i < pv.next := by
              have h1 := skipFrom_ge bs (skipFrom bs k.next + 1)
              have h2 := pv.consumed
              omega
            match parseMembersTail bs pv.next depth with
            | .fail e => .fail e
            | .done t =>
              .done { tokens := .punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ ::
                                 k.token ::
                                 [.punct .colon ⟨skipFrom bs k.next,
                                                 skipFrom bs k.next + 1⟩] ++
                                 pv.tokens ++ t.tokens
                      members := (k.name, pv.value) :: t.members
                      next := t.next
                      moved := by have := t.moved; omega }
  | _ => .done { tokens := [], members := [], next := skipFrom bs i,
                 moved := by have := skipFrom_ge bs i; omega }
termination_by bs.length - i
decreasing_by all_goals omega

end

/-- The whole-document parse.  Outcome priority is fixed here: input length, then
byte-order mark, then syntax, then token capacity. -/
def parseBytes (l : Limits) (bs : Bytes) : ParseResult :=
  if bs.length > l.maxInput then .error .inputTooLong
  else if bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF] then
    .error (.invalid .byteOrderMark)
  else
    match parseValue bs (skipFrom bs 0) l.maxDepth with
    | .done p =>
        if skipFrom bs p.next < bs.length then
          .error (.invalid (.trailingData (skipFrom bs p.next)))
        else if p.tokens.length ≤ l.maxTokens then .ok ⟨bs, p.tokens⟩
        else .error .outOfCapacity
    | .fail e => .error e

/-- The contract's public entry point.  `ByteArray` is the carrier, so `input` is
`Bytes` itself: the tape the parse returns is index-based over the caller's bytes,
with no conversion and no copy.  A consumer that wants to read the caller's buffer
takes the tape's spans. -/
def parseDocument (l : Limits) (input : ByteArray) : ParseResult :=
  parseBytes l input

end LeanLLVM.JSON
