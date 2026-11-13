/-
The scanners: the computable reflections of the string and number productions.

The string scanner returns the refusal reason, because the contract's diagnostic
row names `Policy` refusals (`unpairedSurrogate`, `noncharacter`) and the scenario
asserts them.  The number scan needs no reason type: a number has one refusal.
-/
import LeanLLVM.JSON.Spec

namespace LeanLLVM.JSON

open ByteString

/-- Why a string body was refused.  The offset is relative to the subject;
`parseString` adds the opening quote's index.  No theorem depends on the reason or
the offset — the contract's diagnostics row leaves them out of the equivalence —
so this type exists for the executable's report and for the scenario's assertions.
`ended` is the one reason that is about the subject running out rather than about
a byte: it is what makes `Reject.unterminatedString` reachable. -/
inductive ScanError where
  | ended
  | badEscape (offset : Nat)
  | badUTF8 (offset : Nat)
  | controlCharacter (offset : Nat)
  | unpairedSurrogate (offset : Nat)
  | noncharacter (offset : Nat)
deriving DecidableEq, Repr

/-- The accepting continuation of a scanned character: RFC 7493 §2.1 refuses a
noncharacter wherever it appears, so every accepting branch funnels through this
step, and a refusal of the body passes through it unchanged. -/
def okCons (pos c : Nat) (r : Except ScanError (List Nat × Bytes)) :
    Except ScanError (List Nat × Bytes) :=
  if IsNoncharacter c then .error (.noncharacter pos)
  else
    match r with
    | .error e => .error e
    | .ok (cs, fin) => .ok (c :: cs, fin)

/-- The same step over an index record: the accepted character is prepended to
the code points, and the index the scan stopped at passes through unchanged.
This is the form a caller that reads the carrier at a position uses, because it
never materialises the remainder as a carrier. -/
private def okConsIx (pos c : Nat) (r : Except ScanError (List Nat × Nat)) :
    Except ScanError (List Nat × Nat) :=
  if IsNoncharacter c then .error (.noncharacter pos)
  else
    match r with
    | .error e => .error e
    | .ok (cs, fin) => .ok (c :: cs, fin)

/-- The string body scan, over the carrier's list view: the one definition of
the scan.  It returns carrier remainders, so `scanCharsFrom` is this function
applied to `bs.data.toList` and no conversion stands between them. -/
private def scanCharsL (off : Nat) : List UInt8 → Except ScanError (List Nat × Bytes)
  | [] => .error .ended
  | 0x22 :: rest => .ok ([], literal rest)
  | 0x5C :: rest =>
      match rest with
      | [] => .error .ended
      | e :: rest1 =>
          match EscVal e with
          | some c => okCons off c (scanCharsL (off + 2) rest1)
          | none =>
              if e = 0x75 then
                match rest1 with
                | h0 :: h1 :: h2 :: h3 :: rest2 =>
                    match Hex4 h0 h1 h2 h3 with
                    | some c =>
                        if 0xD800 ≤ c ∧ c ≤ 0xDBFF then
                          match rest2 with
                          | 0x5C :: 0x75 :: l0 :: l1 :: l2 :: l3 :: rest3 =>
                              match Hex4 l0 l1 l2 l3 with
                              | some lo =>
                                  if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                                    okCons off (0x10000 + (c - 0xD800) * 0x400 +
                                      (lo - 0xDC00))
                                      (scanCharsL (off + 12) rest3)
                                  else .error (.unpairedSurrogate off)
                              | none => .error (.badEscape (off + 8))
                          | _ => .error (.unpairedSurrogate off)
                        else if 0xDC00 ≤ c ∧ c ≤ 0xDFFF then
                          .error (.unpairedSurrogate off)
                        else okCons off c (scanCharsL (off + 6) rest2)
                    | none => .error (.badEscape (off + 2))
                | _ => .error .ended
              else .error (.badEscape off)
  | b :: rest =>
      if b.toNat < 0x80 then
        if 0x20 ≤ b.toNat then okCons off b.toNat (scanCharsL (off + 1) rest)
        else .error (.controlCharacter off)
      else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then
        match rest with
        | b1 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then
              okCons off ((b.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80))
                (scanCharsL (off + 2) rest1)
            else .error (.badUTF8 off)
        | [] => .error .ended
      else if b = 0xE0 then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okCons off ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                (scanCharsL (off + 3) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okCons off ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80))
                (scanCharsL (off + 3) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xED then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okCons off (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                (scanCharsL (off + 3) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okCons off ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80))
                (scanCharsL (off + 3) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xF0 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              okCons off ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
                  (b3.toNat - 0x80))
                (scanCharsL (off + 4) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              okCons off ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
                  (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                (scanCharsL (off + 4) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xF4 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              okCons off (0x100000 + (b1.toNat - 0x80) * 0x1000 +
                  (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                (scanCharsL (off + 4) rest1)
            else .error (.badUTF8 off)
        | _ => .error .ended
      else .error (.badUTF8 off)

/-- Decode a string body — the bytes after the opening quote — to the code points
and the remainder, which begins *after* the closing quote (`StrChars`'s `nil`
clause consumes it), or say why it was refused.  The discipline is `StrChar
.strict`, so an unpaired escape and a noncharacter are refused with their own
reasons, and a subject that ends before the quote is `ended`.  `off` is the
position of the argument within the body, so a refusal can name it. -/
def scanCharsFrom (off : Nat) (bs : Bytes) : Except ScanError (List Nat × Bytes) :=
  scanCharsL off bs.data.toList

/-- The continuation of an accepted character: the same step as `okCons`, stated
over the remainder of the body. -/
def scanCons (pos next : Nat) (c : Nat) (rest : Bytes) :
    Except ScanError (List Nat × Bytes) :=
  okCons pos c (scanCharsFrom next rest)

/-- The tail of the subject from index `j`: one `Array.extract` into a fresh
array.  `scanChars` takes it once, at the closing quote; the position scan
records the index instead and copies nothing. -/
private def tailFrom (bs : Bytes) (j : Nat) : Bytes := bs.extract j bs.size

/-- The string body scan from index `i`, read at that index: `scanCharsL`'s
branches with the list view replaced by lookups, recording the index of the byte
that follows the closing quote instead of copying the remainder.  `fuel` bounds
the steps, one per character, so the recursion is structural and a scan over
concrete bytes reduces; the caller supplies the subject's length, which is as
many steps as a scan of it can take. -/
private def scanCharsAt (bs : Bytes) (fuel i off : Nat) :
    Except ScanError (List Nat × Nat) :=
  match fuel with
  | 0 => .error .ended
  | fuel + 1 =>
    match bs[i]? with
    | none => .error .ended
    | some 0x22 => .ok ([], i + 1)
    | some 0x5C =>
      match bs[i + 1]? with
      | none => .error .ended
      | some e =>
        match EscVal e with
        | some c => okConsIx off c (scanCharsAt bs fuel (i + 2) (off + 2))
        | none =>
          if e = 0x75 then
            match bs[i + 2]? with
            | none => .error .ended
            | some h0 =>
              match bs[i + 3]? with
              | none => .error .ended
              | some h1 =>
                match bs[i + 4]? with
                | none => .error .ended
                | some h2 =>
                  match bs[i + 5]? with
                  | none => .error .ended
                  | some h3 =>
                    match Hex4 h0 h1 h2 h3 with
                    | none => .error (.badEscape (off + 2))
                    | some c =>
                      if 0xD800 ≤ c ∧ c ≤ 0xDBFF then
                        match bs[i + 6]? with
                        | none => .error (.unpairedSurrogate off)
                        | some z0 =>
                          match bs[i + 7]? with
                          | none => .error (.unpairedSurrogate off)
                          | some z1 =>
                            match bs[i + 8]? with
                            | none => .error (.unpairedSurrogate off)
                            | some l0 =>
                              match bs[i + 9]? with
                              | none => .error (.unpairedSurrogate off)
                              | some l1 =>
                                match bs[i + 10]? with
                                | none => .error (.unpairedSurrogate off)
                                | some l2 =>
                                  match bs[i + 11]? with
                                  | none => .error (.unpairedSurrogate off)
                                  | some l3 =>
                                    if z0 = 0x5C then
                                      if z1 = 0x75 then
                                        match Hex4 l0 l1 l2 l3 with
                                        | none => .error (.badEscape (off + 8))
                                        | some lo =>
                                          if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                                            okConsIx off (0x10000 + (c - 0xD800) * 0x400 +
                                                (lo - 0xDC00))
                                              (scanCharsAt bs fuel (i + 12) (off + 12))
                                          else .error (.unpairedSurrogate off)
                                      else .error (.unpairedSurrogate off)
                                    else .error (.unpairedSurrogate off)
                      else if 0xDC00 ≤ c ∧ c ≤ 0xDFFF then
                        .error (.unpairedSurrogate off)
                      else okConsIx off c (scanCharsAt bs fuel (i + 6) (off + 6))
          else .error (.badEscape off)
    | some b =>
      if b.toNat < 0x80 then
        if 0x20 ≤ b.toNat then
          okConsIx off b.toNat (scanCharsAt bs fuel (i + 1) (off + 1))
        else .error (.controlCharacter off)
      else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then
            okConsIx off ((b.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80))
              (scanCharsAt bs fuel (i + 2) (off + 2))
          else .error (.badUTF8 off)
      else if b = 0xE0 then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            if 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okConsIx off ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                (scanCharsAt bs fuel (i + 3) (off + 3))
            else .error (.badUTF8 off)
      else if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okConsIx off ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80))
                (scanCharsAt bs fuel (i + 3) (off + 3))
            else .error (.badUTF8 off)
      else if b = 0xED then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okConsIx off (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                (scanCharsAt bs fuel (i + 3) (off + 3))
            else .error (.badUTF8 off)
      else if 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              okConsIx off ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80))
                (scanCharsAt bs fuel (i + 3) (off + 3))
            else .error (.badUTF8 off)
      else if b = 0xF0 then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            match bs[i + 3]? with
            | none => .error .ended
            | some b3 =>
              if 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
                okConsIx off ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
                    (b3.toNat - 0x80))
                  (scanCharsAt bs fuel (i + 4) (off + 4))
              else .error (.badUTF8 off)
      else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            match bs[i + 3]? with
            | none => .error .ended
            | some b3 =>
              if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
                okConsIx off ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
                    (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                  (scanCharsAt bs fuel (i + 4) (off + 4))
              else .error (.badUTF8 off)
      else if b = 0xF4 then
        match bs[i + 1]? with
        | none => .error .ended
        | some b1 =>
          match bs[i + 2]? with
          | none => .error .ended
          | some b2 =>
            match bs[i + 3]? with
            | none => .error .ended
            | some b3 =>
              if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
                okConsIx off (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
                    (b3.toNat - 0x80))
                  (scanCharsAt bs fuel (i + 4) (off + 4))
              else .error (.badUTF8 off)
      else .error (.badUTF8 off)

/-- The string scanner at the start of a body: the index scan at the first byte,
with the body's length as its fuel, and the remainder taken as the one extract
past the closing quote. -/
def scanChars (bs : Bytes) : Except ScanError (List Nat × Bytes) :=
  (scanCharsAt bs bs.size 0 0).map (fun p => (p.1, tailFrom bs p.2))

/-- The string body scan from index `i` of the buffer, returning the code points
and the index just past the closing quote: the form the parser and the tape
decoder use, which reads the buffer at the position it was given and copies no
suffix and no remainder.

The stop is typed as a position in the buffer.  `min` supplies that position by
construction: the scan advances only past bytes it has looked up, but that is an
observation about its branches rather than a theorem here, so the bound is not
proved from them and the pin is what makes the type hold.  The fact the callers
read is that the pinned stop names the same suffix as the index it pins
(`drop_min`), and `scanCharsEnd_sound` states the agreement with the reference
scan through it. -/
def scanCharsEnd (bs : Bytes) (i off : Nat) :
    Except ScanError (List Nat × { stop : Nat // stop ≤ bs.size }) :=
  match scanCharsAt bs (bs.size - i) i off with
  | .error e => .error e
  | .ok (cs, stop) => .ok (cs, ⟨min stop bs.size, Nat.min_le_right _ _⟩)

/-- `*DIGIT` consumes the whole argument, over the carrier's list view. -/
private def allDigitsL : List UInt8 → Bool
  | [] => true
  | b :: rest => IsDigitB b && allDigitsL rest

/-- `*DIGIT` consumes the whole argument. -/
def allDigitsB (bs : Bytes) : Bool := allDigitsL bs.data.toList

/-- `1*DIGIT` consumes the whole argument, over the carrier's list view. -/
private def digits1L : List UInt8 → Bool
  | [] => false
  | b :: rest => IsDigitB b && allDigitsL rest

/-- `1*DIGIT` consumes the whole argument. -/
def digits1B (bs : Bytes) : Bool := digits1L bs.data.toList

/-- The bytes after an `e`: `[ minus / plus ] 1*DIGIT`, exhausted. -/
private def expBL : List UInt8 → Bool
  | [] => false
  | b :: rest => if b = 0x2B ∨ b = 0x2D then digits1L rest else digits1L (b :: rest)

def expB (bs : Bytes) : Bool := expBL bs.data.toList

/-- The bytes after a fraction's digits: an optional exponent, exhausted. -/
private def expTailL : List UInt8 → Bool
  | [] => true
  | b :: rest =>
      if decide (b = 0x65) || decide (b = 0x45) then expBL rest else false

def expTailB (bs : Bytes) : Bool := expTailL bs.data.toList

/-- The bytes after an `int`: an optional fraction, an optional exponent,
exhausted. -/
private def numSuffixL : List UInt8 → Bool
  | [] => true
  | b :: rest =>
      if decide (b = 0x2E) then
        digits1L (List.takeWhile IsDigitB rest) && expTailL (List.dropWhile IsDigitB rest)
      else if decide (b = 0x65) || decide (b = 0x45) then expBL rest
      else false

def numSuffixB (bs : Bytes) : Bool := numSuffixL bs.data.toList

/-- `int [ frac ] [ exp ]`, exhausted. -/
private def numBodyL : List UInt8 → Bool
  | [] => false
  | b :: rest =>
      if decide (b = 0x30) then numSuffixL rest
      else if 0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39 then
        numSuffixL (List.dropWhile IsDigitB rest)
      else false

/-- `[ minus ] int [ frac ] [ exp ]`, exhausted. -/
private def numLexL : List UInt8 → Bool
  | [] => numBodyL []
  | b :: rest => if decide (b = 0x2D) then numBodyL rest else numBodyL (b :: rest)

def numLexB (lex : Bytes) : Bool := numLexL lex.data.toList
where
  numBodyB (bs : Bytes) : Bool := numBodyL bs.data.toList

/-! #### The scanners' equations

One equation per shape.  The carrier's functions apply a list-shaped scan to
`bs.data.toList`, so each equation is the scan's own recursion step: these are
`rfl`, and they are the form the proofs rewrite with. -/

theorem allDigitsB_empty : allDigitsB (empty : Bytes) = true := rfl

theorem allDigitsB_cons (b : UInt8) (bs : Bytes) :
    allDigitsB (b +: bs) = (IsDigitB b && allDigitsB bs) := rfl

theorem digits1B_empty : digits1B (empty : Bytes) = false := rfl

theorem digits1B_cons (b : UInt8) (bs : Bytes) :
    digits1B (b +: bs) = (IsDigitB b && allDigitsB bs) := rfl

theorem expB_empty : expB (empty : Bytes) = false := rfl

theorem expB_cons (b : UInt8) (bs : Bytes) :
    expB (b +: bs) = if b = 0x2B ∨ b = 0x2D then digits1B bs else digits1B (b +: bs) := rfl

theorem expTailB_empty : expTailB (empty : Bytes) = true := rfl

theorem expTailB_cons (b : UInt8) (bs : Bytes) :
    expTailB (b +: bs) =
      if decide (b = 0x65) || decide (b = 0x45) then expB bs else false := rfl

theorem numSuffixB_empty : numSuffixB (empty : Bytes) = true := rfl

theorem numSuffixB_cons (b : UInt8) (bs : Bytes) :
    numSuffixB (b +: bs) =
      (if decide (b = 0x2E) then
        digits1B (takeWhile bs IsDigitB) && expTailB (dropWhile bs IsDigitB)
      else if decide (b = 0x65) || decide (b = 0x45) then expB bs
      else false) := rfl

theorem numLexB_empty : numLexB (empty : Bytes) = numLexB.numBodyB empty := rfl

theorem numLexB_cons (b : UInt8) (bs : Bytes) :
    numLexB (b +: bs) =
      if decide (b = 0x2D) then numLexB.numBodyB bs else numLexB.numBodyB (b +: bs) := rfl

theorem numLexB.numBodyB_empty : numLexB.numBodyB (empty : Bytes) = false := rfl

theorem numLexB.numBodyB_cons (b : UInt8) (bs : Bytes) :
    numLexB.numBodyB (b +: bs) =
      if decide (b = 0x30) then numSuffixB bs
      else if 0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39 then numSuffixB (dropWhile bs IsDigitB)
      else false := rfl

theorem digits_all : ∀ {bs : Bytes}, Digits bs → ∀ b ∈ bs, IsDigitB b = true
  | _, .one h, b, hb => by
      rw [ByteString.mem_singleton] at hb; subst hb; exact h
  | _, .more h _, b, hb => by
      rw [ByteString.mem_cons] at hb
      rcases hb with rfl | hb
      · exact h
      · exact digits_all ‹_› b hb

theorem digits0_all : ∀ {bs : Bytes}, Digits0 bs → ∀ b ∈ bs, IsDigitB b = true
  | _, .nil, b, hb => by simp [ByteString.mem_def] at hb
  | _, .more h hr, b, hb => by
      rw [ByteString.mem_cons] at hb
      rcases hb with rfl | hb
      · exact h
      · exact digits0_all hr b hb

theorem digits0_to_digits_or_empty : ∀ {bs : Bytes}, Digits0 bs → Digits bs ∨ bs = empty
  | _, .nil => Or.inr rfl
  | _, .more hb hr => by
      cases digits0_to_digits_or_empty hr with
      | inl h => exact Or.inl (.more hb h)
      | inr he => subst he; exact Or.inl (.one hb)

theorem digits0_to_digits : ∀ {bs : Bytes}, Digits0 bs → bs ≠ empty → Digits bs
  | bs, h, hne => by
      cases digits0_to_digits_or_empty h with
      | inl hd => exact hd
      | inr he => exact absurd he hne

theorem allDigitsB_spec : ∀ {bs : Bytes}, allDigitsB bs = true → Digits0 bs := by
  intro bs
  have key : ∀ (l : List UInt8), allDigitsB (ByteString.literal l) = true →
      Digits0 (ByteString.literal l) := by
    intro l
    induction l with
    | nil => intro _; exact .nil
    | cons b rest ih =>
        intro h
        rw [ByteString.literal_cons, allDigitsB_cons, Bool.and_eq_true] at h
        exact .more h.1 (ih h.2)
  rw [← ByteString.literal_data_toList bs]
  exact key bs.data.toList

theorem digits1B_spec : ∀ {bs : Bytes}, digits1B bs = true → Digits bs := by
  intro bs h
  match hb : bs.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList hb, digits1B_empty] at h
      exact absurd h (by simp)
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [digits1B_cons, Bool.and_eq_true] at h
      match hr : rest with
      | [] => exact .one h.1
      | c :: cs =>
          rw [ByteString.literal_cons]
          exact .more h.1 (digits0_to_digits (allDigitsB_spec h.2)
            (ByteString.cons_ne_empty c _))

theorem allDigitsB_complete : ∀ {bs : Bytes}, Digits0 bs → allDigitsB bs = true
  | _, .nil => allDigitsB_empty
  | _, .more h hr => by
      rw [allDigitsB_cons, h, allDigitsB_complete hr, Bool.true_and]

theorem digits1B_complete : ∀ {bs : Bytes}, Digits bs → digits1B bs = true
  | _, .one h => by
      rw [digits1B_cons, h, Bool.true_and, allDigitsB_empty]
  | _, .more h hr => by
      rw [digits1B_cons, h, Bool.true_and]
      exact allDigitsB_complete (digits0_to_digits0_of_digits hr)
where
  digits0_to_digits0_of_digits : ∀ {bs : Bytes}, Digits bs → Digits0 bs
    | _, .one h => .more h .nil
    | _, .more h hr => .more h (digits0_to_digits0_of_digits hr)

theorem digits0_takeWhile (bs : Bytes) : Digits0 (bs.takeWhile IsDigitB) := by
  refine ByteString.induction_on (C := fun b => Digits0 (b.takeWhile IsDigitB)) bs ?_ ?_
  · rw [ByteString.takeWhile_empty]
    exact .nil
  · intro b rest ih
    rw [ByteString.takeWhile_cons]
    split
    · rename_i hb
      exact .more hb ih
    · exact .nil

theorem dropWhile_digits : ∀ {bs : Bytes}, Digits0 bs → bs.dropWhile IsDigitB = empty
  | _, .nil => ByteString.dropWhile_empty IsDigitB
  | _, .more h hr => by
      rw [ByteString.dropWhile_cons]
      simp [h, dropWhile_digits hr]

theorem takeWhile_digits : ∀ {bs : Bytes}, Digits0 bs → bs.takeWhile IsDigitB = bs
  | _, .nil => ByteString.takeWhile_empty IsDigitB
  | _, .more h hr => by
      rw [ByteString.takeWhile_cons, if_pos h, takeWhile_digits hr]

theorem eq_takeWhile_of_dropWhile_eq_nil {bs : Bytes} (h : bs.dropWhile IsDigitB = empty) :
    bs = bs.takeWhile IsDigitB := by
  have hsplit := ByteString.takeWhile_append_dropWhile bs IsDigitB
  rw [h, ByteString.append_empty] at hsplit
  exact hsplit.symm

theorem expB_spec {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {bs : Bytes}
    (h : expB bs = true) : ExpPart (e +: bs) := by
  match hb : bs.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList hb, expB_empty] at h
      exact absurd h (by simp)
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [expB_cons] at h
      by_cases hs : b = 0x2B ∨ b = 0x2D
      · rw [if_pos hs] at h
        have hd := digits1B_spec h
        rcases hs with rfl | rfl
        · have hE : ExpPart (e +: ((0x2B +: empty) ++ ByteString.literal rest)) :=
            ExpPart.mk (e := e) (sign := 0x2B +: empty) (ds := ByteString.literal rest) he
              (Or.inr (Or.inl rfl)) hd
          rwa [ByteString.cons_append, ByteString.empty_append] at hE
        · have hE : ExpPart (e +: ((0x2D +: empty) ++ ByteString.literal rest)) :=
            ExpPart.mk (e := e) (sign := 0x2D +: empty) (ds := ByteString.literal rest) he
              (Or.inr (Or.inr rfl)) hd
          rwa [ByteString.cons_append, ByteString.empty_append] at hE
      · rw [if_neg hs] at h
        have hd := digits1B_spec h
        have hE : ExpPart (e +: (empty ++ (b +: ByteString.literal rest))) :=
          ExpPart.mk (e := e) (sign := empty) (ds := b +: ByteString.literal rest) he
            (Or.inl rfl) hd
        rwa [ByteString.empty_append] at hE

theorem expTailB_spec {bs : Bytes} (h : expTailB bs = true) :
    bs = empty ∨ ExpPart bs := by
  match hb : bs.data.toList with
  | [] =>
      left
      exact ByteString.eq_empty_of_data_toList hb
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [expTailB_cons] at h
      split at h
      · rename_i hcond
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with rfl | rfl
        · exact Or.inr (expB_spec (Or.inl rfl) h)
        · exact Or.inr (expB_spec (Or.inr rfl) h)
      · exact absurd h (by simp)

theorem numSuffixB_spec {ip : Bytes} (hi : IntPart ip) :
    ∀ {suf : Bytes}, numSuffixB suf = true → NumBody (ip ++ suf) := by
  intro suf h
  match hb : suf.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList hb] at h ⊢
      simpa [ByteString.append_empty] using NumBody.plain hi
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [numSuffixB_cons] at h
      split at h
      · rename_i hdot
        simp only [decide_eq_true_eq] at hdot
        subst hdot
        simp only [Bool.and_eq_true] at h
        have hf : Digits (ByteString.literal rest |>.takeWhile IsDigitB) := digits1B_spec h.1
        have hsplit : (ByteString.literal rest).takeWhile IsDigitB ++
            (ByteString.literal rest).dropWhile IsDigitB = ByteString.literal rest :=
          ByteString.takeWhile_append_dropWhile _ IsDigitB
        rcases expTailB_spec h.2 with he | he
        · have hrest : ByteString.literal rest =
              (ByteString.literal rest).takeWhile IsDigitB :=
            eq_takeWhile_of_dropWhile_eq_nil he
          have hb2 : NumBody (ip ++ (0x2E +: (ByteString.literal rest).takeWhile IsDigitB)) :=
            NumBody.frac hi hf
          rw [← hrest] at hb2
          simpa using hb2
        · have hb2 : NumBody (ip ++ (0x2E +: ((ByteString.literal rest).takeWhile IsDigitB ++
              (ByteString.literal rest).dropWhile IsDigitB))) := by
            have hfrac := NumBody.fracExp (ip := ip)
              (fs := (ByteString.literal rest).takeWhile IsDigitB)
              (es := (ByteString.literal rest).dropWhile IsDigitB) hi hf he
            rw [ByteString.append_assoc] at hfrac
            rwa [ByteString.cons_append] at hfrac
          rw [hsplit] at hb2
          simpa using hb2
      · split at h
        · rename_i hexp
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hexp
          rcases hexp with rfl | rfl
          · exact NumBody.exp hi (expB_spec (Or.inl rfl) h)
          · exact NumBody.exp hi (expB_spec (Or.inr rfl) h)
        · exact absurd h (by simp)

theorem numBodyB_spec : ∀ {bs : Bytes}, numLexB.numBodyB bs = true → NumBody bs := by
  intro bs h
  match hb : bs.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList hb, numLexB.numBodyB_empty] at h
      exact absurd h (by simp)
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [numLexB.numBodyB_cons] at h
      split at h
      · rename_i hzero
        simp only [decide_eq_true_eq] at hzero
        subst hzero
        have hb2 := numSuffixB_spec (ip := 0x30 +: empty) (IntPart.zero) h
        rwa [ByteString.cons_append, ByteString.empty_append] at hb2
      · split at h
        · rename_i hd
          have htake : Digits0 ((ByteString.literal rest).takeWhile IsDigitB) :=
            digits0_takeWhile _
          have hsplit : (ByteString.literal rest).takeWhile IsDigitB ++
              (ByteString.literal rest).dropWhile IsDigitB = ByteString.literal rest :=
            ByteString.takeWhile_append_dropWhile _ IsDigitB
          have hip : IntPart (b +: (ByteString.literal rest).takeWhile IsDigitB) :=
            IntPart.lead hd.1 hd.2 htake
          have hbody := numSuffixB_spec hip h
          rwa [ByteString.cons_append, hsplit] at hbody
        · exact absurd h (by simp)


theorem digits0_of_digits : ∀ {bs : Bytes}, Digits bs → Digits0 bs
  | _, .one h => .more h .nil
  | _, .more h hr => .more h (digits0_of_digits hr)

theorem expB_digits {ds : Bytes} (hd : Digits ds) : expB ds = true := by
  match h : ds.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList h] at hd
      cases hd
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList h] at hd ⊢
      have hb : IsDigitB b = true := digits_all hd b (ByteString.mem_cons_self b _)
      have hnot : ¬ (b = 0x2B ∨ b = 0x2D) := by
        intro hc
        rcases hc with rfl | rfl <;> simp [IsDigitB] at hb
      rw [expB_cons, if_neg hnot]
      exact digits1B_complete hd

theorem expB_complete {sign ds : Bytes}
    (hs : sign = empty ∨ sign = (0x2B +: empty) ∨ sign = (0x2D +: empty))
    (hd : Digits ds) : expB (sign ++ ds) = true := by
  rcases hs with h | h | h
  · subst h
    rw [ByteString.empty_append]
    exact expB_digits hd
  · subst h
    rw [ByteString.cons_append, ByteString.empty_append, expB_cons, if_pos (Or.inl rfl)]
    exact digits1B_complete hd
  · subst h
    rw [ByteString.cons_append, ByteString.empty_append, expB_cons, if_pos (Or.inr rfl)]
    exact digits1B_complete hd

theorem digits_takeWhile_empty {e : UInt8} (he : e = 0x65 ∨ e = 0x45) (rest : Bytes) :
    (e +: rest).takeWhile IsDigitB = empty := by
  rw [ByteString.takeWhile_cons]
  have h : IsDigitB e = false := by rcases he with rfl | rfl <;> rfl
  simp [h]

theorem digits_dropWhile_self {e : UInt8} (he : e = 0x65 ∨ e = 0x45) (rest : Bytes) :
    (e +: rest).dropWhile IsDigitB = e +: rest := by
  rw [ByteString.dropWhile_cons]
  have h : IsDigitB e = false := by rcases he with rfl | rfl <;> rfl
  simp [h]

theorem expPart_takeWhile_nil {es : Bytes} (h : ExpPart es) :
    es.takeWhile IsDigitB = empty := by
  cases h with
  | mk he hs hd => exact digits_takeWhile_empty he _

theorem expPart_dropWhile_self {es : Bytes} (h : ExpPart es) :
    es.dropWhile IsDigitB = es := by
  cases h with
  | mk he hs hd => exact digits_dropWhile_self he _

theorem numSuffixB_frac {fs : Bytes} (hf : Digits fs) :
    numSuffixB (0x2E +: fs) = true := by
  have h0 : Digits0 fs := digits0_of_digits hf
  have ht : fs.takeWhile IsDigitB = fs := takeWhile_digits h0
  have hd : fs.dropWhile IsDigitB = empty := dropWhile_digits h0
  show numSuffixB (0x2E +: fs) = true
  simp [numSuffixB_cons, expTailB_empty, ht, hd, digits1B_complete hf]

theorem numSuffixB_exp {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {sign ds : Bytes}
    (hs : sign = empty ∨ sign = (0x2B +: empty) ∨ sign = (0x2D +: empty))
    (hd : Digits ds) : numSuffixB (e +: sign ++ ds) = true := by
  have hne : decide (e = 0x2E) = false := by
    rcases he with rfl | rfl <;> rfl
  have hyes : (decide (e = 0x65) || decide (e = 0x45)) = true := by
    rcases he with rfl | rfl <;> rfl
  show numSuffixB (e +: (sign ++ ds)) = true
  simp [numSuffixB_cons, hne, hyes, expB_complete hs hd]

theorem expTailB_exp {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {sign ds : Bytes}
    (hs : sign = empty ∨ sign = (0x2B +: empty) ∨ sign = (0x2D +: empty))
    (hd : Digits ds) : expTailB (e +: sign ++ ds) = true := by
  have hyes : (decide (e = 0x65) || decide (e = 0x45)) = true := by
    rcases he with rfl | rfl <;> rfl
  show expTailB (e +: (sign ++ ds)) = true
  simp [expTailB_cons, hyes, expB_complete hs hd]

theorem expPart_expTailB {es : Bytes} (h : ExpPart es) : expTailB es = true := by
  cases h with
  | mk he hs hd => exact expTailB_exp he hs hd

theorem expPart_numSuffixB {es : Bytes} (h : ExpPart es) : numSuffixB es = true := by
  cases h with
  | mk he hs hd => exact numSuffixB_exp he hs hd

theorem numSuffixB_fracExp {fs es : Bytes} (hf : Digits fs) (he : ExpPart es) :
    numSuffixB (0x2E +: fs ++ es) = true := by
  have h0 : Digits0 fs := digits0_of_digits hf
  have hall : ∀ a ∈ fs, IsDigitB a = true := digits0_all h0
  have htake : (fs ++ es).takeWhile IsDigitB = fs := by
    rw [ByteString.takeWhile_append_of_pos hall, expPart_takeWhile_nil he,
      ByteString.append_empty]
  have hdrop : (fs ++ es).dropWhile IsDigitB = es := by
    rw [ByteString.dropWhile_append_of_pos hall]
    exact expPart_dropWhile_self he
  have hd1 : digits1B fs = true := digits1B_complete hf
  have hexp : expTailB es = true := expPart_expTailB he
  show numSuffixB (0x2E +: (fs ++ es)) = true
  simp [numSuffixB_cons, htake, hdrop, hd1, hexp]

theorem numSuffixB_nodigit {suf : Bytes} (h : numSuffixB suf = true) :
    suf = empty ∨ ∀ (b : UInt8) (rest : Bytes), suf = b +: rest → IsDigitB b = false := by
  match hb : suf.data.toList with
  | [] =>
      left
      exact ByteString.eq_empty_of_data_toList hb
  | b :: rest =>
      right
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [numSuffixB_cons] at h
      split at h
      · rename_i hdot
        have hb2 : b = 0x2E := by simpa using hdot
        subst hb2
        intro b' rest' he
        rw [ByteString.cons_inj] at he
        obtain ⟨h1, _⟩ := he
        subst h1
        rfl

      · split at h
        · rename_i hexp
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hexp
          intro b' rest' he
          rw [ByteString.cons_inj] at he
          obtain ⟨h1, _⟩ := he
          subst h1
          rcases hexp with rfl | rfl <;> rfl
        · exact absurd h (by simp)

theorem digits_dropWhile_notdigit {rest suf : Bytes} (hr : Digits0 rest)
    (hs : suf = empty ∨ ∀ (b : UInt8) (rest' : Bytes), suf = b +: rest' → IsDigitB b = false) :
    (rest ++ suf).dropWhile IsDigitB = suf := by
  rw [ByteString.dropWhile_append_of_pos (digits0_all hr)]
  rcases hs with rfl | hs
  · rw [ByteString.dropWhile_empty]
  · match hb : suf.data.toList with
    | [] => rw [ByteString.eq_empty_of_data_toList hb, ByteString.dropWhile_empty]
    | b :: rest' =>
        rw [ByteString.eq_cons_of_data_toList hb, ByteString.dropWhile_cons]
        have hb' : IsDigitB b = false :=
          hs b (ByteString.literal rest') (ByteString.eq_cons_of_data_toList hb)
        simp [hb']

theorem numBodyB_int {ip suf : Bytes} (hi : IntPart ip) (hsuf : numSuffixB suf = true) :
    numLexB.numBodyB (ip ++ suf) = true := by
  cases hi with
  | zero =>
      rw [show (0x30 +: empty) ++ suf = 0x30 +: suf by
        rw [ByteString.cons_append, ByteString.empty_append]]
      rw [numLexB.numBodyB_cons]
      simp [hsuf]
  | @lead b bs h1 h2 hr =>
      have hne : ¬ (b = 0x30) := by
        intro hc
        rw [hc] at h1
        exact absurd h1 (by decide)
      have hdigit : (0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39) :=
        ⟨UInt8.le_iff_toNat_le.mp h1, UInt8.le_iff_toNat_le.mp h2⟩
      rw [ByteString.cons_append]
      rw [numLexB.numBodyB_cons, if_neg (by simp [hne]), if_pos hdigit]
      rw [digits_dropWhile_notdigit hr (numSuffixB_nodigit hsuf)]
      exact hsuf

theorem numBodyB_complete {bs : Bytes} (h : NumBody bs) : numLexB.numBodyB bs = true := by
  cases h with
  | plain hi => simpa [ByteString.append_empty] using numBodyB_int (suf := empty) hi numSuffixB_empty
  | @frac ip fs hi hf =>
      exact numBodyB_int (suf := 0x2E +: fs) hi (numSuffixB_frac (fs := fs) hf)
  | @exp ip es hi he =>
      exact numBodyB_int (suf := es) hi (expPart_numSuffixB he)
  | @fracExp ip fs es hi hf he =>
      have hb := numBodyB_int (suf := (0x2E +: fs) ++ es) hi
        (numSuffixB_fracExp (fs := fs) (es := es) hf he)
      rw [ByteString.append_assoc]
      exact hb

theorem numLexB_spec {lex : Bytes} (h : numLexB lex = true) : RfcNumber lex := by
  match hb : lex.data.toList with
  | [] =>
      rw [ByteString.eq_empty_of_data_toList hb, numLexB_empty,
        numLexB.numBodyB_empty] at h
      exact absurd h (by simp)
  | b :: rest =>
      rw [ByteString.eq_cons_of_data_toList hb] at h ⊢
      rw [numLexB_cons] at h
      split at h
      · rename_i hminus
        have hb2 : b = 0x2D := by simpa using hminus
        subst hb2
        exact RfcNumber.neg (numBodyB_spec h)
      · exact RfcNumber.pos (numBodyB_spec h)

theorem numLexB_complete {lex : Bytes} (h : RfcNumber lex) : numLexB lex = true := by
  cases h with
  | pos hb =>
      match hl : lex.data.toList with
      | [] =>
          rw [ByteString.eq_empty_of_data_toList hl] at hb
          have htrue := numBodyB_complete hb
          rw [numLexB.numBodyB_empty] at htrue
          exact absurd htrue (by simp)
      | b :: rest =>
          rw [ByteString.eq_cons_of_data_toList hl] at hb ⊢
          rw [numLexB_cons]
          have hnot : decide (b = 0x2D) = false := by
            by_cases hb2d : b = 0x2D
            · exfalso
              subst hb2d
              have htrue := numBodyB_complete hb
              rw [numLexB.numBodyB_cons] at htrue
              simp at htrue
            · simp [hb2d]
          rw [if_neg (by simp [hnot])]
          exact numBodyB_complete hb
  | neg hb =>
      rw [numLexB_cons, if_pos (by decide)]
      exact numBodyB_complete hb


theorem numLexB_iff (lex : Bytes) : numLexB lex = true ↔ RfcNumber lex :=
  ⟨numLexB_spec, numLexB_complete⟩

/-! ### Reflection lemmas

The scanners' specifications.  `scanChars_iff` is stated on the success side,
which is the side the theorems consume; the failure side adds nothing to what the
theorems know, because it is the complement. -/

/-! #### The scanner's equations

One equation per accepting branch: `scanCharsFrom` reduced by
`scanCharsFrom.eq_def` under that branch's side conditions.  The branches are
stated in the relation's own terms (`UInt8` bounds and the `Utf8Char` value
formulas), so completeness can apply them to a `StrChars` derivation's
`StrChar` directly. -/

theorem le_toNat {a b : UInt8} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  UInt8.le_iff_toNat_le.mp h

theorem scanCharsFrom_nil (off : Nat) : scanCharsFrom off (empty : Bytes) = .error .ended := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_empty]

theorem scanCharsFrom_quote (off : Nat) (rest : Bytes) :
    scanCharsFrom off (0x22 +: rest) = .ok ([], rest) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, ByteString.literal_data_toList]

theorem scanCharsFrom_ascii (off : Nat) (b : UInt8) (rest : Bytes)
    (hq : b ≠ 0x22) (hs : b ≠ 0x5C) (h1 : b < 0x80) (h2 : 0x20 ≤ b.toNat) :
    scanCharsFrom off (b +: rest) = scanCons off (off + 1) b.toNat rest := by
  have h1' : b.toNat < 0x80 := UInt8.lt_iff_toNat_lt.mp h1
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hq, hs, h1', h2]

theorem scanCharsFrom_escape (off : Nat) (e : UInt8) (rest1 : Bytes) (c : Nat)
    (hv : EscVal e = some c) :
    scanCharsFrom off (0x5C +: e +: rest1) = scanCons off (off + 2) c rest1 := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hv]

theorem scanCharsFrom_uchar (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (c : Nat)
    (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some c)
    (hhi : ¬ (0xD800 ≤ c ∧ c ≤ 0xDBFF))
    (hlo : ¬ (0xDC00 ≤ c ∧ c ≤ 0xDFFF)) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) =
      scanCons off (off + 6) c rest2 := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hv, hx, hhi, hlo]

theorem scanCharsFrom_pair (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8)
    (rest3 : Bytes) (hi lo : Nat)
    (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some hi) (hy : Hex4 l0 l1 l2 l3 = some lo)
    (hh : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hl : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF) :
    scanCharsFrom off
        (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
          l0 +: l1 +: l2 +: l3 +: rest3) =
      scanCons off (off + 12) (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) rest3 := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hv, hx, hy, hh, hl]

theorem scanCharsFrom_utf8_two (off : Nat) (b0 b1 : UInt8) (rest1 : Bytes)
    (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF) (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) :
    scanCharsFrom off (b0 +: b1 +: rest1) =
      scanCons off (off + 2) ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest1 := by
  have h0n : (0xC2 : Nat) ≤ b0.toNat := by simpa using le_toNat h0
  have h0n' : b0.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have hq : b0 ≠ 0x22 := by intro h; subst h; simp at h0n
  have hs : b0 ≠ 0x5C := by intro h; subst h; simp at h0n
  have hlt : ¬ b0.toNat < 0x80 := by omega
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hlt, h0n, h0n', h1n, h1n']

theorem scanCharsFrom_utf8_e0 (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0xA0 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (0xE0 +: b1 +: b2 +: rest1) =
      scanCons off (off + 3) ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := by
  have h1n : (0xA0 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_e1ec (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (b +: b1 +: b2 +: rest1) =
      scanCons off (off + 3)
        ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest1 := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hlt, htwo, he0, hbn, hbn', h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_ed (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x9F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (0xED +: b1 +: b2 +: rest1) =
      scanCons off (off + 3)
        (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x9F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_eeef (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (b +: b1 +: b2 +: rest1) =
      scanCons off (off + 3)
        ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest1 := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hlt, htwo, he0, h31, hed, hbn, hbn', h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_f0 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x90 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (0xF0 +: b1 +: b2 +: b3 +: rest1) =
      scanCons off (off + 4)
        ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest1 := by
  have h1n : (0x90 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, h1n, h1n', h2n, h2n', h3n, h3n']

theorem scanCharsFrom_utf8_f1f3 (off : Nat) (b b1 b2 b3 : UInt8) (rest1 : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (b +: b1 +: b2 +: b3 +: rest1) =
      scanCons off (off + 4)
        ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  have h33 : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := by omega
  have hf0 : b ≠ 0xF0 := by intro h; subst h; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, hlt, htwo, he0, h31, hed, h33, hf0, hbn, hbn', h1n, h1n', h2n, h2n', h3n, h3n']

theorem scanCharsFrom_utf8_f4 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x8F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (0xF4 +: b1 +: b2 +: b3 +: rest1) =
      scanCons off (off + 4)
        (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest1 := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x8F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [scanCons, scanCharsFrom, ByteString.data_toList_cons, ByteString.literal_data_toList, h1n, h1n', h2n, h2n', h3n, h3n']

/-! ##### The scanner's refusals

The equations above state each accepting branch.  These state each refusing one:
the argument's shape, the side conditions that select the branch, and the reason
and offset the scan reports.  Each is the accepting equations' mirror — the
`\uXXXX` and surrogate branches refuse in several places, so they have several —
and together the two families fix the scan's value on every byte shape, refusal
included.  Where the refusal is `ended` the tail is bounded only by its length,
because the scanner finds out the subject ran out rather than which bytes would
have followed. -/

theorem scanCharsFrom_escape_ended (off : Nat) :
    scanCharsFrom off (0x5C +: empty) = .error .ended := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, ByteString.data_toList_empty]

theorem scanCharsFrom_escape_bad (off : Nat) (e : UInt8) (rest1 : Bytes)
    (hv : EscVal e = none) (he : e ≠ 0x75) :
    scanCharsFrom off (0x5C +: e +: rest1) = .error (.badEscape off) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, he]

theorem scanCharsFrom_uchar_ended (off : Nat) (l : Bytes) (hl : l.length < 4) :
    scanCharsFrom off (0x5C +: 0x75 +: l) = .error .ended := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  have hl' : l.data.toList.length < 4 := by
    rw [Array.length_toList]
    exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv]
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_uchar_badHex (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes)
    (hx : Hex4 h0 h1 h2 h3 = none) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) =
      .error (.badEscape (off + 2)) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx]

theorem scanCharsFrom_uchar_low (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (c : Nat)
    (hx : Hex4 h0 h1 h2 h3 = some c) (hlo : 0xDC00 ≤ c ∧ c ≤ 0xDFFF) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) =
      .error (.unpairedSurrogate off) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  have hhi : ¬ (0xD800 ≤ c ∧ c ≤ 0xDBFF) := by omega
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx, hhi, hlo]

theorem scanCharsFrom_pair_ended (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (hi : Nat)
    (hx : Hex4 h0 h1 h2 h3 = some hi) (hhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF)
    (hr : rest2.length < 6) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) =
      .error (.unpairedSurrogate off) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  have hr' : rest2.data.toList.length < 6 := by
    rw [Array.length_toList]
    exact hr
  rw [← ByteString.literal_data_toList rest2, scanCharsFrom]
  unfold scanCharsL
  rcases hr'' : rest2.data.toList with
    _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, r⟩⟩⟩⟩⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hv, hx, hhi]
  · exfalso
    rw [hr''] at hr'
    simp only [List.length_cons] at hr'
    omega

theorem scanCharsFrom_pair_noEscape (off : Nat) (h0 h1 h2 h3 : UInt8) (z0 : UInt8) (zs : Bytes)
    (hi : Nat) (hx : Hex4 h0 h1 h2 h3 = some hi) (hhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF)
    (hz : z0 ≠ 0x5C) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: z0 +: zs) =
      .error (.unpairedSurrogate off) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx, hhi, hz]

theorem scanCharsFrom_pair_noU (off : Nat) (h0 h1 h2 h3 : UInt8) (z1 : UInt8) (zs : Bytes)
    (hi : Nat) (hx : Hex4 h0 h1 h2 h3 = some hi) (hhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF)
    (hz : z1 ≠ 0x75) :
    scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: z1 +: zs) =
      .error (.unpairedSurrogate off) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx, hhi, hz]

theorem scanCharsFrom_pair_badHex (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8)
    (rest3 : Bytes) (hi : Nat) (hx : Hex4 h0 h1 h2 h3 = some hi)
    (hhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hy : Hex4 l0 l1 l2 l3 = none) :
    scanCharsFrom off
        (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
          l0 +: l1 +: l2 +: l3 +: rest3) =
      .error (.badEscape (off + 8)) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx, hhi, hy]

theorem scanCharsFrom_pair_badLow (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8)
    (rest3 : Bytes) (hi lo : Nat) (hx : Hex4 h0 h1 h2 h3 = some hi)
    (hhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hy : Hex4 l0 l1 l2 l3 = some lo)
    (hlo : ¬ (0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)) :
    scanCharsFrom off
        (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
          l0 +: l1 +: l2 +: l3 +: rest3) =
      .error (.unpairedSurrogate off) := by
  have hv : EscVal (0x75 : UInt8) = none := rfl
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hv, hx, hhi, hy, hlo]

theorem scanCharsFrom_control (off : Nat) (b : UInt8) (rest : Bytes)
    (h1 : b.toNat < 0x80) (h2 : ¬ 0x20 ≤ b.toNat) :
    scanCharsFrom off (b +: rest) = .error (.controlCharacter off) := by
  have hq : b ≠ 0x22 := by intro h; subst h; simp at h2
  have hs : b ≠ 0x5C := by intro h; subst h; simp at h2
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hq, hs, h1, h2]

theorem scanCharsFrom_utf8_two_ended (off : Nat) (b : UInt8) (h0 : 0xC2 ≤ b) (h0' : b ≤ 0xDF) :
    scanCharsFrom off (b +: empty) = .error .ended := by
  have h0n : (0xC2 : Nat) ≤ b.toNat := by simpa using le_toNat h0
  have h0n' : b.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at h0n
  have hs : b ≠ 0x5C := by intro h; subst h; simp at h0n
  have hlt : ¬ b.toNat < 0x80 := by omega
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, ByteString.data_toList_empty, hq, hs, hlt, h0n, h0n']

theorem scanCharsFrom_utf8_two_bad (off : Nat) (b0 b1 : UInt8) (rest1 : Bytes)
    (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF) (hb : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)) :
    scanCharsFrom off (b0 +: b1 +: rest1) = .error (.badUTF8 off) := by
  have h0n : (0xC2 : Nat) ≤ b0.toNat := by simpa using le_toNat h0
  have h0n' : b0.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have hq : b0 ≠ 0x22 := by intro h; subst h; simp at h0n
  have hs : b0 ≠ 0x5C := by intro h; subst h; simp at h0n
  have hlt : ¬ b0.toNat < 0x80 := by omega
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hq, hs, hlt, h0n, h0n', hb]

theorem scanCharsFrom_utf8_e0_ended (off : Nat) (l : Bytes) (hl : l.length < 2) :
    scanCharsFrom off (0xE0 +: l) = .error .ended := by
  have hl' : l.data.toList.length < 2 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, r⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_e1ec_ended (off : Nat) (b : UInt8) (l : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC) (hl : l.length < 2) :
    scanCharsFrom off (b +: l) = .error .ended := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have hl' : l.data.toList.length < 2 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, r⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      hbn, hbn']
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      hbn, hbn']
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_ed_ended (off : Nat) (l : Bytes) (hl : l.length < 2) :
    scanCharsFrom off (0xED +: l) = .error .ended := by
  have hl' : l.data.toList.length < 2 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, r⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_eeef_ended (off : Nat) (b : UInt8) (l : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF) (hl : l.length < 2) :
    scanCharsFrom off (b +: l) = .error .ended := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  have hl' : l.data.toList.length < 2 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, r⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      h31, hed, hbn, hbn']
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      h31, hed, hbn, hbn']
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_f0_ended (off : Nat) (l : Bytes) (hl : l.length < 3) :
    scanCharsFrom off (0xF0 +: l) = .error .ended := by
  have hl' : l.data.toList.length < 3 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, _ | ⟨b2, r⟩⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_f1f3_ended (off : Nat) (b : UInt8) (l : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3) (hl : l.length < 3) :
    scanCharsFrom off (b +: l) = .error .ended := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  have h33 : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := by omega
  have hf0 : b ≠ 0xF0 := by intro h; subst h; simp at hbn
  have hl' : l.data.toList.length < 3 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, _ | ⟨b2, r⟩⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      h31, hed, h33, hf0, hbn, hbn']
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      h31, hed, h33, hf0, hbn, hbn']
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal, hq, hs, hlt, htwo, he0,
      h31, hed, h33, hf0, hbn, hbn']
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_f4_ended (off : Nat) (l : Bytes) (hl : l.length < 3) :
    scanCharsFrom off (0xF4 +: l) = .error .ended := by
  have hl' : l.data.toList.length < 3 := by rw [Array.length_toList]; exact hl
  rw [← ByteString.literal_data_toList l, scanCharsFrom]
  unfold scanCharsL
  rcases hl'' : l.data.toList with _ | ⟨a, _ | ⟨b1, _ | ⟨b2, r⟩⟩⟩
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · simp [ByteString.data_toList_cons, ByteString.data_toList_literal]
  · exfalso
    rw [hl''] at hl'
    simp only [List.length_cons] at hl'
    omega

theorem scanCharsFrom_utf8_e0_bad (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h : ¬ (0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)) :
    scanCharsFrom off (0xE0 +: b1 +: b2 +: rest1) = .error (.badUTF8 off) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, h]

theorem scanCharsFrom_utf8_e1ec_bad (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC)
    (h : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)) :
    scanCharsFrom off (b +: b1 +: b2 +: rest1) = .error (.badUTF8 off) := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro hh; subst hh; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hq, hs, hlt, htwo, he0, hbn, hbn', h]

theorem scanCharsFrom_utf8_ed_bad (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)) :
    scanCharsFrom off (0xED +: b1 +: b2 +: rest1) = .error (.badUTF8 off) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, h]

theorem scanCharsFrom_utf8_eeef_bad (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF)
    (h : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)) :
    scanCharsFrom off (b +: b1 +: b2 +: rest1) = .error (.badUTF8 off) := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro hh; subst hh; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro hh; subst hh; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hq, hs, hlt, htwo, he0, h31, hed, hbn, hbn', h]

theorem scanCharsFrom_utf8_f0_bad (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h : ¬ (0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
      b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)) :
    scanCharsFrom off (0xF0 +: b1 +: b2 +: b3 +: rest1) = .error (.badUTF8 off) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, h]

theorem scanCharsFrom_utf8_f1f3_bad (off : Nat) (b b1 b2 b3 : UInt8) (rest1 : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3)
    (h : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
      b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)) :
    scanCharsFrom off (b +: b1 +: b2 +: b3 +: rest1) = .error (.badUTF8 off) := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro hh; subst hh; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro hh; subst hh; simp at hbn
  have h33 : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := by omega
  have hf0 : b ≠ 0xF0 := by intro hh; subst hh; simp at hbn
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, hq, hs, hlt, htwo, he0, h31, hed, h33, hf0, hbn, hbn', h]

theorem scanCharsFrom_utf8_f4_bad (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧ 0x80 ≤ b2.toNat ∧
      b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)) :
    scanCharsFrom off (0xF4 +: b1 +: b2 +: b3 +: rest1) = .error (.badUTF8 off) := by
  rw [scanCharsFrom]
  unfold scanCharsL
  simp [ByteString.data_toList_cons, h]

theorem scanCharsFrom_utf8_lead (off : Nat) (b : UInt8) (rest : Bytes)
    (hge : 0x80 ≤ b.toNat) (hbad : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xF4)) :
    scanCharsFrom off (b +: rest) = .error (.badUTF8 off) := by
  have hq : b ≠ 0x22 := by intro h; subst h; exact absurd hge (by decide)
  have hs : b ≠ 0x5C := by intro h; subst h; exact absurd hge (by decide)
  have hlt : ¬ b.toNat < 0x80 := Nat.not_lt.mpr hge
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by
    rintro ⟨h1, h2⟩
    exact hbad ⟨h1, Nat.le_trans h2 (by decide)⟩
  have he0 : b ≠ 0xE0 := by intro h; subst h; exact hbad ⟨by decide, by decide⟩
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by
    rintro ⟨h1, h2⟩
    exact hbad ⟨Nat.le_trans (by decide) h1, Nat.le_trans h2 (by decide)⟩
  have hed : b ≠ 0xED := by intro h; subst h; exact hbad ⟨by decide, by decide⟩
  have h33 : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := by
    rintro ⟨h1, h2⟩
    exact hbad ⟨Nat.le_trans (by decide) h1, Nat.le_trans h2 (by decide)⟩
  have hf0 : b ≠ 0xF0 := by intro h; subst h; exact hbad ⟨by decide, by decide⟩
  have h41 : ¬ (0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3) := by
    rintro ⟨h1, h2⟩
    exact hbad ⟨Nat.le_trans (by decide) h1, Nat.le_trans h2 (by decide)⟩
  have hf4 : b ≠ 0xF4 := by intro h; subst h; exact hbad ⟨by decide, by decide⟩
  rw [scanCharsFrom]
  cases hl : rest.data.toList with
  | nil =>
    have hemp : rest = empty := by
      apply ByteString.eq_of_data_toList_eq
      rw [hl, ByteString.data_toList_empty]
    subst hemp
    rw [ByteString.data_toList_cons, ByteString.data_toList_empty, scanCharsL.eq_7 off b hq hs]
    simp only [ite_true, ite_false, hlt, htwo, he0, h31, hed, h33, hf0, h41, hf4, and_self,
      and_true, true_and]
  | cons b1 rest1 =>
    rw [ByteString.data_toList_cons, hl, scanCharsL.eq_6 off b b1 rest1 hq hs]
    simp only [ite_true, ite_false, hlt, htwo, he0, h31, hed, h33, hf0, h41, hf4, and_self,
      and_true, true_and]

/-! #### Character and byte facts

The strict character policy on the relation's side, and the arithmetic the branch
conditions imply for the bytes they constrain. -/

theorem strict_noncharacter {n : Nat} (h : ModeAllows .strict n) :
    IsNoncharacter n = false := by
  simp only [ModeAllows, CharAllowed] at h
  exact h.2

theorem charAllowed_of {n : Nat} (hs : IsScalar n) (hn : IsNoncharacter n = false) :
    ModeAllows .strict n :=
  ⟨hs, hn⟩

theorem high_ne_of_scalar {n : Nat} (h : IsScalar n) : ¬ (0xD800 ≤ n ∧ n ≤ 0xDBFF) := by
  obtain ⟨_, h'⟩ := h
  rintro ⟨a, b⟩
  exact h' ⟨a, by omega⟩

theorem low_ne_of_scalar {n : Nat} (h : IsScalar n) : ¬ (0xDC00 ≤ n ∧ n ≤ 0xDFFF) := by
  obtain ⟨_, h'⟩ := h
  rintro ⟨a, b⟩
  exact h' ⟨by omega, b⟩

theorem escVal_noncharacter {e : UInt8} {c : Nat} (h : EscVal e = some c) :
    IsNoncharacter c = false := by
  unfold EscVal at h
  split at h <;> (first | (simp_all only [Option.some.injEq]; subst_vars; decide) | simp_all)

theorem byte_ne_quote {b : UInt8} (h : b.toNat ≠ 0x22) : b ≠ 0x22 := by
  intro hb
  exact h (congrArg UInt8.toNat hb)

theorem byte_ne_backslash {b : UInt8} (h : b.toNat ≠ 0x5C) : b ≠ 0x5C := by
  intro hb
  exact h (congrArg UInt8.toNat hb)

theorem hexVal_le {b : UInt8} {v : Nat} (h : HexVal b = some v) : v ≤ 15 := by
  unfold HexVal at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
      UInt8.toNat_ofNat] at hd
    omega
  · rename_i hd
    split at h
    · rename_i hu
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
        UInt8.toNat_ofNat] at hu
      omega
    · split at h
      · rename_i hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
          UInt8.toNat_ofNat] at hl
        omega
      · simp at h

theorem hex4_le {a b c d : UInt8} {n : Nat} (h : Hex4 a b c d = some n) : n ≤ 0xFFFF := by
  unfold Hex4 at h
  split at h
  · rename_i x y z w hx hy hz hw
    simp only [Option.some.injEq] at h
    subst h
    have hx' := hexVal_le hx
    have hy' := hexVal_le hy
    have hz' := hexVal_le hz
    have hw' := hexVal_le hw
    omega
  · simp at h

/-! #### The continuation step

`scanCons` accepts the character exactly when the policy allows it, and then
delegates to the body's remainder. -/

theorem scanCons_ok (pos next c rest cs fin)
    (hnc : IsNoncharacter c = false) (h : scanCharsFrom next rest = .ok (cs, fin)) :
    scanCons pos next c rest = .ok (c :: cs, fin) := by
  unfold scanCons okCons
  rw [if_neg (by simp [hnc])]
  rw [h]

theorem scanCons_inv (pos next c rest cs fin)
    (h : scanCons pos next c rest = .ok (cs, fin)) :
    IsNoncharacter c = false ∧ ∃ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom next rest = .ok (cs', fin') ∧ cs = c :: cs' ∧ fin = fin' := by
  unfold scanCons okCons at h
  split at h
  · simp at h
  · rename_i hnc
    split at h
    · simp at h
    · rename_i cs0 fin0 hrec
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hcs, hfin⟩ := h
      subst hcs
      subst hfin
      refine ⟨?_, cs0, fin0, hrec, rfl, rfl⟩
      cases hb : IsNoncharacter c <;> simp_all

/-! #### Completeness

A `StrChars` derivation names a branch and its side conditions, so the scanner
takes that branch. -/

theorem scanCharsFrom_complete :
    ∀ (b : Bytes) (cs : List Nat) (rest : Bytes),
      StrChars .strict b cs rest → ∀ off : Nat, scanCharsFrom off b = .ok (cs, rest) := by
  intro b cs rest hr
  induction hr with
  | nil =>
      intro off
      exact scanCharsFrom_quote off _
  | cons hch hr ih =>
      intro off
      cases hch with
      | unescaped hutf hctrl hq hb hm =>
          have hnc := strict_noncharacter hm
          cases hutf with
          | one hlt =>
              rw [scanCharsFrom_ascii off _ _ (byte_ne_quote hq) (byte_ne_backslash hb) hlt hctrl]
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 1))
          | two h0 h0' h1 h1' =>
              rw [scanCharsFrom_utf8_two off _ _ _ h0 h0' h1 h1']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 2))
          | three₀ h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_e0 off _ _ _ h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₁ h0 h0' h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_e1ec off _ _ _ _ h0 h0' h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₂ h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_ed off _ _ _ h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₃ h0 h0' h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_eeef off _ _ _ _ h0 h0' h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | four₀ h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f0 off _ _ _ _ h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
          | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f1f3 off _ _ _ _ _ h0 h0' h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
          | four₂ h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f4 off _ _ _ _ h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
      | short hv =>
          rw [scanCharsFrom_escape off _ _ _ hv]
          exact scanCons_ok _ _ _ _ _ _ (escVal_noncharacter hv) (ih (off + 2))
      | escU hx hs hm =>
          rw [scanCharsFrom_uchar off _ _ _ _ _ _ (by decide) hx
            (high_ne_of_scalar hs) (low_ne_of_scalar hs)]
          exact scanCons_ok _ _ _ _ _ _ (strict_noncharacter hm) (ih (off + 6))
      | escPair hx hy hh hl hc hm =>
          rw [scanCharsFrom_pair off _ _ _ _ _ _ _ _ _ _ _ (by decide) hx hy hh hl]
          rw [← hc]
          exact scanCons_ok _ _ _ _ _ _ (strict_noncharacter hm) (ih (off + 12))
      | escLone hm _ _ => cases hm

/-! #### Reading each branch backwards

Each accepting branch, inverted: a successful scan of that branch's byte shape
is the corresponding `StrChar`. -/

theorem strChars_ascii (off : Nat) (q : UInt8) (tl : Bytes)
    (hq : q ≠ 0x22) (hs : q ≠ 0x5C) (hlt : q.toNat < 0x80) (hctrl : 0x20 ≤ q.toNat)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (q +: tl) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 1) tl = .ok (cs', fin') → StrChars .strict tl cs' fin') :
    StrChars .strict (q +: tl) cs fin := by
  rw [scanCharsFrom_ascii off q tl hq hs (UInt8.lt_iff_toNat_lt.mpr hlt) hctrl] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hutf : Utf8Char (q +: tl) q.toNat tl := Utf8Char.one (UInt8.lt_iff_toNat_lt.mpr hlt)
  refine StrChars.cons (StrChar.unescaped hutf hctrl ?_ ?_ ?_) ?_
  · intro hc
    exact hq (UInt8.toNat_inj.mp hc)
  · intro hc
    exact hs (UInt8.toNat_inj.mp hc)
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_escape (off : Nat) (e : UInt8) (rest1 : Bytes) (c : Nat)
    (hv : EscVal e = some c) {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0x5C +: e +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 2) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0x5C +: e +: rest1) cs fin := by
  rw [scanCharsFrom_escape off e rest1 c hv] at h
  obtain ⟨_, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  exact StrChars.cons (StrChar.short hv) (ih cs' fin' hrec)

theorem strChars_uchar (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (c : Nat)
    (hv : EscVal (0x75 : UInt8) = none) (hx : Hex4 h0 h1 h2 h3 = some c)
    (hhi : ¬ (0xD800 ≤ c ∧ c ≤ 0xDBFF)) (hlo : ¬ (0xDC00 ≤ c ∧ c ≤ 0xDFFF))
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) =
      .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 6) rest2 = .ok (cs', fin') → StrChars .strict rest2 cs' fin') :
    StrChars .strict (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest2) cs fin := by
  rw [scanCharsFrom_uchar off h0 h1 h2 h3 rest2 c hv hx hhi hlo] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hbound := hex4_le hx
  have hscalar : IsScalar c := by
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b⟩
    by_cases hb' : c ≤ 0xDBFF
    · exact hhi ⟨a, hb'⟩
    · exact hlo ⟨by omega, b⟩
  exact StrChars.cons (StrChar.escU hx hscalar (charAllowed_of hscalar hnc))
    (ih cs' fin' hrec)

theorem strChars_pair (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8) (rest3 : Bytes)
    (hi lo : Nat) (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some hi) (hy : Hex4 l0 l1 l2 l3 = some lo)
    (hh : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hl : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off
      (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
        l0 +: l1 +: l2 +: l3 +: rest3) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 12) rest3 = .ok (cs', fin') →
        StrChars .strict rest3 cs' fin') :
    StrChars .strict
      (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
        l0 +: l1 +: l2 +: l3 +: rest3) cs fin := by
  rw [scanCharsFrom_pair off h0 h1 h2 h3 l0 l1 l2 l3 rest3 hi lo hv hx hy hh hl] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hb1 := hex4_le hx
  have hb2 := hex4_le hy
  have hscalar : IsScalar (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) := by
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b⟩
    omega
  exact StrChars.cons
    (StrChar.escPair hx hy hh hl rfl (charAllowed_of hscalar hnc))
    (ih cs' fin' hrec)

theorem strChars_utf8_two (off : Nat) (b0 b1 : UInt8) (rest1 : Bytes)
    (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF) (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b0 +: b1 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 2) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b0 +: b1 +: rest1) cs fin := by
  have h0n : (0xC2 : Nat) ≤ b0.toNat := by simpa using le_toNat h0
  have h0n' : b0.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  rw [scanCharsFrom_utf8_two off b0 b1 rest1 h0 h0' h1 h1'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b0 +: b1 +: rest1)
      ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest1 := Utf8Char.two h0 h0' h1 h1'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_e0 (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0xA0 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xE0 +: b1 +: b2 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xE0 +: b1 +: b2 +: rest1) cs fin := by
  have h1n : (0xA0 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_e0 off b1 b2 rest1 h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xE0 +: b1 +: b2 +: rest1)
      ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := Utf8Char.three₀ h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_e1ec (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b +: b1 +: b2 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b +: b1 +: b2 +: rest1) cs fin := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_e1ec off b b1 b2 rest1 hb hb' h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b +: b1 +: b2 +: rest1)
      ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₁ hb hb' h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_ed (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x9F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xED +: b1 +: b2 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xED +: b1 +: b2 +: rest1) cs fin := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x9F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_ed off b1 b2 rest1 h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xED +: b1 +: b2 +: rest1)
      (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₂ h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_eeef (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b +: b1 +: b2 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b +: b1 +: b2 +: rest1) cs fin := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_eeef off b b1 b2 rest1 hb hb' h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b +: b1 +: b2 +: rest1)
      ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₃ hb hb' h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f0 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x90 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xF0 +: b1 +: b2 +: b3 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xF0 +: b1 +: b2 +: b3 +: rest1) cs fin := by
  have h1n : (0x90 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f0 off b1 b2 b3 rest1 h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xF0 +: b1 +: b2 +: b3 +: rest1)
      ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₀ h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f1f3 (off : Nat) (b b1 b2 b3 : UInt8) (rest1 : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b +: b1 +: b2 +: b3 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b +: b1 +: b2 +: b3 +: rest1) cs fin := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f1f3 off b b1 b2 b3 rest1 hb hb' h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b +: b1 +: b2 +: b3 +: rest1)
      ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
        (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₁ hb hb' h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f4 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x8F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xF4 +: b1 +: b2 +: b3 +: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xF4 +: b1 +: b2 +: b3 +: rest1) cs fin := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x8F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f4 off b1 b2 b3 rest1 h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xF4 +: b1 +: b2 +: b3 +: rest1)
      (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
        (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₂ h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

/-! #### Soundness

By induction on the subject's length: the scanner's recursive call is on a
strictly shorter remainder, and every accepting branch yields the corresponding
`StrChar`, so the body is a `StrChars` cons chain. -/

theorem le_of_toNat {a b : UInt8} (h : a.toNat ≤ b.toNat) : a ≤ b :=
  UInt8.le_iff_toNat_le.mpr h

theorem scanCharsFrom_sound_aux (n : Nat) :
    ∀ (l : List UInt8), l.length ≤ n →
      ∀ (off : Nat) (cs : List Nat) (rest : Bytes),
        scanCharsFrom off (ByteString.literal l) = .ok (cs, rest) →
          StrChars .strict (ByteString.literal l) cs rest := by
  induction n with
  | zero =>
      intro l hlen off cs rest h
      cases l with
      | nil => rw [show ByteString.literal ([] : List UInt8) = empty from rfl, scanCharsFrom_nil] at h; simp at h
      | cons q tl => simp at hlen
  | succ n ih =>
      intro l hlen off cs rest h
      cases l with
      | nil => rw [show ByteString.literal ([] : List UInt8) = empty from rfl, scanCharsFrom_nil] at h; simp at h
      | cons q tl =>
          simp only [ByteString.literal_cons] at h ⊢
          have htl : tl.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          by_cases hq : q = 0x22
          · subst hq
            rw [scanCharsFrom_quote] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact StrChars.nil
          · by_cases hs : q = 0x5C
            · subst hs
              cases tl with
              | nil =>
                  simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp at h
              | cons e rest1 =>
                  simp only [ByteString.literal_cons] at h ⊢
                  cases hv : EscVal e with
                  | some c =>
                      have hrest : rest1.length ≤ n := by
                        simp only [List.length_cons] at hlen
                        omega
                      exact strChars_escape off e  (ByteString.literal rest1) c hv h (ih rest1 hrest (off + 2))
                  | none =>
                      by_cases he : e = 0x75
                      · subst he
                        rcases rest1 with _ | ⟨h0, r0⟩
                        · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv] at h
                        · rcases r0 with _ | ⟨h1, r1⟩
                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv] at h
                          · rcases r1 with _ | ⟨h2, r2⟩
                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv] at h
                            · rcases r2 with _ | ⟨h3, rest2⟩
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv] at h
                              · cases hx : Hex4 h0 h1 h2 h3 with
                                | none => simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx] at h
                                | some c =>
                                    by_cases hhi : 0xD800 ≤ c ∧ c ≤ 0xDBFF
                                    · rcases rest2 with _ | ⟨z0, w0⟩
                                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                      · by_cases hz0 : z0 = 0x5C
                                        · subst hz0
                                          rcases w0 with _ | ⟨z1, w1⟩
                                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                          · by_cases hz1 : z1 = 0x75
                                            · subst hz1
                                              rcases w1 with _ | ⟨l0, v0⟩
                                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                              · rcases v0 with _ | ⟨l1, v1⟩
                                                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                                · rcases v1 with _ | ⟨l2, v2⟩
                                                  · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                                  · rcases v2 with _ | ⟨l3, rest3⟩
                                                    · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi] at h
                                                    · cases hy : Hex4 l0 l1 l2 l3 with
                                                      | none =>
                                                          simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi, hy] at h
                                                      | some lo =>
                                                          by_cases hlo : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF
                                                          · have hrest : rest3.length ≤ n := by
                                                              simp only [List.length_cons] at hlen
                                                              omega
                                                            exact strChars_pair off h0 h1 h2 h3
                                                              l0 l1 l2 l3 (ByteString.literal rest3) c lo (by decide)
                                                              hx hy hhi hlo h
                                                              (ih rest3 hrest (off + 12))
                                                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi, hy, hlo] at h
                                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi, hz1] at h
                                        · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi, hz0] at h
                                    · by_cases hlo : 0xDC00 ≤ c ∧ c ≤ 0xDFFF
                                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, hx, hhi, hlo] at h
                                      · have hrest : rest2.length ≤ n := by
                                          simp only [List.length_cons] at hlen
                                          omega
                                        exact strChars_uchar off h0 h1 h2 h3  (ByteString.literal rest2) c
                                          (by decide) hx hhi hlo h (ih rest2 hrest (off + 6))
                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hv, he] at h
            · by_cases hlt : q.toNat < 0x80
              · by_cases hctrl : 0x20 ≤ q.toNat
                · exact strChars_ascii off q  (ByteString.literal tl) hq hs hlt hctrl h (ih tl htl (off + 1))
                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, hctrl] at h
              · by_cases htwo : 0xC2 ≤ q.toNat ∧ q.toNat ≤ 0xDF
                · rcases tl with _ | ⟨b1, rest1⟩
                  · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo] at h
                  · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                    · have hrest : rest1.length ≤ n := by
                        simp only [List.length_cons] at hlen
                        omega
                      exact strChars_utf8_two off q b1  (ByteString.literal rest1)
                        (le_of_toNat htwo.1) (le_of_toNat htwo.2)
                        (le_of_toNat h12.1) (le_of_toNat h12.2) h
                        (ih rest1 hrest (off + 2))
                    · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, h12] at h
                · by_cases he0 : q = 0xE0
                  · subst he0
                    rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                    · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp at h
                    · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp at h
                    · by_cases h12 : 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                          0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                      · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                        have hrest : rest1.length ≤ n := by
                          simp only [List.length_cons] at hlen
                          omega
                        exact strChars_utf8_e0 off b1 b2  (ByteString.literal rest1)
                          (le_of_toNat h1n) (le_of_toNat h1n')
                          (le_of_toNat h2n) (le_of_toNat h2n') h
                          (ih rest1 hrest (off + 3))
                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [h12] at h
                  · by_cases h31 : 0xE1 ≤ q.toNat ∧ q.toNat ≤ 0xEC
                    · rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31] at h
                      · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31] at h
                      · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                            0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                        · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                          have hrest : rest1.length ≤ n := by
                            simp only [List.length_cons] at hlen
                            omega
                          exact strChars_utf8_e1ec off q b1 b2  (ByteString.literal rest1)
                            (le_of_toNat h31.1) (le_of_toNat h31.2)
                            (le_of_toNat h1n) (le_of_toNat h1n')
                            (le_of_toNat h2n) (le_of_toNat h2n') h
                            (ih rest1 hrest (off + 3))
                        · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, h12] at h
                    · by_cases hed : q = 0xED
                      · subst hed
                        rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                        · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0] at h
                        · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0] at h
                        · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧
                              0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                          · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                            have hrest : rest1.length ≤ n := by
                              simp only [List.length_cons] at hlen
                              omega
                            exact strChars_utf8_ed off b1 b2  (ByteString.literal rest1)
                              (le_of_toNat h1n) (le_of_toNat h1n')
                              (le_of_toNat h2n) (le_of_toNat h2n') h
                              (ih rest1 hrest (off + 3))
                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, h12] at h
                      · by_cases h33 : 0xEE ≤ q.toNat ∧ q.toNat ≤ 0xEF
                        · rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33] at h
                          · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33] at h
                          · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                            · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                              have hrest : rest1.length ≤ n := by
                                simp only [List.length_cons] at hlen
                                omega
                              exact strChars_utf8_eeef off q b1 b2  (ByteString.literal rest1)
                                (le_of_toNat h33.1) (le_of_toNat h33.2)
                                (le_of_toNat h1n) (le_of_toNat h1n')
                                (le_of_toNat h2n) (le_of_toNat h2n') h
                                (ih rest1 hrest (off + 3))
                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, h12] at h
                        · by_cases hf0 : q = 0xF0
                          · subst hf0
                            rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed] at h
                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed] at h
                            · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed] at h
                            · by_cases h12 : 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                  0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                              · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                have hrest : rest1.length ≤ n := by
                                  simp only [List.length_cons] at hlen
                                  omega
                                exact strChars_utf8_f0 off b1 b2 b3  (ByteString.literal rest1)
                                  (le_of_toNat h1n) (le_of_toNat h1n')
                                  (le_of_toNat h2n) (le_of_toNat h2n')
                                  (le_of_toNat h3n) (le_of_toNat h3n') h
                                  (ih rest1 hrest (off + 4))
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed, h12] at h
                          · by_cases h41 : 0xF1 ≤ q.toNat ∧ q.toNat ≤ 0xF3
                            · rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                    0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                    0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                  have hrest : rest1.length ≤ n := by
                                    simp only [List.length_cons] at hlen
                                    omega
                                  exact strChars_utf8_f1f3 off q b1 b2 b3  (ByteString.literal rest1)
                                    (le_of_toNat h41.1) (le_of_toNat h41.2)
                                    (le_of_toNat h1n) (le_of_toNat h1n')
                                    (le_of_toNat h2n) (le_of_toNat h2n')
                                    (le_of_toNat h3n) (le_of_toNat h3n') h
                                    (ih rest1 hrest (off + 4))
                                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, hf0, h41, h12] at h
                            · by_cases hf4 : q = 0xF4
                              · subst hf4
                                rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed, hf0] at h
                                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed, hf0] at h
                                · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed, hf0] at h
                                · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧
                                      0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                      0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                  · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                    have hrest : rest1.length ≤ n := by
                                      simp only [List.length_cons] at hlen
                                      omega
                                    exact strChars_utf8_f4 off b1 b2 b3  (ByteString.literal rest1)
                                      (le_of_toNat h1n) (le_of_toNat h1n')
                                      (le_of_toNat h2n) (le_of_toNat h2n')
                                      (le_of_toNat h3n) (le_of_toNat h3n') h
                                      (ih rest1 hrest (off + 4))
                                  · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [he0, hed, hf0, h12] at h
                              · simp only [scanCharsFrom, ByteString.data_toList_cons, ByteString.data_toList_literal] at h; unfold scanCharsL at h; simp [hlt, htwo, he0, h31, hed, h33, hf0, h41, hf4] at h

theorem scanCharsFrom_sound {off : Nat} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : scanCharsFrom off b = .ok (cs, rest)) : StrChars .strict b cs rest := by
  have h' : scanCharsFrom off (ByteString.literal b.data.toList) = .ok (cs, rest) := h
  have := scanCharsFrom_sound_aux b.data.toList.length b.data.toList (Nat.le_refl _) off cs rest h'
  rwa [ByteString.literal_data_toList] at this

/-! #### The index scan against the reference

The index scan reads the carrier at an index; the reference walks the list view.
At every offset the index scan is the reference applied to the tail from that
offset.  The proof follows the branch tree the two definitions share, and each
leaf is one of the equations above: the reference's value at the leaf's shape,
applied to the peeled carrier.  The accepting leaves then close on the induction
hypothesis, because the reference recurses on the tail the leaf left.  The
carrier peels are `Bytes`'s (`ge_of_getElem?_eq_none`,
`data_toList_drop_eq_cons`, `data_toList_drop_eq_nil`), the same ones the number
and whitespace runs index through. -/

/-- The tail's list view is the list view dropped at the same index. -/
private theorem tailFrom_data_toList (bs : Bytes) (j : Nat) :
    (tailFrom bs j).data.toList = bs.data.toList.drop j :=
  ByteString.extract_suffix_data_toList bs j

/-- The tail from index `0` is the subject. -/
private theorem tailFrom_zero (bs : Bytes) : tailFrom bs 0 = bs := by
  apply ByteString.eq_of_data_toList_eq
  rw [tailFrom_data_toList bs 0, List.drop_zero]

/-- The tail past the end is empty. -/
private theorem tailFrom_eq_empty {bs : Bytes} {i : Nat} (h : bs.size ≤ i) :
    tailFrom bs i = empty := by
  apply ByteString.eq_of_data_toList_eq
  rw [tailFrom_data_toList bs i, data_toList_drop_eq_nil h, ByteString.data_toList_empty]

/-- The tail at a byte splits off that byte: the shape the equations are stated in. -/
private theorem tailFrom_cons {bs : Bytes} {i : Nat} {a : UInt8} (h : bs[i]? = some a) :
    tailFrom bs i = a +: tailFrom bs (i + 1) := by
  apply ByteString.eq_of_data_toList_eq
  rw [ByteString.data_toList_cons, tailFrom_data_toList bs _, tailFrom_data_toList bs _,
    data_toList_drop_eq_cons h]

/-- The same split, with the tail's index named by the caller. -/
private theorem tailFrom_cons_at {bs : Bytes} {i j : Nat} {a : UInt8}
    (h : bs[i]? = some a) (hj : j = i + 1) : tailFrom bs i = a +: tailFrom bs j := by
  rw [hj]
  exact tailFrom_cons h

/-- The tail's length is the buffer's remainder, for every index. -/
private theorem tailFrom_length (bs : Bytes) (j : Nat) : (tailFrom bs j).length = bs.size - j := by
  have h : (tailFrom bs j).data.toList.length = bs.data.toList.length - j := by
    rw [tailFrom_data_toList, List.length_drop]
  have h1 : (tailFrom bs j).length = (tailFrom bs j).data.toList.length := by
    rw [ByteString.length_eq_size, ByteString.size_eq_data, Array.length_toList]
  have h2 : bs.size = bs.data.toList.length := by
    rw [ByteString.size_eq_data, Array.length_toList]
  rw [h1, h2, h]

/-- The tail is the dropped suffix. -/
private theorem tailFrom_eq_drop (bs : Bytes) (j : Nat) : tailFrom bs j = bs.drop j := by
  apply ByteString.eq_of_data_toList_eq
  rw [tailFrom_data_toList, ByteString.data_toList_drop]

/-- Reading an error through the tail map is the error. -/
private theorem map_error {α β : Type} (e : ScanError) (f : α → β) :
    (Except.error e : Except ScanError α).map f = Except.error e := rfl

/-- Reading an accepted record through the tail map maps its payload. -/
private theorem map_ok {α β : Type} (a : α) (f : α → β) :
    (Except.ok a : Except ScanError α).map f = Except.ok (f a) := rfl

/-- The continuation commutes with reading the stop as a tail: accepting a
character prepends its code point and passes the index through, so mapping the
index scan's result through `tailFrom` is the reference step. -/
private theorem okConsIx_tail (bs : Bytes) (pos c : Nat)
    (r : Except ScanError (List Nat × Nat)) :
    (okConsIx pos c r).map (fun p => (p.1, tailFrom bs p.2)) =
      okCons pos c (r.map (fun p => (p.1, tailFrom bs p.2))) := by
  unfold okConsIx okCons
  cases r with
  | error e => split <;> simp [Except.map]
  | ok p => split <;> simp [Except.map]

set_option maxHeartbeats 800000 in
/-- The index scan is the reference scan of the tail, at every offset: reading
the carrier at a position and recording the stopping index, then reading the
tail there, is scanning the suffix that position starts. -/
private theorem scanCharsAt_eq (fuel : Nat) :
    ∀ (bs : Bytes) (i off : Nat), bs.size ≤ i + fuel →
      (scanCharsAt bs fuel i off).map (fun p => (p.1, tailFrom bs p.2)) =
        scanCharsFrom off (tailFrom bs i) := by
  induction fuel with
  | zero =>
    intro bs i off h
    have hge : bs.size ≤ i := by omega
    simp only [scanCharsAt.eq_1, map_error, map_ok, tailFrom_eq_empty hge, scanCharsFrom_nil]
  | succ fuel ih =>
    intro bs i off h
    have hb := h
    rw [scanCharsAt.eq_2]
    cases hk : bs[i]? with
    | none =>
      have hge := ge_of_getElem?_eq_none hk
      simp only [hk, map_error, map_ok, tailFrom_eq_empty hge, scanCharsFrom_nil]
    | some a =>
      rw [tailFrom_cons_at (j := i + 1) hk (by omega)]
      by_cases hq : a = 0x22
      · subst a
        have hstep := scanCharsFrom_quote off (tailFrom bs (i + 1))
        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
      · by_cases hs : a = 0x5C
        · subst a
          cases h1 : bs[i + 1]? with
          | none =>
            have hge := ge_of_getElem?_eq_none h1
            rw [tailFrom_eq_empty hge]
            have hstep := scanCharsFrom_escape_ended off
            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
          | some e =>
            rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
            cases hv : EscVal e with
            | some c =>
              have hstep := scanCharsFrom_escape off e (tailFrom bs (i + 2)) c hv
              simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
              rw [okConsIx_tail bs, ih bs (i + 2) (off + 2) (Nat.le_trans hb (by omega))]
            | none =>
              by_cases he : e = 0x75
              · subst e
                have hv' : EscVal (0x75 : UInt8) = none := rfl
                cases h2 : bs[i + 2]? with
                | none =>
                  have hge := ge_of_getElem?_eq_none h2
                  have hstep := scanCharsFrom_uchar_ended off (tailFrom bs (i + 2))
                    (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                  simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                | some h0 =>
                  rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                  cases h3 : bs[i + 3]? with
                  | none =>
                    have hge := ge_of_getElem?_eq_none h3
                    have hstep := scanCharsFrom_uchar_ended off (h0 +: tailFrom bs (i + 3))
                      (by rw [tailFrom_eq_empty hge, ByteString.length_cons, ByteString.length_empty]; omega)
                    simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                  | some h1' =>
                    rw [tailFrom_cons_at (j := i + 4) h3 (by omega)]
                    cases h4 : bs[i + 4]? with
                    | none =>
                      have hge := ge_of_getElem?_eq_none h4
                      have hstep := scanCharsFrom_uchar_ended off
                        (h0 +: h1' +: tailFrom bs (i + 4))
                        (by rw [tailFrom_eq_empty hge, ByteString.length_cons, ByteString.length_cons,
                          ByteString.length_empty]; omega)
                      simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                    | some h2' =>
                      rw [tailFrom_cons_at (j := i + 5) h4 (by omega)]
                      cases h5 : bs[i + 5]? with
                      | none =>
                        have hge := ge_of_getElem?_eq_none h5
                        have hstep := scanCharsFrom_uchar_ended off
                          (h0 +: h1' +: h2' +: tailFrom bs (i + 5))
                          (by rw [tailFrom_eq_empty hge, ByteString.length_cons, ByteString.length_cons,
                            ByteString.length_cons, ByteString.length_empty]; omega)
                        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                      | some h3' =>
                        rw [tailFrom_cons_at (j := i + 6) h5 (by omega)]
                        cases hx : Hex4 h0 h1' h2' h3' with
                        | none =>
                          have hstep := scanCharsFrom_uchar_badHex off h0 h1' h2' h3'
                            (tailFrom bs (i + 6)) hx
                          simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                        | some c =>
                          by_cases hhi : 0xD800 ≤ c ∧ c ≤ 0xDBFF
                          · cases h6 : bs[i + 6]? with
                            | none =>
                              have hge := ge_of_getElem?_eq_none h6
                              have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                (tailFrom bs (i + 6)) c hx hhi
                                (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            | some z0 =>
                              rw [tailFrom_cons_at (j := i + 7) h6 (by omega)]
                              cases h7 : bs[i + 7]? with
                              | none =>
                                have hge := ge_of_getElem?_eq_none h7
                                have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                  (z0 +: tailFrom bs (i + 7)) c hx hhi
                                  (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                    ByteString.length_empty]; omega)
                                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                              | some z1 =>
                                rw [tailFrom_cons_at (j := i + 8) h7 (by omega)]
                                cases h8 : bs[i + 8]? with
                                | none =>
                                  have hge := ge_of_getElem?_eq_none h8
                                  have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                    (z0 +: z1 +: tailFrom bs (i + 8)) c hx hhi
                                    (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                      ByteString.length_cons, ByteString.length_empty]; omega)
                                  simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                | some l0 =>
                                  rw [tailFrom_cons_at (j := i + 9) h8 (by omega)]
                                  cases h9 : bs[i + 9]? with
                                  | none =>
                                    have hge := ge_of_getElem?_eq_none h9
                                    have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                      (z0 +: z1 +: l0 +: tailFrom bs (i + 9)) c hx hhi
                                      (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                        ByteString.length_cons, ByteString.length_cons,
                                        ByteString.length_empty]; omega)
                                    simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                  | some l1 =>
                                    rw [tailFrom_cons_at (j := i + 10) h9 (by omega)]
                                    cases h10 : bs[i + 10]? with
                                    | none =>
                                      have hge := ge_of_getElem?_eq_none h10
                                      have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                        (z0 +: z1 +: l0 +: l1 +: tailFrom bs (i + 10)) c hx hhi
                                        (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                          ByteString.length_cons, ByteString.length_cons,
                                          ByteString.length_cons, ByteString.length_empty]; omega)
                                      simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                    | some l2 =>
                                      rw [tailFrom_cons_at (j := i + 11) h10 (by omega)]
                                      cases h11 : bs[i + 11]? with
                                      | none =>
                                        have hge := ge_of_getElem?_eq_none h11
                                        have hstep := scanCharsFrom_pair_ended off h0 h1' h2' h3'
                                          (z0 +: z1 +: l0 +: l1 +: l2 +: tailFrom bs (i + 11))
                                          c hx hhi
                                          (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                            ByteString.length_cons, ByteString.length_cons,
                                            ByteString.length_cons, ByteString.length_cons,
                                            ByteString.length_empty]; omega)
                                        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                      | some l3 =>
                                        rw [tailFrom_cons_at (j := i + 12) h11 (by omega)]
                                        by_cases hz0 : z0 = 0x5C
                                        · subst z0
                                          by_cases hz1 : z1 = 0x75
                                          · subst z1
                                            cases hy : Hex4 l0 l1 l2 l3 with
                                            | none =>
                                              have hstep := scanCharsFrom_pair_badHex off
                                                h0 h1' h2' h3' l0 l1 l2 l3
                                                (tailFrom bs (i + 12)) c hx hhi hy
                                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                            | some lo =>
                                              by_cases hlo : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF
                                              · have hstep := scanCharsFrom_pair off h0 h1'
                                                  h2' h3' l0 l1 l2 l3
                                                  (tailFrom bs (i + 12)) c lo hv' hx hy hhi hlo
                                                simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                                rw [okConsIx_tail bs, ih bs (i + 12) (off + 12)
                                                  (Nat.le_trans hb (by omega))]
                                              · have hstep := scanCharsFrom_pair_badLow off h0
                                                  h1' h2' h3' l0 l1 l2 l3
                                                  (tailFrom bs (i + 12)) c lo hx hhi hy hlo
                                                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                          · have hstep := scanCharsFrom_pair_noU off h0 h1' h2' h3'
                                              z1 (l0 +: l1 +: l2 +: l3 +: tailFrom bs (i + 12)) c hx
                                              hhi hz1
                                            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                        · have hstep := scanCharsFrom_pair_noEscape off h0 h1'
                                            h2' h3' z0 (z1 +: l0 +: l1 +: l2 +: l3 +: tailFrom bs (i + 12))
                                            c hx hhi hz0
                                          simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                          · by_cases hlo : 0xDC00 ≤ c ∧ c ≤ 0xDFFF
                            · have hstep := scanCharsFrom_uchar_low off h0 h1' h2' h3'
                                (tailFrom bs (i + 6)) c hx hlo
                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            · have hstep := scanCharsFrom_uchar off h0 h1' h2' h3'
                                (tailFrom bs (i + 6)) c hv' hx hhi hlo
                              simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                              rw [okConsIx_tail bs, ih bs (i + 6) (off + 6) (Nat.le_trans hb (by omega))]
              · have hstep := scanCharsFrom_escape_bad off e (tailFrom bs (i + 2)) hv he
                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
        · by_cases hlt : a.toNat < 0x80
          · by_cases hctrl : 0x20 ≤ a.toNat
            · have hstep := scanCharsFrom_ascii off a (tailFrom bs (i + 1)) hq hs
                (UInt8.lt_iff_toNat_lt.mpr hlt) hctrl
              simp only [hstep, scanCons, map_error, map_ok, hk, hq, hs, hlt, hctrl, ite_true, ite_false,
                and_self, and_true, true_and]
              rw [okConsIx_tail bs, ih bs (i + 1) (off + 1) (Nat.le_trans hb (by omega))]
            · have hstep := scanCharsFrom_control off a (tailFrom bs (i + 1)) hlt hctrl
              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
          · by_cases htwo : 0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF
            · cases h1 : bs[i + 1]? with
              | none =>
                have hge := ge_of_getElem?_eq_none h1
                rw [tailFrom_eq_empty hge]
                have hstep := scanCharsFrom_utf8_two_ended off a
                  (le_of_toNat htwo.1) (le_of_toNat htwo.2)
                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
              | some b1 =>
                rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                · have hstep := scanCharsFrom_utf8_two off a b1 (tailFrom bs (i + 2))
                    (le_of_toNat htwo.1) (le_of_toNat htwo.2) (le_of_toNat h12.1) (le_of_toNat h12.2)
                  simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                  rw [okConsIx_tail bs, ih bs (i + 2) (off + 2) (Nat.le_trans hb (by omega))]
                · have hstep := scanCharsFrom_utf8_two_bad off a b1 (tailFrom bs (i + 2))
                    (le_of_toNat htwo.1) (le_of_toNat htwo.2) h12
                  simp only [hstep, map_error, hk, hq, hs, h1, hlt, htwo, h12, ite_true, ite_false,
                    and_self, and_true, true_and]
            · by_cases he0 : a = 0xE0
              · subst a
                cases h1 : bs[i + 1]? with
                | none =>
                  have hge := ge_of_getElem?_eq_none h1
                  have hstep := scanCharsFrom_utf8_e0_ended off (tailFrom bs (i + 1))
                    (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                  simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                | some b1 =>
                  rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                  cases h2 : bs[i + 2]? with
                  | none =>
                    have hge := ge_of_getElem?_eq_none h2
                    have hstep := scanCharsFrom_utf8_e0_ended off (b1 +: tailFrom bs (i + 2))
                      (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                        ByteString.length_empty]; omega)
                    simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                  | some b2 =>
                    rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                    by_cases h12 : 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                      0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                    · have hstep := scanCharsFrom_utf8_e0 off b1 b2 (tailFrom bs (i + 3))
                        (le_of_toNat h12.1) (le_of_toNat h12.2.1) (le_of_toNat h12.2.2.1)
                        (le_of_toNat h12.2.2.2)
                      simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                      rw [okConsIx_tail bs, ih bs (i + 3) (off + 3) (Nat.le_trans hb (by omega))]
                    · have hstep := scanCharsFrom_utf8_e0_bad off b1 b2 (tailFrom bs (i + 3))
                        h12
                      simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
              · by_cases h31 : 0xE1 ≤ a.toNat ∧ a.toNat ≤ 0xEC
                · cases h1 : bs[i + 1]? with
                  | none =>
                    have hge := ge_of_getElem?_eq_none h1
                    have hstep := scanCharsFrom_utf8_e1ec_ended off a (tailFrom bs (i + 1))
                      (le_of_toNat h31.1) (le_of_toNat h31.2)
                      (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                    simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                  | some b1 =>
                    rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                    cases h2 : bs[i + 2]? with
                    | none =>
                      have hge := ge_of_getElem?_eq_none h2
                      have hstep := scanCharsFrom_utf8_e1ec_ended off a
                        (b1 +: tailFrom bs (i + 2)) (le_of_toNat h31.1) (le_of_toNat h31.2)
                        (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                          ByteString.length_empty]; omega)
                      simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                    | some b2 =>
                      rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                      by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                        0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                      · have hstep := scanCharsFrom_utf8_e1ec off a b1 b2 (tailFrom bs (i + 3))
                          (le_of_toNat h31.1) (le_of_toNat h31.2) (le_of_toNat h12.1)
                          (le_of_toNat h12.2.1) (le_of_toNat h12.2.2.1) (le_of_toNat h12.2.2.2)
                        simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                        rw [okConsIx_tail bs, ih bs (i + 3) (off + 3) (Nat.le_trans hb (by omega))]
                      · have hstep := scanCharsFrom_utf8_e1ec_bad off a b1 b2
                          (tailFrom bs (i + 3)) (le_of_toNat h31.1) (le_of_toNat h31.2) h12
                        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                · by_cases hed : a = 0xED
                  · subst a
                    cases h1 : bs[i + 1]? with
                    | none =>
                      have hge := ge_of_getElem?_eq_none h1
                      have hstep := scanCharsFrom_utf8_ed_ended off (tailFrom bs (i + 1))
                        (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                      simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                    | some b1 =>
                      rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                      cases h2 : bs[i + 2]? with
                      | none =>
                        have hge := ge_of_getElem?_eq_none h2
                        have hstep := scanCharsFrom_utf8_ed_ended off (b1 +: tailFrom bs (i + 2))
                          (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                            ByteString.length_empty]; omega)
                        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                      | some b2 =>
                        rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                        by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧
                          0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                        · have hstep := scanCharsFrom_utf8_ed off b1 b2 (tailFrom bs (i + 3))
                            (le_of_toNat h12.1) (le_of_toNat h12.2.1) (le_of_toNat h12.2.2.1)
                            (le_of_toNat h12.2.2.2)
                          simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                          rw [okConsIx_tail bs, ih bs (i + 3) (off + 3) (Nat.le_trans hb (by omega))]
                        · have hstep := scanCharsFrom_utf8_ed_bad off b1 b2
                            (tailFrom bs (i + 3)) h12
                          simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                  · by_cases h33 : 0xEE ≤ a.toNat ∧ a.toNat ≤ 0xEF
                    · cases h1 : bs[i + 1]? with
                      | none =>
                        have hge := ge_of_getElem?_eq_none h1
                        have hstep := scanCharsFrom_utf8_eeef_ended off a
                          (tailFrom bs (i + 1)) (le_of_toNat h33.1) (le_of_toNat h33.2)
                          (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                        simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                      | some b1 =>
                        rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                        cases h2 : bs[i + 2]? with
                        | none =>
                          have hge := ge_of_getElem?_eq_none h2
                          have hstep := scanCharsFrom_utf8_eeef_ended off a
                            (b1 +: tailFrom bs (i + 2)) (le_of_toNat h33.1) (le_of_toNat h33.2)
                            (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                              ByteString.length_empty]; omega)
                          simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                        | some b2 =>
                          rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                          by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                            0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                          · have hstep := scanCharsFrom_utf8_eeef off a b1 b2
                              (tailFrom bs (i + 3)) (le_of_toNat h33.1) (le_of_toNat h33.2)
                              (le_of_toNat h12.1) (le_of_toNat h12.2.1) (le_of_toNat h12.2.2.1)
                              (le_of_toNat h12.2.2.2)
                            simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            rw [okConsIx_tail bs, ih bs (i + 3) (off + 3) (Nat.le_trans hb (by omega))]
                          · have hstep := scanCharsFrom_utf8_eeef_bad off a b1 b2
                              (tailFrom bs (i + 3)) (le_of_toNat h33.1) (le_of_toNat h33.2) h12
                            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                    · by_cases hf0 : a = 0xF0
                      · subst a
                        cases h1 : bs[i + 1]? with
                        | none =>
                          have hge := ge_of_getElem?_eq_none h1
                          have hstep := scanCharsFrom_utf8_f0_ended off (tailFrom bs (i + 1))
                            (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                          simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                        | some b1 =>
                          rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                          cases h2 : bs[i + 2]? with
                          | none =>
                            have hge := ge_of_getElem?_eq_none h2
                            have hstep := scanCharsFrom_utf8_f0_ended off
                              (b1 +: tailFrom bs (i + 2))
                              (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                ByteString.length_empty]; omega)
                            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                          | some b2 =>
                            rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                            cases h3 : bs[i + 3]? with
                            | none =>
                              have hge := ge_of_getElem?_eq_none h3
                              have hstep := scanCharsFrom_utf8_f0_ended off
                                (b1 +: b2 +: tailFrom bs (i + 3))
                                (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                  ByteString.length_cons, ByteString.length_empty]; omega)
                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            | some b3 =>
                              rw [tailFrom_cons_at (j := i + 4) h3 (by omega)]
                              by_cases h12 : 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                              · have hstep := scanCharsFrom_utf8_f0 off b1 b2 b3
                                  (tailFrom bs (i + 4)) (le_of_toNat h12.1) (le_of_toNat h12.2.1)
                                  (le_of_toNat h12.2.2.1) (le_of_toNat h12.2.2.2.1)
                                  (le_of_toNat h12.2.2.2.2.1) (le_of_toNat h12.2.2.2.2.2)
                                simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                rw [okConsIx_tail bs, ih bs (i + 4) (off + 4) (Nat.le_trans hb (by omega))]
                              · have hstep := scanCharsFrom_utf8_f0_bad off b1 b2 b3
                                  (tailFrom bs (i + 4)) h12
                                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                      · by_cases h41 : 0xF1 ≤ a.toNat ∧ a.toNat ≤ 0xF3
                        · cases h1 : bs[i + 1]? with
                          | none =>
                            have hge := ge_of_getElem?_eq_none h1
                            have hstep := scanCharsFrom_utf8_f1f3_ended off a
                              (tailFrom bs (i + 1)) (le_of_toNat h41.1) (le_of_toNat h41.2)
                              (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                          | some b1 =>
                            rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                            cases h2 : bs[i + 2]? with
                            | none =>
                              have hge := ge_of_getElem?_eq_none h2
                              have hstep := scanCharsFrom_utf8_f1f3_ended off a
                                (b1 +: tailFrom bs (i + 2)) (le_of_toNat h41.1) (le_of_toNat h41.2)
                                (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                  ByteString.length_empty]; omega)
                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            | some b2 =>
                              rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                              cases h3 : bs[i + 3]? with
                              | none =>
                                have hge := ge_of_getElem?_eq_none h3
                                have hstep := scanCharsFrom_utf8_f1f3_ended off a
                                  (b1 +: b2 +: tailFrom bs (i + 3)) (le_of_toNat h41.1)
                                  (le_of_toNat h41.2)
                                  (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                    ByteString.length_cons, ByteString.length_empty]; omega)
                                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                              | some b3 =>
                                rw [tailFrom_cons_at (j := i + 4) h3 (by omega)]
                                by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                  0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                · have hstep := scanCharsFrom_utf8_f1f3 off a b1 b2 b3
                                    (tailFrom bs (i + 4)) (le_of_toNat h41.1) (le_of_toNat h41.2)
                                    (le_of_toNat h12.1) (le_of_toNat h12.2.1)
                                    (le_of_toNat h12.2.2.1) (le_of_toNat h12.2.2.2.1)
                                    (le_of_toNat h12.2.2.2.2.1) (le_of_toNat h12.2.2.2.2.2)
                                  simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                  rw [okConsIx_tail bs, ih bs (i + 4) (off + 4) (Nat.le_trans hb (by omega))]
                                · have hstep := scanCharsFrom_utf8_f1f3_bad off a b1 b2 b3
                                    (tailFrom bs (i + 4)) (le_of_toNat h41.1) (le_of_toNat h41.2) h12
                                  simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                        · by_cases hf4 : a = 0xF4
                          · subst a
                            cases h1 : bs[i + 1]? with
                            | none =>
                              have hge := ge_of_getElem?_eq_none h1
                              have hstep := scanCharsFrom_utf8_f4_ended off (tailFrom bs (i + 1))
                                (by rw [tailFrom_eq_empty hge, ByteString.length_empty]; omega)
                              simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                            | some b1 =>
                              rw [tailFrom_cons_at (j := i + 2) h1 (by omega)]
                              cases h2 : bs[i + 2]? with
                              | none =>
                                have hge := ge_of_getElem?_eq_none h2
                                have hstep := scanCharsFrom_utf8_f4_ended off
                                  (b1 +: tailFrom bs (i + 2))
                                  (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                    ByteString.length_empty]; omega)
                                simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                              | some b2 =>
                                rw [tailFrom_cons_at (j := i + 3) h2 (by omega)]
                                cases h3 : bs[i + 3]? with
                                | none =>
                                  have hge := ge_of_getElem?_eq_none h3
                                  have hstep := scanCharsFrom_utf8_f4_ended off
                                    (b1 +: b2 +: tailFrom bs (i + 3))
                                    (by rw [tailFrom_eq_empty hge, ByteString.length_cons,
                                      ByteString.length_cons, ByteString.length_empty]; omega)
                                  simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                | some b3 =>
                                  rw [tailFrom_cons_at (j := i + 4) h3 (by omega)]
                                  by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧
                                    0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                    0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                  · have hstep := scanCharsFrom_utf8_f4 off b1 b2 b3
                                      (tailFrom bs (i + 4)) (le_of_toNat h12.1) (le_of_toNat h12.2.1)
                                      (le_of_toNat h12.2.2.1) (le_of_toNat h12.2.2.2.1)
                                      (le_of_toNat h12.2.2.2.2.1) (le_of_toNat h12.2.2.2.2.2)
                                    simp_all only [hstep, scanCons, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                                    rw [okConsIx_tail bs, ih bs (i + 4) (off + 4) (Nat.le_trans hb (by omega))]
                                  · have hstep := scanCharsFrom_utf8_f4_bad off b1 b2 b3
                                      (tailFrom bs (i + 4)) h12
                                    simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]
                          · have hbad : ¬ (0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xF4) := by
                              rintro ⟨h1, h2⟩
                              have hgt : ¬ a.toNat ≤ 0xDF := fun h => htwo ⟨h1, h⟩
                              have hE0 : 0xE0 ≤ a.toNat := Nat.succ_le_of_lt (Nat.lt_of_not_le hgt)
                              have hne0 : a.toNat ≠ 0xE0 := fun h => he0 (UInt8.toNat_inj.mp h)
                              have hE1 : 0xE1 ≤ a.toNat := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hE0 hne0.symm)
                              by_cases hEC : a.toNat ≤ 0xEC
                              · exact h31 ⟨hE1, hEC⟩
                              · have hED : 0xED ≤ a.toNat :=
                                  Nat.succ_le_of_lt (Nat.lt_of_not_le hEC)
                                have hneD : a.toNat ≠ 0xED := fun h => hed (UInt8.toNat_inj.mp h)
                                have hEE : 0xEE ≤ a.toNat :=
                                  Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hED hneD.symm)
                                by_cases hEF : a.toNat ≤ 0xEF
                                · exact h33 ⟨hEE, hEF⟩
                                · have hF0 : 0xF0 ≤ a.toNat :=
                                    Nat.succ_le_of_lt (Nat.lt_of_not_le hEF)
                                  have hneF : a.toNat ≠ 0xF0 := fun h => hf0 (UInt8.toNat_inj.mp h)
                                  have hF1 : 0xF1 ≤ a.toNat :=
                                    Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hF0 hneF.symm)
                                  by_cases hF3 : a.toNat ≤ 0xF3
                                  · exact h41 ⟨hF1, hF3⟩
                                  · have hF4 : 0xF4 ≤ a.toNat :=
                                      Nat.succ_le_of_lt (Nat.lt_of_not_le hF3)
                                    exact hf4 (UInt8.toNat_inj.mp (Nat.le_antisymm h2 hF4))
                            have hstep := scanCharsFrom_utf8_lead off a (tailFrom bs (i + 1))
                              (Nat.not_lt.mp hlt) hbad
                            simp_all only [hstep, map_error, map_ok, ite_true, ite_false, and_self, and_true, true_and]

/-- The string scanner at the start of a body is the index scan, and the index
scan is the reference scan of the body: the bridge the reflection lemma rewrites
through. -/
theorem scanChars_eq (bs : Bytes) : scanChars bs = scanCharsFrom 0 bs := by
  rw [scanChars, scanCharsAt_eq bs.size bs 0 0 (by omega), tailFrom_zero]

/-! #### The position scan

The parser and the tape decoder read the carrier at the index a token starts at,
so they use `scanCharsEnd`, which records the index after the closing quote
instead of materialising the bytes past it.  These are the lemmas that state
what the recorded index means, in the reference scan's own terms. -/

/-- A clamped stop names the same suffix as the index it clamps: past the end a
drop is empty whichever of the two indices is used. -/
private theorem drop_min (bs : Bytes) (k : Nat) : bs.drop (min k bs.size) = bs.drop k := by
  rcases Nat.lt_or_ge k bs.size with hlt | hge
  · rw [show min k bs.size = k from by omega]
  · have hk : bs.drop k = empty := by
      apply ByteString.eq_empty_of_data_toList
      rw [ByteString.data_toList_drop, data_toList_drop_eq_nil (by omega)]
    have hm : bs.drop (min k bs.size) = empty := by
      rw [show min k bs.size = bs.size from by omega]
      exact ByteString.drop_length bs
    rw [hk, hm]

/-- Reading a mapped success back: the value under the map accepted. -/
private theorem map_ok_inv {α β : Type} {e : Except ScanError α} {f : α → β} {b : β}
    (h : e.map f = .ok b) : ∃ a, e = .ok a := by
  cases e with
  | error err => rw [map_error] at h; cases h
  | ok a => exact ⟨a, rfl⟩

/-- The position scan's success is the reference scan's success, and its stop
names the buffer position the reference remainder begins at. -/
theorem scanCharsEnd_sound {bs : Bytes} {i off : Nat} {cs : List Nat}
    {stop : { n : Nat // n ≤ bs.size }}
    (h : scanCharsEnd bs i off = .ok (cs, stop)) :
    ∃ rest : Bytes, scanCharsFrom off (bs.drop i) = .ok (cs, rest) ∧
      bs.drop stop.val = rest := by
  rcases Nat.lt_or_ge i bs.size with hi | hi
  · have hmap := scanCharsAt_eq (bs.size - i) bs i off (by omega)
    unfold scanCharsEnd at h
    split at h
    · cases h
    · rename_i cs0 stop0 hs
      have hp := Except.ok.inj h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨hcs, hstop⟩ := hp
      rw [hcs] at hs
      have hval : stop.val = min stop0 bs.size := by
        rw [← hstop]
      have hm : (Except.ok (cs, stop0) : Except ScanError (List Nat × Nat)).map
          (fun p => (p.1, tailFrom bs p.2)) = scanCharsFrom off (tailFrom bs i) := by
        rw [← hs]; exact hmap
      rw [map_ok] at hm
      refine ⟨tailFrom bs stop0, ?_, ?_⟩
      · rw [← tailFrom_eq_drop, ← hm]
      · rw [hval, drop_min, tailFrom_eq_drop]
  · have hz : bs.size - i = 0 := by omega
    unfold scanCharsEnd at h
    rw [hz] at h
    simp only [scanCharsAt.eq_1] at h
    cases h

/-- The reference scan's success is the position scan's, and the recorded stop
names where the reference remainder begins. -/
theorem scanCharsEnd_ok_of_scanCharsFrom {bs : Bytes} {i off : Nat} {cs : List Nat}
    {rest : Bytes} (h : scanCharsFrom off (bs.drop i) = .ok (cs, rest)) :
    ∃ stop : { n : Nat // n ≤ bs.size },
      scanCharsEnd bs i off = .ok (cs, stop) ∧ bs.drop stop.val = rest := by
  rcases Nat.lt_or_ge i bs.size with hi | hi
  · have hmap := scanCharsAt_eq (bs.size - i) bs i off (by omega)
    have hfrom : scanCharsFrom off (tailFrom bs i) = .ok (cs, rest) := by
      rw [tailFrom_eq_drop]; exact h
    have hok : (scanCharsAt bs (bs.size - i) i off).map
        (fun p => (p.1, tailFrom bs p.2)) = .ok (cs, rest) := by
      rw [hmap]; exact hfrom
    obtain ⟨⟨cs0, e0⟩, he⟩ := map_ok_inv hok
    have hpair : (cs0, tailFrom bs e0) = (cs, rest) := by
      rw [he, map_ok] at hok
      exact Except.ok.inj hok
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨hcs, hrest⟩ := hpair
    rw [hcs] at he
    refine ⟨⟨min e0 bs.size, Nat.min_le_right _ _⟩, ?_, ?_⟩
    · have : scanCharsEnd bs i off =
          .ok (cs, (⟨min e0 bs.size, Nat.min_le_right _ _⟩ : { n : Nat // n ≤ bs.size })) := by
        unfold scanCharsEnd
        rw [he]
      rw [this]
    · show bs.drop (min e0 bs.size) = rest
      rw [drop_min, ← hrest, tailFrom_eq_drop]
  · have hd : bs.drop i = empty := by
      apply ByteString.eq_empty_of_data_toList
      rw [ByteString.data_toList_drop, data_toList_drop_eq_nil (by omega)]
    rw [hd, scanCharsFrom_nil] at h
    cases h

/-- The position scan's refusal is the reference scan's: the same reason and the
same offset.  `scanCharsEnd_sound` states the success side; this states the
failure side, which is what a caller reporting *why* a body was refused reads.
The two together fix the position scan's value on every input, so a decision
read through `scanCharsEnd` names the reference's own reason rather than a
second implementation's. -/
theorem scanCharsEnd_error {bs : Bytes} {i off : Nat} {e : ScanError} :
    scanCharsEnd bs i off = .error e ↔ scanCharsFrom off (bs.drop i) = .error e := by
  rcases Nat.lt_or_ge i bs.size with hi | hi
  · have hmap := scanCharsAt_eq (bs.size - i) bs i off (by omega)
    have hmap' : (scanCharsAt bs (bs.size - i) i off).map
        (fun p => (p.1, tailFrom bs p.2)) = scanCharsFrom off (bs.drop i) := by
      rw [hmap, tailFrom_eq_drop]
    constructor
    · intro h
      unfold scanCharsEnd at h
      split at h
      · rename_i err he
        have herr : err = e := Except.error.inj h
        rw [← hmap', he, map_error, herr]
      · cases h
    · intro h
      unfold scanCharsEnd
      rw [← hmap'] at h
      cases hc : scanCharsAt bs (bs.size - i) i off with
      | error err =>
        have herr : err = e := by
          rw [hc, map_error] at h
          exact Except.error.inj h
        rw [herr]
      | ok p => rw [hc] at h; cases h
  · have hz : bs.size - i = 0 := by omega
    have hd : bs.drop i = empty := by
      apply ByteString.eq_empty_of_data_toList
      rw [ByteString.data_toList_drop, data_toList_drop_eq_nil (by omega)]
    rw [hd]
    unfold scanCharsEnd
    rw [hz]
    simp only [scanCharsAt.eq_1, scanCharsFrom_nil, Except.error.injEq]

/-! #### The reflection lemma -/

/-- The success side of `scanChars` is exactly the strict character relation.  The
failure side adds nothing to what the theorems know: it is the complement. -/
theorem scanChars_iff (b : Bytes) (cs : List Nat) (rest : Bytes) :
    scanChars b = .ok (cs, rest) ↔ StrChars .strict b cs rest := by
  rw [scanChars_eq]
  constructor
  · intro h
    exact scanCharsFrom_sound h
  · intro h
    exact scanCharsFrom_complete b cs rest h 0

/-! #### The mode correspondence

The two modes differ in exactly two places in `StrChar`: the raw, `\u` and
surrogate-pair clauses carry `ModeAllows`, which is `True` in `rfc` and
`CharAllowed` in `strict`, and `escLone` — RFC 8259 §8.2's unpaired surrogate
escape — has no `strict` derivation at all.  `valid_iff_strict` is those two
differences read in each direction.  A value's policy is a property of its whole
tree, so each direction is a joint induction over the six grammar relations,
with `StrChars` supplying the string leaf. -/

/-- The three membership forms the list-level motives are stated in. -/
private theorem forall_mem_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  cases hx

private theorem forall_mem_singleton {α : Type} {P : α → Prop} {a : α} (h : P a) :
    ∀ x ∈ [a], P x := by
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact h

private theorem forall_mem_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (h1 : P a)
    (h2 : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1
  · exact h2 x hx

/-- Every code point a two-character escape denotes is a scalar: the eight escapes
of §7 all lie in the BMP. -/
theorem escVal_scalar {e : UInt8} {c : Nat} (h : EscVal e = some c) : IsScalar c := by
  unfold EscVal at h
  split at h <;> (first | (simp_all only [Option.some.injEq]; subst_vars; decide) | simp_all)

/-- Every code point a two-character escape denotes satisfies `Policy`. -/
theorem escVal_charAllowed {e : UInt8} {c : Nat} (h : EscVal e = some c) : CharAllowed c :=
  ⟨escVal_scalar h, escVal_noncharacter h⟩

/-- A `strict` character's code point satisfies RFC 7493 §2.1.  The raw and `\u`
clauses carry `ModeAllows .strict`, the two-character escape is enumerated, and
`escLone` cannot occur in `strict`. -/
theorem strChar_strict_allowed {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .strict b c rest) : CharAllowed c := by
  cases h with
  | unescaped _ _ _ _ hm => exact hm
  | short he => exact escVal_charAllowed he
  | escU _ _ hm => exact hm
  | escPair _ _ _ _ _ hm => exact hm
  | escLone hm _ _ => cases hm

/-- Every code point of a `strict` string body satisfies RFC 7493 §2.1. -/
theorem strChars_strict_policy {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .strict b cs rest) : ∀ c ∈ cs, CharAllowed c := by
  induction h with
  | nil => intro c hc; cases hc
  | cons hch _ ih =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact strChar_strict_allowed hch
      · exact ih c hc

/-- Mode weakening, character case: an `rfc` character is a `strict` one when its
code point satisfies `Policy`.  `escLone` is the case whose hypothesis refutes
it. -/
theorem strChar_rfc_strict {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .rfc b c rest) (hc : CharAllowed c) : StrChar .strict b c rest := by
  cases h with
  | unescaped h8 hctrl hq hb _ => exact .unescaped h8 hctrl hq hb hc
  | short he => exact .short he
  | escU hx hs _ => exact .escU hx hs hc
  | escPair hhi hlo hh hl hco _ => exact .escPair hhi hlo hh hl hco hc
  | escLone _ _ hs => exact absurd hc.1 hs

/-- Mode weakening for a string body. -/
theorem strChars_rfc_strict {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .rfc b cs rest) (hp : ∀ c ∈ cs, CharAllowed c) :
    StrChars .strict b cs rest := by
  induction h with
  | nil => exact .nil
  | cons hch _ ih =>
      exact .cons (strChar_rfc_strict hch (hp _ List.mem_cons_self))
        (ih (fun c hc => hp c (List.mem_cons_of_mem _ hc)))

/-- Mode weakening for a string literal. -/
theorem stringAt_rfc_strict {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .rfc bs i j cs) (hp : ∀ c ∈ cs, CharAllowed c) :
    StringAt .strict bs i j cs := by
  obtain ⟨hq, rest, hsc, hdrop⟩ := h
  exact ⟨hq, rest, strChars_rfc_strict hsc hp, hdrop⟩

/-- The other direction at the character level: a `strict` character is an `rfc`
one, because `ModeAllows .rfc` is `True`. -/
theorem strChar_strict_rfc {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .strict b c rest) : StrChar .rfc b c rest := by
  cases h with
  | unescaped h8 hctrl hq hb _ => exact .unescaped h8 hctrl hq hb trivial
  | short he => exact .short he
  | escU hx hs _ => exact .escU hx hs trivial
  | escPair hhi hlo hh hl hc _ => exact .escPair hhi hlo hh hl hc trivial
  | escLone hm _ _ => cases hm

/-- A `strict` string body is an `rfc` one. -/
theorem strChars_strict_rfc {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .strict b cs rest) : StrChars .rfc b cs rest := by
  induction h with
  | nil => exact .nil
  | cons hch _ ih => exact .cons (strChar_strict_rfc hch) ih

/-- A `strict` string literal is an `rfc` one. -/
theorem stringAt_strict_rfc {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict bs i j cs) : StringAt .rfc bs i j cs := by
  obtain ⟨hq, rest, hsc, hdrop⟩ := h
  exact ⟨hq, rest, strChars_strict_rfc hsc, hdrop⟩

/-- A `strict` string literal's code points satisfy `Policy`. -/
theorem stringAt_strict_policy {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict bs i j cs) : ∀ c ∈ cs, CharAllowed c := by
  obtain ⟨-, rest, hsc, -⟩ := h
  exact strChars_strict_policy hsc

/- Policy-directed mode weakening, value case: an `rfc` derivation of a value
whose code points satisfy `Policy` is a `strict` derivation. -/
mutual
theorem valueAt_rfc_strict : (bs : Bytes) → (i : Nat) → (v : Value) → (j : Nat) →
    ValueAt .rfc bs i v j → v.charPolicy → ValueAt .strict bs i v j
  | _, _, _, _, .null h, _ => .null h
  | _, _, _, _, .true h, _ => .true h
  | _, _, _, _, .false h, _ => .false h
  | _, _, _, _, .number h, _ => .number h
  | _, _, _, _, .string h, hp =>
      .string (stringAt_rfc_strict h ((charPolicy_string _).mp hp))
  | _, _, _, _, .array hl hb hr, hp =>
      .array hl (arrBody_rfc_strict _ _ _ _ hb ((charPolicy_array _).mp hp)) hr
  | _, _, _, _, .object hl hb hr, hp =>
      .object hl (objBody_rfc_strict _ _ _ _ hb
        ((membersPolicy_iff _).mp ((charPolicy_object _).mp hp))) hr

/-- Policy-directed mode weakening, array body case. -/
theorem arrBody_rfc_strict : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    ArrBody .rfc bs i vs k → (∀ v ∈ vs, v.charPolicy) → ArrBody .strict bs i vs k
  | _, _, _, _, .empty h, _ => .empty h
  | _, _, _, _, .elems he h, hp => .elems (elems_rfc_strict _ _ _ _ he hp) h

/-- Policy-directed mode weakening, element-list case. -/
theorem elems_rfc_strict : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    Elems .rfc bs i vs k → (∀ v ∈ vs, v.charPolicy) → Elems .strict bs i vs k
  | _, _, _, _, .last hv hw, hp =>
      .last (valueAt_rfc_strict _ _ _ _ hv (hp _ (List.mem_singleton_self _))) hw
  | _, _, _, _, .cons hv hw1 hc hw2 hr, hp =>
      .cons (valueAt_rfc_strict _ _ _ _ hv (hp _ List.mem_cons_self)) hw1 hc hw2
        (elems_rfc_strict _ _ _ _ hr (fun x hx => hp x (List.mem_cons_of_mem _ hx)))

/-- Policy-directed mode weakening, member case: the name and the value are
checked separately. -/
theorem member_rfc_strict : (bs : Bytes) → (i : Nat) → (mem : List Nat × Value) → (j : Nat) →
    Member .rfc bs i mem j → ((∀ c ∈ mem.1, CharAllowed c) ∧ mem.2.charPolicy) →
      Member .strict bs i mem j
  | _, _, _, _, .mk hk hw1 hc hw2 hv, hp =>
      .mk (stringAt_rfc_strict hk hp.1) hw1 hc hw2 (valueAt_rfc_strict _ _ _ _ hv hp.2)

/-- Policy-directed mode weakening, member-list case. -/
theorem members_rfc_strict : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    Members .rfc bs i ms k → (∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy) →
      Members .strict bs i ms k
  | _, _, _, _, .last hm hw, hp =>
      .last (member_rfc_strict _ _ _ _ hm (hp _ (List.mem_singleton_self _))) hw
  | _, _, _, _, .cons hm hw1 hc hw2 hr, hp =>
      .cons (member_rfc_strict _ _ _ _ hm (hp _ List.mem_cons_self)) hw1 hc hw2
        (members_rfc_strict _ _ _ _ hr (fun x hx => hp x (List.mem_cons_of_mem _ hx)))

/-- Policy-directed mode weakening, object body case. -/
theorem objBody_rfc_strict : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    ObjBody .rfc bs i ms k → (∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy) →
      ObjBody .strict bs i ms k
  | _, _, _, _, .empty h, _ => .empty h
  | _, _, _, _, .members hm h, hp => .members (members_rfc_strict _ _ _ _ hm hp) h
end

/- The reading side: a `strict` derivation is an `rfc` derivation, and the policy
of the value it names.  The second component is where `Policy` is produced rather
than consumed. -/
mutual
theorem valueAt_strict_rfc : (bs : Bytes) → (i : Nat) → (v : Value) → (j : Nat) →
    ValueAt .strict bs i v j → ValueAt .rfc bs i v j ∧ v.charPolicy
  | _, _, _, _, .null h => ⟨.null h, charPolicy_null⟩
  | _, _, _, _, .true h => ⟨.true h, charPolicy_bool _⟩
  | _, _, _, _, .false h => ⟨.false h, charPolicy_bool _⟩
  | _, _, _, _, .number h => ⟨.number h, charPolicy_number _⟩
  | _, _, _, _, .string h =>
      ⟨.string (stringAt_strict_rfc h),
       (charPolicy_string _).mpr (stringAt_strict_policy h)⟩
  | _, _, _, _, .array hl hb hr =>
      ⟨.array hl (arrBody_strict_rfc _ _ _ _ hb).1 hr,
       (charPolicy_array _).mpr (arrBody_strict_rfc _ _ _ _ hb).2⟩
  | _, _, _, _, .object hl hb hr =>
      ⟨.object hl (objBody_strict_rfc _ _ _ _ hb).1 hr,
       (charPolicy_object _).mpr
         ((membersPolicy_iff _).mpr (objBody_strict_rfc _ _ _ _ hb).2)⟩

/-- The reading side, array body case. -/
theorem arrBody_strict_rfc : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    ArrBody .strict bs i vs k → ArrBody .rfc bs i vs k ∧ (∀ v ∈ vs, v.charPolicy)
  | _, _, _, _, .empty h => ⟨.empty h, forall_mem_nil⟩
  | _, _, _, _, .elems he h =>
      ⟨.elems (elems_strict_rfc _ _ _ _ he).1 h, (elems_strict_rfc _ _ _ _ he).2⟩

/-- The reading side, element-list case. -/
theorem elems_strict_rfc : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    Elems .strict bs i vs k → Elems .rfc bs i vs k ∧ (∀ v ∈ vs, v.charPolicy)
  | _, _, _, _, .last hv hw =>
      ⟨.last (valueAt_strict_rfc _ _ _ _ hv).1 hw,
       forall_mem_singleton (valueAt_strict_rfc _ _ _ _ hv).2⟩
  | _, _, _, _, .cons hv hw1 hc hw2 hr =>
      ⟨.cons (valueAt_strict_rfc _ _ _ _ hv).1 hw1 hc hw2
          (elems_strict_rfc _ _ _ _ hr).1,
       forall_mem_cons (valueAt_strict_rfc _ _ _ _ hv).2 (elems_strict_rfc _ _ _ _ hr).2⟩

/-- The reading side, member case. -/
theorem member_strict_rfc : (bs : Bytes) → (i : Nat) → (mem : List Nat × Value) → (j : Nat) →
    Member .strict bs i mem j →
      Member .rfc bs i mem j ∧ ((∀ c ∈ mem.1, CharAllowed c) ∧ mem.2.charPolicy)
  | _, _, _, _, .mk hk hw1 hc hw2 hv =>
      ⟨.mk (stringAt_strict_rfc hk) hw1 hc hw2 (valueAt_strict_rfc _ _ _ _ hv).1,
       ⟨stringAt_strict_policy hk, (valueAt_strict_rfc _ _ _ _ hv).2⟩⟩

/-- The reading side, member-list case. -/
theorem members_strict_rfc : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    Members .strict bs i ms k →
      Members .rfc bs i ms k ∧ ∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy
  | _, _, _, _, .last hm hw =>
      ⟨.last (member_strict_rfc _ _ _ _ hm).1 hw,
       forall_mem_singleton (member_strict_rfc _ _ _ _ hm).2⟩
  | _, _, _, _, .cons hm hw1 hc hw2 hr =>
      ⟨.cons (member_strict_rfc _ _ _ _ hm).1 hw1 hc hw2
          (members_strict_rfc _ _ _ _ hr).1,
       forall_mem_cons (member_strict_rfc _ _ _ _ hm).2
         (members_strict_rfc _ _ _ _ hr).2⟩

/-- The reading side, object body case. -/
theorem objBody_strict_rfc : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    ObjBody .strict bs i ms k →
      ObjBody .rfc bs i ms k ∧ ∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy
  | _, _, _, _, .empty h => ⟨.empty h, forall_mem_nil⟩
  | _, _, _, _, .members hm h =>
      ⟨.members (members_strict_rfc _ _ _ _ hm).1 h, (members_strict_rfc _ _ _ _ hm).2⟩
end

/-- `ValidDocument` and `StrictText` are the same language: the RFC 8259 grammar
restricted by RFC 7493 §2.1's character constraint.  The two directions are the
mode correspondence above; the top-level indices and the whitespace are mode
independent, so only the `ValueAt` derivation moves. -/
theorem valid_iff_strict (bs : Bytes) (v : Value) :
    (RfcText bs v ∧ Policy v) ↔ StrictText bs v := by
  constructor
  · rintro ⟨⟨i, j, h0, hv, hlen⟩, hp⟩
    exact ⟨i, j, h0, valueAt_rfc_strict bs i v j hv hp, hlen⟩
  · intro h
    obtain ⟨i, j, h0, hv, hlen⟩ := h
    obtain ⟨hrfc, hpol⟩ := valueAt_strict_rfc bs i v j hv
    exact ⟨⟨i, j, h0, hrfc, hlen⟩, hpol⟩

/-- `Utf8Char` consumes at least one byte. -/
theorem utf8_rest_lt {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    rest.length < b.length := by
  cases h <;> simp [ByteString.length_cons, ByteString.length_empty, ByteString.size_cons] <;> omega

/-- A string character consumes at least one byte. -/
theorem strChar_rest_lt {m : Strictness} {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar m b c rest) : rest.length < b.length := by
  cases h with
  | unescaped h _ _ _ _ => exact utf8_rest_lt h
  | short _ => simp [ByteString.length_cons, ByteString.size_cons] <;> omega
  | escU _ _ _ => simp [ByteString.length_cons, ByteString.size_cons] <;> omega
  | escPair _ _ _ _ _ _ => simp [ByteString.length_cons, ByteString.size_cons] <;> omega
  | escLone _ _ _ => simp [ByteString.length_cons, ByteString.size_cons] <;> omega

/-- A string body consumes at least its characters' bytes. -/
theorem strChars_suffix_lt {m : Strictness} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars m b cs rest) : rest.length < b.length := by
  induction h with
  | nil => simp [ByteString.length_cons, ByteString.size_cons]
  | cons hch _ ih =>
      have h1 := strChar_rest_lt hch
      omega

/-- `Utf8Char` consumes a prefix. -/
theorem utf8_split {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    ∃ pre, b = pre ++ rest := by
  cases h with
  | @one b rest _ =>
      exact ⟨b +: empty, by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @two b0 b1 rest _ _ _ _ =>
      exact ⟨b0 +: b1 +: empty, by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @three₀ b1 b2 rest _ _ _ _ =>
      exact ⟨0xE0 +: b1 +: b2 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @three₁ b0 b1 b2 rest _ _ _ _ _ _ =>
      exact ⟨b0 +: b1 +: b2 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @three₂ b1 b2 rest _ _ _ _ =>
      exact ⟨0xED +: b1 +: b2 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @three₃ b0 b1 b2 rest _ _ _ _ _ _ =>
      exact ⟨b0 +: b1 +: b2 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @four₀ b1 b2 b3 rest _ _ _ _ _ _ =>
      exact ⟨0xF0 +: b1 +: b2 +: b3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @four₁ b0 b1 b2 b3 rest _ _ _ _ _ _ _ _ =>
      exact ⟨b0 +: b1 +: b2 +: b3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @four₂ b1 b2 b3 rest _ _ _ _ _ _ =>
      exact ⟨0xF4 +: b1 +: b2 +: b3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩

/-- A string character consumes a prefix. -/
theorem strChar_split {m : Strictness} {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar m b c rest) : ∃ pre, b = pre ++ rest := by
  cases h with
  | @unescaped b c rest h8 _ _ _ _ => exact utf8_split h8
  | @short e c rest _ =>
      exact ⟨0x5C +: e +: empty, by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @escU h0 h1 h2 h3 c rest _ _ _ =>
      exact ⟨0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @escPair h0 h1 h2 h3 l0 l1 l2 l3 hi lo c rest _ _ _ _ _ _ =>
      exact ⟨0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
         l0 +: l1 +: l2 +: l3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | @escLone h0 h1 h2 h3 c rest _ _ _ =>
      exact ⟨0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: empty,
        by simp [ByteString.cons_append, ByteString.empty_append]⟩

/-- A string body consumes a prefix, so the remainder it leaves is a suffix. -/
theorem strChars_split {m : Strictness} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars m b cs rest) : ∃ pre, b = pre ++ rest := by
  induction h with
  | nil =>
      exact ⟨0x22 +: empty, by simp [ByteString.cons_append, ByteString.empty_append]⟩
  | cons hch _ ih =>
      obtain ⟨pre1, hp1⟩ := strChar_split hch
      obtain ⟨pre2, hp2⟩ := ih
      exact ⟨pre1 ++ pre2, by rw [hp1, hp2, ByteString.append_assoc]⟩


/-- Dropping the last `after.length` bytes of a split list gives `after`. -/
theorem drop_of_split {l pre after : Bytes} (h : l = pre ++ after) :
    l.drop (l.length - after.length) = after := by
  rw [h, ByteString.length_append, Nat.add_sub_cancel, ByteString.drop_left]

/-- The remainder a scanned body leaves is no longer than the body: the fact
`parseKey`'s `consumed` field needs. -/
theorem scalar_suffix_le (b : Bytes) (cs : List Nat) (after : Bytes)
    (h : scanChars b = .ok (cs, after)) : after.length ≤ b.length := by
  have hs := scanChars_iff b cs after |>.mp h
  have := strChars_suffix_lt hs
  omega

/-- A number lexeme is non-empty, so a parsed number consumes at least one byte. -/
theorem rfcNumber_nonempty {lex : Bytes} (h : RfcNumber lex) : 0 < lex.length := by
  cases h with
  | pos hb =>
      cases hb with
      | plain hi => cases hi <;> simp [ByteString.length_cons, ByteString.size_cons] <;> omega
      | frac hi _ =>
          cases hi <;> simp [ByteString.length_cons, ByteString.size_cons] <;> omega
      | exp hi _ =>
          cases hi <;> simp [ByteString.length_cons, ByteString.size_cons] <;> omega
      | fracExp hi _ _ =>
          cases hi <;> simp [ByteString.length_cons, ByteString.size_cons] <;> omega
  | neg _ => simp [ByteString.length_cons, ByteString.size_cons]

theorem numLexB_nonempty (lex : Bytes) (h : numLexB lex = true) : 0 < lex.length :=
  rfcNumber_nonempty (numLexB_iff lex |>.mp h)

theorem numRun_length_le (b : Bytes) : (numRun b).length ≤ b.length := by
  refine ByteString.induction_on
    (C := fun b => (numRun b).length ≤ b.length) b ?_ ?_
  · rw [numRun_empty, ByteString.length_empty]
    exact Nat.zero_le _
  · intro c rest ih
    rw [numRun_cons]
    split
    · rw [ByteString.length_cons, ByteString.length_cons]
      omega
    · rw [ByteString.length_empty]
      exact Nat.zero_le _

/-- The run from a position stays inside the bytes from that position on: the
fact a number token's stop needs. -/
theorem numRunFrom_length_le (bs : Bytes) (i : Nat) :
    (numRunFrom bs i).length ≤ bs.length - i := by
  rw [numRunFrom_eq, ← ByteString.length_drop]
  exact numRun_length_le (bs.drop i)

/-- `numRun b` is the longest constituent prefix: it is a prefix of `b`, and the
byte where it stops is not a constituent. -/
theorem numRun_spec (b : Bytes) :
    b.take (numRun b).length = numRun b ∧
      ∀ (c : UInt8) (rest : Bytes), b.drop (numRun b).length = c +: rest →
        NumConstituent c = false := by
  refine ByteString.induction_on
    (C := fun b => b.take (numRun b).length = numRun b ∧
      ∀ (c : UInt8) (rest : Bytes), b.drop (numRun b).length = c +: rest →
        NumConstituent c = false) b ?_ ?_
  · rw [numRun_empty, ByteString.length_empty, ByteString.take_zero]
    refine ⟨rfl, ?_⟩
    intro c rest hd
    rw [ByteString.drop_zero] at hd
    exact absurd hd.symm (ByteString.cons_ne_empty c rest)
  · intro a rest ih
    obtain ⟨ih1, ih2⟩ := ih
    rw [numRun_cons]
    split
    · rename_i hc
      refine ⟨?_, ?_⟩
      · rw [ByteString.length_cons, ByteString.take_succ_cons, ih1]
      · intro c tail hd
        rw [ByteString.length_cons, ByteString.drop_succ_cons] at hd
        exact ih2 c tail hd
    · rename_i hc
      refine ⟨?_, ?_⟩
      · rw [ByteString.length_empty, ByteString.take_zero]
      · intro c tail hd
        rw [ByteString.length_empty, ByteString.drop_zero] at hd
        obtain ⟨h1, _⟩ := ByteString.cons_inj.mp hd.symm
        subst h1
        cases hv : NumConstituent c <;> simp_all

/-! ### Whitespace arithmetic

The parser's measure is `bs.length - i`, so it needs `skipFrom` to be at least its
index and at most the input's length. -/

theorem spaceRun_le_length (bs : Bytes) : spaceRun bs ≤ bs.length := by
  refine ByteString.induction_on
    (C := fun bs => spaceRun bs ≤ bs.length) bs ?_ ?_
  · rw [spaceRun_empty, ByteString.length_empty]
    exact Nat.zero_le _
  · intro b rest ih
    rw [spaceRun_cons]
    split
    · rw [ByteString.length_cons]
      omega
    · exact Nat.zero_le _

theorem skipFrom_ge (bs : Bytes) (i : Nat) : i ≤ skipFrom bs i := by
  rw [skipFrom_def]
  omega

/-- In range, the skip stays inside the input.  The `i ≤ bs.length` hypothesis is
not decoration: `skipFrom bs i = i` once `i` is past the end, and that exceeds
`bs.length`. -/
theorem skipFrom_le_length (bs : Bytes) (i : Nat) (h : i ≤ bs.length) :
    skipFrom bs i ≤ bs.length := by
  rw [skipFrom_def]
  have hs := spaceRun_le_length (bs.drop i)
  have hd : (bs.drop i).length = bs.length - i := ByteString.length_drop bs i
  omega

/-- Every byte of the leading whitespace run is whitespace. -/
theorem spaceRun_all (bs : Bytes) (k : Nat) (b : UInt8)
    (hk : k < spaceRun bs) (hget : bs[k]? = some b) : IsSpaceB b = true := by
  revert k b
  refine ByteString.induction_on
    (C := fun bs => ∀ (k : Nat) (b : UInt8), k < spaceRun bs → bs[k]? = some b →
      IsSpaceB b = true) bs ?_ ?_
  · intro k b hk _
    rw [spaceRun_empty] at hk
    omega
  · intro a rest ih k b hk hget
    rw [spaceRun_cons] at hk
    split at hk
    · rename_i ha
      cases k with
      | zero =>
          rw [ByteString.getElem?_cons_zero] at hget
          injection hget with hb
          subst hb
          exact ha
      | succ k =>
          rw [ByteString.getElem?_cons_succ] at hget
          exact ih k b (by omega) hget
    · omega

/-- The leading whitespace run is a `ws` range: the empty range when the input
starts with a non-whitespace byte. -/
theorem spaceRun_space (bs : Bytes) : SpaceAt bs 0 (spaceRun bs) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro k b _ hk hget
  exact spaceRun_all bs k b hk hget

/-- A whitespace range in a dropped list is the same range in the whole list,
shifted by the drop. -/
theorem spaceAt_drop {bs : Bytes} {i j : Nat} (h : SpaceAt (bs.drop i) 0 j) :
    SpaceAt bs i (i + j) := by
  obtain ⟨_, hall⟩ := h
  refine ⟨by omega, ?_⟩
  intro k b hi hk hget
  have hbase : i + (k - i) = k := Nat.add_sub_of_le hi
  have hget' : (bs.drop i)[k - i]? = some b := by
    rw [ByteString.getElem?_drop, hbase]
    exact hget
  have hlt : k - i < j := by
    rw [← hbase] at hk
    exact Nat.lt_of_add_lt_add_left hk
  show IsSpaceB b = true
  exact hall (k - i) b (Nat.zero_le _) hlt hget'

/-- The skipped range is whitespace: what a separator's `ws` run needs. -/
theorem skipFrom_space (bs : Bytes) (i : Nat) : SpaceAt bs i (skipFrom bs i) := by
  rw [skipFrom_def]
  exact spaceAt_drop (spaceRun_space (bs.drop i))

/-- A checked prefix has room in the input: the fact a span's stop needs. -/
theorem hasPrefix_le {bs : Bytes} {i : Nat} {p : Bytes} (h : HasPrefix bs i p)
    (hne : 0 < p.length) : i + p.length ≤ bs.length := by
  unfold HasPrefix at h
  have h1 : ((bs.drop i).take p.length).length = p.length := by rw [h]
  rw [ByteString.length_take, ByteString.length_drop] at h1
  omega

end LeanLLVM.JSON
