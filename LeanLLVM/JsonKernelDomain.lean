/-
The JSON kernel's certified domain: the document-side predicate a caller checks
before it hands a document to the native pipeline, and the three outcomes the
route distinguishes.

The native pipeline is certified against `pipelineSpecPre`
(`LeanLLVM/Refinement/JsonPipelineSpec.lean`), whose document clauses are a
non-empty input inside `Limits.default.maxInput`, no nesting deeper than
`Limits.default.maxDepth`, no token exhaustion, and — as the wrapper's own
stricter requirement — no character-policy refusal.  The pipeline's ABI carries
no depth limit (its stage-2 walk pushes 520 frames) and no character-policy
slot (its verdict is the RFC 8259 one), so a document outside those clauses
must not reach it: the route reports it as outside the certified domain and
answers it with the scalar parser.

`admission` is that decision, and it is a *boundary*, not a wall.  Each clause
is one checker:

* `0 < doc.size` and `doc.size ≤ kernelMaxInput` — arithmetic;
* `openersTotal` counts the `{`/`[` bytes in the document.  The parser consumes
  one opener per container it descends through, so a document it refuses with
  `depthExceeded` holds at least `kernelMaxDepth + 1` of them; counting openers
  is a sound over-approximation of the nesting bound (it is wider than the
  bound, and the certificate in `LeanLLVM/JsonKernelCertificate.lean` says so);
* `policyRefusal` scans the document's quotes and runs the reference's own body
  scanner at each, reporting the reference's reason and byte.  It looks at
  every quote, not only the ones a well-formed document would open, because a
  policy refusal must never be missed — a false positive only narrows the
  domain, and the scalar parser still answers it;
* the pointer-arithmetic widths the units need are consequences of the input
  bound and are discharged in the certificate, not decided here.

The clauses are separate functions and separate certificate theorems.  Widening
the domain later — including to a total fast path — means removing a clause
from `admission` and dropping its certificate, not renegotiating the interface:
the fallback arm is what makes the API total today, and it is expected to
shrink as checkers are proved.
-/
import LeanLLVM.JSON.Scan

namespace LeanLLVM.Refinement

open LeanLLVM.JSON

/-- The input bound the certificate's depth and length clauses are stated at.
It is `Limits.default.maxInput`, restated here because this module is the
domain's own statement and does not import the parser's limit structure. -/
def kernelMaxInput : Nat := 1048576

/-- The reference parser's nesting bound (`Limits.default.maxDepth`). -/
def kernelMaxDepth : Nat := 128

/-- Why a document is outside the certified domain.  Every reason names the
clause that failed; the fallback's answer is the reference parser's, and the
outcome is reported as a fallback rather than as a certified refusal. -/
inductive KernelRefusal where
  /-- The empty document is outside every record's domain. -/
  | emptyInput
  /-- The document is longer than the record's input bound. -/
  | inputTooLong (bound : Nat)
  /-- The document holds more opener bytes than the nesting bound admits. -/
  | depthBound (openers : Nat)
  /-- The reference refuses an unpaired surrogate escape at this byte. -/
  | unpairedSurrogate (pos : Nat)
  /-- The reference refuses a noncharacter at this byte. -/
  | noncharacter (pos : Nat)
deriving DecidableEq, Repr

/-- The reason a caller sees for an out-of-domain document. -/
def KernelRefusal.message : KernelRefusal → String
  | .emptyInput =>
      "outside the kernel's domain: the empty document"
  | .inputTooLong bound =>
      s!"outside the kernel's domain: the document is longer than {bound} bytes"
  | .depthBound openers =>
      s!"outside the kernel's domain: {openers} opener bytes exceed the {kernelMaxDepth} the reference admits"
  | .unpairedSurrogate pos =>
      s!"outside the kernel's domain: the reference refuses an unpaired surrogate at byte {pos}"
  | .noncharacter pos =>
      s!"outside the kernel's domain: the reference refuses a noncharacter at byte {pos}"

/-- An opener byte: `{` or `[`.  It over-approximates the parser's structural
descent: bytes inside a string literal are counted too, which can only narrow
the domain. -/
def openerB (b : UInt8) : Bool := b = 0x5B || b = 0x7B

/-- The document's opener bytes. -/
def openersTotal (doc : ByteArray) : Nat :=
  (doc.data.toList).countP openerB

/-- The character-policy check at one byte: if it is a quote, the reference's
own body scanner runs on the body and its policy refusal is reported at the
byte the reference names.  The scan is the reference's (`scanCharsEnd`), so the
reason and position are the reference's, not a second implementation's. -/
def policyRefusalAt (doc : ByteArray) (i : Nat) : Option KernelRefusal :=
  if doc[i]? = some 0x22 then
    match scanCharsEnd doc (i + 1) 0 with
    | .error (.unpairedSurrogate off) => some (.unpairedSurrogate (i + 1 + off))
    | .error (.noncharacter off) => some (.noncharacter (i + 1 + off))
    | _ => none
  else none

/-- The document's first character-policy refusal, at the byte the reference
names. -/
def policyRefusal (doc : ByteArray) : Option KernelRefusal :=
  (List.range doc.size).findSome? (policyRefusalAt doc)

/-- Whether the document carries a quote whose body the reference refuses under
its character policy. -/
def policyScan (doc : ByteArray) : Bool :=
  (policyRefusal doc).isSome

/-- The certified domain's decision procedure.  `ok` admits the document to the
native pipeline; `error` names the clause that kept it out.  The reason order is
the one the route reports: empty, over-long, too many openers, then the
character policy. -/
def admission (doc : ByteArray) : Except KernelRefusal Unit :=
  if doc.size = 0 then .error .emptyInput
  else if kernelMaxInput < doc.size then .error (.inputTooLong kernelMaxInput)
  else if kernelMaxDepth < openersTotal doc then .error (.depthBound (openersTotal doc))
  else
    match policyRefusal doc with
    | some r => .error r
    | none => .ok ()

/-- `admission`'s yes-or-no projection, for a caller that has no room for the
reason. -/
def admitted (doc : ByteArray) : Bool := (admission doc).isOk

/-! ### The buffers the wrapper constructs from the input length

None of these is an admission clause: the record's staging pre is discharged by
construction from `doc.size`.  `kernelEpCap` is the entry stream's capacity
(`64` entries per block plus the emitter's nine-entry reserve), `kernelXpCap`
the escape list's, `kernelDstCap` the arena's (`n + 64` for the expander's
decoding slack) and `kernelEvCap` the event stream's (`13` bytes per input
byte at the encoding's worst case).  They are here so the probe and the library
size the same buffers from the same numbers. -/

/-- The document's 64-byte blocks. -/
def kernelBlocks (n : Nat) : Nat := (n + 63) / 64

/-- The entry stream's capacity, in words. -/
def kernelEpCap (n : Nat) : Nat := 64 * kernelBlocks n + 9

/-- The escape list's capacity, in words. -/
def kernelXpCap (n : Nat) : Nat := 64 * kernelBlocks n + 8

/-- The arena's capacity, in bytes. -/
def kernelDstCap (n : Nat) : Nat := n + 64

/-- The event stream's capacity, in bytes. -/
def kernelEvCap (n : Nat) : Nat := 13 * n + 128

/-- The staged document window's base: three bytes of prefix room and the
32-byte read-past tail.  The probe stages the window at address 0, so the
document's base is this. -/
def kernelBase : Nat := 3

end LeanLLVM.Refinement
