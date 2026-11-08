/-
The JSON classifier scenarios: the emitted classifier text the parser must
accept, the vector constructs it must refuse while naming each one, the block
operation's full-block and short-block outcomes with the per-byte mask, the
classifier body's own run returning that same mask and leaving the caller's
memory alone, and the staging caller's run returning that mask under the
installed selection, the reference selection and a complementing body.

The classifier text is `probes/install/ir/json-classify.candidate.ll`, read here
through `include_str`, so the assertion is about the committed bytes.  The
refusal cases are eight function texts written in this file — six carrying one
unmodelled vector construct each, one a splat whose element type is not an
integer, and one a splat whose element width disagrees with the operand type's —
with five controls that must stay accepted (three scalar forms and two splats
whose type and width agree).  Every observation is a `#guard` over
`parseModule`, so each assertion is a closed decision about one parse; no
compiler, proof checker, service, clock or network is reached.

Elaborated by `nix develop -c lake env lean tests/json-classify.lean`.
-/
import LeanLLVM

namespace JsonClassifyScenario

open LeanLLVM

/-! ### JB1 — the emitted classifier fixture is what the parser must accept -/

/-- The classifier as emitted and committed. -/
def classifierSrc : String :=
  include_str "../probes/install/ir/json-classify.candidate.ll"

/-- The single function a parsed classifier text holds. -/
def soleFunction (m : Module) : Option Function :=
  match m.functions with
  | [f] => some f
  | _ => none

/-- The single block a function holds. -/
def soleBlock (f : Function) : Option Block :=
  match f.blocks with
  | [b] => some b
  | _ => none

/-- The classifier's only block, when the text parses to one function with one
block. -/
def classifierBlock (src : String) : Option Block :=
  match parseModule src with
  | .ok m => soleFunction m >>= soleBlock
  | .error _ => none

-- (1) One function and no declarations.
#guard
  match parseModule classifierSrc with
  | .ok m => m.functions.length = 1 ∧ m.decls = []
  | .error _ => false

-- (2) The function's name, return type and parameter list.
#guard
  match parseModule classifierSrc with
  | .ok m =>
      match soleFunction m with
      | some f =>
          f.name = "leanllvm_json_classify32" ∧
          f.retTy = Ty.int 32 ∧
          f.params = [("%arg", Ty.ptr)]
      | none => false
  | .error _ => false

-- (3) One block, named `bb`, returning the mask register.
#guard
  match classifierBlock classifierSrc with
  | some b =>
      b.name = "bb" ∧ b.term = Term.ret (Ty.int 32) (some (Operand.reg "%i23"))
  | none => false

-- (4) Twenty-four instructions.
#guard
  match classifierBlock classifierSrc with
  | some b => b.instrs.length = 24
  | none => false

/-! ### JB2 — unmodelled vector shapes are refused, and the refusal names the
construct

Each text is an otherwise well-formed function carrying one vector construct.  A
refusal is asserted on its own, and the message's naming of the construct on its
own, so a failure says which half failed. -/

/-- (1) A vector `bitcast` to a scalar integer. -/
def bitcastVec : String :=
"define i32 @bitcast_vec(ptr %p) {
entry:
  %r = bitcast <32 x i8> %v to i32
  ret i32 %r
}
"

/-- (2) A vector `store` whose total width is not a whole number of bytes: five
bits have no byte layout.  The refusal is the **width**, not the vector-ness —
`<32 x i8>` is admitted at 32 whole bytes — so this text is refused before and
after the widening alike. -/
def storeVec : String :=
"define i32 @store_vec(ptr %p) {
entry:
  store <5 x i1> %v, ptr %p
  ret i32 0
}
"

/-- (3) An `alloca` of a vector type. -/
def allocaVec : String :=
"define i32 @alloca_vec() {
entry:
  %p = alloca <32 x i8>
  ret i32 0
}
"

/-- (4) A vector `select`. -/
def selectVec : String :=
"define i32 @select_vec() {
entry:
  %s = select <32 x i1> %c, <32 x i8> %a, <32 x i8> %b
  ret i32 0
}
"

/-- (5) A vector `icmp` under the signed-less-than predicate. -/
def icmpSltVec : String :=
"define i32 @icmp_slt_vec() {
entry:
  %r = icmp slt <32 x i8> %a, %b
  ret i32 %r
}
"

/-- (6) A `splat` operand whose element is `zeroinitializer`. -/
def splatZero : String :=
"define i32 @splat_zero() {
entry:
  %i1 = icmp eq <32 x i8> %i, splat (i8 zeroinitializer)
  ret i32 0
}
"

/-- The refusal message `parseModule` produced, if it refused. -/
def refusal (src : String) : Option String :=
  match parseModule src with
  | .ok _ => none
  | .error e => some e

/-- The parser refused the text. -/
def refused (src : String) : Bool := (refusal src).isSome

/-- The parser's refusal names `needle`. -/
def refusalNames (src : String) (needle : String) : Bool :=
  match refusal src with
  | some e => e.contains needle
  | none => false

/-- The parser accepted the text. -/
def accepted (src : String) : Bool :=
  match parseModule src with
  | .ok _ => true
  | .error _ => false

-- (1) Refused, and the message names `bitcast` and a source or destination type.
#guard refused bitcastVec
#guard refusalNames bitcastVec "bitcast"
#guard refusalNames bitcastVec "<32 x i8>" || refusalNames bitcastVec "i32"

-- (2) Refused, and the message names `store`.
#guard refused storeVec
#guard refusalNames storeVec "store"

-- (3) Refused, and the message names `alloca`.
#guard refused allocaVec
#guard refusalNames allocaVec "alloca"

-- (4) Refused, and the message names `select`.
#guard refused selectVec
#guard refusalNames selectVec "select"

-- (5) Refused, and the message names the predicate `slt`.
#guard refused icmpSltVec
#guard refusalNames icmpSltVec "slt"

-- (6) Refused, and the message names `zeroinitializer`.
#guard refused splatZero
#guard refusalNames splatZero "zeroinitializer"

/-! #### The affirmative controls

The same detector accepts the scalar forms, so a refusal above is not the
detector rejecting everything. -/

/-- A scalar `store`. -/
def storeScalar : String :=
"define i32 @store_scalar(ptr %p) {
entry:
  store i32 %v, ptr %p
  ret i32 0
}
"

/-- A scalar `alloca`. -/
def allocaScalar : String :=
"define i32 @alloca_scalar() {
entry:
  %p = alloca i32
  ret i32 0
}
"

/-- A scalar `icmp slt`. -/
def icmpScalar : String :=
"define i32 @icmp_scalar() {
entry:
  %r = icmp slt i32 %a, %b
  ret i32 %r
}
"

#guard accepted storeScalar
#guard accepted allocaScalar
#guard accepted icmpScalar

/-! ### JB6 — a splat's element is refused at the type and width positions, and
each message names what it refused

A splat carries its lane width and value from the element token: a token that is
not an integer type has no width to take, and one whose width disagrees with the
operand type's would render as text whose element type contradicts its
instruction.  The parser refuses each position by name.

Refusal and naming are asserted separately for each text: the type text's
naming is on the refused type token (`ptr`), the width text's on the two width
tokens (`i32` and `i8`) rather than on the sentence, so rewording survives but a
collapsed message fails.  The affirmative controls are the same constructs at
matching type and width, accepted in the same run, so the refusals are not the
parser rejecting every `ptr` or every splat. -/

/-- A splat whose element type (`ptr`) is not an integer type. -/
def splatTypeMismatch : String :=
"define i32 @splat_type_mismatch() {
entry:
  %i1 = icmp eq <32 x i8> %i, splat (ptr null)
  ret i32 0
}
"

/-- A splat whose element width (`i32`) disagrees with the operand type's
element width (`i8`). -/
def splatWidthMismatch : String :=
"define i32 @splat_width_mismatch() {
entry:
  %i1 = icmp eq <32 x i8> %i, splat (i32 5)
  ret i32 0
}
"

/-- An integer splat whose element width matches the operand type's. -/
def splatTypeMatch : String :=
"define i32 @splat_type_match() {
entry:
  %i1 = icmp eq <32 x i8> %i, splat (i8 34)
  ret i32 0
}
"

/-- The same `i32` splat inside an operand type whose element width is `i32`. -/
def splatWidthMatch : String :=
"define i32 @splat_width_match() {
entry:
  %i1 = icmp eq <32 x i32> %i, splat (i32 5)
  ret i32 0
}
"

-- The type position is refused, and the message names the refused type.
#guard refused splatTypeMismatch
#guard refusalNames splatTypeMismatch "ptr"

-- The width position is refused, and the message names both widths.
#guard refused splatWidthMismatch
#guard refusalNames splatWidthMismatch "i32"
#guard refusalNames splatWidthMismatch "i8"

-- Both matching splats are accepted.
#guard accepted splatTypeMatch
#guard accepted splatWidthMatch

/-! ### JB3 — a full block is classified and advances the cursor, a short block
reports no information, and the mask is the scalar decision per byte

`scanBlock` receives the block and the number of bytes offered.  A full block
(`valid = 32`) is classified, advances the cursor by 32 and reports `ok`; a
block offered with `valid = 31` produces no information and leaves the cursor
where it was, reporting `short`.  The mixed block's mask is asserted against a
hand-written constant rather than read back through `maskOf`, so the assertion
is not a tautology; the block's bytes make bit 0 set and bit 31 clear, which a
reversed bit order cannot satisfy.

The `valid = 32` half is definitional — it is the branch `scanBlock`'s `if`
takes — and is stated for clarity rather than as evidence.  The load-bearing
assertions are the mask constant and the short-block outcome. -/

open LeanLLVM.JSON

/-- The cursor the block is offered at.  Not zero, so an advanced cursor is not
mistaken for the initial state. -/
def blockCursor : ScanState := { pos := 7 }

/-- The mixed block's 32 bytes: structural bytes, JSON whitespace and ordinary
content interleaved. -/
def mixedBytes : List UInt8 :=
  [ 0x5B, 0x20, 0x20, 0x31, 0x2C, 0x20, 0x32, 0x5D,
    0x0A, 0x20, 0x22, 0x61, 0x22, 0x20, 0x3A, 0x20,
    0x78, 0x2C, 0x20, 0x79, 0x09, 0x7A, 0x7B, 0x20,
    0x22, 0x5C, 0x6B, 0x22, 0x7D, 0x0D, 0x20, 0x71 ]

/-- The mixed block, indexed as `Block32` requires. -/
def mixedBlock : Block32 := fun i => mixedBytes.get ⟨i.val, i.isLt⟩

/-- The mask the scalar transition must produce for `mixedBlock`: bit `k` set
exactly where byte `k` is structural or JSON whitespace.  Written out rather
than read back through `maskOf`, and mixed in the bit-order-sensitive sense —
bit 0 is set (byte 0 is `[`) and bit 31 is clear (byte 31 is `q`). -/
def mixedMask : BitVec 32 := 0x7BD6F7B7

-- (1) A full block reports `ok`, and the cursor advances by 32.  This half is
-- definitional: `valid = 32` takes `scanBlock`'s first branch.
#guard (scanBlock blockCursor mixedBlock 32).2.2 = .ok
#guard (scanBlock blockCursor mixedBlock 32).1.pos = blockCursor.pos + 32

-- (2) The full block's mask is the hand-written constant, not `maskOf` read
-- back.
#guard (scanBlock blockCursor mixedBlock 32).2.1 = mixedMask

-- (3) A block offered with 31 valid bytes is `short`, leaves the cursor alone
-- and produces no information.
#guard (scanBlock blockCursor mixedBlock 31).2.2 = .short
#guard (scanBlock blockCursor mixedBlock 31).1.pos = blockCursor.pos
#guard (scanBlock blockCursor mixedBlock 31).2.1 = (0 : BlockInfo)

/-! ### JB4 — the staging caller returns the staged block's mask and memory
under both the reference selection and the installed classifier body, and a
complementing body is distinguishable

The same `mixedBytes` block is staged by the caller's four `i64` stores, so the
caller's outcome is asserted against the same hand-written constant `JB3` and
`JB5` use, together with the memory its stores staged.  The words are derived
from `mixedBytes` through the production `blockOf` encoding rather than
retyped, and the derivation is itself asserted, so a fixture that failed to
stage that block cannot make the mask assertion disagree with `JB3` silently.
A third selection — the complemented body — is run at the same caller: it must
return the complement, and its run must differ from the classifier's, so the
value clause is observed rather than assumed.  The caller's returned memory is
read back as the staged block, so the mask is bound to the bytes actually
written. -/

open LeanLLVM.Vellum.JsonSeam
open LeanLLVM.Vellum.JsonClassifyIR

/-- The little-endian `i64` word staging bytes `8 * j` through `8 * j + 7` of
`mixedBytes`: the bytes the caller's `j`-th store writes. -/
def mixedWord (j : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (bytesToNat ((mixedBytes.drop (8 * j)).take 8))

/-- The four words the caller is run on, in argument order. -/
def mixedArgs : List LeanLLVM.Value :=
  [.int 64 (mixedWord 0), .int 64 (mixedWord 1),
   .int 64 (mixedWord 2), .int 64 (mixedWord 3)]

/-- The caller's run under a selection, from `initState`. -/
def callerOutcome (calls : Calls) : Option Outcome :=
  runFuel calls 10000 scanCaller (initState scanCaller mixedArgs)

/-- The outcome the caller must produce: the hand-written mask and the memory
its four stores staged. -/
def stagedOutcome : Outcome :=
  .ret (some (.int 32 mixedMask))
    (stagedMem (mixedWord 0) (mixedWord 1) (mixedWord 2) (mixedWord 3))

/-- The memory the caller's run returned, when it returned. -/
def callerReturnedMem (calls : Calls) : Option Mem :=
  match callerOutcome calls with
  | some (.ret _ m) => some m
  | _ => none

/-- The installed classifier body's selection. -/
def candidateCalls : Calls :=
  envForBodySym jsonSeamSymbol 10000 0 classify32Function

/-- The complemented body's selection. -/
def wrongCalls : Calls :=
  envForBodySym jsonSeamSymbol 10000 0 wrongMaskFunction

-- (0) The four words stage `mixedBytes`, so the expected mask below is the mask
-- of the bytes the caller actually writes.
#guard blockOf (mixedWord 0) (mixedWord 1) (mixedWord 2) (mixedWord 3) = mixedBytes

-- (1) Under the installed classifier body's selection the caller's one outcome
-- is the hand-written mask with the staged memory.
#guard callerOutcome candidateCalls = some stagedOutcome

-- (2) The same value and memory hold under the reference selection — the two
-- selections agree at the caller.
#guard callerOutcome envForMask = some stagedOutcome

-- (3) Under the complemented body's selection the caller returns the
-- complement of the mask, with the same staged memory.
#guard callerOutcome wrongCalls = some
  (.ret (some (.int 32 (mixedMask ^^^ BitVec.ofInt 32 (-1))))
    (stagedMem (mixedWord 0) (mixedWord 1) (mixedWord 2) (mixedWord 3)))

-- (4) The complemented body's run differs from the classifier's.
#guard callerOutcome wrongCalls ≠ callerOutcome candidateCalls

-- (5) The caller's returned memory reads back exactly the block it staged at
-- address `1` (its first local), so the mask is bound to those bytes.
#guard (callerReturnedMem candidateCalls).bind (fun m => readBytes m 1 32) =
  some (blockOf (mixedWord 0) (mixedWord 1) (mixedWord 2) (mixedWord 3))

-- (6) The block's bytes are the committed fixture `--emit-block` writes, read
-- from disk.  A byte change that preserves the byte's mask class would leave
-- every mask assertion above green while the scenario and the fixture
-- described different blocks, so the bytes are compared directly.
#guard (include_str "json-classify/mixed.block").toList.map (·.toNat) =
  mixedBytes.map (·.toNat)

/-! ### JB5 — the classifier body, run from a memory holding the chosen block,
returns the hand-written mask and leaves the caller's memory alone

The same `mixedBytes` block `JB3` classifies through `scanBlock` is placed in
memory at a non-zero address, and `classify32Function` — the AST pinned from
`probes/install/ir/json-classify.candidate.ll` — is run over it under the
repository's semantics.  The returned `i32` is asserted against the same
hand-written `mixedMask`, so `JB3` and this section read together as
*body = hand value* and *`scanBlock` = hand value* rather than either one
reading its expectation back out of `maskOf`.  The returned memory is asserted
to read back the same 32 bytes, so the body is a pure read: a store, an alloca
or a clobbered address would show here. -/

open LeanLLVM.Vellum.JsonClassifyIR

/-- The address the block is placed at.  Non-zero, because `initState` reserves
address `0` for `null`, and not `mixedBlock`'s own size, so the read is not
anchored at the start of memory. -/
def blockBase : Nat := 4096

/-- Memory holding `mixedBytes` at `blockBase`, one cell per byte, laid out as
`readBytes` consumes it. -/
def blockMem : Mem :=
  List.ofFn fun i : Fin 32 =>
    (blockBase + i.val, mixedBytes.get ⟨i.val, i.isLt⟩)

/-- The body run from that memory, under the repository's semantics. -/
def classifyOutcome : Option Outcome :=
  runFuel noCalls 10000 classify32Function
    { (initState classify32Function [.ptr blockBase]) with mem := blockMem }

/-- The `i32` the run returned, when it returned one. -/
def classifyReturned : Option (BitVec 32) :=
  match classifyOutcome with
  | some (.ret (some (.int 32 v)) _) => some v
  | _ => none

/-- The memory the run returned, when it returned. -/
def classifyReturnedMem : Option Mem :=
  match classifyOutcome with
  | some (.ret _ m) => some m
  | _ => none

-- (1) The returned `i32` is the hand-written constant `JB3` uses for the same
-- block.
#guard classifyReturned = some mixedMask

-- (2) The returned memory reads back the same bytes, so the run neither wrote
-- nor displaced the caller's block.
#guard (classifyReturnedMem.bind fun m => readBytes m blockBase 32) =
  some mixedBytes

end JsonClassifyScenario
