/-
JS1's parser half: the eleven spellings the stage-1 closure admits, and the
thirteen neighbouring spellings it refuses by name.

This file imports `LeanLLVM` only — not `LeanLLVM.Vellum.JsonS1MasksIR` — so it
elaborates against the parser that exists today.  That is what makes it a live
observation: the admitted controls are the forms the emission uses — plus the
vector `shl` that is the widening's other direction, exercised here as an
accepted control and not emitted by this body — and, before those rules landed,
five of the eleven accepted controls failed at their own assertion instead of the
file stopping at an unresolved import.  The six that passed then were not
evidence: five of them were accepted by a `call` path that validates no intrinsic
spelling, and `icmp ult` is genuinely modelled.  All eleven pass now.

The admitted set, one text each: `shufflevector` with a defined mask; a vector
`store`; a non-mask vector `bitcast` at equal total bit width; the two-argument
`@llvm.x86.avx2.pshuf.b`; `@llvm.x86.pclmulqdq` at `i8 0`; `@llvm.x86.bmi.pext.64`
and `.pdep.64`; `@llvm.ctlz.i64` with `i1 false`; `lshr` and `shl` on
`<16 x i16>`; and the already-modelled `icmp ult` on a vector.

The refused set, one text each: `shufflevector` with a mask entry at `2n`; the
same with an `undef` entry; a vector `store` whose total width is not a whole
number of bytes; a `bitcast` whose total widths disagree — not one that changes
element size, which is the admitted `<4 x i64>` → `<32 x i8>`; a `bitcast` to a
vector of non-integer elements; `pshuf.b` with three arguments; `pclmulqdq` at
`i8 1`; `pext.32`; `pdep.32`; `ctlz` with `i1 true`; `umin`; `umax`; and a
vector `ashr`.

Every observation is a `#guard`, so a failed one stops elaboration with a
nonzero exit status; no compiler, proof checker, service, clock or network is
reached.  Elaborated by
`nix develop -c lake env lean tests/json-s1-parser.lean`.
-/
import LeanLLVM

namespace JsonS1ParserScenario

open LeanLLVM

/-! ### Reading one answer -/

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

/-! ### The eleven admitted spellings -/

/-- `shufflevector` with a defined mask: the SLP vectorizer's merge of two
`<4 x i64>` operands into an `<8 x i64>` permutation, the result shape the
emission has. -/
def okShuffle : String :=
"define i32 @ok_shuffle(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  ret i32 0
}
"

/-- A vector `store`: the packed mask's store. -/
def okStoreMask : String :=
"define i32 @ok_store_mask(ptr %p) {
entry:
  %v = load <64 x i8>, ptr %p
  %c = icmp eq <64 x i8> %v, splat (i8 34)
  store <64 x i1> %c, ptr %p
  ret i32 0
}
"

/-- A non-mask vector `bitcast` at equal total width, changing element size. -/
def okBitcast : String :=
"define i32 @ok_bitcast(ptr %p) {
entry:
  %v = load <4 x i64>, ptr %p
  %r = bitcast <4 x i64> %v to <32 x i8>
  ret i32 0
}
"

/-- The two-argument `pshuf.b`, the declaration's own arity. -/
def okPshufb : String :=
"define i32 @ok_pshufb(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %a, <32 x i8> %a)
  ret i32 0
}
"

/-- `pclmulqdq` at immediate 0. -/
def okClmul : String :=
"define i32 @ok_clmul(ptr %p) {
entry:
  %a = load <2 x i64>, ptr %p
  %r = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %a, <2 x i64> %a, i8 0)
  ret i32 0
}
"

/-- `pext` at 64 bits. -/
def okPext : String :=
"define i32 @ok_pext(ptr %p) {
entry:
  %a = load i64, ptr %p
  %r = call i64 @llvm.x86.bmi.pext.64(i64 %a, i64 %a)
  ret i32 0
}
"

/-- `pdep` at 64 bits. -/
def okPdep : String :=
"define i32 @ok_pdep(ptr %p) {
entry:
  %a = load i64, ptr %p
  %r = call i64 @llvm.x86.bmi.pdep.64(i64 %a, i64 %a)
  ret i32 0
}
"

/-- `ctlz` with the non-poison flag. -/
def okCtlz : String :=
"define i32 @ok_ctlz(ptr %p) {
entry:
  %a = load i64, ptr %p
  %r = call i64 @llvm.ctlz.i64(i64 %a, i1 false)
  ret i32 0
}
"

/-- A vector `lshr` at lane width 16. -/
def okLshr : String :=
"define i32 @ok_lshr(ptr %p) {
entry:
  %a = load <16 x i16>, ptr %p
  %r = lshr <16 x i16> %a, splat (i16 4)
  ret i32 0
}
"

/-- A vector `shl` at lane width 16. -/
def okShl : String :=
"define i32 @ok_shl(ptr %p) {
entry:
  %a = load <16 x i16>, ptr %p
  %r = shl <16 x i16> %a, splat (i16 4)
  ret i32 0
}
"

/-- The already-modelled vector `icmp ult`, which the emission uses for the
control test. -/
def okIcmpUlt : String :=
"define i32 @ok_icmp_ult(ptr %p) {
entry:
  %a = load <64 x i8>, ptr %p
  %r = icmp ult <64 x i8> %a, splat (i8 32)
  ret i32 0
}
"

#guard accepted okShuffle
#guard accepted okStoreMask
#guard accepted okBitcast
#guard accepted okPshufb
#guard accepted okClmul
#guard accepted okPext
#guard accepted okPdep
#guard accepted okCtlz
#guard accepted okLshr
#guard accepted okShl
#guard accepted okIcmpUlt

/-! ### The thirteen refused neighbours -/

/-- A `shufflevector` mask entry at `2n`: `i32 8` at `<4 x i64>`. -/
def badShuffleIndex : String :=
"define i32 @bad_shuffle_index(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 5, i32 6, i32 7>
  ret i32 0
}
"

/-- A `shufflevector` mask with an `undef` entry. -/
def badShuffleUndef : String :=
"define i32 @bad_shuffle_undef(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 undef, i32 3, i32 4, i32 5, i32 6, i32 7>
  ret i32 0
}
"

/-- A vector `store` whose total width is not a whole number of bytes. -/
def badStoreWidth : String :=
"define i32 @bad_store_width(ptr %p) {
entry:
  %v = load <5 x i8>, ptr %p
  %c = icmp eq <5 x i8> %v, splat (i8 34)
  store <5 x i1> %c, ptr %p
  ret i32 0
}
"

/-- A `bitcast` whose total widths disagree: 256 bits to 128. -/
def badBitcastWidth : String :=
"define i32 @bad_bitcast_width(ptr %p) {
entry:
  %v = load <4 x i64>, ptr %p
  %r = bitcast <4 x i64> %v to <16 x i8>
  ret i32 0
}
"

/-- A `bitcast` to a vector of non-integer elements. -/
def badBitcastElem : String :=
"define i32 @bad_bitcast_elem(ptr %p) {
entry:
  %v = load <4 x i64>, ptr %p
  %r = bitcast <4 x i64> %v to <8 x ptr>
  ret i32 0
}
"

/-- `pshuf.b` with three arguments. -/
def badPshufbArity : String :=
"define i32 @bad_pshufb_arity(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %a, <32 x i8> %a, <32 x i8> %a)
  ret i32 0
}
"

/-- `pclmulqdq` at immediate 1. -/
def badClmulImm : String :=
"define i32 @bad_clmul_imm(ptr %p) {
entry:
  %a = load <2 x i64>, ptr %p
  %r = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %a, <2 x i64> %a, i8 1)
  ret i32 0
}
"

/-- `pext` at 32 bits. -/
def badPext32 : String :=
"define i32 @bad_pext32(ptr %p) {
entry:
  %a = load i32, ptr %p
  %r = call i32 @llvm.x86.bmi.pext.32(i32 %a, i32 %a)
  ret i32 0
}
"

/-- `pdep` at 32 bits. -/
def badPdep32 : String :=
"define i32 @bad_pdep32(ptr %p) {
entry:
  %a = load i32, ptr %p
  %r = call i32 @llvm.x86.bmi.pdep.32(i32 %a, i32 %a)
  ret i32 0
}
"

/-- `ctlz` with the poison flag. -/
def badCtlzPoison : String :=
"define i32 @bad_ctlz_poison(ptr %p) {
entry:
  %a = load i64, ptr %p
  %r = call i64 @llvm.ctlz.i64(i64 %a, i1 true)
  ret i32 0
}
"

/-- `umin`, which the emission does not contain. -/
def badUmin : String :=
"define i32 @bad_umin(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = umin <32 x i8> %a, %a
  ret i32 0
}
"

/-- `umax`, the sibling the emission also does not contain. -/
def badUmax : String :=
"define i32 @bad_umax(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = umax <32 x i8> %a, %a
  ret i32 0
}
"

/-- A vector `ashr`, the signed shift the widening does not admit. -/
def badAshr : String :=
"define i32 @bad_ashr(ptr %p) {
entry:
  %a = load <16 x i16>, ptr %p
  %r = ashr <16 x i16> %a, splat (i16 4)
  ret i32 0
}
"

#guard refused badShuffleIndex
#guard refusalNames badShuffleIndex "shufflevector"
#guard refused badShuffleUndef
#guard refusalNames badShuffleUndef "shufflevector"
#guard refused badStoreWidth
#guard refusalNames badStoreWidth "store"
#guard refused badBitcastWidth
#guard refusalNames badBitcastWidth "bitcast"
#guard refused badBitcastElem
-- A refusal names what it refused: here it is the element type, refused at
-- `Parser.lean:218`, and the type refusal names the type token.
#guard refusalNames badBitcastElem "bitcast" || refusalNames badBitcastElem "ptr"
#guard refused badPshufbArity
#guard refusalNames badPshufbArity "pshuf.b"
#guard refused badClmulImm
#guard refusalNames badClmulImm "pclmulqdq"
#guard refused badPext32
#guard refusalNames badPext32 "pext"
#guard refused badPdep32
#guard refusalNames badPdep32 "pdep"
#guard refused badCtlzPoison
#guard refusalNames badCtlzPoison "ctlz"
#guard refused badUmin
#guard refusalNames badUmin "umin"
#guard refused badUmax
#guard refusalNames badUmax "umax"
#guard refused badAshr
#guard refusalNames badAshr "ashr"

end JsonS1ParserScenario
