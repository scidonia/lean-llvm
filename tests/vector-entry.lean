/-
JE1's parser half: the six spellings the entry closure admits, and the nine
neighbouring spellings it refuses by name.

This file imports `LeanLLVM` only — not `LeanLLVM.Vellum.JsonEntryIR` — so it
elaborates against the parser that exists today, and an admitted control fails
at its own assertion rather than the file stopping at an unresolved import.

The admitted set, one text each: `@llvm.ctpop.i32` and `@llvm.ctpop.i64`; the
`@llvm.cttz.i64` poison flag at both `i1 true` and `i1 false`; a vector `store`
at integer lanes (`<8 x i32>`, the entry emitter's store); and the already
modelled `phi` as a control, so a failure elsewhere is not a failure of the
harness.

The refused set, one text each: `ctpop.i16` and `cttz.i32`, at a width that is
not the symbol's; a two-argument `ctpop.i32`; `cttz` with no flag; `cttz` with
`i64 0` where the flag belongs; `ctlz.i64` with `i1 true`; a vector `store`
whose total width is not a whole number of bytes; a `store` of `<8 x i32>` where
the value is an `i64`; and a `store` of `<8 x i64>` where the value is an
`<8 x i32>`.

Every observation is a `#guard`, so a failed one stops elaboration with a
nonzero exit status; no compiler, proof checker, service, clock or network is
reached.  Elaborated by
`nix develop -c lake env lean tests/vector-entry.lean`.
-/
import LeanLLVM

namespace JsonEntryVectorScenario

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

/-! ### The six admitted spellings -/

/-- `ctpop` at 32 bits: the seven count sites a block's eight group bytes need. -/
def okCtpop32 : String :=
"define i32 @ok_ctpop32(ptr %p) {
entry:
  %x = load i32, ptr %p
  %r = tail call i32 @llvm.ctpop.i32(i32 %x)
  ret i32 %r
}
"

/-- `ctpop` at 64 bits: the block's own population count. -/
def okCtpop64 : String :=
"define i64 @ok_ctpop64(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.ctpop.i64(i64 %x)
  ret i64 %r
}
"

/-- `cttz` with the poison flag, every observed site's spelling. -/
def okCttzTrue : String :=
"define i64 @ok_cttz_true(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.cttz.i64(i64 %x, i1 true)
  ret i64 %r
}
"

/-- The same `cttz` at the non-poison flag, admitted at both values. -/
def okCttzFalse : String :=
"define i64 @ok_cttz_false(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.cttz.i64(i64 %x, i1 false)
  ret i64 %r
}
"

/-- A vector `store` at integer lanes: POS8's row store. -/
def okStoreVec : String :=
"define i32 @ok_store_vec(ptr %p) {
entry:
  %v = load <8 x i32>, ptr %p
  store <8 x i32> %v, ptr %p
  ret i32 0
}
"

/-- The already-modelled control: a `phi` with two literal incomings. -/
def okPhi : String :=
"define i64 @ok_phi(ptr %p) {
entry:
  %d = phi i64 [ 0, %a ], [ 1, %b ]
  ret i64 %d
}
"

#guard accepted okCtpop32
#guard accepted okCtpop64
#guard accepted okCttzTrue
#guard accepted okCttzFalse
#guard accepted okStoreVec
#guard accepted okPhi

/-! ### The nine refused neighbours -/

/-- `ctpop.i16`: a width the symbol does not carry. -/
def badCtpop16 : String :=
"define i16 @bad_ctpop16(ptr %p) {
entry:
  %x = load i16, ptr %p
  %r = tail call i16 @llvm.ctpop.i16(i16 %x)
  ret i16 %r
}
"

/-- `cttz.i32`: the sibling width, likewise not the symbol's. -/
def badCttz32 : String :=
"define i32 @bad_cttz32(ptr %p) {
entry:
  %x = load i32, ptr %p
  %r = tail call i32 @llvm.cttz.i32(i32 %x, i1 false)
  ret i32 %r
}
"

/-- A two-argument `ctpop.i32`. -/
def badCtpopArity : String :=
"define i32 @bad_ctpop_arity(ptr %p) {
entry:
  %x = load i32, ptr %p
  %r = tail call i32 @llvm.ctpop.i32(i32 %x, i32 %x)
  ret i32 %r
}
"

/-- `cttz` with no flag operand. -/
def badCttzNoFlag : String :=
"define i64 @bad_cttz_no_flag(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.cttz.i64(i64 %x)
  ret i64 %r
}
"

/-- `cttz` with an `i64 0` where the `i1` flag belongs. -/
def badCttzFlagType : String :=
"define i64 @bad_cttz_flag_type(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.cttz.i64(i64 %x, i64 0)
  ret i64 %r
}
"

/-- `ctlz` with the poison flag: not observed, and no clause bounds its poison. -/
def badCtlzTrue : String :=
"define i64 @bad_ctlz_true(ptr %p) {
entry:
  %x = load i64, ptr %p
  %r = tail call i64 @llvm.ctlz.i64(i64 %x, i1 true)
  ret i64 %r
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

/-- A `store` of `<8 x i32>` whose value is an `i64`. -/
def badStoreScalarValue : String :=
"define i32 @bad_store_scalar_value(ptr %p) {
entry:
  %q = load i64, ptr %p
  store <8 x i32> %q, ptr %p
  ret i32 0
}
"

/-- A `store` whose written type is `<8 x i64>` and whose value is an
`<8 x i32>`: the total width is whole, the shapes disagree. -/
def badStoreShape : String :=
"define i32 @bad_store_shape(ptr %p) {
entry:
  %v = load <8 x i32>, ptr %p
  store <8 x i64> %v, ptr %p
  ret i32 0
}
"

#guard refused badCtpop16
#guard refusalNames badCtpop16 "ctpop"
#guard refused badCttz32
#guard refusalNames badCttz32 "cttz"
#guard refused badCtpopArity
#guard refusalNames badCtpopArity "ctpop"
#guard refused badCttzNoFlag
#guard refusalNames badCttzNoFlag "cttz"
#guard refused badCttzFlagType
#guard refusalNames badCttzFlagType "cttz"
#guard refused badCtlzTrue
#guard refusalNames badCtlzTrue "ctlz"
#guard refused badStoreWidth
#guard refusalNames badStoreWidth "store"
#guard refused badStoreScalarValue
#guard refusalNames badStoreScalarValue "store"
#guard refused badStoreShape
#guard refusalNames badStoreShape "store"

end JsonEntryVectorScenario
