/-
The UTF-8 stage's parser half: the four spellings the stage emits, and the six
neighbouring spellings it must refuse by name.

This file imports `LeanLLVM` only — not the emission module — so it elaborates
against the parser that exists today, and an admitted control fails at its own
assertion rather than the file stopping at an unresolved import.

The admitted set, one text each: the saturating vector subtract
`@llvm.usub.sat.v32i8` at `<32 x i8>`; the `@llvm.x86.avx.ptestz.256` test at
`<4 x i64>`; the already-modelled `@llvm.x86.avx2.pshuf.b` the same body calls,
as a control, so a failure elsewhere is not a failure of the harness; and a
`getelementptr i8, ptr %b, i64 %n` with no `inbounds`, the form the stage emits.

The refused set, one text each: `usub.sat` at `v16i8`; a one-argument
`usub.sat.v32i8`; `usub.sat.v32i8` with an `i32` second operand; the neighbour
spelling `@llvm.x86.avx.ptest.256`; `ptestz.128` at `<2 x i64>`; and
`ptestz.256` declared to return `i64`.

Every observation is a `#guard`, so a failed one stops elaboration with a
nonzero exit status; no compiler, proof checker, service, clock or network is
reached.  Elaborated by
`nix develop -c lake env lean tests/vector-utf8.lean`.
-/
import LeanLLVM

namespace VectorUtf8Scenario

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

/-! ### The four emitted spellings -/

/-- `usub.sat` at 32 lanes of `i8`: the stage's saturating subtract. -/
def okUsubSat : String :=
"define i32 @ok_usub_sat(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %b = load <32 x i8>, ptr %p
  %r = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %a, <32 x i8> %b)
  ret i32 0
}
"

/-- `ptestz.256` at `<4 x i64>`: the stage's zero test. -/
def okPtestz : String :=
"define i32 @ok_ptestz(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %b = load <4 x i64>, ptr %p
  %r = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %a, <4 x i64> %b)
  ret i32 %r
}
"

/-- The already-modelled control: `pshuf.b`, which the same body calls. -/
def okPshufB : String :=
"define i32 @ok_pshuf_b(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %b = load <32 x i8>, ptr %p
  %r = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %a, <32 x i8> %b)
  ret i32 0
}
"

/-- A `getelementptr` with no `inbounds`, the form the stage emits. -/
def okGep : String :=
"define i64 @ok_gep(ptr %b, i64 %n) {
entry:
  %g = getelementptr i8, ptr %b, i64 %n
  ret i64 0
}
"

#guard accepted okUsubSat
#guard accepted okPtestz
#guard accepted okPshufB
#guard accepted okGep

/-! ### The six refused neighbours -/

/-- `usub.sat` at `v16i8`: a lane count the symbol does not carry. -/
def badUsubLanes : String :=
"define i32 @bad_usub_lanes(ptr %p) {
entry:
  %a = load <16 x i8>, ptr %p
  %b = load <16 x i8>, ptr %p
  %r = tail call <16 x i8> @llvm.usub.sat.v16i8(<16 x i8> %a, <16 x i8> %b)
  ret i32 0
}
"

/-- A one-argument `usub.sat.v32i8`. -/
def badUsubArity : String :=
"define i32 @bad_usub_arity(ptr %p) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %a)
  ret i32 0
}
"

/-- `usub.sat.v32i8` with an `i32` second operand. -/
def badUsubOperand : String :=
"define i32 @bad_usub_operand(ptr %p, i32 %n) {
entry:
  %a = load <32 x i8>, ptr %p
  %r = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %a, i32 %n)
  ret i32 0
}
"

/-- The neighbour spelling `ptest.256`, not the `ptestz` the stage emits. -/
def badPtest : String :=
"define i32 @bad_ptest(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %b = load <4 x i64>, ptr %p
  %r = tail call i32 @llvm.x86.avx.ptest.256(<4 x i64> %a, <4 x i64> %b)
  ret i32 %r
}
"

/-- `ptestz.128`: the sibling width, not the symbol's. -/
def badPtestzWidth : String :=
"define i32 @bad_ptestz_width(ptr %p) {
entry:
  %a = load <2 x i64>, ptr %p
  %b = load <2 x i64>, ptr %p
  %r = tail call i32 @llvm.x86.avx.ptestz.128(<2 x i64> %a, <2 x i64> %b)
  ret i32 %r
}
"

/-- `ptestz.256` declared to return `i64`: the result type is `i32`. -/
def badPtestzResult : String :=
"define i64 @bad_ptestz_result(ptr %p) {
entry:
  %a = load <4 x i64>, ptr %p
  %b = load <4 x i64>, ptr %p
  %r = tail call i64 @llvm.x86.avx.ptestz.256(<4 x i64> %a, <4 x i64> %b)
  ret i64 %r
}
"

#guard refused badUsubLanes
#guard refusalNames badUsubLanes "llvm.usub.sat.v16i8"
#guard refused badUsubArity
#guard refusalNames badUsubArity "llvm.usub.sat.v32i8"
#guard refused badUsubOperand
#guard refusalNames badUsubOperand "llvm.usub.sat.v32i8"
#guard refused badPtest
#guard refusalNames badPtest "llvm.x86.avx.ptest.256"
#guard refused badPtestzWidth
#guard refusalNames badPtestzWidth "llvm.x86.avx.ptestz.128"
#guard refused badPtestzResult
#guard refusalNames badPtestzResult "llvm.x86.avx.ptestz.256"

end VectorUtf8Scenario
