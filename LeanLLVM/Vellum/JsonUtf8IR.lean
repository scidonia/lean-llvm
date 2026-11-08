/-
The UTF-8 stage's call environment.

The stage's emission calls three intrinsics and no others:
`llvm.x86.avx2.pshuf.b` for the table lookups, `llvm.usub.sat.v32i8` for the
two saturating subtracts, and `llvm.x86.avx.ptestz.256` for the zero tests.
This module binds those three to `BitLanes`' and `Semantics`' lane vocabulary —
`pshufbLanes`, `subsSat`, `ptestz` — and to nothing else: an unresolved symbol
stays `ub`, which is what makes an emission this environment does not describe
fail rather than be read as something it is not.

The parser validates the three symbols' arity, operand types and result type
(`checkIntrinsicShape`), so the shapes matched below are the only ones that
reach this environment from a parsed module.

The tables the stage shuffles are folded to literal `<32 x i8>` operands by the
compiler, so the shuffle arm takes its table from the call's first operand and
this environment carries no table parameter.  That is the structural difference
between this unit's call sites and the mask unit's, whose table arrives as a
`<32 x i8>` register read from the caller's buffer.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum.JsonUtf8IR

open LeanLLVM

/-- The stage's reference call environment: the three intrinsics the emission
calls, each at the shape the parser admits, and nothing else. -/
def utf8Calls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx2.pshuf.b", [.vec 32 8 table, .vec 32 8 control] =>
        some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next }
    | "llvm.usub.sat.v32i8", [.vec 32 8 a, .vec 32 8 b] =>
        some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
               mem := mem, next := next }
    | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
        some { ret := .int 32 (BitLanes.ptestz (BitVec.ofNat 256 (packLanes a))
              (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
    | _, _ => none

/-- The table lookup: `pshuf.b`'s meaning is `pshufbLanes` on the two operand
lane lists, the table then the control. -/
theorem utf8Calls_pshufb (table control : List (BitVec 8)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.x86.avx2.pshuf.b" [.vec 32 8 table, .vec 32 8 control] mem next =
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next } :=
  rfl

/-- The saturating subtract: `subsSat` applied lane by lane, and no flag. -/
theorem utf8Calls_usubSat (a b : List (BitVec 8)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.usub.sat.v32i8" [.vec 32 8 a, .vec 32 8 b] mem next =
      some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
             mem := mem, next := next } :=
  rfl

/-- The zero test: the two `<4 x i64>` operands packed little-endian into one
256-bit word each, and `ptestz` read at that word. -/
theorem utf8Calls_ptestz (a b : List (BitVec 64)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.x86.avx.ptestz.256" [.vec 4 64 a, .vec 4 64 b] mem next =
      some { ret := .int 32 (BitLanes.ptestz (BitVec.ofNat 256 (packLanes a))
            (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next } :=
  rfl

end LeanLLVM.Vellum.JsonUtf8IR
