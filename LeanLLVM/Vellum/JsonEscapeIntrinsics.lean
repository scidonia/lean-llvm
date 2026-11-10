/-
The escape unit's intrinsic vocabulary: the five call spellings the captured
emission calls, each bound to its model.  That the bound set is exactly the
fixture's measured call set is checked in `tests/escape-intrinsics.lean`, which
compares the two on every run.

`probes/install/ir/json-escape.candidate.ll` is that emission, and its
`probes/install/ir/json-escape.inventory` names five intrinsic spellings.  Two are
the entry kernels' — `llvm.ctpop.i64` and `llvm.cttz.i64`, bound at `BitLanes`'
`ctpop` and `cttz` — and three are new with this unit: `llvm.umin.i32`,
`llvm.x86.sse2.pmadd.wd` and `llvm.x86.ssse3.pmadd.ub.sw.128`, whose models
`BitLanes` states at the lanes the instructions read.  A spelling is bound in the
environment of the unit that calls it, because a `Calls` environment resolves on
its own; the models behind the two shared spellings are one definition each, so
the entry and escape units cannot disagree about what those two instructions mean.

`escapeCalls` takes the shape `entryCalls`, `s1Calls` and `utf8Calls` take: a
symbol and an argument list either resolve to a model or to `none`, which `step`
reads as undefined behaviour.  An unresolved spelling is therefore `ub` here, and
that is the only statement this module makes about coverage: the check that the
fixture calls nothing else lives in `tests/escape-intrinsics.lean` and nowhere
else, because an `include_str` in a compiled module is read when that module is
elaborated, so a regenerated inventory would be compared only when something else
forced a rebuild, whereas the evidence file is compiled from source on every run.

Each arm matches the shape the call spells, and the arguments keep the call's
order: `umin`'s two operands in order, and the multiply-adds' unsigned-then-signed
(PMADDUBSW) and signed-then-signed (PMADDWD) orders.  `checkIntrinsicShape` fixes
each admitted shape, so a call at another shape is refused by name before it
reaches this environment, and an arm here that no call can reach is not how a
wrong shape is met.  The step lemmas that read one call at a time — the head of each
escape-body step — are in `tests/escape-intrinsics.lean`, which is where this
vocabulary's sufficiency is demonstrated rather than claimed.
-/
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum.JsonEscapeIntrinsics

open LeanLLVM
open LeanLLVM.Vellum.BitLanes

/-! ### The types the emission spells -/

/-- The `<16 x i8>` operand of `pmadd.ub.sw`. -/
abbrev v16i8 : Ty := .vec 16 (.int 8)

/-- The `<8 x i16>` operand of `pmadd.wd`, and the result of `pmadd.ub.sw`. -/
abbrev v8i16 : Ty := .vec 8 (.int 16)

/-- The `<4 x i32>` result of `pmadd.wd`. -/
abbrev v4i32 : Ty := .vec 4 (.int 32)

/-! ### The call environment -/

/-- The escape unit's reference call environment: the five spellings the captured
emission (`probes/install/ir/json-escape.candidate.ll`) calls, and nothing else.  Every arm returns the caller's memory and
allocator cursor unchanged, because none of the five reads or writes memory.

`cttz`'s `i1` flag is admitted at both values for the reason `entryCalls` states:
at `false` the model is exactly LLVM's, and at `true` LLVM makes the zero word
poison while this model gives it the width.  It is admissible here because a
cleared word's count reaches only the batch reserve past the emitted positions:
`escapePositionsPost` (`JsonEscapeSteps.lean`) claims the positions up to
`escapePositionsFrom`'s length, and its unchanged conjunct names the run's *touched*
extent — those positions plus that reserve (`touchedPositions`), and not the
capacity — so no clause of the list record reads a value the poison could have
produced.  The three new spellings have no flag, so nothing is bounded for
them. -/
def escapeCalls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.ctpop.i64", [.int 64 x] =>
        some { ret := .int 64 (BitVec.ofNat 64 (ctpop x)), mem := mem, next := next }
    | "llvm.cttz.i64", [.int 64 x, .int 1 _flag] =>
        some { ret := .int 64 (BitVec.ofNat 64 (cttz x)), mem := mem, next := next }
    | "llvm.umin.i32", [.int 32 a, .int 32 b] =>
        some { ret := .int 32 (umin a b), mem := mem, next := next }
    | "llvm.x86.sse2.pmadd.wd", [.vec 8 16 x, .vec 8 16 y] =>
        some { ret := .vec 4 32 (pmaddWd x y), mem := mem, next := next }
    | "llvm.x86.ssse3.pmadd.ub.sw.128", [.vec 16 8 x, .vec 16 8 y] =>
        some { ret := .vec 8 16 (pmaddUbSw x y), mem := mem, next := next }
    | _, _ => none

/-- The 64-bit population count. -/
theorem escapeCalls_ctpop64 (x : BitVec 64) (mem : Mem) (next : Nat) :
    escapeCalls "llvm.ctpop.i64" [.int 64 x] mem next =
      some { ret := .int 64 (BitVec.ofNat 64 (ctpop x)), mem := mem, next := next } :=
  rfl

/-- The trailing count, at either flag: the flag does not change the value the
model gives, as at `entryCalls`. -/
theorem escapeCalls_cttz (x : BitVec 64) (flag : BitVec 1) (mem : Mem) (next : Nat) :
    escapeCalls "llvm.cttz.i64" [.int 64 x, .int 1 flag] mem next =
      some { ret := .int 64 (BitVec.ofNat 64 (cttz x)), mem := mem, next := next } :=
  rfl

/-- The unsigned minimum, at the call's operand order. -/
theorem escapeCalls_umin32 (a b : BitVec 32) (mem : Mem) (next : Nat) :
    escapeCalls "llvm.umin.i32" [.int 32 a, .int 32 b] mem next =
      some { ret := .int 32 (umin a b), mem := mem, next := next } :=
  rfl

/-- Signed word multiply-add, at `<8 x i16>` operands and a `<4 x i32>` result. -/
theorem escapeCalls_pmaddWd (x y : List (BitVec 16)) (mem : Mem) (next : Nat) :
    escapeCalls "llvm.x86.sse2.pmadd.wd" [.vec 8 16 x, .vec 8 16 y] mem next =
      some { ret := .vec 4 32 (pmaddWd x y), mem := mem, next := next } :=
  rfl

/-- Unsigned-by-signed byte multiply-add with a saturated word result, at
`<16 x i8>` operands and an `<8 x i16>` result. -/
theorem escapeCalls_pmaddUbSw (x y : List (BitVec 8)) (mem : Mem) (next : Nat) :
    escapeCalls "llvm.x86.ssse3.pmadd.ub.sw.128" [.vec 16 8 x, .vec 16 8 y] mem next =
      some { ret := .vec 8 16 (pmaddUbSw x y), mem := mem, next := next } :=
  rfl

/-- **Every arm is memory- and allocator-neutral.**  None of the five spellings
reads or writes memory or allocates, so whichever arm resolves, the caller's memory
and allocator cursor are what the callee leaves.  This is the frame head a step over
one of these calls consumes: the instruction binds a value and changes nothing
else, so a clause about the memory after it is a clause about the memory before it.
Stated once over the environment rather than once per spelling, because every arm
is the same statement. -/
theorem escapeCalls_mem_next {callee : String} {args : List Value} {mem : Mem}
    {next : Nat} {r : CallOutcome} (h : escapeCalls callee args mem next = some r) :
    r.mem = mem ∧ r.next = next := by
  simp only [escapeCalls] at h
  split at h <;> simp_all
  all_goals (subst h; simp)

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_mem_next' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_mem_next

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_ctpop64' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_ctpop64

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_cttz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_cttz

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_umin32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_umin32

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_pmaddWd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_pmaddWd

/-- info: 'LeanLLVM.Vellum.JsonEscapeIntrinsics.escapeCalls_pmaddUbSw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_pmaddUbSw

end LeanLLVM.Vellum.JsonEscapeIntrinsics
