/-
The stage-2 walk's entry run: `entry`'s fifty-seven instructions as four
`denoteCode` segments, and the block's step.

`WalkSeedState` (`JsonStage2WalkScope`) is the state at the loop head, and
`JsonStage2WalkSeed` states it, the preheader and the header as the seed's
production.  This module supplies the run that reaches them: the entry block's
own instruction list, cut into four segments that are each one `denoteCode`
equality at a symbolic environment and state, and composed into the block's run
and its `step`.

The segments are a partition of the pinned list: `walkEntryInstrs_segments` is
the `rfl` that says the four cuts are `walkEntryInstrs` and nothing else, so a
change to the block's text fails here rather than in a paraphrase.

Segment 1 is the four `alloca`s, the three `lifetime.start` markers, and the
`(%n + 63) >> 6` block count.  It writes no memory: the allocator's cursor moves
by the four objects' sizes and the environment binds the four pointers and the
two arithmetic words.

Three of the four are proved (`walkEntrySeg1_denote`, `walkEntrySeg3_denote`,
`walkEntrySeg4_denote`).  The second — the initialisation, the `S2` record's
fields, the log's memset and stores, and the two cursor loads — is cut into its
two halves (`walkEntrySeg2a`/`walkEntrySeg2b`, pinned by a `rfl`) and **not**
proved: its goal carries the initialisation's fifteen-store list, and at
`maxRecDepth 20000`/`maxHeartbeats 2000000` the elaboration times out at the
store that follows the `S2` field writes in both halves.  Splitting the segment
at its loads and deferring the side goals did not reduce the cost, so it is the
term's own size rather than a tactic shape.  The shape that avoids it is a
list-level read lemma (`readBytes (stage2WriteStores m (s2InitStores ...))`) read
*before* the chain, so that the goal never carries the store list.

The segments' statements carry `env`, `s` and `is` explicitly rather than
leaving them to unification: `lookupName` reduces to an `if` on a `String`
equality that `isDefEq` cannot soundly decide, so an implicit state whose
lookup is asked to reduce definitionally can leave a metavariable assigned from
the branch it then rejects.  Every side goal below is stated at a named
environment and closed by the `block_lk` peel, `simpa [lookupName]`, or the
hypothesis the segment takes.
-/
import LeanLLVM.Refinement.JsonStage2WalkSeed

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### The four segments -/

/-- `entry`'s first nine instructions: the four `alloca`s, the three lifetime
markers, and the block count `(%n + 63) >> 6`. -/
def walkEntrySeg1 : List Instr := [
  Instr.alloca "%ei.i" (Ty.int 64) 0,
  Instr.alloca "%root_done.i" (Ty.int 32) 0,
  Instr.alloca "%xj.i" (Ty.int 64) 0,
  Instr.alloca "%outn.i" (Ty.int 64) 0,
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (Operand.reg "%s"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (Operand.reg "%z"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
  Instr.binop "%add" BinOp.add 64 (Operand.reg "%n") (Operand.imm (.int 64 (BitVec.ofNat 64 63))),
  Instr.binop "%shr" BinOp.lshr 64 (Operand.reg "%add") (Operand.imm (.int 64 (BitVec.ofNat 64 6)))]

/-- `entry`'s next twenty-three: `s2_init`, the `S2` record's three argument
fields, the log's four fields at `%z` (after the hash word's sixteen zero bytes),
and the two cursor words loaded from the caller's slots. -/
def walkEntrySeg2 : List Instr := [
  Instr.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")), ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")), (Ty.ptr, (Operand.reg "%ep"))],
  Instr.gep "%nsp" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
  Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nsp"),
  Instr.gep "%xp1" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 72))),
  Instr.store Ty.ptr (Operand.reg "%xp") (Operand.reg "%xp1"),
  Instr.gep "%nxp2" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 80))),
  Instr.store (Ty.int 64) (Operand.reg "%nxp") (Operand.reg "%nxp2"),
  Instr.gep "%hash1.i.i" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
  Instr.gep "%ar" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 40))),
  Instr.gep "%0" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
  Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 16)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
  Instr.store Ty.ptr (Operand.reg "%dst") (Operand.reg "%ar"),
  Instr.load "%1" (Ty.int 64) (Operand.reg "%ndst"),
  Instr.gep "%alen" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 48))),
  Instr.store (Ty.int 64) (Operand.reg "%1") (Operand.reg "%alen"),
  Instr.gep "%acap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
  Instr.store (Ty.int 64) (Operand.reg "%dstcap") (Operand.reg "%acap"),
  Instr.store Ty.ptr (Operand.reg "%ev") (Operand.reg "%z"),
  Instr.load "%2" (Ty.int 64) (Operand.reg "%nev"),
  Instr.gep "%len" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
  Instr.store (Ty.int 64) (Operand.reg "%2") (Operand.reg "%len"),
  Instr.gep "%cap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
  Instr.store (Ty.int 64) (Operand.reg "%evcap") (Operand.reg "%cap")]

/-- `entry`'s next seventeen: the document base and length and the entry stream's
base read back out of the `S2` record, then the cursor record `%c.i` — its one
memset and its five stores. -/
def walkEntrySeg3 : List Instr := [
  Instr.load "%3" Ty.ptr (Operand.reg "%s"),
  Instr.gep "%n2.i" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
  Instr.load "%4" (Ty.int 64) (Operand.reg "%n2.i"),
  Instr.gep "%ep3.i" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 48))),
  Instr.load "%5" Ty.ptr (Operand.reg "%ep3.i"),
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c.i"))],
  Instr.gep "%6" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 40))),
  Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%6")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1152)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
  Instr.store Ty.ptr (Operand.reg "%3") (Operand.reg "%c.i"),
  Instr.gep "%n6.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
  Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%n6.i"),
  Instr.gep "%ix.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
  Instr.store Ty.ptr (Operand.reg "%5") (Operand.reg "%ix.i"),
  Instr.gep "%nix.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
  Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nix.i"),
  Instr.gep "%e7.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1112))),
  Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e7.i")]

/-- `entry`'s last eight: three more lifetime markers, the two zeroed slots the
nesting arm and the decoder read, the document base's predecessor, and the entry
count's test. -/
def walkEntrySeg4 : List Instr := [
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%ctype.i"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%cst.i"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), (Ty.ptr, (Operand.reg "%root_done.i"))],
  Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 0))) (Operand.reg "%root_done.i"),
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj.i"))],
  Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%xj.i"),
  Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%3") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
  Instr.icmp "%cmp.i247.not" IPred.eq 64 (Operand.reg "%nep") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))]

/-- **The cuts are the block.**  A change to `entry`'s text that is not also made
here fails this `rfl`, so the segments are the pinned list's own and not a
paraphrase of it. -/
theorem walkEntryInstrs_segments :
    walkEntryInstrs =
      walkEntrySeg1 ++ walkEntrySeg2 ++ walkEntrySeg3 ++ walkEntrySeg4 := rfl

/-! ### The values a segment leaves -/

/-- Segment 1's environment: the block count, its numerator, and the four stack
objects at the allocator's cursor. -/
def walkEntryEnv1 (env : Env) (c n : Nat) : Env :=
  cells [("%shr", .int 64 ((BitVec.ofNat 64 n + BitVec.ofNat 64 63) >>> 6)),
         ("%add", .int 64 (BitVec.ofNat 64 n + BitVec.ofNat 64 63)),
         ("%outn.i", .ptr (c + 20)), ("%xj.i", .ptr (c + 12)),
         ("%root_done.i", .ptr (c + 8)), ("%ei.i", .ptr c)] env

/-- The `lifetime.start` marker's two-argument list, evaluated: the immediate
length and the pointer register. -/
theorem walkEvalOperands_lifetime (env : Env) (s : State) (n : Nat) (p : String)
    {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalOperands (stateAt env s)
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 n))), (Ty.ptr, Operand.reg p)] =
      some [.int 64 (BitVec.ofNat 64 n), .ptr a] := by
  simp [evalOperands, evalOperand, Const.toValue, stateAt, hp]

/-- A `lifetime.start` marker at a register pointer and an immediate length: the
form `entry`'s seven markers have.  Stated at the instruction's own operands so
the rewrite fixes the pointer name and the length rather than leaving them to
`evalOperands`' unification. -/
theorem denoteCode_lifetime_at (sub : Calls) (env : Env) (s : State)
    (n : Nat) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2Calls sub)
        (.callVoid "llvm.lifetime.start.p0"
          [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 n))), (Ty.ptr, Operand.reg p)]
          :: is) (stateAt env s) =
      denoteCode (stage2Calls sub) is (stateAt env s) :=
  denoteCode_lifetime sub env s "llvm.lifetime.start.p0" (by left; rfl)
    (walkEvalOperands_lifetime env s n p hp) is

/-- A pointer load: `%d = load ptr, ptr %p` at the eight bytes a word occupies.
`loadValue` reads a pointer as the word's `Nat`, so the read produces `.ptr q`. -/
theorem denoteCode_loadPtr (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes q 8)) (hq : q < 2 ^ 64)
    (is : List Instr) :
    denoteCode calls (.load d Ty.ptr (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr q) :: env) s) := by
  have hv' : loadValue s.mem Ty.ptr a = some (.ptr q) := by
    simp only [loadValue, hv, natToBytes_toNat,
      show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt hq]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := by simpa only [stateAt] using hv')])]
  simp only [stateAt, State.bind]

/-- A literal `getelementptr` offset as the step leaves it: `signExtend` of the
written immediate.  The step lemmas produce this form, so the outgoing
environment states it, so the segments close by `rfl`. -/
def woff (k : Nat) : Nat := (BitVec.signExtend 64 (BitVec.ofNat 64 k)).toNat

theorem woff_0 : woff 0 = 0 := by decide
theorem woff_4 : woff 4 = 4 := by decide
theorem woff_8 : woff 8 = 8 := by decide
theorem woff_16 : woff 16 = 16 := by decide
theorem woff_24 : woff 24 = 24 := by decide
theorem woff_32 : woff 32 = 32 := by decide
theorem woff_40 : woff 40 = 40 := by decide
theorem woff_48 : woff 48 = 48 := by decide
theorem woff_56 : woff 56 = 56 := by decide
theorem woff_64 : woff 64 = 64 := by decide
theorem woff_72 : woff 72 = 72 := by decide
theorem woff_80 : woff 80 = 80 := by decide
theorem woff_1112 : woff 1112 = 1112 := by decide
theorem woff_1192 : woff 1192 = 1192 := by decide

/-- The literal offsets the entry run's reads and writes use, reduced. -/
macro "woff_num" : tactic => `(tactic|
  (simp only [woff_0, woff_4, woff_8, woff_16, woff_24, woff_32, woff_40,
    woff_48, woff_56, woff_64, woff_72, woff_80, woff_1112, woff_1192]))

/-- Segment 4's environment: the document base's predecessor and the entry count's
test bit. -/
def walkEntryEnv4 (env : Env) (b nep : Nat) : Env :=
  cells [("%cmp.i247.not",
           .int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))),
         ("%invariant.gep", .ptr (b - 1))] env

/-- **Segment 1.**  Four `alloca`s advance the cursor by `28` and bind the four
pointers; the three markers leave the state alone; the block count is
`(%n + 63) >> 6`.  No memory is written. -/
theorem walkEntrySeg1_denote (sub : Calls) (env : Env) (s : State) (is : List Instr)
    {n sAddr zAddr eAddr : Nat}
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hz : lookupName env "%z" = some (.ptr zAddr))
    (he : lookupName env "%e" = some (.ptr eAddr)) :
    denoteCode (stage2Calls sub) (walkEntrySeg1 ++ is) (stateAt env s) =
      denoteCode (stage2Calls sub) is
        (stateAt (walkEntryEnv1 env s.next n) { s with next := s.next + 28 }) := by
  simp only [walkEntrySeg1, List.cons_append, List.nil_append]
  rw [denoteCode_alloca (calls := stage2Calls sub) (d := "%ei.i") (ty := Ty.int 64) (align := 0)]
  rw [denoteCode_alloca (calls := stage2Calls sub) (d := "%root_done.i") (ty := Ty.int 32) (align := 0)]
  rw [denoteCode_alloca (calls := stage2Calls sub) (d := "%xj.i") (ty := Ty.int 64) (align := 0)]
  rw [denoteCode_alloca (calls := stage2Calls sub) (d := "%outn.i") (ty := Ty.int 64) (align := 0)]
  rw [denoteCode_lifetime_at (a := sAddr) _ _ _ 120 "%s" ?_ _] <;> try block_lk
  rw [denoteCode_lifetime_at (a := zAddr) _ _ _ 64 "%z" ?_ _] <;> try block_lk
  rw [denoteCode_lifetime_at (a := eAddr) _ _ _ 24 "%e" ?_ _] <;> try block_lk
  rw [walkDenoteCode_add_imm_w _ _ _ "%add" "%n" 64 (x := BitVec.ofNat 64 n) ?_ _] <;> try block_lk
  rw [denoteCode_lshr_imm _ _ _ "%shr" "%add" (x := BitVec.ofNat 64 n + BitVec.ofNat 64 63) ?_ _]
    <;> try block_lk


/-- Segment 3's environment: the three reads' bindings and the cursor record's
five addresses. -/
def walkEntryEnv3 (env : Env) (b n ep sAddr cAddr : Nat) : Env :=
  cells [("%e7.i", .ptr (cAddr + woff 1112)), ("%nix.i", .ptr (cAddr + woff 24)),
         ("%ix.i", .ptr (cAddr + woff 16)), ("%n6.i", .ptr (cAddr + woff 8)),
         ("%6", .ptr (cAddr + woff 40)), ("%5", .ptr ep),
         ("%ep3.i", .ptr (sAddr + woff 48)),
         ("%4", .int 64 (BitVec.ofNat 64 n)), ("%n2.i", .ptr (sAddr + woff 8)),
         ("%3", .ptr b)] env

/-! ### Segment 2 -/

/-- Segment 2's first thirteen instructions: from the `S2` record's fields to the
arena cursor's word, which the block loads out of the caller's slot. -/
def walkEntrySeg2a : List Instr := [
  Instr.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")), ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")), (Ty.ptr, (Operand.reg "%ep"))],
  Instr.gep "%nsp" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
  Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nsp"),
  Instr.gep "%xp1" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 72))),
  Instr.store Ty.ptr (Operand.reg "%xp") (Operand.reg "%xp1"),
  Instr.gep "%nxp2" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 80))),
  Instr.store (Ty.int 64) (Operand.reg "%nxp") (Operand.reg "%nxp2"),
  Instr.gep "%hash1.i.i" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
  Instr.gep "%ar" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 40))),
  Instr.gep "%0" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
  Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 16)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
  Instr.store Ty.ptr (Operand.reg "%dst") (Operand.reg "%ar"),
  Instr.load "%1" (Ty.int 64) (Operand.reg "%ndst")]

/-- Segment 2's remaining ten: the loaded word written at the log's arena-cursor
field, the capacity word, the stream's base, and the two cursor words at the
log's `len` and `cap`. -/
def walkEntrySeg2b : List Instr := [
  Instr.gep "%alen" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 48))),
  Instr.store (Ty.int 64) (Operand.reg "%1") (Operand.reg "%alen"),
  Instr.gep "%acap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
  Instr.store (Ty.int 64) (Operand.reg "%dstcap") (Operand.reg "%acap"),
  Instr.store Ty.ptr (Operand.reg "%ev") (Operand.reg "%z"),
  Instr.load "%2" (Ty.int 64) (Operand.reg "%nev"),
  Instr.gep "%len" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
  Instr.store (Ty.int 64) (Operand.reg "%2") (Operand.reg "%len"),
  Instr.gep "%cap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
  Instr.store (Ty.int 64) (Operand.reg "%evcap") (Operand.reg "%cap")]

/-- **The second segment is its two halves.** -/
theorem walkEntrySeg2_split : walkEntrySeg2 = walkEntrySeg2a ++ walkEntrySeg2b := rfl

/-! ### Segment 4 -/

/-- **Segment 4.**  Three markers, the two zeroed slots, the document base's
predecessor and the entry count's test. -/
theorem walkEntrySeg4_denote (sub : Calls) (env : Env) (s : State) (is : List Instr)
    {b nep ctypeAddr cstAddr rootAddr xjAddr : Nat}
    (hb : 0 < b)
    (h3 : lookupName env "%3" = some (.ptr b))
    (hct : lookupName env "%ctype.i" = some (.ptr ctypeAddr))
    (hcs : lookupName env "%cst.i" = some (.ptr cstAddr))
    (hr : lookupName env "%root_done.i" = some (.ptr rootAddr))
    (hx : lookupName env "%xj.i" = some (.ptr xjAddr))
    (hne : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    denoteCode (stage2Calls sub) (walkEntrySeg4 ++ is) (stateAt env s) =
      denoteCode (stage2Calls sub) is
        (stateAt (walkEntryEnv4 env b nep)
          { s with mem := (writeBytes
              (writeBytes s.mem rootAddr (natToBytes 0 4)) xjAddr (natToBytes 0 8)) }) := by
  simp only [walkEntrySeg4, List.cons_append, List.nil_append]
  rw [denoteCode_lifetime_at (a := ctypeAddr) (n := 520) (p := "%ctype.i") (hp := hct)]
  rw [denoteCode_lifetime_at (a := cstAddr) (n := 520) (p := "%cst.i") (hp := hcs)]
  rw [denoteCode_lifetime_at (a := rootAddr) (n := 4) (p := "%root_done.i") (hp := hr)]
  rw [denoteCode_store32_imm (calls := stage2Calls sub) (x := BitVec.ofNat 32 0)
    (p := "%root_done.i") (a := rootAddr) (hp := hr)]; try block_lk
  rw [denoteCode_lifetime_at (a := xjAddr) (n := 8) (p := "%xj.i") (hp := hx)]
  rw [denoteCode_store64_imm (calls := stage2Calls sub) (x := BitVec.ofNat 64 0)
    (p := "%xj.i") (a := xjAddr) (hp := hx)]; try block_lk
  rw [denoteCode_gep8_lit_back_one (calls := stage2Calls sub) (d := "%invariant.gep")
    (base := "%3") (a := b) (hb := h3) (ha := hb)]; try block_lk
  rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub) (d := "%cmp.i247.not")
    (a := "%nep") (w := 64) (x := BitVec.ofNat 64 nep) (c := BitVec.ofNat 64 0)]
    <;> try block_lk
  all_goals first | rfl | block_lk | skip

/-! ### Segment 3 -/

/-- **Segment 3.**  The three reads back out of the `S2` record, then the cursor
record: its memset and its five stores. -/
theorem walkEntrySeg3_denote (sub : Calls) (env : Env) (s : State) (is : List Instr)
    {b n ep nep eAddr sAddr cAddr : Nat}
    (hb64 : b < 2 ^ 64) (hn64 : n < 2 ^ 64) (hep64 : ep < 2 ^ 64) (hne64 : nep < 2 ^ 64)
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hc : lookupName env "%c.i" = some (.ptr cAddr))
    (he : lookupName env "%e" = some (.ptr eAddr))
    (hne : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (h3r : readBytes s.mem sAddr 8 = some (natToBytes b 8))
    (h4r : readBytes s.mem (sAddr + woff 8) 8 = some (natToBytes n 8))
    (h5r : readBytes s.mem (sAddr + woff 48) 8 = some (natToBytes ep 8)) :
    denoteCode (stage2Calls sub) (walkEntrySeg3 ++ is) (stateAt env s) =
      denoteCode (stage2Calls sub) is
        (stateAt (walkEntryEnv3 env b n ep sAddr cAddr)
          { s with mem := (writeBytes
              (writeBytes
                (writeBytes
                  (writeBytes
                    (writeBytes
                      (writeBytes s.mem (cAddr + woff 40) (List.replicate 1152 0))
                      cAddr (natToBytes b 8))
                    (cAddr + woff 8) (natToBytes n 8))
                  (cAddr + woff 16) (natToBytes ep 8))
                (cAddr + woff 24) (natToBytes nep 8))
              (cAddr + woff 1112) (natToBytes eAddr 8)) }) := by
  simp only [walkEntrySeg3, List.cons_append, List.nil_append]
  rw [denoteCode_loadPtr (calls := stage2Calls sub) (d := "%3") (p := "%s")
    (a := sAddr) (q := b) (hp := hs) (hv := h3r) (hq := hb64)]
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%n2.i") (base := "%s")
    (a := sAddr) (n := BitVec.ofNat 64 8) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_load64 (calls := stage2Calls sub) (d := "%4") (p := "%n2.i")
    (v := BitVec.ofNat 64 n)
    (hv := by rw [walkToNat_ofNat64 hn64]; exact h4r)] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%ep3.i") (base := "%s")
    (a := sAddr) (n := BitVec.ofNat 64 48) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_loadPtr (calls := stage2Calls sub) (d := "%5") (p := "%ep3.i")
    (a := sAddr + woff 48) (q := ep) (hv := h5r) (hq := hep64)] <;> try block_lk
  rw [denoteCode_lifetime_at (a := cAddr) (n := 1192) (p := "%c.i")] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%6") (base := "%c.i")
    (a := cAddr) (n := BitVec.ofNat 64 40) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_memset (sub := sub) (p := "%6") (nz := 1152) (a := cAddr + woff 40)]
    <;> try block_lk
  rw [denoteCode_storePtr (calls := stage2Calls sub) (v := "%3") (p := "%c.i")
    (q := b) (a := cAddr)] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%n6.i") (base := "%c.i")
    (a := cAddr) (n := BitVec.ofNat 64 8) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub) (v := "%4") (p := "%n6.i")
    (j := n) (a := cAddr + woff 8) (hj := hn64)] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%ix.i") (base := "%c.i")
    (a := cAddr) (n := BitVec.ofNat 64 16) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_storePtr (calls := stage2Calls sub) (v := "%5") (p := "%ix.i")
    (q := ep) (a := cAddr + woff 16)] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%nix.i") (base := "%c.i")
    (a := cAddr) (n := BitVec.ofNat 64 24) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_store64_ofNat (calls := stage2Calls sub) (v := "%nep") (p := "%nix.i")
    (j := nep) (a := cAddr + woff 24) (hj := hne64)] <;> try block_lk
  rw [denoteCode_gep8_lit_w (calls := stage2Calls sub) (d := "%e7.i") (base := "%c.i")
    (a := cAddr) (n := BitVec.ofNat 64 1112) (hpos := by decide)] <;> try block_lk
  rw [denoteCode_storePtr (calls := stage2Calls sub) (v := "%e") (p := "%e7.i")
    (q := eAddr) (a := cAddr + woff 1112)] <;> try block_lk
  all_goals first | rfl | block_lk | skip

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkScope.denoteCode_loadPtr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.denoteCode_loadPtr

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg1_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg1_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg3_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg3_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg4_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg4_denote

end WalkScope
end LeanLLVM.Refinement
