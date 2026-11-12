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

All four are proved (`walkEntrySeg1_denote`, `walkEntrySeg2_denote`,
`walkEntrySeg3_denote`, `walkEntrySeg4_denote`).  The second — the
initialisation, the `S2` record's fields, the log's memset and stores, and the
two cursor loads — is cut into its two halves
(`walkEntrySeg2a`/`walkEntrySeg2b`, pinned by a `rfl`), and its twenty-two
instructions after the initialisation are pinned to the block's own list as
`walkEntrySeg2Post` (`walkEntrySeg2_cut`).

Segment 2 is stated over `memAt` rather than over a state literal, and that is
what keeps the run linear.  `denoteCode`'s conclusion for one step is
`stateAt env {s with mem := ...}`; with `s` the previous state literal, each
conclusion repeats that literal in the four fields the step does not touch, so
the term grows four-fold per store, and the chain of twenty-two diverged at
`whnf` at `maxHeartbeats 4000000` after 2 m 05 s in that form.  `memAt` threads
the memory as an argument of its own (`JsonStage2WalkSeed`), so each conclusion
is `memAt s (writeBytes m ...)`: this module now elaborates in full in about
three seconds, and the segment's own `rfl` reduces a chain of projections rather
than a tree of literals.

The two cursor loads' values are transported before the chain:
`readBytes_stage2WriteStores_of_all_outside` reads a *store list* — one entry
avoiding the range is all it asks — so `walkSeg2Read1` and `walkSeg2Read2`
carry each load's value from the caller's memory (`m`) across the
initialisation's record and the segment's own store list.
`walkSeg2Ws1Window`/`Ws2Window`/`Ws3Window` place every entry of that list in
one of two windows — the record's cursor fields `[%s + 56, %s + 88)` and the
log's whole extent `[%z, %z + 64)` — and `seg2StoreOutside` turns a read
separated from a window into one separated from the entries inside it.
`walkSeg2PostMem_eq` reads the outgoing memory as a single fold over
`walkSeg2Stores`, so a composition over the segment meets the fold its statement
names without unfolding the run's own nesting.

The segments' statements carry `env`, `s`, `m` and `is` explicitly rather than
leaving them to unification: `lookupName` reduces to an `if` on a `String`
equality that `isDefEq` cannot soundly decide, so an implicit state whose lookup
is asked to reduce definitionally can leave a metavariable assigned from the
branch it then rejects.  Segment 2's side goals are the run's own cells, and
they are closed by peeling the cells as a syntactic rewrite and then matching a
binding exactly; `block_lk`'s `assumption` is not used there, because on this
goal set its definitional comparison of distinct `String` literals does not
terminate promptly.  The arithmetic that places the windows' entries is split
into its conjuncts before `omega` sees it, since `omega` on a conjunction is
what would otherwise add `Classical.choice` to the footprint.

The four segments compose in pairs.  `walkEntrySeg12_denote` runs segment 1 and
segment 2 — the second segment's `%shr` argument being the block count the first
computed — and leaves `walkEntryEnv2` over `walkEntryEnv1`.
`walkEntrySeg34_denote` runs the last two, reading the record's `%s->b`, `%s->n`
and `%s->ep` back out of the memory segment 2 leaves, and staging the cursor
record and the two zeroed slots.  `readBytes_stage2WriteStores_at` is the read
both halves use to recover the initialisation's fields: the record's writes lie
in `[%s, %s + 56)` and segment 2 writes only `[%s + 56, %s + 88)` and the log, so
a store list split at the field's own write reads that write's bytes back, with
the half after it required to lie outside.

One equality over all four is **not** stated, and the obstruction is measured
rather than guessed: the halves' conclusions name the memory as raw nested
`writeBytes`, so closing `produced = stated` asks `whnf` to compare two
eight-deep chains whose innermost term differs by one `memAt` projection.  A
memset's 1152-byte write reduces byte by byte in front of a memory that grows a
cell per byte, so that comparison is quadratic in the write's length: at
`maxHeartbeats 2000000` the check ran 61 s without finishing, and stating the
target in the produced form moves the same cost into the statement's own
elaboration.  The vocabulary that avoids it is segment 2's own — state the later
segments' conclusions over `stage2WriteStores` folds rather than raw nesting, so
the comparison meets a fold the run never unfolds.  That is the open row, and the
block's `step`, its `runFuel` prefix and `WalkSeedState`'s production all wait on
it: the loop head's facts are read at the memory this composition names.
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

/-! ### Segment 2: the initialisation, its fields, and the two cursor loads -/

/-- A store list all of whose entries lie outside the read range leaves the read
alone.  The sibling `readBytes_stage2WriteStores_of_outside` asks for one window
containing every entry; this asks only that each entry avoid the range, which is
what the entry run's two cursor loads need. -/
theorem readBytes_stage2WriteStores_of_all_outside :
    ∀ (stores : List (Nat × List UInt8)) {m : Mem} {a len : Nat},
      (∀ st ∈ stores, a + len ≤ st.1 ∨ st.1 + st.2.length ≤ a) →
      readBytes (stage2WriteStores m stores) a len = readBytes m a len
  | [], _, _, _, _ => rfl
  | (a', bs) :: rest, m, a, len, h => by
      have h1 : a + len ≤ a' ∨ a' + bs.length ≤ a := h (a', bs) (by simp)
      have hrest : ∀ st ∈ rest, a + len ≤ st.1 ∨ st.1 + st.2.length ≤ a :=
        fun st hst => h st (by simp [hst])
      show readBytes (stage2WriteStores (writeBytes m a' bs) rest) a len = readBytes m a len
      rw [readBytes_stage2WriteStores_of_all_outside rest (m := writeBytes m a' bs) hrest]
      exact walkReadBytes_writeBytes_outside (v := bs) (start := a') (addr := a) (n := len) h1

/-- A store inside an object's extent is outside a read separated from that
extent.  Each side of the separation is a disjunction, which `omega` will not
split on its own, so the split is here and each window is one linear step. -/
theorem seg2StoreOutside {a len base ext p : Nat} {l : List UInt8}
    (hp : base ≤ p) (hext : p + l.length ≤ base + ext) :
    (a + len ≤ base ∨ base + ext ≤ a) → a + len ≤ p ∨ p + l.length ≤ a := by
  intro hsep
  rcases hsep with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The `memset`'s literal count, reduced: the step writes `List.replicate` of it. -/
theorem seg2MemsetCount : (BitVec.ofNat 64 16).toNat = 16 := by decide

/-- Segment 2's first five stores, after `s2_init`: the `S2` record's three
argument fields and the log's arena words. -/
def walkSeg2Ws1 (sAddr zAddr nep xp nxp dst : Nat) : List (Nat × List UInt8) :=
  [(sAddr + woff 56, wordBytes 8 nep), (sAddr + woff 72, natToBytes xp 8),
   (sAddr + woff 80, wordBytes 8 nxp),
   (zAddr + woff 24, List.replicate (BitVec.ofNat 64 16).toNat 0),
   (zAddr + woff 40, natToBytes dst 8)]

/-- Segment 2's next three stores: the arena cursor read from the caller's slot,
the capacity word, and the log's stream base. -/
def walkSeg2Ws2 (zAddr v1 dstcap ev : Nat) : List (Nat × List UInt8) :=
  [(zAddr + woff 48, wordBytes 8 v1), (zAddr + woff 56, wordBytes 8 dstcap),
   (zAddr, natToBytes ev 8)]

/-- Segment 2's last two stores: the event cursor and the event capacity. -/
def walkSeg2Ws3 (zAddr v2 evcap : Nat) : List (Nat × List UInt8) :=
  [(zAddr + woff 8, wordBytes 8 v2), (zAddr + woff 16, wordBytes 8 evcap)]

/-- The three runs in the order the block writes them. -/
def walkSeg2Stores (sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat) :
    List (Nat × List UInt8) :=
  walkSeg2Ws1 sAddr zAddr nep xp nxp dst ++ walkSeg2Ws2 zAddr v1 dstcap ev ++
    walkSeg2Ws3 zAddr v2 evcap

/-- The memory at the first cursor load: the record's fields and the five stores
before the load. -/
def walkSeg2Mem1 (sAddr zAddr nep xp nxp dst : Nat) (m : Mem) : Mem :=
  stage2WriteStores m (walkSeg2Ws1 sAddr zAddr nep xp nxp dst)

/-- The memory at the second cursor load: the first run's stores, then the
second's. -/
def walkSeg2Mem2 (sAddr zAddr nep xp nxp dst v1 dstcap ev : Nat) (m : Mem) : Mem :=
  stage2WriteStores (walkSeg2Mem1 sAddr zAddr nep xp nxp dst m) (walkSeg2Ws2 zAddr v1 dstcap ev)

/-- The memory segment 2 hands on: the first two runs' stores, then the third's. -/
def walkSeg2PostMem (sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat) (m : Mem) : Mem :=
  stage2WriteStores (walkSeg2Mem2 sAddr zAddr nep xp nxp dst v1 dstcap ev m)
    (walkSeg2Ws3 zAddr v2 evcap)

/-- Segment 2's outgoing environment, newest first. -/
def walkEntryEnv2 (env : Env) (sAddr zAddr nep xp nxp dst v1 v2 ev : Nat) : Env :=
  cells [("%cap", .ptr (zAddr + woff 16)), ("%len", .ptr (zAddr + woff 8)),
         ("%2", .int 64 (BitVec.ofNat 64 v2)), ("%acap", .ptr (zAddr + woff 56)),
         ("%alen", .ptr (zAddr + woff 48)), ("%1", .int 64 (BitVec.ofNat 64 v1)),
         ("%0", .ptr (zAddr + woff 24)), ("%ar", .ptr (zAddr + woff 40)),
         ("%hash1.i.i", .ptr (zAddr + woff 32)),
         ("%nxp2", .ptr (sAddr + woff 80)), ("%xp1", .ptr (sAddr + woff 72)),
         ("%nsp", .ptr (sAddr + woff 56))] env

/-- Segment 2 after the initialisation: the `S2` record's fields, the log's
fields, and the two cursor loads. -/
def walkEntrySeg2Post : List Instr := [
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

/-- **Segment 2 is the initialisation and then these twenty-two.** -/
theorem walkEntrySeg2_cut :
    walkEntrySeg2 =
      Instr.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")),
        ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")),
        (Ty.ptr, (Operand.reg "%ep"))] :: walkEntrySeg2Post := rfl



/-! ### The second segment's equality

The step vocabulary of `JsonStage2WalkSeed` (`memAt`) is what makes this chain
linear: the incoming memory is an argument, so the twenty-three steps compose
without repeating the state four times per step.  The reads the two cursor loads
make are transported before the chain runs — `walkSeg2Read1` and `walkSeg2Read2`
carry each across the initialisation's record and the segment's own store list —
so the chain itself is only the steps.

The stores lie in two windows: the record's three cursor fields,
`[%s + 56, %s + 88)`, and the log's whole extent, `[%z, %z + 64)`.  That is the
fact the transport lemmas rest on, and the fact a read at the record's argument
fields (`%s + 0`, `%s + 8`, `%s + 48`) needs in order to survive the segment. -/

/-- The memory the initialisation hands the rest of the segment. -/
def walkSeg2InitMem (sAddr b ep : Nat) (n nb : BitVec 64) (m : Mem) : Mem :=
  stage2WriteStores m (s2InitStores sAddr b n.toNat nb.toNat ep)

/-- Folding a store list is folding its two halves. -/
theorem stage2WriteStores_append : ∀ (ws1 ws2 : List (Nat × List UInt8)) (m : Mem),
    stage2WriteStores m (ws1 ++ ws2) = stage2WriteStores (stage2WriteStores m ws1) ws2
  | [], _, _ => rfl
  | (a, bs) :: rest, ws2, m => by
      show stage2WriteStores (writeBytes m a bs) (rest ++ ws2) = _
      rw [stage2WriteStores_append rest ws2 (writeBytes m a bs)]
      rfl

/-- **The first run's stores lie in the two windows.**  The record's `%nep`,
`%xp` and `%nxp` fields, and the log's arena cursor and stream base. -/
theorem walkSeg2Ws1Window (sAddr zAddr nep xp nxp dst : Nat) :
    ∀ st ∈ walkSeg2Ws1 sAddr zAddr nep xp nxp dst,
      (sAddr + 56 ≤ st.1 ∧ st.1 + st.2.length ≤ sAddr + 88) ∨
      (zAddr ≤ st.1 ∧ st.1 + st.2.length ≤ zAddr + 64) := by
  intro st hst
  simp only [walkSeg2Ws1, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl
  all_goals
    (simp (config := { failIfUnchanged := false }) only
       [woff_24, woff_40, woff_56, woff_72, woff_80, seg2MemsetCount,
        wordBytes, natToBytes_length, List.length_replicate]
     first
     | exact Or.inl ⟨by omega, by omega⟩
     | exact Or.inr ⟨by omega, by omega⟩)

/-- **The second run's stores lie in the log's window.** -/
theorem walkSeg2Ws2Window (zAddr v1 dstcap ev : Nat) :
    ∀ st ∈ walkSeg2Ws2 zAddr v1 dstcap ev,
      (zAddr ≤ st.1 ∧ st.1 + st.2.length ≤ zAddr + 64) := by
  intro st hst
  simp only [walkSeg2Ws2, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl
  all_goals
    (simp (config := { failIfUnchanged := false }) only
       [woff_48, woff_56, wordBytes, natToBytes_length]
     constructor <;> omega)

/-- **The third run's stores lie in the log's window.** -/
theorem walkSeg2Ws3Window (zAddr v2 evcap : Nat) :
    ∀ st ∈ walkSeg2Ws3 zAddr v2 evcap,
      (zAddr ≤ st.1 ∧ st.1 + st.2.length ≤ zAddr + 64) := by
  intro st hst
  simp only [walkSeg2Ws3, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl
  all_goals
    (simp (config := { failIfUnchanged := false }) only
       [woff_8, woff_16, wordBytes, natToBytes_length]
     constructor <;> omega)

/-- **Every store the second segment writes lies in one of two windows.** -/
theorem walkSeg2StoreWindow (sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat) :
    ∀ st ∈ walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap,
      (sAddr + 56 ≤ st.1 ∧ st.1 + st.2.length ≤ sAddr + 88) ∨
      (zAddr ≤ st.1 ∧ st.1 + st.2.length ≤ zAddr + 64) := by
  intro st hst
  simp only [walkSeg2Stores, List.mem_append] at hst
  rcases hst with (h | h) | h
  · exact walkSeg2Ws1Window sAddr zAddr nep xp nxp dst st h
  · exact Or.inr (walkSeg2Ws2Window zAddr v1 dstcap ev st h)
  · exact Or.inr (walkSeg2Ws3Window zAddr v2 evcap st h)

/-- A read separated from both windows is untouched by every store the second
segment writes. -/
theorem walkSeg2StoresOutside {a len sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat}
    (hs : a + len ≤ sAddr + 56 ∨ sAddr + 88 ≤ a)
    (hz : a + len ≤ zAddr ∨ zAddr + 64 ≤ a) :
    ∀ st ∈ walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap,
      a + len ≤ st.1 ∨ st.1 + st.2.length ≤ a := by
  intro st hst
  rcases walkSeg2StoreWindow sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap st hst with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hs with h | h <;> omega
  · rcases hz with h | h <;> omega

/-- The segment's whole store list leaves such a read alone. -/
theorem readBytes_walkSeg2Stores {m : Mem} {a len sAddr zAddr nep xp nxp dst v1 dstcap ev
    v2 evcap : Nat}
    (hs : a + len ≤ sAddr + 56 ∨ sAddr + 88 ≤ a)
    (hz : a + len ≤ zAddr ∨ zAddr + 64 ≤ a) :
    readBytes (stage2WriteStores m (walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap))
        a len = readBytes m a len :=
  readBytes_stage2WriteStores_of_all_outside _ (walkSeg2StoresOutside hs hz)

/-- The segment's outgoing memory is its three runs folded over its store list. -/
theorem walkSeg2PostMem_eq (sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat) (m : Mem) :
    walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap m =
      stage2WriteStores m (walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap) := by
  simp only [walkSeg2PostMem, walkSeg2Mem2, walkSeg2Mem1, walkSeg2Stores, List.append_assoc]
  rw [stage2WriteStores_append, stage2WriteStores_append]

/-- **The first cursor load's value**, read at the caller's memory and carried
through the initialisation and the five stores before the load. -/
theorem walkSeg2Read1 {m : Mem} {sAddr b ep zAddr nep xp nxp dst ndst v1 : Nat} {n nb : BitVec 64}
    (hs : ndst + 8 ≤ sAddr ∨ sAddr + 120 ≤ ndst)
    (hz : ndst + 8 ≤ zAddr ∨ zAddr + 64 ≤ ndst)
    (h : readBytes m ndst 8 = some (natToBytes v1 8)) :
    readBytes (walkSeg2Mem1 sAddr zAddr nep xp nxp dst (walkSeg2InitMem sAddr b ep n nb m))
        ndst 8 = some (natToBytes v1 8) := by
  have hsub : ∀ st ∈ walkSeg2Ws1 sAddr zAddr nep xp nxp dst,
      ndst + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ ndst := by
    intro st hst
    rcases walkSeg2Ws1Window sAddr zAddr nep xp nxp dst st hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hs with h | h <;> omega
    · rcases hz with h | h <;> omega
  rw [walkSeg2Mem1, walkSeg2InitMem,
    readBytes_stage2WriteStores_of_all_outside _ hsub,
    readBytes_s2Init_of_outside (sv := sAddr) (b := b) (n := n.toNat) (nb := nb.toNat)
      (ep := ep) hs]
  exact h

/-- **The second cursor load's value**, carried through the initialisation and
the eight stores before it. -/
theorem walkSeg2Read2 {m : Mem} {sAddr b ep zAddr nep xp nxp dst dstcap ev nev v1 v2 : Nat}
    {n nb : BitVec 64}
    (hs : nev + 8 ≤ sAddr ∨ sAddr + 120 ≤ nev)
    (hz : nev + 8 ≤ zAddr ∨ zAddr + 64 ≤ nev)
    (h : readBytes m nev 8 = some (natToBytes v2 8)) :
    readBytes (walkSeg2Mem2 sAddr zAddr nep xp nxp dst v1 dstcap ev
        (walkSeg2InitMem sAddr b ep n nb m)) nev 8 = some (natToBytes v2 8) := by
  have hWs1 : ∀ st ∈ walkSeg2Ws1 sAddr zAddr nep xp nxp dst,
      nev + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ nev := by
    intro st hst
    rcases walkSeg2Ws1Window sAddr zAddr nep xp nxp dst st hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hs with h | h <;> omega
    · rcases hz with h | h <;> omega
  have hWs2 : ∀ st ∈ walkSeg2Ws2 zAddr v1 dstcap ev,
      nev + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ nev := by
    intro st hst
    obtain ⟨h1, h2⟩ := walkSeg2Ws2Window zAddr v1 dstcap ev st hst
    rcases hz with h | h <;> omega
  rw [walkSeg2Mem2,
    readBytes_stage2WriteStores_of_all_outside (walkSeg2Ws2 zAddr v1 dstcap ev) hWs2,
    walkSeg2Mem1,
    readBytes_stage2WriteStores_of_all_outside (walkSeg2Ws1 sAddr zAddr nep xp nxp dst) hWs1,
    walkSeg2InitMem,
    readBytes_s2Init_of_outside (sv := sAddr) (b := b) (n := n.toNat) (nb := nb.toNat)
      (ep := ep) hs]
  exact h

/-- **The second segment's equality.**  `s2_init`, the record's three argument
fields, the log's fields, and the two cursor loads — twenty-three instructions at
a symbolic environment, state, and incoming memory, leaving the environment
`walkEntryEnv2` and the memory `walkSeg2PostMem`.

The chain is composed of `memAt` steps, so each conclusion threads the memory
instead of repeating the state: the twenty-two post-initialisation steps cost
`whnf` a chain of projections rather than a tree of literals, which is what the
structure-literal form of the same chain could not do at `maxHeartbeats
4000000`.  The reads are the two hypotheses at the caller's memory, transported
by `walkSeg2Read1` and `walkSeg2Read2` before the chain starts.  The side
conditions are the run's own cells: each is the cell the step before it wrote, or
a binding the incoming environment carries, and the search is a syntactic peel
followed by an exact match rather than `block_lk`'s `assumption`, whose
definitional comparison of distinct `String` literals does not terminate
promptly on this goal set. -/
theorem walkEntrySeg2_denote (env : Env) (s : State) (m : Mem) (is : List Instr)
    {sAddr b ep zAddr nep xp nxp dst dstcap ev ndst nev v1 v2 evcap : Nat} {n nb : BitVec 64}
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnb : lookupName env "%shr" = some (.int 64 nb))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hz : lookupName env "%z" = some (.ptr zAddr))
    (hne : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 nxp)))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hndst : lookupName env "%ndst" = some (.ptr ndst))
    (hdcap : lookupName env "%dstcap" = some (.int 64 (BitVec.ofNat 64 dstcap)))
    (hev : lookupName env "%ev" = some (.ptr ev))
    (hnev : lookupName env "%nev" = some (.ptr nev))
    (hevcap : lookupName env "%evcap" = some (.int 64 (BitVec.ofNat 64 evcap)))
    (hjne : nep < 2 ^ 64) (hjnxp : nxp < 2 ^ 64) (hjdc : dstcap < 2 ^ 64)
    (hjv1 : v1 < 2 ^ 64) (hjv2 : v2 < 2 ^ 64) (hjecap : evcap < 2 ^ 64)
    (hs1 : ndst + 8 ≤ sAddr ∨ sAddr + 120 ≤ ndst)
    (hz1 : ndst + 8 ≤ zAddr ∨ zAddr + 64 ≤ ndst)
    (hs2 : nev + 8 ≤ sAddr ∨ sAddr + 120 ≤ nev)
    (hz2 : nev + 8 ≤ zAddr ∨ zAddr + 64 ≤ nev)
    (hnd : readBytes m ndst 8 = some (natToBytes v1 8))
    (hnev' : readBytes m nev 8 = some (natToBytes v2 8)) :
    denoteCode (stage2Calls stage2SubCalls) (walkEntrySeg2 ++ is) (stateAt env (memAt s m)) =
      denoteCode (stage2Calls stage2SubCalls) is
        (stateAt (walkEntryEnv2 env sAddr zAddr nep xp nxp dst v1 v2 ev)
          (memAt s (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
            (walkSeg2InitMem sAddr b ep n nb m)))) := by
  have h1 : readBytes (walkSeg2Mem1 sAddr zAddr nep xp nxp dst
        (walkSeg2InitMem sAddr b ep n nb m)) ndst 8 = some (natToBytes v1 8) :=
    walkSeg2Read1 (m := m) (n := n) (nb := nb) hs1 hz1 hnd
  have h2 : readBytes (walkSeg2Mem2 sAddr zAddr nep xp nxp dst v1 dstcap ev
        (walkSeg2InitMem sAddr b ep n nb m)) nev 8 = some (natToBytes v2 8) :=
    walkSeg2Read2 (m := m) (n := n) (nb := nb) hs2 hz2 hnev'
  simp only [walkEntrySeg2, List.cons_append, List.nil_append]
  rw [walkMemS2Init (env := env) (s := s) (m := m) (sAddr := sAddr) (b := b) (ep := ep)
    (n := n) (nb := nb) hs hb hn hnb hep]
  rw [denoteCode_gep8_lit_w (d := "%nsp") (base := "%s") (a := sAddr)
    (n := BitVec.ofNat 64 56) (hpos := by decide)]
  rw [walkMemStore64 (v := "%nep") (p := "%nsp") (a := sAddr + woff 56) (j := nep) (hj := hjne)]
  rw [denoteCode_gep8_lit_w (d := "%xp1") (base := "%s") (a := sAddr)
    (n := BitVec.ofNat 64 72) (hpos := by decide)]
  rw [walkMemStorePtr (v := "%xp") (p := "%xp1") (q := xp) (a := sAddr + woff 72)]
  rw [denoteCode_gep8_lit_w (d := "%nxp2") (base := "%s") (a := sAddr)
    (n := BitVec.ofNat 64 80) (hpos := by decide)]
  rw [walkMemStore64 (v := "%nxp") (p := "%nxp2") (a := sAddr + woff 80) (j := nxp) (hj := hjnxp)]
  rw [denoteCode_gep8_lit_w (d := "%hash1.i.i") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 32) (hpos := by decide)]
  rw [denoteCode_gep8_lit_w (d := "%ar") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 40) (hpos := by decide)]
  rw [denoteCode_gep8_lit_w (d := "%0") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 24) (hpos := by decide)]
  rw [walkMemMemset (sub := stage2SubCalls) (p := "%0") (a := zAddr + woff 24) (nz := 16)]
  rw [walkMemStorePtr (v := "%dst") (p := "%ar") (q := dst) (a := zAddr + woff 40)]
  rw [walkMemLoad64 (d := "%1") (p := "%ndst") (a := ndst) (v := BitVec.ofNat 64 v1)
    (hv := by rw [walkToNat_ofNat64 hjv1]; exact h1)]
  rw [denoteCode_gep8_lit_w (d := "%alen") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 48) (hpos := by decide)]
  rw [walkMemStore64 (v := "%1") (p := "%alen") (a := zAddr + woff 48) (j := v1) (hj := hjv1)]
  rw [denoteCode_gep8_lit_w (d := "%acap") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 56) (hpos := by decide)]
  rw [walkMemStore64 (v := "%dstcap") (p := "%acap") (a := zAddr + woff 56) (j := dstcap)
    (hj := hjdc)]
  rw [walkMemStorePtr (v := "%ev") (p := "%z") (q := ev) (a := zAddr)]
  rw [walkMemLoad64 (d := "%2") (p := "%nev") (a := nev) (v := BitVec.ofNat 64 v2)
    (hv := by rw [walkToNat_ofNat64 hjv2]; exact h2)]
  rw [denoteCode_gep8_lit_w (d := "%len") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 8) (hpos := by decide)]
  rw [walkMemStore64 (v := "%2") (p := "%len") (a := zAddr + woff 8) (j := v2) (hj := hjv2)]
  rw [denoteCode_gep8_lit_w (d := "%cap") (base := "%z") (a := zAddr)
    (n := BitVec.ofNat 64 16) (hpos := by decide)]
  rw [walkMemStore64 (v := "%evcap") (p := "%cap") (a := zAddr + woff 16) (j := evcap)
    (hj := hjecap)]
  all_goals first
    | rfl
    | (repeat rw [lookupName_cons_ne _ _ (by decide)]
       first
       | exact hs | exact hb | exact hn | exact hnb | exact hep | exact hz | exact hne
       | exact hxp | exact hnxp | exact hdst | exact hndst | exact hdcap | exact hev
       | exact hnev | exact hevcap
       | (rw [lookupName_cons_self] <;> rfl))

/-- A lookup at a run's accumulated environment: the environment's own builders
are unfolded first, so the peel is over a cons chain and not over a `cells`
application whose delta the rewrite would repeat once per cell. -/
macro "walk_env_lk" : tactic => `(tactic|
  (try dsimp only [walkEntryEnv1, walkEntryEnv2, walkEntryEnv3, walkEntryEnv4]
   simp (config := { failIfUnchanged := false }) only [cells]
   repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
   | assumption
   | (rw [lookupName_cons_self] <;> rfl)))

/-! ### The block's run: the four segments composed

The composition needs four things beyond the segments themselves: segment 1 in
the `memAt` form segment 2's statement asks for, the record's three argument
fields read back at the memory the run leaves, the cursor record's and the
zeroed slots' memories named once, and the associativity that turns the pinned
`walkEntryInstrs_segments` into the order the segments are applied in.

`readBytes_stage2WriteStores_at` is the read the record's fields need: a store
list split as `pre ++ (a, bs) :: post` reads `bs` back at `a`, whatever `pre`
is, because the write at `a` is the last one the read sees; `post` is the half
that must lie outside.  The initialisation's fifteen stores are split that way
for `%s->b`, `%s->n` and `%s->ep`, and then carried across segment 2's own store
list — outside all three ranges, since those lie in `[%s, %s + 56)` and segment
2 writes only `[%s + 56, %s + 88)` and the log. -/

/-- A store list whose entry at `a` is the last to cover `a` reads back its
bytes there. -/
theorem readBytes_stage2WriteStores_at (m : Mem) (pre post : List (Nat × List UInt8))
    (a : Nat) (bs : List UInt8)
    (hpost : ∀ st ∈ post, a + bs.length ≤ st.1 ∨ st.1 + st.2.length ≤ a) :
    readBytes (stage2WriteStores m (pre ++ (a, bs) :: post)) a bs.length = some bs := by
  rw [stage2WriteStores_append,
    show (a, bs) :: post = [(a, bs)] ++ post from rfl, stage2WriteStores_append,
    readBytes_stage2WriteStores_of_all_outside post hpost]
  exact readBytes_writeBytes_same (stage2WriteStores m pre) bs

/-- **The record's first field**, `%s->b`, read back at the initialised memory. -/
theorem readBytes_s2Init_b (m : Mem) (sv b n nb ep : Nat) :
    readBytes (stage2WriteStores m (s2InitStores sv b n nb ep)) sv 8 = some (wordBytes 8 b) := by
  have hpost : ∀ st ∈ (s2InitStores sv b n nb ep).drop 1,
      sv + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sv := by
    intro st hst
    simp only [s2InitStores, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals (simp only [wordBytes, natToBytes_length]; omega)
  rw [show s2InitStores sv b n nb ep =
      [] ++ (sv, wordBytes 8 b) :: (s2InitStores sv b n nb ep).drop 1 from rfl]
  exact readBytes_stage2WriteStores_at m [] _ sv (wordBytes 8 b) hpost

/-- **The record's second field**, `%s->n`. -/
theorem readBytes_s2Init_n (m : Mem) (sv b n nb ep : Nat) :
    readBytes (stage2WriteStores m (s2InitStores sv b n nb ep)) (sv + 8) 8 =
      some (wordBytes 8 n) := by
  have hpost : ∀ st ∈ (s2InitStores sv b n nb ep).drop 2,
      sv + 8 + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sv + 8 := by
    intro st hst
    simp only [s2InitStores, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [wordBytes, natToBytes_length]; omega)
  rw [show s2InitStores sv b n nb ep =
      [(sv, wordBytes 8 b)] ++ (sv + 8, wordBytes 8 n) ::
        (s2InitStores sv b n nb ep).drop 2 from rfl]
  exact readBytes_stage2WriteStores_at m _ _ (sv + 8) (wordBytes 8 n) hpost

/-- **The record's fifth field**, `%s->ep`. -/
theorem readBytes_s2Init_ep (m : Mem) (sv b n nb ep : Nat) :
    readBytes (stage2WriteStores m (s2InitStores sv b n nb ep)) (sv + 48) 8 =
      some (wordBytes 8 ep) := by
  have hpost : ∀ st ∈ (s2InitStores sv b n nb ep).drop 7,
      sv + 48 + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sv + 48 := by
    intro st hst
    simp only [s2InitStores, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [wordBytes, natToBytes_length]; omega)
  rw [show s2InitStores sv b n nb ep =
      (s2InitStores sv b n nb ep).take 6 ++ (sv + 48, wordBytes 8 ep) ::
        (s2InitStores sv b n nb ep).drop 7 from rfl]
  exact readBytes_stage2WriteStores_at m _ _ (sv + 48) (wordBytes 8 ep) hpost

/-- **The record's first field survives the second segment.** -/
theorem walkSeg2ReadRecord_b {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64}
    (hzs : sAddr + 120 ≤ zAddr ∨ zAddr + 64 ≤ sAddr) :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) sAddr 8 = some (wordBytes 8 b) := by
  have hout : ∀ st ∈ walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap,
      sAddr + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sAddr := by
    intro st hst
    rcases walkSeg2StoreWindow sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap st hst with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rcases hzs with h | h <;> omega
  rw [walkSeg2PostMem_eq, walkSeg2InitMem,
    readBytes_stage2WriteStores_of_all_outside _ hout, readBytes_s2Init_b]

/-- **The record's second field survives the second segment.** -/
theorem walkSeg2ReadRecord_n {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64}
    (hzs : sAddr + 120 ≤ zAddr ∨ zAddr + 64 ≤ sAddr) :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (sAddr + 8) 8 = some (wordBytes 8 n.toNat) := by
  have hout : ∀ st ∈ walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap,
      sAddr + 8 + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sAddr + 8 := by
    intro st hst
    rcases walkSeg2StoreWindow sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap st hst with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rcases hzs with h | h <;> omega
  rw [walkSeg2PostMem_eq, walkSeg2InitMem,
    readBytes_stage2WriteStores_of_all_outside _ hout, readBytes_s2Init_n]

/-- **The record's fifth field survives the second segment.** -/
theorem walkSeg2ReadRecord_ep {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64}
    (hzs : sAddr + 120 ≤ zAddr ∨ zAddr + 64 ≤ sAddr) :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (sAddr + 48) 8 = some (wordBytes 8 ep) := by
  have hout : ∀ st ∈ walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap,
      sAddr + 48 + 8 ≤ st.1 ∨ st.1 + st.2.length ≤ sAddr + 48 := by
    intro st hst
    rcases walkSeg2StoreWindow sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap st hst with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rcases hzs with h | h <;> omega
  rw [walkSeg2PostMem_eq, walkSeg2InitMem,
    readBytes_stage2WriteStores_of_all_outside _ hout, readBytes_s2Init_ep]

/-- Segment 1 in the `memAt` form: it writes no memory, so the updater is the
one it was handed. -/
theorem walkEntrySeg1_denote_mem (sub : Calls) (env : Env) (s : State) (m : Mem)
    (is : List Instr) {n sAddr zAddr eAddr : Nat}
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hz : lookupName env "%z" = some (.ptr zAddr))
    (he : lookupName env "%e" = some (.ptr eAddr)) :
    denoteCode (stage2Calls sub) (walkEntrySeg1 ++ is) (stateAt env (memAt s m)) =
      denoteCode (stage2Calls sub) is
        (stateAt (walkEntryEnv1 env s.next n) (memAt { s with next := s.next + 28 } m)) := by
  rw [walkEntrySeg1_denote (sub := sub) (env := env) (s := memAt s m) (is := is) hn hs hz he]
  rfl

/-- **The first two segments.**  The allocation and the block count, then the
initialisation, the record's fields, the log's fields and the two cursor loads.
The second segment's `%shr` argument is the block count segment 1 computed. -/
theorem walkEntrySeg12_denote (env : Env) (s : State) (m : Mem) (is : List Instr)
    {n sAddr zAddr eAddr b ep nep xp nxp dst dstcap ev ndst nev v1 v2 evcap : Nat}
    (hb64 : b < 2 ^ 64)
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hz : lookupName env "%z" = some (.ptr zAddr))
    (he : lookupName env "%e" = some (.ptr eAddr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hne : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 nxp)))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hndst : lookupName env "%ndst" = some (.ptr ndst))
    (hdcap : lookupName env "%dstcap" = some (.int 64 (BitVec.ofNat 64 dstcap)))
    (hev : lookupName env "%ev" = some (.ptr ev))
    (hnev : lookupName env "%nev" = some (.ptr nev))
    (hevcap : lookupName env "%evcap" = some (.int 64 (BitVec.ofNat 64 evcap)))
    (hjne : nep < 2 ^ 64) (hjnxp : nxp < 2 ^ 64) (hjdc : dstcap < 2 ^ 64)
    (hjv1 : v1 < 2 ^ 64) (hjv2 : v2 < 2 ^ 64) (hjecap : evcap < 2 ^ 64)
    (hs1 : ndst + 8 ≤ sAddr ∨ sAddr + 120 ≤ ndst)
    (hz1 : ndst + 8 ≤ zAddr ∨ zAddr + 64 ≤ ndst)
    (hs2 : nev + 8 ≤ sAddr ∨ sAddr + 120 ≤ nev)
    (hz2 : nev + 8 ≤ zAddr ∨ zAddr + 64 ≤ nev)
    (hnd : readBytes m ndst 8 = some (natToBytes v1 8))
    (hnev' : readBytes m nev 8 = some (natToBytes v2 8)) :
    denoteCode (stage2Calls stage2SubCalls) (walkEntrySeg1 ++ walkEntrySeg2 ++ is)
        (stateAt env (memAt s m)) =
      denoteCode (stage2Calls stage2SubCalls) is
        (stateAt (walkEntryEnv2 (walkEntryEnv1 env s.next n) sAddr zAddr nep xp nxp dst v1 v2 ev)
          (memAt { s with next := s.next + 28 }
            (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
              (walkSeg2InitMem sAddr b ep (BitVec.ofNat 64 n)
                ((BitVec.ofNat 64 n + BitVec.ofNat 64 63) >>> 6) m)))) := by
  rw [List.append_assoc]
  rw [walkEntrySeg1_denote_mem (sub := stage2SubCalls) (env := env) (s := s) (m := m)
    (is := walkEntrySeg2 ++ is) hn hs hz he]
  rw [walkEntrySeg2_denote (env := walkEntryEnv1 env s.next n)
    (s := { s with next := s.next + 28 }) (m := m) (is := is) (n := BitVec.ofNat 64 n)
    (nb := (BitVec.ofNat 64 n + BitVec.ofNat 64 63) >>> 6)
    (sAddr := sAddr) (b := b) (ep := ep) (zAddr := zAddr) (nep := nep) (xp := xp)
    (nxp := nxp) (dst := dst) (dstcap := dstcap) (ev := ev) (ndst := ndst) (nev := nev)
    (v1 := v1) (v2 := v2) (evcap := evcap)
    (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk)
    (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk) (by walk_env_lk)
    (by walk_env_lk) (by walk_env_lk) (by walk_env_lk)
    hjne hjnxp hjdc hjv1 hjv2 hjecap hs1 hz1 hs2 hz2 hnd hnev']

/-- **The last two segments.**  The record's fields read back out of the `S2`
record, the cursor record's memset and five stores, then the three markers, the
two zeroed slots and the entry count's test. -/
theorem walkEntrySeg34_denote (sub : Calls) (env : Env) (s : State)
    {b n ep nep eAddr sAddr cAddr ctypeAddr cstAddr rootAddr xjAddr : Nat}
    (hb64 : b < 2 ^ 64) (hn64 : n < 2 ^ 64) (hep64 : ep < 2 ^ 64)
    (hne64 : nep < 2 ^ 64) (hb0 : 0 < b)
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hc : lookupName env "%c.i" = some (.ptr cAddr))
    (he : lookupName env "%e" = some (.ptr eAddr))
    (hne : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hct : lookupName env "%ctype.i" = some (.ptr ctypeAddr))
    (hcs : lookupName env "%cst.i" = some (.ptr cstAddr))
    (hr : lookupName env "%root_done.i" = some (.ptr rootAddr))
    (hx : lookupName env "%xj.i" = some (.ptr xjAddr))
    (h3r : readBytes s.mem sAddr 8 = some (natToBytes b 8))
    (h4r : readBytes s.mem (sAddr + woff 8) 8 = some (natToBytes n 8))
    (h5r : readBytes s.mem (sAddr + woff 48) 8 = some (natToBytes ep 8)) :
    denoteCode (stage2Calls sub) (walkEntrySeg3 ++ walkEntrySeg4) (stateAt env s) =
      denoteCode (stage2Calls sub) []
        (stateAt (walkEntryEnv4 (walkEntryEnv3 env b n ep sAddr cAddr) b nep)
          { s with mem := (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes s.mem (cAddr + woff 40) (List.replicate 1152 0)) cAddr (natToBytes b 8)) (cAddr + woff 8) (natToBytes n 8)) (cAddr + woff 16) (natToBytes ep 8)) (cAddr + woff 24) (natToBytes nep 8)) (cAddr + woff 1112) (natToBytes eAddr 8)) rootAddr (natToBytes 0 4)) xjAddr (natToBytes 0 8)) }) := by
  rw [walkEntrySeg3_denote (sub := sub) (env := env) (s := s) (is := walkEntrySeg4)
    (b := b) (n := n) (ep := ep) (nep := nep) (eAddr := eAddr) (sAddr := sAddr)
    (cAddr := cAddr) hb64 hn64 hep64 hne64 hs hc he hne h3r h4r h5r]
  rw [show walkEntrySeg4 = walkEntrySeg4 ++ ([] : List Instr) from (List.append_nil _).symm]
  rw [walkEntrySeg4_denote (sub := sub) (env := walkEntryEnv3 env b n ep sAddr cAddr)
    (s := { s with mem := (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes (writeBytes s.mem (cAddr + woff 40) (List.replicate 1152 0)) cAddr (natToBytes b 8)) (cAddr + woff 8) (natToBytes n 8)) (cAddr + woff 16) (natToBytes ep 8)) (cAddr + woff 24) (natToBytes nep 8)) (cAddr + woff 1112) (natToBytes eAddr 8)) })
    (is := []) (b := b) (nep := nep) (ctypeAddr := ctypeAddr) (cstAddr := cstAddr)
    (rootAddr := rootAddr) (xjAddr := xjAddr) hb0 (by walk_env_lk) (by walk_env_lk) (by walk_env_lk)
    (by walk_env_lk) (by walk_env_lk) (by walk_env_lk)]

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_stage2WriteStores_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_stage2WriteStores_at

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_s2Init_b' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_s2Init_b

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_s2Init_n' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_s2Init_n

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_s2Init_ep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_s2Init_ep

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg1_denote_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg1_denote_mem

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg12_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg12_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg34_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg34_denote


/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntrySeg2_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntrySeg2_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2StoreWindow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2StoreWindow

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_eq

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2Read1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2Read1

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2Read2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2Read2

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
