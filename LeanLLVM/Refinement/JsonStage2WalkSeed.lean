/-
The stage-2 walk's seed: `entry`, its preheader, and the header.

`WalkSeedState` (`JsonStage2WalkScope`) is the state at the loop head: the two
`phi` values, the six pointer registers, the log's four fields, the initialisation
`memset`'s zeroed hash word, the staging's presence, and the frame.  This module
produces it: `entry`'s fifty-seven instructions, `while.body.i.lr.ph`'s five
`getelementptr`s and `while.body.i`'s two `phi`s, two loads and cursor store.

The block lists are transcribed from the pinned body and pinned by `_find`, so
the runs below are about `stage2Body` rather than about a paraphrase.  The steps
the rest of the tree does not have are here: the `alloca` step (it moves the
allocator cursor), the pointer store, the 32- and 64-bit immediate stores, the
signed `getelementptr` at `-1` (the header's unused `%invariant.gep`), and the
two `memset`s and `s2_init`, whose memories are the model's own.

The seed needs two facts `stage2Pre` does not state, both recorded here rather
than assumed away: `0 < b`, because `%invariant.gep` is `%3 - 1` and the
semantics refuses a displacement past the base; and `0 < nep`, because `entry`
branches to `if.then492.i` when the entry count is zero.

The register carriers are `WalkInv` fields (`WalkRegs`, `WalkIter`), and this
module is where their *production* belongs: `WalkSeedState` asks for them, and
the run that would establish it — `entry`'s fifty-seven instructions, the
preheader's five `getelementptr`s and the header's first pass — is the open row.
The step vocabulary below is what that run is built from: the `alloca`, the
pointer and immediate stores, the signed `getelementptr` at `-1`, the two
`memset`s and `s2_init`.  `JsonStage2WalkRun` states `entry`'s own run as four
segments, all four proved as `denoteCode` equalities at a symbolic environment,
state and memory, with the cut pinned to this module's `walkEntryInstrs` by an
`rfl`.  The fourth — the initialisation and the twenty-two instructions after it
— is stated over this module's `memAt`, which is what keeps it linear: the
structure-literal form of `denoteCode`'s step conclusion repeats the previous
state in the four fields the step does not touch, so the chain of twenty-two
diverged at `maxHeartbeats 4000000`.  `memAt` makes the memory an argument of
each conclusion, and the run of twenty-three steps then elaborates in a
three-second module.  The step vocabulary below is that form of the steps the
rest of the tree does not have (`walkMemStore64`, `walkMemStorePtr`,
`walkMemMemset`, `walkMemLoad64`, `walkMemS2Init`), and it is what any longer
straight-line run in this walk must be built from.

The block's own run is `walkEntry_denote`: one equality over all four segments,
with segment 3 and segment 4 restated at their own memory variable
(`walkEntrySeg3_denote_mem`, `walkEntrySeg4_denote_mem`) so that the close meets
the named folds `walkSeg3PostMem`/`walkSeg4PostMem` rather than reducing the
cursor record's 1152-byte memset — that module's census carries the measurement
and the shape.  `JsonStage2WalkSeedRun` reads it: the entry block's step in both
arms of its test, the preheader's and the header's first pass, their `runFuel`
prefixes, the environment and memory clauses of `WalkSeedState`, and its last
three rows: `WalkIter`, the staged objects' presence and the frame
(`walkSeedState`, `walkSeedState_geometry`).  What remains below the seed is what
`JsonStage2WalkScope`'s census names: the stack map and the completion arc.
-/
import LeanLLVM.Refinement.JsonStage2WalkCall

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

namespace WalkScope

/-! ### The two block lists -/

/-- `entry`'s instruction list, as the pinned body writes it. -/
def walkEntryInstrs : List Instr := [
  Instr.alloca "%ei.i" (Ty.int 64) 0,
  Instr.alloca "%root_done.i" (Ty.int 32) 0,
  Instr.alloca "%xj.i" (Ty.int 64) 0,
  Instr.alloca "%outn.i" (Ty.int 64) 0,
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (Operand.reg "%s"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (Operand.reg "%z"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
  Instr.binop "%add" BinOp.add 64 (Operand.reg "%n") (Operand.imm (.int 64 (BitVec.ofNat 64 63))),
  Instr.binop "%shr" BinOp.lshr 64 (Operand.reg "%add") (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
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
  Instr.store (Ty.int 64) (Operand.reg "%evcap") (Operand.reg "%cap"),
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
  Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e7.i"),
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%ctype.i"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%cst.i"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), (Ty.ptr, (Operand.reg "%root_done.i"))],
  Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 0))) (Operand.reg "%root_done.i"),
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj.i"))],
  Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%xj.i"),
  Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%3") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
  Instr.icmp "%cmp.i247.not" IPred.eq 64 (Operand.reg "%nep") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))]

/-- `entry`, pinned: the block the run below is about. -/
def walkEntryBlock : Block :=
  { name := "entry", instrs := walkEntryInstrs,
    term := Term.condbr (Operand.reg "%cmp.i247.not") "if.then492.i" "while.body.i.lr.ph" }

theorem walkEntryBlock_find : stage2Body.findBlock "entry" = some walkEntryBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkEntryBlock, walkEntryInstrs]

/-- `while.body.i.lr.ph`'s instruction list, as the pinned body writes it. -/
def walkPreheaderInstrs : List Instr := [
  Instr.gep "%k11.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
  Instr.gep "%h1.i.i.i51" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
  Instr.gep "%gap.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 20))),
  Instr.gep "%end.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
  Instr.gep "%kind404.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16)))]

/-- The preheader, pinned. -/
def walkPreheaderBlock : Block :=
  { name := "while.body.i.lr.ph", instrs := walkPreheaderInstrs,
    term := Term.br "while.body.i" }

theorem walkPreheaderBlock_find :
    stage2Body.findBlock "while.body.i.lr.ph" = some walkPreheaderBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkPreheaderBlock,
    walkPreheaderInstrs]

/-! ### The steps the rest of the tree does not have -/

/-- An `alloca`: it binds a pointer to the allocator's cursor and advances it by
the type's size.  Nothing is written. -/
theorem denoteCode_alloca (calls : Calls) (env : Env) (s : State) (d : String)
    (ty : Ty) (align : Nat) (is : List Instr) :
    denoteCode calls (.alloca d ty align :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr s.next) :: env) { s with next := s.next + ty.sizeBytes }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by simp only [evalInstr, stateAt]; rfl)]
  simp only [stateAt]

/-- A store of a pointer word. -/
theorem denoteCode_storePtr (calls : Calls) (env : Env) (s : State) (v p : String)
    {q a : Nat}
    (hv : lookupName env v = some (.ptr q))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store Ty.ptr (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes q 8) }) := by
  have hs : storeValue (stateAt env s) Ty.ptr (.ptr q) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes q 8) }) := by
    simp [storeValue, stateAt]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .ptr q) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes q 8) })
      (hv := evalOperand_reg_of env s v (.ptr q) hv)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- A store of a 32-bit immediate. -/
theorem denoteCode_store32_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 32) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.imm (.int 32 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hs : storeValue (stateAt env s) (.int 32) (.int 32 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [storeValue, stateAt, show (32 + 7) / 8 = 4 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 32 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
      (hv := evalOperand_lit_of (stateAt env s) 32 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- A store of a 64-bit immediate. -/
theorem denoteCode_store64_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 64) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hs : storeValue (stateAt env s) (.int 64) (.int 64 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    simp [storeValue, stateAt, show (64 + 7) / 8 = 8 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 64 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
      (hv := evalOperand_lit_of (stateAt env s) 64 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- The signed `getelementptr i8` at `-1`: the backward accepting case, which is
what `entry`'s unused `%invariant.gep` is.  It needs the base to be positive. -/
theorem denoteCode_gep8_lit_back_one (calls : Calls) (env : Env) (s : State)
    (d base : String) {a : Nat}
    (hb : lookupName env base = some (.ptr a)) (ha : 0 < a) (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a - 1)) :: env) s) := by
  have hconst : 2 ^ 64 - (BitVec.signExtend 64
      (BitVec.ofNat 64 18446744073709551615)).toNat = 1 := by decide
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [evalInstr_gep_back (s := stateAt env s)
      (hb := evalOperand_reg_of env s base (.ptr a) hb)
      (ho := evalOperand_lit_of (stateAt env s) 64 (BitVec.ofNat 64 18446744073709551615))
      (hneg := by decide) (hk := by
        rw [hconst, show (Ty.int 8).sizeBytes = 1 from rfl]
        exact ha)])]
  simp only [stateAt, State.bind, hconst, Nat.mul_one,
    show Ty.sizeBytes (Ty.int 8) = 1 from rfl]

/-- A lifetime marker writes nothing and allocates nothing. -/
theorem denoteCode_lifetime (sub : Calls) (env : Env) (s : State)
    (callee : String) (hcallee : callee = "llvm.lifetime.start.p0"
      ∨ callee = "llvm.lifetime.end.p0")
    {args : List (Ty × Operand)} {vs : List Value}
    (ha : evalOperands (stateAt env s) args = some vs) (is : List Instr) :
    denoteCode (stage2Calls sub) (.callVoid callee args :: is) (stateAt env s) =
      denoteCode (stage2Calls sub) is (stateAt env s) := by
  have hc : stage2Calls sub callee vs s.mem s.next
      = some { ret := .int 1 0, mem := s.mem, next := s.next } := by
    rcases hcallee with rfl | rfl <;> rfl
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := callee) ha hc]

/-- A `memset(p, 0, n)` with a register base and literal count. -/
theorem denoteCode_memset (sub : Calls) (env : Env) (s : State) (p : String)
    {a nz : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2Calls sub)
        (.callVoid "llvm.memset.p0.i64"
          [(Ty.ptr, (Operand.reg p)), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))),
           ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 nz)))),
           ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] :: is)
        (stateAt env s) =
      denoteCode (stage2Calls sub) is
        (stateAt env { s with mem := writeBytes s.mem a (List.replicate (BitVec.ofNat 64 nz).toNat 0) }) := by
  have ha : evalOperands (stateAt env s)
      [(Ty.ptr, (Operand.reg p)), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))),
       ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 nz)))),
       ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] =
      some [.ptr a, .int 8 (BitVec.ofNat 8 0), .int 64 (BitVec.ofNat 64 nz),
        .int 1 (BitVec.ofNat 1 0)] := by
    simp [evalOperands, evalOperand, Const.toValue, stateAt, hp]
  have hc : stage2Calls sub "llvm.memset.p0.i64"
      [.ptr a, .int 8 (BitVec.ofNat 8 0), .int 64 (BitVec.ofNat 64 nz),
        .int 1 (BitVec.ofNat 1 0)] s.mem s.next =
      some { ret := .int 1 0,
             mem := writeBytes s.mem a (List.replicate (BitVec.ofNat 64 nz).toNat 0),
             next := s.next } := rfl
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub) (env := env) (s := s)
    (callee := "llvm.memset.p0.i64") ha hc]

/-- `s2_init`, at the five arguments the block passes. -/
theorem denoteCode_s2_init (env : Env) (s : State)
    {sAddr b ep : Nat} {n nb : BitVec 64}
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnb : lookupName env "%shr" = some (.int 64 nb))
    (hep : lookupName env "%ep" = some (.ptr ep)) (is : List Instr) :
    denoteCode (stage2Calls stage2SubCalls)
        (.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")),
          ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")),
          (Ty.ptr, (Operand.reg "%ep"))] :: is)
        (stateAt env s) =
      denoteCode (stage2Calls stage2SubCalls) is
        (stateAt env { s with mem := stage2WriteStores s.mem (s2InitStores sAddr b n.toNat nb.toNat ep) }) := by
  have ha : evalOperands (stateAt env s)
      [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")),
       ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")),
       (Ty.ptr, (Operand.reg "%ep"))] =
      some [.ptr sAddr, .ptr b, .int 64 n, .int 64 nb, .ptr ep] := by
    simp [evalOperands, evalOperand, stateAt, hs, hb, hn, hnb, hep]
  -- the five-argument list is `stage2Init`'s, which is the model's answer
  have hc5 : stage2Calls stage2SubCalls "s2_init" [.ptr sAddr, .ptr b, .int 64 n, .int 64 nb,
      .ptr ep] s.mem s.next =
      some { ret := voidRet,
             mem := stage2WriteStores s.mem (s2InitStores sAddr b n.toNat nb.toNat ep),
             next := s.next } := by
    rw [stage2Calls_s2_init]
    rfl
  rw [walkDenoteCode_callVoid (calls := stage2Calls stage2SubCalls) (env := env) (s := s)
    (callee := "s2_init") ha hc5]

/-! ### The step vocabulary with a memory-only updater

`denoteCode`'s conclusion for one step is stated against a state *literal*,
`{ s with mem := … }`.  Chained, that conclusion repeats the previous state
literal in every field the step does not touch, so the term a run of `n` stores
builds grows as `4 ^ n`: the entry block's twenty-two post-initialisation
instructions are twenty-two stores, gepe and loads, and their direct chain
diverges at `whnf` at `maxHeartbeats 4000000`.  A step stated over `memAt s m`
threads the memory as an argument of its own and leaves the state a single atom,
so the run composes linearly: each conclusion is `memAt s (writeBytes m …)` and
the closing `rfl` reduces a chain of projections rather than a tree of
literals.  The two rewrite facts are `rfl`, and they are what keeps the chain
flat. -/

/-- A state seen as its memory, and nothing else. -/
def memAt (s : State) (m : Mem) : State := { s with mem := m }

/-- The memory a `memAt` state carries. -/
theorem memAt_mem (s : State) (m : Mem) : (memAt s m).mem = m := rfl

/-- Two updaters are the later one: the first is overwritten, not nested. -/
theorem memAt_memAt (s : State) (m m' : Mem) : memAt (memAt s m) m' = memAt s m' := rfl

/-- A 64-bit store, at the incoming memory. -/
theorem walkMemStore64 (calls : Calls) (env : Env) (s : State) (m : Mem) (v p : String)
    {a j : Nat}
    (hv : lookupName env v = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 64) (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.reg v) (.reg p) :: is) (stateAt env (memAt s m)) =
      denoteCode calls is (stateAt env (memAt s (writeBytes m a (wordBytes 8 j)))) := by
  rw [denoteCode_store64_ofNat (calls := calls) (env := env) (s := memAt s m) (v := v)
    (p := p) (a := a) (j := j) hv hj hp is, memAt_mem]
  rfl

/-- A pointer store, at the incoming memory. -/
theorem walkMemStorePtr (calls : Calls) (env : Env) (s : State) (m : Mem) (v p : String)
    {q a : Nat}
    (hv : lookupName env v = some (.ptr q))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store Ty.ptr (.reg v) (.reg p) :: is) (stateAt env (memAt s m)) =
      denoteCode calls is (stateAt env (memAt s (writeBytes m a (natToBytes q 8)))) := by
  rw [denoteCode_storePtr (calls := calls) (env := env) (s := memAt s m) (v := v) (p := p)
    (q := q) (a := a) hv hp is, memAt_mem]
  rfl

/-- A `memset`, at the incoming memory. -/
theorem walkMemMemset (sub : Calls) (env : Env) (s : State) (m : Mem) (p : String)
    {a nz : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2Calls sub)
        (.callVoid "llvm.memset.p0.i64"
          [(Ty.ptr, (Operand.reg p)), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))),
           ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 nz)))),
           ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] :: is)
        (stateAt env (memAt s m)) =
      denoteCode (stage2Calls sub) is
        (stateAt env (memAt s (writeBytes m a (List.replicate (BitVec.ofNat 64 nz).toNat 0)))) := by
  rw [denoteCode_memset (sub := sub) (env := env) (s := memAt s m) (p := p) (a := a)
    (nz := nz) hp is, memAt_mem]
  rfl

/-- A 64-bit load, read at the incoming memory. -/
theorem walkMemLoad64 (calls : Calls) (env : Env) (s : State) (m : Mem) (d p : String)
    {a : Nat} {v : BitVec 64}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes m a 8 = some (natToBytes v.toNat 8)) (is : List Instr) :
    denoteCode calls (.load d (.int 64) (.reg p) :: is) (stateAt env (memAt s m)) =
      denoteCode calls is (stateAt ((d, .int 64 v) :: env) (memAt s m)) := by
  rw [denoteCode_load64 (calls := calls) (env := env) (s := memAt s m) (d := d) (p := p)
    (a := a) (v := v) hp (by rw [memAt_mem]; exact hv) is]

/-- `s2_init`, at the incoming memory. -/
theorem walkMemS2Init (env : Env) (s : State) (m : Mem)
    {sAddr b ep : Nat} {n nb : BitVec 64}
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hnb : lookupName env "%shr" = some (.int 64 nb))
    (hep : lookupName env "%ep" = some (.ptr ep)) (is : List Instr) :
    denoteCode (stage2Calls stage2SubCalls)
        (.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")),
          ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")),
          (Ty.ptr, (Operand.reg "%ep"))] :: is)
        (stateAt env (memAt s m)) =
      denoteCode (stage2Calls stage2SubCalls) is
        (stateAt env (memAt s (stage2WriteStores m (s2InitStores sAddr b n.toNat nb.toNat ep)))) := by
  rw [denoteCode_s2_init (env := env) (s := memAt s m) (sAddr := sAddr) (b := b) (ep := ep)
    (n := n) (nb := nb) hs hb hn hnb hep is, memAt_mem]
  rfl

/-! ### The initialisation's writes are inside the record

`entry` calls `s2_init`, whose fifteen stores are the `S2` record at `%s`
(`s2InitStores`: `s + 0` through `s + 112`, eight bytes each).  Every read after
the initialisation — the document's byte, the entry stream's lane, the log's
fields — is therefore unchanged, provided it lies outside `[s, s + 120)`.  This
is the read-over-write fact the seed's production needs: the predecessor's
blocker was that the `%7`/`%8` loads read the document through the fifteen
stores, and the staging separates the record from the document and the entry
stream (`WalkGeom`'s separation). -/

/-- **A store list whose entries lie inside one window leaves a read outside it
alone**, for any base memory: the induction carries the memory, so each entry's
write is the next induction's base. -/
theorem readBytes_stage2WriteStores_of_outside :
    ∀ (stores : List (Nat × List UInt8)) {m : Mem} {sv a len : Nat},
      (∀ st ∈ stores, sv ≤ st.1 ∧ st.1 + st.2.length ≤ sv + 120) →
      (a + len ≤ sv ∨ sv + 120 ≤ a) →
      readBytes (stage2WriteStores m stores) a len = readBytes m a len
  | [], _, _, _, _, _, _ => rfl
  | (a', bs) :: rest, m, sv, a, len, hstep, h => by
      obtain ⟨hin1, hin2⟩ := hstep (a', bs) (by simp)
      simp only [Prod.snd] at hin2
      have hrest : ∀ st ∈ rest, sv ≤ st.1 ∧ st.1 + st.2.length ≤ sv + 120 :=
        fun st hst => hstep st (by simp [hst])
      have hout : a + len ≤ a' ∨ a' + bs.length ≤ a := by
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      show readBytes (stage2WriteStores (writeBytes m a' bs) rest) a len =
        readBytes m a len
      rw [readBytes_stage2WriteStores_of_outside rest (m := writeBytes m a' bs) hrest h]
      exact walkReadBytes_writeBytes_outside hout

/-- **A read outside the `S2` record survives `s2_init`.**  The fifteen stores are
`s + 0` through `s + 112`, eight bytes each. -/
theorem readBytes_s2Init_of_outside {m : Mem} {sv b n nb ep a len : Nat}
    (h : a + len ≤ sv ∨ sv + 120 ≤ a) :
    readBytes (stage2WriteStores m (s2InitStores sv b n nb ep)) a len =
      readBytes m a len := by
  refine readBytes_stage2WriteStores_of_outside (s2InitStores sv b n nb ep) ?_ h
  intro st hst
  simp only [s2InitStores, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [wordBytes, natToBytes_length]

/-! ### The traversal, stated conditionally

The completion conjunct of `Stage2WalkObligation` is `Stage2WalkCompletes`: at
the ABI's thirteen arguments the pinned body returns within `stage2Budget`.  The
loop proof is an arc, and this is its assembly point, stated with every premise
named and none assumed away:

* `hprefix` — the entry seed's run: from `EntryState`, `j` steps reach the loop
  head state `s0` and leave it exactly, for every further fuel;
* `hchain` — the dispatch as a `WalkChain` from the seed: one link per block, the
  thing the 165-block next-link lemma produces;
* `hsteps` — the chain's own step count, read as a fuel shift (`k` steps from
  `s0` are `k` steps, for every continuation); `WalkChain.steps` is what the
  traversal sitting discharges it with;
* `hret` — the last state's step returns;
* `hbudget` — the count against the record's allowance: the seed's `j` steps,
  the chain's `k`, and the return's one step fit the budget.

Nothing here proves any of the five; the theorem is what a proof of them buys,
and `Stage2WalkCompletes` follows from it once they are supplied. -/
theorem walkCompletes_of_prefix_chain {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (S : WalkStage G) {s s0 s' sret : State} {j k B : Nat}
    {v : Value}
    (hprefix : ∀ n, runFuel calls (j + n) stage2Body s = runFuel calls n stage2Body s0)
    (_hchain : WalkChain calls G (walkSeed G S) s0 (walkSeed G S) s')
    (hsteps : ∀ n, runFuel calls (k + n) stage2Body s0 = runFuel calls n stage2Body s')
    (hret : step calls stage2Body s' = .ret v sret)
    (hbudget : j + k + 1 ≤ B) :
    ∃ v' m, runFuel calls B stage2Body s = some (.ret v' m) := by
  have h1 : runFuel calls (k + 1) stage2Body s0 = some (.ret v sret.mem) := by
    rw [hsteps 1]
    simp only [runFuel, hret]
  have h2 : runFuel calls (j + (k + 1)) stage2Body s = some (.ret v sret.mem) := by
    rw [hprefix (k + 1)]
    exact h1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hbudget
  refine ⟨v, sret.mem, ?_⟩
  rw [hd]
  have hB : j + (k + 1) + d = j + k + 1 + d := by omega
  rw [← hB]
  exact runFuel_mono h2

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_stage2WriteStores_of_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_stage2WriteStores_of_outside

/-- info: 'LeanLLVM.Refinement.WalkScope.readBytes_s2Init_of_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.readBytes_s2Init_of_outside

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkRegs.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkRegs.of_run

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkIter.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkIter.of_run

/-- info: 'LeanLLVM.Refinement.WalkScope.walkCompletes_of_prefix_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_prefix_chain

end WalkScope

end LeanLLVM.Refinement
