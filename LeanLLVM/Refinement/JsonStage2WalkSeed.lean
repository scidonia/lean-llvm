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

/-! ### The two register carriers

The dispatch's blocks read registers the invariant does not bind, and the
traversal's successor hypotheses have to come from somewhere.  There are two
kinds, and they are different kinds:

* **static** registers, bound once by `entry` or `while.body.i.lr.ph` and never
  rebound.  Their values are fixed by the staging (the `%z`/`%s`/`%c.i`
  offsets, the document base's predecessor, and the four stack objects' slots
  at the call's cursor), so `WalkRegs` is a list of lookups, one entry each.
  `WalkRegs.of_run` is the whole preservation proof: a run that binds none of
  the names keeps every one of them, by `denoteCode_lookupName`.
* **per-iteration** registers, rebound by the header on every pass: `%7` is the
  entry stream's lane at the carried index and `%8` the document byte that lane
  selects.  Their values are functions of the carry's `k`, so the clause is
  stated at `entryPos G C.k` and `entryByte G C.k` rather than at a constant.
  `WalkIter.of_run` is the same preservation by freshness.

What is *not* here, and why: the container stacks' bytes read at
`ctype/cst + (sp - 1)`.  A clause of the form "the byte at `sp - 1` is `t`"
cannot be carried by a link that pushes or pops, because the byte at the new
`sp - 1` was written at an earlier index and the carry does not remember it.
The sound shape is a carried map `Nat → UInt8` updated at the pushed index,
which the push link (`if.end24_step`), the container-byte stores (class D's
`if.end150.i`, `if.end162.i`, `if.end195.i`, `if.then330.i`) and the merge
(`cleanup478.i`) all have to move.  That is the class-D rework, and it belongs
with the 165-block next-link lemma rather than with the seed.  The register
carriers below are what the header and the seed produce; the stack map is
recorded here as the remaining half of the second carrier, not assumed.

The two predicates are stated beside `WalkInv` rather than as fields of it so
this module lands green: adding a field to the structure changes all ~31 of its
record literals and every hand-built link at once, which is the rework the
census below records as open, not a change the seed's step vocabulary can carry
on its own. -/

/-- The entry stream's position at index `k`, with `0` past the end.  The
carrier is read at an index the loop's own bound keeps inside the stream, so
the default is a totalisation, not a case the walk takes. -/
def entryPos {m0 : Mem} (G : WalkGeom m0) (k : Nat) : Nat :=
  G.ent.getD k 0

/-- The document byte the entry at index `k` selects, with `0` past the end.
`%8` is `entry[%idxprom.i]`, so this is the value the header binds. -/
def entryByte {m0 : Mem} (G : WalkGeom m0) (k : Nat) : UInt8 :=
  G.bs.getD (entryPos G k) 0

/-- The static address registers the dispatch reads, beside `WalkPtrs`' six: the
`%s` record's fields the header's preheader stores, the log's six addresses the
reserves and the merges read, the token's three, the cursor record's five, the
document base's predecessor, and the four stack objects at the call's cursor.
Every one is bound before the loop and no block rebinds it. -/
def walkStaticRegs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (String × Value) :=
  [("%nsp", .ptr (C.stage.s + 56)), ("%xp1", .ptr (C.stage.s + 72)),
   ("%nxp2", .ptr (C.stage.s + 80)), ("%n2.i", .ptr (C.stage.s + 8)),
   ("%ep3.i", .ptr (C.stage.s + 48)),
   ("%len", .ptr (C.stage.z + 8)), ("%cap", .ptr (C.stage.z + 16)),
   ("%0", .ptr (C.stage.z + 24)), ("%h1.i.i.i51", .ptr (C.stage.z + 24)),
   ("%ar", .ptr (C.stage.z + 40)), ("%alen", .ptr (C.stage.z + 48)),
   ("%acap", .ptr (C.stage.z + 56)),
   ("%gap.i", .ptr (C.stage.tok + 20)), ("%end.i", .ptr (C.stage.tok + 8)),
   ("%kind404.i", .ptr (C.stage.tok + 16)),
   ("%n6.i", .ptr (C.stage.c + 8)), ("%ix.i", .ptr (C.stage.c + 16)),
   ("%nix.i", .ptr (C.stage.c + 24)), ("%e7.i", .ptr (C.stage.c + 1112)),
   ("%invariant.gep", .ptr (G.b - 1)),
   ("%ei.i", .ptr G.next0), ("%root_done.i", .ptr (G.next0 + 8)),
   ("%xj.i", .ptr (G.next0 + 12)), ("%outn.i", .ptr (G.next0 + 20))]

/-- **The static carrier**: every register `walkStaticRegs` names holds the value
the staging fixes for it. -/
def WalkRegs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  ∀ p ∈ walkStaticRegs G C, lookupName env p.1 = some p.2

/-- **A run that binds none of the static names keeps both carriers.**  One
`denoteCode_lookupName` per name, and no memory reasoning. -/
theorem WalkRegs.of_run {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {env env' : Env} {s s' : State} {is : List Instr}
    (h : WalkRegs G C env)
    (hfree : ∀ i ∈ is, ∀ p ∈ walkStaticRegs G C, i.dst? ≠ some p.1)
    (hden : denoteCode calls is (stateAt env s) = some (stateAt env' s')) :
    WalkRegs G C env' := by
  intro p hp
  have hlk : lookupName env' p.1 = lookupName env p.1 := by
    simpa only [stateAt] using LeanLLVM.Refinement.JsonEntrySteps.denoteCode_lookupName calls is p.1
      (fun i hi => hfree i hi p hp) (stateAt env s) (stateAt env' s') hden
  rw [hlk]
  exact h p hp

/-- **The per-iteration carrier**: `%7` is the entry stream's lane at the carried
index, and `%8` is the document byte that lane selects.  Both are rebound by
`while.body.i`, so the clause is a function of `C.k`, not a constant; the header's
step produces it and every other block's run leaves it alone. -/
structure WalkIter {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop where
  /-- `%7` holds the lane at the carried index. -/
  reg7 : lookupName env "%7" = some (.int 32 (BitVec.ofNat 32 (entryPos G C.k)))
  /-- `%8` holds the document byte the lane selects. -/
  reg8 : lookupName env "%8" = some (.int 8 (BitVec.ofNat 8 (entryByte G C.k).toNat))

/-- A run that binds neither `%7` nor `%8` keeps the per-iteration carrier. -/
theorem WalkIter.of_run {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {env env' : Env} {s s' : State} {is : List Instr}
    (h : WalkIter G C env)
    (h7 : ∀ i ∈ is, i.dst? ≠ some "%7") (h8 : ∀ i ∈ is, i.dst? ≠ some "%8")
    (hden : denoteCode calls is (stateAt env s) = some (stateAt env' s')) :
    WalkIter G C env' := by
  refine ⟨?_, ?_⟩
  · have hlk : lookupName env' "%7" = lookupName env "%7" := by
      simpa only [stateAt] using LeanLLVM.Refinement.JsonEntrySteps.denoteCode_lookupName calls is "%7" h7
        (stateAt env s) (stateAt env' s') hden
    rw [hlk]; exact h.reg7
  · have hlk : lookupName env' "%8" = lookupName env "%8" := by
      simpa only [stateAt] using LeanLLVM.Refinement.JsonEntrySteps.denoteCode_lookupName calls is "%8" h8
        (stateAt env s) (stateAt env' s') hden
    rw [hlk]; exact h.reg8

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
