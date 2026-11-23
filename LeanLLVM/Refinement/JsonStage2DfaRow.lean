/-
The DFA body's first semantic row: the entry prefix through `s2_init`.

`stage2DfaEntryPrefix` is the first eight instructions of the pinned
`stage2DfaBody`'s entry block — the two body allocas (`%xj.i`, `%outn.i`), the
three lifetime markers, the count arithmetic and the `s2_init` call.  The
certified walk's `walkEntrySeg1` is the same family with two extra allocas
(`%ei.i`, `%root_done.i`); the DFA keeps neither, so its cursor advances by 16
rather than 28.

The row is a `denoteCode` equality: from a symbolic environment whose `%s`,
`%b`, `%n`, `%ep`, `%z`, `%e` are the call's arguments, the prefix leaves the
entry environment and the memory `s2_init` writes.  The `s2_init` step is
`WalkScope.walkMemS2Init`, so the row is the certified helper call's semantics at
this body's arguments, not a re-proved helper body.

What this is not: the `Satisfies` composition, the loop invariant, or any row
after `s2_init`.  Those are the body proof's remaining stages.
-/
import LeanLLVM.Refinement.JsonStage2DfaBody
import LeanLLVM.Refinement.JsonStage2WalkSeed

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.WalkScope
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)

/-- The DFA entry's prefix through `s2_init`, exactly as the pinned body writes
it. -/
def stage2DfaEntryPrefix : List Instr := [
  Instr.alloca "%xj.i" (Ty.int 64) 0,
  Instr.alloca "%outn.i" (Ty.int 64) 0,
  Instr.callVoid "llvm.lifetime.start.p0"
    [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (.reg "%s"))],
  Instr.callVoid "llvm.lifetime.start.p0"
    [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (.reg "%z"))],
  Instr.callVoid "llvm.lifetime.start.p0"
    [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%e"))],
  Instr.binop "%add" BinOp.add 64 (.reg "%n") (.imm (.int 64 (BitVec.ofNat 64 63))),
  Instr.binop "%shr" BinOp.lshr 64 (.reg "%add") (.imm (.int 64 (BitVec.ofNat 64 6))),
  Instr.callVoid "s2_init" [(Ty.ptr, (.reg "%s")), (Ty.ptr, (.reg "%b")),
    ((Ty.int 64), (.reg "%n")), ((Ty.int 64), (.reg "%shr")), (Ty.ptr, (.reg "%ep"))]
]

/-- The prefix is the pinned body's first eight instructions. -/
theorem stage2DfaEntryPrefix_pin :
    stage2DfaBody.blocks.head?.map (·.instrs.take 8) = some stage2DfaEntryPrefix := by
  decide

/-- The entry environment after the prefix: the two allocas at the cursor, the
count numerator and the block count. -/
def stage2DfaEntryEnv (env : Env) (c n : Nat) : Env :=
  cells [("%shr", .int 64 ((BitVec.ofNat 64 n + BitVec.ofNat 64 63) >>> 6)),
         ("%add", .int 64 (BitVec.ofNat 64 n + BitVec.ofNat 64 63)),
         ("%outn.i", .ptr (c + 8)), ("%xj.i", .ptr c)] env

/-- **The DFA entry prefix's semantic row.**  From the call's argument
environment, the eight instructions leave the entry environment and the memory
`s2_init` writes at `(%s, %b, %n, %shr, %ep)`. -/
theorem stage2DfaEntryPrefix_denote (env : Env) (s : State)
    (is : List Instr) {n b ep sAddr zAddr eAddr : Nat}
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hb : lookupName env "%b" = some (.ptr b))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hs : lookupName env "%s" = some (.ptr sAddr))
    (hz : lookupName env "%z" = some (.ptr zAddr))
    (he : lookupName env "%e" = some (.ptr eAddr)) :
    denoteCode (stage2Calls stage2SubCalls) (stage2DfaEntryPrefix ++ is) (stateAt env s) =
      denoteCode (stage2Calls stage2SubCalls) is
        (stateAt (stage2DfaEntryEnv env s.next n)
          (memAt { s with next := s.next + 16 }
            (stage2WriteStores s.mem
              (s2InitStores sAddr b (BitVec.toNat (BitVec.ofNat 64 n))
                (BitVec.toNat ((BitVec.ofNat 64 n + BitVec.ofNat 64 63)
                  >>> (6 : BitVec 64))) ep)))) := by
  simp only [stage2DfaEntryPrefix, List.cons_append, List.nil_append]
  rw [denoteCode_alloca (calls := stage2Calls stage2SubCalls) (d := "%xj.i") (ty := Ty.int 64) (align := 0)]
  rw [denoteCode_alloca (calls := stage2Calls stage2SubCalls) (d := "%outn.i") (ty := Ty.int 64) (align := 0)]
  rw [denoteCode_lifetime_at (sub := stage2SubCalls) (a := sAddr) _ _ 120 "%s" ?_ _] <;> try block_lk
  rw [denoteCode_lifetime_at (sub := stage2SubCalls) (a := zAddr) _ _ 64 "%z" ?_ _] <;> try block_lk
  rw [denoteCode_lifetime_at (sub := stage2SubCalls) (a := eAddr) _ _ 24 "%e" ?_ _] <;> try block_lk
  rw [walkDenoteCode_add_imm_w _ _ _ "%add" "%n" 64 (x := BitVec.ofNat 64 n) ?_ _] <;> try block_lk
  rw [denoteCode_lshr_imm _ _ _ "%shr" "%add"
    (x := BitVec.ofNat 64 n + BitVec.ofNat 64 63) ?_ _] <;> try block_lk
  change denoteCode (stage2Calls stage2SubCalls)
      (.callVoid "s2_init" [(Ty.ptr, (.reg "%s")), (Ty.ptr, (.reg "%b")),
        ((Ty.int 64), (.reg "%n")), ((Ty.int 64), (.reg "%shr")), (Ty.ptr, (.reg "%ep"))]
        :: is)
      (stateAt (stage2DfaEntryEnv env s.next n)
        (memAt { s with next := s.next + 16 } s.mem)) =
    denoteCode (stage2Calls stage2SubCalls) is
      (stateAt (stage2DfaEntryEnv env s.next n)
        (memAt { s with next := s.next + 16 }
          (stage2WriteStores s.mem
            (s2InitStores sAddr b (BitVec.toNat (BitVec.ofNat 64 n))
              (BitVec.toNat ((BitVec.ofNat 64 n + BitVec.ofNat 64 63)
                >>> (6 : BitVec 64))) ep))))
  rw [walkMemS2Init (env := stage2DfaEntryEnv env s.next n)
    (s := { s with next := s.next + 16 }) (m := s.mem)
    (sAddr := sAddr) (b := b) (ep := ep)
    (n := BitVec.ofNat 64 n)
    (nb := (BitVec.ofNat 64 n + BitVec.ofNat 64 63) >>> 6)]
  all_goals first | rfl | block_lk

end LeanLLVM.Refinement
