/-
The closing delimiter's arm at documents that reach depth one, and the merge route it
finally selects.

`LastEntryArm.closeWithOpen` and `HcontArm.closeWithOpen` are stated from the loop head at
`C.sp ≠ 0`, so the regression has to exhibit them at a head a document actually reaches.
The producer that carries the two stack bytes is `containerOpen_depth_one_stacks`
(`JsonStage2WalkDispatchClosers`): the opener's merge and the header's pass, with the
push's write to each stack at the index it wrote.  The documents are the opener followed
by a delimiter, and nothing else:

| document | bytes | entries | level | route |
|---|---|---|---|---|
| `[]` | `91, 93` | two | last entry | merge, `closeBracketMerge_at` (11 links) |
| `{}` | `123, 125` | two | last entry | merge, `closeBraceMerge_at` (13 links) |
| `[}` | `91, 125` | two | last entry | marker mismatch, `closeMarkerBrace_at` (7 links) |
| `{]` | `123, 93` | two | last entry | marker mismatch, `closeMarkerBracket_at` (7 links) |
| `[]0` | `91, 93, 48` | three | continuing | merge, `closeBracketMerge_at` (11 links) |
| `{}0` | `123, 125, 48` | three | continuing | merge, `closeBraceMerge_at` (13 links) |
| `[}0` | `91, 125, 48` | three | continuing | marker mismatch, `closeMarkerBrace_at` (7 links) |
| `{]0` | `123, 93, 48` | three | continuing | marker mismatch, `closeMarkerBracket_at` (7 links) |

**Why `[]` and `{}` merge.**  The push writes `ifEnd24TyByte c` on the type stack —
`2` for `[`, `1` for `{` — and `ifEnd24StByte` (`0`) on the state stack.  At the head the
opener hands over, `C.sp = 1`, so the nesting check's index `C.sp - 1` is the push's own
index `0`: the marker the check compares is the container's own marker, and the state
byte is `0`, which is a merge value for both bytes (`]` merges at `0` and `1`, `}` at `0`
and `3`).  Both documents therefore select the merge, which is the round's purpose: every
earlier depth-one document could only reach a refusal, because the depth-one producer
stated the reached head and not the stacks.

`[}` and `{]` keep the byte's own marker test apart from the container's: `}` expects `1`
and reads `2`, `]` expects `2` and reads `1`, so both are `mismatchedRefuse_at`'s refusal.
They are the depth-one documents that make the marker test *observable*, and they are
proved by the same arm — the state byte's merge set is never read.

The negative controls are the one-byte documents `]` and `}`: the same byte detector finds
`93` and `125` there, so the byte's class premise holds, but the depth is the seed's zero
and the arm's `C.sp ≠ 0` premise is refuted.  The affirmative control for that detector is
the producer's `C'.sp = 1`, read off each reachability theorem below.

Each document's theorem carries the selectors the dispatch's case split reads — the byte,
the type stack's byte and the state stack's byte — so the route it selects is visible
without unfolding the dispatch, and the result is produced by the real
`LastEntryArm.dispatch` / `HcontArm.dispatch` at the arm.  The two merge documents also
have a route theorem whose proof applies the merge theorem itself, which is what names
them theorem by theorem.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The depth-one head the documents reach, with the push's stacks

`containerOpen_depth_one_stacks` composes the opener's merge and the header's pass; the
entry immediately after the opener is the delimiter, and the two stack bytes at the
delimiter's head are the push's, at the index the push wrote. -/

/-- **`[]`/`[}`/`{}`/`{]`'s depth-one head is the delimiter's, with the push's two stack
bytes.**  The opener is entry zero at depth zero, so its product is a loop head one level
deeper at entry one; the head's `%8` is the document's second byte, and the stacks hold
`ifEnd24TyByte c` and `ifEnd24StByte` at the index the push wrote — which is the closing
delimiter's `C.sp - 1`. -/
theorem depthOne_stacks_last_reachable {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G c d)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 d.toNat)) ∧
      C'.tyMap (C'.sp - 1) = ifEnd24TyByte (BitVec.ofNat 8 c.toNat) ∧
      C'.stMap (C'.sp - 1) = ifEnd24StByte := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hInv := seededInv (S := S) hargs hnext hn
  have h8s : evalOperand (openerHead G S args next) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
    simpa only [evalOperand] using
      seed_head_byte G S (openerHead G S args next) h.entryByte_zero hInv
  have hopen : BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 91 ∨
      BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 123 := by
    rcases hc with hc | hc
    · rw [hc]; exact Or.inl (by decide)
    · rw [hc]; exact Or.inr (by decide)
  obtain ⟨C', s', hInv', hblock', hsp', hk', hty, hst⟩ :=
    containerOpen_depth_one_stacks G (walkSeed G S) (openerHead G S args next) hInv
      (walkSeed_block G S) h8s hopen
      (by change (0 : Nat) ≤ 519; decide)
      hrd hpreV r hcall hret
      (by change (0 : Nat) + 1 < G.nep; rw [h.count]; decide)
  have hsp1 : C'.sp = 1 := by rw [hsp']; rfl
  have hk1 : C'.k = 1 := by rw [hk']; rfl
  have hsub : C'.sp - 1 = (walkSeed G S).sp := by rw [hsp']; simp only [walkSeed]
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_, ?_, ?_⟩
  · have hreg := hInv'.iter.reg8
    rw [hk1, h.entryByte_one] at hreg
    simpa only [evalOperand] using hreg
  · rw [hsub]; exact hty
  · rw [hsub]; exact hst

/-- **`[]0`/`[}0`/`{}0`/`{]0`'s depth-one head is the delimiter's, with an entry left.**
The same producer at the three-entry document's opener, so the continuing guard holds at
the head the delimiter sits at. -/
theorem depthOne_stacks_cont_reachable {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c d e)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      C'.k + 1 < G.nep ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 d.toNat)) ∧
      C'.tyMap (C'.sp - 1) = ifEnd24TyByte (BitVec.ofNat 8 c.toNat) ∧
      C'.stMap (C'.sp - 1) = ifEnd24StByte := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hInv := seededInv (S := S) hargs hnext hn
  have h8s : evalOperand (openerHead G S args next) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
    simpa only [evalOperand] using
      seed_head_byte G S (openerHead G S args next) h.entryByte_zero hInv
  have hopen : BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 91 ∨
      BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 123 := by
    rcases hc with hc | hc
    · rw [hc]; exact Or.inl (by decide)
    · rw [hc]; exact Or.inr (by decide)
  obtain ⟨C', s', hInv', hblock', hsp', hk', hty, hst⟩ :=
    containerOpen_depth_one_stacks G (walkSeed G S) (openerHead G S args next) hInv
      (walkSeed_block G S) h8s hopen
      (by change (0 : Nat) ≤ 519; decide)
      hrd hpreV r hcall hret
      (by change (0 : Nat) + 1 < G.nep; rw [h.count]; decide)
  have hsp1 : C'.sp = 1 := by rw [hsp']; rfl
  have hk1 : C'.k = 1 := by rw [hk']; rfl
  have hsub : C'.sp - 1 = (walkSeed G S).sp := by rw [hsp']; simp only [walkSeed]
  have hguard : C'.k + 1 < G.nep := by rw [hk1, h.count]; omega
  refine ⟨C', s', hInv', hblock', hsp1, hk1, hguard, ?_, ?_, ?_⟩
  · have hreg := hInv'.iter.reg8
    rw [hk1, h.entryByte_one] at hreg
    simpa only [evalOperand] using hreg
  · rw [hsub]; exact hty
  · rw [hsub]; exact hst

/-! ### The arm, through the real dispatch

`hvj`, `he` and the offset bound are the invariant's own (`WalkInv.idx_reg`,
`WalkInv.regs`, `entryPos_lt`), so the wrapper takes only the call's pre-state bundle
beside the arm's premises. -/

/-- **The closing delimiter's arm at a last entry.** -/
theorem closeWithOpen_last_dispatch {m0 : Mem} {G : WalkGeom m0} {C' : WalkCarry G}
    {s' : State} (hInv : WalkInv G C' s') (hblock : C'.block = walkLoopHead)
    (hnot : ¬ (C'.k + 1 < G.nep)) {v : BitVec 8}
    (h8 : evalOperand s' (.reg "%8") = some (.int 8 v))
    (hv : v = BitVec.ofNat 8 93 ∨ v = BitVec.ofNat 8 125)
    (hsp : C'.sp ≠ 0) {b1 b2 : UInt8} (hmark : C'.tyMap (C'.sp - 1) = b1)
    (hstate : C'.stMap (C'.sp - 1) = b2)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  have hklt : C'.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have hvj : evalOperand s' (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C'.k))) := by
    simpa only [evalOperand] using hInv.idx_reg
  have he : lookupName s'.env "%e" = some (.ptr C'.stage.e) :=
    hInv.regs ("%e", .ptr C'.stage.e) (by simp [walkStaticRegs])
  exact LastEntryArm.dispatch hInv hblock hnot
    (.closeWithOpen h8 hv hsp hmark hstate hpreA hvj he
      (le_of_lt (entryPos_lt G hklt))
      (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega))

/-- **The closing delimiter's arm at a continuing entry.** -/
theorem closeWithOpen_cont_dispatch {m0 : Mem} {G : WalkGeom m0} {C' : WalkCarry G}
    {s' : State} (hInv : WalkInv G C' s') (hblock : C'.block = walkLoopHead)
    (hk : C'.k + 1 < G.nep) {v : BitVec 8}
    (h8 : evalOperand s' (.reg "%8") = some (.int 8 v))
    (hv : v = BitVec.ofNat 8 93 ∨ v = BitVec.ofNat 8 125)
    (hsp : C'.sp ≠ 0) {b1 b2 : UInt8} (hmark : C'.tyMap (C'.sp - 1) = b1)
    (hstate : C'.stMap (C'.sp - 1) = b2)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  have hklt : C'.k < G.nep := by omega
  have hvj : evalOperand s' (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C'.k))) := by
    simpa only [evalOperand] using hInv.idx_reg
  have he : lookupName s'.env "%e" = some (.ptr C'.stage.e) :=
    hInv.regs ("%e", .ptr C'.stage.e) (by simp [walkStaticRegs])
  exact HcontArm.dispatch hInv hblock hk
    (.closeWithOpen h8 hv hsp hmark hstate hpreA hvj he
      (le_of_lt (entryPos_lt G hklt))
      (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega))

/-! ### `[]` at the two levels: the merge, through the dispatch

The document's byte is `93` and the push writes the bracket's marker `2` and the state
byte `0` at the index the nesting check reads, so the dispatch's case split selects
`closeBracketMerge_at`'s merge. -/

/-- **`[]` reaches the closing bracket's arm above depth zero.** -/
theorem closeBracketMerge_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (91 : UInt8) 93)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_last_dispatch hInv' hblock' (by rw [hk1, h.count]; omega) h8c
    (Or.inl rfl) (by rw [hsp1]; decide) hmark2 hstate0 hpreA'

/-- **`[]0` reaches the closing bracket's arm above depth zero, with an entry left.** -/
theorem closeBracketMerge_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (91 : UInt8) 93 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hguard, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_cont_dispatch hInv' hblock' hguard h8c
    (Or.inl rfl) (by rw [hsp1]; decide) hmark2 hstate0 hpreA'

/-! ### `{}` at the two levels: the merge, through the dispatch -/

/-- **`{}` reaches the closing brace's arm above depth zero.** -/
theorem closeBraceMerge_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (123 : UInt8) 125)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_last_dispatch hInv' hblock' (by rw [hk1, h.count]; omega) h8c
    (Or.inr rfl) (by rw [hsp1]; decide) hmark1 hstate0 hpreA'

/-- **`{}0` reaches the closing brace's arm above depth zero, with an entry left.** -/
theorem closeBraceMerge_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (123 : UInt8) 125 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hguard, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_cont_dispatch hInv' hblock' hguard h8c
    (Or.inr rfl) (by rw [hsp1]; decide) hmark1 hstate0 hpreA'

/-! ### `[}` and `{]` at the two levels: the marker's refusal

The byte's own marker is not the container's, so the nesting check refuses before the
state stack is read.  The state byte is still the push's zero; it is simply not reached,
which is what makes these two the documents where the marker test is observable. -/

/-- **`[}` reaches the closing brace's marker-mismatch refusal.** -/
theorem closeMarkerBrace_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (91 : UInt8) 125)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_last_dispatch hInv' hblock' (by rw [hk1, h.count]; omega) h8c
    (Or.inr rfl) (by rw [hsp1]; decide) hmark2 hstate0 hpreA'

/-- **`{]` reaches the closing bracket's marker-mismatch refusal.** -/
theorem closeMarkerBracket_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (123 : UInt8) 93)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_last_dispatch hInv' hblock' (by rw [hk1, h.count]; omega) h8c
    (Or.inl rfl) (by rw [hsp1]; decide) hmark1 hstate0 hpreA'

/-- **`[}0` reaches the closing brace's marker-mismatch refusal, with an entry left.** -/
theorem closeMarkerBrace_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (91 : UInt8) 125 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hguard, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_cont_dispatch hInv' hblock' hguard h8c
    (Or.inr rfl) (by rw [hsp1]; decide) hmark2 hstate0 hpreA'

/-- **`{]0` reaches the closing bracket's marker-mismatch refusal, with an entry left.** -/
theorem closeMarkerBracket_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (123 : UInt8) 93 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hguard, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeWithOpen_cont_dispatch hInv' hblock' hguard h8c
    (Or.inl rfl) (by rw [hsp1]; decide) hmark1 hstate0 hpreA'

/-! ### The merge route, named theorem by theorem

The four theorems above are the real dispatch's result at each document.  These apply the
merge theorem each merge document selects, so the route the dispatch's case split takes is
named by a proof and not only by the selectors.
-/

/-- **`[]` merges at `closeBracketMerge_at`.** -/
theorem bracketMerge_route_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (91 : UInt8) 93)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  have hbe : BitVec.ofNat 8 (entryByte G C'.k).toNat = BitVec.ofNat 8 93 := by
    have h1 : lookupName s'.env "%8" = some (.int 8 (BitVec.ofNat 8 93)) := by
      simpa only [evalOperand] using h8c
    have h := Option.some.inj (hInv'.iter.reg8.symm.trans h1)
    simpa using h
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeBracketMerge_at G C' s' hInv' hblock' h8c hbe
    (by rw [hsp1]; decide) hmark2 hstate0 (by decide) (by decide) hpreA'

/-- **`{}` merges at `closeBraceMerge_at`.** -/
theorem braceMerge_route_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G (123 : UInt8) 125)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8', hmark', hstate'⟩ :=
    depthOne_stacks_last_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  have hbe : BitVec.ofNat 8 (entryByte G C'.k).toNat = BitVec.ofNat 8 125 := by
    have h1 : lookupName s'.env "%8" = some (.int 8 (BitVec.ofNat 8 125)) := by
      simpa only [evalOperand] using h8c
    have h := Option.some.inj (hInv'.iter.reg8.symm.trans h1)
    simpa using h
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeBraceMerge_at G C' s' hInv' hblock' h8c hbe
    (by rw [hsp1]; decide) hmark1 hstate0 (by decide) (Or.inl (by decide)) hpreA'

/-- **`[]0` merges at `closeBracketMerge_at`, with an entry left.** -/
theorem bracketMerge_route_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (91 : UInt8) 93 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      C'.tyMap (C'.sp - 1) = 2 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, -, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inl rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have ht : ((93 : UInt8)).toNat = 93 := by decide
    simpa only [ht] using h8'
  have hmark2 : C'.tyMap (C'.sp - 1) = 2 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  have hbe : BitVec.ofNat 8 (entryByte G C'.k).toNat = BitVec.ofNat 8 93 := by
    have h1 : lookupName s'.env "%8" = some (.int 8 (BitVec.ofNat 8 93)) := by
      simpa only [evalOperand] using h8c
    have h := Option.some.inj (hInv'.iter.reg8.symm.trans h1)
    simpa using h
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark2, hstate0, ?_⟩
  intro hpreA'
  exact closeBracketMerge_at G C' s' hInv' hblock' h8c hbe
    (by rw [hsp1]; decide) hmark2 hstate0 (by decide) (by decide) hpreA'

/-- **`{}0` merges at `closeBraceMerge_at`, with an entry left.** -/
theorem braceMerge_route_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G (123 : UInt8) 125 48)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      C'.tyMap (C'.sp - 1) = 1 ∧ C'.stMap (C'.sp - 1) = 0 ∧
      (s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C'.sp + BitVec.ofNat 32 4294967295),
         .ptr (G.next0 + 8), .ptr C'.stage.ctype, .ptr C'.stage.cst] s'.mem s'.next →
       WalkDispatchResult (stage2Calls stage2SubCalls) G C' s') := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, -, h8', hmark', hstate'⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h (Or.inr rfl) hrd hpreV r hcall hret
  have h8c : evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    have ht : ((125 : UInt8)).toNat = 125 := by decide
    simpa only [ht] using h8'
  have hmark1 : C'.tyMap (C'.sp - 1) = 1 := by
    rw [hmark']; decide
  have hstate0 : C'.stMap (C'.sp - 1) = 0 := by
    rw [hstate']; decide
  have hbe : BitVec.ofNat 8 (entryByte G C'.k).toNat = BitVec.ofNat 8 125 := by
    have h1 : lookupName s'.env "%8" = some (.int 8 (BitVec.ofNat 8 125)) := by
      simpa only [evalOperand] using h8c
    have h := Option.some.inj (hInv'.iter.reg8.symm.trans h1)
    simpa using h
  refine ⟨C', s', hInv', hblock', hsp1, hk1, h8c, hmark1, hstate0, ?_⟩
  intro hpreA'
  exact closeBraceMerge_at G C' s' hInv' hblock' h8c hbe
    (by rw [hsp1]; decide) hmark1 hstate0 (by decide) (Or.inl (by decide)) hpreA'

/-! ### The negative controls

The one-byte documents `]` and `}` carry the arm's bytes but not its depth.  The byte
conjunct is the affirmative control for the detector the absence is claimed with: the same
read finds `93` and `125` there. -/

/-- **The document `]` carries the closing bracket's byte but the seed's depth is zero**,
so the arm's `C.sp ≠ 0` premise is refuted there. -/
theorem depthZero_no_closeBracketAbove {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : OneByteDocument G (93 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) ∧
      ¬ ((walkSeed G S).sp ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hreg := seed_reg8 G S s h hInv
    have htoNat : ((93 : UInt8)).toNat = 93 := by decide
    rw [htoNat] at hreg
    simpa only [evalOperand] using hreg
  · simp [walkSeed]

/-- **The document `}` carries the closing brace's byte but the seed's depth is zero**, so
the arm's `C.sp ≠ 0` premise is refuted there. -/
theorem depthZero_no_closeBraceAbove {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (s : State) (h : OneByteDocument G (125 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) ∧
      ¬ ((walkSeed G S).sp ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hreg := seed_reg8 G S s h hInv
    have htoNat : ((125 : UInt8)).toNat = 125 := by decide
    rw [htoNat] at hreg
    simpa only [evalOperand] using hreg
  · simp [walkSeed]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.depthOne_stacks_last_reachable
#print axioms LeanLLVM.Refinement.WalkScope.depthOne_stacks_cont_reachable
#print axioms LeanLLVM.Refinement.WalkScope.closeWithOpen_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.closeWithOpen_cont_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.closeBracketMerge_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeBraceMerge_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeMarkerBrace_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeMarkerBracket_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeBracketMerge_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeBraceMerge_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeMarkerBrace_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.closeMarkerBracket_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.bracketMerge_route_at_document
#print axioms LeanLLVM.Refinement.WalkScope.braceMerge_route_at_document
#print axioms LeanLLVM.Refinement.WalkScope.bracketMerge_route_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.braceMerge_route_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.depthZero_no_closeBracketAbove
#print axioms LeanLLVM.Refinement.WalkScope.depthZero_no_closeBraceAbove

end WalkScope
end LeanLLVM.Refinement
