/-
# The string opener above depth zero, at a document

`HcontClass.stringOpener` is the byte `34`, and `HcontArm.twoEntry` describes it at depth
zero only.  The class at a positive depth is `JsonStage2WalkDispatchHcontStringDeep`'s
`stringOpenAboveZero`: the depth edge, the two marker links and the key-true tail (or the
nest's own refusal).  This module exhibits the state at a real document, and the control
that keeps the two classes apart.

## The document

`["`·`a` — an opener, a string opener and a trailing byte — is `DelimiterContDocument G
91 34 97`: three bytes, three entries, lanes `0`, `1`, `2`.  The opener at entry zero is
`containerOpen_depth_one_stacks`', so the head it produces has `sp = 1`, `k = 1` and an
entry left; the byte at that head is the document's second, `34`.  That is the class's
statement: byte `34` at depth one, with the guarded head the continuing branch needs.

The control is the *same* document's seed head.  There the depth is `0` and the byte is
the opener's `91`, so the arm's two class premises both fail: it is the seed's
`HcontArm.containerOpen` (or a refusal), never the positive-depth opener.

## What is taken, and what is derived

The opener's own staging — `s2_value_pos`'s precondition, its answer and the reservation
of the root slot — is the seed state's, exactly as `JsonStage2WalkDispatchClosersDomain`
takes it.  The class's premises are then **derived**: the depth is `1` by the producer's
own equation, and the byte is the document's at `entryByte_one`.  Nothing about the string
body is supplied here, because the arm's route is a row of its own.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontStringDeep
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosersDomain

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The positive-depth string opener's state at `["`·`a`.**  The opener's pass at entry
zero produces a head with an entry left, depth one and the byte `34`, and the class's own
statement — the byte's equality test at the invariant's `%8` cell — holds there. -/
theorem stringOpenAboveZero_reachable {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c d e)
    (hc : c = 91 ∨ c = 123) (hd : d = 34)
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
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.k + 1 < G.nep ∧ C'.sp ≠ 0 ∧
      evalICmp .eq (hlastByte G C') (BitVec.ofNat 8 34) = 1 ∧
      C'.tyMap (C'.sp - 1) = ifEnd24TyByte (BitVec.ofNat 8 c.toNat) ∧
      C'.stMap (C'.sp - 1) = ifEnd24StByte := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hguard, h8m, hty, hst⟩ :=
    depthOne_stacks_cont_reachable hargs hnext h hc hrd hpreV r hcall hret
  have hbyte : hlastByte G C' = BitVec.ofNat 8 34 := by
    have h1 : lookupName s'.env "%8" = some (.int 8 (BitVec.ofNat 8 d.toNat)) := by
      simpa only [evalOperand] using h8m
    have h2 := hInv'.iter.reg8
    rw [h1] at h2
    have h3 : hlastByte G C' = BitVec.ofNat 8 d.toNat :=
      (eq_of_heq (Value.int.inj (Option.some.inj h2)).2).symm
    rw [h3, hd]
    rfl
  refine ⟨C', s', hInv', hblock', hguard, ?_, ?_, hty, hst⟩
  · rw [hsp1]
    decide
  · rw [hbyte]
    exact walkEvalICmp_eq_self _

/-- **The same document's seed head is the control.**  Its depth is `0` and its byte is
the opener's, so the positive-depth opener's two class premises fail there: the seed is
`HcontArm.containerOpen`'s state (or a refusal), and the byte `34` at positive depth is
not it. -/
theorem stringOpenAboveZero_absent_at_seed {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c d e)
    (hc : c = 91 ∨ c = 123) :
    (walkSeed G S).sp = 0 ∧
      evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 34) = 0 := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hInv := seededInv (S := S) hargs hnext hn
  have hbyte : hlastByte G (walkSeed G S) = BitVec.ofNat 8 c.toNat := by
    have hreg := hInv.iter.reg8
    have h1 : lookupName (openerHead G S args next).env "%8" =
        some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
      simpa only [evalOperand] using
        seed_head_byte G S (openerHead G S args next) h.entryByte_zero hInv
    have h2 : lookupName (openerHead G S args next).env "%8" =
        some (.int 8 (hlastByte G (walkSeed G S))) := hreg
    exact eq_of_heq (Value.int.inj (Option.some.inj (h2.symm.trans h1))).2
  refine ⟨rfl, ?_⟩
  rw [hbyte]
  rcases hc with hc | hc
  · rw [hc]
    exact refuseICmp_eq_zero (by decide)
  · rw [hc]
    exact refuseICmp_eq_zero (by decide)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.stringOpenAboveZero_reachable
#print axioms LeanLLVM.Refinement.WalkScope.stringOpenAboveZero_absent_at_seed

end WalkScope
end LeanLLVM.Refinement
