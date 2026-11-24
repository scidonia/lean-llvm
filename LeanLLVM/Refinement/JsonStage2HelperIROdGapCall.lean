/-
`od_gap_recover` at the two-argument call boundary, and the document window's
bound a composition stages.

`JsonStage2HelperOdGap` states the helper's model, its rule, and its post at the
call boundary.  Two things are still owed to a caller that reaches the helper
through the no-event walk's selection, and this module supplies them without
restating either the rule or the post:

* **The call record.**  `stage2GapRecover` is a `Calls` entry, not a `Function`:
  it answers a `CallOutcome` directly, the way the fixture's `declare void`
  does, so `stage2GapRecover_post` is the bridge rather than a body's
  `Satisfies`.  `Γ_gapRecover` is the record the walk reads it at, and
  `stage2GapRecover_callSatisfies` is `satisfies_calls_void`'s conclusion shape —
  `CallSatisfies` at a value-blind post — with its `ValueIrrelevant` premise
  discharged (`Γ_gapRecover_valueIrrelevant`) because the entry's return is
  `voidRet`, the placeholder `envForUnit` supplies for a body that returns
  nothing.  The statement is at `stage2NoEventCalls (gap := stage2GapRecover)`,
  the selection the walk's own call site uses, and at `stage2GapRecover` itself.

* **`hwin`'s first disjunct.**  A composition stages the document region ending
  at or below the allocator cursor (`b + n ≤ next`) and the invariant gives the
  token's boundary inside the document (`ip < n`); `gapWindow_le_next` is the
  consequence `b + ip ≤ next`, and `gapWindow_hwin_of_staging` is the
  composition's window premise `b + ip ≤ next ∨ next + 16 ≤ b` at that disjunct.
  Both are inequalities over the naturals; the record's address is the document's
  base plus the boundary the rule already computed.
-/
import LeanLLVM.Refinement.JsonStage2NoEventBody

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The call boundary

The fixture's `declare void @od_gap_recover(ptr %c, i64 %t.0.val)` fixes the two
argument slots: the cursor's address and the token's position as a word.  The
record below reads those two and nothing else, which is what both the model and
the walk's call site do.
-/

/-- **The record `od_gap_recover`'s model is read at.**  The precondition is the
fixture's two argument slots and the resolution of the rule at them — the read
the staging supplies, and the only fact the entry needs to answer.  The post is
value-blind, because the entry's return is `voidRet`: it says the memory the call
leaves is the rule's effect at the cursor's refusal record, and the allocator
cursor is the caller's (`Stage2GapRecoverPost`'s `out.next = next`). -/
def Γ_gapRecover : MemContract where
  budget := fun _ _ => 1
  pre := fun args mem _ =>
    ∃ (c : Nat) (p : BitVec 64) (eff : GapRecoverEffect),
      args = [.ptr c, .int 64 p] ∧ stage2GapRecoverRule mem c p.toNat = some eff
  post := fun args mem next o =>
    match o with
    | .ub => False
    | .ret _ m => ∃ (c : Nat) (p : BitVec 64) (r : CallOutcome),
        args = [.ptr c, .int 64 p] ∧ Stage2GapRecoverPost mem next c p.toNat r ∧
          m = r.mem

/-- **The void return's `ValueIrrelevant` premise.**  The record reads no
returned value: `voidRet` is a placeholder, so two outcomes that differ only in
the value carry the same guarantee. -/
theorem Γ_gapRecover_valueIrrelevant : ValueIrrelevant Γ_gapRecover := by
  intro args mem next v v' m
  rfl

/-- **The model entry's answer, from the rule's resolution.**  `stage2GapRecover`
is a case split on the effect the rule produced; the two cases are the module's
own `stage2GapRecover_unchanged` and `stage2GapRecover_wrote`, so nothing here
re-reads the rule. -/
theorem stage2GapRecover_resolves {mem : Mem} {next c : Nat} {p : BitVec 64}
    {eff : GapRecoverEffect} (hrule : stage2GapRecoverRule mem c p.toNat = some eff) :
    stage2GapRecover "od_gap_recover" [.ptr c, .int 64 p] mem next =
      some { ret := voidRet, mem := eff.apply mem, next := next } := by
  cases eff with
  | unchanged => exact stage2GapRecover_unchanged hrule
  | wrote e off tag => exact stage2GapRecover_wrote hrule

/-- **The model entry's call record at the walk's selection.**  This is the shape
`satisfies_calls_void` concludes — a `CallSatisfies` at a record whose post
ignores the returned value — derived from `stage2GapRecover_post`: the pre
resolves the rule, the entry's answer is `stage2GapRecover_resolves`'s, and the
post and the allocator-cursor monotonicity are the post theorem's two conjuncts
at that answer.  The selection is `stage2NoEventCalls (gap := stage2GapRecover)`,
the one the no-event body's `od_gap_recover` call site is written at. -/
theorem stage2GapRecover_callSatisfies :
    CallSatisfies (stage2NoEventCalls (gap := stage2GapRecover)) Γ_gapRecover
      "od_gap_recover" := by
  intro args mem next hpre
  obtain ⟨c, p, eff, hargs, hrule⟩ := hpre
  subst hargs
  have hres := stage2GapRecover_resolves (mem := mem) (next := next) (c := c)
    (p := p) (eff := eff) hrule
  obtain ⟨-, c', p', hargs', hpost⟩ := stage2GapRecover_post hres
  refine ⟨_, ?_, ⟨c', p', _, hargs', hpost, rfl⟩, Nat.le_of_eq hpost.2.1.symm⟩
  rw [stage2NoEventCalls_gap]
  exact hres

/-- **The same record at the model entry itself.**  `stage2NoEventCalls` forwards
`od_gap_recover` to the model unchanged (`stage2NoEventCalls_gap`), so the walk's
selection and the entry carry the same guarantee at the symbol. -/
theorem stage2GapRecover_callSatisfies_model :
    CallSatisfies stage2GapRecover Γ_gapRecover "od_gap_recover" := by
  intro args mem next hpre
  obtain ⟨r, hres, hpost, hle⟩ := stage2GapRecover_callSatisfies args mem next hpre
  exact ⟨r, by rwa [stage2NoEventCalls_gap] at hres, hpost, hle⟩

/-! ### The document window's bound

`hwin` is the composition's window premise at the document region and the
refusal record: the region's end is at or below the cursor, and the record's
address is inside the region.  The consequence is arithmetic over the naturals;
the strictness of the invariant's bound is what makes the sum stay inside.
-/

/-- **The document region's bound reaches the token's boundary.**  From the
staging `b + n ≤ next` (the document's `n` bytes end at or below the cursor) and
the invariant's `ip < n` (the boundary is inside the document), the record's
address `b + ip` is at or below the cursor. -/
theorem gapWindow_le_next {b n ip next : Nat} (hstage : b + n ≤ next) (hip : ip < n) :
    b + ip ≤ next := by
  omega

/-- **`hwin`'s first disjunct.**  The composition's premise
`b + ip ≤ next ∨ next + 16 ≤ b`, discharged at the staging and the invariant's
bound rather than assumed. -/
theorem gapWindow_hwin_of_staging {b n ip next : Nat} (hstage : b + n ≤ next)
    (hip : ip < n) :
    b + ip ≤ next ∨ next + 16 ≤ b :=
  Or.inl (gapWindow_le_next hstage hip)

/-! ### Axiom footprints -/

#print axioms Γ_gapRecover_valueIrrelevant
#print axioms stage2GapRecover_resolves
#print axioms stage2GapRecover_callSatisfies
#print axioms stage2GapRecover_callSatisfies_model
#print axioms gapWindow_le_next
#print axioms gapWindow_hwin_of_staging

end LeanLLVM.Refinement
