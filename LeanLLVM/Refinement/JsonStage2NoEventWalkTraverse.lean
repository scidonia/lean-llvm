/-
The no-event walk's loop step and its completion.

`JsonStage2NoEventWalkSegment` states the counted segment, the potential and the
flush route.  This module states the loop's step at the post-read head
`NodeBlock5` — a priced continuing segment to the next head, or the terminal
route's completion — and proves the strong recursion on the entries left and the
completion at the record's budget:

* the **step** is the interface the dispatch classes produce: from a head
  carrying `k < nep`, either a priced segment to a head with a larger `k` (the
  count class's cycle-closing row, via `of_head_chain`), or the terminal route — the
  flush, refusal or acceptance conclusion already proved, bounded by the head's
  credit plus `F`;
* the **recursion** on `nep - k` composes the continuing segments' credits and
  ends at whichever state the step's terminal branch is taken from, carrying the
  verdict and the memory out of the recursion as the terminal run produced them;
* the **completion** composes a seed run of `j` steps with the loop's and fits
  `j + F + 2` inside the finalisation allowance, so the run completes at
  `potential + 32 ≤ 32 * nep + 8 * n + 32 ≤ stage2NoEventBudget` of the carry's
  argument words.

The step's continuing branch carries the facts the walk's static numbers are
kept — `nep`, `a12` and `next0` — because the boundary is read at the record's
argument list and the caller's cursor, which the rows do not move; they are the
no-event analogue of the certified segment's `stage_eq`. -/
import LeanLLVM.Refinement.JsonStage2NoEventWalkHead

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The credit's bound -/

/-- **The credit is inside the record's first two terms.**  Both subtractions are
bounded by their minuends, so no count hypothesis is needed. -/
theorem stage2NoEventWalkPotential_le (K : Stage2NoEventWalkCarry) (k : Nat) :
    stage2NoEventWalkPotential K k ≤
      32 * K.nep + 8 * K.n := by
  unfold stage2NoEventWalkPotential
  have h₁ : K.nep - k ≤ K.nep := Nat.sub_le _ _
  have h₂ : K.n - K.ent.getD k 0 ≤ K.n := Nat.sub_le _ _
  have h₃ := Nat.mul_le_mul_left 32 h₁
  have h₄ := Nat.mul_le_mul_left 8 h₂
  omega

/-! ### The loop's step -/

/-- **One head visit.**  From a head state (`Stage2NoEventWalkHead`: the invariant,
the parameters, the index below the entry count, and the head block's read values),
either

* a priced head segment reaches the next head `NodeBlock5` with a larger index `k'`
  still below `nep`, the carry's `nep`, `a12` and `next0` unchanged, and the
  potential's credit paid (`p + Φ(K', k') ≤ Φ(K, k)`); the segment carries the
  target's `Head` and `Trace`, which the loop's next visit and the row's continuing
  branch consume; or
* the terminal route completes: `q` steps of the segment and the terminal arm's
  two reach the return with the record's boundary at the returned memory, and
  `q` is inside the head's credit plus `F`.

The producer is the dispatch tier: the count class's cycle-closing row and the
three terminal arms (flush, refusal, acceptance) are its evidence; this module
consumes the step, never constructs it. -/
def Stage2NoEventWalkStep (calls : Calls) (mem : Mem) (F : Nat) : Prop :=
  ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    (∃ (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat),
        Stage2NoEventWalkHeadPricedSegment calls mem K k s K' k' s' p ∧
        K'.nep = K.nep ∧ K'.a12 = K.a12 ∧ K'.next0 = K.next0 ∧
        k < k' ∧ k' < K.nep)
    ∨ (∃ (q : Nat) (v : BitVec 64) (m : Mem),
        q ≤ stage2NoEventWalkPotential K k + F ∧
        runFuel calls (q + 2) stage2NoEventBody s = some (.ret (some (.int 64 v)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 v))

/-- **The loop finishes inside the credit.**  Strong recursion on the entries
left: the continuing branch shortens `nep - k` (the next head's index is larger
and still below `nep`), and the terminal branch is the completion at the state
it is taken from.  The verdict and the memory are the terminal run's.  The
recursion re-enters the step at the continuing target's own `Head`, which is the
head segment's carried fact. -/
theorem stage2NoEventWalkLoopFinishes {calls : Calls} {mem : Mem} {F : Nat}
    (hstep : Stage2NoEventWalkStep calls mem F)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
    (hhead : Stage2NoEventWalkHead K mem k s) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem),
      q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
      runFuel calls (q + 2) stage2NoEventBody s = some (.ret (some (.int 64 v)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 v) := by
  have key : ∀ (m : Nat), ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      K.nep - k = m → Stage2NoEventWalkHead K mem k s →
      ∃ (q : Nat) (v : BitVec 64) (mr : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s = some (.ret (some (.int 64 v)) mr) ∧
        stage2NoEventBoundary K.a12 mem K.next0 mr (.int 64 v) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro K k s hm hhead
        rcases hstep K k s hhead with
          ⟨K', k', s', p, hseg, hnep, ha12, hn0, hklt', hk'lt⟩ |
          ⟨q, v, mr, hq, hrun, hb⟩
        · have hmeas : K'.nep - k' < m := by omega
          have hk'ne : k' < K'.nep := by omega
          obtain ⟨q, v, mr, hq', hrun', hb'⟩ :=
            ih (K'.nep - k') hmeas K' k' s' rfl hseg.seg.head'
          have hcredit := hseg.credit
          refine ⟨p + q, v, mr, by omega, ?_, ?_⟩
          · rw [show p + q + 2 = p + (q + 2) from by omega, hseg.seg.seg.run (q + 2)]
            exact hrun'
          · rw [← ha12, ← hn0]
            exact hb'
        · exact ⟨q, v, mr, by omega, hrun, hb⟩
  exact key (K.nep - k) K k s rfl hhead

/-! ### The completion from a seed run -/

/-- **The completion at the potential's budget.**  The seed's `j` steps, the
loop's run and the returning step fit `potential + the finalisation allowance`,
which is `j + F + 2 ≤ 32`'s content. -/
theorem stage2NoEventWalkCompletes_of_loop {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k j F : Nat} {sHead sEntry : State}
    (hseed : ∀ n, runFuel calls (j + n) stage2NoEventBody sEntry =
      runFuel calls n stage2NoEventBody sHead)
    (hhead : Stage2NoEventWalkHead K mem k sHead)
    (hstep : Stage2NoEventWalkStep calls mem F)
    (hF : j + F + 2 ≤ stage2NoEventFinalisationAllowance) :
    ∃ v m, runFuel calls
        (stage2NoEventWalkPotential K k + stage2NoEventFinalisationAllowance)
        stage2NoEventBody sEntry = some (.ret v m) := by
  obtain ⟨q, v, mr, hq, hrun, -⟩ :=
    stage2NoEventWalkLoopFinishes hstep K k sHead hhead
  have htotal : runFuel calls (j + (q + 2)) stage2NoEventBody sEntry =
      some (.ret (some (.int 64 v)) mr) := by
    rw [hseed (q + 2)]
    exact hrun
  have hle : j + (q + 2) ≤
      stage2NoEventWalkPotential K k + stage2NoEventFinalisationAllowance := by
    omega
  exact ⟨some (.int 64 v), mr, runFuel_mono_le hle htotal⟩

/-- **The completion at the potential's two counted terms.**  The credit is inside
`32 * nep + 8 * n` at the invariant, so the walk completes at that plus the
finalisation allowance — `stage2NoEventBudget` without the escape-position term. -/
theorem stage2NoEventWalkCompletes_of_loop_budget {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k j F : Nat} {sHead sEntry : State}
    (hseed : ∀ n, runFuel calls (j + n) stage2NoEventBody sEntry =
      runFuel calls n stage2NoEventBody sHead)
    (hhead : Stage2NoEventWalkHead K mem k sHead)
    (hstep : Stage2NoEventWalkStep calls mem F)
    (hF : j + F + 2 ≤ stage2NoEventFinalisationAllowance) :
    ∃ v m, runFuel calls (32 * K.nep + 8 * K.n + 32) stage2NoEventBody sEntry =
      some (.ret v m) := by
  obtain ⟨v, m, hrun⟩ :=
    stage2NoEventWalkCompletes_of_loop hseed hhead hstep hF
  have hpot := stage2NoEventWalkPotential_le K k
  refine ⟨v, m, runFuel_mono_le ?_ hrun⟩
  simp only [stage2NoEventFinalisationAllowance] at hpot ⊢
  omega

/-! ### At the record's budget

`stage2NoEventBudget` reads three of the ABI's words: the entry count, the
document's length and the escape count.  The two counted terms are the first two,
so the bound follows as soon as the arguments are the invariant's own words. -/

/-- **The potential's bound is inside `stage2NoEventBudget`**, at the carry's
twelve argument words. -/
theorem stage2NoEventWalkBudget_le {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    32 * K.nep + 8 * K.n + 32 ≤ stage2NoEventBudget K.a12 mem := by
  rw [h.args_eq]
  simp only [stage2NoEventBudget, stage2NoEventEntryAllowance,
    stage2NoEventByteAllowance, stage2NoEventPositionAllowance,
    stage2NoEventFinalisationAllowance, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h.nLt, Nat.mod_eq_of_lt h.nepLt]
  omega

/-- **The completion at the record's own budget.**  The walk completes at
`stage2NoEventBudget` of the carry's argument words, from the seed run, the loop's
step and the finalisation bound. -/
theorem stage2NoEventWalkCompletes_at_stage2Budget {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k j F : Nat} {sHead sEntry : State}
    (hseed : ∀ n, runFuel calls (j + n) stage2NoEventBody sEntry =
      runFuel calls n stage2NoEventBody sHead)
    (hhead : Stage2NoEventWalkHead K mem k sHead)
    (hstep : Stage2NoEventWalkStep calls mem F)
    (hF : j + F + 2 ≤ stage2NoEventFinalisationAllowance) :
    ∃ v m, runFuel calls (stage2NoEventBudget K.a12 mem) stage2NoEventBody sEntry =
      some (.ret v m) := by
  obtain ⟨v, m, hrun⟩ :=
    stage2NoEventWalkCompletes_of_loop_budget hseed hhead hstep hF
  exact ⟨v, m, runFuel_mono_le (stage2NoEventWalkBudget_le hhead.inv) hrun⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkPotential_le
#print axioms stage2NoEventWalkLoopFinishes
#print axioms stage2NoEventWalkCompletes_of_loop
#print axioms stage2NoEventWalkCompletes_of_loop_budget
#print axioms stage2NoEventWalkBudget_le
#print axioms stage2NoEventWalkCompletes_at_stage2Budget

end LeanLLVM.Refinement
