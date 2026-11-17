/-
The dispatch's three outcomes, from the dispatch's own result.

`WalkDispatchThree` (`JsonStage2WalkAssembly`) says a dispatch from the loop head is one
of three outcomes.  The producer in that module, `ofContinueAndLast`, decides which by
testing `C.k + 1 < G.nep` **before the dispatch runs**.  That test is not the dispatch's
branch, and on one case it is the wrong one.

**The case.**  A standalone string — `C.k = 0`, `G.nep = 2` — consumes two entries: the
opener and the closer.  The merge at `cleanup478.i` selects `%k.2.i = %inc208.i =
%k.0.i249 + 2 = 2`.  The head's test at `C.k = 0` is `0 + 1 < 2` and it is *true*, so
`ofContinueAndLast` takes its first branch and asks `hcont` for an outcome at
`C.k + 1 < G.nep`.  The only thing `hcont` may return there without further evidence is
the continue outcome, and `WalkDispatchOutcome.cont` demands `k2 < G.nep` — `2 < 2`,
which is false.  The dispatch is a `finish` and the split cannot say so.

**What this module does instead.**  It takes the dispatch's *actual result*: a segment
from the head whose endpoint names the block it reached — `cleanup478.i` or `if.then` —
with that endpoint's own facts.  The merge arm deliberately does **not** carry
`k2 < nepv.toNat`, `k2 < G.nep` or `k2 = nepv.toNat`; it carries the one fact the merge
supplies about its index, that the index is inside the stream (`k2 ≤ nepv.toNat`),
because the merge's test is `%k.2.i < %nep` and a walk's index never passes the count.
The classification is then a split on the *result's* index against the count, which is
the merge's own test, and the standalone string falls out as `finish` with no hypothesis
about `C.k + 1`.

**What a `finish` asserts.**  Entry-stream exhaustion at the merge and nothing more: the
index has reached the end of the entry stream, so the loop does not run again.  The
finalisation that follows still decides between acceptance and refusal — an unclosed
container or an unfinished root is refused there (`if.then485.i`'s three arms) — which is
why the consumer's terminal branch states both its verdict and its memory existentially
(`WalkTargetPost`) and is never `v = 1` here.

**Which outcomes come from what.**

| outcome | evidence |
|---|---|
| `cont` | the merge arm with `k2 < nepv.toNat`, the merge's `%nep ≤ G.nep`, and the arm's own price |
| `finish` | the merge arm with `¬ (k2 < nepv.toNat)`; with `k2 ≤ nepv.toNat` that is `k2 = nepv.toNat` |
| `finish` at the stream's end | the `mergeLast` arm: the same cells with `k2 = G.nep`, and the price read at the credit boundary |
| `refuse` | the refusal arm: the segment ends at `if.then` with the word the copy loads inside the document |

**Why there are two merge arms, and why their prices are two readings of one credit.**
`merge`'s price has a byte term, `8 · (entryPos G k2 - entryPos G C.k)`, and it is a fact
about the merge's own index that the span it crossed is charged.  Past the last entry
there is no such *span*: `entryPos G G.nep = 0` (`walkEntryPos_at_nep`), because the
position is a stream read and the index has left the stream — not because the walk has no
bytes left.  The document's bytes are still there, and the potential counts them through
`boundary`, whose byte term is the document's length at and past the terminal index
(`boundary_nep`).  So `mergeLast` states the same credit read at the boundary —
`p + 2 ≤ 32 · (k2 - C.k) + 8 · (boundary G k2 - boundary G C.k)` — and it is a separate
constructor because it also carries `k2 = G.nep`, which is what lets a caller read the
terminal index rather than infer it.  Below the stream the two readings are the same
number (`boundary_eq_entryPos`), so `toOutcome` carries `merge`'s price to the boundary
form by `terminalPrice_boundary` and both arms reach `finish` at the same price.  The
one convention across the three arms is the potential's: the byte term is the credit
consumed between the two indices, read where `boundary` reads it.

`ofContinueAndLast` stays in the tree: it is the assembly's own producer and other
modules read it, and this module's producer is a second route to the same predicate, not
a replacement of that module's statement.

**A note on `%nep`.**  `WalkInv` does not carry the register, so the producers take the
fact the loop's step already takes (`walkLoopStepThree_of_dispatchResult`'s `hnepBound`):
the merge's `%nep` is no larger than the stream.  It is what makes the continue arm's
`k2 < G.nep` follow from the merge's own test, and it is the same bound the terminal
post's merge wrapper reads (`WalkLoopEnd.nepBound`).
-/
import LeanLLVM.Refinement.JsonStage2WalkLoopStepOutcome
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkCredit

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The dispatch's result, at the block it reached -/

/-- **What the dispatch actually did.**  A counted segment from the loop head whose
endpoint is classified by the block it reached and the facts that block leaves, and not
by any test on the index before the dispatch runs.

The merge arm's index `k2` is `cleanup478.i`'s `%k.2.i` and `nepv` its `%nep`; the arm
says the index advanced and stayed inside the stream (`C.k < k2 ≤ nepv.toNat`) and
carries the price, and it says nothing else about `k2`.  In particular it does not say
`k2 < nepv.toNat` — that is the merge's test, which this predicate lets the caller read
— and it does not say `k2 < G.nep`, which is what the old producer's split demanded.

The refusal arm is the same segment ending at the refusal copy with the error offset
inside the document. -/
inductive WalkDispatchResult (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) : Prop
  /-- **The dispatch reached the merge.**  `cleanup478.i`'s two `phi` selections, the
  register `%nep`, an index strictly advanced and no larger than the entry count, the
  merge's depth inside the stacks, and the price.  Whether the merge then goes back to
  the head or leaves the loop is its test's own reading of `k2` against `nepv`. -/
  | merge (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64)
      (seg : WalkSegment calls G C s Cd sd p)
      (hblock : Cd.block = "cleanup478.i") (hk : Cd.k = C.k)
      (hpre : sd.pre = some prev)
      (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
      (hspv : evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)))
      (hkOp : phiIncoming prev cleanupKIncoming = some kOp)
      (hk2 : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)))
      (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
      (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
      (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ Cd.wlen)
      (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k))
  /-- **The dispatch reached the merge past the last entry.**  The same two `phi`
  selections, the same register `%nep`, the same bounds and the same counted segment as
  `merge`; the index is the stream's end and the price reads the byte credit at the
  boundary.

  **Why the price is stated this way.**  `entryPos G G.nep = 0`
  (`walkEntryPos_at_nep`), so the byte term `merge`'s price states through `entryPos` is
  *not applicable* past the last entry — it is not that the span is empty, it is that the
  index has left the stream the position is read from.  The credit does not vanish:
  `boundary G G.nep = G.n` (`boundary_nep`), so at `k2 = G.nep` the term is
  `8·(G.n - entryPos G C.k)`, the document bytes the entry has left to reach — which the
  potential already counts and which pays the trailing whitespace run and scan
  (`runLast_price_with_credit`, `JsonStage2WalkDispatchRun`).  The result is the same shape
  `refuse` states, with `k2` in place of `G.nep`. -/
  | mergeLast (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64)
      (seg : WalkSegment calls G C s Cd sd p)
      (hblock : Cd.block = "cleanup478.i") (hk : Cd.k = C.k)
      (hpre : sd.pre = some prev)
      (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
      (hspv : evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)))
      (hkOp : phiIncoming prev cleanupKIncoming = some kOp)
      (hk2 : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)))
      (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
      (hlast : k2 = G.nep)
      (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
      (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ Cd.wlen)
      (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (boundary G k2 - boundary G C.k))
  /-- **The dispatch reached the refusal copy.**  The token was rejected before the merge
  at any index, so the segment ends at `if.then` with the word the copy's `%off` load
  reads — a stored word inside the document — and the price inside the remaining
  entries' and bytes' credit.

  The word is the refusal's own store, read at the endpoint's memory: each arm that
  reaches `if.then` writes `wordBytes 8 k` at `%e + 8` and the copy loads it
  (`WalkRefuseSegment`, `JsonStage2WalkTraverse`).  It is not the carry's `eoff`:
  `WalkInv.eoff_le` bounds that word, and the copy reports the one it loaded. -/
  | refuse (Cd : WalkCarry G) (sd : State) (p : Nat)
      (seg : WalkSegment calls G C s Cd sd p)
      (hblock : Cd.block = "if.then")
      (hrw : ∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k))
      (herr : Cd.eoff ≤ G.n)
      (hprice : p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k))

/-- **A result is one of the three outcomes.**  The split is on the merge's own test,
`%k.2.i < %nep`, which is `k2` against `nepv` — the dispatch's *result* index against
the count — and never on `C.k + 1`.

`hcap` closes the exit arm into an equation: the index is inside the stream and not below
it, so it *is* the stream's end, which is `finish`'s `hterm`.  `hnepBound` supplies the
continue arm's `k2 < G.nep` from `k2 < nepv.toNat` and the count's own bound; that is a
fact about `%nep` at the merge, and it is the same one the loop's step takes beside the
three outcomes.

The `mergeLast` arm is the same equation with its evidence already in hand: `hlast` makes
the index the stream's end, `hnepBound` makes `%nep` no larger, and `hcap` makes it no
smaller, so `hterm` is the three together.  Its price is already stated at the credit
boundary, which is `finish`'s form, so the arm hands it over unchanged. -/
theorem WalkDispatchResult.toOutcome {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (r : WalkDispatchResult calls G C s)
    (hnepBound : ∀ (nepv : BitVec 64), ∀ (Cd : WalkCarry G) (sd : State),
      WalkInv G Cd sd → Cd.block = "cleanup478.i" →
      lookupName sd.env "%nep" = some (.int 64 nepv) → nepv.toNat ≤ G.nep) :
    WalkDispatchOutcome calls G C s := by
  cases r with
  | merge Cd sd p spv k2 prev spOp kOp nepv seg hblock hk hpre hsp hspv hkOp hk2 hnepv
      hadvance hcap hspcap hspw hprice =>
    -- the head's index is inside the stream, so the two spellings of the credit agree
    have hkc : C.k < G.nep := by
      have := hnepBound nepv Cd sd seg.inv' hblock hnepv
      omega
    by_cases hbelow : k2 < nepv.toNat
    · exact WalkDispatchOutcome.cont Cd sd p spv k2 prev spOp kOp nepv seg hblock hk hpre
        hsp hspv hkOp hk2 hnepv hbelow
        (by have := hnepBound nepv Cd sd seg.inv' hblock hnepv; omega)
        hadvance hspcap hspw hprice
    · exact WalkDispatchOutcome.finish Cd sd p k2 prev kOp nepv seg hblock hpre hkOp hk2
        hnepv (by omega) (terminalPrice_boundary G hkc hprice)
  | mergeLast Cd sd p spv k2 prev spOp kOp nepv seg hblock hk hpre hsp hspv hkOp hk2 hnepv
      hlast hadvance hcap hspcap hspw hprice =>
    have hterm : k2 = nepv.toNat := by
      have := hnepBound nepv Cd sd seg.inv' hblock hnepv
      omega
    exact WalkDispatchOutcome.finish Cd sd p k2 prev kOp nepv seg hblock hpre hkOp hk2
      hnepv hterm hprice
  | refuse Cd sd p seg hblock _hrw herr hprice =>
    exact WalkDispatchOutcome.refuse Cd sd p seg hblock herr hprice

/-! ### The producer -/

/-- **`WalkDispatchThree`, from the dispatch's result.**  No hypothesis on
`C.k + 1 < G.nep`: the outcome is the one the dispatch's own endpoint supports, and each
head state supplies its own. -/
theorem WalkDispatchThree.ofResult {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (hres : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      WalkDispatchResult calls G C s)
    (hnepBound : ∀ (nepv : BitVec 64), ∀ (Cd : WalkCarry G) (sd : State),
      WalkInv G Cd sd → Cd.block = "cleanup478.i" →
      lookupName sd.env "%nep" = some (.int 64 nepv) → nepv.toNat ≤ G.nep) :
    WalkDispatchThree calls G := by
  intro C s hInv hhead
  exact (hres C s hInv hhead).toOutcome hnepBound

/-- **The loop's step, straight from the dispatch's result.**  Each head state's own
result decides the branch, and the two terminal arms read the post producers at the
data the result carries: the merge's `phi` operands and their values, the carry's
index, the merge's `%nep` and its `hterm`, and — on the refusal arm — the endpoint's
own block.  So this is the rule the layer applies, and the reason it is stated on
`WalkDispatchResult` rather than on `WalkDispatchOutcome`: the `finish` outcome does not
carry the depth operand's value, which decides the accept/refuse split at
`if.then485.i` (`walkFinishPost_merge`'s case), and the merge arm does.

The two terminal branches spend the dispatch's own price (`hprice`) and the terminal
post's own count (`q + 2 ≤ 27`), and both fit `p + q ≤ walkPotential G C + F` at
`F ≥ 27`.  Neither asserts acceptance, and neither fixes the verdict. -/
theorem walkLoopStepThree_of_dispatchResult {calls : Calls} {m0 : Mem}
    {G : WalkGeom m0} {F : Nat} (hF : 27 ≤ F)
    (hres : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      WalkDispatchResult calls G C s)
    (hmerge : ∀ (Cd : WalkCarry G) (sd : State) (p spv k2 : Nat) (prev : String)
      (spOp kOp : Operand) (nepv : BitVec 64),
      WalkInv G Cd sd → Cd.block = "cleanup478.i" → sd.pre = some prev →
      phiIncoming prev cleanupSpIncoming = some spOp →
      evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)) →
      phiIncoming prev cleanupKIncoming = some kOp →
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) →
      lookupName sd.env "%nep" = some (.int 64 nepv) → k2 = nepv.toNat →
      WalkTargetPost calls G Cd sd)
    (hrefuse : ∀ (Cd : WalkCarry G) (sd : State), WalkInv G Cd sd →
      Cd.block = "if.then" →
      (∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)) →
      WalkTargetPost calls G Cd sd)
    (hnepBound : ∀ (nepv : BitVec 64), ∀ (Cd : WalkCarry G) (sd : State),
      WalkInv G Cd sd → Cd.block = "cleanup478.i" →
      lookupName sd.env "%nep" = some (.int 64 nepv) → nepv.toNat ≤ G.nep) :
    WalkLoopStepThree calls G F := by
  intro C s hInv hhead hk
  rcases hres C s hInv hhead with
    ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblock, hkc, hpre, hsp, hspv,
      hkOp, hk2, hnepv, hadvance, hcap, hspcap, hspw, hprice⟩ |
    ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, seg, hblock, hkc, hpre, hsp, hspv,
      hkOp, hk2, hnepv, hlast, hadvance, hcap, hspcap, hspw, hprice⟩ |
    ⟨Cd, sd, p, seg, hblock, hrw, _herr, hprice⟩
  · by_cases hbelow : k2 < nepv.toNat
    · exact Or.inl (walkContRevolution seg hblock hkc hpre hsp hspv hkOp hk2 hnepv
        hbelow (by have := hnepBound nepv Cd sd seg.inv' hblock hnepv; omega)
        hadvance hspcap hspw hprice)
    · have hterm : k2 = nepv.toNat := by omega
      obtain ⟨q, v, m, hq, hrun, hb⟩ :=
        hmerge Cd sd p spv k2 prev spOp kOp nepv seg.inv' hblock hpre hsp hspv hkOp hk2
          hnepv hterm
      refine Or.inr ⟨p + q, v, m, ?_, ?_, hb⟩
      · have hk2nep : k2 ≤ G.nep := by
          have := hnepBound nepv Cd sd seg.inv' hblock hnepv
          omega
        have hcredit := walkFinishCredit_le (G := G) (C := C) hk (by omega) hk2nep
        simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
          stage2ByteAllowance] at hcredit hprice hq ⊢
        omega
      · rw [show p + q + 2 = p + (q + 2) from by omega, seg.run (q + 2)]
        exact hrun
  · -- the terminal merge: its index is the stream's end, so the outcome is `finish`
    have hterm : k2 = nepv.toNat := by
      have := hnepBound nepv Cd sd seg.inv' hblock hnepv
      omega
    obtain ⟨q, v, m, hq, hrun, hb⟩ :=
      hmerge Cd sd p spv k2 prev spOp kOp nepv seg.inv' hblock hpre hsp hspv hkOp hk2
        hnepv hterm
    refine Or.inr ⟨p + q, v, m, ?_, ?_, hb⟩
    · have hk2nep : k2 ≤ G.nep := by rw [hlast]
      have hcredit := walkFinishCreditBoundary_le (G := G) (C := C) hk hk2nep
      have hbound := boundary_le G k2
      simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
        stage2ByteAllowance] at hcredit hprice hq ⊢
      omega
    · rw [show p + q + 2 = p + (q + 2) from by omega, seg.run (q + 2)]
      exact hrun
  · obtain ⟨q, v, m, hq, hrun, hb⟩ := hrefuse Cd sd seg.inv' hblock hrw
    refine Or.inr ⟨p + q, v, m, ?_, ?_, hb⟩
    · simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
        stage2ByteAllowance] at hprice hq ⊢
      omega
    · rw [show p + q + 2 = p + (q + 2) from by omega, seg.run (q + 2)]
      exact hrun

/-! ### The last entry's bundle, as a result

`HlastFacts` is the input's facts at the last entry, and its merge path —
`hlast_toMerge`'s counted segment to `cleanup478.i` — is the arm here.  It needs no
`¬ (C.k + 1 < G.nep)`: the guard is what selects *which bundle describes a head
state*, and it does not classify the dispatch, so it does not appear here.

The refusal path (`hlast_refuse`) reaches the copy at `if.then` with `%4`'s word at
`%e + 8`, not the carry's `eoff`, so it is not the `refuse` arm's word: that arm
carries the segment's own store (`WalkRefuseSegment`), and the last entry's refusal is
carried by its own arms (`quoteRefuse_at`, `bracketRefuse_at`, `commaRefuse_at`,
`colonRefuse_at`, `closeWithOpen_at`) rather than forced through this bundle.

The merge arm's evidence is `hlast_finish`'s, read at the endpoint that lemma names
(`hlastMergeCF f`, `hlastMergeF f`) rather than through its existential: the arm has to
carry the endpoint's own carry (its index is `C.k`, which is what the revolution's price
is stated against) and that carry is opaque inside an existential.  The price is the same
arithmetic as the continuing arm's: `hlast_finish` states the entry position's byte term,
`walkEntryPos_at_nep` makes it zero at the stream's end, and `G.nep - C.k = 1` pays for
the path.

**Why this arm builds `merge` and not `mergeLast`.**  `hlastFacts_of_staging` gives the
index's equation (`hk2nep`) as well as the segment, so the byte term is here to be
discharged — `walkEntryPos_at_nep` makes it zero — and the price is stated in `merge`'s
own spelling.  `mergeLast` is the arm for the producer that reads the credit at the
boundary (the run class's composition, `runLastMerge_at`), whose byte term is the
document's remaining bytes rather than the zero `entryPos` totalises to.  Both are prices
the potential pays, and a result that stated the shorter where the longer is proved would
be needlessly weak; `mergeLast`'s `k2 = G.nep` is what keeps the boundary reading from
standing in for `merge` elsewhere. -/

/-- **The `merge` arm from the last entry's bundle.**  The dispatch reaches
`cleanup478.i` at `%k.2.i = %nep`, so its index is the stream's end and its outcome is
`finish`; the depth is the merge's `%sp.i.0248` and the two bounds are the invariant's.
The premise is `HlastFacts` and nothing else — no test on the head's index. -/
theorem WalkDispatchResult.ofHlastMerge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HlastFacts G C s) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨seg, hinv⟩ := hlast_toMerge G C s hInv hblock f
  refine WalkDispatchResult.merge (hlastMergeCF f) (hlastMergeF f)
    ((((((6 + 1) + 5) + 3) + 3) + 1) + 1) (hlastMergeCF f).sp f.k2 "if.end473.i"
    (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") f.nepv seg rfl rfl rfl (by decide)
    hinv.depth_reg (by decide) f.hk2 f.hnepM ?_ ?_ hinv.depth_cap hinv.sp_le_wlen ?_
  · have h1 := f.hlastK
    have h2 := f.hk2nep
    show C.k < f.k2
    omega
  · show f.k2 ≤ f.nepv.toNat
    rw [f.hterm]
  · rw [f.hk2nep, walkEntryPos_at_nep G]
    have hΔ : G.nep - C.k = 1 := by rw [← f.hlastK]; omega
    simp only [Nat.zero_sub, Nat.mul_zero, Nat.add_zero, stage2EntryAllowance, hΔ]
    omega

/-! ### The standalone string

`C.k = 0` and `G.nep = 2`: the head's test is `0 + 1 < 2`, true, and the merge's index is
`2`, the stream's end.  The old producer's split takes the continue branch there and
demands `2 < 2`.  This is the same result stated as an outcome, with no such demand: the
merge's index is the count, and the outcome is `finish`. -/

/-- **The standalone string is a `finish`.**  The merge reached `cleanup478.i` with
`%k.2.i = 2` and `%nep = 2`, so the entry stream is exhausted at the merge and the loop
does not run again.  The price is the dispatch's own, at `Δk = 2 - C.k` and the byte
credit between the head's index and the stream's end read at the boundary — at `C.k = 0`
two entry allowances and the document from its first byte.

Nothing here asserts acceptance: the finalisation that follows decides, and an unclosed
string is refused there. -/
theorem standaloneString_finish {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {Cd : WalkCarry G} {sd : State} {p : Nat}
    {prev : String} {kOp : Operand}
    (seg : WalkSegment calls G C s Cd sd p) (hblock : Cd.block = "cleanup478.i")
    (hpre : sd.pre = some prev)
    (hkOp : phiIncoming prev cleanupKIncoming = some kOp)
    (hk2 : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 2)))
    (hnepv : lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 2)))
    (hprice : p + 2 ≤ stage2EntryAllowance * (2 - C.k) +
      stage2ByteAllowance * (boundary G 2 - boundary G C.k)) :
    WalkDispatchOutcome calls G C s :=
  WalkDispatchOutcome.finish Cd sd p 2 prev kOp (BitVec.ofNat 64 2) seg hblock hpre hkOp
    hk2 hnepv (by decide) hprice

/-- **The standalone string's dispatch is a result, at the values the merge leaves.**  The
merge arm at `k2 = 2` and `nepv = 2`: the index advanced past the head's `0` and stayed
inside the stream, which is exactly `0 < 2 ≤ 2`.  With `standaloneString_finish` this is
the case `ofContinueAndLast`'s split cannot express, and it needs no `k2 < G.nep`. -/
theorem standaloneString_result {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {Cd : WalkCarry G} {sd : State} {p spv : Nat}
    {prev : String} {spOp kOp : Operand}
    (seg : WalkSegment calls G C s Cd sd p) (hblock : Cd.block = "cleanup478.i")
    (hk : Cd.k = C.k) (hpre : sd.pre = some prev)
    (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
    (hspv : evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hkOp : phiIncoming prev cleanupKIncoming = some kOp)
    (hk2 : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 2)))
    (hnepv : lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 2)))
    (hk0 : C.k = 0) (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ Cd.wlen)
    (hprice : p + 2 ≤ stage2EntryAllowance * (2 - C.k) +
      stage2ByteAllowance * (entryPos G 2 - entryPos G C.k)) :
    WalkDispatchResult calls G C s :=
  WalkDispatchResult.merge Cd sd p spv 2 prev spOp kOp (BitVec.ofNat 64 2) seg hblock hk
    hpre hsp hspv hkOp hk2 hnepv (by omega) (by decide) hspcap hspw hprice

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkDispatchResult.toOutcome
#print axioms LeanLLVM.Refinement.WalkScope.WalkDispatchThree.ofResult
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStepThree_of_dispatchResult
#print axioms LeanLLVM.Refinement.WalkScope.WalkDispatchResult.ofHlastMerge
#print axioms LeanLLVM.Refinement.WalkScope.standaloneString_finish
#print axioms LeanLLVM.Refinement.WalkScope.standaloneString_result

end WalkScope

end LeanLLVM.Refinement
