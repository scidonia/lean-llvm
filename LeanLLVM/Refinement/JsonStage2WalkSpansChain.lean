/-
# The `[1]` walk's carry chain: seed, opener, number, closer, and the head passes between

`spans_nil_of_three_arms` (`JsonStage2WalkSpansNil`) states the span half of the
release's last premise: if the *merge* carry at `cleanup478.i` is the opener's
(`openC₉`), then the scalar arm's (`scMergeC`), then the closer's (`closeCEnd`), a
seed with no span leaves the merge's list empty.  It takes the three equations as
hypotheses; what it does not say is where the walks' carries come from.

This module supplies that half for the document `[1]` (`evbDoc`, one opener, one
numeral and one closer, `nep = 3`).  The walk's carries are, in order:

* the **seed** `walkSeed G S`, whose `spans` field is `[]` — the seed's own `rfl`;
* the **opener's merge** `C₁ = openC₉ (openHeadC C₀) b`, the carry `openTailSeg`
  reaches (`JsonStage2WalkDispatchOpeners:748`, composed with `openBracketHead`).
  The arm's endpoint names `openHeadC C₀`, not `C₀`; the head carry's only change
  is the block, so its span list is the source's (`openHeadC_spans`, `rfl`);
* the **number's merge** `C₂ = scMergeC H₁ ev`, exactly the carry
  `walkRevolutionMergeSegScalar` (`JsonStage2WalkHcontScalar:1246`) names.  Its
  *source* is not `C₁` but the loop-head carry the revolution reaches, `H₁`.  This
  is the one identification the arm lemmas do not expose: a `WalkSegment` records a
  run and an invariant, not a relation between two carries, so the step from `C₁`
  at `cleanup478.i` back to the head is the back edge and the header's pass — and
  those two steps *do* expose it (`walkBack_step_at`, `whileBody_step`): their
  target carry is the record update `headPassC` defined below, whose `def` is the
  two steps' own term;
* the **closer's merge** `C₃ = closeCEnd (closeC₁₀b H₂) spz c8`, the carry the
  closer's route builds (`JsonStage2WalkDispatchClosers:1615`).  `closeC₁₀b` is a
  block update, so the span list is `H₂`'s (`closeC₁₀b_spans`, `rfl`), and
  `closeCEnd` keeps it too (`closeCEnd_spans`).

**What the closer's public lemma does not expose.**  `closeBracketMerge_at`
(`JsonStage2WalkDispatchClosers:1343`) concludes a `WalkDispatchResult`, whose
`merge` constructor binds the target carry existentially.  The exact term
`closeCEnd (closeC₁₀b H) spz c8` is visible only inside the proof (its `hseg11`),
so a caller holding the lemma's type cannot write `C₃`'s identification.  The chain
theorem therefore states the closer's contribution as the span equation
`C₃.spans = H₂.spans`, which is what the release reads, and reports the carry term
as the gap it is.  Two variants are given: `spans_nil_of_arm_chain` takes the
closer's carry by term (for a caller that has descended into the route), and
`spans_nil_of_arm_spans` takes it by span list (for a caller holding
`closeBracketMerge_at` or `LastEntryArm.dispatch`).

**The composition.**  `bracketChainSegment` composes the five counted segments —
the opener's 9, the revolution's 2, the number's `p₂`, the revolution's 2 and the
closer's `p₃` — and `bracket_walk_chain` adds the span result and the invariant at
the composed endpoint.  `evb_emission_of_bracket_walk` is `evb_emission_of_walk_accept`
at that end state: the span-list premise is the chain's, not an assumption, no
arena word at the walk is taken, and the returned memory enters as the four reads
`JsonWalkReads` names rather than as an equation with the accept finalisation.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2WalkSpansNil
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkScopeStaged
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seed's span list -/

/-- **The seed reserves nothing.**  `walkSeed`'s `spans` field is the empty list, so
the chain's base case is the definition and not a hypothesis. -/
theorem walkSeed_spans {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).spans = [] := rfl

/-! ### The two record updates an arm's endpoint names over

The opener's tail is stated at `openHeadC C` (`{ C with block := "if.then.i" }`) and
the closer's at `closeC₁₀b C` (a nested block update).  Both change the block only,
so neither moves the span list; each is one projection and one `rfl`. -/

/-- The opener's head carry keeps the span list. -/
theorem openHeadC_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (openHeadC C).spans = C.spans := rfl

/-- The closer's `LeafBlock25`/`cond.end.i` carries keep the span list. -/
theorem closeC₁₀b_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (closeC₁₀b C).spans = C.spans := rfl

/-! ### The revolution's head carry

`WalkDispatch.revolution` names the state and leaves the carry as a `let`; the two
steps it is built from (`walkBack_step_at`, `whileBody_step`) state the carry
directly.  That term is named here once, so the chain can write it. -/

/-- **The loop head a revolution reaches**: the merge's back edge (block
`while.body.i`, the inner allowance reset) and the header's pass (block
`NodeBlock21`, the merge's `%k.2.i` and `%sp.i.1`).  Both steps are record updates
on the merge carry, so every field they do not name — and in particular `spans` —
is the merge's. -/
abbrev headPassC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 spv : Nat) :
    WalkCarry G :=
  { { C with block := "while.body.i", inner := walkInnerCap G } with
      block := "NodeBlock21", k := k2, sp := spv }

/-- **A revolution keeps the span list.**  The two updates move the block, the
inner allowance, the index and the depth; `spans` is untouched. -/
theorem headPassC_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 spv : Nat) :
    (headPassC C k2 spv).spans = C.spans := rfl

/-- The head carry is the loop head, by the header's own block. -/
theorem headPassC_block {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 spv : Nat) :
    (headPassC C k2 spv).block = walkLoopHead := rfl

/-- The head carry's index is the merge's `%k.2.i`. -/
theorem headPassC_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 spv : Nat) :
    (headPassC C k2 spv).k = k2 := rfl

/-- The head carry's depth is the merge's `%sp.i.1`. -/
theorem headPassC_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 spv : Nat) :
    (headPassC C k2 spv).sp = spv := rfl

/-! ### The revolution as a counted segment

The dispatch's segment ends at `cleanup478.i`; the next arm starts at the loop
head.  Between them are the merge's back edge and the header's pass, two steps
whose carries the two step lemmas name.  This is the segment
`WalkDispatch.revolution` builds, with the carry named rather than existential. -/

/-- **One revolution's closing steps**: from a merge carry and its two `phi`
selections to the next loop head, at the merge's own `%k.2.i` and `%sp.i.1`.
`walkBack_step_at` reaches `cleanup478Out` at the back-edge carry and
`whileBody_step` reaches the head at `headPassC`. -/
theorem headPassSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {prev : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some prev)
    (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming prev cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) (hcap : k2 < G.nep) (hadvance : C.k < k2)
    (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ C.wlen) :
    ∃ s' : State,
      WalkSegment (stage2Calls stage2SubCalls) G C s (headPassC C k2 spv) s' 2 := by
  obtain ⟨-, hInvB, hrunB⟩ :=
    walkBack_step_at G C s hInv hblock hpre hsp hspv hk hkv hnep hguard
  obtain ⟨s', -, hInvH, -, hrunH⟩ :=
    whileBody_step (G := G)
      (C := { C with block := "while.body.i", inner := walkInnerCap G })
      (s := cleanup478Out s spv k2) hInvB rfl (cleanup478Out_pre) (cleanup478Out_k)
      (cleanup478Out_sp) (by simpa using hadvance) hcap hspcap (by simpa using hspw)
  refine ⟨s', ?_⟩
  refine ⟨?_, hInvH, rfl⟩
  intro n
  rw [show 2 + n = 1 + (1 + n) from by omega, hrunB (1 + n), hrunH n]

/-! ### The three arms and the two head passes

The span half of the chain, in the form the release reads.  The seed is at
`openHeadC C₀` for the purpose of `spans_nil_of_three_arms` — that carry's list is
`C₀`'s — so the theorem is that lemma's head-free instance at the arm carry the
opener's own tail names. -/

/-- **The three-arm chain, with the revolution's head passes.**  If the opener's
merge is `openC₉ (openHeadC C₀) b`, the first head pass reaches `H₁`, the number's
merge is `scMergeC H₁ ev`, the second head pass reaches `H₂`, the closer's merge is
`closeCEnd (closeC₁₀b H₂) spz c8`, and the seed carry has no span, then the
closer's merge has no span.

The two head carries are the ones `headPassSeg` produces; `spans_nil_of_three_arms`
is applied at the opener's arm carry (`openHeadC C₀`, whose list is `C₀`'s) and at
the canonical number and closer carries, and the head passes transport the span
list between the arm carries and the canonical ones. -/
theorem spans_nil_of_arm_chain {m0 : Mem} {G : WalkGeom m0}
    {C₀ C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    (h₁ : C₁ = openC₉ (openHeadC C₀) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8)
    (h₀ : C₀.spans = []) : C₃.spans = [] := by
  have hcanon : (closeCEnd (scMergeC C₁ ev) spz c8).spans = [] := by
    refine spans_nil_of_three_arms (C₀ := openHeadC C₀) (C₁ := C₁)
      (C₂ := scMergeC C₁ ev) (C₃ := closeCEnd (scMergeC C₁ ev) spz c8)
      (b := b) (ev := ev) (spz := spz) (c8 := c8) ?_ ?_ ?_ ?_
    · exact h₁
    · rfl
    · rfl
    · rw [openHeadC_spans]; exact h₀
  have hC : C₃.spans = C₁.spans := by
    rw [h₃, closeCEnd_spans, closeC₁₀b_spans, hH₂, headPassC_spans,
      h₂, scMergeC_spans, hH₁, headPassC_spans]
  have hCE : (closeCEnd (scMergeC C₁ ev) spz c8).spans = C₁.spans := by
    rw [closeCEnd_spans, scMergeC_spans]
  rw [hC, ← hCE]
  exact hcanon

/-- **The same chain when the closer's carry is known only by its span.**  A caller
holding `closeBracketMerge_at` (or `LastEntryArm.dispatch`) has a
`WalkDispatchResult`, whose merge carry is existential; what it can state is that
the closer's merge does not reserve, `C₃.spans = H₂.spans`.  The rest of the chain
is the term-level one. -/
theorem spans_nil_of_arm_spans {m0 : Mem} {G : WalkGeom m0}
    {C₀ C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {b : BitVec 8} {ev : EventRecord}
    {k₁ sp₁ k₂ sp₂ : Nat}
    (h₁ : C₁ = openC₉ (openHeadC C₀) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃.spans = H₂.spans)
    (h₀ : C₀.spans = []) : C₃.spans = [] := by
  have hcanon : (closeCEnd (scMergeC C₁ ev) (BitVec.ofNat 32 0) (BitVec.ofNat 8 0)).spans
      = [] := by
    refine spans_nil_of_three_arms (C₀ := openHeadC C₀) (C₁ := C₁)
      (C₂ := scMergeC C₁ ev)
      (C₃ := closeCEnd (scMergeC C₁ ev) (BitVec.ofNat 32 0) (BitVec.ofNat 8 0))
      (b := b) (ev := ev) (spz := BitVec.ofNat 32 0) (c8 := BitVec.ofNat 8 0) ?_ ?_ ?_ ?_
    · exact h₁
    · rfl
    · rfl
    · rw [openHeadC_spans]; exact h₀
  have hC : C₃.spans = C₁.spans := by
    rw [h₃, hH₂, headPassC_spans, h₂, scMergeC_spans, hH₁, headPassC_spans]
  have hCE : (closeCEnd (scMergeC C₁ ev) (BitVec.ofNat 32 0) (BitVec.ofNat 8 0)).spans
      = C₁.spans := by
    rw [closeCEnd_spans, scMergeC_spans]
  rw [hC, ← hCE]
  exact hcanon

/-! ### The opener's armed segment, at its own endpoint

`containerOpenSeg` concludes existentially, although its proof's target is the
tail's `openC₉ (openHeadC C) b`.  The two links it composes are stated at that
term, so the bracket's route is restated with the carry exposed. -/

/-- **The bracket opener's segment to the merge**, at the carry `openTailSeg`
names.  Four head links (`openBracketHead`) and the tail's five
(`openTailSeg`), nine in all. -/
theorem bracketOpenSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91)
    (hbe : b = BitVec.ofNat 8 (entryByte G C.k).toNat)
    (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkSegment (stage2Calls stage2SubCalls) G C s
      (openC₉ (openHeadC C) b) (openS₉ (openHeadC C) (openBrS₄ s) r rd b) 9 := by
  have hbe91 : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 :=
    hbe.symm.trans hopen
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have hhead := openBracketHead G C s hInv hblock (by rw [← hopen]; exact h8) hbe91
  have htail := openTailSeg G (openHeadC C) (openBrS₄ s) hhead.inv' rfl hbe hsp519
    (by rw [openBrS₄_mem]; exact hread)
    (by rw [openBrS₄_mem, openBrS₄_next]; exact hpreV)
    r hcall hret hklt
  exact hhead.trans htail

/-! ### The chain, composed

The five counted pieces: the opener's nine, the revolution's two, the number's
`p₂`, the revolution's two, the closer's `p₃`. -/

/-- **The `[1]` walk from the seed to the closer's merge**, as one counted segment.
The carries and states are the pieces' own; the composition is `WalkSegment.trans`
five times. -/
theorem bracketChainSegment {m0 : Mem} {G : WalkGeom m0}
    {C₀ C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {s₀ s₁ sh₁ s₂ sh₂ s₃ : State}
    {p₁ p₂ p₃ : Nat}
    (hopen : WalkSegment (stage2Calls stage2SubCalls) G C₀ s₀ C₁ s₁ p₁)
    (hhead₁ : WalkSegment (stage2Calls stage2SubCalls) G C₁ s₁ H₁ sh₁ 2)
    (hnumber : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁ C₂ s₂ p₂)
    (hhead₂ : WalkSegment (stage2Calls stage2SubCalls) G C₂ s₂ H₂ sh₂ 2)
    (hcloser : WalkSegment (stage2Calls stage2SubCalls) G H₂ sh₂ C₃ s₃ p₃) :
    WalkSegment (stage2Calls stage2SubCalls) G C₀ s₀ C₃ s₃
      ((((p₁ + 2) + p₂) + 2) + p₃) :=
  (((hopen.trans hhead₁).trans hnumber).trans hhead₂).trans hcloser

/-- **The chain's end: the invariant and the empty span list.**  The composed
segment supplies `WalkInv` at `C₃`; the five carry identifications supply the span
list through `spans_nil_of_arm_chain`. -/
theorem bracket_walk_chain {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {s₀ s₁ sh₁ s₂ sh₂ s₃ : State}
    {p₁ p₂ p₃ : Nat} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    (hopen : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀ C₁ s₁ p₁)
    (hhead₁ : WalkSegment (stage2Calls stage2SubCalls) G C₁ s₁ H₁ sh₁ 2)
    (hnumber : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁ C₂ s₂ p₂)
    (hhead₂ : WalkSegment (stage2Calls stage2SubCalls) G C₂ s₂ H₂ sh₂ 2)
    (hcloser : WalkSegment (stage2Calls stage2SubCalls) G H₂ sh₂ C₃ s₃ p₃)
    (h₁ : C₁ = openC₉ (openHeadC (walkSeed G S)) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8) :
    WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀ C₃ s₃
        ((((p₁ + 2) + p₂) + 2) + p₃) ∧
      WalkInv G C₃ s₃ ∧ C₃.spans = [] := by
  have hseg := bracketChainSegment hopen hhead₁ hnumber hhead₂ hcloser
  refine ⟨hseg, hseg.inv', ?_⟩
  exact spans_nil_of_arm_chain h₁ hH₁ h₂ hH₂ h₃ (walkSeed_spans G S)

/-- **The chain with the opener's segment produced, not assumed.**  `bracketOpenSeg`
builds `[1]`'s nine opener steps from the seed state, at the carry `openTailSeg`
names; the opener's identification is therefore that segment's endpoint and not a
hypothesis.  The remaining four segments are the caller's — the revolution's two,
the number's and the closer's — because their source states are the head states the
revolution's step lemons reach existentially. -/
theorem bracket_walk_chain_open {m0 : Mem} (G : WalkGeom m0) {S : WalkStage G}
    {s₀ : State} {b : BitVec 8}
    (hInv₀ : WalkInv G (walkSeed G S) s₀)
    (h8₀ : evalOperand s₀ (.reg "%8") = some (.int 8 b))
    (hopen₀ : b = BitVec.ofNat 8 91)
    (hbe₀ : b = BitVec.ofNat 8 (entryByte G (walkSeed G S).k).toNat)
    {rd : BitVec 32}
    (hread₀ : readBytes s₀.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV₀ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s₀.mem s₀.next)
    (r : CallOutcome)
    (hcall₀ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s₀.mem s₀.next =
        some r)
    (hret₀ : r.ret = .int 32 (BitVec.ofNat 32 1))
    {H₁ C₂ H₂ C₃ : WalkCarry G} {sh₁ s₂ sh₂ s₃ : State} {p₂ p₃ : Nat}
    {ev : EventRecord} {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    (hhead₁ : WalkSegment (stage2Calls stage2SubCalls) G
      (openC₉ (openHeadC (walkSeed G S)) b)
      (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b) H₁ sh₁ 2)
    (hnumber : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁ C₂ s₂ p₂)
    (hhead₂ : WalkSegment (stage2Calls stage2SubCalls) G C₂ s₂ H₂ sh₂ 2)
    (hcloser : WalkSegment (stage2Calls stage2SubCalls) G H₂ sh₂ C₃ s₃ p₃)
    (hH₁ : H₁ = headPassC (openC₉ (openHeadC (walkSeed G S)) b) k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8) :
    WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀ C₃ s₃
        ((((9 + 2) + p₂) + 2) + p₃) ∧
      WalkInv G C₃ s₃ ∧ C₃.spans = [] := by
  have hsp0 : (walkSeed G S).sp ≤ 519 := by
    show 0 ≤ 519
    decide
  have hopen := bracketOpenSeg G (walkSeed G S) s₀ hInv₀ (walkSeed_block G S) h8₀
    hopen₀ hbe₀ hsp0 hread₀ hpreV₀ r hcall₀ hret₀
  exact bracket_walk_chain hopen hhead₁ hnumber hhead₂ hcloser rfl hH₁ h₂ hH₂ h₃

/-! ### `[1]`'s three entry bytes

The document the chain is stated at.  `evbDoc` is `[1]`; its entry stream is
`[0, 1, 2]`, so the three entries are the document's three bytes: the opener at
position zero, the numeral at one, the closer at two.  These are the bytes the
opener's `h8`/`hbe` and the closer's read, and they are the document's, not the
run's. -/

/-- **`[1]`'s entry bytes and positions.**  With `G.bs = evbDoc` and
`G.ent = [0, 1, 2]`, the entries' document bytes are `[`, `1`, `]` and their
positions are `0`, `1`, `2`. -/
theorem evbDoc_entryBytes {m0 : Mem} {G : WalkGeom m0}
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    entryPos G 0 = 0 ∧ entryPos G 1 = 1 ∧ entryPos G 2 = 2 ∧
      entryByte G 0 = 0x5B ∧ entryByte G 1 = 0x31 ∧ entryByte G 2 = 0x5D := by
  have hbs' : G.bs = [0x5B, 0x31, 0x5D] := hbs.trans evbDoc_def
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [entryPos, entryByte, hent, hbs'] <;> decide

/-! ### The emission at the chain's end

`evb_emission_of_walk_accept` takes the merge state's invariant, its empty span
list and the returned memory's four reads.  The first two come from the chain: the
invariant is the composed segment's, and the span list is `spans_nil_of_arm_chain`'s.
No arena word at the walk, no span list and no memory equation are assumed; the
returned memory is `JsonWalkReads`'s four values. -/

/-- **The emission at `[1]`, the span premise discharged by the chain.**  The
arena datum `evb_emission_of_spec` reads follows from the merge carry's empty span
list — derived here from the seed, the opener's, number's and closer's carries and
the two head passes — the zeroed staging, and the `%ndst` read the returned memory
carries.  The whole-memory equation is not among the premises. -/
theorem evb_emission_of_bracket_walk {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {s₀ s₁ sh₁ s₂ sh₂ s₃ : State}
    {p₁ p₂ p₃ : Nat} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ sp₁ k₂ sp₂ : Nat}
    {m : Mem} {next ndstU nev' : Nat}
    (hpre : routePre evbLayout evbDoc)
    (hndstG : G.ndst = evbLayout.ndst)
    (hopen : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀ C₁ s₁ p₁)
    (hhead₁ : WalkSegment (stage2Calls stage2SubCalls) G C₁ s₁ H₁ sh₁ 2)
    (hnumber : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁ C₂ s₂ p₂)
    (hhead₂ : WalkSegment (stage2Calls stage2SubCalls) G C₂ s₂ H₂ sh₂ 2)
    (hcloser : WalkSegment (stage2Calls stage2SubCalls) G H₂ sh₂ C₃ s₃ p₃)
    (h₁ : C₁ = openC₉ (openHeadC (walkSeed G S)) b)
    (hH₁ : H₁ = headPassC C₁ k₁ sp₁)
    (h₂ : C₂ = scMergeC H₁ ev)
    (hH₂ : H₂ = headPassC C₂ k₂ sp₂)
    (h₃ : C₃ = closeCEnd (closeC₁₀b H₂) spz c8)
    (hstaged : readBytes m0 G.ndst 8 = some (wordBytes 8 0))
    (hreads : JsonWalkReads G C₃ m)
    (hext : pipelineOutputExtents evbArgs (.ret (some (.int 64 1)) m) ndstU nev')
    (hspec : Sigma_pipeline stage2EventRel evbLayout.base evbArgs evbMem next
      (.ret (some (.int 64 1)) m)) :
    ∃ (arena evs : List UInt8),
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 ndstU) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      readBytes m evbLayout.dst ndstU = some arena ∧
      readBytes m evbLayout.ev nev' = some evs ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evs) (ByteString.literal arena)).bind valueOfEvents =
        scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate := by
  obtain ⟨-, hInv, hspans⟩ :=
    bracket_walk_chain hopen hhead₁ hnumber hhead₂ hcloser h₁ hH₁ h₂ hH₂ h₃
  exact evb_emission_of_walk_accept hreads hpre hndstG hInv hspans hstaged
    hext hspec

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkSeed_spans
#print axioms LeanLLVM.Refinement.WalkScope.openHeadC_spans
#print axioms LeanLLVM.Refinement.WalkScope.closeC₁₀b_spans
#print axioms LeanLLVM.Refinement.WalkScope.headPassC_spans
#print axioms LeanLLVM.Refinement.WalkScope.headPassSeg
#print axioms LeanLLVM.Refinement.WalkScope.spans_nil_of_arm_chain
#print axioms LeanLLVM.Refinement.WalkScope.spans_nil_of_arm_spans
#print axioms LeanLLVM.Refinement.WalkScope.bracketOpenSeg
#print axioms LeanLLVM.Refinement.WalkScope.bracketChainSegment
#print axioms LeanLLVM.Refinement.WalkScope.bracket_walk_chain
#print axioms LeanLLVM.Refinement.WalkScope.bracket_walk_chain_open
#print axioms LeanLLVM.Refinement.WalkScope.evbDoc_entryBytes
#print axioms LeanLLVM.Refinement.WalkScope.evb_emission_of_bracket_walk

end WalkScope
end LeanLLVM.Refinement
