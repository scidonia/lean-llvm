import LeanLLVM.Refinement.JsonStage2WalkDispatchWitness

/-! # The state stack's refusal

`cleanup104.i` is the dispatch's third refusal shape: a closing bracket whose container
marker *agrees* — so the type stack's check passes — but whose state stack records a
value of at least `2` (`cond.end.i`'s `%15 ult 2`).  Its path is nine blocks: the
switch's four pivots, `if.then53.i`'s depth test, `if.end59.i`'s select nest on the
*continue* arm, `if.end74.i`'s `cst` read, `cond.end.i`'s test, and the offset store.

It lives in its own module because the nine links are the weight: each `WalkLink` carries
a full `WalkInv` proof term, and nine of them in one declaration exceeds the 6 GB
elaboration scope even when every state is named and every peel is free.  One Lean
process per file is the instrument for that, and it is the one the layer's own rule
prescribes when the weight is the link terms rather than the terms they name.

**The peels are definitional.**  Every fact this module needs about a state's
environment — `%idxprom65.i` and `%cmp61.i` at the select nest's successor, `%15` at the
`cst` read's, `%idxprom.i` and `%e` at the store's — closes by `rfl` or by `exact` of the
hypothesis at the *source* state: the lookup of an unbound name through a literal cell
list reduces, so `simp` on `lookupName` over a concrete binder list is a workaround for a
reduction the elaborator already performs.  The five facts below are the measurement:
they elaborate in seconds with no memory pressure, where the `simp`-based forms of the
same four peels were killed at the cap. -/

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-! ### The state stack's refusal, at a named prefix

The nine-link composition needs the same cells four times over: the select nest's
successor, the `cst` read's successor, the test's, and the store's.  Each is named once
here, so the peels below are lookups on a short term instead of four re-unfoldings of an
eight-cell nest — *a peel that re-derives a state's environment costs the same as a wide
lemma application, because the elaborator spells the same term each time*. -/

/-- The depth test's successor, at the nest's input. -/
abbrev ssNest (s : State) : State :=
  mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))

/-- The select nest's successor, at the bracket's marker test. -/
abbrev ssSel {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  stackSelOut (ssNest s) C.sp C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
    (stackSelBit (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1)))

/-- The `cst` read's successor, at the state stack's test. -/
abbrev ssPeek {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  ifEnd74Out (ssSel C s) C.stage.cst
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat
    (C.stMap (C.sp - 1)) (evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 125))

/-- The test's successor, at the refusal store. -/
abbrev ssCond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  clS₈ (ssPeek C s)

/-- The store's successor, at the refusal copy. -/
abbrev ssDone {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State) : State :=
  clS₉ C j (ssCond C s)

/-- `%idxprom65.i` at the nest's successor: the nest's own offset cell. -/
theorem ssSel_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) :
    lookupName (ssSel C s).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) := rfl

/-- `%cmp61.i` at the nest's successor: the bracket's marker test, in the nest's own
form. -/
theorem ssSel_cmp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) :
    lookupName (ssSel C s).env "%cmp61.i" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 125))) := rfl

/-- `%15` at the state stack's test: the `cst` byte. -/
theorem ssPeek_15 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) :
    evalOperand (ssPeek C s) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 (C.stMap (C.sp - 1)).toNat)) := rfl

/-- `%idxprom.i` survives the whole prefix: none of the five environments binds it. -/
theorem ssDone_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State)
    {v : Value} (hv : evalOperand s (.reg "%idxprom.i") = some v) :
    evalOperand (ssDone C j s) (.reg "%idxprom.i") = some v := hv

/-- `%e` survives the whole prefix. -/
theorem ssDone_e {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s : State)
    (he : lookupName s.env "%e" = some (.ptr C.stage.e)) :
    lookupName (ssDone C j s).env "%e" = some (.ptr C.stage.e) := he

/-- **An unsigned comparison that is false is the zero bit** (8-bit operands). -/
theorem refuseUlt8_zero {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) (h : ¬ a < b) :
    evalICmp .ult (BitVec.ofNat 8 a) (BitVec.ofNat 8 b) = 0 := by
  have hu : BitVec.ult (BitVec.ofNat 8 a) (BitVec.ofNat 8 b) = false := by
    rw [BitVec.ult]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact decide_eq_false h
  simp only [evalICmp, hu]
  rfl

/-- **The state stack's refusal, first half**: the switch's four pivots at `]` and the
depth test's non-refusal arm, five links to the select nest's input. -/
theorem stateStackSeg₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) :
    WalkSegment calls G C s { C with block := "if.end59.i" } (ssNest s) 5 := by
  have h8₁ : evalOperand (refuseS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (refuseS₂ (refuseS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₂, refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (refuseS₃ (refuseS₂ (refuseS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [refuseS₃, refuseS₂, refuseS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have L₁ : WalkLink calls G C s { C with block := "NodeBlock19" } (refuseS₁ s) :=
    refuseStep₁ G C s hInv hhead h8
  have L₂ : WalkLink calls G { C with block := "NodeBlock19" } (refuseS₁ s)
      { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) :=
    refuseStep₂ G { C with block := "NodeBlock19" } (refuseS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink calls G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s))
      { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s))) :=
    refuseStep₃ G { C with block := "NodeBlock11" } (refuseS₂ (refuseS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink calls G { C with block := "LeafBlock9" }
      (refuseS₃ (refuseS₂ (refuseS₁ s))) { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) :=
    refuseStep₄ G { C with block := "LeafBlock9" } (refuseS₃ (refuseS₂ (refuseS₁ s)))
      L₃.inv' rfl h8₃
  have L₅ : WalkLink calls G { C with block := "if.then53.i" }
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) { C with block := "if.end59.i" }
      (ssNest s) :=
    mlStep₅ G { C with block := "if.then53.i" } (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))
      L₄.inv' rfl hsp
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.tail L₅
    (Seg.nil L₅.inv'))))))



/-- **The state stack's refusal, second half's first part**: the select nest's agreeing
arm and the `cst` read, two links from the nest's input to the state stack's test.

The invariant is the segment's *own* source — `WalkInv G { C with block := "if.end59.i" }
(ssNest s)` — and a composing theorem supplies it as the first half's `inv'`.  A segment
stated at the wrong invariant is the trap a split invites: it can only be papered over by
a `show` that the state mismatch makes unprovable. -/
theorem stateStackSeg₂a {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G { C with block := "if.end59.i" } (ssNest s))
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) (hmark : (C.tyMap (C.sp - 1)).toNat = 2) :
    WalkSegment calls G { C with block := "if.end59.i" } (ssNest s)
      { C with block := "cond.end.i" } (ssPeek C s) 2 := by
  have hsp₆ : lookupName (ssNest s).env "%sp.i.0248" =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := hInv.depth_reg
  have h8₆ : lookupName (ssNest s).env "%8" = some (.int 8 (BitVec.ofNat 8 93)) := by
    simpa only [ssNest, mlS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf10") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hct₆ : lookupName (ssNest s).env "%ctype.i" = some (.ptr C.stage.ctype) :=
    hInv.ptrs.2.2.2.1
  have hsub : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsp32 : C.sp < 2 ^ 32 := by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega
    have hb : (4294967295 : Nat) < 2 ^ 32 := by decide
    rw [Nat.mod_eq_of_lt hsp32, Nat.mod_eq_of_lt hb]
    rw [show C.sp + 4294967295 = (C.sp - 1) + 4294967296 from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hq63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63 := by
    rw [hsub]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    omega
  have hread : readBytes (ssNest s).mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [C.tyMap (C.sp - 1)] := by
    rw [hsub, JsonEntrySteps.readBytes_one]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hlt : C.sp - 1 < C.wlen := by
      have hspw : C.sp ≤ C.wlen := hInv.sp_le_wlen
      omega
    rw [hInv.tyBytes (C.sp - 1) hlt]
    rfl
  have hq256 : (C.tyMap (C.sp - 1)).toNat < 256 := UInt8.toNat_lt (C.tyMap (C.sp - 1))
  have hbit : evalICmp .eq (walkSelVal (BitVec.ofNat 8 93))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [C.tyMap (C.sp - 1)])).toNat) = 1 := by
    have hselbit : evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 125) = 0 := by decide
    have hsel : walkSelVal (BitVec.ofNat 8 93) = BitVec.ofNat 32 2 := by
      rw [walkSelVal, walkSelBit, hselbit]; rfl
    have hbs : bytesToNat [C.tyMap (C.sp - 1)] = (C.tyMap (C.sp - 1)).toNat := by
      simp [bytesToNat]
    have hq8 : (BitVec.ofNat 8 (C.tyMap (C.sp - 1)).toNat).toNat =
        (C.tyMap (C.sp - 1)).toNat := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hq256
    rw [hsel, hbs, hq8, hmark]
    decide
  have L₆ : WalkLink calls G { C with block := "if.end59.i" } (ssNest s)
      { C with block := "if.end74.i" } (ssSel C s) :=
    mlStep₆c G { C with block := "if.end59.i" } (ssNest s) hInv rfl hsp₆ h8₆ hct₆ hq63 hread
      hbit
  have hread₇ : readBytes (ssNest s).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [C.stMap (C.sp - 1)] := by
    rw [hsub, JsonEntrySteps.readBytes_one]
    have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
    have hlt : C.sp - 1 < C.wlen := by
      have hspw : C.sp ≤ C.wlen := hInv.sp_le_wlen
      omega
    rw [hInv.stBytes (C.sp - 1) hlt]
    rfl
  have L₇ : WalkLink calls G { C with block := "if.end74.i" } (ssSel C s)
      { C with block := "cond.end.i" } (ssPeek C s) := by
    have hzero : evalICmp .eq (BitVec.ofNat 8 93) (BitVec.ofNat 8 125) = 0 := by decide
    obtain ⟨s', hl, hs'⟩ := walkIfEnd74_at (calls := calls) G { C with block := "if.end74.i" }
      (ssSel C s) L₆.inv' rfl L₆.inv'.ptrs.2.2.2.2.1
      (ssSel_idx C s) hq63 hread₇ (ssSel_cmp C s)
    rw [hs'] at hl
    rw [hzero] at hl
    exact hl
  exact Seg.measure (Seg.tail L₆ (Seg.tail L₇ (Seg.nil L₇.inv')))

/-- **The state stack's refusal, second half's second part**: `cond.end.i`'s test and the
offset store, two links from the state stack's test to the refusal copy. -/
theorem stateStackSeg₂b {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G { C with block := "cond.end.i" } (ssPeek C s))
    {j : Nat} (hst : 2 ≤ (C.stMap (C.sp - 1)).toNat)
    (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkSegment calls G { C with block := "cond.end.i" } (ssPeek C s)
      { C with block := "if.then", eoff := j, refusal := true } (ssDone C j s) 2 := by
  have hst256 : (C.stMap (C.sp - 1)).toNat < 2 ^ 8 := UInt8.toNat_lt _
  have hbit₈ : evalICmp .ult (BitVec.ofNat 8 (C.stMap (C.sp - 1)).toNat)
      (BitVec.ofNat 8 2) = 0 :=
    refuseUlt8_zero hst256 (by decide) (by omega)
  have L₈ : WalkLink calls G { C with block := "cond.end.i" } (ssPeek C s)
      { C with block := "cleanup104.i" } (ssCond C s) :=
    clStep₈ G { C with block := "cond.end.i" } (ssPeek C s) hInv rfl (ssPeek_15 C s) hbit₈
  have L₉ : WalkLink calls G { C with block := "cleanup104.i" } (ssCond C s)
      { C with block := "if.then", eoff := j, refusal := true } (ssDone C j s) :=
    clStep₉ G { C with block := "cleanup104.i" } (ssCond C s) L₈.inv' rfl
      (ssDone_idx C j s hv) (ssDone_e C j s he) hj hj64
  exact Seg.measure (Seg.tail L₈ (Seg.tail L₉ (Seg.nil L₉.inv')))

/-- **The state stack's refusal, as one counted run.**  The halves composed at the
segment algebra's own count (`5 + 2 + 2`), each half taking the invariant at its own
source: the composition supplies them as `inv'`. -/
theorem stateStackRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) (hmark : (C.tyMap (C.sp - 1)).toNat = 2)
    (hst : 2 ≤ (C.stMap (C.sp - 1)).toNat)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have h₁ := stateStackSeg₁ (calls := calls) G C s hInv hhead h8 hsp
  have h₂ := stateStackSeg₂a (calls := calls) G C s h₁.inv' h8 hsp hmark
  have h₃ := stateStackSeg₂b (calls := calls) G C s h₂.inv' hst hv he hj hj64
  exact ⟨_, ssDone C j s, 9, h₁.trans (h₂.trans h₃), rfl, h₃.inv'.eoff_le,
    refusePrice_of_le G C (by omega) hk⟩

/-- **The `refuse` witness at the state stack's byte**, in the exact shape
`WalkDispatchThree.ofContinueAndLast`'s `hlast` states its second disjunct: a closing
bracket that matches the type stack's marker, refused because the state stack's own byte
is at least `2`. -/
theorem walkRefuseWitness_stateStack {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hsp : C.sp ≠ 0) (hmark : (C.tyMap (C.sp - 1)).toNat = 2)
    (hst : 2 ≤ (C.stMap (C.sp - 1)).toNat)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) :=
  stateStackRefuse_at G C s hInv hhead h8 hsp hmark hst hv he hj hj64 hk

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.refuseUlt8_zero
#print axioms LeanLLVM.Refinement.WalkScope.ssSel_idx
#print axioms LeanLLVM.Refinement.WalkScope.ssSel_cmp
#print axioms LeanLLVM.Refinement.WalkScope.ssPeek_15
#print axioms LeanLLVM.Refinement.WalkScope.ssDone_idx
#print axioms LeanLLVM.Refinement.WalkScope.ssDone_e
#print axioms LeanLLVM.Refinement.WalkScope.stateStackSeg₁
#print axioms LeanLLVM.Refinement.WalkScope.stateStackSeg₂a
#print axioms LeanLLVM.Refinement.WalkScope.stateStackSeg₂b
#print axioms LeanLLVM.Refinement.WalkScope.stateStackRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.walkRefuseWitness_stateStack
