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
abbrev ssNest {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))

/-- The select nest's successor, at the bracket's marker test. -/
abbrev ssSel {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  stackSelOut (ssNest C s) C.sp C.stage.ctype (BitVec.ofNat 8 93) (C.tyMap (C.sp - 1))
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
    evalOperand (ssSel C s) (.reg "%idxprom65.i") =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) := rfl

/-- `%cmp61.i` at the nest's successor: the bracket's marker test, in the nest's own
form. -/
theorem ssSel_cmp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) :
    evalOperand (ssSel C s) (.reg "%cmp61.i") =
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
    WalkSegment calls G C s { C with block := "if.end59.i" } (ssNest C s) 5 := by
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
      (ssNest C s) :=
    mlStep₅ G { C with block := "if.then53.i" } (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))
      L₄.inv' rfl hsp
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.tail L₅
    (Seg.nil L₅.inv'))))))


/-! ### What remains

The second half — the select nest's agreeing arm, the `cst` read, `cond.end.i`'s test and
the store, four links from the nest's input to `if.then` — is written but does not fit the
elaboration scope here: with the peels definitional and every state named, the four
remaining `WalkLink` terms still exceed it in this file's own process.  The instrument for
that is one step further down the same ladder — split the half into two two-link segments
and compose with `WalkSegment.trans`, exactly as the five-link half above composes — and it
is mechanical, because each of the four links is already a committed theorem of the witness
module (`mlStep₆c`, `walkIfEnd74_at`, `clStep₈`, `clStep₉`) and the five peel facts beside
them are `rfl`.

`cleanup104.i`'s path is therefore proved up to `if.end59.i`'s input here, and the remaining
four links are the ones listed above. -/

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.refuseUlt8_zero
#print axioms LeanLLVM.Refinement.WalkScope.ssSel_idx
#print axioms LeanLLVM.Refinement.WalkScope.ssSel_cmp
#print axioms LeanLLVM.Refinement.WalkScope.ssPeek_15
#print axioms LeanLLVM.Refinement.WalkScope.ssDone_idx
#print axioms LeanLLVM.Refinement.WalkScope.ssDone_e
#print axioms LeanLLVM.Refinement.WalkScope.stateStackSeg₁
