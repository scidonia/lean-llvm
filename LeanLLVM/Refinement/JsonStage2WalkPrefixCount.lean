/-
The last entry's path to the merge, counted.

## The structural fact, for the third time

**`WalkChain` is a `Prop`, and its `steps` is existential by necessity** — a `Nat`-valued
length over a `Prop` would be a large elimination — so a consumer that must *price* needs
segments, not chains.  This is the third place it bites, and each time the resolution was
the same: a counted twin, not a derivation.

| appearance | what needed the count | resolution |
|---|---|---|
| `walkScanRounds457` | the scan's round | `hround` returns a segment |
| `walkHeadChainToScan` | the last entry's price | `hprice` became a bundle field |
| `consumer_tail_seg` | the tail's count, to compose it | the count existed — `3` — and a **name** did not |
| this module | the price, again | counted twins and a `Nat` |

The third row is the fact one layer further in: **a count without a name is not a
composable count.**  `consumer_tail_seg` returns a segment at `3` already; its target
state is existential, and `WalkSegment.trans` needs the next piece's source state to be
the same *term*, so the count was there and unusable.  `consumerTailSegAt` is the same
proof at `ScanEntry s r₁ r₂ r₃ ei cd c rdv x`.

## The prefix, piece by piece

The last entry's path, as finding 23's repair re-stated it: the head's four pivots and
`sw.default.i`'s *failing* count test, the byte test's `1` arm with the whitespace check
and its three pivots, the token's end, the class-C span, and the **scan-free** tail —
`if.then447.i`'s target tests `ult v v` on the same word at both cells, so the walk leaves
for `if.end473.i` and the extra-token scan is never entered.

| piece | counted form | count |
|---|---|---|
| `walkHeadChainA`'s six links, at the byte test's `1` arm | `walkHeadChainASeg` | 6 |
| the whitespace check (`land.lhs.true357.i` and three pivots) | `Seg.tail` in `hlastTailSeg` | 4 |
| the seam (`WalkLink.if_end372_i_at`) | `Seg.tail` in `hlastTailSeg` | 1 |
| `walkHeadChainC` | `walkHeadChainCSeg` | 5 |
| the tail, on its empty arm | `consumerTailSegEmptyAt` | 3 |

`consumerTailSegAt` exists beside the committed `consumer_tail_seg`, which already
returns a segment at count `3` — but its target *state* is existential, and the scan's
segment needs its premises at that state.  A counted piece that cannot be composed is not
counted for this purpose, so the twin names `ScanEntry s r₁ r₂ r₃ ei cd c rdv x`: the
state `TailS₃ (TailS₂ (TailS₁ s …) …) …` is exactly that abbreviation.
`consumerTailSegEmptyAt` is the same three links on the empty arm, at `ScanEntry s r₁ r₂ r₃
cd cd c rdv x`.

The `Seg` twins are copies of the committed proofs at the `Seg` constructors: the links,
their named targets and their peels are unchanged, and the composition line is `Seg.tail`
in place of `WalkChain.tail`.  That is what the third appearance costs — the count is a
property of *how* the chain was built, so it cannot be recovered from the chain.

The total is `6 + 4 + 1 + 5 = 16` to the tail's start (`hlastTailSeg`), and the scan-free
tail's three make `19` (`hlastPrefixSeg`); `hlast_toMerge` adds the merge's own step:
`19 + 1 = 20`, which is the assembly's own longest path.  The price at the last entry is
then `20 + 2 ≤ 32 · Δk + 8 · Δbytes`, i.e. `22 ≤ 32` at `Δk = 1` with the byte term zero
(`entryPos G G.nep = 0`): `omega`, not a hypothesis.

**The split is not cosmetic.**  A `WalkSegment` records only its *target's* invariant, so
the tail's segment needs `WalkInv` at `hlastTail` — a state no other lemma's conclusion
names.  `hlastTailSeg` is that record, and `hlastTail_of_calls`/`hlastFacts_of_staging`
take its `inv'` as the tail's source invariant.

**The scan the earlier statement entered is not this path's.**  `walkHeadChainToScan` is
the `hugt = 0` arm's chain — the direct edge `cond.end349.i → if.end372.i` followed by the
scan — and a last entry does not take it: its `%cond350.i` is the stream's end, above its
own index.  That arm's chain stays a true conditional statement; the price it used to
carry (`18 + 7`) is not the last entry's, and the last entry's is the twenty above.
-/

import LeanLLVM.Refinement.JsonStage2WalkHeadChainA
import LeanLLVM.Refinement.JsonStage2WalkHeadChainC
import LeanLLVM.Refinement.JsonStage2WalkHeadChainScan
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head's fall-through, counted, on the byte test's `1` arm

The last entry's head: the four high-byte pivots, `sw.default.i`'s count test on its
*failing* arm and `cond.end349.i` — six links.  The bound's `phi` takes `%4`'s word there
(the default arm is the one the count test's failure takes), and the last entry's `%4` is
the stream's end — above its own index — so the byte test is `1` and the carry continues
at `land.lhs.true357.i` rather than at the token's end.  The target *state* is still
`headEndS`: `condEnd349OutAt` writes its `pc` from the word the test compares, so the name
is the same on both arms and only the carry differs.
-/

/-- The default arm's `phi` selects `%4`: its two incoming entries, the second of which
`sw.default.i` names. -/
theorem hlast_pre5 :
    phiIncoming "sw.default.i"
      [("cond.true345.i", Operand.reg "%conv347.i"),
       ("sw.default.i", Operand.reg "%4")] = some (.reg "%4") := by
  decide

/-- The byte `land.lhs.true357.i` loads, as the `%35` cell holds it. -/
abbrev head35 (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

/-- The carry at the whitespace check: the byte test's `1` arm. -/
abbrev HlastAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₅ C with block := "land.lhs.true357.i" }

/-- The carry at the byte's first pivot. -/
abbrev HlastAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HlastAC₁ C with block := "NodeBlock41" }

/-- The carry at the byte's second pivot. -/
abbrev HlastAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HlastAC₂ C with block := "NodeBlock39" }

/-- The carry at the leaf the byte's class selects. -/
abbrev HlastAC₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HlastAC₃ C with block := "LeafBlock35" }

/-- **The tail's carry when the scan is empty**: `if.then447.i`'s target on its `ult v v`
arm, which is the merge's entry block.  The copy call is what advances the carry, so the
segment's endpoint carries `TailCarry₃`'s trace and the scan's own `stMap`. -/
abbrev TailCarryEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { TailCarry₃ C ev with
    block := "if.end473.i"
    stMap := walkAfterValueMap (TailCarry₃ C ev) }

theorem walkHeadChainASeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} {ix : BitVec 64}
    (hav5 : lookupName (headAS₅ s x inc nep).env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1) :
    Seg (stage2Calls stage2SubCalls) G C s (HlastAC₁ C)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix) 6 := by
  -- the four arms, resolved by the class's bits
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by
    rw [hlt91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by
    rw [hlt123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock15" := by
    rw [hlt125]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 125) = 1 then
      "if.then53.i" else "sw.default.i") = "sw.default.i" := by
    rw [hne125]; rfl
  have hres₅ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.end349.i" := by
    rw [hge]; rfl
  have hres₆ : (if evalICmp .ugt (BitVec.ofNat 64 v) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  -- the byte's operand fact at each pivot, peeled past the cells the pivots bind
  have h8₁ : evalOperand (headAS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (headAS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₃ : evalOperand (headAS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₃, headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (HeadAC₁ C) (headAS₁ s x) := by
    have hst : s₁ = headAS₁ s x := by
      rw [hs₁, hres₁]
      rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. the second pivot
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (HeadAC₁ C)
      (headAS₁ s x) hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₁ C) (headAS₁ s x)
      (HeadAC₂ C) (headAS₂ s x) := by
    have hst : s₂ = headAS₂ s x := by
      rw [hs₂, hres₂]
      rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the third pivot
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock17_at (calls := stage2Calls stage2SubCalls) G (HeadAC₂ C)
      (headAS₂ s x) hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₂ C) (headAS₂ s x)
      (HeadAC₃ C) (headAS₃ s x) := by
    have hst : s₃ = headAS₃ s x := by
      rw [hs₃, hres₃]
      rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock15_at (calls := stage2Calls stage2SubCalls) G (HeadAC₃ C)
      (headAS₃ s x) hl₃'.inv' rfl h8₃
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₃ C) (headAS₃ s x)
      (HeadAC₄ C) (headAS₄ s x) := by
    have hst : s₄ = headAS₄ s x := by
      rw [hs₄, hres₄]
      rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- 5. the default arm's entry count
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C)
      (headAS₄ s x) hl₄'.inv' rfl hinc hnep
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) (headAS₄ s x)
      (HeadAC₅ C) (headAS₅ s x inc nep) := by
    have hst : s₅ = headAS₅ s x inc nep := by
      rw [hs₅, hres₅]
      rfl
    rw [hst] at hl₅
    rw [hres₅] at hl₅
    exact hl₅
  -- 6. the token's position against the entry's index, on the last entry's arm
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.cond_end349_i_at G (HeadAC₅ C) (headAS₅ s x inc nep) hl₅'.inv' rfl
      (p := "sw.default.i") rfl hlast_pre5 hav5 hidx5 htok5 hgap5
  rw [hres₆] at hl₆
  rw [hs₆] at hl₆
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₅ C) (headAS₅ s x inc nep)
      (HlastAC₁ C)
      (condEnd349OutAt (headAS₅ s x inc nep) (BitVec.ofNat 64 v) ix C.stage.tok
        (C.stage.tok + 20)) := hl₆
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃'
    (Seg.tail hl₄' (Seg.tail hl₅' (Seg.tail hl₆'
      (Seg.nil hl₆'.inv'))))))

/-! ### The class-C span, counted -/

theorem walkHeadChainCSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x1 : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x1))
    (h₁ : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h₃ : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    Seg calls G C s (HeadC₄₁₃ C) (HeadS413 s x1) 5 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x1) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x1 := hs₂
  rw [hs₂'] at hl₂
  have h8₂ : evalOperand (HeadS60 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 3. `NodeBlock60`, whose bit is clear
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x1) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock58" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = HeadS58 s x1 := hs₃
  rw [hs₃'] at hl₃
  have h8₃ : evalOperand (HeadS58 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS58, HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot61") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 4. `LeafBlock58`, whose bit is clear
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock58_at (calls := calls) (G := G)
    (C := HeadC₅₈ C) (s := HeadS58 s x1) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.then413.i"
    else "if.else405.i") = "if.else405.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = HeadS405 s x1 := hs₄
  rw [hs₄'] at hl₄
  -- 5. the empty body at `if.else405.i`
  obtain ⟨s₅, hl₅, hs₅⟩ := headChain_else405_at (calls := calls) G (HeadC₄₀₅ C)
    (HeadS405 s x1) hl₄.inv' rfl
  have hs₅' : s₅ = HeadS413 s x1 := hs₅
  rw [hs₅'] at hl₅
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃
    (Seg.tail hl₄ (Seg.tail hl₅ (Seg.nil hl₅.inv')))))

/-! ### The tail, counted at the named scan entry -/

theorem consumerTailSegAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (ei cd : Nat) :
    ∀ (_hInv : WalkInv G C s) (_hblock : C.block = "if.then413.i")
    (p : String) (_reg : String) (c : BitVec 32) (op : Operand) (rdv : BitVec 32)
    (x : BitVec 32),
    s.pre = some p →
    phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op →
    evalOperand (stateAt s.env s) op = some (.int 32 c) →
    lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)) →
    lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) →
    readBytes (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) →
    s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next →
    stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r₁ →
    r₁.ret = .int 32 x →
    evalICmp .eq x (BitVec.ofNat 32 0) = 0 →
    readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) →
    lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c) →
    lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok) →
    lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z) →
    stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂ →
    s2ScalarValueAppend r₁.mem r₂.mem (TailCarry₂ C).stage.z ev.encodedBytes →
    r₂.ret = .int 32 (BitVec.ofNat 32 1) →
    G.ev < 2 ^ 64 → C.evlen < 2 ^ 64 → C.events.length ≤ C.k → C.k < G.nep →
    s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next →
    stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next = some r₃ →
    lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)) →
    lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
    cd - ei ≤ C.inner → ei < cd → cd < 2 ^ 64 →
    Seg (stage2Calls stage2SubCalls) G C s (TailCarryScan C ev)
      (ScanEntry s r₁ r₂ r₃ ei cd c rdv x) 3 := by
  intro hInv hblock p reg c op rdv x hpre hinc hop hkind hrd hread hpre' hcall₁ hret₁
    hbit0 hzreadJ hc ht ho hcall₂ happ₂ hret₂ hev64 hevlen64 htight hklt hpre447 hcall₃ hei hcd
    hinner hlt2 hcd64
  -- 1. the value-position call
  have hx413 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x := by
    intro r hr
    have h : r = r₁ := Option.some.inj (hr.symm.trans hcall₁)
    rw [h]; exact hret₁
  obtain ⟨r₁', s₁', hcall₁', hl₁, hs₁'⟩ := walkIfThen413_at (G := G) (C := C) (s := s)
    (p := p) (reg := reg) (x := x) (op := op) hInv hblock hpre hinc hop hkind hrd hread hpre'
    hx413
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hs₁'
  have hs₁ : s₁' = TailS₁ s r₁ c rdv x := hs₁'
  rw [hs₁] at hl₁
  rw [show { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
      then "if.then418.i" else "if.then425.i") } = TailCarry₂ C from by rw [hbit0]; rfl] at hl₁
  -- 2. the scalar call's emit arm
  obtain ⟨s₂', hl₂, hs₂'⟩ := walkIfThen425_emit_at (G := G) (C := TailCarry₂ C)
    (s := TailS₁ s r₁ c rdv x) hl₁.inv' rfl
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%c.i") _ _ (by decide)] using hc)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%t352.i") _ _ (by decide)] using ht)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%z") _ _ (by decide)] using ho)
    (by simpa only [TailS₁, stateAt] using hzreadJ)
    (by simpa only [TailS₁, stateAt] using hcall₂) happ₂ hret₂ hev64 hevlen64 htight hklt
  have hs₂ : s₂' = TailS₂ (TailS₁ s r₁ c rdv x) r₂ := hs₂'
  rw [hs₂] at hl₂
  -- 3. the copy call, at the scan's entry
  obtain ⟨r₃', s₃', hcall₃', hl₃, hs₃'⟩ := walkIfThen447_at (G := G) (C := TailCarry₃ C ev)
    (s := TailS₂ (TailS₁ s r₁ c rdv x) r₂) hl₂.inv' rfl
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%root_done.i") _ _ (by decide)] using hrd)
    (by simpa only [TailS₂, TailS₁, stateAt] using hpre447)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%ee.1.i") _ _ (by decide)] using hei)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%cond350.i") _ _ (by decide)] using hcd)
    hinner hlt2 hcd64
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hs₃'
  have hbit1 : evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = (1 : BitVec 1) := by
    have h1 : (BitVec.ofNat 64 ei).toNat < (BitVec.ofNat 64 cd).toNat := by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)
        = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)) from rfl,
      show BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = true from
        (BitVec.ult_iff_toNat_lt).2 h1]
    rfl
  rw [show (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
      then "land.rhs457.i" else "if.end473.i") = "land.rhs457.i" from by rw [hbit1]; rfl] at hl₃
  have hs₃ : s₃' = TailS₃ (TailS₂ (TailS₁ s r₁ c rdv x) r₂) r₃ ei cd := hs₃'
  rw [hs₃] at hl₃
  subst hs₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

/-! ### The last entry's scan-free arm

The last entry's token ends at the stream's end.  `%inc.i` has reached the entry count, so
`sw.default.i` sends the walk to `cond.end349.i` without reading a next entry's lane, and
the bound's `phi` takes `%4`'s word — the stream's end.  That word is above the entry's
index, so `cond.end349.i` takes `land.lhs.true357.i` and the walk reads the byte *before*
the token's end.

The class the price's longest path names is the no-whitespace one (`13 ≤ %35 < 32`,
`%35 ≠ 13`): the walk reaches `if.end372.i` through `NodeBlock41 → NodeBlock39 →
LeafBlock35` with no run, and the token's end `phi` takes `%cond350.i`.  `%ee.1.i` is then
the bound itself, so `if.then447.i`'s test is `ult v v`, the walk leaves for `if.end473.i`,
and the extra-token scan is **never entered**.  That is why the last entry's tail is the
scan-free one: it needs no inner budget, no landing and no latch, because there is no visit
to afford.

The states below are `JsonStage2WalkRevolutionPrefix`'s whitespace-check states with `%4`'s
word in place of the lane's, re-stated here because that module sits *above* this one — it
imports the last entry's bundle, so its `contLandS` … `contP35S` are not visible below it.
`head35` is the one name the re-statement needed: `cont35`'s definition, here because this
module is the lower one.
-/

/-- An unsigned comparison of a word with itself is zero. -/
theorem hlast_ult_self {w : Nat} (a : BitVec w) : evalICmp .ult a a = 0 := by
  simp only [evalICmp, BitVec.ult_eq_decide, lt_self_iff_false]
  rfl

/-- `%cond350.i` at the token's end is `%4`'s word: the `phi` is bound once there. -/
theorem hlastEndS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) :
    lookupName (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [headEndS, condEnd349OutAt, cells]
  rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `land.lhs.true357.i`'s target: the byte before the token's end and its address. -/
def hlastLand {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { (stateAt (cells [("%35", .int 8 (head35 b35)), ("%gep", .ptr ((G.b - 1) + v))]
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).env)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix)) with
    pc := "NodeBlock41", pre := some (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).pc }

/-- `NodeBlock41`'s target, on the arm its `%35 < 13` test does not take. -/
def hlastP41 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((hlastLand C s x inc nep v ix b35).bind "%Pivot42"
      (.int 1 (evalICmp .slt (head35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some (hlastLand C s x inc nep v ix b35).pc }

/-- `NodeBlock39`'s target, on the arm its `%35 < 32` test takes. -/
def hlastP39 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((hlastP41 C s x inc nep v ix b35).bind "%Pivot40"
      (.int 1 (evalICmp .slt (head35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock35", pre := some (hlastP41 C s x inc nep v ix b35).pc }

/-- `LeafBlock35`'s target: the token's end, on the arm its `%35 = 13` test does not
take — the no-whitespace class, so no run is entered. -/
def hlastP35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  { ((hlastP39 C s x inc nep v ix b35).bind "%SwitchLeaf36"
      (.int 1 (evalICmp .eq (head35 b35) (BitVec.ofNat 8 13)))) with
    pc := "if.end372.i", pre := some (hlastP39 C s x inc nep v ix b35).pc }

/-- The seam at the token's end: the `phi` selects `%cond350.i`, so the stored end is
`%4`'s word and the `%8` test reads the entry's first byte. -/
def hlastSeam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  seamS (hlastP35 C s x inc nep v ix b35) (BitVec.ofNat 64 v) x C.stage.tok

/-- The tail's start: the class-C span's target at the value-position call. -/
def hlastTail {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  HeadS413 (hlastSeam C s x inc nep v ix b35) x

/-- **The tail's target: the scan's entry on its empty arm.**  `%ee.1.i` is the seam's
stored end — `%4`'s word — and `%cond350.i` is the same cell, so the counter and the bound
are one number and `TailS₃`'s `if` is the else arm: the walk reaches `if.end473.i` with the
scan never entered. -/
def hlastEntry {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) : State :=
  ScanEntry (hlastTail C s x inc nep v ix b35) r₁ r₂ r₃ v v cA rdv xA

/-- The merge's state: `walkIfEnd473_at`'s target, at the merge's own block. -/
def hlastMerge {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) : State :=
  { hlastEntry C s x inc nep v ix b35 r₁ r₂ r₃ cA rdv xA with
    pc := "cleanup478.i", pre := some "if.end473.i" }

/-! ### The cells these states carry -/

/-- `%8` at the token's end is the loop head's: neither the head chain nor
`cond.end349.i`'s two cells rebinds it. -/
theorem hlastEndS_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep c ix : BitVec 64) :
    lookupName (headEndS C s x inc nep c ix).env "%8" = lookupName s.env "%8" := by
  simp only [headEndS, condEnd349OutAt, headAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
    State.bind, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the token's end is the loop head's. -/
theorem hlastEndS_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep c ix : BitVec 64) :
    lookupName (headEndS C s x inc nep c ix).env "%end.i" = lookupName s.env "%end.i" := by
  simp only [headEndS, condEnd349OutAt, headAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
    State.bind, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%t352.i` at the token's end is the loop head's. -/
theorem hlastEndS_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep c ix : BitVec 64) :
    lookupName (headEndS C s x inc nep c ix).env "%t352.i" = lookupName s.env "%t352.i" := by
  simp only [headEndS, condEnd349OutAt, headAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
    State.bind, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%35` at the whitespace check's target. -/
theorem hlastLand_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastLand C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [hlastLand, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's first pivot. -/
theorem hlastP41_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastP41 C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [hlastP41, hlastLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's second pivot. -/
theorem hlastP39_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastP39 C s x inc nep v ix b35).env "%35" =
      some (.int 8 (head35 b35)) := by
  simp only [hlastP39, hlastP41, hlastLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%8` at the token's end `phi`'s source is the loop head's: the whitespace check and
the three pivots bind their own cells. -/
theorem hlastP35_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastP35 C s x inc nep v ix b35).env "%8" = lookupName s.env "%8" := by
  simp only [hlastP35, hlastP39, hlastP41, hlastLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hlastEndS_env8 C s x inc nep (BitVec.ofNat 64 v) ix

/-- `%end.i` at the same source. -/
theorem hlastP35_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastP35 C s x inc nep v ix b35).env "%end.i" = lookupName s.env "%end.i" := by
  simp only [hlastP35, hlastP39, hlastP41, hlastLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hlastEndS_envEnd C s x inc nep (BitVec.ofNat 64 v) ix

/-- The bound at the token's end's source: `cond.end349.i` bound it once. -/
theorem hlastP35_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastP35 C s x inc nep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [hlastP35, hlastP39, hlastP41, hlastLand, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hlastEndS_cond C s x inc nep v ix

/-- `%t352.i` at the tail's target is the loop head's: every block on the path binds its
own cells and none of them rebinds the token record's register. -/
theorem hlastEntry_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (hlastEntry C s x inc nep v ix b35 r₁ r₂ r₃ cA rdv xA).env "%t352.i" =
      lookupName (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).env "%t352.i" := by
  simp only [hlastEntry, ScanEntry, hlastTail, hlastSeam, HeadS413, HeadS405, HeadS58,
    HeadS60, HeadS62, seamS, seamFin, hlastP35, hlastP39, hlastP41, hlastLand, TailS₃,
    stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The token's end's `phi` selects `%cond350.i` when the whitespace check is what sent
the walk there: the entry's end, on the class with no run. -/
theorem hlast_phiSeam :
    phiIncoming "LeafBlock35"
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some (.reg "%cond350.i") := by
  decide

/-! ### The scan-free tail, counted at three

The tail's three links are `consumerTailSegAt`'s, with the third taken on its empty arm:
the copy call still runs and still appends the record, and the test it leaves the walk on
is `ult (%ee.1.i) (%cond350.i)` with both cells the same word — `0`, so the successor is
`if.end473.i` and the landing's local fact is `ScanEmpty`'s (`WalkLink.if_then447_i_empty`
carries that arm's `WalkLocal` unchanged).
-/

/-- **`if.then447.i`'s target, named, on the empty arm.**  The `_at` twin of
`WalkLink.if_then447_i_empty`: the same link and the same call contract, with the
successor written down.  `TailS₃`'s own `if` is `ult ei cd`, and the caller's `hempty` is
what resolves it — so the statement is his cell, not a second one here. -/
theorem walkIfThen447EmptyAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then447.i")
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hpre : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {cd : Nat}
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hcd64 : cd < 2 ^ 64) :
    ∃ (r : CallOutcome) (s' : State),
      stage2Calls stage2SubCalls "s2_after_value"
        [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r ∧
      WalkLink (stage2Calls stage2SubCalls) G C s
        { C with
          block := (if evalICmp .ult (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd) = 1
            then "land.rhs457.i" else "if.end473.i")
          stMap := walkAfterValueMap C } s' ∧
      s' = TailS₃ s r cd cd := by
  obtain ⟨r, hcall, hpost, -⟩ := s2AfterValueContract.resolves (next := s.next) hpre
  obtain ⟨s', hl⟩ := WalkLink.if_then447_i_empty (G := G) (C := C) (s := s) hInv hblock
    hrd hpre hei hcd rfl hcd64
  refine ⟨r, s', hcall, hl, ?_⟩
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen447I.instrs s =
      some (stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult (BitVec.ofNat 64 cd)
        (BitVec.ofNat 64 cd))) ] s.env) { s with mem := r.mem, next := r.next }) := by
    simpa only [stateAt] using (walkIfThen447I_denote (sub := stage2SubCalls) (env := s.env)
      (s := s) (sp := BitVec.ofNat 32 C.sp) (rd := G.next0 + 8) (ct := C.stage.ctype)
      (cs := C.stage.cst) (r := r) (ei := cd) (cd := cd) hInv.depth_reg hrd
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hei hcd)
  have hbit : lookupName (stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult
      (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd))) ] s.env)
      { s with mem := r.mem, next := r.next }).env "%cmp451.i" =
      some (.int 1 (evalICmp .ult (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd))) := by
    simp only [stateAt, cells, lookupName_cons_self]
  have hfind : stage2Body.findBlock s.pc = some walkIfThen447I := by
    rw [hInv.pc_eq, hblock]; exact walkIfThen447I_find
  have hterm : walkIfThen447I.term =
      Term.condbr (.reg "%cmp451.i") "land.rhs457.i" "if.end473.i" := rfl
  have hstep : step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump
      { stateAt (cells [("%cmp451.i", .int 1 (evalICmp .ult (BitVec.ofNat 64 cd)
          (BitVec.ofNat 64 cd))) ] s.env)
          { s with mem := r.mem, next := r.next } with
        pc := (if evalICmp .ult (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd) = 1
          then "land.rhs457.i" else "if.end473.i")
        pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%cmp451.i") (tl := "land.rhs457.i") (fl := "if.end473.i")
      (bit := evalICmp .ult (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd)) hbit]
    dsimp only [stateAt]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **The tail, counted at three, on the arm where the scan is empty.**  `consumerTailSegAt`'s
three links with the third's `hinner`/`hlt` replaced by the arm's own equation: the counter
and the bound are the same cell, so no span is claimed and none is needed. -/
theorem consumerTailSegEmptyAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (cd : Nat) :
    ∀ (_hInv : WalkInv G C s) (_hblock : C.block = "if.then413.i")
    (p : String) (_reg : String) (c : BitVec 32) (op : Operand) (rdv : BitVec 32)
    (x : BitVec 32),
    s.pre = some p →
    phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op →
    evalOperand (stateAt s.env s) op = some (.int 32 c) →
    lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)) →
    lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) →
    readBytes (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) →
    s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next →
    stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r₁ →
    r₁.ret = .int 32 x →
    evalICmp .eq x (BitVec.ofNat 32 0) = 0 →
    readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) →
    lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c) →
    lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok) →
    lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z) →
    stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂ →
    s2ScalarValueAppend r₁.mem r₂.mem (TailCarry₂ C).stage.z ev.encodedBytes →
    r₂.ret = .int 32 (BitVec.ofNat 32 1) →
    G.ev < 2 ^ 64 → C.evlen < 2 ^ 64 → C.events.length ≤ C.k → C.k < G.nep →
    s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next →
    stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next = some r₃ →
    lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
    lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
    cd < 2 ^ 64 →
    Seg (stage2Calls stage2SubCalls) G C s (TailCarryEnd C ev)
      (ScanEntry s r₁ r₂ r₃ cd cd c rdv x) 3 := by
  intro hInv hblock p reg c op rdv x hpre hinc hop hkind hrd hread hpre' hcall₁ hret₁
    hbit0 hzreadJ hc ht ho hcall₂ happ₂ hret₂ hev64 hevlen64 htight hklt hpre447 hcall₃ hei hcd hcd64
  -- 1. the value-position call
  have hx413 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x := by
    intro r hr
    have h : r = r₁ := Option.some.inj (hr.symm.trans hcall₁)
    rw [h]; exact hret₁
  obtain ⟨r₁', s₁', hcall₁', hl₁, hs₁'⟩ := walkIfThen413_at (G := G) (C := C) (s := s)
    (p := p) (reg := reg) (x := x) (op := op) hInv hblock hpre hinc hop hkind hrd hread hpre'
    hx413
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hs₁'
  have hs₁ : s₁' = TailS₁ s r₁ c rdv x := hs₁'
  rw [hs₁] at hl₁
  rw [show { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
      then "if.then418.i" else "if.then425.i") } = TailCarry₂ C from by rw [hbit0]; rfl] at hl₁
  -- 2. the scalar call's emit arm
  obtain ⟨s₂', hl₂, hs₂'⟩ := walkIfThen425_emit_at (G := G) (C := TailCarry₂ C)
    (s := TailS₁ s r₁ c rdv x) hl₁.inv' rfl
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%c.i") _ _ (by decide)] using hc)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%t352.i") _ _ (by decide)] using ht)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%z") _ _ (by decide)] using ho)
    (by simpa only [TailS₁, stateAt] using hzreadJ)
    (by simpa only [TailS₁, stateAt] using hcall₂) happ₂ hret₂ hev64 hevlen64 htight hklt
  have hs₂ : s₂' = TailS₂ (TailS₁ s r₁ c rdv x) r₂ := hs₂'
  rw [hs₂] at hl₂
  -- 3. the copy call, on the arm where the scan is empty
  obtain ⟨r₃', s₃', hcall₃', hl₃, hs₃'⟩ := walkIfThen447EmptyAt (G := G)
    (C := TailCarry₃ C ev) (s := TailS₂ (TailS₁ s r₁ c rdv x) r₂) hl₂.inv' rfl
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%root_done.i") _ _ (by decide)] using hrd)
    (by simpa only [TailS₂, TailS₁, stateAt] using hpre447)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%ee.1.i") _ _ (by decide)] using hei)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%cond350.i") _ _ (by decide)] using hcd)
    hcd64
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hs₃'
  rw [show (if evalICmp .ult (BitVec.ofNat 64 cd) (BitVec.ofNat 64 cd) = 1
      then "land.rhs457.i" else "if.end473.i") = "if.end473.i" from by
    rw [hlast_ult_self (BitVec.ofNat 64 cd)]; rfl] at hl₃
  have hs₃ : s₃' = TailS₃ (TailS₂ (TailS₁ s r₁ c rdv x) r₂) r₃ cd cd := hs₃'
  rw [hs₃] at hl₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

/-! ### The token's end's source, at `%8`

`if.end372.i`'s else arm binds five cells and none of them is `%8`, so the seam's byte
test and the class-C span's three read the entry's first byte — the same witness the
head's four pivots read. -/

/-- `%8` at the seam is the token's end source's own: the seam binds five cells and none
of them is `%8`. -/
theorem hlastSeam_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (hlastSeam C s x inc nep v ix b35).env "%8" =
      lookupName (hlastP35 C s x inc nep v ix b35).env "%8" := by
  simp only [hlastSeam, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The prefix, as one segment at its own count

The last entry's path to the merge's entry: `walkHeadChainASeg`'s six links (the four
pivots, `sw.default.i`'s failing count test and the byte test's `1` arm), the whitespace
check's four, the token's end's one, the class-C span's five and the scan-free tail's
three — `6 + 4 + 1 + 5 + 3 = 19`. -/

/-- **The head path to the tail's start, counted at sixteen.**  The six head links, the
whitespace check's four, the token's end's one and the class-C span's five.  It is cut out
of `hlastPrefixSeg` so that the tail's *source* invariant has a producer: a segment records
only its target's, so a consumer that must supply the tail (`hlastTail_of_calls`,
`hlastFacts_of_staging`) takes `inv'` of this. -/
theorem hlastTailSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} {ix : BitVec 64}
    (hav5 : lookupName (headAS₅ s x inc nep).env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hbit6 : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hc110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x (BitVec.ofNat 8 116) = 0) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (TailStartC C)
      (hlastTail C s x inc nep v ix b35) 16 := by
  -- the head's fall-through and the byte test's `1` arm: six links
  have hA : Seg (stage2Calls stage2SubCalls) G C s (HlastAC₁ C)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix) 6 :=
    walkHeadChainASeg (G := G) (C := C) (s := s) hInv hblock h8 hlt91 hlt123 hlt125 hne125
      hinc hnep hge hav5 hidx5 htok5 hgap5 hugt
  -- the whitespace check: four links at the byte before the token's end
  have hig : lookupName (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    (Seg.measure hA).inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := hlastEndS_cond C s x inc nep v ix
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.land_lhs_true357_i_at G (HlastAC₁ C)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix) (Seg.measure hA).inv' rfl
      (ig := G.b - 1) (q := v) (b := b35) hig hcond hv63 hread35
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₁ C)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix) (HlastAC₂ C)
      (hlastLand C s x inc nep v ix b35) := by
    rw [hs₇] at hl₇
    exact hl₇
  -- the byte's first pivot
  have h35a : evalOperand (hlastLand C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact hlastLand_35 C s x inc nep v ix b35
  obtain ⟨s₈, hl₈, hs₈⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (HlastAC₂ C)
      (hlastLand C s x inc nep v ix b35) hl₇'.inv' rfl h35a
  have hl₈' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₂ C)
      (hlastLand C s x inc nep v ix b35) (HlastAC₃ C)
      (hlastP41 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₈ = hlastP41 C s x inc nep v ix b35 := by rw [hs₈, harm]; rfl
    rw [hst] at hl₈
    rw [harm] at hl₈
    exact hl₈
  -- the byte's second pivot
  have h35b : evalOperand (hlastP41 C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact hlastP41_35 C s x inc nep v ix b35
  obtain ⟨s₉, hl₉, hs₉⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (HlastAC₃ C)
      (hlastP41 C s x inc nep v ix b35) hl₈'.inv' rfl h35b
  have hl₉' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₃ C)
      (hlastP41 C s x inc nep v ix b35) (HlastAC₄ C)
      (hlastP39 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := by rw [hb32]; rfl
    have hst : s₉ = hlastP39 C s x inc nep v ix b35 := by rw [hs₉, harm]; rfl
    rw [hst] at hl₉
    rw [harm] at hl₉
    exact hl₉
  -- the leaf's equality test
  have h35c : evalOperand (hlastP39 C s x inc nep v ix b35) (.reg "%35") =
      some (.int 8 (head35 b35)) := by
    simp only [evalOperand]
    exact hlastP39_35 C s x inc nep v ix b35
  obtain ⟨s₁₀, hl₁₀, hs₁₀⟩ :=
    WalkLink.LeafBlock35_at (calls := stage2Calls stage2SubCalls) G (HlastAC₄ C)
      (hlastP39 C s x inc nep v ix b35) hl₉'.inv' rfl h35c
  have hl₁₀' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₄ C)
      (hlastP39 C s x inc nep v ix b35) (HeadAC₆ C)
      (hlastP35 C s x inc nep v ix b35) := by
    have harm : (if evalICmp .eq (head35 b35) (BitVec.ofNat 8 13) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by rw [hbne13]; rfl
    have hst : s₁₀ = hlastP35 C s x inc nep v ix b35 := by rw [hs₁₀, harm]; rfl
    rw [hst] at hl₁₀
    rw [harm] at hl₁₀
    exact hl₁₀
  -- the token's end: one link
  have h8s : evalOperand (hlastP35 C s x inc nep v ix b35) (.reg "%8") = some (.int 8 x) := by
    simp only [evalOperand]
    rw [hlastP35_env8 C s x inc nep v ix b35]
    exact h8
  have hconds : evalOperand (hlastP35 C s x inc nep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    simp only [evalOperand]
    exact hlastP35_cond C s x inc nep v ix b35
  have hends : lookupName (hlastP35 C s x inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
    rw [hlastP35_envEnd C s x inc nep v ix b35]
    exact (Seg.measure hA).inv'.regs ("%end.i", .ptr (C.stage.tok + 8))
      (by simp [walkStaticRegs])
  obtain ⟨s₁₁, hl₁₁, hs₁₁⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := HeadAC₆ C)
      (s := hlastP35 C s x inc nep v ix b35) hl₁₀'.inv' rfl (p := "LeafBlock35") rfl
      hlast_phiSeam hconds hends h8s hbit6
  have hl₁₁' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₆ C)
      (hlastP35 C s x inc nep v ix b35) (HeadSeamC C)
      (hlastSeam C s x inc nep v ix b35) := by
    rw [hs₁₁] at hl₁₁
    exact hl₁₁
  -- the head part, counted at eleven
  have hseg5 : Seg (stage2Calls stage2SubCalls) G (HlastAC₁ C)
      (headEndS C s x inc nep (BitVec.ofNat 64 v) ix) (HeadSeamC C)
      (hlastSeam C s x inc nep v ix b35) 5 :=
    Seg.tail hl₇' (Seg.tail hl₈' (Seg.tail hl₉' (Seg.tail hl₁₀'
      (Seg.tail hl₁₁' (Seg.nil hl₁₁'.inv')))))
  have hseg11 : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadSeamC C)
      (hlastSeam C s x inc nep v ix b35) 11 :=
    (Seg.measure hA).trans (Seg.measure hseg5)
  -- the class-C span, five links
  have h8c : evalOperand (hlastSeam C s x inc nep v ix b35) (.reg "%8") = some (.int 8 x) := by
    simp only [evalOperand]
    rw [hlastSeam_env8 C s x inc nep v ix b35, hlastP35_env8 C s x inc nep v ix b35]
    exact h8
  have hC : Seg (stage2Calls stage2SubCalls) G (HeadSeamC C)
      (hlastSeam C s x inc nep v ix b35) (TailStartC C)
      (hlastTail C s x inc nep v ix b35) 5 :=
    walkHeadChainCSeg (G := G) (C := HeadSeamC C) (s := hlastSeam C s x inc nep v ix b35)
      hl₁₁'.inv' rfl h8c hc110 hc116 hceq116
  -- the head part and the class-C span: `11 + 5 = 16`
  exact hseg11.trans (Seg.measure hC)

/-- **The last entry's path to the merge's entry, counted at nineteen.**  The sixteen
links to the tail's start and the scan-free tail's three. -/
theorem hlastPrefixSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} {ix : BitVec 64}
    (hav5 : lookupName (headAS₅ s x inc nep).env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (head35 b35) (BitVec.ofNat 8 13) = 0)
    (hbit6 : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hc110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
      (hlastTail C s x inc nep v ix b35)
      (TailCarryEnd (TailStartC C) ev)
      (hlastEntry C s x inc nep v ix b35 r₁ r₂ r₃ cA rdv xA) 3) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryEnd (TailStartC C) ev)
      (hlastEntry C s x inc nep v ix b35 r₁ r₂ r₃ cA rdv xA) 19 :=
  (hlastTailSeg (G := G) (C := C) (s := s) hInv hblock h8 hlt91 hlt123 hlt125 hne125
    hinc hnep hge hav5 hidx5 htok5 hgap5 hugt hread35 hv63 hb13 hb32 hbne13 hbit6
    hc110 hc116 hceq116).trans hTail

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChainASeg
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen447EmptyAt
#print axioms LeanLLVM.Refinement.WalkScope.consumerTailSegEmptyAt
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailSeg
#print axioms LeanLLVM.Refinement.WalkScope.hlastPrefixSeg

end WalkScope
end LeanLLVM.Refinement
