/-
# The letters class's head chain, per head class

`JsonStage2WalkDispatchSegments` records why the head's chain to `if.else387.i` is not one
composition: the four pivots above `sw.default.i` select different blocks per head-switch
class, so the chain's carries and states — which a `Seg` unifies syntactically — are the
class's own.  `contPrefixLand` states the *high-byte* class's eight links (the bytes
`126`/`127`, the bits `slt 91 = 0`, `slt 123 = 0`, `slt 125 = 0`, `≠ 125`), and the letters
arm's own classes had no statement at all.

This module factors that chain into the two parts the classes actually share and the part
they do not:

* **the suffix** — `sw.default.i`'s step, the count test's succeeding arm
  (`cond.true345.i`), the bound's `phi` (`cond.end349.i`), the whitespace check
  (`land.lhs.true357.i`), the byte's three pivots (`NodeBlock41`, `NodeBlock39`,
  `LeafBlock35`) and the token's end (`if.end372.i`) — eight links, stated at **any** state
  whose block is `sw.default.i` (`contDefaultSeg`).  The blocks from `sw.default.i` on do
  not read the pivot cells the head switch bound, so the eight links are the same eight for
  every class that reaches the default arm; only the *state term* differs, and it is the
  suffix's parameter.
* **the prefixes** — the pivots to `sw.default.i`, one per head-switch class:
  `.defaultValueLow` (`NodeBlock5 → LeafBlock`, three links), `.defaultValueMid`
  (`NodeBlock5 → NodeBlock → LeafBlock3`, four), `.otherValue`
  (`NodeBlock5 → NodeBlock → LeafBlock1`, four), `.defaultValueBracket`
  (`NodeBlock19 → NodeBlock11 → LeafBlock7`, four) and `.defaultValueBracketHigh`
  (`NodeBlock19 → NodeBlock11 → LeafBlock9`, four).  Each prefix is joined to the suffix at
  its own `sw.default.i` state, so the count is the class's: **eleven** for `.defaultValueLow`
  (the low bytes and every byte above `127`, which the signed pivots route together) and
  **twelve** for the four bracket-and-mid classes.

## What the letters class admits

The letters arm's class is `slt %8 110 = 1` in the signed order beside the tag test's clear
arm and `%8 ≠ 102`.  Its bytes are `0 … 109 \ {45, 48…57, 102}` and `128 … 255`, which the
head switch sends through *five* default classes: `.defaultValueLow` for `0 … 43` and
`128 … 255`, `.defaultValueMid` for `59 … 90`, `.otherValue` for `46`/`47`,
`.defaultValueBracket` for `92` and `.defaultValueBracketHigh` for `94 … 109`.  The other
classes of the head switch are the dispatch's own arms (`"`, `,`, `:`, `[`, `{`, `]`, `}`,
`f`), so a producer that holds the class has the prefix; a producer that holds only the
letters class does not, and the five theorems below are what makes the class's chain a
statement rather than a field.

The chain's *cells* are the lane's: the entry count at the head (the invariant's), the next
entry's position word and its read (the document's), the position table's index and the
token record's two addresses, the bound's compare, and the byte before the entry's end with
its three class bits.  They enter as the arm's own premises at the class's named states,
exactly as `HcontFacts` carries them for the high-byte route.

## The suffix's states

Five names, mirroring `contPrefixLand`'s, each a block's target as its `_at` lemma states
it, but parameterized by the state they are read at rather than by the high-byte route's
`headAS₄`.  `contSeamMid` is the suffix's endpoint: `if.else387.i`'s state, which is where
the class-C span (`lettersSpan`, `fSpan`, `classCSpan_at`) begins.

## The last entry's suffix, and the class's counted prefix

The same factoring at the *exhausted* count: `%inc.i ≥ %nep` is the arm `sw.default.i`
leaves on, so the count test's succeeding arm is not taken and `cond.end349.i` follows
directly — the bound's `phi` selects `%4` there, the document's own width word.  That is
`contDefLastSeg`, seven links at any state at `sw.default.i`, and `contSeamMidFail` is its
endpoint.

The prefixes are the continuing ones, now stated once per class as counted chains
(`contLowToDefault` at three links, `contMidToDefault`/`contOthToDefault`/
`contBrkToDefault`/`contBhToDefault`/`contBrcToDefault` at four), and `Seg.trans` composes
counted chains.  So the last entry's chain to `if.else387.i` is the class's prefix beside
the seven-link suffix — `contLastLowHeadSeg` at ten links, the other five at eleven — one
link shorter than the continuing chain's eleven and twelve, which is the count the last
entry's `.letters`/`.fLetter`/`.classC` arms state (`nH ≤ 11`).
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLetters
import LeanLLVM.Refinement.JsonStage2WalkRevolutionPrefix

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The suffix's states, at any state at `sw.default.i` -/

/-- `sw.default.i`'s target on the succeeding arm: the count test's cell, at
`cond.true345.i`. -/
def contSwOut (s : State) (inc nep : BitVec 64) : State :=
  { (s.bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep))) with
    pc := "cond.true345.i", pre := some s.pc }

/-- `cond.end349.i`'s target: the bound's cell and the token's two stores. -/
def contMidS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) : State :=
  condEnd349OutAt (cte345OutAt (contSwOut q inc nep) ep inc v)
    (BitVec.ofNat 64 v.toNat) ix C.stage.tok (C.stage.tok + 20)

/-- The whitespace check's target: the byte before the entry's end, at `NodeBlock41`. -/
def contLandOut {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) : State :=
  { (stateAt (cells [("%35", .int 8 (cont35 b35)),
      ("%gep", .ptr ((G.b - 1) + v))] s.env) s) with
    pc := "NodeBlock41", pre := some s.pc }

/-- `NodeBlock41`'s target: the byte's first pivot, at `NodeBlock39`. -/
def contP41Out (s : State) (b35 : UInt8) : State :=
  { (s.bind "%Pivot42" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock39", pre := some s.pc }

/-- `NodeBlock39`'s target: the byte's second pivot, at `LeafBlock35`. -/
def contP39Out (s : State) (b35 : UInt8) : State :=
  { (s.bind "%Pivot40" (.int 1 (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock35", pre := some s.pc }

/-- `LeafBlock35`'s target: the byte's equality test, at `if.end372.i`. -/
def contP35Out (s : State) (b35 : UInt8) : State :=
  { (s.bind "%SwitchLeaf36" (.int 1 (evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13)))) with
    pc := "if.end372.i", pre := some s.pc }

/-- The byte's three pivots' target, at `if.end372.i`. -/
def contP35Mid {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) : State :=
  contP35Out (contP39Out (contP41Out (contLandOut (G := G)
    (contMidS C q inc nep ep v ix) v.toNat b35) b35) b35) b35

/-- The suffix's endpoint: `if.end372.i`'s else arm, at the class-C span's entry. -/
def contSeamMid {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (b8 : BitVec 8) : State :=
  seamS (contP35Mid C q inc nep ep v ix b35) (BitVec.ofNat 64 v.toNat) b8 C.stage.tok

/-! ### The cells the suffix's own states carry -/

/-- `%35` at the whitespace check's target. -/
theorem contLandOut_35 {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) :
    lookupName (contLandOut (G := G) s v b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contLandOut, stateAt, cells]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's first pivot. -/
theorem contP41Out_35 {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) :
    lookupName (contP41Out (contLandOut (G := G) s v b35) b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contP41Out, contLandOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%35` at the byte's second pivot. -/
theorem contP39Out_35 {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) :
    lookupName (contP39Out (contP41Out (contLandOut (G := G) s v b35) b35) b35).env "%35" =
      some (.int 8 (cont35 b35)) := by
  simp only [contP39Out, contP41Out, contLandOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end is the bound `cond.end349.i` stored. -/
theorem contP35Mid_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contP35Mid C q inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contP35Mid, contP35Out, contP39Out, contP41Out, contLandOut, contMidS,
    condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the bound's target, before the byte's pivots. -/
theorem contMidS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    lookupName (contMidS C q inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contMidS, condEnd349OutAt, cells]
  rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%8` at the token's end is the state's own: the byte's pivots and the seam bind no
`%8`. -/
theorem contP35Mid_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contP35Mid C q inc nep ep v ix b35).env "%8" = lookupName q.env "%8" := by
  simp only [contP35Mid, contP35Out, contP39Out, contP41Out, contLandOut, contMidS,
    condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the token's end is the state's own: no block of the suffix rebinds it. -/
theorem contP35Mid_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contP35Mid C q inc nep ep v ix b35).env "%end.i" = lookupName q.env "%end.i" := by
  simp only [contP35Mid, contP35Out, contP39Out, contP41Out, contLandOut, contMidS,
    condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the seam is the token's end's own. -/
theorem contSeamMid_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (b8 : BitVec 8) :
    lookupName (contSeamMid C q inc nep ep v ix b35 b8).env "%8" =
      lookupName q.env "%8" := by
  simp only [contSeamMid, seamS, seamFin, contP35Mid, contP35Out, contP39Out, contP41Out,
    contLandOut, contMidS, condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The suffix, counted at eight -/

/-- **The default arm's four links to the whitespace check**, at any state at
`sw.default.i`.  `contDefaultSeg`'s first four, cut out so the run class's head can join
them to the run instead of to the byte's pivots and the token's end: every default class's
run reaches its check state as its own prefix plus these four. -/
theorem contSwToLandSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (hInv : WalkInv G (HeadAC₄ C) q5) (hblock : (HeadAC₄ C).block = "sw.default.i")
    {inc nep : BitVec 64}
    (hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut q5 inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut q5 inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut q5 inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C q5 inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
      some [b35]) :
    WalkSegment (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5 (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) 4 := by
  -- 1. `sw.default.i`'s count test, on the succeeding arm
  have hres₁ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.true345.i" := by
    rw [hnext]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      hInv hblock hinc hnep
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      (ContAC₁ C) (contSwOut q5 inc nep) := by
    have hst : s₁ = contSwOut q5 inc nep := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `cond.true345.i`: the next entry's lane
  have hinc' : lookupName (contSwOut q5 inc nep).env "%inc.i" = some (.int 64 inc) := by
    simp only [contSwOut, State.bind, lookupName_cons_ne (k := "%cmp343.i") (n := "%inc.i")
      _ _ (by decide)]
    simpa only [evalOperand] using hinc
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.cond_true345_i_at (calls := stage2Calls stage2SubCalls) G (ContAC₁ C)
      (contSwOut q5 inc nep) hl₁'.inv' rfl h5 hinc' hi63 hread
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₁ C) (contSwOut q5 inc nep)
      (ContAC₂ C) (cte345OutAt (contSwOut q5 inc nep) ep inc v) := by
    rw [hs₂] at hl₂
    exact hl₂
  -- 3. the bound's `phi` and the compare
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.cond_end349_i_at G (ContAC₂ C) (cte345OutAt (contSwOut q5 inc nep) ep inc v)
      hl₂'.inv' rfl (p := "cond.true345.i") rfl contPhi6
      (cte345OutAt_conv (contSwOut q5 inc nep) ep inc v) hidx htok hgap
  have hres₃ : (if evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₂ C)
      (cte345OutAt (contSwOut q5 inc nep) ep inc v) (ContAC₃ C)
      (contMidS C q5 inc nep ep v ix) := by
    have hst : s₃ = contMidS C q5 inc nep ep v ix := by
      rw [hs₃]
      rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the whitespace check: the byte before the entry's end
  have hig : lookupName (contMidS C q5 inc nep ep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hl₃'.inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (contMidS C q5 inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := contMidS_cond C q5 inc nep ep v ix
  have hq63 : v.toNat < 2 ^ 63 := by have := v.isLt; omega
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.land_lhs_true357_i_at G (ContAC₃ C) (contMidS C q5 inc nep ep v ix)
      hl₃'.inv' rfl (ig := G.b - 1) (q := v.toNat) (b := b35) hig hcond hq63 hread35
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₃ C)
      (contMidS C q5 inc nep ep v ix) (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) := by
    rw [hs₄] at hl₄
    exact hl₄
  exact ((WalkSegment.of_link hl₁').trans (WalkSegment.of_link hl₂')).trans
    ((WalkSegment.of_link hl₃').trans (WalkSegment.of_link hl₄'))

/-- **The default arm's chain from `sw.default.i` to `if.else387.i`, at any state.**  The
count test's succeeding arm, the bound's `phi`, the whitespace check and the byte's three
pivots with the token's end: eight links, the same eight for every head class that reaches
the default arm.

`q5` is the state at `sw.default.i` — the class's prefix ends there — and `b35`/`b8` are the
byte before the entry's end and the head's byte at the seam.  Nothing in these eight blocks
reads a cell the head switch bound, which is what makes one statement cover every class:
the route enters as the state term, not as a hypothesis about it. -/
theorem contDefaultSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (hInv : WalkInv G (HeadAC₄ C) q5) (hblock : (HeadAC₄ C).block = "sw.default.i")
    {inc nep : BitVec 64}
    (hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut q5 inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut q5 inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut q5 inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C q5 inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C q5 inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C q5 inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5 (ContSeamC C)
      (contSeamMid C q5 inc nep ep v ix b35 b8) 8 := by
  -- 1. `sw.default.i`'s count test, on the succeeding arm
  have hres₁ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.true345.i" := by
    rw [hnext]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      hInv hblock hinc hnep
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      (ContAC₁ C) (contSwOut q5 inc nep) := by
    have hst : s₁ = contSwOut q5 inc nep := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `cond.true345.i`: the next entry's lane
  have hinc' : lookupName (contSwOut q5 inc nep).env "%inc.i" = some (.int 64 inc) := by
    simp only [contSwOut, State.bind, lookupName_cons_ne (k := "%cmp343.i") (n := "%inc.i")
      _ _ (by decide)]
    simpa only [evalOperand] using hinc
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.cond_true345_i_at (calls := stage2Calls stage2SubCalls) G (ContAC₁ C)
      (contSwOut q5 inc nep) hl₁'.inv' rfl h5 hinc' hi63 hread
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₁ C) (contSwOut q5 inc nep)
      (ContAC₂ C) (cte345OutAt (contSwOut q5 inc nep) ep inc v) := by
    rw [hs₂] at hl₂
    exact hl₂
  -- 3. the bound's `phi` and the compare
  have hidx' : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix) := hidx
  have htok' : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok) := htok
  have hgap' : lookupName (contSwOut q5 inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)) := hgap
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.cond_end349_i_at G (ContAC₂ C) (cte345OutAt (contSwOut q5 inc nep) ep inc v)
      hl₂'.inv' rfl (p := "cond.true345.i") rfl contPhi6
      (cte345OutAt_conv (contSwOut q5 inc nep) ep inc v) hidx' htok' hgap'
  have hres₃ : (if evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₂ C)
      (cte345OutAt (contSwOut q5 inc nep) ep inc v) (ContAC₃ C)
      (contMidS C q5 inc nep ep v ix) := by
    have hst : s₃ = contMidS C q5 inc nep ep v ix := by
      rw [hs₃]
      rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the whitespace check: the byte before the entry's end
  have hig : lookupName (contMidS C q5 inc nep ep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hl₃'.inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (contMidS C q5 inc nep ep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := contMidS_cond C q5 inc nep ep v ix
  have hq63 : v.toNat < 2 ^ 63 := by have := v.isLt; omega
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.land_lhs_true357_i_at G (ContAC₃ C) (contMidS C q5 inc nep ep v ix)
      hl₃'.inv' rfl (ig := G.b - 1) (q := v.toNat) (b := b35) hig hcond hq63 hread35
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₃ C)
      (contMidS C q5 inc nep ep v ix) (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) := by
    rw [hs₄] at hl₄
    exact hl₄
  -- 5. the byte's first pivot
  have h35a : evalOperand (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
      (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandOut_35 (s := contMidS C q5 inc nep ep v ix) (v := v.toNat) b35
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) hl₄'.inv' rfl h35a
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) (ContAC₅ C)
      (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₅ = contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        b35 := by rw [hs₅, harm]; rfl
    rw [hst] at hl₅
    rw [harm] at hl₅
    exact hl₅
  -- 6. the byte's second pivot
  have h35b : evalOperand
      (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) b35)
      (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP41Out_35 (s := contMidS C q5 inc nep ep v ix) (v := v.toNat) b35
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (ContAC₅ C)
      (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) b35)
      hl₅'.inv' rfl h35b
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₅ C)
      (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) b35)
      (ContAC₆ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := by rw [hb32]; rfl
    have hst : s₆ = contP39Out
        (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) b35) b35 := by
      rw [hs₆, harm]; rfl
    rw [hst] at hl₆
    rw [harm] at hl₆
    exact hl₆
  -- 7. the leaf's equality test
  have h35c : evalOperand
      (contP39Out (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        b35) b35) (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP39Out_35 (s := contMidS C q5 inc nep ep v ix) (v := v.toNat) b35
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.LeafBlock35_at (calls := stage2Calls stage2SubCalls) G (ContAC₆ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        b35) b35) hl₆'.inv' rfl h35c
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₆ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        b35) b35) (ContAC₇ C) (contP35Mid C q5 inc nep ep v ix b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by rw [hbne13]; rfl
    have hst : s₇ = contP35Mid C q5 inc nep ep v ix b35 := by
      rw [hs₇, harm]
      rfl
    rw [hst] at hl₇
    rw [harm] at hl₇
    exact hl₇
  -- 8. the token's end
  have hcond35 : evalOperand (contP35Mid C q5 inc nep ep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    simp only [evalOperand]
    exact contP35Mid_cond C q5 inc nep ep v ix b35
  obtain ⟨s₈, hl₈, hs₈⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := ContAC₇ C)
      (s := contP35Mid C q5 inc nep ep v ix b35) hl₇'.inv' rfl (p := "LeafBlock35") rfl
      contPhiSeam hcond35 hend h8end hbit
  have hl₈' : WalkLink (stage2Calls stage2SubCalls) G (ContAC₇ C)
      (contP35Mid C q5 inc nep ep v ix b35) (ContSeamC C)
      (contSeamMid C q5 inc nep ep v ix b35 b8) := by
    rw [hs₈] at hl₈
    exact hl₈
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇' (Seg.tail hl₈'
      (Seg.nil hl₈'.inv'))))))))

/-! ### The prefixes, one per head-switch class

Each prefix is the head switch's steps from `NodeBlock21` to the class's
`sw.default.i`, at the class's own bits.  The carries are the emitted blocks; the states
are their `_at` lemmas' targets, named because the suffix's hypotheses are read at the last
one. -/

/-! #### `.defaultValueLow`: `NodeBlock5 → LeafBlock`, three links -/

/-- The carry at `NodeBlock5`: the first pivot's low arm. -/
abbrev LowAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- The carry at `LeafBlock`. -/
abbrev LowAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { LowAC₁ C with block := "LeafBlock" }

/-- The state `NodeBlock21` leaves on the low arm. -/
def lowS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- The state `NodeBlock5` leaves on the low arm. -/
def lowS₂ (s : State) (x : BitVec 8) : State :=
  { (lowS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "LeafBlock", pre := some (lowS₁ s x).pc }

/-- The state `LeafBlock` leaves: the class's `sw.default.i`. -/
def lowS₃ (s : State) (x : BitVec 8) : State :=
  { (lowS₂ s x).bind "%SwitchLeaf" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 34))) with
    pc := "sw.default.i", pre := some (lowS₂ s x).pc }

/-- **The low class's head chain to `if.else387.i`, at three plus eight.**  `91 ≤ %8` is
false in the signed order, `%8 < 44` true and `%8 ≠ 34`: `NodeBlock5 → LeafBlock →
sw.default.i`, then `contDefaultSeg`'s eight.  The low bytes and every byte above `127`
take this route — the signed `slt` sends both to `NodeBlock5` — which is why the class is
one prefix and not two. -/
theorem contLowHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (lowS₃ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (lowS₃ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (lowS₃ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (lowS₃ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (lowS₃ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (lowS₃ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (lowS₃ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (lowS₃ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (lowS₃ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (lowS₃ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (lowS₃ s x) inc nep ep v ix b35 b8) 11 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "LeafBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .eq x (BitVec.ofNat 8 34) = 1 then
      "sw.bb202.i" else "sw.default.i") = "sw.default.i" := by rw [hne34]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (LowAC₁ C) (lowS₁ s x) := by
    have hst : s₁ = lowS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock5`'s second pivot
  have h8₂ : evalOperand (lowS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [lowS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (LowAC₁ C)
      (lowS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (LowAC₁ C) (lowS₁ s x)
      (LowAC₂ C) (lowS₂ s x) := by
    have hst : s₂ = lowS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the leaf's equality test
  have h8₃ : evalOperand (lowS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [lowS₂, lowS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock_at (calls := stage2Calls stage2SubCalls) G (LowAC₂ C)
      (lowS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (LowAC₂ C) (lowS₂ s x)
      (HeadAC₄ C) (lowS₃ s x) := by
    have hst : s₃ = lowS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (lowS₃ s x)
      (ContSeamC C) (contSeamMid C (lowS₃ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (lowS₃ s x) hl₃'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (by
    simpa only [Nat.reduceAdd] using hseg8)))

/-! #### `.defaultValueMid`: `NodeBlock5 → NodeBlock → LeafBlock3`, four links -/

/-- The carry at `NodeBlock5`: the first pivot's low arm. -/
abbrev MidAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- The carry at `NodeBlock`. -/
abbrev MidAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { MidAC₁ C with block := "NodeBlock" }

/-- The carry at `LeafBlock3`. -/
abbrev MidAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { MidAC₂ C with block := "LeafBlock3" }

/-- The state `NodeBlock21` leaves on the low arm. -/
def midS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- The state `NodeBlock5` leaves: `44 ≤ %8`, so `NodeBlock`. -/
def midS₂ (s : State) (x : BitVec 8) : State :=
  { (midS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "NodeBlock", pre := some (midS₁ s x).pc }

/-- The state `NodeBlock` leaves: `58 ≤ %8`, so `LeafBlock3`. -/
def midS₃ (s : State) (x : BitVec 8) : State :=
  { (midS₂ s x).bind "%Pivot" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 58))) with
    pc := "LeafBlock3", pre := some (midS₂ s x).pc }

/-- The state `LeafBlock3` leaves: the class's `sw.default.i`. -/
def midS₄ (s : State) (x : BitVec 8) : State :=
  { (midS₃ s x).bind "%SwitchLeaf4" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 58))) with
    pc := "sw.default.i", pre := some (midS₃ s x).pc }

/-- **The mid class's head chain to `if.else387.i`, at four plus eight.**  `%8 < 91`,
`44 ≤ %8`, `58 ≤ %8` and `%8 ≠ 58`: `NodeBlock5 → NodeBlock → LeafBlock3 → sw.default.i`,
then `contDefaultSeg`'s eight. -/
theorem contMidHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (midS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (midS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (midS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (midS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (midS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (midS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (midS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (midS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (midS₄ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (midS₄ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (midS₄ s x) inc nep ep v ix b35 b8) 12 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock3" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 58) = 1 then
      "if.then173.i" else "sw.default.i") = "sw.default.i" := by rw [hne58]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (MidAC₁ C) (midS₁ s x) := by
    have hst : s₁ = midS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock5`'s second pivot
  have h8₂ : evalOperand (midS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (MidAC₁ C)
      (midS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₁ C) (midS₁ s x)
      (MidAC₂ C) (midS₂ s x) := by
    have hst : s₂ = midS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. `NodeBlock`'s third pivot
  have h8₃ : evalOperand (midS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₂, midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (MidAC₂ C)
      (midS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₂ C) (midS₂ s x)
      (MidAC₃ C) (midS₃ s x) := by
    have hst : s₃ = midS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  have h8₄ : evalOperand (midS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₃, midS₂, midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock3_at (calls := stage2Calls stage2SubCalls) G (MidAC₃ C)
      (midS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₃ C) (midS₃ s x)
      (HeadAC₄ C) (midS₄ s x) := by
    have hst : s₄ = midS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (midS₄ s x)
      (ContSeamC C) (contSeamMid C (midS₄ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (midS₄ s x) hl₄'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (by
    simpa only [Nat.reduceAdd] using hseg8))))

/-! #### `.otherValue`: `NodeBlock5 → NodeBlock → LeafBlock1`, four links -/

/-- The carry at `NodeBlock5`: the first pivot's low arm. -/
abbrev OthAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock5" }

/-- The carry at `NodeBlock`. -/
abbrev OthAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { OthAC₁ C with block := "NodeBlock" }

/-- The carry at `LeafBlock1`. -/
abbrev OthAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { OthAC₂ C with block := "LeafBlock1" }

/-- The state `NodeBlock21` leaves on the low arm. -/
def othS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock5", pre := some s.pc }

/-- The state `NodeBlock5` leaves: `44 ≤ %8`, so `NodeBlock`. -/
def othS₂ (s : State) (x : BitVec 8) : State :=
  { (othS₁ s x).bind "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
    pc := "NodeBlock", pre := some (othS₁ s x).pc }

/-- The state `NodeBlock` leaves: `%8 < 58`, so `LeafBlock1`. -/
def othS₃ (s : State) (x : BitVec 8) : State :=
  { (othS₂ s x).bind "%Pivot" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 58))) with
    pc := "LeafBlock1", pre := some (othS₂ s x).pc }

/-- The state `LeafBlock1` leaves: the class's `sw.default.i`. -/
def othS₄ (s : State) (x : BitVec 8) : State :=
  { (othS₃ s x).bind "%SwitchLeaf2" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 44))) with
    pc := "sw.default.i", pre := some (othS₃ s x).pc }

/-- **The `.otherValue` class's head chain to `if.else387.i`, at four plus eight.**  `%8 < 91`,
`44 ≤ %8`, `%8 < 58` and `%8 ≠ 44`: `NodeBlock5 → NodeBlock → LeafBlock1 → sw.default.i`,
then `contDefaultSeg`'s eight.  This is the class of the two bytes `46`/`47`. -/
theorem contOthHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (othS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (othS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (othS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (othS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (othS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (othS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (othS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (othS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (othS₄ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (othS₄ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (othS₄ s x) inc nep ep v ix b35 b8) 12 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock1" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 44) = 1 then
      "if.then127.i" else "sw.default.i") = "sw.default.i" := by rw [hne44]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (OthAC₁ C) (othS₁ s x) := by
    have hst : s₁ = othS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock5`'s second pivot
  have h8₂ : evalOperand (othS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (OthAC₁ C)
      (othS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₁ C) (othS₁ s x)
      (OthAC₂ C) (othS₂ s x) := by
    have hst : s₂ = othS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. `NodeBlock`'s third pivot
  have h8₃ : evalOperand (othS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₂, othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (OthAC₂ C)
      (othS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₂ C) (othS₂ s x)
      (OthAC₃ C) (othS₃ s x) := by
    have hst : s₃ = othS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  have h8₄ : evalOperand (othS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₃, othS₂, othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock1_at (calls := stage2Calls stage2SubCalls) G (OthAC₃ C)
      (othS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₃ C) (othS₃ s x)
      (HeadAC₄ C) (othS₄ s x) := by
    have hst : s₄ = othS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (othS₄ s x)
      (ContSeamC C) (contSeamMid C (othS₄ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (othS₄ s x) hl₄'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (by
    simpa only [Nat.reduceAdd] using hseg8))))

/-! #### `.defaultValueBracket`: `NodeBlock19 → NodeBlock11 → LeafBlock7`, four links -/

/-- The carry at `NodeBlock19`: the first pivot's bracket arm. -/
abbrev BrkAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock19" }

/-- The carry at `NodeBlock11`. -/
abbrev BrkAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BrkAC₁ C with block := "NodeBlock11" }

/-- The carry at `LeafBlock7`. -/
abbrev BrkAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BrkAC₂ C with block := "LeafBlock7" }

/-- The state `NodeBlock21` leaves on the bracket arm. -/
def brkS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- The state `NodeBlock19` leaves: `%8 < 123`, so `NodeBlock11`. -/
def brkS₂ (s : State) (x : BitVec 8) : State :=
  { (brkS₁ s x).bind "%Pivot20" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 123))) with
    pc := "NodeBlock11", pre := some (brkS₁ s x).pc }

/-- The state `NodeBlock11` leaves: `%8 < 93`, so `LeafBlock7`. -/
def brkS₃ (s : State) (x : BitVec 8) : State :=
  { (brkS₂ s x).bind "%Pivot12" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 93))) with
    pc := "LeafBlock7", pre := some (brkS₂ s x).pc }

/-- The state `LeafBlock7` leaves: the class's `sw.default.i`. -/
def brkS₄ (s : State) (x : BitVec 8) : State :=
  { (brkS₃ s x).bind "%SwitchLeaf8" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 91))) with
    pc := "sw.default.i", pre := some (brkS₃ s x).pc }

/-- **The `.defaultValueBracket` class's head chain to `if.else387.i`, at four plus
eight.**  `91 ≤ %8`, `%8 < 123`, `%8 < 93` and `%8 ≠ 91`: `NodeBlock19 → NodeBlock11 →
LeafBlock7 → sw.default.i`, then `contDefaultSeg`'s eight.  The byte `92` is the class. -/
theorem contBrkHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brkS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brkS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (brkS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (brkS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (brkS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (brkS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (brkS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (brkS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (brkS₄ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (brkS₄ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (brkS₄ s x) inc nep ep v ix b35 b8) 12 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock11" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 93) = 1 then
      "LeafBlock7" else "LeafBlock9") = "LeafBlock7" := by rw [h93]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 91) = 1 then
      "if.then.i" else "sw.default.i") = "sw.default.i" := by rw [hne91]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BrkAC₁ C) (brkS₁ s x) := by
    have hst : s₁ = brkS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock19`'s second pivot
  have h8₂ : evalOperand (brkS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BrkAC₁ C)
      (brkS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₁ C) (brkS₁ s x)
      (BrkAC₂ C) (brkS₂ s x) := by
    have hst : s₂ = brkS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. `NodeBlock11`'s third pivot
  have h8₃ : evalOperand (brkS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₂, brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock11_at (calls := stage2Calls stage2SubCalls) G (BrkAC₂ C)
      (brkS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₂ C) (brkS₂ s x)
      (BrkAC₃ C) (brkS₃ s x) := by
    have hst : s₃ = brkS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  have h8₄ : evalOperand (brkS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₃, brkS₂, brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock7_at (calls := stage2Calls stage2SubCalls) G (BrkAC₃ C)
      (brkS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₃ C) (brkS₃ s x)
      (HeadAC₄ C) (brkS₄ s x) := by
    have hst : s₄ = brkS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (brkS₄ s x)
      (ContSeamC C) (contSeamMid C (brkS₄ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (brkS₄ s x) hl₄'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (by
    simpa only [Nat.reduceAdd] using hseg8))))

/-! #### `.defaultValueBracketHigh`: `NodeBlock19 → NodeBlock11 → LeafBlock9`, four links -/

/-- The carry at `NodeBlock19`: the first pivot's bracket arm. -/
abbrev BhAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock19" }

/-- The carry at `NodeBlock11`. -/
abbrev BhAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BhAC₁ C with block := "NodeBlock11" }

/-- The carry at `LeafBlock9`. -/
abbrev BhAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BhAC₂ C with block := "LeafBlock9" }

/-- The state `NodeBlock21` leaves on the bracket arm. -/
def bhS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- The state `NodeBlock19` leaves: `%8 < 123`, so `NodeBlock11`. -/
def bhS₂ (s : State) (x : BitVec 8) : State :=
  { (bhS₁ s x).bind "%Pivot20" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 123))) with
    pc := "NodeBlock11", pre := some (bhS₁ s x).pc }

/-- The state `NodeBlock11` leaves: `93 ≤ %8`, so `LeafBlock9`. -/
def bhS₃ (s : State) (x : BitVec 8) : State :=
  { (bhS₂ s x).bind "%Pivot12" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 93))) with
    pc := "LeafBlock9", pre := some (bhS₂ s x).pc }

/-- The state `LeafBlock9` leaves: the class's `sw.default.i`. -/
def bhS₄ (s : State) (x : BitVec 8) : State :=
  { (bhS₃ s x).bind "%SwitchLeaf10" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 93))) with
    pc := "sw.default.i", pre := some (bhS₃ s x).pc }

/-- **The `.defaultValueBracketHigh` class's head chain to `if.else387.i`, at four plus
eight.**  `91 ≤ %8`, `%8 < 123`, `93 ≤ %8` and `%8 ≠ 93`: `NodeBlock19 → NodeBlock11 →
LeafBlock9 → sw.default.i`, then `contDefaultSeg`'s eight.  This is `'a'`'s class (the
bytes `94 … 109` of the letters arm), and it is the twelve links the letters route's
`97` takes. -/
theorem contBhHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (bhS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (bhS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (bhS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (bhS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (bhS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (bhS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (bhS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (bhS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (bhS₄ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (bhS₄ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (bhS₄ s x) inc nep ep v ix b35 b8) 12 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock11" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 93) = 1 then
      "LeafBlock7" else "LeafBlock9") = "LeafBlock9" := by rw [h93]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 93) = 1 then
      "if.then53.i" else "sw.default.i") = "sw.default.i" := by rw [hne93]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BhAC₁ C) (bhS₁ s x) := by
    have hst : s₁ = bhS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock19`'s second pivot
  have h8₂ : evalOperand (bhS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BhAC₁ C)
      (bhS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₁ C) (bhS₁ s x)
      (BhAC₂ C) (bhS₂ s x) := by
    have hst : s₂ = bhS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. `NodeBlock11`'s third pivot
  have h8₃ : evalOperand (bhS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₂, bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock11_at (calls := stage2Calls stage2SubCalls) G (BhAC₂ C)
      (bhS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₂ C) (bhS₂ s x)
      (BhAC₃ C) (bhS₃ s x) := by
    have hst : s₃ = bhS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  have h8₄ : evalOperand (bhS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₃, bhS₂, bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock9_at (calls := stage2Calls stage2SubCalls) G (BhAC₃ C)
      (bhS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₃ C) (bhS₃ s x)
      (HeadAC₄ C) (bhS₄ s x) := by
    have hst : s₄ = bhS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (bhS₄ s x)
      (ContSeamC C) (contSeamMid C (bhS₄ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (bhS₄ s x) hl₄'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (by
    simpa only [Nat.reduceAdd] using hseg8))))

/-! #### `.defaultValueBrace`: `NodeBlock19 → NodeBlock17 → LeafBlock13`, four links

The byte `124`: `91 ≤ %8`, `123 ≤ %8`, `%8 < 125` and `%8 ≠ 123`.  It is the sixth default
class, and the one class-C's byte range reaches without the bracket's route: `124`'s
class-C span is `LeafBlock58`'s else arm (as `117 … 125` is), but its head chain is
`NodeBlock19 → NodeBlock17 → LeafBlock13` and not `NodeBlock19 → NodeBlock11 →
LeafBlock9`.  Stating it completes the class-C selection at every byte of `[110, 125]`
that the letters arm does not take. -/

/-- The carry at `NodeBlock19`: the first pivot's high arm. -/
abbrev BrcAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock19" }

/-- The carry at `NodeBlock17`. -/
abbrev BrcAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BrcAC₁ C with block := "NodeBlock17" }

/-- The carry at `LeafBlock13`. -/
abbrev BrcAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { BrcAC₂ C with block := "LeafBlock13" }

/-- The state `NodeBlock21` leaves on the high arm: `91 ≤ %8`, so `NodeBlock19`. -/
def brcS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- The state `NodeBlock19` leaves: `123 ≤ %8`, so `NodeBlock17`. -/
def brcS₂ (s : State) (x : BitVec 8) : State :=
  { (brcS₁ s x).bind "%Pivot20" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 123))) with
    pc := "NodeBlock17", pre := some (brcS₁ s x).pc }

/-- The state `NodeBlock17` leaves: `%8 < 125`, so `LeafBlock13`. -/
def brcS₃ (s : State) (x : BitVec 8) : State :=
  { (brcS₂ s x).bind "%Pivot18" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 125))) with
    pc := "LeafBlock13", pre := some (brcS₂ s x).pc }

/-- The state `LeafBlock13` leaves: the class's `sw.default.i`. -/
def brcS₄ (s : State) (x : BitVec 8) : State :=
  { (brcS₃ s x).bind "%SwitchLeaf14" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 123))) with
    pc := "sw.default.i", pre := some (brcS₃ s x).pc }

/-- **The `.defaultValueBrace` class's head chain to `if.else387.i`, at four plus eight.**
`91 ≤ %8`, `123 ≤ %8`, `%8 < 125` and `%8 ≠ 123`: `NodeBlock19 → NodeBlock17 →
LeafBlock13 → sw.default.i`, then `contDefaultSeg`'s eight.  The byte `124` is the class,
and its twelve links are what `HcontArm.classC`'s `hHead` takes at it. -/
theorem contBrcHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brcS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brcS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (brcS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (brcS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (brcS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (brcS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (brcS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (brcS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35Mid C (brcS₄ s x) inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35Mid C (brcS₄ s x) inc nep ep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMid C (brcS₄ s x) inc nep ep v ix b35 b8) 12 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock13" := by rw [h125]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 123) = 1 then
      "if.then.i" else "sw.default.i") = "sw.default.i" := by rw [hne123]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BrcAC₁ C) (brcS₁ s x) := by
    have hst : s₁ = brcS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock19`'s second pivot
  have h8₂ : evalOperand (brcS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BrcAC₁ C)
      (brcS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₁ C) (brcS₁ s x)
      (BrcAC₂ C) (brcS₂ s x) := by
    have hst : s₂ = brcS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. `NodeBlock17`'s third pivot
  have h8₃ : evalOperand (brcS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₂, brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock17_at (calls := stage2Calls stage2SubCalls) G (BrcAC₂ C)
      (brcS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₂ C) (brcS₂ s x)
      (BrcAC₃ C) (brcS₃ s x) := by
    have hst : s₃ = brcS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  have h8₄ : evalOperand (brcS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₃, brcS₂, brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock13_at (calls := stage2Calls stage2SubCalls) G (BrcAC₃ C)
      (brcS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₃ C) (brcS₃ s x)
      (HeadAC₄ C) (brcS₄ s x) := by
    have hst : s₄ = brcS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- the suffix at the class's own state
  have hcarry : (HeadAC₄ C).block = "sw.default.i" := rfl
  have hseg8 : Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) (brcS₄ s x)
      (ContSeamC C) (contSeamMid C (brcS₄ s x) inc nep ep v ix b35 b8) 8 :=
    contDefaultSeg G C (brcS₄ s x) hl₄'.inv' hcarry hinc hnep hnext h5 hi63 hread hidx htok
      hgap hugt hread35 hb13 hb32 hbne13 hend h8end hbit
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄' (by
    simpa only [Nat.reduceAdd] using hseg8))))

/-! ### The default classes' prefixes, as counted chains of their own

Each class's pivots from `NodeBlock21` to its `sw.default.i`, cut out of the continuing
chain so the last entry's chain is the same prefix beside its own seven-link suffix.  The
count is the class's: three at `.defaultValueLow`, four at the other five. -/

/-- **Counted chains compose.**  The first chain's links and the second's, at the sum of
their counts. -/
theorem Seg.trans {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' C'' : WalkCarry G} {s s' s'' : State} {n m : Nat}
    (h₁ : Seg calls G C s C' s' n) (h₂ : Seg calls G C' s' C'' s'' m) :
    Seg calls G C s C'' s'' (n + m) := by
  revert h₂
  induction h₁ with
  | nil => intro h₂; simpa only [Nat.zero_add] using h₂
  | tail hl _ ih =>
      intro h₂
      simpa only [Nat.succ_add] using Seg.tail hl (ih h₂)

/-- **The `.defaultValueLow` class's prefix to `sw.default.i`, counted at three.**  `91 ≤ %8`
is false in the signed order, `%8 < 44` true and `%8 ≠ 34`: `NodeBlock5 → LeafBlock →
sw.default.i`.  The low bytes and every byte above `127` take this route. -/
theorem contLowToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (lowS₃ s x) 3 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "LeafBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .eq x (BitVec.ofNat 8 34) = 1 then
      "sw.bb202.i" else "sw.default.i") = "sw.default.i" := by rw [hne34]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (LowAC₁ C) (lowS₁ s x) := by
    have hst : s₁ = lowS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `NodeBlock5`'s second pivot
  have h8₂ : evalOperand (lowS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [lowS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (LowAC₁ C)
      (lowS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (LowAC₁ C) (lowS₁ s x)
      (LowAC₂ C) (lowS₂ s x) := by
    have hst : s₂ = lowS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the leaf's equality test
  have h8₃ : evalOperand (lowS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [lowS₂, lowS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock_at (calls := stage2Calls stage2SubCalls) G (LowAC₂ C)
      (lowS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (LowAC₂ C) (lowS₂ s x)
      (HeadAC₄ C) (lowS₃ s x) := by
    have hst : s₃ = lowS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.nil hl₃'.inv')))

/-- **The `.defaultValueMid` class's prefix to `sw.default.i`, counted at four.**  `%8 < 91`,
`44 ≤ %8`, `58 ≤ %8` and `%8 ≠ 58`: `NodeBlock5 → NodeBlock → LeafBlock3 → sw.default.i`. -/
theorem contMidToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (midS₄ s x) 4 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock3" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 58) = 1 then
      "if.then173.i" else "sw.default.i") = "sw.default.i" := by rw [hne58]; rfl
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (MidAC₁ C) (midS₁ s x) := by
    have hst : s₁ = midS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  have h8₂ : evalOperand (midS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (MidAC₁ C)
      (midS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₁ C) (midS₁ s x)
      (MidAC₂ C) (midS₂ s x) := by
    have hst : s₂ = midS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  have h8₃ : evalOperand (midS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₂, midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (MidAC₂ C)
      (midS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₂ C) (midS₂ s x)
      (MidAC₃ C) (midS₃ s x) := by
    have hst : s₃ = midS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  have h8₄ : evalOperand (midS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [midS₃, midS₂, midS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock3_at (calls := stage2Calls stage2SubCalls) G (MidAC₃ C)
      (midS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (MidAC₃ C) (midS₃ s x)
      (HeadAC₄ C) (midS₄ s x) := by
    have hst : s₄ = midS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.nil hl₄'.inv'))))

/-- **The `.otherValue` class's prefix to `sw.default.i`, counted at four.**  `%8 < 91`,
`44 ≤ %8`, `44 < %8 < 58` and `%8 ≠ 44`: `NodeBlock5 → NodeBlock → LeafBlock1 →
sw.default.i`.  The bytes `46`/`47` are the class. -/
theorem contOthToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (othS₄ s x) 4 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock5" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 44) = 1 then
      "LeafBlock" else "NodeBlock") = "NodeBlock" := by rw [h44]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 58) = 1 then
      "LeafBlock1" else "LeafBlock3") = "LeafBlock1" := by rw [h58]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 44) = 1 then
      "if.then127.i" else "sw.default.i") = "sw.default.i" := by rw [hne44]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (OthAC₁ C) (othS₁ s x) := by
    have hst : s₁ = othS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  have h8₂ : evalOperand (othS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (OthAC₁ C)
      (othS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₁ C) (othS₁ s x)
      (OthAC₂ C) (othS₂ s x) := by
    have hst : s₂ = othS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  have h8₃ : evalOperand (othS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₂, othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock_at (calls := stage2Calls stage2SubCalls) G (OthAC₂ C)
      (othS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₂ C) (othS₂ s x)
      (OthAC₃ C) (othS₃ s x) := by
    have hst : s₃ = othS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  have h8₄ : evalOperand (othS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [othS₃, othS₂, othS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock1_at (calls := stage2Calls stage2SubCalls) G (OthAC₃ C)
      (othS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (OthAC₃ C) (othS₃ s x)
      (HeadAC₄ C) (othS₄ s x) := by
    have hst : s₄ = othS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.nil hl₄'.inv'))))

/-- **The `.defaultValueBracket` class's prefix to `sw.default.i`, counted at four.**
`91 ≤ %8`, `91 < %8 < 123`, `%8 < 93` and `%8 ≠ 91`: `NodeBlock19 → NodeBlock11 →
LeafBlock7 → sw.default.i`.  The byte `92` is the class. -/
theorem contBrkToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (brkS₄ s x) 4 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock11" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 93) = 1 then
      "LeafBlock7" else "LeafBlock9") = "LeafBlock7" := by rw [h93]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 91) = 1 then
      "if.then.i" else "sw.default.i") = "sw.default.i" := by rw [hne91]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BrkAC₁ C) (brkS₁ s x) := by
    have hst : s₁ = brkS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  have h8₂ : evalOperand (brkS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BrkAC₁ C)
      (brkS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₁ C) (brkS₁ s x)
      (BrkAC₂ C) (brkS₂ s x) := by
    have hst : s₂ = brkS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  have h8₃ : evalOperand (brkS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₂, brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock11_at (calls := stage2Calls stage2SubCalls) G (BrkAC₂ C)
      (brkS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₂ C) (brkS₂ s x)
      (BrkAC₃ C) (brkS₃ s x) := by
    have hst : s₃ = brkS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  have h8₄ : evalOperand (brkS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brkS₃, brkS₂, brkS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock7_at (calls := stage2Calls stage2SubCalls) G (BrkAC₃ C)
      (brkS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BrkAC₃ C) (brkS₃ s x)
      (HeadAC₄ C) (brkS₄ s x) := by
    have hst : s₄ = brkS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.nil hl₄'.inv'))))

/-- **The `.defaultValueBracketHigh` class's prefix to `sw.default.i`, counted at four.**
`91 ≤ %8`, `%8 < 123`, `93 ≤ %8` and `%8 ≠ 93`: `NodeBlock19 → NodeBlock11 →
LeafBlock9 → sw.default.i`.  The bytes `94 … 109` are the class. -/
theorem contBhToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (bhS₄ s x) 4 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock11" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 93) = 1 then
      "LeafBlock7" else "LeafBlock9") = "LeafBlock9" := by rw [h93]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 93) = 1 then
      "if.then53.i" else "sw.default.i") = "sw.default.i" := by rw [hne93]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BhAC₁ C) (bhS₁ s x) := by
    have hst : s₁ = bhS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  have h8₂ : evalOperand (bhS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BhAC₁ C)
      (bhS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₁ C) (bhS₁ s x)
      (BhAC₂ C) (bhS₂ s x) := by
    have hst : s₂ = bhS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  have h8₃ : evalOperand (bhS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₂, bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock11_at (calls := stage2Calls stage2SubCalls) G (BhAC₂ C)
      (bhS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₂ C) (bhS₂ s x)
      (BhAC₃ C) (bhS₃ s x) := by
    have hst : s₃ = bhS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  have h8₄ : evalOperand (bhS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [bhS₃, bhS₂, bhS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot12") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock9_at (calls := stage2Calls stage2SubCalls) G (BhAC₃ C)
      (bhS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BhAC₃ C) (bhS₃ s x)
      (HeadAC₄ C) (bhS₄ s x) := by
    have hst : s₄ = bhS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.nil hl₄'.inv'))))

/-- **The `.defaultValueBrace` class's prefix to `sw.default.i`, counted at four.**  `91 ≤ %8`,
`123 ≤ %8`, `%8 < 125` and `%8 ≠ 123`: `NodeBlock19 → NodeBlock17 → LeafBlock13 →
sw.default.i`.  The byte `124` is the class. -/
theorem contBrcToDefault {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (brcS₄ s x) 4 := by
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [h91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by rw [h123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock13" := by rw [h125]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 123) = 1 then
      "if.then.i" else "sw.default.i") = "sw.default.i" := by rw [hne123]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (BrcAC₁ C) (brcS₁ s x) := by
    have hst : s₁ = brcS₁ s x := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  have h8₂ : evalOperand (brcS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (BrcAC₁ C)
      (brcS₁ s x) hl₁'.inv' rfl h8₂
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₁ C) (brcS₁ s x)
      (BrcAC₂ C) (brcS₂ s x) := by
    have hst : s₂ = brcS₂ s x := by rw [hs₂, hres₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  have h8₃ : evalOperand (brcS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₂, brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock17_at (calls := stage2Calls stage2SubCalls) G (BrcAC₂ C)
      (brcS₂ s x) hl₂'.inv' rfl h8₃
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₂ C) (brcS₂ s x)
      (BrcAC₃ C) (brcS₃ s x) := by
    have hst : s₃ = brcS₃ s x := by rw [hs₃, hres₃]; rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  have h8₄ : evalOperand (brcS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [brcS₃, brcS₂, brcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock13_at (calls := stage2Calls stage2SubCalls) G (BrcAC₃ C)
      (brcS₃ s x) hl₃'.inv' rfl h8₄
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (BrcAC₃ C) (brcS₃ s x)
      (HeadAC₄ C) (brcS₄ s x) := by
    have hst : s₄ = brcS₄ s x := by rw [hs₄, hres₄]; rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.nil hl₄'.inv'))))

/-! ### The last entry's suffix, counted at seven

The continuing suffix's twin at the *exhausted* count: `%inc.i ≥ %nep` is the arm
`sw.default.i` leaves on, so it reaches `cond.end349.i` directly and the count test's
succeeding arm (`cond.true345.i`) is not taken.  One link fewer than `contDefaultSeg`'s
eight: `sw.default.i`, the bound's `phi`, the whitespace check, the byte's three pivots
and the token's end.

The bound's `phi` selects `%4` on this edge (the default arm is the one the count test's
failure takes), so `%cond350.i` is the document's own width word rather than the next
entry's position, and the whitespace check's byte is read at `(G.b - 1) + v` for that
word `v`.  As in the continuing suffix, nothing in these seven blocks reads a cell the
head switch bound: the class's route enters as the state term.

The state names mirror `contMidS`/`contLandOut`/`contP35Mid`/`contSeamMid`, at the
failing arm and with `%4`'s word for the bound. -/

/-- `sw.default.i`'s target on the failing arm: the count test's cell, at
`cond.end349.i`. -/
def contSwFailOut (s : State) (inc nep : BitVec 64) : State :=
  { (s.bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep))) with
    pc := "cond.end349.i", pre := some s.pc }

/-- `cond.end349.i`'s target on the failing arm: the bound's `phi` selects `%4`, so the
bound is the document's width word and the token's two stores follow. -/
def contEndFailS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) : State :=
  condEnd349OutAt (contSwFailOut q inc nep) (BitVec.ofNat 64 v) ix C.stage.tok
    (C.stage.tok + 20)

/-- The byte's three pivots' target, at `if.end372.i`. -/
def contP35MidFail {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) : State :=
  contP35Out (contP39Out (contP41Out (contLandOut (G := G)
    (contEndFailS C q inc nep v ix) v b35) b35) b35) b35

/-- The suffix's endpoint: `if.end372.i`'s else arm, at the class-C span's entry. -/
def contSeamMidFail {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) (b8 : BitVec 8) : State :=
  seamS (contP35MidFail C q inc nep v ix b35) (BitVec.ofNat 64 v) b8 C.stage.tok

/-- `%4` at the count test's failing target is the state's own: only `%cmp343.i` is
bound there. -/
theorem contSwFailOut_env4 (s : State) (inc nep : BitVec 64) {v : Nat}
    (h : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v))) :
    lookupName (contSwFailOut s inc nep).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [contSwFailOut, State.bind,
    lookupName_cons_ne (k := "%cmp343.i") (n := "%4") _ _ (by decide)]
  exact h

/-- `%idxprom.i` at the same state. -/
theorem contSwFailOut_envIdx (s : State) (inc nep : BitVec 64) {ix : BitVec 64}
    (h : lookupName s.env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (contSwFailOut s inc nep).env "%idxprom.i" = some (.int 64 ix) := by
  simp only [contSwFailOut, State.bind,
    lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
  exact h

/-- `%t352.i` at the same state. -/
theorem contSwFailOut_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (inc nep : BitVec 64) (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (contSwFailOut s inc nep).env "%t352.i" = some (.ptr C.stage.tok) := by
  simp only [contSwFailOut, State.bind,
    lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
  exact h

/-- `%gap.i` at the same state. -/
theorem contSwFailOut_envGap {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (inc nep : BitVec 64)
    (h : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    lookupName (contSwFailOut s inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)) := by
  simp only [contSwFailOut, State.bind,
    lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
  exact h

/-- `%cond350.i` at the bound's target is `%4`'s word. -/
theorem contEndFailS_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) :
    lookupName (contEndFailS C q inc nep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [contEndFailS, condEnd349OutAt, cells]
  rw [lookupName_cons_ne (k := "%cmp355.i") (n := "%cond350.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the token's end is the bound `cond.end349.i` stored. -/
theorem contP35MidFail_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q : State)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contP35MidFail C q inc nep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [contP35MidFail, contP35Out, contP39Out, contP41Out, contLandOut, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndFailS_cond C q inc nep v ix

/-- **The last entry's seven links from `sw.default.i` to `if.else387.i`, at any state.**
The count test fails, so `cond.end349.i` follows directly; the bound's `phi` takes
`%4`'s word, the whitespace check loads the byte before it, and the byte's three pivots
take the empty body's entry to the token's end.  `q5` is the state at `sw.default.i` —
the class's prefix ends there — and `v`/`ix` are the width word and the entry's index. -/
theorem contDefLastSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (hInv : WalkInv G (HeadAC₄ C) q5) (hblock : (HeadAC₄ C).block = "sw.default.i")
    {inc nep : BitVec 64}
    (hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName q5.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName q5.env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName q5.env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName q5.env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C q5 inc nep v ix).mem ((G.b - 1) + v) 1 =
      some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C q5 inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C q5 inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5 (ContSeamC C)
      (contSeamMidFail C q5 inc nep v ix b35 b8) 7 := by
  -- 1. `sw.default.i`'s count test, on the failing arm
  have hres₁ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.end349.i" := by
    rw [hge]; rfl
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      hInv hblock hinc hnep
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5
      (HeadAC₅ C) (contSwFailOut q5 inc nep) := by
    have hst : s₁ = contSwFailOut q5 inc nep := by rw [hs₁, hres₁]; rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. `cond.end349.i`: the bound's `phi` takes `%4`, and the compare
  have hq5pc : q5.pc = "sw.default.i" := by rw [hInv.pc_eq, hblock]
  have hpre₂ : (contSwFailOut q5 inc nep).pre = some "sw.default.i" := by
    simp only [contSwFailOut, hq5pc]
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.cond_end349_i_at G (HeadAC₅ C) (contSwFailOut q5 inc nep) hl₁'.inv' rfl hpre₂
      (p := "sw.default.i") hlast_pre5 (contSwFailOut_env4 q5 inc nep h4)
      (contSwFailOut_envIdx q5 inc nep hidx) (contSwFailOut_envTok C q5 inc nep htok)
      (contSwFailOut_envGap C q5 inc nep hgap)
  have hres₂ : (if evalICmp .ugt (BitVec.ofNat 64 v) ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "land.lhs.true357.i" := by
    rw [hugt]; rfl
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₅ C)
      (contSwFailOut q5 inc nep) (HlastAC₁ C) (contEndFailS C q5 inc nep v ix) := by
    have hst : s₂ = contEndFailS C q5 inc nep v ix := by rw [hs₂]; rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the whitespace check: the byte before the width word
  have hig : lookupName (contEndFailS C q5 inc nep v ix).env "%invariant.gep" =
      some (.ptr (G.b - 1)) :=
    hl₂'.inv'.regs ("%invariant.gep", .ptr (G.b - 1)) (by simp [walkStaticRegs])
  have hcond : lookupName (contEndFailS C q5 inc nep v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := contEndFailS_cond C q5 inc nep v ix
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.land_lhs_true357_i_at G (HlastAC₁ C) (contEndFailS C q5 inc nep v ix)
      hl₂'.inv' rfl (ig := G.b - 1) (q := v) (b := b35) hig hcond hv63 hread35
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₁ C)
      (contEndFailS C q5 inc nep v ix) (HlastAC₂ C)
      (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) := by
    rw [hs₃] at hl₃
    exact hl₃
  -- 4. the byte's first pivot
  have h35a : evalOperand (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35)
      (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandOut_35 (s := contEndFailS C q5 inc nep v ix) v b35
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.NodeBlock41_at (calls := stage2Calls stage2SubCalls) G (HlastAC₂ C)
      (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) hl₃'.inv' rfl h35a
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₂ C)
      (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) (HlastAC₃ C)
      (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "LeafBlock33" else "NodeBlock39") = "NodeBlock39" := by rw [hb13]; rfl
    have hst : s₄ = contP41Out
        (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35 := by
      rw [hs₄, harm]; rfl
    rw [hst] at hl₄
    rw [harm] at hl₄
    exact hl₄
  -- 5. the byte's second pivot
  have h35b : evalOperand
      (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35)
      (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP41Out_35 (s := contEndFailS C q5 inc nep v ix) v b35
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.NodeBlock39_at (calls := stage2Calls stage2SubCalls) G (HlastAC₃ C)
      (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35)
      hl₄'.inv' rfl h35b
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₃ C)
      (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35)
      (HlastAC₄ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35)
        b35) b35) := by
    have harm : (if evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 then
        "LeafBlock35" else "LeafBlock37") = "LeafBlock35" := by rw [hb32]; rfl
    have hst : s₅ = contP39Out
        (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35) b35) b35 := by
      rw [hs₅, harm]; rfl
    rw [hst] at hl₅
    rw [harm] at hl₅
    exact hl₅
  -- 6. the leaf's equality test
  have h35c : evalOperand
      (contP39Out (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35)
        b35) b35) (.reg "%35") = some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contP39Out_35 (s := contEndFailS C q5 inc nep v ix) v b35
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.LeafBlock35_at (calls := stage2Calls stage2SubCalls) G (HlastAC₄ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35)
        b35) b35) hl₅'.inv' rfl h35c
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (HlastAC₄ C)
      (contP39Out (contP41Out (contLandOut (G := G) (contEndFailS C q5 inc nep v ix) v b35)
        b35) b35) (HeadAC₆ C) (contP35MidFail C q5 inc nep v ix b35) := by
    have harm : (if evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1 then
        "land.rhs.i.preheader" else "if.end372.i") = "if.end372.i" := by rw [hbne13]; rfl
    have hst : s₆ = contP35MidFail C q5 inc nep v ix b35 := by
      rw [hs₆, harm]
      rfl
    rw [hst] at hl₆
    rw [harm] at hl₆
    exact hl₆
  -- 7. the token's end
  have hcond35 : evalOperand (contP35MidFail C q5 inc nep v ix b35) (.reg "%cond350.i") =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    simp only [evalOperand]
    exact contP35MidFail_cond C q5 inc nep v ix b35
  obtain ⟨s₇, hl₇, hs₇⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := HeadAC₆ C)
      (s := contP35MidFail C q5 inc nep v ix b35) hl₆'.inv' rfl (p := "LeafBlock35") rfl
      contPhiSeam hcond35 hend h8end hbit
  have hl₇' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₆ C)
      (contP35MidFail C q5 inc nep v ix b35) (ContSeamC C)
      (contSeamMidFail C q5 inc nep v ix b35 b8) := by
    rw [hs₇] at hl₇
    exact hl₇
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃' (Seg.tail hl₄'
    (Seg.tail hl₅' (Seg.tail hl₆' (Seg.tail hl₇'
      (Seg.nil hl₇'.inv')))))))

/-! ### The last entry's chains, per head-switch class

Each is the class's prefix beside `contDefLastSeg`'s seven links, so the count is the
continuing chain's less the count test's succeeding arm: **ten** at `.defaultValueLow` and
**eleven** at the other five classes.  The arm's count is the class's (`nH ≤ 11`), which is
what `LastEntryArm.letters`/`.fLetter`/`.classC` take.

The hypotheses are the class's own: its pivot bits, the two count words at
`sw.default.i`, `%4`'s word for the bound, the entry's index, the token's cells, the byte
before the width word with its three class bits, and the seam's byte. -/

/-- **The last entry's `.defaultValueLow` chain to `if.else387.i`, at three plus seven.** -/
theorem contLastLowHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (lowS₃ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (lowS₃ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (lowS₃ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (lowS₃ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (lowS₃ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (lowS₃ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (lowS₃ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (lowS₃ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (lowS₃ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (lowS₃ s x) inc nep v ix b35 b8) 10 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (lowS₃ s x) 3 :=
    contLowToDefault G C s hInv hblock h8 h91 h44 hne34
  exact hpref.trans
    (contDefLastSeg G C (lowS₃ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-- **The last entry's `.defaultValueMid` chain to `if.else387.i`, at four plus seven.** -/
theorem contLastMidHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (midS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (midS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (midS₄ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (midS₄ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (midS₄ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (midS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (midS₄ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (midS₄ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (midS₄ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (midS₄ s x) inc nep v ix b35 b8) 11 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (midS₄ s x) 4 :=
    contMidToDefault G C s hInv hblock h8 h91 h44 h58 hne58
  exact hpref.trans
    (contDefLastSeg G C (midS₄ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-- **The last entry's `.otherValue` chain to `if.else387.i`, at four plus seven.** -/
theorem contLastOthHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (othS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (othS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (othS₄ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (othS₄ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (othS₄ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (othS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (othS₄ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (othS₄ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (othS₄ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (othS₄ s x) inc nep v ix b35 b8) 11 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (othS₄ s x) 4 :=
    contOthToDefault G C s hInv hblock h8 h91 h44 h58 hne44
  exact hpref.trans
    (contDefLastSeg G C (othS₄ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-- **The last entry's `.defaultValueBracket` chain to `if.else387.i`, at four plus
seven.** -/
theorem contLastBrkHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brkS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brkS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (brkS₄ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (brkS₄ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (brkS₄ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (brkS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (brkS₄ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (brkS₄ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (brkS₄ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (brkS₄ s x) inc nep v ix b35 b8) 11 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (brkS₄ s x) 4 :=
    contBrkToDefault G C s hInv hblock h8 h91 h123 h93 hne91
  exact hpref.trans
    (contDefLastSeg G C (brkS₄ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-- **The last entry's `.defaultValueBracketHigh` chain to `if.else387.i`, at four plus
seven.** -/
theorem contLastBhHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (bhS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (bhS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (bhS₄ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (bhS₄ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (bhS₄ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (bhS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (bhS₄ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (bhS₄ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (bhS₄ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (bhS₄ s x) inc nep v ix b35 b8) 11 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (bhS₄ s x) 4 :=
    contBhToDefault G C s hInv hblock h8 h91 h123 h93 hne93
  exact hpref.trans
    (contDefLastSeg G C (bhS₄ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-- **The last entry's `.defaultValueBrace` chain to `if.else387.i`, at four plus
seven.**  The byte `124`'s class. -/
theorem contLastBrcHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brcS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brcS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    {v : Nat} (h4 : lookupName (brcS₄ s x).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidx : lookupName (brcS₄ s x).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (brcS₄ s x).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (brcS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndFailS C (brcS₄ s x) inc nep v ix).mem
      ((G.b - 1) + v) 1 = some [b35])
    (hv63 : v < 2 ^ 63)
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    {b8 : BitVec 8}
    (hend : lookupName (contP35MidFail C (brcS₄ s x) inc nep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (contP35MidFail C (brcS₄ s x) inc nep v ix b35).env "%8" =
      some (.int 8 b8))
    (hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) :
    Seg (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamMidFail C (brcS₄ s x) inc nep v ix b35 b8) 11 := by
  have hpref : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) (brcS₄ s x) 4 :=
    contBrcToDefault G C s hInv hblock h8 h91 h123 h125 hne123
  exact hpref.trans
    (contDefLastSeg G C (brcS₄ s x) (Seg.measure hpref).inv' rfl hinc hnep hge h4 hidx
      htok hgap hugt hread35 hv63 hb13 hb32 hbne13 hend h8end hbit)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contDefaultSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLowHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contMidHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contOthHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBrkHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBhHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contSwToLandSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBrcHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.Seg.trans
#print axioms LeanLLVM.Refinement.WalkScope.contLowToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contMidToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contOthToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contBrkToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contBhToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contBrcToDefault
#print axioms LeanLLVM.Refinement.WalkScope.contDefLastSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastLowHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastMidHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastOthHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastBrkHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastBhHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.contLastBrcHeadSeg

end WalkScope
end LeanLLVM.Refinement
