/-
# The last entry's payload, at the fields its own rows produce

`HlastPayload` (`JsonStage2WalkDispatchSupply:1008`) is `HlastLane` beside `HlastAbi`.
This module produces every field of that payload the tree's own lemmas reach, and records
the ones it does not, with the premise each still needs.  Nothing here weakens a field's
type: the structures are the ones the supply module states.

## Produced

| field | producer |
|---|---|
| `HlastLane.tail`'s `hb` | `HcontByteRoute_of_not_wsStop`: the document's last byte has a route **exactly when it is not one of the four whitespace bytes**.  `hlastLane_of_not_wsStop` is the group at that premise. |
| `HlastAbi.openCall` | `hlastAbi_openCall`: the root slot's word is `walkReadBytes_rootSlot_word`, the precondition is `s2ValuePosPre_of_inv` (the stack bytes are `WalkInv.tyBytes`/`stBytes` at `C.sp - 1`), and the answer is `s2ValuePos_answers` at that precondition. |
| `HlastHighByteAbi.hreadT` | `hlastTailRoute_rootSlot_word`: `hlastTail_rootSlot_word` at the class's kind literal `0`, transported to the routed tail by `hlastTailByte_mem`. |
| `HlastHighByteAbi.hzread` | `hlastTailRoute_logBase`: `WalkInv.log_base` carried across the tail's four token-record stores (`token_log_sep`). |
| `HlastHighByteAbi.hev64` | `WalkGeom.evLt`, the staging's own clause — no lemma needed. |
| `HlastHighByteAbi.hcall₁`/`hret₁` | follow from the tail's `s2ValuePosPre` (`s2ValuePos_answers`, `s2ValuePos_reply`): the answer is the model's bit and `xA` is that bit's word.  The precondition at the routed memory is not produced here (see below), and the group is empty at any state, so no structure is assembled from these rows. |

## Not produced, and why

* **`HlastLane.tail` at a variable geometry.**  The field's guard is on the *entry's*
  first byte (`hlastByte G C`); the route it must build is the *document's last* byte's
  (`G.bs.getD (G.n - 1) 0`).  A document ending in `9`, `10`, `13` or `32` has no route at
  all (`HcontByteRoute_not_wsByte`, `HlastTailLane_not_of_wsByte`), and nothing in
  `WalkGeom` or `WalkInv` excludes it: `HlastArmRows.run`'s guard (`wsStop G (G.n - 1)`,
  `JsonStage2WalkDispatchLastRows`) is the run class at exactly that byte, and no clause
  excludes a head state with the high-byte bits (`%8 ∈ {126, 127}`) from being the last
  entry's on such a document.  The group's producer therefore needs one of two things the
  tree does not have: a premise on the geometry (`¬ wsStop G (G.n - 1)`), or an exclusion
  of the high-byte class where the last byte is whitespace.  `hlastLane_of_not_wsStop` is the first.
* **`HlastHighByteAbi.hbit0T`.**  It requires the value-position call's answer to be
  nonzero (`xA ≠ 0`), and no clause supplies that: `hlastHighByteAbi_answer_ne_zero` shows
  that the residue *forces* a nonzero answer, and `stage2ValuePos_some_zero` shows the
  model answering `0` (an object's colon state, say).  So the structure is empty at every
  state whose value-position call answers `0`; its producer needs the answer's bit as a
  guard (the emitting arm's), which the structure does not state.
* **`HlastHighByteAbi` itself, on its own class.**  `hlastHighByteAbi_empty` proves the
  structure has **no inhabitant at all**: its `hret₂` asks the scalar call for the emit bit
  `1`, and the class's own route supplies the kind word `0` (`hlastTailRoute_kindWord` —
  `if.then413.i`'s `%.sink372` incoming from `if.else405.i`), at which
  `od_scalar_value` answers `0` (`s2ScalarValue_kind_zero`).  This is a statement-level
  defect, not a missing premise: the residue describes the emitting tail, while `%8 ∈
  {126, 127}` reaches `if.else405.i` and the error path at `if.then432.i`, not
  `if.then447.i` and the copy call.  The class's real arm is a refusal, and
  `LastEntryArm` has none for it, so the payload's `abi.highByte` and the arm behind it
  cannot be produced by any premise.  `hlastResidue_empty` is the same refutation at the
  structure the arm actually carries (`HlastResidue`: `HlastResidue.toAbi` forgets the
  class bits), so `LastEntryArm.highByte` has no inhabitant either.
* **`HlastHighByteAbi.hpre₁`.**  Derivable from `WalkInv` (`WalkStackBytes.at` at
  `%ctype.i`/`%cst.i`), but not by any existing declaration: it needs a `s2ValuePosPre`
  transport across the tail's token-record stores, which is the `s2ValuePosPre_of_inv`
  shape at `hlastTailRoute`'s memory.
* **`HlastHighByteAbi.hpre₂`, `hpre₃`** (and the calls they answer).  These are the seam's
  groups at the last entry's tail: `HcontSeamAbi.last` / `hcontSeamCallsAt` at
  `hlastTailByte`, whose producer is `JsonStage2WalkDispatchSeamCalls`.  Their words are
  the staging's (`%c`, `%c + 1112`, `%t352.i`, the log's three words and the window read),
  not `WalkInv`'s.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The last byte's route

`HcontByteRoute` is inhabited exactly at the bytes that are not whitespace: the class's
three constructors are the three pivots' non-stop arms, and `wsStop` is their negation at
the same three bits.  So the route is read off a geometry's byte, not supplied.
-/

/-- **Every byte that is not a whitespace stop carries a route.**  `wsStop` is the three
leaves' stop arms; excluding it leaves the low leaf, the scan-free class, or the high leaf
at `wsX`, which is `head35` at the geometry's own byte. -/
def HcontByteRoute_of_not_wsStop {m0 : Mem} (G : WalkGeom m0) (q : Nat)
    (h : ¬ wsStop G q) : HcontByteRoute (wsX G q) := by
  unfold wsStop at h
  by_cases h13 : evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 1
  · by_cases hns : evalICmp .ule (wsX G q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
    · exact absurd (Or.inl ⟨h13, hns⟩) h
    · exact .lowLeaf h13 (bitZeroOfNeOne hns)
  · have h13' : evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 0 := bitZeroOfNeOne h13
    by_cases h32 : evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 1
    · by_cases he13 : evalICmp .eq (wsX G q) (BitVec.ofNat 8 13) = 1
      · exact absurd (Or.inr (Or.inl ⟨h13', h32, he13⟩)) h
      · exact .scanFree h13' h32 (bitZeroOfNeOne he13)
    · have h32' : evalICmp .slt (wsX G q) (BitVec.ofNat 8 32) = 0 := bitZeroOfNeOne h32
      by_cases he32 : evalICmp .eq (wsX G q) (BitVec.ofNat 8 32) = 1
      · exact absurd (Or.inr (Or.inr ⟨h13', h32', he32⟩)) h
      · exact .highLeaf h13' h32' (bitZeroOfNeOne he32)

/-- The scan-free class's bits exclude the four whitespace bytes. -/
theorem scanFree_not_wsByte : ∀ b : BitVec 8,
    evalICmp .slt b (BitVec.ofNat 8 13) = 0 →
    evalICmp .slt b (BitVec.ofNat 8 32) = 1 →
    evalICmp .eq b (BitVec.ofNat 8 13) = 0 →
    ¬ (b = BitVec.ofNat 8 9 ∨ b = BitVec.ofNat 8 10 ∨
       b = BitVec.ofNat 8 13 ∨ b = BitVec.ofNat 8 32) := by
  decide

/-- The low leaf's bits exclude the four whitespace bytes. -/
theorem lowLeaf_not_wsByte : ∀ b : BitVec 8,
    evalICmp .slt b (BitVec.ofNat 8 13) = 1 →
    evalICmp .ule (b + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0 →
    ¬ (b = BitVec.ofNat 8 9 ∨ b = BitVec.ofNat 8 10 ∨
       b = BitVec.ofNat 8 13 ∨ b = BitVec.ofNat 8 32) := by
  decide

/-- The high leaf's bits exclude the four whitespace bytes. -/
theorem highLeaf_not_wsByte : ∀ b : BitVec 8,
    evalICmp .slt b (BitVec.ofNat 8 13) = 0 →
    evalICmp .slt b (BitVec.ofNat 8 32) = 0 →
    evalICmp .eq b (BitVec.ofNat 8 32) = 0 →
    ¬ (b = BitVec.ofNat 8 9 ∨ b = BitVec.ofNat 8 10 ∨
       b = BitVec.ofNat 8 13 ∨ b = BitVec.ofNat 8 32) := by
  decide

/-- **A whitespace byte has no route**, so the route class is a total function of the
byte with exactly the four whitespace bytes undefined. -/
theorem HcontByteRoute_not_wsByte {b : BitVec 8} (hb : HcontByteRoute b)
    (h : b = BitVec.ofNat 8 9 ∨ b = BitVec.ofNat 8 10 ∨
         b = BitVec.ofNat 8 13 ∨ b = BitVec.ofNat 8 32) : False := by
  cases hb with
  | scanFree h1 h2 h3 => exact scanFree_not_wsByte b h1 h2 h3 h
  | lowLeaf h1 h2 => exact lowLeaf_not_wsByte b h1 h2 h
  | highLeaf h1 h2 h3 => exact highLeaf_not_wsByte b h1 h2 h3 h

/-- **The document's last byte's route, from the geometry.**  The route's byte is `wsX` at
`G.n - 1`, which is `head35` at the document's last byte. -/
def HcontByteRoute_lastByte_of_not_wsStop {m0 : Mem} (G : WalkGeom m0)
    (h : ¬ wsStop G (G.n - 1)) :
    HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0)) :=
  HcontByteRoute_of_not_wsStop G (G.n - 1) h

/-! ### The lane group -/

/-- **The last byte's lane**, at the route the geometry's last byte carries. -/
def hlastTailLane_of_route {m0 : Mem} (G : WalkGeom m0)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) : HlastTailLane G :=
  ⟨hb⟩

/-- **The lane group**, at a geometry whose last byte is not whitespace. -/
def hlastLane_of_not_wsStop {m0 : Mem} (G : WalkGeom m0) (h : ¬ wsStop G (G.n - 1)) :
    HlastLane G :=
  ⟨fun _ _ _ _ _ _ _ => hlastTailLane_of_route G (HcontByteRoute_lastByte_of_not_wsStop G h)⟩

/-- **The lane group is empty when the document's last byte is whitespace.**  The field's
guard (`¬ (C.k + 1 < G.nep)` and the two high-byte bits) is on the entry's first byte and
says nothing about the byte the route names, so this is a document-side obstruction, not a
state-side one: `HlastLane` has no inhabitant at such a geometry's route field. -/
theorem HlastTailLane_not_of_wsByte {m0 : Mem} (G : WalkGeom m0)
    (h : G.bs.getD (G.n - 1) 0 = 9 ∨ G.bs.getD (G.n - 1) 0 = 10 ∨
         G.bs.getD (G.n - 1) 0 = 13 ∨ G.bs.getD (G.n - 1) 0 = 32) :
    ¬ Nonempty (HlastTailLane G) := by
  rintro ⟨r⟩
  refine HcontByteRoute_not_wsByte r.hb ?_
  rcases h with h | h | h | h
  · exact Or.inl (by rw [h]; rfl)
  · exact Or.inr (Or.inl (by rw [h]; rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [h]; rfl)))
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; rfl)))

/-! ### The opener's call, from the invariant

`s2ValuePosPre` asks only that the two container stacks hold the byte at `%sp - 1`, or that
the depth is zero.  That is `WalkInv.tyBytes`/`stBytes` at the carried mark, so the
precondition is a theorem; the answer is the contract's (`s2ValuePos_answers`), and the
root slot's word is its own witness.
-/

/-- **`s2_value_pos`'s staging at an invariant state.** -/
theorem s2ValuePosPre_of_inv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (rd : BitVec 32) :
    s2ValuePosPre [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next := by
  unfold s2ValuePosPre
  refine ⟨BitVec.ofNat 32 C.sp, rd, C.stage.ctype, C.stage.cst, rfl, ?_⟩
  have hcap : C.sp ≤ stage2StackExtent := hInv.depth_cap
  have hto : (BitVec.ofNat 32 C.sp).toNat = C.sp :=
    walkToNat_ofNat32 (by simp only [stage2StackExtent] at hcap; omega)
  rw [hto]
  by_cases h0 : C.sp = 0
  · exact Or.inl h0
  · have hlt : C.sp - 1 < C.wlen := by have := hInv.sp_le_wlen; omega
    exact Or.inr
      ⟨⟨_, WalkStackBytes.at hInv.tyBytes hlt⟩, ⟨_, WalkStackBytes.at hInv.stBytes hlt⟩⟩

/-- **The openers' call row at an invariant state.**  Every field is produced: the read by
`walkReadBytes_rootSlot_word`, the precondition by `s2ValuePosPre_of_inv`, and the call by
`s2ValuePos_answers`. -/
noncomputable def hcontOpenCall_of_inv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) : HcontOpenCall G C s := by
  classical
  let rdv : BitVec 32 := Classical.choose (walkReadBytes_rootSlot_word hInv)
  have hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) :=
    Classical.choose_spec (walkReadBytes_rootSlot_word hInv)
  have hpre : s2ValuePosPre [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next := s2ValuePosPre_of_inv hInv rdv
  let r : CallOutcome := Classical.choose (s2ValuePos_answers hpre)
  have hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
      s.mem s.next = some r := Classical.choose_spec (s2ValuePos_answers hpre)
  exact ⟨rdv, hread, hpre, r, hcall⟩

/-- **`HlastAbi`'s opener group, produced.**  The field is a function of the invariant at a
last entry with no entry left; nothing else is needed. -/
noncomputable def hlastAbi_openCall {m0 : Mem} (G : WalkGeom m0) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      ¬ (C.k + 1 < G.nep) → HcontOpenCall G C s :=
  fun _ _ hInv _ _ => hcontOpenCall_of_inv hInv

/-! ### The high-byte class's reads

The routed tail's memory is the plain tail's: the byte's route binds comparison cells and
the seam's stores are the same three.  So the root slot's word and the log's base word are
the plain tail's, and both are theorems.
-/

/-- **The route changes cells, not memory.** -/
theorem hlastTailByte_mem {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    (hlastTailByte C s x inc nep v ix b35 hb).mem =
      (hlastTail C s x inc nep v ix b35).mem := by
  cases hb <;> rfl

/-- **The log's base word at the last entry's tail.**  `WalkInv.log_base` at `%z`, carried
across the token record's four stores (`token_log_sep` at the staged extents). -/
theorem hlastTail_logBase {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hInv : WalkInv G C s) :
    readBytes (writeBytes (hlastTail C s x inc nep v ix b35).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev) := by
  have hsep := token_log_sep (G := G) (C := C)
  have htap : stage2TokenExtent = 24 := rfl
  have hlog : stage2LogExtent = 64 := rfl
  rw [htap, hlog] at hsep
  have h4 : (natToBytes ((0 : BitVec 32)).toNat 4).length = 4 := natToBytes_length _ _
  have h8 : (natToBytes ix.toNat 8).length = 8 := natToBytes_length _ _
  have h8v : (natToBytes (BitVec.ofNat 64 v).toNat 8).length = 8 := natToBytes_length _ _
  have h4g : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length _ _
  have hmem : (hlastTail C s x inc nep v ix b35).mem =
      writeBytes
        (writeBytes
          (writeBytes s.mem C.stage.tok (natToBytes ix.toNat 8))
          (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4))
        (C.stage.tok + 8) (natToBytes (BitVec.ofNat 64 v).toNat 8) := by
    simp only [hlastTail, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, hlastSeam, seamS,
      seamFin, hlastP35, hlastP39, hlastP41, hlastLand, headEndS, condEnd349OutAt, headAS₅,
      headAS₄, headAS₃, headAS₂, headAS₁, stateAt, State.bind, cells]
  rw [hmem]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
    (v := natToBytes ((0 : BitVec 32)).toNat 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 8)
    (v := natToBytes (BitVec.ofNat 64 v).toNat 8)
    (by rw [h8v]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by rw [h4g]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8]; rcases hsep with h | h <;> omega)]
  exact hInv.log_base

/-- **The log's base word at the byte route's tail**: `hlastTail_logBase` transported to the
routed tail, whose memory is the plain tail's. -/
theorem hlastTailRoute_logBase {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) :
    readBytes (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev) := by
  have hmem := hlastTailByte_mem C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.n
    (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0) hb
  rw [hmem]
  exact hlastTail_logBase C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.n
    (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0) hInv

/-- **The root slot's word at the byte route's tail**: `hlastTail_rootSlot_word` at the
class's kind literal `0`, transported to the routed tail. -/
theorem hlastTailRoute_rootSlot_word {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) :
    ∃ rdv : BitVec 32,
      readBytes (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4)) (G.next0 + 8) 4 =
        some (natToBytes rdv.toNat 4) := by
  obtain ⟨rdv, hread⟩ := hlastTail_rootSlot_word C s (hlastByte G C) (hlastIncV C)
    (hlastNepV G) G.n (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0) 0 hInv
  refine ⟨rdv, ?_⟩
  have hmem := hlastTailByte_mem C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.n
    (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0) hb
  rw [hmem]
  exact hread

/-! ### The high-byte class's answer bit

`HlastHighByteAbi` states `hbit0T : xA ≠ 0`, i.e. that the value-position call answered a
nonzero bit.  That is the emitting arm's selector, not a consequence: the model answers
`0` at a non-value position (`stage2ValuePos_some_zero`), so the structure has no
inhabitant at such a state.  This pair is the record of that, not a repair.
-/

/-- **The residue forces a nonzero answer.**  Its `hcall₁` and `hret₁` name the reply's
word, and `hbit0T` says it is not `0`; so the model's answer at the structure's own word is
not `some 0`. -/
theorem hlastHighByteAbi_answer_ne_zero {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0)))
    (h : HlastHighByteAbi G C s hb) :
    stage2ValuePos
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4))
      ((BitVec.ofNat 32 (TailStartC C).sp).toNat) h.rdv.toNat
      (TailStartC C).stage.ctype (TailStartC C).stage.cst ≠ some 0 := by
  intro h0
  have hcall := h.hcall₁
  rw [s2ValuePos_reply, h0] at hcall
  have hr₁ := Option.some.inj hcall
  have hxA : h.xA = BitVec.ofNat 32 0 := by
    have hh := h.hret₁
    rw [← hr₁] at hh
    simpa using hh.symm
  have hbit := h.hbit0T
  rw [hxA] at hbit
  exact absurd hbit (by decide)

/-- **The model answers `0` at a non-value position.**  A depth-one state inside an object
after its colon (type byte `1`, state byte `1`) is not a value position, and an empty
memory with those two bytes staged is a memory the call can be made in. -/
theorem stage2ValuePos_some_zero :
    ∃ mem : Mem, stage2ValuePos mem 1 0 0 5 = some 0 :=
  ⟨[(0, 1), (5, 1)], by decide⟩

/-! ### The scalar call's kind at the byte route's tail

`if.then413.i` stores the `%.sink372` `phi` at `%kind404.i` before it calls
`s2_value_pos`, and the byte route's tail is the state that block is entered at from
`if.else405.i` (`HeadS413`'s `pre`), whose incoming is the literal `0`.  So the word
`od_scalar_value` reads is `0`, the model's kind-zero arm answers `0`, and
`HlastHighByteAbi`'s `hret₂ = 1` has no inhabitant — the structure is empty on the
class it is stated for, and so is the arm that carries it.
-/

/-- **The kind word at the byte route's tail is `0`.**  The `if.then413.i` store wrote
`%.sink372`, whose `if.else405.i` incoming is `0`; the route's span enters the block from
that incoming. -/
theorem hlastTailRoute_kindWord {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) :
    stage2ReadWord (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (C.stage.tok + 16) 4 = some 0 := by
  unfold stage2ReadWord
  have h := readBytes_writeBytes_same (hlastTailRoute C s hb).mem
    (natToBytes ((0 : BitVec 32)).toNat 4) (addr := C.stage.tok + 16)
  rw [show (natToBytes ((0 : BitVec 32)).toNat 4).length = 4 from natToBytes_length _ _] at h
  rw [h]
  show some (bytesToNat (natToBytes ((0 : BitVec 32)).toNat 4)) = some 0
  rw [show bytesToNat (natToBytes ((0 : BitVec 32)).toNat 4) = 0 by decide]

/-- **`od_scalar_value` at a kind-zero token answers `0`**: the model's first arm, which
sets the error message and returns the refusal bit. -/
theorem s2ScalarValue_kind_zero {mem : Mem} {c t o next base e pos endp : Nat}
    (hb : stage2ReadWord mem c 8 = some base)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hp : stage2ReadWord mem t 8 = some pos)
    (hend : stage2ReadWord mem (t + 8) 8 = some endp)
    (hk : stage2ReadWord mem (t + 16) 4 = some 0) :
    ∃ m : Mem, stage2Calls stage2SubCalls "od_scalar_value" [.ptr c, .ptr t, .ptr o] mem next
      = some ⟨.int 32 (BitVec.ofNat 32 0), m, next⟩ := by
  rw [stage2Calls_od_scalar_value]
  unfold stage2ScalarValueCall stage2ScalarValue
  simp only [hb, he, hp, hend, hk, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **`HlastHighByteAbi` is empty on its own class.**  The structure's `hret₂` asks the
scalar call for the emit bit `1`, and the class's own route supplies the kind word `0`, at
which the model answers `0`. -/
theorem hlastHighByteAbi_empty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) :
    ¬ Nonempty (HlastHighByteAbi G C s hb) := by
  rintro ⟨r₁, r₂, r₃, rdv, xA, -, hpre₁, hcall₁, -, -, -, hpre₂, hcall₂, hret₂, -,
    -, -⟩
  -- the value-position reply fixes the scalar call's memory
  have hcall₁' := hcall₁
  rw [s2ValuePos_reply] at hcall₁'
  cases hv : stage2ValuePos
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4))
      ((BitVec.ofNat 32 (TailStartC C).sp).toNat) rdv.toNat
      (TailStartC C).stage.ctype (TailStartC C).stage.cst with
  | none =>
      rw [hv] at hcall₁'
      cases hcall₁'
  | some v =>
      rw [hv] at hcall₁'
      rw [Option.map_some] at hcall₁'
      have hr₁ : r₁ = (⟨.int 32 (BitVec.ofNat 32 v),
          (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
            (natToBytes ((0 : BitVec 32)).toNat 4)),
          (hlastTailRoute C s hb).next⟩ : CallOutcome) := Option.some.inj hcall₁'.symm
      rw [hr₁] at hpre₂ hcall₂
      -- the scalar precondition's five reads, at the same memory
      obtain ⟨c, t, o, hargs, base, e, pos, endp, kind, buf, len, cap, win,
        hbase, he, hpos, hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre₂
      simp only [List.cons.injEq, Value.ptr.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      -- ... whose kind word is the store's `0`
      have hk0 : kind = 0 := by
        have hk' : stage2ReadWord
            (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
              (natToBytes ((0 : BitVec 32)).toNat 4))
            ((TailCarry₂ (TailStartC C)).stage.tok + 16) 4 = some 0 :=
          hlastTailRoute_kindWord hb
        rw [hkind] at hk'
        exact Option.some.inj hk'
      rw [hk0] at hkind
      obtain ⟨m, hm⟩ := s2ScalarValue_kind_zero (mem :=
          writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
            (natToBytes ((0 : BitVec 32)).toNat 4))
        (c := (TailCarry₂ (TailStartC C)).stage.c)
        (t := (TailCarry₂ (TailStartC C)).stage.tok)
        (o := (TailCarry₂ (TailStartC C)).stage.z)
        (next := (hlastTailRoute C s hb).next) hbase he hpos hend hkind
      rw [hm] at hcall₂
      have hr₂ := Option.some.inj hcall₂
      have hret0 : r₂.ret = .int 32 (BitVec.ofNat 32 0) := by
        rw [← hr₂]
      rw [hret0] at hret₂
      exact absurd hret₂ (by decide)

/-- **The payload's high-byte group forgets the class bits**: `HlastResidue` is the same
rows at the byte's own route. -/
def HlastResidue.toAbi {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (r : HlastResidue G C s) : HlastHighByteAbi G C s r.hb :=
  ⟨r.r₁, r.r₂, r.r₃, r.rdv, r.xA, r.hreadT, r.hpre₁, r.hcall₁, r.hret₁, r.hbit0T,
    r.hzread, r.hpre₂, r.hcall₂, r.hret₂, r.hev64, r.hpre₃, r.hcall₃⟩

/-- **The residue the last entry's `.highByte` arm carries is empty too**, so no state
supplies `LastEntryArm.highByte` on the class it is stated for. -/
theorem hlastResidue_empty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State} :
    ¬ Nonempty (HlastResidue G C s) := by
  rintro ⟨r⟩
  exact hlastHighByteAbi_empty r.hb ⟨r.toAbi⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HcontByteRoute_of_not_wsStop
#print axioms LeanLLVM.Refinement.WalkScope.HcontByteRoute_not_wsByte
#print axioms LeanLLVM.Refinement.WalkScope.hlastLane_of_not_wsStop
#print axioms LeanLLVM.Refinement.WalkScope.HlastTailLane_not_of_wsByte
#print axioms LeanLLVM.Refinement.WalkScope.s2ValuePosPre_of_inv
#print axioms LeanLLVM.Refinement.WalkScope.hcontOpenCall_of_inv
#print axioms LeanLLVM.Refinement.WalkScope.hlastAbi_openCall
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailByte_mem
#print axioms LeanLLVM.Refinement.WalkScope.hlastTail_logBase
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailRoute_logBase
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailRoute_rootSlot_word
#print axioms LeanLLVM.Refinement.WalkScope.hlastHighByteAbi_answer_ne_zero
#print axioms LeanLLVM.Refinement.WalkScope.stage2ValuePos_some_zero
#print axioms LeanLLVM.Refinement.WalkScope.hlastTailRoute_kindWord
#print axioms LeanLLVM.Refinement.WalkScope.s2ScalarValue_kind_zero
#print axioms LeanLLVM.Refinement.WalkScope.hlastHighByteAbi_empty
#print axioms LeanLLVM.Refinement.WalkScope.hlastResidue_empty

end WalkScope
end LeanLLVM.Refinement
