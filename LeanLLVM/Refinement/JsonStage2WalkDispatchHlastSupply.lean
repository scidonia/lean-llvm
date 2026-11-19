/-
# The last entry's payload, at the fields its own rows produce

`HlastPayload` (`JsonStage2WalkDispatchSupply`) is `HlastLane` beside `HlastAbi`.  This
module produces every field of that payload the tree's own lemmas reach, records the ones
it does not with the premise each still needs, and states the high-byte class as the
refusal it is.

## The class is a refusal, not an emission

`%8 ∈ {126, 127}` is what the head switch's `slt 125`/`eq 125` bits name.  Those bytes take
`if.end372.i`'s tag test's false arm, so `if.then413.i`'s `%.sink372` `phi` selects its
`if.else405.i` incoming — the literal `0` — and `od_scalar_value` answers `0` at a zero
kind (`stage2ScalarValue`'s first arm, which writes `stage2ErrSetMsg`).  The walk leaves
`if.then425.i` for `if.then432.i` and takes the error path through `cleanup474.i` to the
refusal copy; it never calls `s2_after_value`.

So the emission bundle the payload used to carry is empty on this class
(`hlastResidue_empty`, and the same argument at its three-call form), and the payload's
high-byte field is now `HlastHighByteRefusal`: the two leading calls, the scalar call's
answer `0`, the refusal record, and the class's route to the refusal copy.

## Produced

| field | producer |
|---|---|
| `HlastLane.tail`'s `hb` | `HcontByteRoute_of_not_wsStop`: the document's last byte has a route **exactly when it is not one of the four whitespace bytes**.  `hlastLane_of_not_wsStop` is the group at that premise. |
| `HlastAbi.openCall` — fully produced, no premise | `hlastAbi_openCall`: the root slot's word is `walkReadBytes_rootSlot_word`, the precondition is `s2ValuePosPre_of_inv` (the stack bytes are `WalkInv.tyBytes`/`stBytes` at `C.sp - 1`), and the answer is `s2ValuePos_answers` at that precondition. |
| `HlastAbi.highByte`'s two leading calls | `hlastHighByteRefusal_of_stage`: `hcontSeamMidAt` at a `HcontSeamStage` derives the value-position and scalar rows (the first call's staging from the invariant, the second's from the stage's `hpreS`). |
| `HlastAbi.highByte`'s answer and record | the same producer: the kind word is the store's own `0` (`seamKindStore_word`), so `s2ScalarValue_refused` names both `hret₂` and `hmem` — they are derived from the model, not fields. |
| `HlastAbi.highByte`'s root word and log word | `hlastTailRoute_rootSlot_word`, `hlastTailRoute_logBase` (the payload group's flat forms). |
| **the last level's seam** (`HlastClassRows.seam` and `HcontSeamAbi.last`) | `hlastSeamRefusal_of_stage` / `hlastSeam_nonempty`: `HlastSeam.answerOneRefuse` at the class's literal `0` (`HlastSeamRefusal`, answer and record derived by `s2ScalarValue_refused`; `hcontSeamMidAt` gives the two leading calls).  The other answer is `HlastSeam.answerZero` via `hlastSeamZero_of_call` (the first call's row with answer `0`, routing through `if.then418.i` and `cleanup474.i`). |

## Not produced, and why

* **`HlastLane.tail` at a variable geometry.**  The field's guard is on the *entry's*
  first byte (`hlastByte G C`); the route it must build is the *document's last* byte's
  (`G.bs.getD (G.n - 1) 0`).  A document ending in `9`, `10`, `13` or `32` has no route at
  all (`HcontByteRoute_not_wsByte`, `HlastTailLane_not_of_wsByte`), and nothing in
  `WalkGeom` or `WalkInv` excludes it: `HlastArmRows.run`'s guard (`wsStop G (G.n - 1)`,
  `JsonStage2WalkDispatchLastRows`) is the run class at exactly that byte, and no clause
  excludes a head state with the high-byte bits (`%8 ∈ {126, 127}`) from being the last
  entry's on such a document.  The group's producer therefore needs a premise on the
  geometry (`¬ wsStop G (G.n - 1)`); `hlastLane_of_not_wsStop` is that.
* **`HlastAbi.highByte`'s route (`HlastRefuseRoute`).**  The error path's blocks from
  `if.then432.i` to `cleanup474.i` have no composed segment: `WalkLink.if_then432_i`,
  `WalkLink.if_then418_i` and `WalkLink.cleanup474_i` exist, the scan
  (`cond.end.i96`/`land.rhs.i103`/`while.end.i`), `if.end.i97` and the escape tree
  (`if.else.i` … `if.else43.i`) do not, and the scan's length is the entry's own.  The
  producer owed is a priced segment `if.then432.i → … → cleanup474.i → if.then` with the
  stored word (`stage2ErrSetMsg`'s `%e + 8`, which is the token's `pos`) and a count inside
  the last entry's credit.  The payload carries the route rather than assuming it, exactly
  as `HlastArmRows`' rows carry the arms' own segments.
* **The class's answer-zero sub-route.**  `s2_value_pos` can answer `0` at the class too
  (a depth-zero head whose root slot is already flagged), and that arm is
  `if.then418.i → cleanup474.i → if.then` — three links after the head, and no scalar call.
  It is named, not collapsed: the last level's seam is the sum `HlastSeam`
  (`JsonStage2WalkDispatchSeams`), whose `answerZero` arm is `HlastSeamZero` (produced by
  `hlastSeamZero_of_call` from the first call's row and its zero answer) and whose
  `answerOneRefuse` arm is `HlastSeamRefusal` (produced here).  What the zero arm still
  takes is the same class route, with the `if.then418.i` link chain rather than the error
  path's.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamCalls

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

/-! ### The high-byte class's staged reads

The routed tail's memory is the plain tail's: the byte's route binds comparison cells and
the seam's stores are the same three.  So the root slot's word and the log's base word are
the plain tail's, and both are theorems; the kind word is the class's store.
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

/-- **The kind word at the byte route's tail is `0`.**  The `if.then413.i` store wrote
`%.sink372`, whose `if.else405.i` incoming is `0`; the route's span enters the block from
that incoming. -/
theorem hlastKindStore_word {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) :
    stage2ReadWord (hlastKindStore C s hb) (C.stage.tok + 16) 4 = some 0 := by
  unfold stage2ReadWord hlastKindStore hlastKindStoreAt
  rw [show (BitVec.ofNat 32 0).toNat = 0 from walkToNat_ofNat32 (by decide)]
  have h := readBytes_writeBytes_same (hlastTailRoute C s hb).mem (natToBytes 0 4)
    (addr := C.stage.tok + 16)
  rw [show (natToBytes 0 4).length = 4 from natToBytes_length 0 4] at h
  rw [h]
  show some (bytesToNat (natToBytes 0 4)) = some 0
  rw [show bytesToNat (natToBytes 0 4) = 0 by decide]

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

/-! ### The last level's seam rows, from the staged words

The seam's two leading calls are `hcontSeamMidAt`'s at a `HcontSeamStage`; the kind word is
the store's `0`; and the answer and the record are `s2ScalarValue_refused`'s — the model's
first arm, not a supplied fact.  The row is stated at the state, so the class's seam
(`HlastSeam.answerOneRefuse`) and the arm's payload (`HlastHighByteRefusal.rows`) read the
same theorem.
-/

set_option maxHeartbeats 1000000 in
/-- **The refusal seam's rows, from the staged words.** -/
theorem hlastSeamRefusal_nonempty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (st : HcontSeamStage G C s (BitVec.ofNat 32 0)) :
    Nonempty (HlastSeamRefusal G C s) := by
  obtain ⟨mid, hcA, hrdv⟩ := hcontSeamMidAt st
  -- the kind word at the seam's store is zero
  have hkind0 : stage2ReadWord (seamKindStore C s (BitVec.ofNat 32 0))
      (C.stage.tok + 16) 4 = some 0 := by
    simpa using seamKindStore_word (Cs := C) (s := s) (cA := (BitVec.ofNat 32 0)) (by decide)
  -- the value-position call hands the kind store's memory back
  obtain ⟨_, _, _, hmem₁, hnext₁⟩ := s2ValuePos_sound mid.hpre₁ mid.hcall₁
  have hmem₁' : mid.r₁.mem = seamKindStore C s (BitVec.ofNat 32 0) := by rw [hmem₁, hcA]
  have hpre₂ : s2ScalarValuePre
      [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z]
      (seamKindStore C s (BitVec.ofNat 32 0)) s.next := by
    have h := mid.hpre₂
    rw [hmem₁', hnext₁] at h
    exact h
  have hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z]
      (seamKindStore C s (BitVec.ofNat 32 0)) s.next = some mid.r₂ := by
    have h := mid.hcall₂
    rw [hmem₁', hnext₁] at h
    exact h
  -- the answer and the record are the model's
  obtain ⟨pos, hret₂, hmem₂⟩ :=
    s2ScalarValue_refused (e0 := C.stage.e) hpre₂ st.heErr hkind0 hcall₂
  exact ⟨{ cA := mid.cA
           hcA := hcA
           rdv := mid.rdv
           r₁ := mid.r₁
           xA := mid.xA
           hret₁ := mid.hret₁
           hbit0 := mid.hbit0
           r₂ := mid.r₂
           hret₂ := hret₂
           pos := pos
           hroot := by rw [hrdv]; exact st.hroot
           hpre₁ := mid.hpre₁
           hcall₁ := mid.hcall₁
           hzread := mid.hzread
           hpre₂ := mid.hpre₂
           hcall₂ := mid.hcall₂
           hmem := by rw [hmem₁']; exact hmem₂ }⟩

/-- **The refusal seam's rows**, at the staged words. -/
noncomputable def hlastSeamRefusal_of_stage {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (st : HcontSeamStage G C s (BitVec.ofNat 32 0)) :
    HlastSeamRefusal G C s :=
  Classical.choice (hlastSeamRefusal_nonempty st)

/-- **The last level's seam is inhabited at the class's literal `0`**: the refusal arm, the
one `%8 ∈ {126, 127}` takes.  The second arm is `hlastSeamZero_of_call`'s. -/
theorem hlastSeam_nonempty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (st : HcontSeamStage G C s (BitVec.ofNat 32 0)) : Nonempty (HlastSeam G C s) :=
  ⟨HlastSeam.answerOneRefuse (hlastSeamRefusal_of_stage st)⟩

/-- **The other answer's seam**: `s2_value_pos` answered `0`, so no scalar call is made and
the walk leaves `if.then413.i` for `if.then418.i`, `cleanup474.i` and the copy. -/
def hlastSeamZero_of_call {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (rows : HcontOpenCall G C s) (h0 : rows.r.ret = .int 32 (BitVec.ofNat 32 0)) :
    HlastSeamZero G C s :=
  { rdv := rows.rdv
    hread := rows.hread
    hpre := rows.hpreV
    r := rows.r
    hcall := rows.hcall
    hret := h0 }

/-- **The class's refusal payload**: the seam's rows at the routed tail and the class's
route to the copy. -/
noncomputable def hlastHighByteRefusal_of_stage {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0)))
    (st : HcontSeamStage G (TailStartC C) (hlastTailRoute C s hb) (BitVec.ofNat 32 0))
    (route : HlastRefuseRoute G C s) : HlastHighByteRefusal G C s hb :=
  { rows := hlastSeamRefusal_of_stage st
    route := route }

/-- **`HlastAbi`'s high-byte group, produced**: the seam's staged words and the class's
route, at every last-entry state with the class bits.  The answer and the record are the
producer's, not the caller's. -/
noncomputable def hlastAbi_highByte {m0 : Mem} (G : WalkGeom m0)
    (hstage : ∀ (C : WalkCarry G) (s : State),
      (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) →
      HcontSeamStage G (TailStartC C) (hlastTailRoute C s hb) (BitVec.ofNat 32 0))
    (hroute : ∀ (C : WalkCarry G) (s : State), HlastRefuseRoute G C s) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      ¬ (C.k + 1 < G.nep) →
      evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
      (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) →
      HlastHighByteRefusal G C s hb :=
  fun _ _ _ _ _ _ _ hb => hlastHighByteRefusal_of_stage hb (hstage _ _ hb) (hroute _ _)

/-! ### The emission residue is empty on this class

`HlastResidue` is the emission arm's old evidence: its `hret₂` asks the scalar call for
the emit answer `1`.  At the class's own route the kind word is `0`, so the model answers
`0` — the residue has no inhabitant.  Same argument as the old three-call form, stated at
the structure the tree still carries. -/

/-- **`HlastResidue` is empty**: its `hret₂ = 1` contradicts the kind-`0` model. -/
theorem hlastResidue_empty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State} :
    ¬ Nonempty (HlastResidue G C s) := by
  rintro ⟨r⟩
  -- the value-position reply fixes the scalar call's memory
  have hcall₁ := r.hcall₁
  rw [s2ValuePos_reply] at hcall₁
  cases hv : stage2ValuePos
      (writeBytes (hlastTailRoute C s r.hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4))
      ((BitVec.ofNat 32 (TailStartC C).sp).toNat) r.rdv.toNat
      (TailStartC C).stage.ctype (TailStartC C).stage.cst with
  | none =>
      rw [hv] at hcall₁
      cases hcall₁
  | some v =>
      rw [hv] at hcall₁
      rw [Option.map_some] at hcall₁
      have hr₁ : r.r₁ = (⟨.int 32 (BitVec.ofNat 32 v),
          (writeBytes (hlastTailRoute C s r.hb).mem (C.stage.tok + 16)
            (natToBytes ((0 : BitVec 32)).toNat 4)),
          (hlastTailRoute C s r.hb).next⟩ : CallOutcome) := Option.some.inj hcall₁.symm
      have hpre₂ := r.hpre₂
      have hcall₂ := r.hcall₂
      rw [hr₁] at hpre₂ hcall₂
      -- the scalar precondition's five reads, at the same memory
      obtain ⟨c, t, o, hargs, base, e, pos, endp, kind, buf, len, cap, win,
        hbase, he, hpos, hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre₂
      simp only [List.cons.injEq, Value.ptr.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      -- ... whose kind word is the store's `0`
      have hk0 : kind = 0 := by
        have hk' : stage2ReadWord
            (writeBytes (hlastTailRoute C s r.hb).mem (C.stage.tok + 16)
              (natToBytes ((0 : BitVec 32)).toNat 4))
            ((TailCarry₂ (TailStartC C)).stage.tok + 16) 4 = some 0 :=
          hlastKindStore_word C s r.hb
        rw [hkind] at hk'
        exact Option.some.inj hk'
      rw [hk0] at hkind
      obtain ⟨m, hm⟩ := s2ScalarValue_kind_zero (mem :=
          writeBytes (hlastTailRoute C s r.hb).mem (C.stage.tok + 16)
            (natToBytes ((0 : BitVec 32)).toNat 4))
        (c := (TailCarry₂ (TailStartC C)).stage.c)
        (t := (TailCarry₂ (TailStartC C)).stage.tok)
        (o := (TailCarry₂ (TailStartC C)).stage.z)
        (next := (hlastTailRoute C s r.hb).next) hbase he hpos hend hkind
      rw [hm] at hcall₂
      have hr₂ := Option.some.inj hcall₂
      have hret0 : r.r₂.ret = .int 32 (BitVec.ofNat 32 0) := by
        rw [← hr₂]
      have hret₂ := r.hret₂
      rw [hret0] at hret₂
      exact absurd hret₂ (by decide)

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
#print axioms LeanLLVM.Refinement.WalkScope.hlastKindStore_word
#print axioms LeanLLVM.Refinement.WalkScope.s2ScalarValue_kind_zero
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamRefusal_nonempty
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamRefusal_of_stage
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeam_nonempty
#print axioms LeanLLVM.Refinement.WalkScope.hlastSeamZero_of_call
#print axioms LeanLLVM.Refinement.WalkScope.hlastHighByteRefusal_of_stage
#print axioms LeanLLVM.Refinement.WalkScope.hlastAbi_highByte
#print axioms LeanLLVM.Refinement.WalkScope.hlastResidue_empty

end WalkScope
end LeanLLVM.Refinement
