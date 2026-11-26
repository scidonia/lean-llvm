/-
The depth-zero `[` head of a concrete document, `[1]`.

`JsonStage2NoEventWalkRowsZeroDescend`'s `stage2NoEventWalkZeroHead_bracketDescendRoute`
states the reachability of the depth-zero `[` descend arm over a head and its
readings.  This module supplies the head: the document `"[1]"` at 4096
(`bs = [91, 49, 93]`), its three entry lanes `0, 1, 2` at 4160
(`ent = [0, 1, 2]`, `nep = 3`, `n = 3`), and a state at `NodeBlock5` whose
environment is the loop head's six read cells and nine `phi` cells over the
carry's base table, at depth and frame zero.  The memory is the zero block
`stage2NoEventWalkF1Mem` with the document and the lanes written into it, so
every region the invariant names is present.

**The head is a real head.**  `stage2NoEventWalkW1_inv` is the full invariant
over that memory (the same field-by-field construction the F1 witness uses), and
`stage2NoEventWalkW1_head` its `Stage2NoEventWalkHead` at index zero: the read
cells are the loop head's own, `K.ent[0]? = some 0`, `K.bs[0]? = some 91`, and
the memory's byte at 4096 is `[`.

**Why it matters.**  `stage2NoEventWalkW1_route` instantiates
`stage2NoEventWalkZeroHead_bracketDescendRoute` at that head: the class is the
bracket's, the zero staging holds, the positive staging is refuted, and the
walk runs the depth-zero descend to the continuation dispatch with the second
entry's lane `1` and byte `49`.  So the reachability of the arm is a theorem
with a witness, not a reading of the fixture.

**The one route the witness does not run.**  `Head` is a state predicate: it
says nothing about how the state is entered.  The seed run to it is
`stage2NoEventWalkSeedRun`'s, and it is stated over the record's precondition and
the staged objects; this module does not restate that staging at a concrete
memory (its regions are the F1 block's, not the record's `next0` cursor), so the
witness starts at `NodeBlock5` rather than at `EntryState`.  What the row needs
from a head is what it has.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsZeroDescend
import LeanLLVM.Refinement.JsonStage2NoEventWalkHead
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval (cells)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one readBytes_writeBytes_frame)

/-! ### The concrete document

The zero block `stage2NoEventWalkF1Mem` covers `[4096, 8296)`; this witness
writes the document `[`, `1`, `]` at 4096 and the three entry lanes at 4160,
4164 and 4168, the document last so its bytes are the outermost write. -/

/-- **The witness memory.** -/
def stage2NoEventWalkW1Mem : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes stage2NoEventWalkF1Mem 4160 [0, 0, 0, 0])
        4164 [1, 0, 0, 0])
      4168 [2, 0, 0, 0])
    4096 [91, 49, 93]

/-- **A read inside the zero block, away from the document and the lanes.** -/
theorem stage2NoEventWalkW1_readBytes_zero {a n : Nat}
    (h1 : 4096 ≤ a) (h2 : a + n ≤ 8296)
    (hd : a + n ≤ 4096 ∨ 4099 ≤ a)
    (hl : a + n ≤ 4160 ∨ 4172 ≤ a) :
    readBytes stage2NoEventWalkW1Mem a n = some (List.replicate n 0) := by
  unfold stage2NoEventWalkW1Mem
  rw [readBytes_writeBytes_frame _ [91, 49, 93] 4096 a n hd]
  rw [readBytes_writeBytes_frame _ [2, 0, 0, 0] 4168 a n
    (by simp only [List.length_cons, List.length_nil]; omega)]
  rw [readBytes_writeBytes_frame _ [1, 0, 0, 0] 4164 a n
    (by simp only [List.length_cons, List.length_nil]; omega)]
  rw [readBytes_writeBytes_frame _ [0, 0, 0, 0] 4160 a n
    (by simp only [List.length_cons, List.length_nil]; omega)]
  exact stage2NoEventWalkF1_readBytes_zeros h1 h2

/-- **Presence inside the zero block, away from the document and the lanes.** -/
theorem stage2NoEventWalkW1_present {a : Nat}
    (h1 : 4096 ≤ a) (h2 : a + 1 ≤ 8296)
    (hd : a + 1 ≤ 4096 ∨ 4099 ≤ a)
    (hl : a + 1 ≤ 4160 ∨ 4172 ≤ a) :
    present stage2NoEventWalkW1Mem a := by
  have hb := stage2NoEventWalkW1_readBytes_zero (a := a) (n := 1) h1 h2 hd hl
  rw [readBytes_one] at hb
  cases hr : readByte stage2NoEventWalkW1Mem a with
  | none => rw [hr] at hb; cases hb
  | some b => exact ⟨b, hr⟩

/-- **A byte range is present.** -/
theorem stage2NoEventWalkW1_hasBytes {a n : Nat}
    (h1 : 4096 ≤ a) (h2 : a + n ≤ 8296)
    (hd : a + n ≤ 4096 ∨ 4099 ≤ a)
    (hl : a + n ≤ 4160 ∨ 4172 ≤ a) :
    HasBytes stage2NoEventWalkW1Mem a n :=
  ⟨_, stage2NoEventWalkW1_readBytes_zero h1 h2 hd hl⟩

/-- **The document, read whole.** -/
theorem stage2NoEventWalkW1_doc :
    readBytes stage2NoEventWalkW1Mem 4096 3 = some [91, 49, 93] := by
  unfold stage2NoEventWalkW1Mem
  exact readBytes_writeBytes_same _ _

/-- **The document's byte at `k < 3`.** -/
theorem stage2NoEventWalkW1_docByte (k : Nat) (hk : k < 3) :
    readByte stage2NoEventWalkW1Mem (4096 + k) = some ([91, 49, 93].getD k 0) := by
  unfold stage2NoEventWalkW1Mem
  exact readByte_writeBytes_at _ _ 4096 k hk

/-- **The document's opening byte is `[`.** -/
theorem stage2NoEventWalkW1_open :
    readBytes stage2NoEventWalkW1Mem (4096 + 0) 1 = some [91] := by
  rw [readBytes_one, stage2NoEventWalkW1_docByte 0 (by decide)]
  rfl

/-- **The document's second byte is `1`.** -/
theorem stage2NoEventWalkW1_second :
    readBytes stage2NoEventWalkW1Mem (4096 + 1) 1 = some [49] := by
  rw [readBytes_one, stage2NoEventWalkW1_docByte 1 (by decide)]
  rfl

/-- **The first lane is `0`.** -/
theorem stage2NoEventWalkW1_lane0 :
    readBytes stage2NoEventWalkW1Mem 4160 4 = some [0, 0, 0, 0] := by
  unfold stage2NoEventWalkW1Mem
  rw [readBytes_writeBytes_frame _ [91, 49, 93] 4096 4160 4 (by decide)]
  rw [readBytes_writeBytes_frame _ [2, 0, 0, 0] 4168 4160 4 (by decide)]
  rw [readBytes_writeBytes_frame _ [1, 0, 0, 0] 4164 4160 4 (by decide)]
  exact readBytes_writeBytes_same _ _

/-- **The second lane is `1`.** -/
theorem stage2NoEventWalkW1_lane1 :
    readBytes stage2NoEventWalkW1Mem 4164 4 = some [1, 0, 0, 0] := by
  unfold stage2NoEventWalkW1Mem
  rw [readBytes_writeBytes_frame _ [91, 49, 93] 4096 4164 4 (by decide)]
  rw [readBytes_writeBytes_frame _ [2, 0, 0, 0] 4168 4164 4 (by decide)]
  exact readBytes_writeBytes_same _ _

/-- **The third lane is `2`.** -/
theorem stage2NoEventWalkW1_lane2 :
    readBytes stage2NoEventWalkW1Mem 4168 4 = some [2, 0, 0, 0] := by
  unfold stage2NoEventWalkW1Mem
  rw [readBytes_writeBytes_frame _ [91, 49, 93] 4096 4168 4 (by decide)]
  exact readBytes_writeBytes_same _ _

/-- **The entry stream is `[0, 1, 2]`.** -/
theorem stage2NoEventWalkW1_entries :
    readLanes32 stage2NoEventWalkW1Mem 4160 3 = some [0, 1, 2] := by
  simp only [readLanes32, stage2NoEventWalkW1_lane0]
  rfl

/-! ### The carry and the state

The twelve arguments at `b = 4096`, `n = 3`, `ep = 4160`, `nep = 3`,
`xp = 4200`, `nxp = 0`, `scratch = 4224`, `scratchcap = 68`, the four output
words from 4300, and the four staged objects from 4352 — the F1 layout with the
document's length raised and the scratch widened to hold the reserve over it. -/

/-- **The witness carry.** -/
def stage2NoEventWalkW1K : Stage2NoEventWalkCarry :=
  { a12 := [.ptr 4096, .int 64 (BitVec.ofNat 64 3), .ptr 4160,
      .int 64 (BitVec.ofNat 64 3), .ptr 4200, .int 64 (BitVec.ofNat 64 0),
      .ptr 4224, .int 64 (BitVec.ofNat 64 68), .ptr 4300, .ptr 4312, .ptr 4324,
      .ptr 4336]
    next0 := 8192, b := 4096, n := 3, ep := 4160, nep := 3, xp := 4200, nxp := 0,
    scratch := 4224, scratchcap := 68, tokensOut := 4300, valuesOut := 4312,
    sumOut := 4324, err := 4336, bs := [91, 49, 93], ent := [0, 1, 2], stk := 4352,
    d := 6112, xj := 8192, e := 4880, c := 4912, tok := 0, terms := 0, arena := [],
    arenaWord := 0, nextEnd := 8228 }

/-- **The witness state**: the loop head's layers over the carry's base table, at
`NodeBlock5`, depth and frame zero, with the document's opening byte in `%3`. -/
def stage2NoEventWalkW1S : State :=
  { env := cells (loopHeadReadCellsAt stage2NoEventWalkW1K 0 0 0 0 520 0 91)
      (cells (loopHeadPhiCellsAt stage2NoEventWalkW1K 0 0 0 0 520)
        (stage2NoEventWalkBaseValues stage2NoEventWalkW1K))
    mem := stage2NoEventWalkW1Mem, next := 0, pc := "NodeBlock5", pre := none }

/-! ### The invariant at the witness

The F1 witness's field-by-field construction, at this document's memory. -/

/-! ### The base table resolves at the witness

`lookupName` returns a table's first entry for a name, so a member's value is
recovered when the names are distinct. -/

/-- **A member of a name-distinct table resolves to its value.** -/
theorem lookupName_of_mem_nodup {α : Type} :
    ∀ (l : List (String × α)), (l.map (·.1)).Nodup →
      ∀ {n : String} {v : α}, (n, v) ∈ l → lookupName l n = some v
  | [], _, _, _, h => (List.not_mem_nil h).elim
  | (k, w) :: rest, hnd, n, v, h => by
      have hnd' : (rest.map (·.1)).Nodup := (List.nodup_cons.mp hnd).2
      have hknot : k ∉ rest.map (·.1) := (List.nodup_cons.mp hnd).1
      rcases List.mem_cons.mp h with h' | h'
      · injection h' with hkn hv
        subst hkn
        subst hv
        rw [lookupName_cons_self]
      · have hne : k ≠ n := by
          intro hkn
          subst hkn
          exact hknot (List.mem_map_of_mem (f := Prod.fst) h')
        rw [lookupName_cons_ne _ _ hne]
        exact lookupName_of_mem_nodup rest hnd' h'

/-- **The base table resolves at the witness.** -/
theorem stage2NoEventWalkW1_baseLookups :
    Stage2NoEventWalkBaseLookups stage2NoEventWalkW1K stage2NoEventWalkW1S := by
  intro n v hv
  have hmem : n ∈ stage2NoEventWalkBaseNames := by
    have := List.mem_map_of_mem (f := Prod.fst) hv
    rwa [stage2NoEventWalkBaseValues_names] at this
  have hnotR : n ∉ loopHeadReadCellNames := by
    have h := List.all_eq_true.mp (by decide : stage2NoEventWalkBaseNames.all
      (fun m => !decide (m ∈ loopHeadReadCellNames)) = true) n hmem
    simpa using h
  have hnotP : n ∉ loopHeadPhiCellNames := by
    have h := List.all_eq_true.mp (by decide : stage2NoEventWalkBaseNames.all
      (fun m => !decide (m ∈ loopHeadPhiCellNames)) = true) n hmem
    simpa using h
  show lookupName (cells (loopHeadReadCellsAt stage2NoEventWalkW1K 0 0 0 0 520 0 91)
      (cells (loopHeadPhiCellsAt stage2NoEventWalkW1K 0 0 0 0 520)
        (stage2NoEventWalkBaseValues stage2NoEventWalkW1K))) n = some v
  rw [cells_lookup_of_notin _ _ (by
    rw [loopHeadReadCellsAt_names]; exact hnotR)]
  rw [cells_lookup_of_notin _ _ (by
    rw [loopHeadPhiCellsAt_names]; exact hnotP)]
  exact lookupName_of_mem_nodup (l := stage2NoEventWalkBaseValues stage2NoEventWalkW1K)
    (by rw [stage2NoEventWalkBaseValues_names]; decide) hv

/-- **The invariant at the witness.** -/
theorem stage2NoEventWalkW1_inv :
    Stage2NoEventWalkInv stage2NoEventWalkW1K stage2NoEventWalkW1Mem
      stage2NoEventWalkW1S := by
  refine
    { args_eq := rfl
      doc := stage2NoEventWalkW1_doc
      tail := stage2NoEventWalkW1_hasBytes (a := 4099) (n := 32) (by omega) (by omega)
        (by omega) (by omega)
      entries := stage2NoEventWalkW1_entries
      order := by decide
      inside := by
        intro q hq
        simp only [stage2NoEventWalkW1K, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl | rfl <;> decide
      esc := ⟨[], rfl⟩
      scratchBytes :=
        stage2NoEventWalkW1_hasBytes (a := 4224) (n := 68) (by omega) (by omega)
          (by omega) (by omega)
      scratchRoom := by decide
      tokensBytes := stage2NoEventWalkW1_hasBytes (a := 4300) (n := 8) (by omega)
        (by omega) (by omega) (by omega)
      valuesBytes := stage2NoEventWalkW1_hasBytes (a := 4312) (n := 8) (by omega)
        (by omega) (by omega) (by omega)
      sumBytes := stage2NoEventWalkW1_hasBytes (a := 4324) (n := 8) (by omega)
        (by omega) (by omega) (by omega)
      errBytes := stage2NoEventWalkW1_hasBytes (a := 4336) (n := 8) (by omega)
        (by omega) (by omega) (by omega)
      maxDoc := by decide
      nLt := by decide
      scratchcapLt := by decide
      nepLt := by decide
      nxpLt := by decide
      separate := by
        unfold DisjointRegions
        simp only [stage2NoEventWalkW1K, stage2NoEventRegions, stage2NoEventWrites,
          stage2ReadTail]
        decide
      watermark := ?_
      stagedBytes := ?_
      stagedEnd := ?_
      sep := by
        unfold Stage2NoEventWalkSep DisjointRegions
        simp only [stage2NoEventWalkW1K, stage2NoEventRegions, stage2NoEventWrites,
          stage2ReadTail, stage2NoEventStagedRegions, stage2NoEventStackExtent,
          stage2NoEventErrorExtent, stage2NoEventCursorExtent, stage2NoEventNumExtent]
        decide
      arenaEq := by decide
      tokLe := by decide
      nextEnd_static := by decide
      xjNext0 := rfl
      walkPresent := ?_
      walkFrame := by intro a ha; rfl }
  · intro r hr
    simp only [stage2NoEventWalkW1K, stage2NoEventRegions, stage2NoEventWrites,
      stage2ReadTail, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    simp only [stage2NoEventWalkW1K, stage2NoEventStagedRegions,
      stage2NoEventStackExtent, stage2NoEventErrorExtent,
      stage2NoEventCursorExtent, stage2NoEventNumExtent, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      refine stage2NoEventWalkW1_hasBytes (by omega) (by omega) (by omega) (by omega)
  · intro r hr
    simp only [stage2NoEventWalkW1K, stage2NoEventStagedRegions,
      stage2NoEventStackExtent, stage2NoEventErrorExtent,
      stage2NoEventCursorExtent, stage2NoEventNumExtent, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    simp only [stage2NoEventWalkW1K, stage2NoEventRunRegions,
      stage2NoEventStagedRegions, stage2NoEventStackExtent,
      stage2NoEventErrorExtent, stage2NoEventCursorExtent, stage2NoEventNumExtent,
      List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact stage2NoEventWalkW1_present (by omega) (by omega) (by omega) (by omega)

/-! ### The head at `NodeBlock5` -/

/-- **The witness is a head at index zero**: the six read cells and nine `phi`
cells over the base table, `K.ent[0]? = some 0`, `K.bs[0]? = some 91`, and the
memory's byte at `4096` is `[`. -/
theorem stage2NoEventWalkW1_head :
    Stage2NoEventWalkHead stage2NoEventWalkW1K stage2NoEventWalkW1Mem 0
      stage2NoEventWalkW1S :=
  { inv := stage2NoEventWalkW1_inv
    pc := rfl
    klt := by decide
    count := by show stage2NoEventWalkW1K.tok ≤ 0; decide
    bPos := by decide
    layers := ⟨stage2NoEventWalkBaseValues stage2NoEventWalkW1K, 0, 0, 0, 520, 0, 91,
      rfl, by decide, by decide, by decide, stage2NoEventWalkW1_open,
      by decide, by decide, rfl, rfl⟩
    baseLookups := stage2NoEventWalkW1_baseLookups }

/-- **The witness's depth word is zero.** -/
theorem stage2NoEventWalkW1_sp :
    lookupName stage2NoEventWalkW1S.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
  show lookupName (cells (loopHeadReadCellsAt stage2NoEventWalkW1K 0 0 0 0 520 0 91)
      (cells (loopHeadPhiCellsAt stage2NoEventWalkW1K 0 0 0 0 520)
        (stage2NoEventWalkBaseValues stage2NoEventWalkW1K))) "%sp.0.ph1403" = _
  rw [cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt])
    (by rw [loopHeadPhiCellsAt_names]; decide)

/-- **A `UInt8` literal's value is itself.** -/
theorem stage2NoEventWalkW1_u91 : (91 : UInt8).toNat = 91 := by
  simp [UInt8.toNat_ofNat]

/-- **The opening quote's value.** -/
theorem stage2NoEventWalkW1_u49 : (49 : UInt8).toNat = 49 := by
  simp [UInt8.toNat_ofNat]

/-- **Reachability with a witness.**  At the concrete `[1]` head the class is the
bracket's, the zero staging holds, the positive staging is refuted, and the walk
runs the depth-zero descend to the continuation dispatch at the second entry
(lane `1`, byte `49`). -/
theorem stage2NoEventWalkW1_route {calls : Calls} :
    Stage2NoEventWalkHeadBracketClass stage2NoEventWalkW1K 0 stage2NoEventWalkW1S ∧
      Stage2NoEventWalkZeroDescendBranch stage2NoEventWalkW1S ∧
      (¬ Stage2NoEventWalkDescendBranch stage2NoEventWalkW1K 0
        stage2NoEventWalkW1S) ∧
      ∃ s1 : State,
        Stage2NoEventWalkChain calls stage2NoEventWalkW1Mem stage2NoEventWalkW1K
            stage2NoEventWalkW1S stage2NoEventWalkW1K s1 ∧
          Stage2NoEventWalkBracketDispatch stage2NoEventWalkW1K 0 s1 1 49 :=
  stage2NoEventWalkZeroHead_bracketDescendRoute (calls := calls)
    (byte0 := 91) (lane := 0) (next := 1) (nextByte := 49)
    stage2NoEventWalkW1_head stage2NoEventWalkW1_sp
    (by decide) (by decide) stage2NoEventWalkW1_u91 (by decide) (by decide)
    (by rw [stage2NoEventWalkW1_u49]; decide)

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkW1Mem
#print axioms stage2NoEventWalkW1_readBytes_zero
#print axioms stage2NoEventWalkW1_doc
#print axioms stage2NoEventWalkW1_entries
#print axioms stage2NoEventWalkW1K
#print axioms stage2NoEventWalkW1S
#print axioms stage2NoEventWalkW1_inv
#print axioms stage2NoEventWalkW1_head
#print axioms stage2NoEventWalkW1_route

end LeanLLVM.Refinement
