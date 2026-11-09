/-
The list body's record, at its pinned entry point.

`escape_positions_satisfies` is the record's `Satisfies` instance: from a staging
`Γ_escape_positions.pre` admits, the run of the pinned `leanllvm_json_escape_list`
completes at `Γ_escape_positions.budget` and every behaviour it has satisfies the
record's post.  The pieces below are what the assembly consumes, and each is
stated where it is used rather than in one conjunction:

* the position list's order and length, so the writer's invariant is inhabited
  at its bound;
* the unchanged-outside frame, as one lemma per memory constructor the body uses
  (`writeBytes`, the out-of-line batch, the inlined batch, the exit block's two
  carry stores), and a remaining-block induction over the writer loop that
  carries it — the loop's exit fact says nothing about the memory it did not
  claim;
* the same constructors as presence, and the same induction carrying it: the
  record's exclusion names the whole capacity, so what a caller staged there is
  handed on as presence rather than as a byte equality;
* the writer's entry, with the inline batch's stream and count readbacks as
  *components*, because refining a supplied term against the unfolded
  `ListLoopInv`/`ListWriterInv` conjunction is what times out;
* the exit-successor segment, one lemma per arm of the position word's test.

The frame's regions are the record's: the stream's capacity `xp … xp + 4 *
blockMax xn0`, the count's slot, and the carry's sixteen bytes.  The batch writes
its eight-entry reserve inside the capacity, which is why the first region is the
capacity and not the claimed prefix.
-/
import LeanLLVM.Vellum.JsonEscapeListPositions
import LeanLLVM.Vellum.JsonEntrySteps

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonB8Steps

/-! ### The position list's order and length -/

/-- The block's escape positions are increasing, because they are a filter of the
lane range. -/
theorem escapePositionsFrom_pairwise (bs : List UInt8) (st : ClassState) :
    (escapePositionsFrom bs st).Pairwise (· < ·) := by
  unfold escapePositionsFrom
  exact List.Pairwise.filter _ (range_pairwise bs.length)

/-- The block's escape positions are no more than the block has bytes. -/
theorem escapePositionsFrom_length_le (bs : List UInt8) (st : ClassState) :
    (escapePositionsFrom bs st).length ≤ bs.length := by
  unfold escapePositionsFrom
  have h := List.length_filter_le (fun k => match bs[k]? with
    | some b => IsEscapeLane (classCarryAt bs st k) b
    | none => false) (List.range bs.length)
  rwa [List.length_range] at h

/-- Every position of a sixty-four-byte block is a lane below sixty-four. -/
theorem escapePositionsFrom_lt_block {lo hi : Block32} {st : ClassState} {k : Nat}
    (h : k ∈ escapePositionsFrom (block64 lo hi) st) : k < 64 := by
  have hlt := escapePositionsFrom_lt h
  rwa [block64_length] at hlt

/-- The block's position list has at most sixty-four entries. -/
theorem escapePositionsFrom_length_le_block (lo hi : Block32) (st : ClassState) :
    (escapePositionsFrom (block64 lo hi) st).length ≤ 64 := by
  have h := escapePositionsFrom_length_le (block64 lo hi) st
  rwa [block64_length] at h

/-- **The body's position word is the specification's.**  The exit block forms
`(w | ctl) & im` from the word the lanes loop fixed, and the loop's word is
`specRunStarts`, so the word the batch counts is the one the block's positions are
read off. -/
theorem lxWord_specPositionWord (bs ctl im : BitVec 64) (odd0 : Bool) :
    lxWord ctl im (specRunStarts bs odd0) = specPositionWord bs ctl im odd0 := rfl

/-- The body's escape word counts the block's positions. -/
theorem ctpop_lxWord_positionWord {lo hi : Block32} {st : ClassState} :
    ctpop (lxWord (specControl64 lo hi st) (specInString64 lo hi st)
        (specRunStarts (specBackslash64 lo hi st) st.oddRun)) =
      (escapePositionsFrom (block64 lo hi) st).length := by
  rw [lxWord_specPositionWord, ctpop_eq_setLanes_length, setLanes_specPositionWord]

/-! ### The frame's regions -/

/-- The three regions the run may write: the stream's capacity (which includes
the batch's reserve), the count's slot, and the carry's sixteen bytes. -/
def escapeRegions (xp xn carry xn0 : Nat) : List (Nat × Nat) :=
  [(xp, 4 * blockMax xn0), (xn, 8), (carry, 16)]

/-- A byte outside a region containing `start … start + n` is below the interval
or above it.  Stated as the disjunction rather than as the negation of the
interval, because `omega` proves this one without case-splitting on the
hypothesis and so leaves no `Classical.choice` in the footprint. -/
theorem outside_region_lt_or_le {regions : List (Nat × Nat)}
    {start n : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ start ∧ start + n ≤ r.1 + r.2) :
    ∀ a, (∀ r ∈ regions, ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) →
      a < start ∨ start + n ≤ a := by
  intro a ha
  rcases Nat.lt_or_ge a start with hlt | hge
  · exact Or.inl hlt
  · right
    rcases Nat.lt_or_ge a (start + n) with hin2 | hge2
    · obtain ⟨r, hr, rlo, rhi⟩ := hin
      exact absurd ⟨Nat.le_trans rlo hge, Nat.lt_of_lt_of_le hin2 rhi⟩ (ha r hr)
    · exact hge2

/-- A write whose interval is inside one of the regions does not disturb a byte
outside them all. -/
theorem unchangedOutside_writeBytes {mem0 m : Mem} {regions : List (Nat × Nat)}
    {start : Nat} {bs : List UInt8}
    (hin : ∃ r ∈ regions, r.1 ≤ start ∧ start + bs.length ≤ r.1 + r.2)
    (h : UnchangedOutside mem0 m regions) :
    UnchangedOutside mem0 (writeBytes m start bs) regions := by
  intro a ha
  rw [readByte_writeBytes_outside m bs (outside_region_lt_or_le hin a ha)]
  exact h a ha

/-- The out-of-line batch's eight entries are inside a region that contains its
thirty-two bytes. -/
theorem unchangedOutside_batchMem {mem0 m : Mem} {regions : List (Nat × Nat)}
    {base : BitVec 32} {esc : BitVec 64} {o : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ o ∧ o + 32 ≤ r.1 + r.2)
    (h : UnchangedOutside mem0 m regions) :
    UnchangedOutside mem0 (batchMem base esc o m) regions := by
  intro a ha
  rw [batchMem_unchanged base esc o m (outside_region_lt_or_le hin a ha)]
  exact h a ha

/-- The inline batch's eight entries write inside the same region. -/
theorem unchangedOutside_inlWrites {mem0 m : Mem} {regions : List (Nat × Nat)}
    {base : BitVec 32} {esc : BitVec 64} {o : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ o ∧ o + 32 ≤ r.1 + r.2)
    (h : UnchangedOutside mem0 m regions) :
    UnchangedOutside mem0 (inlWrites base esc o 8 m) regions := by
  intro a ha
  rw [inlWrites_frame base esc o 8 a (outside_region_lt_or_le hin a ha) m]
  exact h a ha

/-- The inline batch's block: eight entries at `o` and the count at `xn`. -/
theorem unchangedOutside_lstIfEnd4Mem {mem0 m : Mem} {regions : List (Nat × Nat)}
    {base : BitVec 32} {esc : BitVec 64} {o xn count : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ o ∧ o + 32 ≤ r.1 + r.2)
    (hin2 : ∃ r ∈ regions, r.1 ≤ xn ∧ xn + 8 ≤ r.1 + r.2)
    (h : UnchangedOutside mem0 m regions) :
    UnchangedOutside mem0 (lstIfEnd4Mem base esc o xn count m) regions := by
  intro a ha
  rw [lstIfEnd4Mem_unchanged base esc o xn count m
    (outside_region_lt_or_le hin a ha) (outside_region_lt_or_le hin2 a ha)]
  exact h a ha

/-- The exit block's two carry stores: both inside the carry's sixteen bytes. -/
theorem unchangedOutside_lxMem2 {mem0 m : Mem} {regions : List (Nat × Nat)}
    {bs w : BitVec 64} {carry : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ carry ∧ carry + 16 ≤ r.1 + r.2)
    (h : UnchangedOutside mem0 m regions) :
    UnchangedOutside mem0 (lxMem2 m bs w carry) regions := by
  unfold lxMem2 lxMem1
  refine unchangedOutside_writeBytes ?_ (unchangedOutside_writeBytes ?_ h)
  · obtain ⟨r, hr, hlo, hhi⟩ := hin
    exact ⟨r, hr, by omega, by rw [natToBytes_length]; omega⟩
  · obtain ⟨r, hr, hlo, hhi⟩ := hin
    exact ⟨r, hr, by omega, by rw [natToBytes_length]; omega⟩

/-! ### The same constructors, as presence

The exits a unit's post describes as *touched* extents are still present
afterwards: the body only stores, and a store adds cells rather than removing
them.  So each constructor the frame above is stated for has a presence form too,
and the record's capacity clause travels the same path its unchanged-outside
clause does. -/

/-- The inline batch's writes preserve every present region. -/
theorem hasBytes_inlWrites {mem : Mem} {a K : Nat} (h : HasBytes mem a K) :
    ∀ (base : BitVec 32) (esc : BitVec 64) (o n : Nat),
      HasBytes (inlWrites base esc o n mem) a K
  | base, esc, o, 0 => h
  | base, esc, o, n + 1 => by
      show HasBytes (writeBytes (inlWrites base esc o n mem) (o + 4 * n)
        (inlBytes base esc n)) a K
      exact hasBytes_writeBytes (hasBytes_inlWrites h base esc o n)

/-- The inline batch's block writes the eight inline entries and the count. -/
theorem hasBytes_lstIfEnd4Mem {mem : Mem} {a K : Nat} (h : HasBytes mem a K)
    (base : BitVec 32) (esc : BitVec 64) (o xn count : Nat) :
    HasBytes (lstIfEnd4Mem base esc o xn count mem) a K := by
  unfold lstIfEnd4Mem
  exact hasBytes_writeBytes (hasBytes_inlWrites h base esc o 8)

/-- The out-of-line batch's eight entries. -/
theorem hasBytes_batchMem {mem : Mem} {a K : Nat} (h : HasBytes mem a K)
    (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    HasBytes (batchMem base esc o mem) a K := by
  unfold batchMem
  repeat apply hasBytes_writeBytes
  exact h

/-- The exit block's two carry stores. -/
theorem hasBytes_lxMem2 {mem : Mem} {a K : Nat} (h : HasBytes mem a K)
    (bs w : BitVec 64) (carry : Nat) : HasBytes (lxMem2 mem bs w carry) a K := by
  unfold lxMem2 lxMem1
  repeat apply hasBytes_writeBytes
  exact h

/-! ### The writer's entry

The preheaders and the first batch lift the state into the writer's invariant: the
state that arrives at `while.body.i.i` is the inline batch's memory, the loop's
eight cleared lanes, and the cursor the inlined batch left, thirty-two bytes on.
The invariant's two read facts are taken as components here; deriving them from
the inline batch's block is the caller's business, and doing both in one
declaration is what makes elaboration unfold the conjunction. -/

/-- **The writer's invariant at its entry.**  Each conjunct is one of the facts
the head, its loop and the later blocks read; the two read facts arrive as
components. -/
theorem writerInv_entry (blk0 : BitVec 64) (xp xn xn0 : Nat) (position : List Nat)
    (base : BitVec 32) (o : Nat) (s : State) (w : BitVec 64)
    (hpc : s.pc = "while.body.i.i")
    (hpre : s.pre = some "while.body.preheader.i.i")
    (hoo : evalOperand s (.reg "%add.ptr5.i.i") = some (.ptr o))
    (hw : evalOperand s (.reg "%and.7.i.i") = some (.int 64 w))
    (hlanes : ∀ k, k < 64 → w.getLsbD k = decide (k ∈ position.drop 8))
    (hprefix : readBytes s.mem (xp + 4 * xn0) (4 * 8) =
      some (positionsBytes 4 ((position.take 8).map fun k => blockAddr blk0 + k)))
    (hcount : readBytes s.mem xn 8 = some (wordBytes 8 (xn0 + 8)))
    (h8 : 8 ≤ position.length) (hplen : position.length ≤ 64)
    (hcur : o = xp + 4 * xn0 + 4 * 8)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hconv : lookupName s.env "%conv" = some (.int 32 base))
    (hxn : lookupName s.env "%xn" = some (.ptr xn))
    (hpair : position.Pairwise (· < ·))
    (hlt : ∀ k ∈ position, k < 64)
    (hbase : base = lxBase blk0)
    (hcap : blk0.toNat * 64 + 64 < 2 ^ 32) :
    lstWriterInv blk0 xp xn xn0 position base 8 o s w := by
  refine ⟨hpc, ⟨"while.body.preheader.i.i", .reg "%add.ptr5.i.i", .reg "%and.7.i.i",
    hpre, by decide, by decide, hoo, hw, Or.inr rfl⟩,
    ⟨hlanes, hprefix, hcount, h8, hplen⟩, hcur, hkeep, hconv, hxn, hpair, hlt,
    hbase, hcap⟩


/-! ### A writer step's memory

Both arms of the writer head write the same thing: the batch at `o`, then the
count at `xn`.  Stated once, because the frame proof needs the memory and not the
branch. -/

/-- **One writer step's memory**, whichever arm the cleared word selects. -/
theorem lstWriter_step_mem (blk0 : BitVec 64) (xp xn xn0 : Nat) (position : List Nat)
    (base : BitVec 32) (used o : Nat) (s : State) (w : BitVec 64)
    (hinv : lstWriterInv blk0 xp xn xn0 position base used o s w) :
    ∃ e : State, step (escapeListCalls Γ_xl_batch) escapeListFunction s = .jump e ∧
      e.mem = writeBytes (batchMem base w o s.mem) xn
        (natToBytes (xn0 + used + lstBatchCount w) 8) := by
  obtain ⟨hpc, ⟨p, oo, oc, hpre, hoo, hoc, hvo, hvc, hocv⟩, hLLI, hcur, hkeep,
    hconv, hxn, hpair, hplt, hbase, hcap⟩ := hinv
  obtain ⟨hlanes, hprefix, hcount, husedle, hplen⟩ := hLLI
  have hbridge := setLanes_eq_drop_of_inv hpair hplt hlanes
  have hσ : s = withEnv s.env s := (withEnv_self s).symm
  rw [hσ] at hpc hpre hvo hvc hconv hxn ⊢
  have hdisj : xn + 8 ≤ o ∨ o + 32 ≤ xn := by
    rcases hkeep with h | h
    · left; rw [hcur]; omega
    · right
      have h64 : used ≤ 64 := Nat.le_trans husedle hplen
      have : xp + 4 * xn0 + 4 * used + 32 ≤ xp + 4 * blockMax xn0 := by
        unfold blockMax batchReserve; omega
      omega
  have hne : ∀ n, oc = .reg n → n ≠ "%o.044.i.i" := by
    intro n hn
    rcases hocv with h | h <;> rw [hn] at h <;>
      (injection h with h'; rw [h']; decide)
  have hvc' : evalOperand (withEnv (("%o.044.i.i", .ptr o) :: s.env) s) oc =
      some (.int 64 w) :=
    evalOperand_cons_of_ne s.env s "%o.044.i.i" (.ptr o) oc (.int 64 w) hne hvc
  have hload : readBytes (batchMem base w o s.mem) xn 8 =
      some (natToBytes (xn0 + used) 8) := by
    have hc := hcount
    rw [show wordBytes 8 (xn0 + used) = natToBytes (xn0 + used) 8 from rfl] at hc
    rcases hdisj with h | h
    · rw [readBytes_batchMem_below base w o s.mem 8 xn h]; exact hc
    · rw [readBytes_batchMem_above base w o s.mem 8 xn h]; exact hc
  obtain ⟨e, hstep, hpcE, hmemE, hpreE, handE, haddrE, hcmpE, hconvE, hxnE⟩ :=
    lstWhileBody_step s.env s w base o (xn0 + used) xn p oo oc hpc hpre hoo hoc
      hvo hvc' hconv hxn hload
  exact ⟨e, hstep, hmemE⟩

/-! ### The writer's frame, one step at a time -/

/-- The batch's region contains its thirty-two bytes, at the cursor the invariant
names. -/
theorem writerBatch_region {xp xn carry xn0 used o : Nat} (hcur : o = xp + 4 * xn0 + 4 * used)
    (husedle : used ≤ 64) :
    ∃ r ∈ escapeRegions xp xn carry xn0, r.1 ≤ o ∧ o + 32 ≤ r.1 + r.2 := by
  refine ⟨(xp, 4 * blockMax xn0), by simp [escapeRegions], by omega, ?_⟩
  rw [hcur]; unfold blockMax batchReserve; omega

/-- The count's store is exactly the count's region. -/
theorem writerCount_region {xp xn carry xn0 : Nat} :
    ∃ r ∈ escapeRegions xp xn carry xn0, r.1 ≤ xn ∧ xn + 8 ≤ r.1 + r.2 :=
  ⟨(xn, 8), by simp [escapeRegions], by omega, by omega⟩

/-- A writer step preserves the frame. -/
theorem lstWriter_step_frame (blk0 : BitVec 64) (xp xn xn0 carry : Nat) (position : List Nat)
    (base : BitVec 32) (used o : Nat) (s : State) (w : BitVec 64) (mem0 : Mem)
    (hinv : lstWriterInv blk0 xp xn xn0 position base used o s w)
    (hframe : UnchangedOutside mem0 s.mem (escapeRegions xp xn carry xn0)) :
    ∃ e : State, step (escapeListCalls Γ_xl_batch) escapeListFunction s = .jump e ∧
      UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0) := by
  obtain ⟨e, hstep, hmem⟩ := lstWriter_step_mem blk0 xp xn xn0 position base used o s w hinv
  obtain ⟨hpc, _hphi, hLLI, hcur, _hkeep, _hconv, _hxn, _hpair, _hplt, _hbase,
    _hcap⟩ := hinv
  obtain ⟨_hlanes, _hprefix, _hcount, husedle, hplen⟩ := hLLI
  refine ⟨e, hstep, ?_⟩
  rw [hmem]
  refine unchangedOutside_writeBytes ?_ (unchangedOutside_batchMem ?_ hframe)
  · obtain ⟨r, hr, hlo, hhi⟩ := writerCount_region (xp := xp) (xn := xn) (carry := carry)
      (xn0 := xn0)
    exact ⟨r, hr, hlo, by rw [natToBytes_length]; exact hhi⟩
  · exact writerBatch_region hcur (Nat.le_trans husedle hplen)

/-- A writer step preserves the carry pair: its two stores are the batch at `o`
and the count at `xn`, and both lie outside the carry's sixteen bytes. -/
theorem lstWriter_step_carry (blk0 : BitVec 64) (xp xn xn0 carry : Nat) (position : List Nat)
    (base : BitVec 32) (used o : Nat) (s : State) (w : BitVec 64)
    (hinv : lstWriterInv blk0 xp xn xn0 position base used o s w)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry) :
    ∀ (e : State), step (escapeListCalls Γ_xl_batch) escapeListFunction s = .jump e →
      readBytes e.mem carry 16 = readBytes s.mem carry 16 := by
  obtain ⟨e', hstep', hmem⟩ := lstWriter_step_mem blk0 xp xn xn0 position base used o s w hinv
  obtain ⟨hpc, _hphi, hLLI, hcur, _hkeep, _hconv, _hxn, _hpair, _hplt, _hbase,
    _hcap⟩ := hinv
  obtain ⟨_hlanes, _hprefix, _hcount, husedle, hplen⟩ := hLLI
  have hbatch : carry + 16 ≤ o ∨ o + 32 ≤ carry := by
    rcases hcx with h | h
    · exact Or.inl (by omega)
    · right
      have h64 : used ≤ 64 := Nat.le_trans husedle hplen
      have hle : xp + 4 * xn0 + 4 * used + 32 ≤ xp + 4 * blockMax xn0 := by
        unfold blockMax batchReserve
        omega
      rw [hcur]
      omega
  intro e hstep
  rw [hstep] at hstep'
  have heq : e = e' := Ctrl.jump.inj hstep'
  subst e'
  have hframeH : carry + 16 ≤ xn ∨
      xn + (natToBytes (xn0 + used + lstBatchCount w) 8).length ≤ carry := by
    simpa only [natToBytes_length] using hcarr
  rw [hmem]
  rw [JsonEntrySteps.readBytes_writeBytes_frame _ _ xn carry 16 hframeH]
  rcases hbatch with h | h
  · rw [readBytes_batchMem_below base w o s.mem 16 carry h]
  · rw [readBytes_batchMem_above base w o s.mem 16 carry h]

/-- A writer step preserves every present region: its memory is the batch at `o`
and the count at `xn`, and both are stores. -/
theorem lstWriter_step_presence (blk0 : BitVec 64) (xp xn xn0 : Nat) (position : List Nat)
    (base : BitVec 32) (used o : Nat) (s : State) (w : BitVec 64)
    (hinv : lstWriterInv blk0 xp xn xn0 position base used o s w)
    (hhas : HasBytes s.mem xp (4 * blockMax xn0)) :
    ∀ (e : State), step (escapeListCalls Γ_xl_batch) escapeListFunction s = .jump e →
      HasBytes e.mem xp (4 * blockMax xn0) := by
  obtain ⟨e', hstep', hmem⟩ := lstWriter_step_mem blk0 xp xn xn0 position base used o s w hinv
  intro e hstep
  rw [hstep] at hstep'
  have heq : e = e' := Ctrl.jump.inj hstep'
  subst e'
  rw [hmem]
  exact hasBytes_writeBytes (hasBytes_batchMem hhas base w o)

/-- **The writer loop, carrying the frame.**  The same remaining-block induction
as `lstWriter_run`, with the memory's agreement with the input outside the three
regions in the invariant; the exit fact alone says nothing about the bytes the
loop did not claim.  The presence conjunct rides the same induction: every step's
memory is a batch store and a count store, and neither removes a byte. -/
theorem lstWriter_run_frame (blk0 : BitVec 64) (xp xn xn0 carry : Nat) (position : List Nat)
    (base : BitVec 32) (mem0 : Mem) (carryBytes : List UInt8)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry) :
    ∀ (r used o : Nat) (s : State) (w : BitVec 64),
      lstWriterInv blk0 xp xn xn0 position base used o s w →
      UnchangedOutside mem0 s.mem (escapeRegions xp xn carry xn0) →
      readBytes s.mem carry 16 = some carryBytes →
      ctpop w ≤ 8 * r →
      HasBytes s.mem xp (4 * blockMax xn0) →
      ∃ (e : State) (j : Nat), j ≤ r + 1 ∧ lstWriterExit blk0 xp xn xn0 position e ∧
        UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0) ∧
        readBytes e.mem carry 16 = some carryBytes ∧
        HasBytes e.mem xp (4 * blockMax xn0) ∧
        ∀ m, runFuel (escapeListCalls Γ_xl_batch) (j + m) escapeListFunction s =
          runFuel (escapeListCalls Γ_xl_batch) m escapeListFunction e := by
  intro r
  induction r with
  | zero =>
      rintro used o s w hInv hframe hcarry hBnd hhas
      have hInv0 := hInv
      obtain ⟨_hpc, ⟨_p, _oo, _oc, _hpre, _hoo, _hoc, _hvo, _hvc, _hocv⟩, hLLI, _hcur,
        _hkeep, _hconv, _hxn, hpair, hplt, _hbase, _hcap⟩ := hInv0
      obtain ⟨hlanes, _hprefix, _hcount, _husedle, _hplen⟩ := hLLI
      have hbridge := setLanes_eq_drop_of_inv hpair hplt hlanes
      have hdrop : (position.drop used).length = ctpop w := by
        rw [ctpop_eq_setLanes_length, hbridge]
      have hz : clearLow w 8 = 0 := by
        apply eq_zero_of_setLanes_nil
        rw [setLanes_clearLow w 8, hbridge,
          List.drop_eq_nil_of_le (as := position.drop used) (i := 8)
            (by rw [hdrop]; omega)]
      obtain ⟨e, hstep, hexit⟩ := lstWriter_step_exit blk0 xp xn xn0 position base
        used o s w hInv hz
      obtain ⟨e', hstep', hframe'⟩ := lstWriter_step_frame blk0 xp xn xn0 carry position
        base used o s w mem0 hInv hframe
      have heq : e = e' := by
        rw [hstep] at hstep'
        exact Ctrl.jump.inj hstep'
      subst e'
      have hcarry' : readBytes e.mem carry 16 = some carryBytes := by
        rw [lstWriter_step_carry blk0 xp xn xn0 carry position base used o s w hInv hcx hcarr e hstep]
        exact hcarry
      have hhas' : HasBytes e.mem xp (4 * blockMax xn0) :=
        lstWriter_step_presence blk0 xp xn xn0 position base used o s w hInv hhas e hstep
      refine ⟨e, 1, by omega, hexit, hframe', hcarry', hhas', fun m => ?_⟩
      rw [show 1 + m = m + 1 from by omega]
      exact runFuel_jump_calls hstep
  | succ r ih =>
      rintro used o s w hInv hframe hcarry hBnd hhas
      have hInv0 := hInv
      by_cases hz : clearLow w 8 = 0
      · obtain ⟨e, hstep, hexit⟩ := lstWriter_step_exit blk0 xp xn xn0 position base
          used o s w hInv hz
        obtain ⟨e', hstep', hframe'⟩ := lstWriter_step_frame blk0 xp xn xn0 carry position
          base used o s w mem0 hInv hframe
        have heq : e = e' := by
          rw [hstep] at hstep'
          exact Ctrl.jump.inj hstep'
        subst e'
        have hcarry' : readBytes e.mem carry 16 = some carryBytes := by
          rw [lstWriter_step_carry blk0 xp xn xn0 carry position base used o s w hInv hcx hcarr e hstep]
          exact hcarry
        have hhas' : HasBytes e.mem xp (4 * blockMax xn0) :=
          lstWriter_step_presence blk0 xp xn xn0 position base used o s w hInv hhas e hstep
        refine ⟨e, 1, by omega, hexit, hframe', hcarry', hhas', fun m => ?_⟩
        rw [show 1 + m = m + 1 from by omega]
        exact runFuel_jump_calls hstep
      · obtain ⟨e, hstep, hinv'⟩ := lstWriter_step_loop blk0 xp xn xn0 position base
          used o s w hInv hz
        obtain ⟨e', hstep', hframe'⟩ := lstWriter_step_frame blk0 xp xn xn0 carry position
          base used o s w mem0 hInv hframe
        have heq : e = e' := by
          rw [hstep] at hstep'
          exact Ctrl.jump.inj hstep'
        subst e'
        have hcarry' : readBytes e.mem carry 16 = some carryBytes := by
          rw [lstWriter_step_carry blk0 xp xn xn0 carry position base used o s w hInv hcx hcarr e hstep]
          exact hcarry
        have hb' : ctpop (clearLow w 8) ≤ 8 * r := by
          rw [ctpop_clearLow w 8]; omega
        have hhas' : HasBytes e.mem xp (4 * blockMax xn0) :=
          lstWriter_step_presence blk0 xp xn xn0 position base used o s w hInv hhas e hstep
        obtain ⟨e'', j', hj', hexit', hframe'', hcarry'', hhas'', hrun'⟩ :=
          ih (used + lstBatchCount w) (o + 4 * lstBatchCount w) e (clearLow w 8)
            hinv' hframe' hcarry' hb' hhas'
        refine ⟨e'', j' + 1, by omega, hexit', hframe'', hcarry'', hhas'', fun m => ?_⟩
        rw [show j' + 1 + m = (j' + m) + 1 from by omega, runFuel_jump_calls hstep]
        exact hrun' m


/-! ### Reading around the exit block's carry stores -/

/-- The zero word has no set lanes. -/
theorem setLanes_zero64 : setLanes (0 : BitVec 64) = [] := by
  simp [setLanes, getLsbD_zero_64]

/-- A read at a range outside the carry's sixteen bytes is unaffected by the exit
block's two stores. -/
theorem readBytes_lxMem2_off (mem : Mem) (bs w : BitVec 64) (carry a n : Nat)
    (h : a + n ≤ carry ∨ carry + 16 ≤ a) :
    readBytes (lxMem2 mem bs w carry) a n = readBytes mem a n := by
  unfold lxMem2 lxMem1
  rcases h with h | h
  · rw [readBytes_writeBytes_below _ _ n a (carry + 8) (by omega)]
    rw [readBytes_writeBytes_below _ _ n a carry h]
  · rw [readBytes_writeBytes_above _ _ n a (carry + 8)
      (by rw [natToBytes_length]; omega)]
    rw [readBytes_writeBytes_above _ _ n a carry
      (by rw [natToBytes_length]; omega)]

/-- The sixteen bytes the exit block's two stores leave at the carry slot: the
run-open word and the run-parity word, as `lxMem2` writes them. -/
def lxCarry (bs w : BitVec 64) : List UInt8 :=
  natToBytes (bs >>> 63).toNat 8 ++ natToBytes (((w &&& bs) >>> 63)).toNat 8

/-- Those sixteen bytes are exactly what the exit block's two stores read back. -/
theorem readBytes_lxMem2_carry (mem : Mem) (bs w : BitVec 64) (carry : Nat) :
    readBytes (lxMem2 mem bs w carry) carry 16 = some (lxCarry bs w) := by
  have h8a : readBytes (lxMem2 mem bs w carry) carry 8 =
      some (natToBytes (bs >>> 63).toNat 8) := by
    unfold lxMem2
    rw [readBytes_writeBytes_below _ _ 8 carry (carry + 8) (by omega)]
    exact readBytes_writeBytes_same _ _
  have h8b : readBytes (lxMem2 mem bs w carry) (carry + 8) 8 =
      some (natToBytes ((w &&& bs) >>> 63).toNat 8) := by
    unfold lxMem2
    exact readBytes_writeBytes_same _ _
  have hcomb := JsonEntrySteps.readBytes_append (lxMem2 mem bs w carry) 8 carry
    (natToBytes (bs >>> 63).toNat 8) 8 (natToBytes ((w &&& bs) >>> 63).toNat 8) h8a h8b
  rw [show (8 + 8 : Nat) = 16 from rfl] at hcomb
  simpa only [lxCarry] using hcomb

/-- Two memories that agree byte for byte over a range read the same range. -/
theorem readBytes_congr_range {m m' : Mem} {a n : Nat}
    (h : ∀ k, k < n → readByte m' (a + k) = readByte m (a + k)) :
    readBytes m' a n = readBytes m a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      have h0 : readByte m' a = readByte m a := by simpa using h 0 (by omega)
      simp only [readBytes]
      rw [h0]
      cases readByte m a with
      | none => rfl
      | some b =>
          rw [ih (a := a + 1) (fun k hk => by
            rw [show a + 1 + k = a + (k + 1) from by omega]
            exact h (k + 1) (by omega))]

/-- A read outside the inline batch's two stores is unaffected by them: the eight
entries at `o` and the count at `xn`, on either side of the read. -/
theorem readBytes_lstIfEnd4Mem_off (base : BitVec 32) (esc : BitVec 64) (o xn count : Nat)
    (mem : Mem) (n a : Nat)
    (h1 : a + n ≤ o ∨ o + 32 ≤ a)
    (h2 : a + n ≤ xn ∨ xn + 8 ≤ a) :
    readBytes (lstIfEnd4Mem base esc o xn count mem) a n = readBytes mem a n := by
  refine readBytes_congr_range (fun k hk => ?_)
  exact lstIfEnd4Mem_unchanged base esc o xn count mem
    (by rcases h1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    (by rcases h2 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))

/-! ### The exit block's successor, and what each arm has to establish -/

/-- The state the exit block leaves: the two carry stores, the position word, the
position base, and the branch the word selects. -/
def lxSuccessor (env : Env) (s : State) (bs ctl im blk0 w : BitVec 64) (carry : Nat) : State :=
  withEnv (lx9 env bs ctl im w blk0)
    { s with mem := lxMem2 s.mem bs w carry, pc := lxNext ctl im w,
             pre := some "xl_lanes.exit" }

/-- The record's memory claim, as one predicate over the final memory: the count,
the position stream, the carry pair the run stores, the presence of the extent the
record's exclusion names, and the frame.

The presence conjunct is what the successor reads: the record's exclusion lists
`(xp, 4 * blockMax xn0)` as touched, so a caller cannot carry a capacity across the
call by byte equality, and the bytes below the written span are present only because
the body only stores.  Its extent is exactly the exclusion's, because that is the
region the record declines to describe byte by byte. -/
def EscapeReach (blk0 : BitVec 64) (xp xn carry xn0 : Nat) (position : List Nat)
    (carryBytes : List UInt8) (mem0 M : Mem) : Prop :=
  readBytes M xn 8 = some (wordBytes 8 (xn0 + position.length)) ∧
  readBytes M (xp + 4 * xn0) (4 * position.length) =
    some (positionsBytes 4 (position.map fun k => blockAddr blk0 + k)) ∧
  readBytes M carry 16 = some carryBytes ∧
  HasBytes M xp (4 * blockMax xn0) ∧
  UnchangedOutside mem0 M (escapeRegions xp xn carry xn0)

/-- The carry region is a region. -/
theorem mem_escapeRegions_carry (xp xn carry xn0 : Nat) :
    (carry, 16) ∈ escapeRegions xp xn carry xn0 := by
  simp [escapeRegions]

/-- The count's region is a region. -/
theorem mem_escapeRegions_count (xp xn carry xn0 : Nat) :
    (xn, 8) ∈ escapeRegions xp xn carry xn0 := by
  simp [escapeRegions]

/-- The stream's capacity region is a region. -/
theorem mem_escapeRegions_stream (xp xn carry xn0 : Nat) :
    (xp, 4 * blockMax xn0) ∈ escapeRegions xp xn carry xn0 := by
  simp [escapeRegions]

/-- **The `lxWord = 0` arm.**  The exit block jumps straight to the emitter's
exit, so the run is the block's own step plus the return.  The stream is empty
because the position word is, and the count is the caller's because the carry's
stores are off its slot. -/
theorem exitSegment_zero {Γ : MemContract} (env : Env) (s : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hzero : lxWord ctl im w = 0)
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hcount : readBytes s.mem xn 8 = some (wordBytes 8 xn0))
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hframe : UnchangedOutside mem0 s.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes s.mem xp (4 * blockMax xn0)) :
    runFuel (escapeListCalls Γ) 1 escapeListFunction
        (lxSuccessor env s bs ctl im blk0 w carry) =
      some (.ret none (lxMem2 s.mem bs w carry)) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0
        (lxMem2 s.mem bs w carry) := by
  have hpc : (lxSuccessor env s bs ctl im blk0 w carry).pc = "xl_emit.exit" := by
    unfold lxSuccessor lxNext
    rw [ite_eq_left hzero]
    rfl
  have hrun := emit_exit_at (Γ := Γ) (lxSuccessor env s bs ctl im blk0 w carry) hpc
  have hpos : position = [] := by rw [← hbridge, hzero]; exact setLanes_zero64
  refine ⟨hrun, ?_⟩
  unfold EscapeReach
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpos, List.length_nil, Nat.add_zero]
    rw [readBytes_lxMem2_off s.mem bs w carry xn 8 (Or.symm hcarr)]
    exact hcount
  · rw [hpos]
    rfl
  · exact readBytes_lxMem2_carry s.mem bs w carry
  · exact hasBytes_lxMem2 hhas bs w carry
  · exact unchangedOutside_lxMem2
      ⟨(carry, 16), mem_escapeRegions_carry xp xn carry xn0, by omega, by omega⟩ hframe


/-! ### The exit block's environment, read back -/

/-- The block's position word, at the environment it leaves. -/
theorem lx9_and31 (env : Env) (bs ctl im w blk0 : BitVec 64) :
    lookupName (lx9 env bs ctl im w blk0) "%and31.i" =
      some (.int 64 (lxWord ctl im w)) := by
  lx_simp; lx_lk

/-- The block's position base, at the environment it leaves. -/
theorem lx9_conv (env : Env) (bs ctl im w blk0 : BitVec 64) :
    lookupName (lx9 env bs ctl im w blk0) "%conv" = some (.int 32 (lxBase blk0)) := by
  lx_simp; lx_lk

theorem lx9_xp (env : Env) (bs ctl im w blk0 : BitVec 64) :
    lookupName (lx9 env bs ctl im w blk0) "%xp" = lookupName env "%xp" := by
  lx_simp; lx_lk

theorem lx9_xn (env : Env) (bs ctl im w blk0 : BitVec 64) :
    lookupName (lx9 env bs ctl im w blk0) "%xn" = lookupName env "%xn" := by
  lx_simp; lx_lk

theorem lx9_carry (env : Env) (bs ctl im w blk0 : BitVec 64) :
    lookupName (lx9 env bs ctl im w blk0) "%carry" = lookupName env "%carry" := by
  lx_simp; lx_lk

/-! ### The batch arm: the position word is small, so the first batch is the whole
stream -/

/-- **The `xlWord ≠ 0`, `ctpop ≤ 8` arm.**  The exit block jumps to the first
batch, the batch writes its at-most-eight entries and the count, and the block's
own test sends the run to the emitter's exit.  The stream is the whole position
list because the batch's claim is the list's length. -/
theorem exitSegment_skip {Γ : MemContract} (env : Env) (s : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hne : lxWord ctl im w ≠ 0)
    (hskip : ¬ ctpop (lxWord ctl im w) > 8)
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes s.mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe : UnchangedOutside mem0 s.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes s.mem xp (4 * blockMax xn0)) :
    let M := lstIfEnd4Mem (lxBase blk0) (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry)
    runFuel (escapeListCalls Γ) 2 escapeListFunction
        (lxSuccessor env s bs ctl im blk0 w carry) = some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0 M := by
  intro M
  have hpcS : (lxSuccessor env s bs ctl im blk0 w carry).pc = "if.end.i4" := by
    unfold lxSuccessor lxNext
    rw [ite_eq_right hne]
    rfl
  have hes := lx9_and31 env bs ctl im w blk0
  have hconv := lx9_conv env bs ctl im w blk0
  have hxp' : lookupName (lx9 env bs ctl im w blk0) "%xp" = some (.ptr xp) := by
    rw [lx9_xp]; exact hxp
  have hxn' : lookupName (lx9 env bs ctl im w blk0) "%xn" = some (.ptr xn) := by
    rw [lx9_xn]; exact hxn
  have hld : readBytes (lxMem2 s.mem bs w carry) xn 8 = some (natToBytes xn0 8) := by
    rw [readBytes_lxMem2_off s.mem bs w carry xn 8 (Or.symm hcarr)]
    exact hcount
  have hrun : runFuel (escapeListCalls Γ) 2 escapeListFunction
      (lxSuccessor env s bs ctl im blk0 w carry) = some (.ret none M) := by
    refine batch_at (Γ := Γ) (env := lx9 env bs ctl im w blk0)
      (s := { s with mem := lxMem2 s.mem bs w carry, pc := lxNext ctl im w,
                       pre := some "xl_lanes.exit" })
      (esc := lxWord ctl im w) (base := lxBase blk0) (xp := xp) (xn := xn)
      (c0 := xn0) hpcS hes hconv hxp' hxn' hxn0 hld 1 ?_
    intro e hpcE hmemE _hkeeps _haddr _hcountcell
    have hpc' : e.pc = "xl_emit.exit" := by
      rw [hpcE]
      unfold lstIfEnd4Next
      rw [ite_eq_right hskip]
    have hret := emit_exit_at (Γ := Γ) e hpc'
    rw [hmemE] at hret
    exact hret
  refine ⟨hrun, ?_⟩
  unfold EscapeReach
  have hctp : ctpop (lxWord ctl im w) = position.length := by
    rw [← hbridge, ctpop_eq_setLanes_length]
  have hmin : min (ctpop (lxWord ctl im w)) 8 = ctpop (lxWord ctl im w) :=
    Nat.min_eq_left (by omega)
  have hcountEq : lstIfEnd4Count xn0 (lxWord ctl im w) = xn0 + position.length := by
    unfold lstIfEnd4Count
    rw [hmin, hctp]
  have hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32 := by
    rw [lxBase_toNat_eq blk0 hblkcap]; unfold blockAddr; omega
  have hdisj : xn + 8 ≤ xp + xn0 * 4 ∨ xp + xn0 * 4 + 32 ≤ xn := by
    rcases hkeep with h | h
    · left; omega
    · right
      have : xp + xn0 * 4 + 32 ≤ xp + 4 * blockMax xn0 := by
        unfold blockMax batchReserve; omega
      omega
  have hk : position.length ≤ min (ctpop (lxWord ctl im w)) 8 := by
    rw [hctp]
    exact Nat.le_min.mpr ⟨Nat.le_refl _, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lstIfEnd4Mem_count, hcountEq]
  · rw [Nat.mul_comm 4 xn0]
    rw [lstIfEnd4Mem_positions blk0 (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry)
      position.length hk hcap hdisj]
    rw [← hbridge, List.take_length, lxBase_toNat_eq blk0 hblkcap]
  · -- the pair the exit block stored survives the batch, since the batch's two
    -- stores lie outside the carry's sixteen bytes
    have h1 : carry + 16 ≤ xp + xn0 * 4 ∨ xp + xn0 * 4 + 32 ≤ carry := by
      rcases hcx with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by
          have : xp + xn0 * 4 + 32 ≤ xp + 4 * blockMax xn0 := by
            unfold blockMax batchReserve; omega
          omega)
    change readBytes (lstIfEnd4Mem (lxBase blk0) (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry)) carry 16 =
        some (lxCarry bs w)
    rw [readBytes_lstIfEnd4Mem_off (lxBase blk0) (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry) 16 carry h1
      hcarr]
    exact readBytes_lxMem2_carry s.mem bs w carry
  · exact hasBytes_lstIfEnd4Mem (hasBytes_lxMem2 hhas bs w carry) (lxBase blk0)
      (lxWord ctl im w) (xp + xn0 * 4) xn (lstIfEnd4Count xn0 (lxWord ctl im w))
  · refine unchangedOutside_lstIfEnd4Mem ?_ ?_ (unchangedOutside_lxMem2 ?_ hframe)
    · refine ⟨(xp, 4 * blockMax xn0), mem_escapeRegions_stream xp xn carry xn0,
        by omega, ?_⟩
      unfold blockMax batchReserve; omega
    · exact ⟨(xn, 8), mem_escapeRegions_count xp xn carry xn0, by omega, by omega⟩
    · exact ⟨(carry, 16), mem_escapeRegions_carry xp xn carry xn0, by omega, by omega⟩


/-! ### The writer arm's tail: the loop, the frame and the return -/

/-- A cleared word is non-zero while the word has more than eight set lanes. -/
theorem clearLow_ne_zero_of_ctpop_gt (w : BitVec 64) (h : 8 < ctpop w) :
    clearLow w 8 ≠ 0 := by
  intro hz
  have h1 := ctpop_clearLow w 8
  rw [hz, ctpop_zero64] at h1
  omega

/-- The first preheader does not bind `%add.ptr.i.i`. -/
theorem fp17_addptr (env : Env) (esc : BitVec 64) :
    lookupName (fp17 env esc) "%add.ptr.i.i" = lookupName env "%add.ptr.i.i" := by
  fp_simp; fp_lk

/-- **The writer's invariant at the batch's exit.**  The components `ListLoopInv`
and the writer's record are stated over are supplied separately and then
conjoined; refining a supplied term against the unfolded conjunction is what
times out. -/
theorem writerInv_of_batch (blk0 : BitVec 64) (xp xn xn0 : Nat) (position : List Nat)
    (esc : BitVec 64) (e1 : State)
    (hpc1 : e1.pc = "for.body.preheader.i.i")
    (haddr : lookupName e1.env "%add.ptr.i.i" = some (.ptr (xp + xn0 * 4)))
    (handi : lookupName e1.env "%and31.i" = some (.int 64 esc))
    (hconv1 : lookupName e1.env "%conv" = some (.int 32 (lxBase blk0)))
    (hxn1 : lookupName e1.env "%xn" = some (.ptr xn))
    (hprefix1 : readBytes e1.mem (xp + 4 * xn0) (4 * 8) =
      some (positionsBytes 4 ((position.take 8).map fun k => blockAddr blk0 + k)))
    (hcount1 : readBytes e1.mem xn 8 = some (wordBytes 8 (xn0 + 8)))
    (hgt : ctpop esc > 8)
    (hbridge : setLanes esc = position)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32) :
    lstWriterInv blk0 xp xn xn0 position (lxBase blk0) 8 (xp + 4 * xn0 + 32)
      (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4)) (clearLow esc 8) := by
  have hctp : ctpop esc = position.length := by
    rw [← hbridge, ctpop_eq_setLanes_length]
  have hlt64 : ∀ k ∈ position, k < 64 := by
    intro k hk
    rw [← hbridge] at hk
    exact (mem_setLanes.mp hk).1
  have hset : setLanes (clearLow esc 8) = position.drop 8 := by
    have h0 : setLanes esc = position.drop 0 := by rw [hbridge, List.drop_zero]
    have h := setLanes_clearLow_positions esc position 0 h0
    rwa [Nat.zero_add, Nat.min_eq_right (by omega)] at h
  have hlanes : ∀ k, k < 64 → (clearLow esc 8).getLsbD k =
      decide (k ∈ position.drop 8) :=
    lane_mem_of_setLanes hset (fun k hk => hlt64 k (List.mem_of_mem_drop hk))
  have hpair : position.Pairwise (· < ·) := by
    rw [← hbridge]; exact setLanes_pairwise esc
  have hplen : position.length ≤ 64 := by
    rw [← hbridge]; exact setLanes_length_le esc
  have hoo : evalOperand (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4))
      (.reg "%add.ptr5.i.i") = some (.ptr (xp + 4 * xn0 + 32)) := by
    show lookupName (wpEnv (fp17 e1.env esc) (xp + xn0 * 4)) "%add.ptr5.i.i" = _
    rw [show xp + 4 * xn0 + 32 = xp + xn0 * 4 + 32 from by omega]
    exact writerEntry_ptr e1.env esc (xp + xn0 * 4)
  have hw : evalOperand (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4))
      (.reg "%and.7.i.i") = some (.int 64 (clearLow esc 8)) := by
    show lookupName (wpEnv (fp17 e1.env esc) (xp + xn0 * 4)) "%and.7.i.i" = _
    exact writerEntry_and7 e1.env esc (xp + xn0 * 4)
  have hconv' : lookupName (wpEnv (fp17 e1.env esc) (xp + xn0 * 4)) "%conv" =
      some (.int 32 (lxBase blk0)) :=
    writerEntry_conv e1.env esc (xp + xn0 * 4) (lxBase blk0) hconv1
  have hxn' : lookupName (wpEnv (fp17 e1.env esc) (xp + xn0 * 4)) "%xn" =
      some (.ptr xn) :=
    writerEntry_xn e1.env esc (xp + xn0 * 4) xn hxn1
  refine writerInv_entry blk0 xp xn xn0 position (lxBase blk0) (xp + 4 * xn0 + 32)
    (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4)) (clearLow esc 8)
    rfl rfl hoo hw hlanes ?_ ?_ (by omega) hplen ?_ hkeep hconv' hxn' hpair hlt64 rfl hblkcap
  · exact hprefix1
  · exact hcount1
  · show xp + 4 * xn0 + 32 = xp + 4 * xn0 + 4 * 8
    omega

/-- **The writer loop and the return, with the frame.**  Ten control steps from
the writer's head, and the record's memory claim at the state the return leaves. -/
theorem writerTail (blk0 : BitVec 64) (xp xn xn0 carry : Nat)
    (position : List Nat) (base : BitVec 32) (mem0 : Mem) (s3 : State) (w : BitVec 64)
    (carryBytes : List UInt8)
    (hinv : lstWriterInv blk0 xp xn xn0 position base 8 (xp + 4 * xn0 + 32) s3 w)
    (hframe : UnchangedOutside mem0 s3.mem (escapeRegions xp xn carry xn0))
    (hcarry : readBytes s3.mem carry 16 = some carryBytes)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hhas : HasBytes s3.mem xp (4 * blockMax xn0)) :
    ∃ M, runFuel (escapeListCalls Γ_xl_batch) 10 escapeListFunction s3 =
        some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M := by
  have hct : ctpop w ≤ 8 * 8 := by
    have hinv0 := hinv
    obtain ⟨_hpc, _hphi, hLLI, _hcur, _hkeep, _hconv, _hxn, hpair, hplt, _hbase,
      _hcap⟩ := hinv0
    obtain ⟨hlanes, _hprefix, _hcount, husedle, hplen⟩ := hLLI
    have hbridge := setLanes_eq_drop_of_inv hpair hplt hlanes
    rw [ctpop_eq_setLanes_length, hbridge]
    have := List.length_drop (i := 8) (l := position)
    omega
  obtain ⟨e, j, hj, hexit, hframe', hcarry', hhas', hrun⟩ :=
    lstWriter_run_frame blk0 xp xn xn0 carry position base mem0 carryBytes hcx hcarr
      8 8 (xp + 4 * xn0 + 32) s3 w hinv hframe hcarry hct hhas
  have hret := emit_exit_at (Γ := Γ_xl_batch) e hexit.1
  have h1 : runFuel (escapeListCalls Γ_xl_batch) (j + 1) escapeListFunction s3 =
      some (.ret none e.mem) := by
    rw [hrun 1]
    exact hret
  exact ⟨e.mem, runFuel_mono_le (by omega) h1, hexit.2.1, hexit.2.2, hcarry', hhas', hframe'⟩

/-- **From the batch's exit to the return.**  Twelve control steps: the first
preheader, the second, then the writer loop and the return. -/
theorem writerHeadAt (blk0 : BitVec 64) (xp xn xn0 carry : Nat)
    (position : List Nat) (esc : BitVec 64) (e1 : State) (mem0 : Mem)
    (carryBytes : List UInt8)
    (hpc1 : e1.pc = "for.body.preheader.i.i")
    (haddr : lookupName e1.env "%add.ptr.i.i" = some (.ptr (xp + xn0 * 4)))
    (handi : lookupName e1.env "%and31.i" = some (.int 64 esc))
    (hconv1 : lookupName e1.env "%conv" = some (.int 32 (lxBase blk0)))
    (hxn1 : lookupName e1.env "%xn" = some (.ptr xn))
    (hprefix1 : readBytes e1.mem (xp + 4 * xn0) (4 * 8) =
      some (positionsBytes 4 ((position.take 8).map fun k => blockAddr blk0 + k)))
    (hcount1 : readBytes e1.mem xn 8 = some (wordBytes 8 (xn0 + 8)))
    (hgt : ctpop esc > 8)
    (hbridge : setLanes esc = position)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe1 : UnchangedOutside mem0 e1.mem (escapeRegions xp xn carry xn0))
    (hcarry1 : readBytes e1.mem carry 16 = some carryBytes)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hhas1 : HasBytes e1.mem xp (4 * blockMax xn0)) :
    ∃ M, runFuel (escapeListCalls Γ_xl_batch) 12 escapeListFunction e1 =
        some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M := by
  have hinv := writerInv_of_batch blk0 xp xn xn0 position esc e1 hpc1 haddr handi hconv1
    hxn1 hprefix1 hcount1 hgt hbridge hkeep hblkcap
  have hframe3 : UnchangedOutside mem0
      (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4)).mem
      (escapeRegions xp xn carry xn0) := hframe1
  have hcarry3 : readBytes
      (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4)).mem
      carry 16 = some carryBytes := hcarry1
  have hhas3 : HasBytes
      (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4)).mem
      xp (4 * blockMax xn0) := hhas1
  obtain ⟨M, hrun10, hreach⟩ :=
    writerTail blk0 xp xn xn0 carry position (lxBase blk0) mem0
      (wpSucc (fp17 e1.env esc) (fpSucc e1.env e1 esc) (xp + xn0 * 4))
      (clearLow esc 8) carryBytes hinv hframe3 hcarry3 hcx hcarr hhas3
  have hpc2 : (withEnv (fp17 e1.env esc) (fpSucc e1.env e1 esc)).pc =
      "while.body.preheader.i.i" := by
    show (fpSucc e1.env e1 esc).pc = "while.body.preheader.i.i"
    show fpNext esc = "while.body.preheader.i.i"
    unfold fpNext
    rw [ite_eq_right (clearLow_ne_zero_of_ctpop_gt esc hgt)]
  have haddr2 : lookupName (fp17 e1.env esc) "%add.ptr.i.i" = some (.ptr (xp + xn0 * 4)) := by
    rw [fp17_addptr]; exact haddr
  have hwhile : runFuel (escapeListCalls Γ_xl_batch) 11 escapeListFunction
      (fpSucc e1.env e1 esc) = some (.ret none M) :=
    whilePre_at (Γ := Γ_xl_batch) (env := fp17 e1.env esc) (s := fpSucc e1.env e1 esc)
      (o := xp + xn0 * 4) hpc2 haddr2 10 hrun10
  have hfor : runFuel (escapeListCalls Γ_xl_batch) 12 escapeListFunction e1 =
      some (.ret none M) :=
    forPre_at (Γ := Γ_xl_batch) (env := e1.env) (s := e1) (esc := esc)
      (by rw [withEnv_self]; exact hpc1) handi 11 hwhile
  exact ⟨M, hfor, hreach⟩

/-- **The writer arm.**  The position word has more than eight lanes, so the exit
block reaches the first batch, the two preheaders, the writer loop and the
return: thirteen control steps.  The record's memory claim comes from the writer's
exit, and the frame from the loop's own induction. -/
theorem exitSegment_writer (env : Env) (s : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hne : lxWord ctl im w ≠ 0)
    (hgt : ctpop (lxWord ctl im w) > 8)
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes s.mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe : UnchangedOutside mem0 s.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes s.mem xp (4 * blockMax xn0)) :
    ∃ M, runFuel (escapeListCalls Γ_xl_batch) 13 escapeListFunction
        (lxSuccessor env s bs ctl im blk0 w carry) = some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0 M := by
  have hpcS : (lxSuccessor env s bs ctl im blk0 w carry).pc = "if.end.i4" := by
    unfold lxSuccessor lxNext
    rw [ite_eq_right hne]
    rfl
  have hes := lx9_and31 env bs ctl im w blk0
  have hconv := lx9_conv env bs ctl im w blk0
  have hxp' : lookupName (lx9 env bs ctl im w blk0) "%xp" = some (.ptr xp) := by
    rw [lx9_xp]; exact hxp
  have hxn' : lookupName (lx9 env bs ctl im w blk0) "%xn" = some (.ptr xn) := by
    rw [lx9_xn]; exact hxn
  have hld : readBytes (lxMem2 s.mem bs w carry) xn 8 = some (natToBytes xn0 8) := by
    rw [readBytes_lxMem2_off s.mem bs w carry xn 8 (Or.symm hcarr)]
    exact hcount
  obtain ⟨e1, hstep1, hpc1, hmem1, hkeeps, haddr, hcountcell, _hcmp⟩ :=
    lstIfEnd4_step_calls (Γ := Γ_xl_batch) (lx9 env bs ctl im w blk0)
      { s with mem := lxMem2 s.mem bs w carry, pc := lxNext ctl im w,
               pre := some "xl_lanes.exit" }
      (lxWord ctl im w) (lxBase blk0) xp xn xn0 hpcS hes hconv hxp' hxn' hxn0 hld
  have hpc1' : e1.pc = "for.body.preheader.i.i" := by
    rw [hpc1]; unfold lstIfEnd4Next; rw [ite_eq_left hgt]
  have handi : lookupName e1.env "%and31.i" = some (.int 64 (lxWord ctl im w)) := by
    rw [hkeeps.andiReg]; exact hes
  have hconv1 : lookupName e1.env "%conv" = some (.int 32 (lxBase blk0)) := by
    rw [hkeeps.convReg]; exact hconv
  have hxn1 : lookupName e1.env "%xn" = some (.ptr xn) := by
    rw [hkeeps.xnReg]; exact hxn'
  have hctp : ctpop (lxWord ctl im w) = position.length := by
    rw [← hbridge, ctpop_eq_setLanes_length]
  have hmin : min (ctpop (lxWord ctl im w)) 8 = 8 := Nat.min_eq_right (by omega)
  have hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32 := by
    rw [lxBase_toNat_eq blk0 hblkcap]; unfold blockAddr; omega
  have hdisj : xn + 8 ≤ xp + xn0 * 4 ∨ xp + xn0 * 4 + 32 ≤ xn := by
    rcases hkeep with h | h
    · left; omega
    · right
      have : xp + xn0 * 4 + 32 ≤ xp + 4 * blockMax xn0 := by
        unfold blockMax batchReserve; omega
      omega
  have hprefix1 : readBytes e1.mem (xp + 4 * xn0) (4 * 8) =
      some (positionsBytes 4 ((position.take 8).map fun k => blockAddr blk0 + k)) := by
    rw [hmem1, Nat.mul_comm 4 xn0]
    rw [lstIfEnd4Mem_positions blk0 (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry) 8
      (Nat.le_min.mpr ⟨by omega, by omega⟩) hcap hdisj]
    rw [← hbridge, lxBase_toNat_eq blk0 hblkcap]
  have hcount1 : readBytes e1.mem xn 8 = some (wordBytes 8 (xn0 + 8)) := by
    rw [hmem1, lstIfEnd4Mem_count]
    have : lstIfEnd4Count xn0 (lxWord ctl im w) = xn0 + 8 := by
      unfold lstIfEnd4Count; rw [hmin]
    rw [this]
  have hframe1 : UnchangedOutside mem0 e1.mem (escapeRegions xp xn carry xn0) := by
    rw [hmem1]
    refine unchangedOutside_lstIfEnd4Mem ?_ ?_ (unchangedOutside_lxMem2 ?_ hframe)
    · refine ⟨(xp, 4 * blockMax xn0), mem_escapeRegions_stream xp xn carry xn0,
        by omega, ?_⟩
      unfold blockMax batchReserve; omega
    · exact ⟨(xn, 8), mem_escapeRegions_count xp xn carry xn0, by omega, by omega⟩
    · exact ⟨(carry, 16), mem_escapeRegions_carry xp xn carry xn0, by omega, by omega⟩
  have hcarry1 : readBytes e1.mem carry 16 = some (lxCarry bs w) := by
    rw [hmem1]
    have h1 : carry + 16 ≤ xp + xn0 * 4 ∨ xp + xn0 * 4 + 32 ≤ carry := by
      rcases hcx with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by
          have : xp + xn0 * 4 + 32 ≤ xp + 4 * blockMax xn0 := by
            unfold blockMax batchReserve; omega
          omega)
    rw [readBytes_lstIfEnd4Mem_off (lxBase blk0) (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 s.mem bs w carry) 16 carry h1
      hcarr]
    exact readBytes_lxMem2_carry s.mem bs w carry
  have hhas1 : HasBytes e1.mem xp (4 * blockMax xn0) := by
    rw [hmem1]
    exact hasBytes_lstIfEnd4Mem (hasBytes_lxMem2 hhas bs w carry) (lxBase blk0)
      (lxWord ctl im w) (xp + xn0 * 4) xn (lstIfEnd4Count xn0 (lxWord ctl im w))
  obtain ⟨M, hrun12, hreach⟩ :=
    writerHeadAt blk0 xp xn xn0 carry position (lxWord ctl im w) e1 mem0 (lxCarry bs w)
      hpc1' haddr handi hconv1 hxn1 hprefix1 hcount1 hgt hbridge hkeep hcx hblkcap
      hframe1 hcarry1 hcarr hhas1
  refine ⟨M, ?_, hreach⟩
  rw [show (13 : Nat) = 12 + 1 from by omega]
  unfold lxSuccessor
  rw [runFuel_jump_calls hstep1 (n := 12)]
  exact hrun12


/-! ### The continuation from the exit block, one lemma per arm

The exit block's `phi` supply is left to the caller: the two ways the block is
reached name different predecessors and different operands, and both are the same
word.  Each arm is stated at its own exact cost, because the record's fuel is a
term of the arguments and the count's population decides which arm runs. -/

/-- The `lxWord = 0` arm from the exit block: two control steps. -/
theorem exitCont_zero (env : Env) (e : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hpc : e.pc = "xl_lanes.exit")
    (henv : e.env = env)
    (hp : ∃ (p : String) (op : Operand), e.pre = some p ∧
      phiIncoming p lstExitIncoming = some op ∧
      evalOperand e op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8)))
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes e.mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe : UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes e.mem xp (4 * blockMax xn0))
    (hzero : lxWord ctl im w = 0) :
    runFuel (escapeListCalls Γ_xl_batch) 2 escapeListFunction e =
      some (.ret none (lxMem2 e.mem bs w carry)) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0
        (lxMem2 e.mem bs w carry) := by
  obtain ⟨p, op, hpre, hinc, hop⟩ := hp
  have hstate : withEnv env e = e := by rw [← henv, withEnv_self]
  have hop' : evalOperand (withEnv env e) op = some (.int 64 w) := by
    rw [hstate]; exact hop
  obtain ⟨h1, hreach⟩ :=
    exitSegment_zero (Γ := Γ_xl_batch) env e bs ctl im blk0 w carry xp xn xn0 position mem0
      hzero hbridge hcount hcarr hframe hhas
  have hem := emit_at (Γ := Γ_xl_batch) env e bs ctl im blk0 w carry p op
    hpc hpre hinc hop' hbs hctl him hblk hcarry harr 1
    (by simpa only [lxSuccessor] using h1)
  refine ⟨?_, hreach⟩
  rw [hstate] at hem
  rw [show (2 : Nat) = 1 + 1 from by omega]
  exact hem

/-- The small-word arm from the exit block: three control steps. -/
theorem exitCont_skip (env : Env) (e : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hpc : e.pc = "xl_lanes.exit")
    (henv : e.env = env)
    (hp : ∃ (p : String) (op : Operand), e.pre = some p ∧
      phiIncoming p lstExitIncoming = some op ∧
      evalOperand e op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8)))
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes e.mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe : UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes e.mem xp (4 * blockMax xn0))
    (hne : lxWord ctl im w ≠ 0)
    (hskip : ¬ ctpop (lxWord ctl im w) > 8) :
    let M := lstIfEnd4Mem (lxBase blk0) (lxWord ctl im w) (xp + xn0 * 4) xn
      (lstIfEnd4Count xn0 (lxWord ctl im w)) (lxMem2 e.mem bs w carry)
    runFuel (escapeListCalls Γ_xl_batch) 3 escapeListFunction e = some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0 M := by
  intro M
  obtain ⟨p, op, hpre, hinc, hop⟩ := hp
  have hstate : withEnv env e = e := by rw [← henv, withEnv_self]
  have hop' : evalOperand (withEnv env e) op = some (.int 64 w) := by
    rw [hstate]; exact hop
  obtain ⟨h2, hreach⟩ :=
    exitSegment_skip (Γ := Γ_xl_batch) env e bs ctl im blk0 w carry xp xn xn0 position mem0
      hne hskip hbridge hxn0 hxp hxn hcarr hcount hkeep hcx hblkcap hframe hhas
  have hem := emit_at (Γ := Γ_xl_batch) env e bs ctl im blk0 w carry p op
    hpc hpre hinc hop' hbs hctl him hblk hcarry harr 2
    (by simpa only [lxSuccessor] using h2)
  refine ⟨?_, hreach⟩
  rw [hstate] at hem
  rw [show (3 : Nat) = 1 + 2 from by omega]
  exact hem

/-- The writer arm from the exit block: fourteen control steps. -/
theorem exitCont_writer (env : Env) (e : State)
    (bs ctl im blk0 w : BitVec 64) (carry xp xn xn0 : Nat) (position : List Nat)
    (mem0 : Mem)
    (hpc : e.pc = "xl_lanes.exit")
    (henv : e.env = env)
    (hp : ∃ (p : String) (op : Operand), e.pre = some p ∧
      phiIncoming p lstExitIncoming = some op ∧
      evalOperand e op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8)))
    (hbridge : setLanes (lxWord ctl im w) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes e.mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hframe : UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0))
    (hhas : HasBytes e.mem xp (4 * blockMax xn0))
    (hne : lxWord ctl im w ≠ 0)
    (hgt : ctpop (lxWord ctl im w) > 8) :
    ∃ M, runFuel (escapeListCalls Γ_xl_batch) 14 escapeListFunction e = some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position (lxCarry bs w) mem0 M := by
  obtain ⟨p, op, hpre, hinc, hop⟩ := hp
  have hstate : withEnv env e = e := by rw [← henv, withEnv_self]
  have hop' : evalOperand (withEnv env e) op = some (.int 64 w) := by
    rw [hstate]; exact hop
  obtain ⟨M, h13, hreach⟩ :=
    exitSegment_writer env e bs ctl im blk0 w carry xp xn xn0 position mem0
      hne hgt hbridge hxn0 hxp hxn hcarr hcount hkeep hcx hblkcap hframe hhas
  have hem := emit_at (Γ := Γ_xl_batch) env e bs ctl im blk0 w carry p op
    hpc hpre hinc hop' hbs hctl him hblk hcarry harr 13
    (by simpa only [lxSuccessor] using h13)
  refine ⟨M, ?_, hreach⟩
  rw [hstate] at hem
  rw [show (14 : Nat) = 1 + 13 from by omega]
  exact hem

/-! ### The lanes loop with its memory and its predecessor

`lanes_run_calls` returns the exit state's word and its register frame, and
`lanes_mem_run_at` returns the memory — the first at `escapeCalls`, the second
without the predecessor the exit block's `phi` reads.  The exit block needs all
three at the call environment: `%carry`/`%arrayidx1` to store the outgoing carry,
the memory to read the count, and the predecessor to choose between `%e.1.i` and
`%or13.i`.  So the loop is re-closed once more, with the memory, the array slot and
the predecessor in the invariant. -/

/-- The lanes loop's invariant with the state's memory, its predecessor (the seed
chain's `if.end.i`, or the head's own block), and the array slot the exit block
reads. -/
def lstLanesInvC (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (mem : Mem)
    (i : Nat) (s : State) (w : BitVec 64) : Prop :=
  lstLanesInv bs prevb prevs env0 i s w ∧ s.mem = mem ∧
    (s.pre = some "if.end.i" ∨ s.pre = some "do.body.i") ∧
    lookupName s.env "%arrayidx1" = lookupName env0 "%arrayidx1"

/-- What the loop leaves, with the same three facts.  The predecessor is the
head's own block, because every state the head jumps to carries it. -/
def lstLanesExitC (env0 : Env) (mem : Mem) (s : State) (w : BitVec 64) : Prop :=
  lstLanesExitWord env0 s w ∧ s.mem = mem ∧ s.pre = some "do.body.i" ∧
    lookupName s.env "%arrayidx1" = lookupName env0 "%arrayidx1"

/-- The lanes loop as a `CarriedLoop` at the call environment, with the memory,
the predecessor and the array slot. -/
def lstLanesLoopC (Γ : MemContract) (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env)
    (mem : Mem) : CarriedLoop (escapeListCalls Γ) escapeListFunction where
  head := "do.body.i"
  exitBlock := "xl_lanes.exit"
  map := stepWord bs
  seed := escapeSeed bs prevb prevs
  N := 32
  Inv := lstLanesInvC bs prevb prevs env0 mem
  ExitWord := lstLanesExitC env0 mem
  step_exit := by
    intro i s w h hfix
    obtain ⟨hinv, hmem, _hpre, harr⟩ := h
    obtain ⟨hpc, hmask, ⟨p, op, hpre0, hinc, hop⟩, _hiter, _hbound, hkeeps⟩ := hinv
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre0 hop ⊢
    obtain ⟨hstep, hkeeps', _hmask', he, _hor⟩ :=
      lstDoBody_step_calls s.env s bs w p op env0 hpc hpre0 hinc hop hmask hkeeps
    refine ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, ?_⟩
    refine ⟨⟨he, hkeeps'⟩, hmem, rfl, ?_⟩
    show lookupName (ld5 s.env bs w) "%arrayidx1" = lookupName env0 "%arrayidx1"
    rw [ld5_arrayidx1]; exact harr
  step_loop := by
    intro i s w h hfix
    obtain ⟨hinv, hmem, _hpre, harr⟩ := h
    obtain ⟨hpc, hmask, ⟨p, op, hpre0, hinc, hop⟩, hiter, hbound, hkeeps⟩ := hinv
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre0 hop ⊢
    obtain ⟨hstep, hkeeps', hmask', he, hor⟩ :=
      lstDoBody_step_calls s.env s bs w p op env0 hpc hpre0 hinc hop hmask hkeeps
    have hi32 : i ≠ 32 := by
      intro h32
      refine hfix ?_
      rw [hiter, h32]
      exact stepN_32_is_fixed bs prevb prevs
    refine ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, ?_⟩
    refine ⟨⟨by simp only [hfix]; rfl, hmask',
      ⟨"do.body.i", .reg "%or23.i", rfl, ?_, ?_⟩, ?_, by omega, hkeeps'⟩, hmem,
      Or.inr rfl, ?_⟩
    · decide
    · show evalOperand (withEnv (ld5 s.env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) (.reg "%or23.i") =
        some (.int 64 (stepWord bs w))
      simpa only [withEnv, evalOperand] using hor
    · rw [hiter, stepN_succ]
    · show lookupName (ld5 s.env bs w) "%arrayidx1" = lookupName env0 "%arrayidx1"
      rw [ld5_arrayidx1]; exact harr
  word_iterate := by
    intro i s w h
    obtain ⟨hinv, _hmem, _hpre, _harr⟩ := h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := hinv
    rw [hiter, stepN_eq_iter]
  bound := by
    intro i s w h
    obtain ⟨hinv, _hmem, _hpre, _harr⟩ := h
    exact hinv.2.2.2.2.1
  fixed := by
    intro s w h
    obtain ⟨hinv, _hmem, _hpre, _harr⟩ := h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := hinv
    rw [hiter]
    exact stepN_32_is_fixed bs prevb prevs

/-- **The lanes loop's run with the memory and the predecessor.**  From iteration
`i` the run reaches `xl_lanes.exit` within `32 - i + 1` steps, leaving the rule's
word, the entry memory, the head's predecessor and the array slot, as a prefix of
any continuation. -/
theorem lanesRunC {Γ : MemContract} (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env)
    (mem : Mem) (i : Nat) (σ : State) (w : BitVec 64)
    (hinv : lstLanesInvC bs prevb prevs env0 mem i σ w) :
    ∃ (e : State) (j : Nat), j ≤ 32 - i + 1 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitC env0 mem e (specRunStarts bs (prevb && prevs)) ∧
      ∀ k, runFuel (escapeListCalls Γ) (j + k) escapeListFunction σ =
        runFuel (escapeListCalls Γ) k escapeListFunction e := by
  obtain ⟨e, j, d, hj, _hd, hpc, hexit, _hfix, hrun⟩ :=
    (lstLanesLoopC Γ bs prevb prevs env0 mem).run_from (32 - i) i σ w hinv rfl
  refine ⟨e, j, hj, hpc, ?_, hrun⟩
  have hword : iter (stepWord bs) d (escapeSeed bs prevb prevs) =
      specRunStarts bs (prevb && prevs) := by
    rw [← stepN_eq_iter]
    exact stepN_fixed_eq_specRunStarts bs prevb prevs d (by rwa [stepN_eq_iter])
  have hexit' : lstLanesExitC env0 mem e
      (iter (stepWord bs) d (escapeSeed bs prevb prevs)) := hexit
  rw [hword] at hexit'
  exact hexit'

/-- The loop from its head at iteration two: at most thirty-one steps. -/
theorem lanesRunC_at {Γ : MemContract} (bs : BitVec 64) (prevb prevs : Bool)
    (env0 : Env) (mem : Mem) (σ : State)
    (hinv : lstLanesInvC bs prevb prevs env0 mem 2 σ
      (stepN bs 2 (escapeSeed bs prevb prevs))) :
    ∃ (e : State) (j : Nat), j ≤ 31 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitC env0 mem e (specRunStarts bs (prevb && prevs)) ∧
      ∀ k, runFuel (escapeListCalls Γ) (j + k) escapeListFunction σ =
        runFuel (escapeListCalls Γ) k escapeListFunction e :=
  lanesRunC bs prevb prevs env0 mem 2 σ _ hinv


/-- The seed chain's exit test, at the second iterate: `%and17.i`'s value. -/
theorem em11_stepN (bs e0 : BitVec 64) :
    em11 bs e0 = ((stepN bs 2 e0 <<< 2) &&& (stepN bs 2 e0 ^^^ (-1))) &&& stepMask bs := by
  rw [em11_eq, em7_eq]
  rfl

/-! ### The exit state, bundled, and the seed chain's continuation -/

/-- What the exit block's continuation may assume about the state it starts at:
the predecessor's word, the block's environment, the memory, and the caller's
staging.  Bundled because the two ways the state is reached — the seed chain's
direct jump and the lanes loop — supply the same twelve facts. -/
def AtExit (env : Env) (e : State) (mem0 : Mem) (bs ctl im blk0 w : BitVec 64)
    (carry xp xn xn0 : Nat) : Prop :=
  e.pc = "xl_lanes.exit" ∧ e.env = env ∧ e.mem = mem0 ∧
  (∃ (p : String) (op : Operand), e.pre = some p ∧
    phiIncoming p lstExitIncoming = some op ∧ evalOperand e op = some (.int 64 w)) ∧
  lookupName env "%bs" = some (.int 64 bs) ∧
  lookupName env "%ctl" = some (.int 64 ctl) ∧
  lookupName env "%im" = some (.int 64 im) ∧
  lookupName env "%blk0" = some (.int 64 blk0) ∧
  lookupName env "%xp" = some (.ptr xp) ∧
  lookupName env "%xn" = some (.ptr xn) ∧
  lookupName env "%carry" = some (.ptr carry) ∧
  lookupName env "%arrayidx1" = some (.ptr (carry + 8)) ∧
  UnchangedOutside mem0 e.mem (escapeRegions xp xn carry xn0)

/-- **From the seed chain to the position list.**  Either the chain's second
doubling is already the fixed point — then it jumps straight to the exit block —
or the lanes loop runs from the head; both reach a state `AtExit` describes, and
the continuation is the same.  The bound is the loop's thirty-one plus the
continuation's own, which covers the direct jump too. -/
theorem runFromSeed (σ : State) (mem0 : Mem) (bs ctl im blk0 : BitVec 64)
    (prevb prevs : Bool) (xp xn carry xn0 : Nat) (position : List Nat) (K : Nat)
    (hpc : σ.pc = (if em11 bs (escapeSeed bs prevb prevs) = 0
      then "xl_lanes.exit" else "do.body.i"))
    (hpre : σ.pre = some "if.end.i")
    (hmemσ : σ.mem = mem0)
    (hbsσ : lookupName σ.env "%bs" = some (.int 64 bs))
    (hctlσ : lookupName σ.env "%ctl" = some (.int 64 ctl))
    (himσ : lookupName σ.env "%im" = some (.int 64 im))
    (hblkσ : lookupName σ.env "%blk0" = some (.int 64 blk0))
    (hxpσ : lookupName σ.env "%xp" = some (.ptr xp))
    (hxnσ : lookupName σ.env "%xn" = some (.ptr xn))
    (hcarryσ : lookupName σ.env "%carry" = some (.ptr carry))
    (harrσ : lookupName σ.env "%arrayidx1" = some (.ptr (carry + 8)))
    (hseed : lookupName σ.env "%or13.i" =
      some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs))))
    (hmask : lookupName σ.env "%and7.i" = some (.int 64 (stepMask bs)))
    (hbridge : setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes mem0 xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hcont : ∀ (env : Env) (e : State),
      AtExit env e mem0 bs ctl im blk0 (specRunStarts bs (prevb && prevs)) carry xp xn xn0 →
      ∃ (k : Nat) (M : Mem), k ≤ K ∧
        runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction e =
          some (.ret none M) ∧
        EscapeReach blk0 xp xn carry xn0 position
          (lxCarry bs (specRunStarts bs (prevb && prevs))) mem0 M) :
    ∃ (k : Nat) (M : Mem), k ≤ 31 + K ∧
      runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction σ = some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position
        (lxCarry bs (specRunStarts bs (prevb && prevs))) mem0 M := by
  by_cases hP : em11 bs (escapeSeed bs prevb prevs) = 0
  · have hpc' : σ.pc = "xl_lanes.exit" := by
      rw [hpc, ite_eq_left hP]
    have hfixP : stepWord bs (stepN bs 2 (escapeSeed bs prevb prevs)) =
        stepN bs 2 (escapeSeed bs prevb prevs) := by
      apply (stepWord_fixed_iff bs (stepN bs 2 (escapeSeed bs prevb prevs))).mp
      rw [em11_stepN] at hP
      exact hP
    have hspec : stepN bs 2 (escapeSeed bs prevb prevs) =
        specRunStarts bs (prevb && prevs) :=
      stepN_fixed_eq_specRunStarts bs prevb prevs 2 hfixP
    obtain ⟨k, M, hk, hrun, hreach⟩ := hcont σ.env σ
      ⟨hpc', rfl, hmemσ,
        ⟨"if.end.i", .reg "%or13.i", hpre, by decide, by
          show evalOperand σ (.reg "%or13.i") = some (.int 64 (specRunStarts bs (prevb && prevs)))
          show lookupName σ.env "%or13.i" = _
          rw [hseed, hspec]⟩,
        hbsσ, hctlσ, himσ, hblkσ, hxpσ, hxnσ, hcarryσ, harrσ, by
          rw [hmemσ]; exact fun a _ => rfl⟩
    exact ⟨k, M, by omega, hrun, hreach⟩
  · have hpc' : σ.pc = "do.body.i" := by
      rw [hpc, ite_eq_right hP]
    have hinvC : lstLanesInvC bs prevb prevs σ.env mem0 2 σ
        (stepN bs 2 (escapeSeed bs prevb prevs)) :=
      ⟨lstLanesInv_entry bs prevb prevs σ hpc' hpre hseed hmask, hmemσ,
        Or.inl hpre, rfl⟩
    obtain ⟨e, j, hj, hpcE, hexitE, hrunE⟩ :=
      lanesRunC_at (Γ := Γ_xl_batch) bs prevb prevs σ.env mem0 σ hinvC
    obtain ⟨k, M, hk, hrun, hreach⟩ := hcont e.env e
      ⟨hpcE, rfl, hexitE.2.1,
        ⟨"do.body.i", .reg "%e.1.i", hexitE.2.2.1, by decide, by
          show evalOperand e (.reg "%e.1.i") = some (.int 64 (specRunStarts bs (prevb && prevs)))
          exact hexitE.1.1⟩,
        hexitE.1.2.bsReg.trans hbsσ, hexitE.1.2.ctlReg.trans hctlσ,
        hexitE.1.2.imReg.trans himσ, hexitE.1.2.blk0Reg.trans hblkσ,
        hexitE.1.2.xpReg.trans hxpσ, hexitE.1.2.xnReg.trans hxnσ,
        hexitE.1.2.carryReg.trans hcarryσ, hexitE.2.2.2.trans harrσ, by
          rw [hexitE.2.1]; exact fun a _ => rfl⟩
    refine ⟨j + k, M, by omega, ?_, hreach⟩
    rw [hrunE k]
    exact hrun


/-! ### The budget

The record's fuel is the seed chain's three steps, the lanes loop's thirty-one,
the exit block's own step and the selected arm: two for the empty word, three for
a word of at most eight lanes, fourteen for the writer.  The largest is
`3 + 31 + 14 = 48`, and the term the record states is `41 + min (ctpop …) 8`: the
`41` covers the first two arms and the `min` raises the third to `49` exactly when
the position word has more than eight lanes, which is the condition that selects
it. -/

def escapePositionsBudget (args : List Value) (mem : Mem) : Nat :=
  match args with
  | [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 _, .ptr _, .ptr _, .ptr _] =>
      41 + min (ctpop ((bs ||| ctl) &&& im)) 8
  | _ => 41

/-- A filter's length is monotone under a pointwise implication. -/
theorem length_filter_le_of_imp (l : List Nat) (p q : Nat → Bool)
    (h : ∀ k ∈ l, p k = true → q k = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a t ih =>
      rw [List.filter_cons, List.filter_cons]
      have ht := ih (fun k hk => h k (List.mem_cons_of_mem a hk))
      by_cases hp : p a
      · have hq : q a = true := h a (by simp) hp
        rw [ite_eq_left hp, ite_eq_left hq, List.length_cons, List.length_cons]
        omega
      · rw [ite_eq_right hp]
        by_cases hq : q a
        · rw [ite_eq_left hq, List.length_cons]; omega
        · rw [ite_eq_right hq]; exact ht

/-- A lane-wise implication bounds the population count. -/
theorem ctpop_le_of_lane_imp {a b : BitVec 64}
    (h : ∀ k, k < 64 → a.getLsbD k = true → b.getLsbD k = true) :
    ctpop a ≤ ctpop b := by
  rw [ctpop_eq_setLanes_length, ctpop_eq_setLanes_length]
  unfold setLanes
  exact length_filter_le_of_imp _ _ _
    (fun k hk hp => h k (List.mem_range.mp hk) hp)

/-- The body's position word is inside the argument word the budget reads: the
loop's word is the block's run starts, whose lanes are all `%bs` lanes. -/
theorem lxWord_ctpop_le (bs ctl im : BitVec 64) (odd0 : Bool) :
    ctpop (lxWord ctl im (specRunStarts bs odd0)) ≤ ctpop ((bs ||| ctl) &&& im) := by
  apply ctpop_le_of_lane_imp
  intro k hk h
  rw [lxWord, BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_eq_true] at h
  obtain ⟨hor, himl⟩ := h
  rw [Bool.or_eq_true] at hor
  have hbsor : ((bs ||| ctl).getLsbD k) = true := by
    rw [BitVec.getLsbD_or, Bool.or_eq_true]
    rcases hor with hw | hc
    · left
      rw [specRunStarts_getLsbD hk, Bool.and_eq_true] at hw
      exact hw.1
    · right; exact hc
  rw [BitVec.getLsbD_and, hbsor, himl]
  exact Bool.and_self true

/-- **From the seed chain's exit state to the record's memory claim**, with the
budget met.  The three arms of the position word's test select the continuation
and its cost; the seeds' own cost is passed as `seedN`.  The capacity the caller
staged is handed to the arm as presence, because the arm reaches the exit state at
the caller's own memory: the lanes loop stores nothing, so `AtExit`'s
`s.mem = mem0` is what supplies it. -/
theorem finishSeed (args : List Value) (mem : Mem) (σ : State)
    (bs ctl im blk0 : BitVec 64) (prevb prevs : Bool)
    (xp xn carry xn0 : Nat) (position : List Nat) (seedN : Nat)
    (hseedN : seedN ≤ 3)
    (hb41 : 41 ≤ escapePositionsBudget args mem)
    (hb48 : ctpop (lxWord ctl im (specRunStarts bs (prevb && prevs))) > 8 →
      48 ≤ escapePositionsBudget args mem)
    (hpc : σ.pc = (if em11 bs (escapeSeed bs prevb prevs) = 0
      then "xl_lanes.exit" else "do.body.i"))
    (hpre : σ.pre = some "if.end.i")
    (hmemσ : σ.mem = mem)
    (hbsσ : lookupName σ.env "%bs" = some (.int 64 bs))
    (hctlσ : lookupName σ.env "%ctl" = some (.int 64 ctl))
    (himσ : lookupName σ.env "%im" = some (.int 64 im))
    (hblkσ : lookupName σ.env "%blk0" = some (.int 64 blk0))
    (hxpσ : lookupName σ.env "%xp" = some (.ptr xp))
    (hxnσ : lookupName σ.env "%xn" = some (.ptr xn))
    (hcarryσ : lookupName σ.env "%carry" = some (.ptr carry))
    (harrσ : lookupName σ.env "%arrayidx1" = some (.ptr (carry + 8)))
    (hseedV : lookupName σ.env "%or13.i" =
      some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs))))
    (hmaskV : lookupName σ.env "%and7.i" = some (.int 64 (stepMask bs)))
    (hbridge : setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))) = position)
    (hxn0 : xn0 < 2 ^ 63)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcount : readBytes mem xn 8 = some (wordBytes 8 xn0))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hhas : HasBytes mem xp (4 * blockMax xn0))
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32) :
    ∃ (k : Nat) (M : Mem), seedN + k ≤ escapePositionsBudget args mem ∧
      runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction σ =
        some (.ret none M) ∧
      EscapeReach blk0 xp xn carry xn0 position
          (lxCarry bs (specRunStarts bs (prevb && prevs))) mem M := by
  by_cases hzero : lxWord ctl im (specRunStarts bs (prevb && prevs)) = 0
  · have hcont : ∀ (env : Env) (e : State),
        AtExit env e mem bs ctl im blk0 (specRunStarts bs (prevb && prevs)) carry xp xn xn0 →
        ∃ (k : Nat) (M : Mem), k ≤ 2 ∧
          runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction e =
            some (.ret none M) ∧
          EscapeReach blk0 xp xn carry xn0 position
          (lxCarry bs (specRunStarts bs (prevb && prevs))) mem M := by
      intro env e ha
      obtain ⟨hpcE, henvE, hmemE, hpE, hbsE, hctlE, himE, hblkE, hxpE, hxnE,
        hcarryE, harrE, hframeE⟩ := ha
      have hcntE : readBytes e.mem xn 8 = some (wordBytes 8 xn0) := by
        rw [hmemE]; exact hcount
      have hhasE : HasBytes e.mem xp (4 * blockMax xn0) := by
        rw [hmemE]; exact hhas
      obtain ⟨hrunE, hreachE⟩ :=
        exitCont_zero env e bs ctl im blk0 (specRunStarts bs (prevb && prevs))
          carry xp xn xn0 position mem hpcE henvE hpE hbsE hctlE himE hblkE hxpE
          hxnE hcarryE harrE hbridge hxn0 hcarr hcntE hkeep hblkcap hframeE hhasE hzero
      exact ⟨2, lxMem2 e.mem bs (specRunStarts bs (prevb && prevs)) carry,
        Nat.le_refl 2, hrunE, hreachE⟩
    obtain ⟨k, M, hk, hrun, hreach⟩ :=
      runFromSeed σ mem bs ctl im blk0 prevb prevs xp xn carry xn0 position 2
        hpc hpre hmemσ hbsσ hctlσ himσ hblkσ hxpσ hxnσ hcarryσ harrσ hseedV hmaskV
        hbridge hxn0 hcarr hcount hkeep hcx hblkcap hcont
    exact ⟨k, M, by omega, hrun, hreach⟩
  · by_cases hgt : ctpop (lxWord ctl im (specRunStarts bs (prevb && prevs))) > 8
    · have hcont : ∀ (env : Env) (e : State),
          AtExit env e mem bs ctl im blk0 (specRunStarts bs (prevb && prevs)) carry xp xn xn0 →
          ∃ (k : Nat) (M : Mem), k ≤ 14 ∧
            runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction e =
              some (.ret none M) ∧
            EscapeReach blk0 xp xn carry xn0 position
          (lxCarry bs (specRunStarts bs (prevb && prevs))) mem M := by
        intro env e ha
        obtain ⟨hpcE, henvE, hmemE, hpE, hbsE, hctlE, himE, hblkE, hxpE, hxnE,
          hcarryE, harrE, hframeE⟩ := ha
        have hcntE : readBytes e.mem xn 8 = some (wordBytes 8 xn0) := by
          rw [hmemE]; exact hcount
        have hhasE : HasBytes e.mem xp (4 * blockMax xn0) := by
          rw [hmemE]; exact hhas
        obtain ⟨M', hrunE, hreachE⟩ :=
          exitCont_writer env e bs ctl im blk0 (specRunStarts bs (prevb && prevs))
            carry xp xn xn0 position mem hpcE henvE hpE hbsE hctlE himE hblkE hxpE
            hxnE hcarryE harrE hbridge hxn0 hcarr hcntE hkeep hcx hblkcap hframeE hhasE
            hzero hgt
        exact ⟨14, M', Nat.le_refl 14, hrunE, hreachE⟩
      obtain ⟨k, M, hk, hrun, hreach⟩ :=
        runFromSeed σ mem bs ctl im blk0 prevb prevs xp xn carry xn0 position 14
          hpc hpre hmemσ hbsσ hctlσ himσ hblkσ hxpσ hxnσ hcarryσ harrσ hseedV hmaskV
          hbridge hxn0 hcarr hcount hkeep hcx hblkcap hcont
      exact ⟨k, M, by omega, hrun, hreach⟩
    · have hcont : ∀ (env : Env) (e : State),
          AtExit env e mem bs ctl im blk0 (specRunStarts bs (prevb && prevs)) carry xp xn xn0 →
          ∃ (k : Nat) (M : Mem), k ≤ 3 ∧
            runFuel (escapeListCalls Γ_xl_batch) k escapeListFunction e =
              some (.ret none M) ∧
            EscapeReach blk0 xp xn carry xn0 position
          (lxCarry bs (specRunStarts bs (prevb && prevs))) mem M := by
        intro env e ha
        obtain ⟨hpcE, henvE, hmemE, hpE, hbsE, hctlE, himE, hblkE, hxpE, hxnE,
          hcarryE, harrE, hframeE⟩ := ha
        have hcntE : readBytes e.mem xn 8 = some (wordBytes 8 xn0) := by
          rw [hmemE]; exact hcount
        have hhasE : HasBytes e.mem xp (4 * blockMax xn0) := by
          rw [hmemE]; exact hhas
        obtain ⟨hrunE, hreachE⟩ :=
          exitCont_skip env e bs ctl im blk0 (specRunStarts bs (prevb && prevs))
            carry xp xn xn0 position mem hpcE henvE hpE hbsE hctlE himE hblkE hxpE
            hxnE hcarryE harrE hbridge hxn0 hcarr hcntE hkeep hcx hblkcap hframeE hhasE
            hzero hgt
        exact ⟨3, _, Nat.le_refl 3, hrunE, hreachE⟩
      obtain ⟨k, M, hk, hrun, hreach⟩ :=
        runFromSeed σ mem bs ctl im blk0 prevb prevs xp xn carry xn0 position 3
          hpc hpre hmemσ hbsσ hctlσ himσ hblkσ hxpσ hxnσ hcarryσ harrσ hseedV hmaskV
          hbridge hxn0 hcarr hcount hkeep hcx hblkcap hcont
      exact ⟨k, M, by omega, hrun, hreach⟩


/-! ### The seed environments' array slot -/

theorem seedExit_entry_arr (env : Env) (bs w0 e0 : BitVec 64) (carry : Nat) :
    lookupName (ie13 (entryEnv env bs w0 carry) bs e0) "%arrayidx1" =
      some (.ptr (carry + 8)) := by
  env_simp; lk

theorem seedExit_then_arr (env : Env) (bs w0 w1 e0 andI : BitVec 64) (carry a : Nat) :
    lookupName (ie13 (ifThenEnv (entryEnv env bs w0 carry) bs w1 andI) bs e0)
        "%arrayidx1" = some (.ptr (carry + 8)) := by
  env_simp; lk

/-! ### The carry the run stores, in the record's vocabulary

The run's two stores are `>>> 63` words; the record names the pair the mask unit
writes, `(IsBackslashB (hi 31), (carry64 lo hi st).oddRun)`.  The lemmas below are
the bridge, one per word, plus the consistency `carryPair` asks of its state.
-/

/-- `x >>> 63` as the value of the top lane: zero or one, the top bit. -/
theorem ushr63_toNat (x : BitVec 64) :
    (x >>> 63).toNat = if x.getLsbD 63 then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have htb : x.getLsbD 63 = x.toNat.testBit 63 := rfl
  rw [htb]
  unfold Nat.testBit
  have hlt : x.toNat / 2 ^ 63 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)]
    rw [show 2 * 2 ^ 63 = 2 ^ 64 from by decide]
    exact x.isLt
  have hone : (1 : Nat) &&& (x.toNat >>> 63) = x.toNat / 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.mod_eq_of_lt hlt]
  rw [hone]
  by_cases h : x.toNat / 2 ^ 63 = 1
  · rw [if_pos (by rw [h]; decide), h]
  · have h0 : x.toNat / 2 ^ 63 = 0 := by omega
    rw [if_neg (by rw [h0]; decide), h0]

/-- The specification's outgoing carry is the fold over the block's sixty-four
bytes. -/
theorem carry64_eq_classCarryAt (lo hi : Block32) (st : ClassState) :
    carry64 lo hi st = classCarryAt (block64 lo hi) st 64 := by
  unfold carry64 block64
  rw [classWindow_carry, classWindow_carry]
  simpa only [List.length_ofFn] using
    (classCarryAt_append (List.ofFn lo) (List.ofFn hi) st 32).symm

/-- The parity one lane past the block's last, read at the last byte. -/
theorem parityAt_block64_succ (lo hi : Block32) (st : ClassState) :
    parityAt (block64 lo hi) st.oddRun 64 =
      if IsBackslashB (hi ⟨31, by decide⟩) then
        !parityAt (block64 lo hi) st.oddRun 63 else false := by
  show (match (block64 lo hi)[63]? with
    | some b => if IsBackslashB b then !parityAt (block64 lo hi) st.oddRun 63 else false
    | none => parityAt (block64 lo hi) st.oddRun 63) = _
  rw [block64_getElem?_hi (by decide : 31 < 32),
    ofFn_getElem?_of_lt (by decide : 31 < 32)]

/-- The outgoing parity, from the block's last byte. -/
theorem carry64_oddRun_eq (lo hi : Block32) (st : ClassState) :
    (carry64 lo hi st).oddRun =
      if IsBackslashB (hi ⟨31, by decide⟩) then
        !parityAt (block64 lo hi) st.oddRun 63 else false := by
  rw [carry64_eq_classCarryAt, classCarryAt_oddRun, parityAt_block64_succ]

/-- The state consistency `carryPair` carries: the outgoing parity is the last
byte's backslash bit conjoined with itself. -/
theorem carry64_oddRun_and_self (lo hi : Block32) (st : ClassState) :
    (carry64 lo hi st).oddRun =
      (IsBackslashB (hi ⟨31, by decide⟩) && (carry64 lo hi st).oddRun) := by
  rw [carry64_oddRun_eq]
  cases h : IsBackslashB (hi ⟨31, by decide⟩) <;> simp [h]

/-- The run's two stored words are the record's pair: the last byte's backslash
bit and the outgoing parity, which are `carrySlot`'s first two words. -/
theorem lxCarry_spec (lo hi : Block32) (st : ClassState) (prevb prevs : Bool)
    (hodd : st.oddRun = (prevb && prevs)) :
    lxCarry (specBackslash64 lo hi st)
        (specRunStarts (specBackslash64 lo hi st) (prevb && prevs)) =
      flagBytes (IsBackslashB (hi ⟨31, by decide⟩)) ++
        flagBytes (carry64 lo hi st).oddRun := by
  unfold lxCarry flagBytes
  rw [ushr63_toNat, ushr63_toNat]
  have hb63 : (specBackslash64 lo hi st).getLsbD 63 =
      IsBackslashB (hi ⟨31, by decide⟩) := by
    rw [show 63 = 31 + 32 from by decide]
    exact specBackslash64_getLsbD_hi (by decide)
  rw [hb63]
  have hw63 : ((specRunStarts (specBackslash64 lo hi st) (prevb && prevs)) &&&
      (specBackslash64 lo hi st)).getLsbD 63 =
      (IsBackslashB (hi ⟨31, by decide⟩) && (carry64 lo hi st).oddRun) := by
    rw [BitVec.getLsbD_and, specRunStarts_getLsbD (by decide), hb63, ← hodd,
      parityBit_specBackslash64 lo hi st 63 (by omega), carry64_oddRun_eq]
    cases h : IsBackslashB (hi ⟨31, by decide⟩) <;> simp [h]
  rw [hw63, ← carry64_oddRun_and_self lo hi st]

/-! ### The record's instance -/

/-- **The escape position list refines its specification.**  From a staging the
record admits at the caller's document base `base`, the run of the pinned entry point
completes at the record's budget and every behaviour it has satisfies the record's
post: the count advanced by the block's positions, the positions written at the
stream cursor, and every byte outside the three regions unchanged. -/
theorem escape_positions_satisfies (base : Nat) :
    Satisfies (escapeListCalls Γ_xl_batch) escapeListFunction
      (Γ_escape_positions base escapePositionsBudget) := by
  intro args mem next hpre
  obtain ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, prevb, prevs, xn0,
    hargs, hblock, hbs, hctl, him, hpair, hcount, hxn0, hdisj, hcarr, hcx,
    hhas, hblkcap⟩ := hpre
  have hodd : st.oddRun = (prevb && prevs) := hpair.2
  have hcarry : readBytes mem carry 16 = some (flagBytes prevb ++ flagBytes prevs) := hpair.1
  subst hargs
  let args : List Value :=
    [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn, .ptr carry]
  have hEbs : lookupName (EntryState escapeListFunction args mem next).env "%bs" =
      some (.int 64 bs) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hEctl : lookupName (EntryState escapeListFunction args mem next).env "%ctl" =
      some (.int 64 ctl) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hEim : lookupName (EntryState escapeListFunction args mem next).env "%im" =
      some (.int 64 im) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hEblk : lookupName (EntryState escapeListFunction args mem next).env "%blk0" =
      some (.int 64 blk0) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hExp : lookupName (EntryState escapeListFunction args mem next).env "%xp" =
      some (.ptr xp) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hExn : lookupName (EntryState escapeListFunction args mem next).env "%xn" =
      some (.ptr xn) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hEcarry : lookupName (EntryState escapeListFunction args mem next).env "%carry" =
      some (.ptr carry) := by
    simp [args, EntryState, escapeListFunction, List.zip, List.map, List.zipWith] <;>
      first | rfl | lk
  have hcw := carry_words hcarry
  let position := escapePositionsFrom (block64 lo hi) st
  have hbridge : setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))) =
      position := by
    show setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))) =
      escapePositionsFrom (block64 lo hi) st
    rw [hbs, hctl, him, ← hodd, lxWord_specPositionWord]
    exact setLanes_specPositionWord
  have hbudget : escapePositionsBudget args mem =
      41 + min (ctpop ((bs ||| ctl) &&& im)) 8 := by
    simp [args, escapePositionsBudget]
  have hb41 : 41 ≤ escapePositionsBudget args mem := by
    rw [hbudget]; omega
  have hb48 : ctpop (lxWord ctl im (specRunStarts bs (prevb && prevs))) > 8 →
      48 ≤ escapePositionsBudget args mem := by
    intro hgt
    rw [hbudget]
    have hle := lxWord_ctpop_le bs ctl im (prevb && prevs)
    have hmin : min (ctpop ((bs ||| ctl) &&& im)) 8 = 8 :=
      Nat.min_eq_right (by omega)
    omega
  by_cases hz0 : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) = 0
  · let σ : State :=
      site (ie13 (entryEnv (EntryState escapeListFunction args mem next).env bs
              (prevBackslashWord prevb) carry) bs (escapeSeed bs prevb prevs))
        (EntryState escapeListFunction args mem next)
        (if em11 bs (escapeSeed bs prevb prevs) = 0 then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")
    have hLRun : LRunC (escapeListCalls Γ_xl_batch) escapeListFunction 2
        (EntryState escapeListFunction args mem next) σ :=
      seed_entry_run_calls (Γ := Γ_xl_batch)
        (EntryState escapeListFunction args mem next).env
        (EntryState escapeListFunction args mem next) none bs prevb prevs carry
        hEbs hEcarry hcw.1 hz0
    obtain ⟨hbσ, hcσ, hiσ, hkσ, hxpσ, hxnσ, hcarσ, hand7σ, hor13σ⟩ :=
      seedExit_entry_cells (EntryState escapeListFunction args mem next).env bs
        (prevBackslashWord prevb) (escapeSeed bs prevb prevs) carry
        hEbs hEctl hEim hEblk hExp hExn hEcarry
    have haσ : lookupName σ.env "%arrayidx1" = some (.ptr (carry + 8)) :=
      seedExit_entry_arr (EntryState escapeListFunction args mem next).env bs
        (prevBackslashWord prevb) (escapeSeed bs prevb prevs) carry
    have hseedV : lookupName σ.env "%or13.i" =
        some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs))) := by
      show lookupName (ie13 (entryEnv (EntryState escapeListFunction args mem next).env bs
        (prevBackslashWord prevb) carry) bs (escapeSeed bs prevb prevs)) "%or13.i" = _
      rw [hor13σ, em7_eq]
      rfl
    have hpcσ : σ.pc = (if em11 bs (escapeSeed bs prevb prevs) = 0
        then "xl_lanes.exit" else "do.body.i") := rfl
    have hpreσ : σ.pre = some "if.end.i" := rfl
    have hmemσ : σ.mem = mem := rfl
    obtain ⟨k, M, hb, hrun, hreach⟩ :=
      finishSeed args mem σ bs ctl im blk0 prevb prevs xp xn carry xn0 position 2
        (by omega) hb41 hb48 hpcσ hpreσ hmemσ hbσ hcσ hiσ hkσ hxpσ hxnσ hcarσ haσ
        hseedV hand7σ hbridge hxn0 hcarr hcount hdisj hcx hhas hblkcap
    have hcomp : runFuel (escapeListCalls Γ_xl_batch) (escapePositionsBudget args mem)
        escapeListFunction (EntryState escapeListFunction args mem next) =
          some (.ret none M) :=
      runFuel_mono_le hb (by rw [LRunC.runFuel hLRun k]; exact hrun)
    refine ⟨⟨none, M, hcomp⟩, ?_⟩
    intro o ho
    rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
    · cases runFuel_outcome_unique hn hcomp
    · have ho' : o = .ret none M := runFuel_outcome_unique hn hcomp
      subst ho'
      have hout : carryPair M carry (carry64 lo hi st)
          (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi st).oddRun := by
        have hcarryEq : flagBytes (IsBackslashB (hi ⟨31, by decide⟩)) ++
            flagBytes (carry64 lo hi st).oddRun =
              lxCarry bs (specRunStarts bs (prevb && prevs)) := by
          rw [hbs]
          exact (lxCarry_spec lo hi st prevb prevs hodd).symm
        refine ⟨?_, carry64_oddRun_and_self lo hi st⟩
        rw [hcarryEq]
        exact hreach.2.2.1
      exact ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, prevb, prevs, xn0,
        rfl, hblock, hbs, hctl, him, hpair, hcount,
        hreach.1, hreach.2.1, hout, hreach.2.2.2.1, hreach.2.2.2.2⟩
  · let σ : State :=
      site (ie13 (ifThenEnv (entryEnv (EntryState escapeListFunction args mem next).env bs
              (prevBackslashWord prevb) carry) bs (prevBackslashWord prevs)
              (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) bs
          (escapeSeed bs prevb prevs))
        (EntryState escapeListFunction args mem next)
        (if em11 bs (escapeSeed bs prevb prevs) = 0 then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")
    have hLRun : LRunC (escapeListCalls Γ_xl_batch) escapeListFunction 3
        (EntryState escapeListFunction args mem next) σ :=
      seed_then_run_calls (Γ := Γ_xl_batch)
        (EntryState escapeListFunction args mem next).env
        (EntryState escapeListFunction args mem next) none bs prevb prevs carry
        hEbs hEcarry hcw.1 hcw.2 hz0
    obtain ⟨hbσ, hcσ, hiσ, hkσ, hxpσ, hxnσ, hcarσ, hand7σ, hor13σ⟩ :=
      seedExit_then_cells (EntryState escapeListFunction args mem next).env bs
        (prevBackslashWord prevb) (prevBackslashWord prevs) (escapeSeed bs prevb prevs)
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))) carry
        hEbs hEctl hEim hEblk hExp hExn hEcarry
    have haσ : lookupName σ.env "%arrayidx1" = some (.ptr (carry + 8)) :=
      seedExit_then_arr (EntryState escapeListFunction args mem next).env bs
        (prevBackslashWord prevb) (prevBackslashWord prevs) (escapeSeed bs prevb prevs)
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))) carry (carry + 8)
    have hseedV : lookupName σ.env "%or13.i" =
        some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs))) := by
      show lookupName (ie13 (ifThenEnv (entryEnv (EntryState escapeListFunction args mem next).env
        bs (prevBackslashWord prevb) carry) bs (prevBackslashWord prevs)
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) bs
        (escapeSeed bs prevb prevs)) "%or13.i" = _
      rw [hor13σ, em7_eq]
      rfl
    have hpcσ : σ.pc = (if em11 bs (escapeSeed bs prevb prevs) = 0
        then "xl_lanes.exit" else "do.body.i") := rfl
    have hpreσ : σ.pre = some "if.end.i" := rfl
    have hmemσ : σ.mem = mem := rfl
    obtain ⟨k, M, hb, hrun, hreach⟩ :=
      finishSeed args mem σ bs ctl im blk0 prevb prevs xp xn carry xn0 position 3
        (by omega) hb41 hb48 hpcσ hpreσ hmemσ hbσ hcσ hiσ hkσ hxpσ hxnσ hcarσ haσ
        hseedV hand7σ hbridge hxn0 hcarr hcount hdisj hcx hhas hblkcap
    have hcomp : runFuel (escapeListCalls Γ_xl_batch) (escapePositionsBudget args mem)
        escapeListFunction (EntryState escapeListFunction args mem next) =
          some (.ret none M) :=
      runFuel_mono_le hb (by rw [LRunC.runFuel hLRun k]; exact hrun)
    refine ⟨⟨none, M, hcomp⟩, ?_⟩
    intro o ho
    rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
    · cases runFuel_outcome_unique hn hcomp
    · have ho' : o = .ret none M := runFuel_outcome_unique hn hcomp
      subst ho'
      have hout : carryPair M carry (carry64 lo hi st)
          (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi st).oddRun := by
        have hcarryEq : flagBytes (IsBackslashB (hi ⟨31, by decide⟩)) ++
            flagBytes (carry64 lo hi st).oddRun =
              lxCarry bs (specRunStarts bs (prevb && prevs)) := by
          rw [hbs]
          exact (lxCarry_spec lo hi st prevb prevs hodd).symm
        refine ⟨?_, carry64_oddRun_and_self lo hi st⟩
        rw [hcarryEq]
        exact hreach.2.2.1
      exact ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, prevb, prevs, xn0,
        rfl, hblock, hbs, hctl, him, hpair, hcount,
        hreach.1, hreach.2.1, hout, hreach.2.2.2.1, hreach.2.2.2.2⟩

/-! ### Axiom footprints

Two carriers appear below and each is named once.  `Classical.choice` reaches the
count's store and readback through `natToBytes_mod_pow`, whose carrier is the
repository's `Nat.mod_mul_right_div_self` (the same carrier the writer's own pins
name); it reaches the zero word's lane arithmetic through `ctpop_zero64`, which is
`setLanes`'s `List.getLsbD` route at the zero word.  No declaration here adds an
axiom: `escape_positions_satisfies` carries exactly the union of its pieces',
which is those two carriers and `propext`/`Quot.sound`.
-/

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsFrom_pairwise

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapePositionsFrom_length_le

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_lt_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsFrom_lt_block

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_length_le_block' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapePositionsFrom_length_le_block

/-- info: 'LeanLLVM.Vellum.lxWord_specPositionWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lxWord_specPositionWord

/-- info: 'LeanLLVM.Vellum.ctpop_lxWord_positionWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ctpop_lxWord_positionWord

/-- info: 'LeanLLVM.Vellum.escapeRegions' does not depend on any axioms -/
#guard_msgs in
#print axioms escapeRegions

/-- info: 'LeanLLVM.Vellum.outside_region_lt_or_le' does not depend on any axioms -/
#guard_msgs in
#print axioms outside_region_lt_or_le

/-- info: 'LeanLLVM.Vellum.unchangedOutside_writeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unchangedOutside_writeBytes

/-- info: 'LeanLLVM.Vellum.unchangedOutside_batchMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unchangedOutside_batchMem

/-- info: 'LeanLLVM.Vellum.unchangedOutside_inlWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unchangedOutside_inlWrites

/-- info: 'LeanLLVM.Vellum.unchangedOutside_lstIfEnd4Mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unchangedOutside_lstIfEnd4Mem

/-- info: 'LeanLLVM.Vellum.unchangedOutside_lxMem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unchangedOutside_lxMem2

/-- info: 'LeanLLVM.Vellum.hasBytes_inlWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_inlWrites

/-- info: 'LeanLLVM.Vellum.hasBytes_lstIfEnd4Mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_lstIfEnd4Mem

/-- info: 'LeanLLVM.Vellum.hasBytes_batchMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_batchMem

/-- info: 'LeanLLVM.Vellum.hasBytes_lxMem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_lxMem2

/-- info: 'LeanLLVM.Vellum.lstWriter_step_presence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstWriter_step_presence

/-- info: 'LeanLLVM.Vellum.writerInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerInv_entry

/-- info: 'LeanLLVM.Vellum.lstWriter_step_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstWriter_step_mem

/-- info: 'LeanLLVM.Vellum.writerBatch_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerBatch_region

/-- info: 'LeanLLVM.Vellum.writerCount_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerCount_region

/-- info: 'LeanLLVM.Vellum.lstWriter_step_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstWriter_step_frame

/-- info: 'LeanLLVM.Vellum.lstWriter_run_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstWriter_run_frame

/-- info: 'LeanLLVM.Vellum.setLanes_zero64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setLanes_zero64

/-- info: 'LeanLLVM.Vellum.readBytes_lxMem2_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_lxMem2_off

/-- info: 'LeanLLVM.Vellum.lxSuccessor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lxSuccessor

/-- info: 'LeanLLVM.Vellum.EscapeReach' does not depend on any axioms -/
#guard_msgs in
#print axioms EscapeReach

/-- info: 'LeanLLVM.Vellum.mem_escapeRegions_carry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_escapeRegions_carry

/-- info: 'LeanLLVM.Vellum.mem_escapeRegions_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_escapeRegions_count

/-- info: 'LeanLLVM.Vellum.mem_escapeRegions_stream' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_escapeRegions_stream

/-- info: 'LeanLLVM.Vellum.exitSegment_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitSegment_zero

/-- info: 'LeanLLVM.Vellum.lx9_and31' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lx9_and31

/-- info: 'LeanLLVM.Vellum.lx9_conv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lx9_conv

/-- info: 'LeanLLVM.Vellum.lx9_xp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lx9_xp

/-- info: 'LeanLLVM.Vellum.lx9_xn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lx9_xn

/-- info: 'LeanLLVM.Vellum.lx9_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lx9_carry

/-- info: 'LeanLLVM.Vellum.exitSegment_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitSegment_skip

/-- info: 'LeanLLVM.Vellum.clearLow_ne_zero_of_ctpop_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearLow_ne_zero_of_ctpop_gt

/-- info: 'LeanLLVM.Vellum.fp17_addptr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fp17_addptr

/-- info: 'LeanLLVM.Vellum.writerInv_of_batch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writerInv_of_batch

/-- info: 'LeanLLVM.Vellum.writerTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms writerTail

/-- info: 'LeanLLVM.Vellum.writerHeadAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms writerHeadAt

/-- info: 'LeanLLVM.Vellum.exitSegment_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitSegment_writer

/-- info: 'LeanLLVM.Vellum.exitCont_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitCont_zero

/-- info: 'LeanLLVM.Vellum.exitCont_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitCont_skip

/-- info: 'LeanLLVM.Vellum.exitCont_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exitCont_writer

/-- info: 'LeanLLVM.Vellum.lstLanesInvC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesInvC

/-- info: 'LeanLLVM.Vellum.lstLanesExitC' does not depend on any axioms -/
#guard_msgs in
#print axioms lstLanesExitC

/-- info: 'LeanLLVM.Vellum.lstLanesLoopC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesLoopC

/-- info: 'LeanLLVM.Vellum.lanesRunC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanesRunC

/-- info: 'LeanLLVM.Vellum.lanesRunC_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanesRunC_at

/-- info: 'LeanLLVM.Vellum.em11_stepN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms em11_stepN

/-- info: 'LeanLLVM.Vellum.AtExit' does not depend on any axioms -/
#guard_msgs in
#print axioms AtExit

/-- info: 'LeanLLVM.Vellum.runFromSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runFromSeed

/-- info: 'LeanLLVM.Vellum.length_filter_le_of_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_filter_le_of_imp

/-- info: 'LeanLLVM.Vellum.ctpop_le_of_lane_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ctpop_le_of_lane_imp

/-- info: 'LeanLLVM.Vellum.lxWord_ctpop_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lxWord_ctpop_le

/-- info: 'LeanLLVM.Vellum.escapePositionsBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsBudget

/-- info: 'LeanLLVM.Vellum.finishSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finishSeed

/-- info: 'LeanLLVM.Vellum.seedExit_entry_arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seedExit_entry_arr

/-- info: 'LeanLLVM.Vellum.seedExit_then_arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seedExit_then_arr

/-- info: 'LeanLLVM.Vellum.escape_positions_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms escape_positions_satisfies

/-- info: 'LeanLLVM.Vellum.lxCarry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lxCarry

/-- info: 'LeanLLVM.Vellum.readBytes_lxMem2_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_lxMem2_carry

/-- info: 'LeanLLVM.Vellum.readBytes_congr_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_congr_range

/-- info: 'LeanLLVM.Vellum.readBytes_lstIfEnd4Mem_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_lstIfEnd4Mem_off

/-- info: 'LeanLLVM.Vellum.lstWriter_step_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstWriter_step_carry

/-- info: 'LeanLLVM.Vellum.ushr63_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ushr63_toNat

/-- info: 'LeanLLVM.Vellum.carry64_eq_classCarryAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carry64_eq_classCarryAt

/-- info: 'LeanLLVM.Vellum.parityAt_block64_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parityAt_block64_succ

/-- info: 'LeanLLVM.Vellum.carry64_oddRun_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carry64_oddRun_eq

/-- info: 'LeanLLVM.Vellum.carry64_oddRun_and_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carry64_oddRun_and_self

/-- info: 'LeanLLVM.Vellum.lxCarry_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lxCarry_spec

end LeanLLVM.Vellum
