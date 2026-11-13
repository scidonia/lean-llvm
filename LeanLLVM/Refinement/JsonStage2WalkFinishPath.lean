/-
The stage-2 walk's finish tail: the three routes from the merge's false arm to the return.

`JsonStage2WalkAssembly`'s tail census lists them:

  `if.then485.i → if.end490.i → s2_walk.exit → if.end`          (path 1)
  `if.then485.i → if.end490.i → if.then492.i → if.then → if.end` (path 2)
  `if.then485.i → if.then488.i → if.then → if.end`               (path 3)

Every block's step is already proved (`walkIfThen485Step`, `walkIfThen488Step`,
`walkIfEnd490Step` and `walkIfThen492Step` at a generic `calls`; `walkExitStep`,
`walkIfThen_step` and `walkReturn_at` at `stage2Calls sub`).  What the three routes owe is
their composure, and the obstruction is that a `WalkSegment` carries its target's invariant
(`WalkSegment.inv'`) while a bare `.jump` does not produce one.

**Past `if.end490.i` no route is a segment, and the reason is the frame.**  `WalkInv.frame`
is `UnchangedOutside m0 s.mem (walkWide G C)`, and `walkWide` names the arena's decoded
prefix, the event stream's prefix, the seven appended objects, `%d.i` and the body's four
allocations — it does **not** name the arena's cursor slot, the event stream's or the refusal
record's.  Two of the tail's blocks store the two cursor words and the refusal offset into
exactly those three slots: `s2_walk.exit` (path 1) and `if.then` (paths 2 and 3), both
`%ndst`, `%nev`, `%err`.  Their targets therefore differ from the initial memory at bytes the
frame claims are unchanged, so **`WalkInv` is not preserved through either block and no
`WalkSegment` can end at `if.end`.**  `walkFinish_not_frame_of` is the proof of the outside
half — every byte of the three slots is outside `walkWide` — and the repository states the
same fact where the arm is described (`JsonStage2WalkCall`'s note that the copy's stores are
the record's, outside the walk's frame, so it is the terminal step's refusal arm and not a
link).  So paths 1 and 2 are `runFuel` equations from `if.then485.i` to `if.end`, and path 3
is a segment only as far as `if.then`, which is the last block on it that preserves the
invariant: `if.then488.i`'s store lands inside the refusal record's staged extent, which
`walkWide` does name.

The three routes share the exit's first step, so it is stated once: `walkFinishPrefix` is
`if.then485.i` on the empty-stack arm, the head of paths 1 and 2 (path 3 takes its sibling,
the bit's other arm, and is `walkFinishPath3`).  `walkFinishPath1`, `walkFinishPath2` and
`walkFinishRun` are then the routes' `runFuel` equations, at the counts the census gives
them, in the shape `walkExitTailRefuse488` already has for the same blocks from the merge.

Only `JsonStage2WalkAssembly` is imported: it carries all four step lemmas, the carries, the
invariant, the staging and the region helpers, and `JsonStage2WalkStepsPath` (which imports
it) adds the chain instances the tail's own steps are stated over, not the ones used here.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The carries and the states, named

A `with`-nest at depth two is not something a term can spell, and a state a hypothesis is
stated at has to be a name — the reading the scan's own carries and states are given
(`ScanC₁₀₅`, `ScanCLand`, `landRhs457OutAt`). -/

/-- `if.then488.i`'s carry: the depth's non-zero arm. -/
abbrev FinishC₄₈₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.then488.i" }

/-- `if.then`'s carry: the refusal copy's entry. -/
abbrev FinishCThen {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { FinishC₄₈₈ C with block := "if.then" }

/-- The state `if.then485.i` leaves on the non-empty-stack arm. -/
def finishS₄₈₈ (s : State) (spv : Nat) : State :=
  { s with
    env := ("%48", .int 1 (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0))) :: s.env
    pc := "if.then488.i"
    pre := some s.pc }

/-- The state `if.then488.i` leaves: the refusal offset's store, at the copy's entry. -/
def finishSThen (s : State) (e v : Nat) : State :=
  { s with
    env := ("%off1.i.i115", .ptr (e + 8)) :: s.env
    mem := writeBytes s.mem (e + 8) (wordBytes 8 v)
    pc := "if.then"
    pre := some s.pc }

/-- The state the copy leaves, at the return's block.  It is the copy's own state with the
`br`'s edge, so the block's `denoteCode` result stays the caller's. -/
def finishSEnd (s s₂ : State) : State :=
  { s₂ with pc := "if.end", pre := some s.pc }

/-! ### The three steps, at their arms -/

/-- **`if.then485.i`'s step at the arm the path takes.**  The depth's bit is clear, so the
successor is `if.then488.i` and the target is `finishS₄₈₈`. -/
theorem walkFinish485Step {calls : Calls} {s : State} {spv : Nat}
    (hpc : s.pc = "if.then485.i")
    (hsp : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hbit : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 0) :
    step calls stage2Body s = .jump (finishS₄₈₈ s spv) := by
  rw [walkIfThen485Step (calls := calls) s hpc hsp]
  simp only [finishS₄₈₈, State.bind]
  rw [show (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
    then "if.end490.i" else "if.then488.i") = "if.then488.i" from
    ite_eq_right (by rw [hbit]; decide)]

/-- **`if.then488.i`'s step at the staged record.**  `%e` is the record the staging names,
so the store lands at `C.stage.e + 8` and the target is `finishSThen`. -/
theorem walkFinish488Step {calls : Calls} {s : State} {e v : Nat}
    (hpc : s.pc = "if.then488.i")
    (he : lookupName s.env "%e" = some (.ptr e))
    (h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64) :
    step calls stage2Body s = .jump (finishSThen s e v) :=
  walkIfThen488Step (calls := calls) s hpc he h4 hv64

/-- **The refusal copy's step.**  The block's `denoteCode` run is the caller's — the equation
is the ceiling, as at `walkRefusalCopy_at` — and the target carries the copy's memory at
`if.end`. -/
theorem walkFinishThenStep {sub : Calls} {s s₂ : State}
    (hpc : s.pc = "if.then") (hpc₂ : s₂.pc = s.pc)
    (hden : denoteCode (stage2Calls sub) walkIfThenBlock.instrs s = some s₂) :
    step (stage2Calls sub) stage2Body s = .jump (finishSEnd s s₂) :=
  walkIfThen_step s hpc hden hpc₂

/-! ### The empty-stack arm's head, and `if.end490.i`'s two arms

Paths 1 and 2 both leave `if.then485.i` on the depth's *zero* test — the bit path 3 does not
take — so the exit's first step is stated once, as the shared head of their runs, and then
`if.end490.i`'s root-done test splits them: a non-zero word takes `s2_walk.exit` (path 1), a
zero word takes the refusal copy's entry `if.then492.i` (path 2).  The two arms are
`walkExit490`'s, with the bit resolved so each route names its own successor. -/

/-- **The exit's first step on the empty-stack arm.**  The block's bit is `1`, so the
successor is `if.end490.i` and the target is `exitS₂`. -/
theorem walkFinish485StepEnd {calls : Calls} {s : State} {spv : Nat}
    (hpc : s.pc = "if.then485.i")
    (hsp : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hbit : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1) :
    step calls stage2Body s = .jump (exitS₂ s spv) := by
  rw [walkIfThen485Step (calls := calls) s hpc hsp]
  simp only [exitS₂]
  rw [show (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
    then "if.end490.i" else "if.then488.i") = "if.end490.i" from
    ite_eq_left (by rw [hbit])]

/-- **The exit's shared head, as a run.**  `if.then485.i` on the empty-stack arm: one step to
`if.end490.i`, the first step of paths 1 and 2, stated once so neither route re-derives it.
Path 3's head is the same block on the bit's other arm (`walkFinish485Step`). -/
theorem walkFinishPrefix {calls : Calls} {s : State} {spv : Nat}
    (hpc : s.pc = "if.then485.i")
    (hsp : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hbit : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1) :
    (∀ n, runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body (exitS₂ s spv)) ∧
      (exitS₂ s spv).pc = "if.end490.i" :=
  ⟨runFuel_jump_prefix (walkFinish485StepEnd hpc hsp hbit), rfl⟩

/-- **`if.end490.i` with the root slot set.**  A non-zero root-done word takes the exit's own
tail, `s2_walk.exit`: path 1's second step. -/
theorem walkFinish490StepExit {calls : Calls} {s : State} {rv : BitVec 32} {rd : Nat}
    (hpc : s.pc = "if.end490.i")
    (hroot : lookupName s.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s.mem rd 4 = some (natToBytes rv.toNat 4))
    (hzero : evalICmp .eq rv (BitVec.ofNat 32 0) = 0) :
    step calls stage2Body s = .jump (exitS₃ s rv) := by
  rw [walkIfEnd490Step (calls := calls) s hpc (v := rv) hroot hread]
  simp only [exitS₃]
  rw [show (if evalICmp .eq rv (BitVec.ofNat 32 0) = 1 then "if.then492.i"
    else "s2_walk.exit") = "s2_walk.exit" from ite_eq_right (by rw [hzero]; decide)]

/-- **`if.end490.i` with the root slot clear.**  A zero root-done word takes the refusal
copy's entry, `if.then492.i`: path 2's second step. -/
theorem walkFinish490StepRefuse {calls : Calls} {s : State} {rv : BitVec 32} {rd : Nat}
    (hpc : s.pc = "if.end490.i")
    (hroot : lookupName s.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s.mem rd 4 = some (natToBytes rv.toNat 4))
    (hone : evalICmp .eq rv (BitVec.ofNat 32 0) = 1) :
    step calls stage2Body s = .jump (exitS₃r s rv) := by
  rw [walkIfEnd490Step (calls := calls) s hpc (v := rv) hroot hread]
  simp only [exitS₃r]
  rw [show (if evalICmp .eq rv (BitVec.ofNat 32 0) = 1 then "if.then492.i"
    else "s2_walk.exit") = "if.then492.i" from ite_eq_left (by rw [hone])]

/-! ### The invariant across one step

`walkIfThen485.i`'s block binds a cell and writes nothing, and `if.then488.i`'s binds a cell
and writes inside the refusal record.  Both are one environment layer over a memory, so the
transport is one lemma: the register carriers read `walkCarriedNames`' names and two cells
of their own, `WalkInv`'s block-reading fields are the target's position and `WalkLocal` at
its block, and every memory clause is the clause at the new memory — the caller's. -/

/-- **The invariant at a state the run has reached**: a cell list in front of the
environment, a new block, a new memory, and each memory clause supplied.  The register
carriers are the cell list's own clause set, and the two block-reading fields are the
target's position and `WalkLocal` at the new block.  This is `walkEntry_inv`'s shape at a
step rather than at a call, and `bindAt`'s at a state whose memory moves. -/
theorem walkFinishInvAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {b : String} {cs : List (String × Value)} {m' : Mem} {pr : Option String}
    (h : WalkInv G C s)
    (hfree : ∀ n ∈ cs.map (·.1), n ∉ walkCarriedNames)
    (hki : ∀ n ∈ cs.map (·.1), n ≠ "%k.0.i249")
    (hspp : ∀ n ∈ cs.map (·.1), n ≠ "%sp.i.0248")
    (hptr : ∀ n ∈ cs.map (·.1), n ≠ "%3" ∧ n ≠ "%5" ∧ n ≠ "%k11.i" ∧
      n ≠ "%ctype.i" ∧ n ≠ "%cst.i" ∧ n ≠ "%hash1.i.i")
    (hEv : readBytes m' (G.ev + G.nev0)
      (C.events.map EventRecord.encodedBytes).flatten.length =
      some (C.events.map EventRecord.encodedBytes).flatten)
    (hTy : WalkStackBytes m' C.stage.ctype C.tyMap C.wlen)
    (hSt : WalkStackBytes m' C.stage.cst C.stMap C.wlen)
    (hlogHash : readBytes m' (C.stage.z + 32) 4 = some (natToBytes 0 4))
    (hlogLen : readBytes m' (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen))
    (hlogCap : readBytes m' (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap))
    (hlogA : ∃ a, G.ndst0 ≤ a ∧ a ≤ C.alen ∧
      readBytes m' (C.stage.z + 48) 8 = some (wordBytes 8 a))
    (hlogAcap : readBytes m' (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap))
    (hown : ∀ r ∈ walkStaged G C, HasBytes m' r.1 r.2)
    (hframe : UnchangedOutside m0 m' (walkWide G C))
    (hloc : WalkLocal { C with block := b }
      { s with env := cells cs s.env, mem := m', pc := b, pre := pr }) :
    WalkInv G { C with block := b }
      { s with env := cells cs s.env, mem := m', pc := b, pre := pr } where
  pc_eq := rfl
  blockIndex := by
    rw [lookupName_cells_of_notin cs "%k.0.i249" s.env
      (fun hin => hki "%k.0.i249" hin rfl)]
    exact h.blockIndex
  k_le := h.k_le
  events_le := h.events_le
  evlen_eq := h.evlen_eq
  evBytes := hEv
  alen_le_sum := h.alen_le_sum
  alen_ge := h.alen_ge
  spans_order := h.spans_order
  spans_inside := h.spans_inside
  spans_end := h.spans_end
  pending_at := h.pending_at
  pending_len := h.pending_len
  pending_cursor := h.pending_cursor
  eoff_le := h.eoff_le
  inner_cap := h.inner_cap
  depth_cap := h.depth_cap
  depth_reg := by
    rw [lookupName_cells_of_notin cs "%sp.i.0248" s.env
      (fun hin => hspp "%sp.i.0248" hin rfl)]
    exact h.depth_reg
  sp_le_wlen := h.sp_le_wlen
  wlen_cap := h.wlen_cap
  tyBytes := hTy
  stBytes := hSt
  ptrs := h.ptrs.cells_of cs (fun c hc => hptr c.1 (List.mem_map_of_mem hc))
  regs := h.regs.cells_of cs (fun n hn => by
    have hc := hfree n hn
    simp only [walkCarriedNames, List.mem_cons, not_or] at hc
    exact hc.2.2)
  iter := h.iter.cells_of cs hfree
  log_hash := hlogHash
  log_len := hlogLen
  log_cap := hlogCap
  log_alen := hlogA
  log_acap := hlogAcap
  owned := hown
  frame := hframe
  blockLocal := hloc

/-- The event stream's room at the trace's widths: the flatten length is the width sum, and
the geometry's `evRoom` bounds it by the capacity.  `walkIfThen25_i`'s arithmetic, named once
because both stores of the tail read it. -/
theorem walkFinish_evRoom {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
  have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
      (C.events.map EventRecord.encodedSize).sum := by
    simp only [List.length_flatten, List.map_map]; rfl
  have hsum := EventRecord.sum_encodedSize_le C.events
  simp only [stage2RecordBytes] at hsum
  have hroom := G.evRoom
  simp only [stage2RecordBytes] at hroom
  have h1 := hInv.events_le
  have h2 := hInv.k_le
  have h3 := G.nep_le
  rw [hlen]; omega

/-- **`if.then485.i`'s invariant.**  One cell in front of the environment and nothing else:
the memory clauses carry unchanged and the four carriers are the bind's own. -/
theorem walkFinish485Inv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {spv : Nat} :
    WalkInv G (FinishC₄₈₈ C) (finishS₄₈₈ s spv) := by
  have hstep := walkFinishInvAt (G := G) (C := C) (s := s) (b := "if.then488.i")
    (cs := [("%48", .int 1 (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0)))])
    (m' := s.mem) (pr := some s.pc) hInv
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)
    hInv.evBytes hInv.tyBytes hInv.stBytes hInv.log_hash hInv.log_len hInv.log_cap
    hInv.log_alen hInv.log_acap hInv.owned hInv.frame
    (by simp [WalkLocal])
  simpa only [finishS₄₈₈, cells] using hstep

/-- **`if.then488.i`'s invariant.**  The block stores the refusal offset at `%e + 8`.  The
store is inside the refusal record's staged extent, so the frame holds by the record's own
region (`eoff_inside` through `walkWide_of_seven`), presence by monotonicity, and the log's
words and the event stream's prefix by the staging's separation of the record from them. -/
theorem walkFinish488Inv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {v : Nat} :
    WalkInv G (FinishCThen C) (finishSThen s C.stage.e v) := by
  have hN := walkFinish_evRoom G hInv
  have hstep := walkFinishInvAt (G := G) (C := C) (s := s) (b := "if.then")
    (cs := [("%off1.i.i115", .ptr (C.stage.e + 8))])
    (m' := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 v)) (pr := some s.pc) hInv
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        decide)
    (by intro n hn
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hn
        rcases hn with rfl
        exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)
    (by
      rw [walkReadBytes_ev_of_eoff_write (e := C.stage.e) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (j := v)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length)
        (e_ev_sep hInv) hN]
      exact hInv.evBytes)
    (by
      refine hInv.tyBytes.write_outside ?_
      have hwl : (wordBytes 8 v).length = 8 := by
        simp [wordBytes, natToBytes_length]
      have hx : stage2ErrorExtent = 24 := rfl
      rcases (stack_e_sep hInv).1 with h' | h'
      · exact Or.inr (by omega)
      · exact Or.inl (by omega))
    (by
      refine hInv.stBytes.write_outside ?_
      have hwl : (wordBytes 8 v).length = 8 := by
        simp [wordBytes, natToBytes_length]
      have hx : stage2ErrorExtent = 24 := rfl
      rcases (stack_e_sep hInv).2 with h' | h'
      · exact Or.inr (by omega)
      · exact Or.inl (by omega))
    (by
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 32)
        (j := v) (N := 4) (e_z_sep hInv) (by decide)]
      exact hInv.log_hash)
    (by
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 8)
        (j := v) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_len)
    (by
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 16)
        (j := v) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_cap)
    (by
      obtain ⟨a, h1, h2, h3⟩ := hInv.log_alen
      refine ⟨a, h1, h2, ?_⟩
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 48)
        (j := v) (N := 8) (e_z_sep hInv) (by decide)]
      exact h3)
    (by
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 56)
        (j := v) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_acap)
    (by
      exact walkStaged_write (m := s.mem) (a := C.stage.e + 8) (bs := wordBytes 8 v)
        rfl hInv.owned)
    (by
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      rw [show (wordBytes 8 v).length = 8 from by
        simp [wordBytes, natToBytes_length]] at hk
      exact walkWide_of_seven (eoff_inside (k := k) (by omega)))
    (by simp [WalkLocal])
  simpa only [finishSThen, cells] using hstep

/-! ### Why the path stops at `if.then`

`walkWide G C` is the arena's decoded prefix, the event stream's prefix, the seven appended
objects, `%d.i` and the body's four allocations.  The copy that follows `if.then` writes the
arena's cursor slot, the event stream's and the refusal offset's — the geometry's own
objects, staged but never in the walk's write extent (`walkStaged` names them, `walkPresent`
does not).  So the frame clause at the copy's target would claim those bytes unchanged while
the copy has just written them, and no hypothesis of the source state produces it: the
outside half is `walkFinish_not_frame_of`, and the missing half is the write itself. -/

/-- **Two entries of the geometry's region list are separated.**  The projection
`stagedWrites_sep` is for the seven appended objects; this is the same projection at the
eight ABI ones, which is where the three record slots live. -/
theorem walkFinishRegions_sep {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions
      (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err))
    {i j : Nat} (hi : i < 8) (hj : j < 8) (hij : i < j) :
    ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).2 ≤
      ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 ∨
    ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).2 ≤
      ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 :=
  (List.pairwise_iff_getElem.mp h) i j hi hj hij

/-- **A byte of one of the three record slots is outside the run's frame.**  The slots are
the thirteen ABI objects' own, so the arena's prefix, the event stream's prefix, the seven
appended objects and the body's four allocations all miss them.  The hypotheses are the four
separations and the watermark, so the caller names the slot's position once and the frame
follows.  This is `err_not_in_walkFrame`'s argument at the invariant's own carries. -/
theorem walkFinish_not_frame_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {a k : Nat}
    (hdst : G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ a ∨ a + 8 ≤ G.dst)
    (hev : G.ev + G.evcap ≤ a ∨ a + 8 ≤ G.ev)
    (hseven : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ a ∨ a + 8 ≤ r.1)
    (hd : C.stage.d + 8 ≤ a ∨ a + 8 ≤ C.stage.d)
    (hwm : a + 8 ≤ G.next0)
    (hk : k < 8) :
    ¬ inRegions (walkWide G C) (a + k) := by
  intro hin
  have halen := hInv.alen_le
  have hevlen : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
  have har : stage2ArenaReserve = 64 := rfl
  obtain ⟨r, hr, hlo, hhi⟩ := hin
  simp only [walkWide, walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · rcases hdst with h' | h' <;> omega
      · rcases List.mem_cons.mp hr with rfl | hnil
        · rcases hev with h' | h' <;> omega
        · exact absurd hnil (by simp)
    · rcases List.mem_append.mp hr with hr | hr
      · rcases hseven r hr with h' | h' <;> omega
      · rcases List.mem_cons.mp hr with rfl | hnil
        · rcases hd with h' | h' <;> omega
        · exact absurd hnil (by simp)
  · exact not_inRegions_allocaWrites (a := G.next0) (x := a + k) (by omega)
      ⟨r, hr, hlo, hhi⟩

/-! ### The path -/

/-- **Path 1, as a run.**  The shared head, `if.end490.i` with the root slot set, and
`s2_walk.exit`'s copy: three control steps to the return's block.  No `WalkInv` is carried
past the head's successor, because the exit block's stores are the record's and lie outside
the walk's frame (`walkFinish_not_frame_of`); the route is a `runFuel` equation for the same
reason `walkExitTailExit` is.

The two lookups the last step is stated at are the caller's, as at `walkExitStep`: they are
the copy's byte facts, not step arithmetic. -/
theorem walkFinishPath1 {sub : Calls} (s0 : State) (hpc : s0.pc = "if.then485.i")
    {spv rd : Nat} {rv : BitVec 32} {s₃ : State}
    (hsp : lookupName s0.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hone : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    (hroot : lookupName s0.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s0.mem rd 4 = some (natToBytes rv.toNat 4))
    (hzero : evalICmp .eq rv (BitVec.ofNat 32 0) = 0)
    (hden : denoteCode (stage2Calls sub) walkExitBlock.instrs
      (exitS₃ (exitS₂ s0 spv) rv) = some s₃)
    (hpc₃ : s₃.pc = (exitS₃ (exitS₂ s0 spv) rv).pc) :
    ∃ (s : State),
      (∀ n, runFuel (stage2Calls sub) (3 + n) stage2Body s0 =
        runFuel (stage2Calls sub) n stage2Body s) ∧
      s.pc = "if.end" ∧ s = exitS₄ (exitS₃ (exitS₂ s0 spv) rv) s₃ := by
  obtain ⟨hstep₁, hpc₁⟩ := walkFinishPrefix hpc hsp hone
  have hstep₂ : step (stage2Calls sub) stage2Body (exitS₂ s0 spv) =
      .jump (exitS₃ (exitS₂ s0 spv) rv) :=
    walkFinish490StepExit hpc₁ ((exitS₂_rd (s := s0) (spv := spv)).trans hroot) hread hzero
  have hstep₃ : step (stage2Calls sub) stage2Body (exitS₃ (exitS₂ s0 spv) rv) =
      .jump (exitS₄ (exitS₃ (exitS₂ s0 spv) rv) s₃) :=
    walkExitStep (sub := sub) _ rfl hden hpc₃
  refine ⟨exitS₄ (exitS₃ (exitS₂ s0 spv) rv) s₃, fun n => ?_, rfl, rfl⟩
  rw [show 3 + n = 1 + (1 + (1 + n)) from by omega]
  rw [hstep₁ (1 + (1 + n))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₂ (1 + n)]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₃ n]

/-- **Path 2, as a run.**  The shared head, `if.end490.i` with the root slot clear,
`if.then492.i`'s refusal store, and the copy: four control steps to the return's block.  Its
stores are the record's (`if.then492.i`'s is inside the refusal record, the copy's the three
record slots), so the route is a `runFuel` equation from `if.end490.i` on.

`%e` and `%4` are stated at the refusal block, where the previous step left them: the copy
reads the offset the store wrote. -/
theorem walkFinishPath2 {sub : Calls} (s0 : State) (hpc : s0.pc = "if.then485.i")
    {spv rd e v : Nat} {rv : BitVec 32} {s₂ : State}
    (hsp : lookupName s0.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hone : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    (hroot : lookupName s0.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s0.mem rd 4 = some (natToBytes rv.toNat 4))
    (hclear : evalICmp .eq rv (BitVec.ofNat 32 0) = 1)
    (he : lookupName (exitS₃r (exitS₂ s0 spv) rv).env "%e" = some (.ptr e))
    (h4 : lookupName (exitS₃r (exitS₂ s0 spv) rv).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64)
    (hden : denoteCode (stage2Calls sub) walkIfThenBlock.instrs
      (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) = some s₂)
    (hpc₂ : s₂.pc = (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v).pc) :
    ∃ (s : State),
      (∀ n, runFuel (stage2Calls sub) (4 + n) stage2Body s0 =
        runFuel (stage2Calls sub) n stage2Body s) ∧
      s.pc = "if.end" ∧
      s = exitS₄ (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) s₂ := by
  obtain ⟨hstep₁, hpc₁⟩ := walkFinishPrefix hpc hsp hone
  have hstep₂ : step (stage2Calls sub) stage2Body (exitS₂ s0 spv) =
      .jump (exitS₃r (exitS₂ s0 spv) rv) :=
    walkFinish490StepRefuse hpc₁ ((exitS₂_rd (s := s0) (spv := spv)).trans hroot) hread hclear
  have hstep₃ : step (stage2Calls sub) stage2Body (exitS₃r (exitS₂ s0 spv) rv) =
      .jump (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) :=
    walkIfThen492Step _ rfl he h4 hv64
  have hstep₄ : step (stage2Calls sub) stage2Body
      (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) =
      .jump (exitS₄ (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) s₂) :=
    walkIfThen_step _ rfl hden hpc₂
  refine ⟨exitS₄ (exitS₅ (exitS₃r (exitS₂ s0 spv) rv) e v) s₂, fun n => ?_, rfl, rfl⟩
  rw [show 4 + n = 1 + (1 + (1 + (1 + n))) from by omega]
  rw [hstep₁ (1 + (1 + (1 + n)))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₂ (1 + (1 + n))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₃ (1 + n)]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₄ n]

/-- **The finish tail's third path's two blocks that preserve the invariant, as one
segment.**  `if.then485.i`'s depth test off the non-empty-stack arm, then `if.then488.i`'s
store of the refusal offset: two control steps to `if.then`, at the carry that names it, with
the invariant at the target.

The copy that follows is not part of the segment, and not because its `denoteCode` is hard to
supply: `if.then` writes the record's three ABI slots, whose bytes are outside `walkWide`
(`walkFinish_not_frame_of`), so the target's frame clause is false.  The two-step segment is
what `WalkDispatchThree.ofContinueAndLast`'s last branch names — a carry whose block is
`if.then` and whose refusal offset is inside the document. -/
theorem walkFinishPath3 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s0 : State)
    (hInv : WalkInv G C s0) (hblock : C.block = "if.then485.i") {spv v : Nat}
    (hsp : lookupName s0.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hbit : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 0)
    (he : lookupName s0.env "%e" = some (.ptr C.stage.e))
    (h4 : lookupName s0.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64) :
    ∃ (s : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s0 (FinishCThen C) s 2 ∧
      s.pc = "if.then" ∧
      s = finishSThen (finishS₄₈₈ s0 spv) C.stage.e v ∧
      WalkInv G (FinishCThen C) s := by
  have hpc : s0.pc = "if.then485.i" := by rw [hInv.pc_eq, hblock]
  have hstep₁ : step (stage2Calls stage2SubCalls) stage2Body s0 =
      .jump (finishS₄₈₈ s0 spv) := walkFinish485Step hpc hsp hbit
  have h4' : lookupName (finishS₄₈₈ s0 spv).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    simp only [finishS₄₈₈]
    rw [lookupName_cons_ne (k := "%48") (n := "%4") _ _ (by decide)]
    exact h4
  have hstep₂ : step (stage2Calls stage2SubCalls) stage2Body (finishS₄₈₈ s0 spv) =
      .jump (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) :=
    walkFinish488Step rfl he h4' hv64
  have hinv := walkFinish488Inv (v := v) (walkFinish485Inv (spv := spv) hInv)
  refine ⟨finishSThen (finishS₄₈₈ s0 spv) C.stage.e v, ⟨fun n => ?_, hinv⟩, rfl, rfl, hinv⟩
  rw [show 2 + n = 1 + (1 + n) from by omega]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₁ (1 + n)]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₂ n]

/-- **The refusal copy, from the segment's target.**  Its run is the caller's, and the step
lands at the return's block. -/
theorem walkFinishCopyStep {sub : Calls} {s s₂ : State} (hpc : s.pc = "if.then")
    (hpc₂ : s₂.pc = "if.then")
    (hden : denoteCode (stage2Calls sub) walkIfThenBlock.instrs s = some s₂) :
    step (stage2Calls sub) stage2Body s = .jump (finishSEnd s s₂) ∧
      (finishSEnd s s₂).pc = "if.end" :=
  ⟨walkFinishThenStep hpc (hpc₂.trans hpc.symm) hden, rfl⟩

/-- **The finish tail's third path, as a run.**  The two-block segment and the copy's step:
three control steps from the merge's non-empty-stack arm to the return's block, at the
segment's own count plus one — the shape `walkExitTailRefuse488` gives the same three blocks
from the other arms.  The copy is a step here rather than a segment's third link because its
stores are the record's and lie outside the walk's frame (`walkFinish_not_frame_of`). -/
theorem walkFinishRun {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s0 : State) (hInv : WalkInv G C s0) (hblock : C.block = "if.then485.i")
    {spv v : Nat} {s₂ : State}
    (hsp : lookupName s0.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hbit : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 0)
    (he : lookupName s0.env "%e" = some (.ptr C.stage.e))
    (h4 : lookupName s0.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64)
    (hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs
      (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) = some s₂)
    (hpc₂ : s₂.pc = "if.then") :
    ∃ (s : State), (∀ n, runFuel (stage2Calls stage2SubCalls) (3 + n) stage2Body s0 =
      runFuel (stage2Calls stage2SubCalls) n stage2Body s) ∧ s.pc = "if.end" ∧
      s = finishSEnd (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) s₂ := by
  obtain ⟨s₁, hseg, hpc₁, hs₁, -⟩ :=
    walkFinishPath3 (G := G) (C := C) (s0 := s0) hInv hblock hsp hbit he h4 hv64
  subst hs₁
  have hstep : step (stage2Calls stage2SubCalls) stage2Body
      (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) =
      .jump (finishSEnd (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) s₂) :=
    walkFinishThenStep hpc₁ (hpc₂.trans hpc₁.symm) hden
  refine ⟨finishSEnd (finishSThen (finishS₄₈₈ s0 spv) C.stage.e v) s₂,
    fun n => ?_, rfl, rfl⟩
  rw [show 3 + n = 2 + (1 + n) from by omega]
  rw [hseg.run (1 + n)]
  exact runFuel_jump_prefix (f := stage2Body) hstep n

end WalkScope
end LeanLLVM.Refinement
