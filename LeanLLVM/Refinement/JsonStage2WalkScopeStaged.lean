import LeanLLVM.Refinement.JsonStage2WalkScopeBlocks

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-- **Two staged ABI objects, by index, are separate.**  The list is a literal, so
a position names an object without needing the pair's own disequality. -/
theorem stage2Regions_sep {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err))
    {i j : Nat} (hi : i < (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err).length)
    (hj : j < (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err).length)
    (hij : i < j) :
    ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).2 ≤
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 ∨
      ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).2 ≤
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 :=
  (List.pairwise_iff_getElem.mp h) i j hi hj hij

/-- **A byte range separated from the walk's write families is outside its write
extents.**  The arena's prefix and the event stream's prefix are sub-intervals of
the staged arena and event entries; the seven are separated by the staging's own
list; and `%d.i`'s slot by the adapter's separation of it. -/
theorem walkPresent_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) {a m : Nat}
    (hArena : a + m ≤ G.dst ∨ G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ a)
    (hEv : a + m ≤ G.ev ∨ G.ev + G.evcap ≤ a)
    (hSeven : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ a ∨ a + m ≤ r.1)
    (hD : C.stage.d + 8 ≤ a ∨ a + m ≤ C.stage.d)
    {e : Nat} (ha : a ≤ e) (he : e < a + m) :
    ¬ inRegions (walkPresent G C) e := by
  have halen := h.alen_le
  have hev := h.evlen_le
  have hevroom := G.evRoom
  rintro ⟨r, hr, hlo, hhi⟩
  simp only [walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · rcases hArena with h' | h' <;> omega
    · rcases List.mem_cons.mp hr with rfl | hr
      · rcases hEv with h' | h' <;> omega
      · exact absurd hr (by simp)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hSeven r hr with h' | h' <;> omega
    · rcases List.mem_cons.mp hr with rfl | hnil
      · rcases hD with h' | h' <;> omega
      · exact absurd hnil (by simp)

/-- **The entry stream is outside the walk's write extents.** -/
theorem WalkInv.entry_present_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.ep ≤ e) (he : e < G.ep + 4 * G.nep) :
    ¬ inRegions (walkPresent G C) e := by
  have hsep := disjointRegions_staged_prefix C.stage.separate
  have h13 := stage2Regions_sep hsep (i := 1) (j := 3)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  have h14 := stage2Regions_sep hsep (i := 1) (j := 4)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h13 h14
  refine walkPresent_outside h (a := G.ep) (m := 4 * G.nep) (e := e) ?_ ?_ ?_ ?_ ha he
  · omega
  · omega
  · intro r hr
    exact stage2StagedWrites_against C.stage.separate
      (a := G.ep) (m := 4 * G.nep) (by simp [stage2Regions]) r hr
  · rcases C.stage.dSep (G.ep, 4 * G.nep)
      (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
    · exact Or.inr hd
    · exact Or.inl hd

/-- **The document's bytes are outside the walk's write extents.** -/
theorem WalkInv.doc_present_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.b ≤ e) (he : e < G.b + G.n) :
    ¬ inRegions (walkPresent G C) e := by
  have hsep := disjointRegions_staged_prefix C.stage.separate
  have h03 := stage2Regions_sep hsep (i := 0) (j := 3)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  have h04 := stage2Regions_sep hsep (i := 0) (j := 4)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h03 h04
  refine walkPresent_outside h (a := G.b) (m := G.n) (e := e) ?_ ?_ ?_ ?_ ha he
  · omega
  · omega
  · intro r hr
    have hout := stage2StagedWrites_against C.stage.separate
      (a := G.b) (m := G.n + stage2ReadTail) (by simp [stage2Regions]) r hr
    rcases hout with h' | h' <;> omega
  · rcases C.stage.dSep (G.b, G.n + stage2ReadTail)
      (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- **The entry stream's bytes are outside the walk's whole frame.**  The write
extents are excluded above; the cursor's interval by the watermark, since the byte
is inside an entry that ends at or below the cursor. -/
theorem WalkInv.entry_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.ep ≤ e) (he : e < G.ep + 4 * G.nep) :
    ¬ inRegions (walkWideAt G C (s.next - G.next0)) e := by
  have hp := h.entry_present_outside ha he
  have hlt : e < G.next0 :=
    Nat.lt_of_lt_of_le he (G.watermark (G.ep, 4 * G.nep) (by simp [stage2Regions]))
  intro hw
  obtain ⟨r, hr, hlo, hhi⟩ := hw
  simp only [walkWideAt] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hp ⟨r, hr, hlo, hhi⟩
  · exact not_interval_of_lt hlt ⟨r, hr, hlo, hhi⟩

/-- **The document's bytes are outside the walk's whole frame.** -/
theorem WalkInv.doc_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.b ≤ e) (he : e < G.b + G.n) :
    ¬ inRegions (walkWideAt G C (s.next - G.next0)) e := by
  have hp := h.doc_present_outside ha he
  have hlt : e < G.next0 :=
    Nat.lt_of_lt_of_le (by omega)
      (G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions]))
  intro hw
  obtain ⟨r, hr, hlo, hhi⟩ := hw
  simp only [walkWideAt] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hp ⟨r, hr, hlo, hhi⟩
  · exact not_interval_of_lt hlt ⟨r, hr, hlo, hhi⟩

/-- **A write into the cursor record leaves the event stream's trace alone.** -/
theorem readBytes_ev_of_cursor_write {m : Mem} {c ev nev0 evcap N : Nat} {v : List UInt8}
    (hcev : c + stage2CursorExtent ≤ ev ∨ ev + evcap ≤ c) (hv : v.length ≤ 8)
    (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (c + 32) v) (ev + nev0) N = readBytes m (ev + nev0) N := by
  have hv' : stage2CursorExtent = 1192 := rfl
  refine walkReadBytes_writeBytes_outside (start := c + 32) ?_
  rcases hcev with hcev | hcev
  · right
    omega
  · left
    omega

/-- The event stream's staged entry is a member of the ABI list. -/
theorem stage2Regions_mem_ev {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat} :
    (ev, evcap) ∈ stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err := by
  unfold stage2Regions
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

/-! ### The staged objects against the two container stacks

The carried maps make the stacks' bytes a clause of the invariant, so every link
that writes elsewhere owes a transfer: the write must miss the bytes the map
covers.  The separation is the staging's own `Pairwise`, read at the positions of
the written object and of a stack, so a link never has to compare two addresses.
-/

/-- **Two entries of the staged seven, by position, are separate.** -/
theorem stagedWrites_sep {c ctype cst tok s z e : Nat}
    (h : DisjointRegions (stage2StagedWrites c ctype cst tok s z e))
    {i j : Nat} (hi : i < 7) (hj : j < 7) (hij : i < j) :
    ((stage2StagedWrites c ctype cst tok s z e)[i]).1 +
        ((stage2StagedWrites c ctype cst tok s z e)[i]).2 ≤
      ((stage2StagedWrites c ctype cst tok s z e)[j]).1 ∨
    ((stage2StagedWrites c ctype cst tok s z e)[j]).1 +
        ((stage2StagedWrites c ctype cst tok s z e)[j]).2 ≤
      ((stage2StagedWrites c ctype cst tok s z e)[i]).1 :=
  (List.pairwise_iff_getElem.mp h) i j hi hj hij

/-- **A staged object other than a container stack is separate from both stacks**
at their staged extents.  The written object is named by its position (`0` the
cursor record, `3` the token, `4` the staging record, `5` the log, `6` the
refusal record), so no address comparison is owed. -/
theorem staged_entry_sep {c ctype cst tok s z e : Nat}
    (h : DisjointRegions (stage2StagedWrites c ctype cst tok s z e))
    {i : Nat} (hi : i < 7) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    (ctype + stage2StackExtent ≤ ((stage2StagedWrites c ctype cst tok s z e)[i]).1 ∨
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 +
          ((stage2StagedWrites c ctype cst tok s z e)[i]).2 ≤ ctype) ∧
      (cst + stage2StackExtent ≤ ((stage2StagedWrites c ctype cst tok s z e)[i]).1 ∨
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 +
          ((stage2StagedWrites c ctype cst tok s z e)[i]).2 ≤ cst) := by
  have hct : ctype + stage2StackExtent ≤
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 ∨
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 +
          ((stage2StagedWrites c ctype cst tok s z e)[i]).2 ≤ ctype := by
    rcases Nat.lt_or_gt_of_ne h1 with hlt | hgt
    · have h' := stagedWrites_sep h (i := i) (j := 1) hi (by decide) hlt
      simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
        using h'.symm
    · have h' := stagedWrites_sep h (i := 1) (j := i) (by decide) hi hgt
      simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
        using h'
  have hcs : cst + stage2StackExtent ≤
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 ∨
        ((stage2StagedWrites c ctype cst tok s z e)[i]).1 +
          ((stage2StagedWrites c ctype cst tok s z e)[i]).2 ≤ cst := by
    rcases Nat.lt_or_gt_of_ne h2 with hlt | hgt
    · have h' := stagedWrites_sep h (i := i) (j := 2) hi (by decide) hlt
      simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
        using h'.symm
    · have h' := stagedWrites_sep h (i := 2) (j := i) (by decide) hi hgt
      simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
        using h'
  exact ⟨hct, hcs⟩

/-- **The two container stacks are separate.**  `if.end24.i` stores into both at
the same depth, so each store must miss the other stack's staged extent — which is
the premise `walkStack_ifEnd24_at` composes the push from. -/
theorem ctype_cst_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.cst + stage2StackExtent ≤ C.stage.ctype ∨
      C.stage.ctype + stage2StackExtent ≤ C.stage.cst := by
  have h' : C.stage.ctype + stage2StackExtent ≤ C.stage.cst ∨
      C.stage.cst + stage2StackExtent ≤ C.stage.ctype := by
    have h := stagedWrites_sep C.stage.writes_separate (i := 1) (j := 2)
      (by decide) (by decide) (by decide)
    simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
      using h
  exact h'.symm

/-- **A write inside the cursor record misses both stacks' carried marks.** -/
theorem stack_c_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    (C.stage.ctype + C.wlen ≤ C.stage.c ∨ C.stage.c + stage2CursorExtent ≤ C.stage.ctype) ∧
      (C.stage.cst + C.wlen ≤ C.stage.c ∨ C.stage.c + stage2CursorExtent ≤ C.stage.cst) := by
  obtain ⟨hct, hcs⟩ := staged_entry_sep C.stage.writes_separate (i := 0)
    (by decide) (by decide) (by decide)
  simp only [stage2StagedWrites, List.getElem_cons_zero] at hct hcs
  have hcap := h.wlen_cap
  constructor
  · rcases hct with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'
  · rcases hcs with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- **A write inside the token's staging misses both stacks' carried marks.** -/
theorem stack_tok_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    (C.stage.ctype + C.wlen ≤ C.stage.tok ∨ C.stage.tok + stage2TokenExtent ≤ C.stage.ctype) ∧
      (C.stage.cst + C.wlen ≤ C.stage.tok ∨ C.stage.tok + stage2TokenExtent ≤ C.stage.cst) := by
  obtain ⟨hct, hcs⟩ := staged_entry_sep C.stage.writes_separate (i := 3)
    (by decide) (by decide) (by decide)
  simp only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ] at hct hcs
  have hcap := h.wlen_cap
  constructor
  · rcases hct with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'
  · rcases hcs with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- **A write inside the refusal record misses both stacks' carried marks.** -/
theorem stack_e_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    (C.stage.ctype + C.wlen ≤ C.stage.e ∨ C.stage.e + stage2ErrorExtent ≤ C.stage.ctype) ∧
      (C.stage.cst + C.wlen ≤ C.stage.e ∨ C.stage.e + stage2ErrorExtent ≤ C.stage.cst) := by
  obtain ⟨hct, hcs⟩ := staged_entry_sep C.stage.writes_separate (i := 6)
    (by decide) (by decide) (by decide)
  simp only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ] at hct hcs
  have hcap := h.wlen_cap
  constructor
  · rcases hct with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'
  · rcases hcs with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- **A write inside `%d.i`'s slot misses both stacks' carried marks.** -/
theorem stack_d_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    (C.stage.ctype + C.wlen ≤ C.stage.d ∨ C.stage.d + 8 ≤ C.stage.ctype) ∧
      (C.stage.cst + C.wlen ≤ C.stage.d ∨ C.stage.d + 8 ≤ C.stage.cst) := by
  have hcap := h.wlen_cap
  have hct := C.stage.dSep (C.stage.ctype, stage2StackExtent)
    (by simp [stage2WalkRegions, stage2Regions, stage2StagedWrites])
  have hcs := C.stage.dSep (C.stage.cst, stage2StackExtent)
    (by simp [stage2WalkRegions, stage2Regions, stage2StagedWrites])
  constructor
  · rcases hct with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'
  · rcases hcs with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- **A write inside the arena's staged window misses both stacks' carried
marks.**  The arena is an ABI object, so the staging separates it from the seven
the stacks belong to. -/
theorem stack_arena_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    (C.stage.ctype + C.wlen ≤ G.dst ∨
        G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ C.stage.ctype) ∧
      (C.stage.cst + C.wlen ≤ G.dst ∨
        G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ C.stage.cst) := by
  have hcap := h.wlen_cap
  have hct := disjointRegions_against C.stage.walk_separate
    (a := G.dst) (n := G.ndst0 + G.n + stage2ArenaReserve)
    (by simp [stage2WalkRegions, stage2Regions])
    (C.stage.ctype, stage2StackExtent)
    (by simp [stage2WalkRegions, stage2Regions, stage2StagedWrites])
  have hcs := disjointRegions_against C.stage.walk_separate
    (a := G.dst) (n := G.ndst0 + G.n + stage2ArenaReserve)
    (by simp [stage2WalkRegions, stage2Regions])
    (C.stage.cst, stage2StackExtent)
    (by simp [stage2WalkRegions, stage2Regions, stage2StagedWrites])
  constructor
  · rcases hct with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'
  · rcases hcs with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- **The state stack's map after `s2_after_value` at a given depth.**  At depth
zero the helper writes the root slot and the state stack is untouched; at a
positive depth it rewrites the top byte to the state the top container's type
calls for. -/
def walkAfterValueMapAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sp : Nat) :
    Nat → UInt8 :=
  fun i => if sp = 0 then C.stMap i
    else if i = sp - 1 then
      UInt8.ofNat (if (C.tyMap (sp - 1)).toNat = 1 then 3 else 1)
    else C.stMap i

/-- The helper's map at the register's own depth. -/
def walkAfterValueMap {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : Nat → UInt8 :=
  walkAfterValueMapAt C C.sp

/-- At a positive depth the map is the top's rewrite. -/
theorem walkAfterValueMapAt_pos {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sp : Nat}
    (h : sp ≠ 0) :
    walkAfterValueMapAt C sp = fun i =>
      if i = sp - 1 then
        UInt8.ofNat (if (C.tyMap (sp - 1)).toNat = 1 then 3 else 1)
      else C.stMap i := by
  funext i
  simp only [walkAfterValueMapAt, h, ite_false]

/-- At depth zero the map is the carried one. -/
theorem walkAfterValueMapAt_zero {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {sp : Nat}
    (h : sp = 0) : walkAfterValueMapAt C sp = C.stMap := by
  funext i
  simp only [walkAfterValueMapAt, h, ite_true]

/-- The depth the helper receives is the register's own. -/
theorem walkAfterValue_sp {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) : (BitVec.ofNat 32 C.sp).toNat = C.sp := by
  have hcap := h.depth_cap
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [stage2StackExtent] at hcap
  omega

/-- **`s2_after_value` keeps the type stack.**  Its write is either the root slot
at the call's cursor or one byte of the state stack, and both miss the type
stack's carried extent. -/
theorem walkAfterValue_tyBytesAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {m : Mem} {sp : Nat}
    (hsp : sp ≤ stage2StackExtent)
    (hm : stage2AfterValue s.mem sp (G.next0 + 8) C.stage.ctype C.stage.cst = some m) :
    WalkStackBytes m C.stage.ctype C.tyMap C.wlen := by
  unfold stage2AfterValue at hm
  by_cases h0 : sp = 0
  · rw [ite_eq_left h0] at hm
    obtain rfl := (Option.some.inj hm).symm
    refine h.tyBytes.write_outside (Or.inr ?_)
    have hw : (wordBytes 4 1).length = 4 := by simp [wordBytes, natToBytes_length]
    have hse := C.stage.sevenEnd (C.stage.ctype, stage2StackExtent)
      (by simp [stage2StagedWrites])
    have hcap := h.wlen_cap
    have hS : stage2StackExtent = 520 := rfl
    simp only [stage2StackExtent] at hse hcap
    omega
  · rw [ite_eq_right h0] at hm
    cases hc : readByte s.mem (C.stage.ctype + (sp - 1)) with
    | none => rw [hc] at hm; exact absurd hm (by simp)
    | some ctv =>
      rw [hc] at hm
      obtain rfl := (Option.some.inj hm).symm
      refine h.tyBytes.write_outside ?_
      have hl : [UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)].length = 1 := rfl
      have hcap := h.wlen_cap
      have hS : stage2StackExtent = 520 := rfl
      simp only [stage2StackExtent] at hcap
      rcases ctype_cst_sep h with hs | hs
      · refine Or.inl ?_ ; omega
      · exact Or.inr (by omega)

/-- **`s2_after_value` advances the state stack's top.**  At depth zero the write
is the root slot and the map is the carried one; above it the byte at `sp - 1` is
the state the type stack's own top names, which is `walkAfterValueMapAt`'s entry —
provided the read index is inside the carried mark. -/
theorem walkAfterValue_stBytesAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {m : Mem} {sp : Nat}
    (hsp : sp ≤ stage2StackExtent) (hspw : sp = 0 ∨ sp - 1 < C.wlen)
    (hm : stage2AfterValue s.mem sp (G.next0 + 8) C.stage.ctype C.stage.cst = some m) :
    WalkStackBytes m C.stage.cst (walkAfterValueMapAt C sp) C.wlen := by
  unfold stage2AfterValue at hm
  by_cases h0 : sp = 0
  · rw [ite_eq_left h0] at hm
    obtain rfl := (Option.some.inj hm).symm
    rw [walkAfterValueMapAt_zero h0]
    refine h.stBytes.write_outside (Or.inr ?_)
    have hw : (wordBytes 4 1).length = 4 := by simp [wordBytes, natToBytes_length]
    have hse := C.stage.sevenEnd (C.stage.cst, stage2StackExtent)
      (by simp [stage2StagedWrites])
    have hcap := h.wlen_cap
    have hS : stage2StackExtent = 520 := rfl
    simp only [stage2StackExtent] at hse hcap
    omega
  · rw [ite_eq_right h0] at hm
    cases hc : readByte s.mem (C.stage.ctype + (sp - 1)) with
    | none => rw [hc] at hm; exact absurd hm (by simp)
    | some ctv =>
      rw [hc] at hm
      obtain rfl := (Option.some.inj hm).symm
      have hlt : sp - 1 < C.wlen := by rcases hspw with h | h <;> omega
      have hctv : ctv = C.tyMap (sp - 1) := by
        have hb := h.tyBytes.at hlt
        rw [hc] at hb
        exact Option.some.inj hb
      rw [hctv, walkAfterValueMapAt_pos h0]
      exact h.stBytes.storeAt (k := sp - 1)
        (v := UInt8.ofNat (if (C.tyMap (sp - 1)).toNat = 1 then 3 else 1))

/-- **A write at or above the call's cursor misses both stacks' carried marks**:
the seven staged objects, the stacks among them, end at or below the cursor. -/
theorem stack_alloca_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) {a : Nat} (ha : G.next0 ≤ a) :
    C.stage.ctype + C.wlen ≤ a ∧ C.stage.cst + C.wlen ≤ a := by
  have hcap := h.wlen_cap
  have hct := C.stage.sevenEnd (C.stage.ctype, stage2StackExtent)
    (by simp [stage2StagedWrites])
  have hcs := C.stage.sevenEnd (C.stage.cst, stage2StackExtent)
    (by simp [stage2StagedWrites])
  constructor <;> omega

/-- **The header's step**: one control step from the invariant at the header,
into `NodeBlock21`, with the index advanced, the depth read from the merge, the
invariant preserved and the measure strictly smaller. -/
theorem whileBody_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i")
    {k sp : Nat}
    (hpre : s.pre = some "cleanup478.i")
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkge : C.k < k) (hklt : k < G.nep) (hspc : sp ≤ stage2StackExtent)
    (hspw : sp ≤ C.wlen) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "NodeBlock21", k := k, sp := sp } e ∧
      walkMeasure G { C with block := "NodeBlock21", k := k, sp := sp } < walkMeasure G C ∧
      ∀ n, runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body e := by
  have hpc : s.pc = "while.body.i" := by rw [hInv.pc_eq, hblock]
  obtain ⟨h3, h5, hK, hct, hcst, hhash⟩ := hInv.ptrs
  -- the entry stream's lane, which is the next position
  obtain ⟨-, hget⟩ := readLanes32_nth (m := m0) (addr := G.ep) (n := G.nep)
    (l := G.ent) G.entries
  obtain ⟨q, bs, hqmem, hread0, hbs0⟩ := hget k hklt
  have hqin : q ∈ G.ent := List.mem_of_getElem? hqmem
  have hqn : q < G.n := G.inside q hqin
  -- its read at the run's memory, and the document's byte at that position
  have hread : readBytes s.mem (G.ep + k * 4) 4 = some bs := by
    rw [show G.ep + k * 4 = G.ep + 4 * k from by rw [Nat.mul_comm]]
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame)
      (a := G.ep + 4 * k) (n := 4)
      (fun i hi => hInv.entry_outside (by omega) (by omega))]
    exact hread0
  have hdocr : readBytes m0 (G.b + q) 1 = some [G.bs.getD q 0] :=
    walkReadBytes_one_of_readByte (readByte_of_readBytes G.doc (k := q) hqn)
  have hdoc : readBytes s.mem (G.b + q) 1 = some [G.bs.getD q 0] := by
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame)
      (a := G.b + q) (n := 1)
      (fun i hi => hInv.doc_outside (by omega) (by omega))]
    exact hdocr
  have hq32 : q < 2 ^ 32 := by
    rw [← hbs0]
    exact bytesToNat_lt_32 (walkReadBytes_length hread0)
  have hmax : G.n ≤ 2 ^ 32 := G.maxDoc
  have hk63 : k < 2 ^ 63 := by have h := G.nep_le; omega
  have hk64 : k + 1 < 2 ^ 64 := by have h := G.nep_le; omega
  -- the log's fields are untouched by the cursor store, and so is the trace
  have hcz := cursor_log_sep hInv
  have hcev : C.stage.c + stage2CursorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.c := by
    have h := stage2StagedWrites_against C.stage.separate
      (a := G.ev) (m := G.evcap) (stage2Regions_mem_ev)
      (r := (C.stage.c, stage2CursorExtent)) (by simp [stage2StagedWrites])
    simpa using h
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 : C.events.length ≤ C.k + 1 := by
      have h := hInv.events_le
      rw [hblock] at h
      have hone : walkEmitC "while.body.i" = 1 := walkEmitC_of_contains (by decide)
      omega
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  let e : State :=
    { (stateAt (whileBodyOut s.env k sp G.b G.ep C.stage.c q (G.bs.getD q 0))
        { s with mem := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (k + 1)) }) with
      pc := "NodeBlock21"
      pre := some "while.body.i" }
  have hstep : step calls stage2Body s = .jump e :=
    whileBody_term (calls := calls) (s := s) hpc h5 h3 hK hk2 hsp1 hpre
      hread hbs0 hdoc hq32 hk63 hk64
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := le_of_lt hklt
        events_le := by
          show C.events.length ≤ k + walkEmitC "NodeBlock21"
          have h := hInv.events_le
          rw [hblock] at h
          have h1 : walkEmitC "while.body.i" = 1 := walkEmitC_of_contains (by decide)
          have h2 : walkEmitC "NodeBlock21" = 0 := walkEmitC_of_not_contains (by decide)
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hspc
        depth_reg := ?_
        sp_le_wlen := hspw
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes.write_outside (by
          rcases (stack_c_sep hInv).1 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by
              have hw : (wordBytes 8 (k + 1)).length = 8 := by
                simp [wordBytes, natToBytes_length]
              have hc : stage2CursorExtent = 1192 := rfl
              omega))
        stBytes := hInv.stBytes.write_outside (by
          rcases (stack_c_sep hInv).2 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by
              have hw : (wordBytes 8 (k + 1)).length = 8 := by
                simp [wordBytes, natToBytes_length]
              have hc : stage2CursorExtent = 1192 := rfl
              omega))
        ptrs := ?_
        regs := by
          dsimp only [e]
          exact hInv.regs.names_of_eq ["%8", "%arrayidx10.i", "%idxprom.i", "%7",
            "%arrayidx.i", "%inc.i", "%sp.i.0248", "%k.0.i249"] rfl (by decide)
        iter :=
          { reg7 := ?_
            reg8 := ?_
            regarr := ?_ }
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        log_base := ?_
        log_dst := ?_
        owned := walkStaged_write rfl hInv.owned
        root_slot := by dsimp only [e]; exact hasBytes_writeBytes hInv.root_slot
        next_ge := hInv.next_ge
        frame := ?_
        inc_reg := by
          dsimp only [e, stateAt, whileBodyOut, cells]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
        idx_reg := by
          have hpos : entryPos G k = q := by simp [entryPos, hqmem]
          dsimp only [e, stateAt, whileBodyOut, cells]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_self, hpos]
        blockLocal := ?_ }
    · dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · dsimp only [e, stateAt]
      rw [readBytes_ev_of_cursor_write (c := C.stage.c) (ev := G.ev) (nev0 := G.nev0)
        (evcap := G.evcap) (N := (C.events.map EventRecord.encodedBytes).flatten.length)
        hcev (by simp [wordBytes, natToBytes_length]) hN]
      exact hInv.evBytes
    · dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_self]
    · dsimp only [e, stateAt]
      exact hInv.ptrs.cells_of _
        (fun c hc => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    · have hpos : entryPos G k = q := by simp [entryPos, hqmem]
      dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hpos]
    · have hpos : entryPos G k = q := by simp [entryPos, hqmem]
      have hbyte : entryByte G k = G.bs.getD q 0 := by simp [entryByte, hpos]
      dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_self, hbyte]
    · have hpos : entryPos G k = q := by simp [entryPos, hqmem]
      dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hpos]
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · dsimp only [e, stateAt]
      rw [readBytes_log_base_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length])]
      exact hInv.log_base
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 40) (len := 8) (by decide)]
      exact hInv.log_dst
    · dsimp only [e]
      exact walkFrame_cursorK (G := G) (C := C)
        (v := wordBytes 8 (k + 1)) (by simp [wordBytes, natToBytes_length]) hInv.frame
    · dsimp only [e]
      simpa [WalkLocal] using hklt
  · exact walkMeasure_step G C _ hkge (le_of_lt hklt) hInv.inner_cap
  · intro n
    rw [show 1 + n = n + 1 from by omega]
    simp only [runFuel, hstep]

end LeanLLVM.Refinement

/-! ### The header step's footprints, measured

Each is `#print axioms` on the declaration itself.  The three that read a
`String` register name — `whileBody_find`, its chain and its terminator — carry
`Classical.choice` beside `propext` and `Quot.sound`, which is the ceiling the
file's other pinned declarations report; the binding lemmas and the reads are at
or below `[propext, Quot.sound]`. -/

/-- info: 'LeanLLVM.Refinement.WalkPtrs.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkPtrs.bind

/-- info: 'LeanLLVM.Refinement.WalkPtrs.cells_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkPtrs.cells_of

/-- info: 'LeanLLVM.Refinement.walkReadBytes_writeBytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkReadBytes_writeBytes_outside

/-- info: 'LeanLLVM.Refinement.readLanes32_nth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.readLanes32_nth

/-- info: 'LeanLLVM.Refinement.stage2Regions_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.stage2Regions_sep

/-- info: 'LeanLLVM.Refinement.WalkInv.entry_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.entry_outside

/-- info: 'LeanLLVM.Refinement.WalkInv.doc_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.doc_outside

/-- info: 'LeanLLVM.Refinement.whileBody_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_find

/-- info: 'LeanLLVM.Refinement.whileBody_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_denote

/-- info: 'LeanLLVM.Refinement.whileBody_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_term

/-- info: 'LeanLLVM.Refinement.whileBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_step
