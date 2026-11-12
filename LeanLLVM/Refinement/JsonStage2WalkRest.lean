/-
The stage-2 walk's remaining census classes, and the two strengthenings the
census turned up.

`JsonStage2WalkScope` classifies the 165-block body and proves 95 of its blocks as
`WalkLink`s: classes A, B, B′, C, the five measure arms, and the two named arms
`while.body.i` and `if.end24.i`.  This module adds six links and the three
transfers the pure classes share.

## The transfers

A block whose run is straight-line needs three things of it: its `denoteCode`
equation, the names it does not bind, and the edge its terminator takes.
`walkCarried` names the eight registers `WalkInv` and `WalkPtrs` carry, and
`denoteCode_lookupName` turns "the run binds none of them" into the eight carried
facts, so a pure run's link needs no per-block environment reasoning beyond its
own `denoteCode`.  `WalkLink.pureCore` is that transfer with a `condbr` on a
computed or carried bit, `WalkLink.pureJumpCore` the same with a `br`, and
`WalkLink.pureCoreCarried` the `condbr` whose bit the run reads rather than binds
(`walkSkips` is the extra freshness fact that needs).  `WalkLink.pureJumpK11` is
the one variant the entry loop's preheader needs: `while.body.i.lr.ph` *is* the
binding of `%k11.i`, at the address the staging fixes, so its sixth pointer fact
is the run's conclusion and not a carried lookup.

## The links

* class H1's five `LeafBlock`s — `%.off = add i8 %NN, -9; %SwitchLeaf = icmp ule
  i8 %.off, 1` — through `WalkLink.addImmBr`, one lemma for the pair at the
  instruction's own width;
* `if.then281.i` (H2), `%add283.i`/`%conv284.i`/`%or.i`, through `pureJumpCore`.

## The two strengthenings

The census's survey of the four `unreachable` arms and of class E found two
statements in `WalkInv`/`WalkLocal` that were too weak, and both are now in
`JsonStage2WalkScope`:

* `WalkInv.pending_cursor` — `alen ≤ ndst0 + p` for the record in flight at entry
  position `p`.  It is the clause the arena reserve's guard (`if.end256.i` →
  `if.end.i83`) reads, and without it the arena trap is reachable under the
  invariant: a cursor at `ndst0 + n` with a positive-length token fails the guard.
  Every arm in `JsonStage2WalkScope` preserves the clause (all of them copy
  `pending` and `alen`), and the seed establishes it vacuously; its *production* is
  `if.end256.i` (`WalkLink.if_end256_i`), the block whose check reads it, and
  `if.else285.i` clears the record again once the window is decoded.  The clause is
  therefore one a traversal supplies at the reservation rather than one every carry
  leaves empty.
* `WalkLocal`'s landing facts are disjunctive.  A scan's landing block (`land.rhs*`)
  has two predecessors and only one of them is the latch, so `ScanLanded` (which
  names `pre = <latch>`) is not the entry edge's fact; `ScanEntered` is, and the
  disjunction is `ScanLanded ∨ ScanEntered`.  `for.body.i.i` is the same pair
  against `if.end48.i`.  This is what `pre` is for, and it costs nothing at the
  arms: they prove the left disjunct.  What the entry edges still need is the inner
  reset — see the measure note below.

## What is not here

* H2's `while.body.i.lr.ph` (`JsonStage2WalkEntry`) and class G's fourteen reads
  (`JsonStage2WalkPure`): each needs its outgoing environment written out so its
  `denoteCode` equality is a term the transfer consumes.  The class lemmas take
  `denoteCode ... = some s₁`, and `s₁`'s memory and `pc` are only visible from that
  term, so the instance states it.  The five `LeafBlock` instances show the shape.
* class D's ten stores (`JsonStage2WalkStore`) and E's merges that write
  (`if.end372.i`, `while.end78.i`, `if.then57.i`, in `JsonStage2WalkPhi`) — the
  memory clauses each owes are `JsonStage2WalkScope`'s class C reasoning at a new
  address, and `if.end372.i`'s token-slot write is carried by `frame` alone.
* **the scan-entry measure — resolved**.  The disjunctive landing fact names the
  entry edge's counter, and the edge must also say what `C.inner` is there.  Under a
  measure whose inner component is the current scan's remaining work an entry resets
  it upward whenever a later scan has more work than the earlier one left, and
  `WalkLink.mono` fails.  The measure's inner component is therefore the iteration's
  shared budget — `walkInnerCap G = 4 * G.n + 5`, refilled at the loop head and drawn
  on by every scan — and an entry edge leaves it alone: `JsonStage2WalkEntry` has
  `if.end48.i`, `cond.end.i96`, and the two landed links whose landing fact was an
  argument.  The escapes' entry (`if.then447.i`) is a call block, so it stays F's.
* **class F's contract gap.**  All nineteen call blocks resolve through
  `stage2Calls`, which leaves `s2_init`, `s2_value_pos`, `s2_after_value`,
  `s2_string_body`, `num_fast_el1` and `od_scalar_value` to the `sub` parameter.  A
  call block's link is therefore the callee's `CallOutcome` at the caller's staging,
  and two shapes need what no current contract gives: the blocks that read a
  returned word (`if.end256.i` reads `%call272.i`'s successors, `if.then328.i` reads
  `%outn.i`) need the callee's **frame** as well as its post, and
  `z_arena_reserve.exit` needs the reservation to be the cursor's — the datum
  `WalkInv.pending_cursor` reads.  The six helpers' contracts are stated and proved
  at their call boundary in `JsonStage2Helpers`; turning them into F links also
  needs the walk's `frame` claim over the four body-allocated objects (`%ei.i`,
  `%root_done.i`, `%xj.i`, `%outn.i`), and no F link is claimed here.
-/
import LeanLLVM.Refinement.JsonStage2WalkScope
import LeanLLVM.Refinement.JsonScanLane

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane

/-! ### The chain steps the classes below need

`walk_step` (`JsonStage2WalkScope`) covers the shapes the two named arms and the
scans use.  The dispatch's remaining pure runs read words (`load i64`), compare
at widths and predicates beyond `eq` at 64 bits, and bind the arithmetic in
`JsonScanLane`'s width-generic steps.  This is that list plus those. -/
macro "walk_step_rest" : tactic => `(tactic|
  (first
   | rw [denoteCode_gep8_lit_w _ _ _ _ _ ?_ _]
   | rw [walkDenoteCode_gep8_imm _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_zext32_64_ofNat _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_zext _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_trunc _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep8_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep32_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep8_reg _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load_i32 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load32 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load_i8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load8_single _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store64_ofNat _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_store32 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_eq_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_one_ofNat _ _ _ _ _ _ ?_ _]
   | rw [walkDenoteCode_add_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_sub_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_xor_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_xor_imm_w _ _ _ _ _ ?_ _]
   | rw [denoteCode_and_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_or_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_and_imm_w _ _ _ _ _ ?_ _]
   | rw [denoteCode_or_imm_w _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_eq_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_ult_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_ult_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_imm_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_select_bit_imm_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_reg_imm_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_reg_w _ _ _ _ _ _ ?_ ?_ ?_ _]
   | block_phi_run))

macro "walk_eval_rest" : tactic => `(tactic|
  (repeat walk_step_rest
   walk_close
   all_goals (try omega)))

namespace WalkScope

/-! ### The carried names a pure run leaves alone

`WalkPtrs` names six registers, and `WalkInv` two more (`%k.0.i249`,
`%sp.i.0248`).  A block that binds none of them keeps all eight facts by
`denoteCode_lookupName`, so its link needs no per-block environment reasoning:
the freshness is one `decide` over the block's own instruction list. -/
def walkCarried (is : List Instr) : Prop :=
  ∀ i ∈ is, i.dst? ≠ some "%k.0.i249" ∧ i.dst? ≠ some "%sp.i.0248" ∧
    i.dst? ≠ some "%3" ∧ i.dst? ≠ some "%5" ∧ i.dst? ≠ some "%k11.i" ∧
    i.dst? ≠ some "%ctype.i" ∧ i.dst? ≠ some "%cst.i" ∧
    i.dst? ≠ some "%hash1.i.i" ∧
    (∀ n ∈ walkStaticNames, i.dst? ≠ some n) ∧
    i.dst? ≠ some "%7" ∧ i.dst? ≠ some "%8"

/-- **A run that binds none of the carried names keeps the static carrier.**  One
`denoteCode_lookupName` per name, and no memory reasoning. -/
theorem WalkRegs.of_run {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s s₁ : State} {is : List Instr} (h : WalkRegs G C s.env)
    (hfree : walkCarried is) (hden : denoteCode calls is s = some s₁) :
    WalkRegs G C s₁.env := by
  intro p hp
  rw [denoteCode_lookupName calls is p.1
    (fun i hi => (hfree i hi).2.2.2.2.2.2.2.2.1 p.1 (by
      rw [← walkStaticRegs_names G C]
      exact List.mem_map_of_mem hp)) s s₁ hden]
  exact h p hp

/-- **A run that binds neither `%7` nor `%8` keeps the per-iteration carrier.** -/
theorem WalkIter.of_run {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {k : Nat}
    {s s₁ : State} {is : List Instr} (h : WalkIter G k s.env)
    (hfree : walkCarried is) (hden : denoteCode calls is s = some s₁) :
    WalkIter G k s₁.env := by
  refine ⟨?_, ?_⟩
  · rw [denoteCode_lookupName calls is "%7"
      (fun i hi => (hfree i hi).2.2.2.2.2.2.2.2.2.1) s s₁ hden]
    exact h.reg7
  · rw [denoteCode_lookupName calls is "%8"
      (fun i hi => (hfree i hi).2.2.2.2.2.2.2.2.2.2) s s₁ hden]
    exact h.reg8

theorem WalkPtrs.of_run {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s s₁ : State} {is : List Instr} (h : WalkPtrs G C s.env)
    (hfree : walkCarried is) (hden : denoteCode calls is s = some s₁) :
    WalkPtrs G C s₁.env := by
  obtain ⟨h3, h5, hk, hc, hs, hh⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [denoteCode_lookupName _ is "%3" (fun i hi => (hfree i hi).2.2.1) s s₁ hden]; exact h3
  · rw [denoteCode_lookupName _ is "%5" (fun i hi => (hfree i hi).2.2.2.1) s s₁ hden]; exact h5
  · rw [denoteCode_lookupName _ is "%k11.i" (fun i hi => (hfree i hi).2.2.2.2.1) s s₁ hden]; exact hk
  · rw [denoteCode_lookupName _ is "%ctype.i" (fun i hi => (hfree i hi).2.2.2.2.2.1) s s₁ hden]
    exact hc
  · rw [denoteCode_lookupName _ is "%cst.i" (fun i hi => (hfree i hi).2.2.2.2.2.2.1) s s₁ hden]
    exact hs
  · rw [denoteCode_lookupName _ is "%hash1.i.i" (fun i hi => (hfree i hi).2.2.2.2.2.2.2.1) s s₁ hden]
    exact hh

/-- **A pure run's invariant transfer.**  The block binds no carried register, so
`blockIndex`, `depth_reg` and `ptrs` are the run's pre-state facts; its memory is
unchanged, so the six memory clauses are `hmem`'s; and only the block-local fact
and the edge are the caller's. -/
theorem WalkLink.pureCore {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode calls B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hmem : s₁.mem = s.mem) (hpc₁ : s₁.pc = s.pc)
    {d tl fl : String} (hterm : B.term = Term.condbr (.reg d) tl fl)
    {bit : BitVec 1} (hbit : lookupName s₁.env d = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s₁ with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s₁ with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if bit = 1 then tl else fl) } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s₁ with pc := (if bit = 1 then tl else fl), pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := d) (tl := tl) (fl := fl) (bit := bit) hbit]
    dsimp only [s']
    rw [hpc₁]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
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
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        regs := by dsimp only [s']; exact WalkRegs.of_run hInv.regs hfree hden
        iter := by dsimp only [s']; exact WalkIter.of_run hInv.iter hfree hden
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := by dsimp only [s']; rw [hmem]; exact hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [denoteCode_lookupName calls B.instrs "%k.0.i249"
        (fun i hi => (hfree i hi).1) s s₁ hden]
      exact hInv.blockIndex
    · dsimp only [s']
      rw [hmem]; exact hInv.evBytes
    · rw [denoteCode_lookupName calls B.instrs "%sp.i.0248"
        (fun i hi => (hfree i hi).2.1) s s₁ hden]
      exact hInv.depth_reg
    · dsimp only [s']
      exact WalkPtrs.of_run hInv.ptrs hfree hden
    · dsimp only [s']
      rw [hmem]; exact hInv.log_hash
    · dsimp only [s']
      rw [hmem]; exact hInv.log_len
    · dsimp only [s']
      rw [hmem]; exact hInv.log_cap
    · dsimp only [s']
      rw [hmem]; exact hInv.log_alen
    · dsimp only [s']
      rw [hmem]; exact hInv.log_acap
    · dsimp only [s']
      rw [hmem]; exact hInv.frame
    · dsimp only [s']
      by_cases ht : bit = 1
      · rw [ite_eq_left ht]; exact hl
      · rw [ite_eq_right ht]; exact hf
  · rfl

/-- **A pure run's jump.**  The block binds only fresh names, writes nothing, and
leaves by `br`. -/
theorem WalkLink.pureJumpCore {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode calls B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hmem : s₁.mem = s.mem) (hpc₁ : s₁.pc = s.pc)
    {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s₁ with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s { C with block := t } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s₁ with pc := t, pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s']
    rw [hpc₁]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
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
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        regs := by dsimp only [s']; exact WalkRegs.of_run hInv.regs hfree hden
        iter := by dsimp only [s']; exact WalkIter.of_run hInv.iter hfree hden
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := by dsimp only [s']; rw [hmem]; exact hInv.owned
        frame := ?_
        blockLocal := hloc }
    · rw [denoteCode_lookupName calls B.instrs "%k.0.i249"
        (fun i hi => (hfree i hi).1) s s₁ hden]
      exact hInv.blockIndex
    · dsimp only [s']
      rw [hmem]; exact hInv.evBytes
    · rw [denoteCode_lookupName calls B.instrs "%sp.i.0248"
        (fun i hi => (hfree i hi).2.1) s s₁ hden]
      exact hInv.depth_reg
    · dsimp only [s']
      exact WalkPtrs.of_run hInv.ptrs hfree hden
    · dsimp only [s']
      rw [hmem]; exact hInv.log_hash
    · dsimp only [s']
      rw [hmem]; exact hInv.log_len
    · dsimp only [s']
      rw [hmem]; exact hInv.log_cap
    · dsimp only [s']
      rw [hmem]; exact hInv.log_alen
    · dsimp only [s']
      rw [hmem]; exact hInv.log_acap
    · dsimp only [s']
      rw [hmem]; exact hInv.frame
  · rfl


/-! ### Class H1: the negative literal's `add` and an unsigned `ule`

The five `LeafBlock`s of the dispatch's switch are two instructions each:
`%.off = add i8 %NN, -9` and `%SwitchLeaf = icmp ule i8 %.off, 1`, then the edge
on the `ule`'s bit (`land.rhs.i.preheader` is the whitespace skip's entry and
`if.end372.i` the exit; the three others are the same pair with their own leaves).
`-9` is written as the literal `247` at the instruction's width.  The class is
`WalkLink.pureCore` at the run: no carried register is bound, the memory is
untouched, and the edge is the compared bit's. -/

/-- **Class H1: the arithmetic latch in front of a switch leaf's comparison.** -/
theorem WalkLink.addImmBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {reg off d tl fl : String} {x c one : BitVec 8}
    (hinstrs : B.instrs = [Instr.binop off BinOp.add 8 (.reg reg) (.imm (.int 8 c)),
      Instr.icmp d IPred.ule 8 (.reg off) (.imm (.int 8 one))])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hreg : lookupName s.env reg = some (.int 8 x))
    (hfree : walkCarried B.instrs)
    (hl : WalkLocal { C with block := tl }
      { stateAt (cells [(d, .int 1 (evalICmp .ule (x + c) one)), (off, .int 8 (x + c))] s.env) s with
        pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl }
      { stateAt (cells [(d, .int 1 (evalICmp .ule (x + c) one)), (off, .int 8 (x + c))] s.env) s with
        pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + c) one = 1 then tl else fl) } s' := by
  have hden : denoteCode calls B.instrs s =
      some (stateAt (cells [(d, .int 1 (evalICmp .ule (x + c) one)),
        (off, .int 8 (x + c))] s.env) s) := by
    rw [hinstrs, ← stateAt_self s,
      walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := off) (a := reg)
        (w := 8) (x := x) (c := c) hreg]
    rw [walkDenoteCode_icmp (calls := calls) (env := (off, .int 8 (x + c)) :: s.env) (s := s)
      d 8 IPred.ule (x := x + c) (y := one)
      (by simp only [stateAt, evalOperand, lookupName_cons_self])
      (by exact evalOperand_lit_of _ _ _) []]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv hfind hden hfree rfl rfl hterm
    (by simp only [stateAt, cells, lookupName_cons_self]) hl hf

/-- `LeafBlock33`: the whitespace skip's leaf, `%35`'s range. -/
def walkLeafBlock33 : Block :=
  { name := "LeafBlock33",
    instrs := [Instr.binop "%.off" BinOp.add 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf34" IPred.ule 8 (Operand.reg "%.off") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (Operand.reg "%SwitchLeaf34") "land.rhs.i.preheader" "if.end372.i" }

theorem walkLeafBlock33_find : stage2Body.findBlock "LeafBlock33" = some walkLeafBlock33 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock33]

theorem WalkLink.LeafBlock33 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock33")
    {x : BitVec 8} (h35 : lookupName s.env "%35" = some (.int 8 x))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "land.rhs.i.preheader" else "if.end372.i") } s' := by
  exact WalkLink.addImmBr (G := G) (C := C) (s := s) hInv
    (B := walkLeafBlock33) (by rw [hblock]; exact walkLeafBlock33_find) rfl rfl h35
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock43`: the whitespace skip's own leaf, `%36`'s range. -/
def walkLeafBlock43 : Block :=
  { name := "LeafBlock43",
    instrs := [Instr.binop "%.off44" BinOp.add 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf45" IPred.ule 8 (Operand.reg "%.off44") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (Operand.reg "%SwitchLeaf45") "if.end372.i" "while.body370.i" }

theorem walkLeafBlock43_find : stage2Body.findBlock "LeafBlock43" = some walkLeafBlock43 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock43]

theorem WalkLink.LeafBlock43 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock43")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hs : WalkLocal { C with block := "while.body370.i" }
      { stateAt (cells [("%SwitchLeaf45", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off44", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body370.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "if.end372.i" else "while.body370.i") } s' := by
  exact WalkLink.addImmBr (G := G) (C := C) (s := s) hInv
    (B := walkLeafBlock43) (by rw [hblock]; exact walkLeafBlock43_find) rfl rfl h36
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) hs

/-- `LeafBlock64`: the string scan's leaf, `%40`'s range. -/
def walkLeafBlock64 : Block :=
  { name := "LeafBlock64",
    instrs := [Instr.binop "%.off65" BinOp.add 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf66" IPred.ule 8 (Operand.reg "%.off65") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (Operand.reg "%SwitchLeaf66") "while.end.i" "while.body.i104" }

theorem walkLeafBlock64_find : stage2Body.findBlock "LeafBlock64" = some walkLeafBlock64 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock64]

theorem WalkLink.LeafBlock64 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock64")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x))
    (hs : WalkLocal { C with block := "while.body.i104" }
      { stateAt (cells [("%SwitchLeaf66", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off65", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body.i104", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "while.end.i" else "while.body.i104") } s' := by
  exact WalkLink.addImmBr (G := G) (C := C) (s := s) hInv
    (B := walkLeafBlock64) (by rw [hblock]; exact walkLeafBlock64_find) rfl rfl h40
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) hs

/-- `LeafBlock85`: the escape scan's leaf, `%46`'s range. -/
def walkLeafBlock85 : Block :=
  { name := "LeafBlock85",
    instrs := [Instr.binop "%.off86" BinOp.add 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf87" IPred.ule 8 (Operand.reg "%.off86") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (Operand.reg "%SwitchLeaf87") "while.body76.i" "while.end78.i" }

theorem walkLeafBlock85_find : stage2Body.findBlock "LeafBlock85" = some walkLeafBlock85 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock85]

theorem WalkLink.LeafBlock85 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock85")
    {x : BitVec 8} (h46 : lookupName s.env "%46" = some (.int 8 x))
    (hs : WalkLocal { C with block := "while.body76.i" }
      { stateAt (cells [("%SwitchLeaf87", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off86", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body76.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "while.body76.i" else "while.end78.i") } s' := by
  exact WalkLink.addImmBr (G := G) (C := C) (s := s) hInv
    (B := walkLeafBlock85) (by rw [hblock]; exact walkLeafBlock85_find) rfl rfl h46
    (by unfold walkCarried; decide)
    hs (by simp [WalkLocal])

/-- `LeafBlock96`: the extra-token scan's leaf, `%47`'s range. -/
def walkLeafBlock96 : Block :=
  { name := "LeafBlock96",
    instrs := [Instr.binop "%.off97" BinOp.add 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf98" IPred.ule 8 (Operand.reg "%.off97") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (Operand.reg "%SwitchLeaf98") "while.body462.i" "if.then467.i" }

theorem walkLeafBlock96_find : stage2Body.findBlock "LeafBlock96" = some walkLeafBlock96 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock96]

theorem WalkLink.LeafBlock96 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock96")
    {x : BitVec 8} (h47 : lookupName s.env "%47" = some (.int 8 x))
    (hs : WalkLocal { C with block := "while.body462.i" }
      { stateAt (cells [("%SwitchLeaf98", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off97", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body462.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "while.body462.i" else "if.then467.i") } s' := by
  exact WalkLink.addImmBr (G := G) (C := C) (s := s) hInv
    (B := walkLeafBlock96) (by rw [hblock]; exact walkLeafBlock96_find) rfl rfl h47
    (by unfold walkCarried; decide)
    hs (by simp [WalkLocal])


/-! ### The pointer block's run

`while.body.i.lr.ph` binds five addresses of which one — `%k11.i` — is a
`WalkPtrs` register: the block *is* the binding, at the address the staging fixes
(`%c.i + 32`).  So its run is pure for the other seven carried names and the
sixth pointer fact is the run's own conclusion, which is the one difference from
`pureJumpCore`. -/
def walkCarriedNoK11 (is : List Instr) : Prop :=
  ∀ i ∈ is, i.dst? ≠ some "%k.0.i249" ∧ i.dst? ≠ some "%sp.i.0248" ∧
    i.dst? ≠ some "%3" ∧ i.dst? ≠ some "%5" ∧
    i.dst? ≠ some "%ctype.i" ∧ i.dst? ≠ some "%cst.i" ∧
    i.dst? ≠ some "%hash1.i.i"

theorem WalkPtrs.of_run_noK11 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s s₁ : State} {is : List Instr} (h : WalkPtrs G C s.env)
    (hfree : walkCarriedNoK11 is) (hden : denoteCode calls is s = some s₁)
    (hk11 : lookupName s₁.env "%k11.i" = some (.ptr (C.stage.c + 32))) :
    WalkPtrs G C s₁.env := by
  obtain ⟨h3, h5, -, hc, hs, hh⟩ := h
  refine ⟨?_, ?_, hk11, ?_, ?_, ?_⟩
  · rw [denoteCode_lookupName _ is "%3" (fun i hi => (hfree i hi).2.2.1) s s₁ hden]; exact h3
  · rw [denoteCode_lookupName _ is "%5" (fun i hi => (hfree i hi).2.2.2.1) s s₁ hden]; exact h5
  · rw [denoteCode_lookupName _ is "%ctype.i" (fun i hi => (hfree i hi).2.2.2.2.1) s s₁ hden]
    exact hc
  · rw [denoteCode_lookupName _ is "%cst.i" (fun i hi => (hfree i hi).2.2.2.2.2.1) s s₁ hden]
    exact hs
  · rw [denoteCode_lookupName _ is "%hash1.i.i" (fun i hi => (hfree i hi).2.2.2.2.2.2) s s₁ hden]
    exact hh

/-- **A run that binds `%k11.i` to the staging's cursor slot, and jumps.** -/
theorem WalkLink.pureJumpK11 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode calls B.instrs s = some s₁)
    (hfree : walkCarriedNoK11 B.instrs) (hmem : s₁.mem = s.mem) (hpc₁ : s₁.pc = s.pc)
    (hregs : WalkRegs G C s₁.env) (hiter : WalkIter G C.k s₁.env)
    (hk11 : lookupName s₁.env "%k11.i" = some (.ptr (C.stage.c + 32)))
    {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s₁ with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s { C with block := t } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s₁ with pc := t, pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s']
    rw [hpc₁]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
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
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        regs := hregs
        iter := hiter
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := by dsimp only [s']; rw [hmem]; exact hInv.owned
        frame := ?_
        blockLocal := hloc }
    · rw [denoteCode_lookupName calls B.instrs "%k.0.i249"
        (fun i hi => (hfree i hi).1) s s₁ hden]
      exact hInv.blockIndex
    · dsimp only [s']
      rw [hmem]; exact hInv.evBytes
    · rw [denoteCode_lookupName calls B.instrs "%sp.i.0248"
        (fun i hi => (hfree i hi).2.1) s s₁ hden]
      exact hInv.depth_reg
    · dsimp only [s']
      exact WalkPtrs.of_run_noK11 hInv.ptrs hfree hden hk11
    · dsimp only [s']
      rw [hmem]; exact hInv.log_hash
    · dsimp only [s']
      rw [hmem]; exact hInv.log_len
    · dsimp only [s']
      rw [hmem]; exact hInv.log_cap
    · dsimp only [s']
      rw [hmem]; exact hInv.log_alen
    · dsimp only [s']
      rw [hmem]; exact hInv.log_acap
    · dsimp only [s']
      rw [hmem]; exact hInv.frame
  · rfl

/-! ### Class H2: the entry loop's five addresses, and the literal's `or` -/

/-- `while.body.i.lr.ph`: the five addresses the dispatch reads, and the edge into
the loop. -/
def walkWhileBodyLrPh : Block :=
  { name := "while.body.i.lr.ph",
    instrs := [
      Instr.gep "%k11.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.gep "%h1.i.i.i51" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.gep "%gap.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 20))),
      Instr.gep "%end.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.gep "%kind404.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16)))],
    term := Term.br "while.body.i" }

theorem walkWhileBodyLrPh_find :
    stage2Body.findBlock "while.body.i.lr.ph" = some walkWhileBodyLrPh := by
  simp [stage2Body, Function.findBlock, findBlockList, walkWhileBodyLrPh]

-- `while.body.i.lr.ph` is `WalkLink.pureJumpK11`'s instance: its five addresses are
-- literal-offset `getelementptr`s and its only carried bind is `%k11.i` at
-- `%c.i + 32`, which the class lemma's `hk11` reads.  Its `denoteCode` equality is
-- the remaining instance work; the block's shape is pinned by `walkWhileBodyLrPh`
-- below, which is also the class's statement check.
/-- `if.then281.i`: the literal's `add`, `zext` and high-bit `or`. -/
def walkIf_then281_i : Block :=
  { name := "if.then281.i",
    instrs := [
      Instr.binop "%add283.i" BinOp.add 32 (Operand.reg "%7") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.zext "%conv284.i" 32 64 (Operand.reg "%add283.i"),
      Instr.binop "%or.i" BinOp.or 64 (Operand.reg "%conv284.i")
        (Operand.imm (.int 64 (BitVec.ofNat 64 9223372036854775808)))],
    term := Term.br "if.end290.i" }

theorem walkIf_then281_i_find : stage2Body.findBlock "if.then281.i" = some walkIf_then281_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then281_i]

theorem WalkLink.if_then281_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then281.i")
    {x7 : BitVec 32} (h7 : lookupName s.env "%7" = some (.int 32 x7))
    : ∃ s', WalkLink calls G C s { C with block := "if.end290.i" } s' := by
  have hden : denoteCode calls walkIf_then281_i.instrs s =
      some (stateAt (cells [("%or.i", .int 64 (BitVec.ofNat 64
          (x7 + BitVec.ofNat 32 1).toNat ||| BitVec.ofNat 64 9223372036854775808)),
        ("%conv284.i", .int 64 (BitVec.ofNat 64 (x7 + BitVec.ofNat 32 1).toNat)),
        ("%add283.i", .int 32 (x7 + BitVec.ofNat 32 1))] s.env) s) := by
    simp only [walkIf_then281_i]
    rw [← stateAt_self s]
    rw [denoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := "%add283.i")
      (a := "%7") (w := 32) (x := x7) (c := BitVec.ofNat 32 1) h7]
    rw [denoteCode_zext (calls := calls)
      (env := ("%add283.i", .int 32 (x7 + BitVec.ofNat 32 1)) :: s.env) (s := s)
      (d := "%conv284.i") (v := "%add283.i") 32 64 (x := x7 + BitVec.ofNat 32 1)
      (by simp only [stateAt, evalOperand, lookupName_cons_self])]
    rw [denoteCode_or_imm_w (calls := calls)
      (env := ("%conv284.i", .int 64 (BitVec.ofNat 64 (x7 + BitVec.ofNat 32 1).toNat)) ::
        ("%add283.i", .int 32 (x7 + BitVec.ofNat 32 1)) :: s.env) (s := s)
      (d := "%or.i") (a := "%conv284.i") (w := 64)
      (x := BitVec.ofNat 64 (x7 + BitVec.ofNat 32 1).toNat)
      (c := BitVec.ofNat 64 9223372036854775808)
      (by simp only [stateAt, evalOperand, lookupName_cons_self])]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_then281_i) (by rw [hblock]; exact walkIf_then281_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (by simp [WalkLocal])


/-! ### The carried-bit and jump shapes

A block that only loads and then branches on a bit it did not compute is a pure
run whose branch register is the caller's: `denoteCode_lookupName` carries the
lookup through the run, so the class is the jump/`condbr` transfer with the
branch fact named at the pre-state. -/
/-- A run binds no occurrence of a fixed name. -/
def walkSkips (n : String) (is : List Instr) : Prop := ∀ i ∈ is, i.dst? ≠ some n

/-- **A pure run's `condbr` on a carried bit.** -/
theorem WalkLink.pureCoreCarried {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {s₁ : State} (hden : denoteCode calls B.instrs s = some s₁)
    (hfree : walkCarried B.instrs) (hmem : s₁.mem = s.mem) (hpc₁ : s₁.pc = s.pc)
    {d tl fl : String} (hterm : B.term = Term.condbr (.reg d) tl fl)
    {bit : BitVec 1} (hbit : lookupName s.env d = some (.int 1 bit))
    (hneD : walkSkips d B.instrs)
    (hl : WalkLocal { C with block := tl } { s₁ with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s₁ with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if bit = 1 then tl else fl) } s' := by
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv hfind hden hfree hmem hpc₁ hterm ?_ hl hf
  rw [denoteCode_lookupName calls B.instrs d hneD s s₁ hden]
  exact hbit

-- The four jump shapes these classes cover (`cond.true345.i`, `cond.true.i106`,
-- `land.lhs.true357.i`, `if.then231.i`) and the carried-bit `condbr`
-- (`if.end74.i`) are instances of the two transfers above; their `denoteCode`
-- equalities are the G instances `JsonStage2WalkPure` supplies (`WalkLink.cond_true345_i`,
-- `WalkLink.cond_true_i106`, `WalkLink.land_lhs_true357_i`, `WalkLink.if_then231_i`
-- and `WalkLink.if_end74_i`).



/-! ### The event reserve's guard, at the invariant

Two of the four `unreachable` arms guard the event stream's reserves: `if.end.i.i`
and `if.end.i.i55` test `len + 1 > cap` for the record's tag byte, and `if.end290.i`
tests `len + 13 > cap` for a whole record.  Both are clear at any state of the loop
whose entry index is strictly inside the stream: the trace is at most one record per
entry consumed (`events_le`), so the cursor is at most `nev0 + 13·k`, and
`k ≤ nep - 1 ≤ n - 1` leaves more than a record's width in `G.evRoom`'s slack.

This is the guard's arithmetic.  It is not the branch bit: that is the block's own
`denoteCode` (`if.end.i.i`'s four instructions), which is one of the G instances this
module does not reach. -/
theorem walkEventReserve_clear {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hkl : C.k < G.nep) :
    C.evlen + 1 ≤ G.evcap ∧ C.evlen + 13 ≤ G.evcap := by
  have hsum := EventRecord.sum_encodedSize_le C.events
  simp only [stage2RecordBytes] at hsum
  have hlen : C.evlen ≤ G.nev0 + 13 * C.k := by
    rw [hInv.evlen_eq]
    have := Nat.mul_le_mul_left 13 hInv.events_le
    omega
  have hroom : G.nev0 + 13 * G.n ≤ G.evcap := G.evRoom
  have hnep : G.nep ≤ G.n := G.nep_le
  omega

/-! ### The instrument

The module's declarations' axiom footprints, measured rather than asserted.  The
two ends are the ones `JsonStage2WalkScope` names for the walk: `WalkPtrs.bind`
(the pure environment step) and `whileBody_step` (the header's step at the whole
frame). -/
/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.pureCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.pureCore

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.pureJumpCore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.pureJumpCore

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.addImmBr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.addImmBr

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock33

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock43

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock64

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock85' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock85

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock96' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock96

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then281_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then281_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkPtrs.of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkPtrs.of_run

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEventReserve_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEventReserve_clear

end WalkScope

end LeanLLVM.Refinement

