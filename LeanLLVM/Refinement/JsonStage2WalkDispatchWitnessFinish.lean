import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessState

/-! # The `finish` alternative

`WalkDispatchThree.ofContinueAndLast`'s other terminal outcome: the dispatch consumed the
last entry and the merge at `cleanup478.i` selects the *terminal* index, `%k.2.i = %nep`.
The dispatch note's longest path is the twenty-two blocks from `while.body.i` to the merge,
and the refusal module's three instruments carry over unchanged — a named prefix per state,
peels stated in the form the elaborator reduces (`lookupName`, closed by `rfl`), and the
trace split into segments composed by `WalkSegment.trans`.

**What this file has so far.**  The path's empty-body blocks, whose step is one `br`: the
elaborator's `walkBrStep` gives the successor outright, and naming it costs only
`Ctrl.jump`'s injectivity.

**What the rest of the path owes, block by block.**  The pattern is the layer's where a
fact's producer is elsewhere (`walkIfThen_step`): the block's `denoteCode` is the caller's
hypothesis and the step names the successor.  Which core a block needs depends on whether
it touches memory, and on whether its call's result is a contract:

| block | core | the hypothesis it owes |
|---|---|---|
| `cond.true345.i` | `pureCore` (no store) | the entry stream's lane read at `%inc.i` — `%5 + %inc.i`'s 32-bit word, which the geometry's `entries` gives at the index |
| `if.end372.i` | store variant (`refusalStore`'s shape) | `denoteCode` **and** the frame for its store through `%end.i`; its `phi` over eight predecessors is `cleanup478_denote`'s sibling |
| `if.then413.i` | store variant + call | `denoteCode`, which consumes `s2_value_pos`'s contract at this call site, plus the frame for the `%kind404.i` store |
| `if.then425.i` | call consumer | **`od_scalar_value`'s contract at `(%c.i, %t352.i, %z)`**, then the frame for its writes |
| `if.then447.i` | call consumer | **`s2_after_value`'s contract** at the two stack pointers, then the scan's test |
| `if.end473.i` | `pureCore` (no store) | only `denoteCode`: `llvm.lifetime.end.p0` writes nothing, so `hmem` is `rfl` |
| `cleanup478.i` | `pureCore` (no store) | the two `phi`s' selection at `pre = some "if.end473.i"` — `cleanup478_denote` is exactly that, and `%cmp.i`'s bit picks `while.body.i` or `if.then485.i` |

Three of the seven therefore fit `pureCore`'s no-store shape and are one `denoteCode` away;
two need the store variant of the same pattern, where the frame is the extra obligation as it
was for `if.end59.i`'s nesting check; and two are *call* consumers, whose step is honest only
with the helper's contract named as its hypothesis — `s2_value_pos`, `od_scalar_value` and
`s2_after_value`, in the handoff's own names.

That is why this file is sized rather than finished: the refusal side of `hlast` is closed by
the witness modules, and `finish`'s remaining work is these seven blocks, four of which are
contract consumers rather than block arithmetic.-/

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-- **`if.else387.i`'s target, named.**  An empty body and one `br`: the successor is the
state itself at `NodeBlock62`. -/
theorem walkIfElse387_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i") :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock62" } s' ∧
      s' = { s with pc := "NodeBlock62", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_else387_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_else387_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_else387_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_else387_i)
    (dest := "NodeBlock62") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.then403.i`'s target, named.**  An empty body and one `br`, at `if.then413.i`. -/
theorem walkIfThen403_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then403.i") :
    ∃ (s' : State), WalkLink calls G C s { C with block := "if.then413.i" } s' ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_then403_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_then403_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_then403_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_then403_i)
    (dest := "if.then413.i") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.then403.i`'s step as a segment.**  One link is `WalkSegment.of_link`'s count, so
the path's empty blocks enter the algebra with no extra machinery: the segment carries the
successor's carry, state and invariant, which is what a composition consumes. -/
theorem walkIfThen403_seg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then403.i") :
    ∃ (C' : WalkCarry G) (s' : State), WalkSegment calls G C s C' s' 1 ∧
      C' = { C with block := "if.then413.i" } ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } ∧
      WalkInv G C' s' := by
  obtain ⟨s', hl, hs'⟩ := walkIfThen403_at (calls := calls) G C s hInv hblock
  exact ⟨_, s', WalkSegment.of_link hl, rfl, hs', hl.inv'⟩

/-! ### The merge's other arm

`cleanup478_denote` states the merge at `k2 < nepv.toNat`, which is the *back edge*: the
`icmp .ult` is one, and the successor is `while.body.i`.  The `finish` outcome needs the
same phi selection with the test **false** — `k2 = nepv.toNat`, the terminal index — whose
successor is `if.then485.i`.  The lemma is restated here as the twin rather than changed,
because `WalkScope`'s form is the loop's and this one is the exit's: the two differ in the
bit and in nothing else. -/

/-- **The merge's `denoteCode` at the terminal index.**  The two `phi`s select the
dispatch's depth and index, and `%cmp.i` is zero because the index has reached the entry
count. -/
theorem cleanup478_denote_finish (calls : Calls) (s : State) (p : String)
    {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat) :
    denoteCode calls cleanup478Block.instrs s =
      some (((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (0 : BitVec 1))) := by
  have hk2lt : k2 < 2 ^ 64 := by
    rw [hterm]; exact nepv.isLt
  have hult : evalICmp .ult (BitVec.ofNat 64 k2) nepv = (0 : BitVec 1) := by
    have hge : ¬ ((BitVec.ofNat 64 k2).toNat < nepv.toNat) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2lt, hterm]
      omega
    have hfalse : BitVec.ult (BitVec.ofNat 64 k2) nepv = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hge ((BitVec.ult_iff_toNat_lt).1 h)
    rw [show evalICmp .ult (BitVec.ofNat 64 k2) nepv
          = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 k2) nepv) from rfl, hfalse]
    rfl
  have hsel : PhiSelects s p
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }]
      [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
       ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] :=
    PhiSelects.cons hsp hspv (PhiSelects.cons hk hkv PhiSelects.nil)
  have hspecs : cleanup478Block.instrs =
      ([{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
        { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }].map
          PhiSpec.instr) ++
        [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
          (Operand.reg "%nep")] := by
    simp [cleanup478Block, PhiSpec.instr]
  rw [hspecs, denoteCode_phiRun (specs :=
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }])
      (vs := [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
              ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))])
      (rest := [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
        (Operand.reg "%nep")]) hpre hsel (by rfl)]
  rw [show s.bindAll [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
        ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] =
      stateAt (("%k.2.i", .int 64 (BitVec.ofNat 64 k2)) ::
        ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)) :: s.env) s from rfl]
  rw [denoteCode_icmp_ult_reg (x := BitVec.ofNat 64 k2) (y := nepv)
    calls _ s "%cmp.i" "%k.2.i" "%nep"
    (by simp only [lookupName_cons_self])
    (by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hnep)
    []]
  rw [hult]
  rfl

end WalkScope

open LeanLLVM.Refinement.BlockEval

/-! ### The invariant, across a block change

`WalkInv` mentions the carry's `block` in exactly two fields — `pc_eq`, which says the
state is at it, and `blockLocal`, which is `WalkLocal` read at it.  Every other field is
about the index, the cursors, the two maps, the staging, the environment, the memory or
the geometry, and a `with` on `block` leaves all of those alone.  So a step that changes a
block and nothing else transports the invariant, with the two block-reading fields
re-supplied — which is the whole cost of a block change, and it is why a step into the
exit's blocks needs no field-by-field construction.

This belongs beside `WalkInv` in the invariant's own module; it is stated here because that
module is not this slice's to extend, and its consumers are the exit's steps, which are. -/

/-- **The invariant transports across a block change.**  `pc_eq` becomes the new state's
position and `blockLocal` the `WalkLocal` at the new block; every other field is the
invariant's own, because none of them reads `C.block`. -/
theorem WalkInv.reblock {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {b : String} (h : WalkInv G C s) (hpc : s.pc = b)
    (hloc : WalkLocal { C with block := b } s) :
    WalkInv G { C with block := b } s where
  pc_eq := hpc
  blockIndex := h.blockIndex
  k_le := h.k_le
  events_le := h.events_le
  evlen_eq := h.evlen_eq
  evBytes := h.evBytes
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
  depth_reg := h.depth_reg
  sp_le_wlen := h.sp_le_wlen
  wlen_cap := h.wlen_cap
  tyBytes := h.tyBytes
  stBytes := h.stBytes
  ptrs := h.ptrs
  regs := h.regs
  iter := h.iter
  log_hash := h.log_hash
  log_len := h.log_len
  log_cap := h.log_cap
  log_alen := h.log_alen
  log_acap := h.log_acap
  owned := h.owned
  frame := h.frame
  blockLocal := hloc

/-- **A block change is free at a non-scan block**: `WalkLocal` there is `True`, so the
transport needs only the state's position. -/
theorem WalkInv.reblock_true {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {b : String} (h : WalkInv G C s) (hpc : s.pc = b)
    (hloc : WalkLocal { C with block := b } s = True) :
    WalkInv G { C with block := b } s :=
  h.reblock hpc (by rw [hloc]; trivial)



/-- **The invariant transports across a bind whose name no field reads.**  The `WalkInv`
fields read four registers and the two carriers: `%k.0.i249` (the block index),
`%sp.i.0248` (the depth), `%7`/`%8` (the lane and the byte), the six pointer names, and
`walkStaticNames` — and `blockLocal` is `WalkLocal`, whose reads are the block's own.  A
bind at a name outside that set leaves every field alone, so the transport is the three
carrier lemmas plus a field copy — which is what `pureCore` assembles inline at each use.

`reblock`'s companion: a step that prepends cells *and* changes block uses both, bind
first and block second. -/
theorem WalkInv.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {d : String} {v : Value} (h : WalkInv G C s)
    (hst : d ∉ walkStaticNames) (hki : d ≠ "%k.0.i249") (hspp : d ≠ "%sp.i.0248")
    (h3 : d ≠ "%3") (h5 : d ≠ "%5") (hk11 : d ≠ "%k11.i") (hct : d ≠ "%ctype.i")
    (hcs : d ≠ "%cst.i") (hhash : d ≠ "%hash1.i.i") (h7 : d ≠ "%7") (h8 : d ≠ "%8")
    (hloc : WalkLocal C (s.bind d v)) :
    WalkInv G C (s.bind d v) where
  pc_eq := h.pc_eq
  blockIndex := by
    simp only [State.bind, lookupName_cons_ne _ _ hki]
    exact h.blockIndex
  k_le := h.k_le
  events_le := h.events_le
  evlen_eq := h.evlen_eq
  evBytes := h.evBytes
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
    simp only [State.bind, lookupName_cons_ne _ _ hspp]
    exact h.depth_reg
  sp_le_wlen := h.sp_le_wlen
  wlen_cap := h.wlen_cap
  tyBytes := h.tyBytes
  stBytes := h.stBytes
  ptrs := h.ptrs.bind h3 h5 hk11 hct hcs hhash
  regs := h.regs.bind hst
  iter := h.iter.bind h7 h8
  log_hash := h.log_hash
  log_len := h.log_len
  log_cap := h.log_cap
  log_alen := h.log_alen
  log_acap := h.log_acap
  owned := h.owned
  frame := h.frame
  blockLocal := hloc

/-- **The invariant transports across a cell list and a block change at once.**  The state
this produces — `cells cs`'s environment at the block `b` and the given predecessor — is the
one a `denoteCode`'s successor has, so a step is `bindAt` and nothing else.

The fused form is necessary rather than convenient: `bind` pins the *source's* `pc`, so a
chain of `bind`s cannot reach a successor whose position the term's own `br`/`condbr`
chooses.  Two facts make the fusion cheap — **no `WalkInv` field reads `pre`**, and `pc` is
read by `pc_eq` alone — so the whole content is the environment change: one field copy for
the two registers that read it (`%k.0.i249`, `%sp.i.0248`) and the three carriers, whose
side conditions are `WalkLink.refusalStore`'s list. -/
theorem WalkInv.bindAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {b : String} {cs : List (String × Value)} {pr : Option String}
    (h : WalkInv G C s)
    (hfree : ∀ n ∈ cs.map (·.1), n ∉ walkCarriedNames)
    (hki : ∀ n ∈ cs.map (·.1), n ≠ "%k.0.i249")
    (hspp : ∀ n ∈ cs.map (·.1), n ≠ "%sp.i.0248")
    (hptr : ∀ c ∈ cs, c.1 ≠ "%3" ∧ c.1 ≠ "%5" ∧ c.1 ≠ "%k11.i" ∧ c.1 ≠ "%ctype.i"
      ∧ c.1 ≠ "%cst.i" ∧ c.1 ≠ "%hash1.i.i")
    (hloc : WalkLocal { C with block := b } { s with env := cells cs s.env, pc := b, pre := pr }) :
    WalkInv G { C with block := b } { s with env := cells cs s.env, pc := b, pre := pr } where
  pc_eq := rfl
  blockIndex := by
    rw [lookupName_cells_of_notin cs "%k.0.i249" s.env
      (fun hin => hki "%k.0.i249" hin rfl)]
    exact h.blockIndex
  k_le := h.k_le
  events_le := h.events_le
  evlen_eq := h.evlen_eq
  evBytes := h.evBytes
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
  tyBytes := h.tyBytes
  stBytes := h.stBytes
  ptrs := h.ptrs.cells_of cs hptr
  regs := h.regs.cells_of cs (fun n hn => by
    have hc : n ∉ walkCarriedNames := hfree n hn
    simp only [walkCarriedNames, List.mem_cons, not_or] at hc
    exact hc.2.2)
  iter := by
    have hgo : ∀ (l : List (String × Value)),
        (∀ n ∈ l.map (·.1), n ∉ walkCarriedNames) → WalkIter G C.k (cells l s.env) := by
      intro l
      induction l with
      | nil => intro _; exact h.iter
      | cons c cs ih =>
          intro hcl
          have hc : c.1 ∉ walkCarriedNames := hcl c.1 (by simp)
          simp only [walkCarriedNames, List.mem_cons, not_or] at hc
          exact WalkIter.bind
            (ih (fun n hn => hcl n (by simp [hn]))) hc.1 hc.2.1
    exact hgo cs hfree
  log_hash := h.log_hash
  log_len := h.log_len
  log_cap := h.log_cap
  log_alen := h.log_alen
  log_acap := h.log_acap
  owned := h.owned
  frame := h.frame
  blockLocal := hloc

end LeanLLVM.Refinement


namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-- **The merge's step at the terminal index.**  The dispatch has consumed the last entry,
so `cleanup478.i`'s test is zero and the run takes the *exit* arm: one control step to
`if.then485.i`, the three cells the merge binds in the environment, and `WalkInv` at the
exit's block — which is `WalkDispatchOutcome.finish`'s `Cd`/`sd` pair.

The invariant comes from `bindAt` (cells plus block, one copy) rather than from a
field-by-field assembly: the merge binds three names no invariant field reads, so the
transport is exactly the one the transport lemmas state. -/
theorem walkFinishMerge_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {p : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat) :
    ∃ (e : State), step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "if.then485.i" } e ∧
      e = { s with
        env := (cells [("%cmp.i", .int 1 (0 : BitVec 1)),
          ("%k.2.i", .int 64 (BitVec.ofNat 64 k2)),
          ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv))] s.env)
        pc := "if.then485.i"
        pre := some "cleanup478.i" } := by
  have hpc : s.pc = "cleanup478.i" := by rw [hInv.pc_eq, hblock]
  have hden := cleanup478_denote_finish calls s p hpre hsp hspv hk hkv hnep hterm
  have hfind : stage2Body.findBlock s.pc = some cleanup478Block := by
    rw [hpc]; exact cleanup478_find
  have hterm' : cleanup478Block.term =
      Term.condbr (.reg "%cmp.i") "while.body.i" "if.then485.i" := rfl
  let cs : List (String × Value) :=
    [("%cmp.i", .int 1 (0 : BitVec 1)),
     ("%k.2.i", .int 64 (BitVec.ofNat 64 k2)),
     ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv))]
  let e : State :=
    { s with
      env := (cells cs s.env)
      pc := "if.then485.i"
      pre := some "cleanup478.i" }
  have hstep : step calls stage2Body s = .jump e := by
    simp only [LeanLLVM.step, hfind, hden, hterm']
    rw [walkExecTerm_condbr (d := "%cmp.i") (tl := "while.body.i") (fl := "if.then485.i")
      (bit := (0 : BitVec 1)) (by simp only [State.bind]; simp [lookupName])]
    dsimp only [e, cs, State.bind]
    rw [hpc]
    rfl
  refine ⟨e, hstep, ?_, rfl⟩
  refine hInv.bindAt (b := "if.then485.i") (cs := cs) (pr := some "cleanup478.i")
    ?_ ?_ ?_ (fun c hc => ?_) ?_
  · intro n hn
    simp only [cs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    rcases hn with h | h | h <;> (rw [h]; decide)
  · intro n hn
    simp only [cs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    rcases hn with h | h | h <;> (rw [h]; decide)
  · intro n hn
    simp only [cs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    rcases hn with h | h | h <;> (rw [h]; decide)
  · have hkey : c.1 ∈ ["%cmp.i", "%k.2.i", "%sp.i.1"] := by
      simpa [cs] using List.mem_map_of_mem (f := (·.1)) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkey
    rcases hkey with h | h | h <;> (rw [h]; decide)
  · simp [WalkLocal]


/-! ### The last block before the merge

`if.end473.i` is a lifetime marker and a `br cleanup478.i`: the marker writes nothing
(`walkDenoteCode_lifetimeEnd`), so the step is the state itself at the merge, and it is the
only block on the path to `cleanup478.i` that needs no contract — the four before it are the
number path's. -/

/-- `if.end473.i`: the token record's lifetime marker, then the merge. -/
def walkIf_end473_i : Block :=
  { name := "if.end473.i",
    instrs := [Instr.callVoid "llvm.lifetime.end.p0"
      [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
       (Ty.ptr, Operand.reg "%t352.i")]],
    term := Term.br "cleanup478.i" }

theorem walkIf_end473_i_find : stage2Body.findBlock "if.end473.i" = some walkIf_end473_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end473_i]

/-- **`if.end473.i`'s target, named.**  The marker leaves the state, and the `br` moves it
to the merge. -/
theorem walkIfEnd473_at {sub : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end473.i")
    {tok : Nat} (htok : lookupName s.env "%t352.i" = some (.ptr tok)) :
    ∃ (s' : State), WalkLink (stage2Calls sub) G C s { C with block := "cleanup478.i" } s' ∧
      s' = { s with pc := "cleanup478.i", pre := some s.pc } := by
  have hden : denoteCode (stage2Calls sub) walkIf_end473_i.instrs s = some s := by
    rw [show walkIf_end473_i.instrs = [Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
         (Ty.ptr, Operand.reg "%t352.i")]] from rfl, ← stateAt_self s,
      walkDenoteCode_lifetimeEnd (sub := sub) s.env s htok []]
    rfl
  have hfind : stage2Body.findBlock C.block = some walkIf_end473_i := by
    rw [hblock]; exact walkIf_end473_i_find
  obtain ⟨s', hl⟩ := WalkLink.pureJumpCore (calls := stage2Calls sub) G C s hInv hfind hden
    (by unfold walkCarried; decide) rfl rfl (t := "cleanup478.i") rfl (by simp [WalkLocal])
  refine ⟨s', hl, ?_⟩
  have hstep : step (stage2Calls sub) stage2Body s =
      Ctrl.jump { s with pc := "cleanup478.i", pre := some s.pc } := by
    simp only [LeanLLVM.step, hInv.pc_eq, hfind, hden]
    dsimp only [walkIf_end473_i, execTerm]
    rw [← hInv.pc_eq]
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkFinishMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfEnd473_at

end WalkScope
end LeanLLVM.Refinement

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkIfElse387_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen403_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen403_seg
#print axioms LeanLLVM.Refinement.WalkScope.cleanup478_denote_finish
#print axioms LeanLLVM.Refinement.WalkInv.reblock
#print axioms LeanLLVM.Refinement.WalkInv.reblock_true
#print axioms LeanLLVM.Refinement.WalkInv.bind
#print axioms LeanLLVM.Refinement.WalkInv.bindAt
