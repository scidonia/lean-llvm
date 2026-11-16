/-
The container openers' dispatch arm: `[` and `{` at the loop head.

## The route

Both bytes enter `if.then.i` — the open bracket through
`NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock7`, the open brace through
`NodeBlock21 → NodeBlock19 → NodeBlock17 → LeafBlock13` — and from there the two share one
tail:

| block | class | what the link is |
|---|---|---|
| `if.then.i` | F | calls `@s2_value_pos`; the answer `1` selects `if.end.i` |
| `if.end.i` | A | `%sp.i.0248 > 519` is false, so the run enters the push |
| `if.end24.i` | — | the push: `wlen`, `tyMap` and `stMap` advance at `C.sp` |
| `if.end.i.i` | G | the event reserve's guard is clear (`walkEventReserve_clear`) |
| `out_reserve.exit.i.i` | D | the tag byte and the length word; the merge follows |

Nine links in all (four head, five tail), and the merge's index is `%inc.i = C.k + 1`
while its depth is `%inc33.i = C.sp + 1`: an opener consumes an entry and pushes a
container.

## The intermediate states

Every link's target is a state the *next* link reads a cell from, so each is a
module-level definition before it can be a segment's index — the reason this module
exists rather than a chain of `WalkLink` existentials.  The tail's states are
`openS₅`…`openS₉`; the head's are `openBrS₁`…`openBrS₄` and `openBcS₁`…`openBcS₄`.

Three links' target states are *inside* their proofs — `if_then_i` and `if_end_i_i`
through `WalkLink.pureCore`'s `s₁`, `out_reserve.exit_i_i` through
`outReserveStore`'s `out`/`m'` — so this module states each block's named `step`
(`openIfThenI_term`, `openIfEndIITerm`, `openOutReserveTerm`), and the state equation
is `Ctrl.jump.inj` of the two `step` equations, exactly as `refuseStep₁` names its
target.  The four head links and `if.end.i` and `if.end24.i` already have a named
form (`_at`, `ifEnd24_term`), so no step lemma sits beside them.

## What the arm owes

The composition's premises are the block's own: the byte's class, the depth's
`519`-guard, the root slot's zero word (what makes the answer `1` at depth zero), the
callee's staging and answer, and the event cursor's gep bound.  Everything else — the
two stacks' bytes, the log's words, `%nep`, `%z` and the trace's tight count — is a
clause of `WalkInv` at the state the previous link's `inv'` names, which is why the
tail is stated at an arbitrary `if.then.i` state and not at the head.

## The depth-one state, and why it is a product

`cleanup478.i`'s depth `phi` is `%inc33.i` on this route, so the merge's successor is a
head state at `C.sp + 1`: the opener is where the walk's depth becomes positive, and
`containerOpen_depth_one` states that state's `WalkInv` as a *produced* fact
(`walkBack_step_at` and `WalkLink.whileBody`, both at the merge's own phi cells).  The
depth-positive arms — a closing delimiter with a container open, a comma or a colon
above depth zero — read their source from this, and nothing else in the layer produces
a `WalkInv` at a positive depth.

## Where the arm lands

`containerOpenMerge_at` is the producer behind `LastEntryArm.containerOpen` and
`HcontArm.containerOpen` (`JsonStage2WalkDispatchArms`,
`JsonStage2WalkDispatchHcontArms`), so both dispatch levels run these nine links; the
documents `[0]`, `{"a":1}` and `[` inhabit the two arms
(`JsonStage2WalkDispatchOpenersDomain`).
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkStore

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The zero word and the `519` guard

Two arithmetic facts the route reads: the loaded depth's zero is the empty word, and
the push's own guard (`%sp.i.0248 > 519` clear) is the depth bound `NestGuard` states. -/

/-- The depth cell's zero word is zero. -/
theorem openDepthZero_toNat : (BitVec.ofNat 32 0).toNat = 0 := by decide

/-- **`if.end.i`'s guard is clear below `520`.**  `%cmp19.i` is
`ugt %sp.i.0248, 519`; at a depth `NestGuard` admits it is `0`, so the run enters
`if.end24.i` rather than the refusal store. -/
theorem openUgt519_zero {sp : Nat} (h : sp ≤ 519) :
    evalICmp .ugt (BitVec.ofNat 32 sp) (BitVec.ofNat 32 519) = 0 := by
  rcases walkBitVec1_zero_or_one
    (evalICmp .ugt (BitVec.ofNat 32 sp) (BitVec.ofNat 32 519)) with h0 | h1
  · exact h0
  · exfalso
    have hlt := (walkEvalICmp_ugt_one_iff _ _).1 h1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : sp < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 519 < 2 ^ 32)] at hlt
    omega

/-- The entry count is a word. -/
theorem openNep_lt {m0 : Mem} (G : WalkGeom m0) : G.nep < 2 ^ 64 := by
  have h1 := G.nep_le
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  omega

/-! ### The carries

The head's carries differ only in their block; the tail's carry the push.  Both are
`abbrev`s so the target carry a link's conclusion names is the same term. -/

/-- `NodeBlock19`'s carry: `%8 < 91` is false at both openers. -/
abbrev openHeadC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock19" }

/-- The `if.then.i` carry: both opener routes end here. -/
abbrev openHeadC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.then.i" }

/-- `if.end.i`'s carry: the push's predecessor. -/
abbrev openC₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.end.i" }

/-- `if.end24.i`'s carry. -/
abbrev openC₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.end24.i" }

/-- **The push's carry**: `if.end24.i` writes the type stack's byte at `C.sp` and the
state stack's zero, and the written mark rises to `max C.wlen (C.sp + 1)`. -/
abbrev openC₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) : WalkCarry G :=
  { C with
    block := "if.end.i.i", wlen := max C.wlen (C.sp + 1),
    tyMap := fun i => if i = C.sp then ifEnd24TyByte b else C.tyMap i,
    stMap := fun i => if i = C.sp then ifEnd24StByte else C.stMap i }

/-- `if.end.i.i`'s carry: the reserve's guard is clear. -/
abbrev openC₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) : WalkCarry G :=
  { openC₇ C b with block := "out_reserve.exit.i.i" }

/-- **The merge's carry**: the tag byte advances the event cursor by one and appends the
record the opener's byte selects (`1` for `{`, `3` for `[`). -/
abbrev openC₉ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) : WalkCarry G :=
  { C with
    block := "cleanup478.i", wlen := max C.wlen (C.sp + 1),
    tyMap := fun i => if i = C.sp then ifEnd24TyByte b else C.tyMap i,
    stMap := fun i => if i = C.sp then ifEnd24StByte else C.stMap i,
    evlen := C.evlen + 1,
    events := C.events ++ [EventRecord.tag (ifEnd24St b).toNat] }

/-! ### The head's states

Four per byte, each the successor a `_at` lemma names: the pivot's bite and the edge's
`pc`/`pre`.  The byte is the operand's literal, so the state is a term of `s` alone. -/

/-- `NodeBlock21`'s target at the open bracket: `91 < 91` is false. -/
def openBrS₁ (s : State) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- `NodeBlock19`'s target at the open bracket: `91 < 123` is true. -/
def openBrS₂ (s : State) : State :=
  { (openBrS₁ s).bind "%Pivot20"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 123))) with
    pc := "NodeBlock11", pre := some (openBrS₁ s).pc }

/-- `NodeBlock11`'s target at the open bracket: `91 < 93` is true. -/
def openBrS₃ (s : State) : State :=
  { (openBrS₂ s).bind "%Pivot12"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 93))) with
    pc := "LeafBlock7", pre := some (openBrS₂ s).pc }

/-- `LeafBlock7`'s target: `91 = 91` is true, so the switch's arm is `if.then.i`. -/
def openBrS₄ (s : State) : State :=
  { (openBrS₃ s).bind "%SwitchLeaf8"
      (.int 1 (evalICmp .eq (BitVec.ofNat 8 91) (BitVec.ofNat 8 91))) with
    pc := "if.then.i", pre := some (openBrS₃ s).pc }

/-- `NodeBlock21`'s target at the open brace: `123 < 91` is false. -/
def openBcS₁ (s : State) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- `NodeBlock19`'s target at the open brace: `123 < 123` is false. -/
def openBcS₂ (s : State) : State :=
  { (openBcS₁ s).bind "%Pivot20"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 123))) with
    pc := "NodeBlock17", pre := some (openBcS₁ s).pc }

/-- `NodeBlock17`'s target at the open brace: `123 < 125` is true. -/
def openBcS₃ (s : State) : State :=
  { (openBcS₂ s).bind "%Pivot18"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 125))) with
    pc := "LeafBlock13", pre := some (openBcS₂ s).pc }

/-- `LeafBlock13`'s target: `123 = 123` is true, so the switch's arm is `if.then.i`. -/
def openBcS₄ (s : State) : State :=
  { (openBcS₃ s).bind "%SwitchLeaf14"
      (.int 1 (evalICmp .eq (BitVec.ofNat 8 123) (BitVec.ofNat 8 123))) with
    pc := "if.then.i", pre := some (openBcS₃ s).pc }

/-- The open bracket's fourth head state has the head's memory. -/
theorem openBrS₄_mem (s : State) : (openBrS₄ s).mem = s.mem := rfl

/-- The open bracket's fourth head state has the head's cursor. -/
theorem openBrS₄_next (s : State) : (openBrS₄ s).next = s.next := rfl

/-- The open brace's fourth head state has the head's memory. -/
theorem openBcS₄_mem (s : State) : (openBcS₄ s).mem = s.mem := rfl

/-- The open brace's fourth head state has the head's cursor. -/
theorem openBcS₄_next (s : State) : (openBcS₄ s).next = s.next := rfl

/-! ### The tail's states

Five, each the successor of one block: the value-position call's cells, the depth
guard's bite, the push's writes, the reserve's four cells, and the tag's two. -/

/-- **`if.then.i`'s target at the answer `1`**: the call's three cells, the branch to
`if.end.i`, and the callee's memory and cursor (it writes nothing). -/
def openS₅ (s : State) (r : CallOutcome) : State :=
  { stateAt (cells
      [("%tobool15.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0))),
       ("%call14.i", .int 32 (BitVec.ofNat 32 1)),
       ("%9", .int 32 (BitVec.ofNat 32 0))] s.env)
      { s with mem := r.mem, next := r.next } with
    pc := "if.end.i", pre := some s.pc }

/-- **`if.end.i`'s target from its own source**: the depth guard's bite, on the arm to
the push. -/
abbrev openS₆From {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₅ : State) : State :=
  { s₅.bind "%cmp19.i"
      (.int 1 (evalICmp .ugt (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 519))) with
    pc := "if.end24.i", pre := some s₅.pc }

/-- **`if.end.i`'s target, at the tail's own state.** -/
abbrev openS₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) : State :=
  openS₆From C (openS₅ s r)

/-- **`if.end24.i`'s target from its own source**: the two stacks written at the carried
depth and the push's own cells, with the log's zeroed hash word fixing the branch to the
reserve. -/
abbrev openS₇From {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₆ : State)
    (b : BitVec 8) : State :=
  { stateAt (ifEnd24Out s₆.env C.sp C.stage.ctype C.stage.cst b)
      { s₆ with
        mem := writeBytes (writeBytes s₆.mem (C.stage.ctype + C.sp)
          (natToBytes (ifEnd24Ty b).toNat 1)) (C.stage.cst + C.sp) (natToBytes 0 1) } with
    pc := "if.end.i.i", pre := some "if.end24.i" }

/-- **`if.end24.i`'s target, at the tail's own state.** -/
abbrev openS₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) : State :=
  openS₇From C (openS₆ C s r) b

/-- `if.end.i.i`'s target from its own source: the two log words' loads, the increment's
sum and the reserve guard's bite, on the arm to the tag's store. -/
abbrev openS₈From {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₇ : State) :
    State :=
  { stateAt (cells
      [("%cmp.not.i.i.i", .int 1 (evalICmp .ugt
          (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1) (BitVec.ofNat 64 G.evcap))),
       ("%add.i.i.i", .int 64 (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)),
       ("%o.val11.i.i", .int 64 (BitVec.ofNat 64 G.evcap)),
       ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen))] s₇.env)
      s₇ with
    pc := "out_reserve.exit.i.i", pre := some s₇.pc }

/-- **`if.end.i.i`'s target, at the tail's own state.** -/
abbrev openS₈ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) : State :=
  openS₈From C (openS₇ C s r b)

/-- **`out_reserve.exit.i.i`'s target from its own source, the merge's own state**: the
tag byte written at the event cursor, the length word advanced by one. -/
abbrev openS₉From {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₈ : State)
    (b : BitVec 8) : State :=
  { stateAt (cells
      [("%add.ptr.i.i", .ptr (G.ev + C.evlen)), ("%13", .ptr G.ev)] s₈.env)
      { s₈ with
        mem := writeBytes (writeBytes s₈.mem (G.ev + C.evlen)
          (natToBytes (ifEnd24St b).toNat 1)) (C.stage.z + 8) (wordBytes 8 (C.evlen + 1)) } with
    pc := "cleanup478.i", pre := some s₈.pc }

/-- **`out_reserve.exit.i.i`'s target, at the tail's own state**: the merge's own state. -/
abbrev openS₉ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) : State :=
  openS₉From C (openS₈ C s r b) b

/-! ### The cells the merge and the tag's store read

The push's cells (`%conv42.i`, `%inc33.i`) and the reserve's two words are the only
carried values the tail's later blocks read; everything else is a clause of `WalkInv`
at the previous link's target. -/

/-- `%conv42.i` at the reserve: the state stack's byte the opener's own byte selects. -/
theorem openS₈_conv42 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₈ C s r b).env "%conv42.i" = some (.int 8 (ifEnd24St b)) := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The reserve's increment cell is `%o.val.i.i + 1`, at the word the tag's store
reads. -/
theorem openS₈_addiii {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₈ C s r b).env "%add.i.i.i" =
      some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))) := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [BitVec.ofNat_add_ofNat]
  exact lookupName_cons_self _ _ _

/-- The reserve's loaded length is the carried event cursor. -/
theorem openS₈_oval {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₈ C s r b).env "%o.val.i.i" = some (.int 64 (BitVec.ofNat 64 C.evlen)) := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The merge's depth operand**: `%inc33.i` is the push's own `C.sp + 1`. -/
theorem openS₉_inc33 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₉ C s r b).env "%inc33.i" =
      some (.int 32 (BitVec.ofNat 32 (C.sp + 1))) := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The merge's index operand**: `%inc.i` is the header's cell, reached through the
whole tail. -/
theorem openS₉_inc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₉ C s r b).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the merge is the static carrier's. -/
theorem openS₉_nep {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (b : BitVec 8) :
    lookupName (openS₉ C s r b).env "%nep" = lookupName s.env "%nep" := by
  simp only [ifEnd24Out, ifEnd24TailCells, ifEnd24Mid, ifEnd24HeadCells, openS₅, stateAt,
    cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The three blocks whose target state is inside their proofs

`if_then_i`, `if.end.i.i` and `out_reserve.exit.i.i` each conclude `∃ s'`, so the state
the next link reads is not a term.  Each block's named `step` is here; the link's own
`step` and this one are two readings of one function, so the state equation is
`Ctrl.jump.inj`. -/

/-- **`if.then.i`'s step, at the state `openS₅`.**  The value-position call's answer is
`1`, so the branch's bit is zero and the edge is `if.end.i`. -/
theorem openIfThenI_term {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hpc : s.pc = "if.then.i")
    {root : Nat} {r : CallOutcome}
    (hroot : lookupName s.env "%root_done.i" = some (.ptr root))
    (hread : readBytes s.mem root 4 = some (natToBytes (BitVec.ofNat 32 0).toNat 4))
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 C.sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr C.stage.ctype))
    (hcs : lookupName s.env "%cst.i" = some (.ptr C.stage.cst))
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (openS₅ s r) := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenI.instrs s =
      some (stateAt (cells
        [("%tobool15.not.i",
            .int 1 (evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0))),
         ("%call14.i", .int 32 (BitVec.ofNat 32 1)),
         ("%9", .int 32 (BitVec.ofNat 32 0))] s.env)
        { s with mem := r.mem, next := r.next }) := by
    rw [← stateAt_self s]
    exact walkIfThenI_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (root := root) (rd := (BitVec.ofNat 32 0)) (sp := BitVec.ofNat 32 C.sp)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r) (x := BitVec.ofNat 32 1)
      hroot hread hsp hct hcs hcall hret
  have hbit : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = (0 : BitVec 1) := by
    decide
  have hd : lookupName
      (stateAt (cells
        [("%tobool15.not.i",
            .int 1 (evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0))),
         ("%call14.i", .int 32 (BitVec.ofNat 32 1)),
         ("%9", .int 32 (BitVec.ofNat 32 0))] s.env) { s with mem := r.mem, next := r.next }).env
      "%tobool15.not.i" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0))) := by
    dsimp only [stateAt, cells]
    exact lookupName_cons_self _ _ _
  have hfind : stage2Body.findBlock s.pc = some walkIfThenI := by
    rw [hpc]; exact walkIfThenI_find
  have hterm : walkIfThenI.term =
      Term.condbr (Operand.reg "%tobool15.not.i") "if.then16.i" "if.end.i" := rfl
  simp only [step, hfind, hden, hterm]
  rw [walkExecTerm_condbr hd]
  simp only [openS₅]
  rw [hbit, ite_eq_right (by decide)]
  rfl

/-- **`if.end.i.i`'s step, at the state `openS₈`.**  The reserve's guard is clear, so
the branch's bit is zero and the edge is `out_reserve.exit.i.i`. -/
theorem openIfEndIITerm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hpc : s.pc = "if.end.i.i")
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hcap : lookupName s.env "%cap" = some (.ptr (C.stage.z + 16)))
    (hreadL : readBytes s.mem (C.stage.z + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8))
    (hreadC : readBytes s.mem (C.stage.z + 16) 8 =
      some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8))
    (hguard : evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 0) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (openS₈From C s) := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIf_end_i_i.instrs s =
      some (stateAt (cells
        [("%cmp.not.i.i.i", .int 1 (evalICmp .ugt
            (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1) (BitVec.ofNat 64 G.evcap))),
         ("%add.i.i.i", .int 64 (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)),
         ("%o.val11.i.i", .int 64 (BitVec.ofNat 64 G.evcap)),
         ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen))] s.env) s) := by
    simp only [walkIf_end_i_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load64 (calls := stage2Calls stage2SubCalls) (env := s.env) (s := s)
      (d := "%o.val.i.i") (p := "%len") (a := C.stage.z + 8)
      (v := BitVec.ofNat 64 C.evlen) hlen hreadL]
    rw [denoteCode_load64 (calls := stage2Calls stage2SubCalls)
      (env := ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen)) :: s.env) (s := s)
      (d := "%o.val11.i.i") (p := "%cap") (a := C.stage.z + 16)
      (v := BitVec.ofNat 64 G.evcap) hcap hreadC]
    rw [walkDenoteCode_add_imm_w (calls := stage2Calls stage2SubCalls)
      (env := ("%o.val11.i.i", .int 64 (BitVec.ofNat 64 G.evcap)) ::
        ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen)) :: s.env) (s := s)
      (d := "%add.i.i.i") (a := "%o.val.i.i") (w := 64) (x := BitVec.ofNat 64 C.evlen)
      (c := BitVec.ofNat 64 1) (by simp [lookupName])]
    rw [denoteCode_icmp_reg_w (calls := stage2Calls stage2SubCalls)
      (env := ("%add.i.i.i", .int 64 (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)) ::
        ("%o.val11.i.i", .int 64 (BitVec.ofNat 64 G.evcap)) ::
        ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen)) :: s.env) (s := s)
      (d := "%cmp.not.i.i.i") (a := "%add.i.i.i") (b := "%o.val11.i.i") IPred.ugt 64
      (x := BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 G.evcap)
      (by simp [lookupName]) (by simp [lookupName])]
    rfl
  have hd : lookupName
      (stateAt (cells
        [("%cmp.not.i.i.i", .int 1 (evalICmp .ugt
            (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1) (BitVec.ofNat 64 G.evcap))),
         ("%add.i.i.i", .int 64 (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)),
         ("%o.val11.i.i", .int 64 (BitVec.ofNat 64 G.evcap)),
         ("%o.val.i.i", .int 64 (BitVec.ofNat 64 C.evlen))] s.env) s).env "%cmp.not.i.i.i" =
      some (.int 1 (evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 G.evcap))) := by
    dsimp only [stateAt, cells]
    exact lookupName_cons_self _ _ _
  have hfind : stage2Body.findBlock s.pc = some walkIf_end_i_i := by
    rw [hpc]; exact walkIf_end_i_i_find
  have hterm : walkIf_end_i_i.term =
      Term.condbr (Operand.reg "%cmp.not.i.i.i") "if.end.i.i.i" "out_reserve.exit.i.i" := rfl
  simp only [step, hfind, hden, hterm]
  rw [walkExecTerm_condbr hd]
  simp only [openS₈From]
  rw [hguard, ite_eq_right (by decide)]
  rfl

/-- **`out_reserve.exit.i.i`'s step, at the state `openS₉`.**  The tag byte and the
length word, and the branch to the merge. -/
theorem openOutReserveTerm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b : BitVec 8) (hpc : s.pc = "out_reserve.exit.i.i")
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hload : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hev64 : G.ev < 2 ^ 64)
    (hs : lookupName s.env "%conv42.i" = some (.int 8 (ifEnd24St b)))
    (ho : lookupName s.env "%o.val.i.i" = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hst : lookupName s.env "%add.i.i.i" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hev63 : C.evlen < 2 ^ 63) (hev64len : C.evlen + 1 < 2 ^ 64) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (openS₉From C s b) := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkOut_reserve_exit_i_i.instrs s =
      some (stateAt (cells
        [("%add.ptr.i.i", .ptr (G.ev + C.evlen)), ("%13", .ptr G.ev)] s.env)
        { s with
          mem := writeBytes (writeBytes s.mem (G.ev + C.evlen)
            (natToBytes (ifEnd24St b).toNat 1)) (C.stage.z + 8)
            (wordBytes 8 (C.evlen + 1)) }) := by
    simp only [walkOut_reserve_exit_i_i]
    conv_lhs => rw [← stateAt_self s]
    rw [walkDenoteCode_loadPtr (stage2Calls stage2SubCalls) s.env s "%13" "%z"
      (q := G.ev) hz hload hev64
      [Instr.gep "%add.ptr.i.i" (.int 8) (.reg "%13") (.reg "%o.val.i.i"),
       Instr.store (.int 8) (.reg "%conv42.i") (.reg "%add.ptr.i.i"),
       Instr.store (.int 64) (.reg "%add.i.i.i") (.reg "%len")]]
    rw [denoteCode_gep8_ofNat (stage2Calls stage2SubCalls) _ s "%add.ptr.i.i" "%13"
      "%o.val.i.i" (by rw [lookupName_cons_self])
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact ho) hev63
      [Instr.store (.int 8) (.reg "%conv42.i") (.reg "%add.ptr.i.i"),
       Instr.store (.int 64) (.reg "%add.i.i.i") (.reg "%len")]]
    rw [denoteCode_store8 (stage2Calls stage2SubCalls) _ s "%conv42.i" "%add.ptr.i.i"
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hs)
      (by rw [lookupName_cons_self])
      [Instr.store (.int 64) (.reg "%add.i.i.i") (.reg "%len")]]
    rw [denoteCode_store64_ofNat (stage2Calls stage2SubCalls) _
      { s with mem := writeBytes s.mem (G.ev + C.evlen) (natToBytes (ifEnd24St b).toNat 1) }
      "%add.i.i.i" "%len"
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hst)
      hev64len
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hlen) []]
    rfl
  have hfind : stage2Body.findBlock s.pc = some walkOut_reserve_exit_i_i := by
    rw [hpc]; exact walkOut_reserve_exit_i_i_find
  have hterm : walkOut_reserve_exit_i_i.term = Term.br "cleanup478.i" := rfl
  simp only [step, hfind, hden, hterm]
  simp only [execTerm]
  simp only [openS₉From]
  rfl

/-! ### The head's four links, per byte

Each is the `_at` instance at its pivot's bit; the state equation is the instance's
own, with the arm's `pc` rewritten in. -/

/-- **The open bracket's route to `if.then.i`.**  Four links: the four pivots' bites. -/
theorem openBracketHead {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (openHeadC C) (openBrS₄ s) 4 := by
  -- 1. the head's first pivot: `91 < 91` is false
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at G C s hInv hblock h8
  have hbit₁ : evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 91) = 0 := by decide
  have harm₁ : (if evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [hbit₁]; rfl
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (openHeadC₁ C) (openBrS₁ s) := by
    have hst₁ : s₁ = openBrS₁ s := by rw [hs₁, harm₁]; rfl
    rw [hst₁, harm₁] at hl₁
    exact hl₁
  -- 2. `91 < 123` is true
  have h8₁ : evalOperand (openBrS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) := by
    simp only [evalOperand]; rw [hl₁'.inv'.iter.reg8, hbe]
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock19_at G (openHeadC₁ C) (openBrS₁ s)
    hl₁'.inv' rfl h8₁
  have hbit₂ : evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 123) = 1 := by decide
  have harm₂ : (if evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock11" := by rw [hbit₂]; rfl
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (openHeadC₁ C) (openBrS₁ s)
      { C with block := "NodeBlock11" } (openBrS₂ s) := by
    have hst₂ : s₂ = openBrS₂ s := by rw [hs₂, harm₂]; rfl
    rw [hst₂, harm₂] at hl₂
    exact hl₂
  -- 3. `91 < 93` is true
  have h8₂ : evalOperand (openBrS₂ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) := by
    simp only [evalOperand]; rw [hl₂'.inv'.iter.reg8, hbe]
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock11_at G { C with block := "NodeBlock11" }
    (openBrS₂ s) hl₂'.inv' rfl h8₂
  have hbit₃ : evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 93) = 1 := by decide
  have harm₃ : (if evalICmp .slt (BitVec.ofNat 8 91) (BitVec.ofNat 8 93) = 1 then
      "LeafBlock7" else "LeafBlock9") = "LeafBlock7" := by rw [hbit₃]; rfl
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G { C with block := "NodeBlock11" }
      (openBrS₂ s) { C with block := "LeafBlock7" } (openBrS₃ s) := by
    have hst₃ : s₃ = openBrS₃ s := by rw [hs₃, harm₃]; rfl
    rw [hst₃, harm₃] at hl₃
    exact hl₃
  -- 4. `91 = 91` is true
  have h8₃ : evalOperand (openBrS₃ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) := by
    simp only [evalOperand]; rw [hl₃'.inv'.iter.reg8, hbe]
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock7_at G { C with block := "LeafBlock7" }
    (openBrS₃ s) hl₃'.inv' rfl h8₃
  have hbit₄ : evalICmp .eq (BitVec.ofNat 8 91) (BitVec.ofNat 8 91) = 1 := by decide
  have harm₄ : (if evalICmp .eq (BitVec.ofNat 8 91) (BitVec.ofNat 8 91) = 1 then
      "if.then.i" else "sw.default.i") = "if.then.i" := by rw [hbit₄]; rfl
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G { C with block := "LeafBlock7" }
      (openBrS₃ s) (openHeadC C) (openBrS₄ s) := by
    have hst₄ : s₄ = openBrS₄ s := by rw [hs₄, harm₄]; rfl
    rw [hst₄, harm₄] at hl₄
    exact hl₄
  exact Seg.measure (Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃'
    (Seg.tail hl₄' (Seg.nil hl₄'.inv')))))

/-- **The open brace's route to `if.then.i`.**  Four links through `NodeBlock17` and
`LeafBlock13`. -/
theorem openBraceHead {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (openHeadC C) (openBcS₄ s) 4 := by
  -- 1. the head's first pivot: `123 < 91` is false
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at G C s hInv hblock h8
  have hbit₁ : evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 91) = 0 := by decide
  have harm₁ : (if evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by rw [hbit₁]; rfl
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (openHeadC₁ C) (openBcS₁ s) := by
    have hst₁ : s₁ = openBcS₁ s := by rw [hs₁, harm₁]; rfl
    rw [hst₁, harm₁] at hl₁
    exact hl₁
  -- 2. `123 < 123` is false
  have h8₁ : evalOperand (openBcS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
    simp only [evalOperand]; rw [hl₁'.inv'.iter.reg8, hbe]
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock19_at G (openHeadC₁ C) (openBcS₁ s)
    hl₁'.inv' rfl h8₁
  have hbit₂ : evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 123) = 0 := by decide
  have harm₂ : (if evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by rw [hbit₂]; rfl
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (openHeadC₁ C) (openBcS₁ s)
      { C with block := "NodeBlock17" } (openBcS₂ s) := by
    have hst₂ : s₂ = openBcS₂ s := by rw [hs₂, harm₂]; rfl
    rw [hst₂, harm₂] at hl₂
    exact hl₂
  -- 3. `123 < 125` is true
  have h8₂ : evalOperand (openBcS₂ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
    simp only [evalOperand]; rw [hl₂'.inv'.iter.reg8, hbe]
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock17_at G { C with block := "NodeBlock17" }
    (openBcS₂ s) hl₂'.inv' rfl h8₂
  have hbit₃ : evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 125) = 1 := by decide
  have harm₃ : (if evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock13" := by rw [hbit₃]; rfl
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G { C with block := "NodeBlock17" }
      (openBcS₂ s) { C with block := "LeafBlock13" } (openBcS₃ s) := by
    have hst₃ : s₃ = openBcS₃ s := by rw [hs₃, harm₃]; rfl
    rw [hst₃, harm₃] at hl₃
    exact hl₃
  -- 4. `123 = 123` is true
  have h8₃ : evalOperand (openBcS₃ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
    simp only [evalOperand]; rw [hl₃'.inv'.iter.reg8, hbe]
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock13_at G { C with block := "LeafBlock13" }
    (openBcS₃ s) hl₃'.inv' rfl h8₃
  have hbit₄ : evalICmp .eq (BitVec.ofNat 8 123) (BitVec.ofNat 8 123) = 1 := by decide
  have harm₄ : (if evalICmp .eq (BitVec.ofNat 8 123) (BitVec.ofNat 8 123) = 1 then
      "if.then.i" else "sw.default.i") = "if.then.i" := by rw [hbit₄]; rfl
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G { C with block := "LeafBlock13" }
      (openBcS₃ s) (openHeadC C) (openBcS₄ s) := by
    have hst₄ : s₄ = openBcS₄ s := by rw [hs₄, harm₄]; rfl
    rw [hst₄, harm₄] at hl₄
    exact hl₄
  exact Seg.measure (Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃'
    (Seg.tail hl₄' (Seg.nil hl₄'.inv')))))

/-! ### The tail's five links

Stated at an arbitrary `if.then.i` state, because every premise but the callee's is a
clause of that state's invariant. -/

/-- **The opener's tail**: the value-position call, the depth guard, the push, the
event reserve and the tag — five links from `if.then.i` to `cleanup478.i`. -/
theorem openTailSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then.i")
    {b : BitVec 8}
    (hbe : b = BitVec.ofNat 8 (entryByte G C.k).toNat)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 =
      some (natToBytes (BitVec.ofNat 32 0).toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hklt : C.k < G.nep) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (openC₉ C b) (openS₉ C s r b) 5 := by
  have hnep64 : G.nep < 2 ^ 64 := openNep_lt G
  -- 5. `if.then.i`: the callee's answer `1` selects `if.end.i`
  have hroot : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have hpc₅ : s.pc = "if.then.i" := by rw [hInv.pc_eq, hblock]
  have hstep₅ : step (stage2Calls stage2SubCalls) stage2Body s = .jump (openS₅ s r) :=
    openIfThenI_term C s hpc₅ hroot hrd hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hret
  have hx : ∀ r', stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r' →
      r'.ret = .int 32 (BitVec.ofNat 32 1) := by
    intro r' h'
    rw [Option.some.inj (h'.symm.trans hcall)]
    exact hret
  obtain ⟨s₅, hl₅⟩ :=
    WalkLink.if_then_i G C s hInv hblock hroot
      (by rw [openDepthZero_toNat]; exact hrd) hpreV hx
  have hbit₅ : (if evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = 1 then
      "if.then16.i" else "if.end.i") = "if.end.i" := by
    rw [show evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = (0 : BitVec 1) from
      by decide]
    rfl
  rw [hbit₅] at hl₅
  have hs₅ : s₅ = openS₅ s r := Ctrl.jump.inj (hl₅.step.symm.trans hstep₅)
  rw [hs₅] at hl₅
  -- 6. `if.end.i`: the depth guard is clear below `520`
  have hstep₆ : evalOperand (openS₅ s r) (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    simp only [evalOperand]
    exact hl₅.inv'.depth_reg
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.if_end_i_at G (openC₅ C) (openS₅ s r) hl₅.inv' rfl hstep₆
  have hbit₆ : (if evalICmp .ugt (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 519) = 1 then
      "if.then21.i" else "if.end24.i") = "if.end24.i" := by
    rw [openUgt519_zero hsp519]; rfl
  have hc₆ : { openC₅ C with block := (if evalICmp .ugt (BitVec.ofNat 32 C.sp)
      (BitVec.ofNat 32 519) = 1 then "if.then21.i" else "if.end24.i") } = openC₆ C := by
    rw [hbit₆]
  rw [hc₆] at hl₆
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (openC₅ C) (openS₅ s r)
      (openC₆ C) (openS₆ C s r) := by
    have hst₆ : s₆ = openS₆ C s r := by rw [hs₆, hbit₆]
    rw [hst₆] at hl₆
    exact hl₆
  -- 7. `if.end24.i`: the push, at the log's zeroed hash word
  have h8₆ : lookupName (openS₆ C s r).env "%8" = some (.int 8 b) := by
    rw [hl₆'.inv'.iter.reg8, ← hbe]
  have hsp32 : C.sp < stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    omega
  obtain ⟨s₇, hl₇⟩ :=
    WalkLink.ifEnd24 G (openC₆ C) (openS₆ C s r) hl₆'.inv' rfl h8₆ hsp519
  have hpc₇ : (openS₆ C s r).pc = "if.end24.i" := hl₆'.inv'.pc_eq
  have hstep₇ : step (stage2Calls stage2SubCalls) stage2Body (openS₆ C s r) =
      .jump (openS₇ C s r b) :=
    ifEnd24_term (calls := stage2Calls stage2SubCalls) (s := openS₆ C s r)
      (sp := C.sp) (ctype := C.stage.ctype) (cst := C.stage.cst) (z := C.stage.z) (b := b)
      hpc₇ h8₆ hl₆'.inv'.depth_reg
      (hl₆'.inv'.ptrs.2.2.2.1) (hl₆'.inv'.ptrs.2.2.2.2.1) (hl₆'.inv'.ptrs.2.2.2.2.2)
      hsp32 (ctype_log_sep (C := openC₆ C) hl₆'.inv')
      (cst_log_sep (C := openC₆ C) hl₆'.inv') hl₆'.inv'.log_hash
  have hs₇ : s₇ = openS₇ C s r b := Ctrl.jump.inj (hl₇.step.symm.trans hstep₇)
  rw [hs₇] at hl₇
  -- 8. `if.end.i.i`: the reserve's guard is clear
  have hevclear : C.evlen + 1 ≤ G.evcap :=
    (walkEventReserve_clear hl₇.inv'
      (walkEmitC_of_not_contains (b := "if.end.i.i") (by decide)) hklt).1
  have hev63 : C.evlen < 2 ^ 63 := by
    have h1 : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := hl₇.inv'.evlen_le
    have h2 := G.ev63
    omega
  have hev64len : C.evlen + 1 < 2 ^ 64 := by
    have h1 := G.evcapLt
    omega
  have hreadL : readBytes (openS₇ C s r b).mem (C.stage.z + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
    have h := hl₇.inv'.log_len
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : C.evlen < 2 ^ 64)]
    simpa only [wordBytes] using h
  have hreadC : readBytes (openS₇ C s r b).mem (C.stage.z + 16) 8 =
      some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
    have h := hl₇.inv'.log_cap
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
    simpa only [wordBytes] using h
  have hguard₈ : evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 0 := by
    have hsum : BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (C.evlen + 1) := BitVec.ofNat_add_ofNat _ _
    rw [hsum]
    exact walkEvalICmp_ugt_ofNat_zero hev64len G.evcapLt (by omega)
  obtain ⟨s₈, hl₈⟩ :=
    WalkLink.if_end_i_i G (openC₇ C b) (openS₇ C s r b) hl₇.inv' rfl
      (hl₇.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
      (hl₇.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
      hreadL hreadC
  have hbit₈ : (if evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i.i.i" else "out_reserve.exit.i.i") =
      "out_reserve.exit.i.i" := by
    rw [hguard₈]; rfl
  have hc₈ : { openC₇ C b with block := (if evalICmp .ugt
      (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i.i.i" else "out_reserve.exit.i.i") } =
      openC₈ C b := by
    rw [hbit₈]
  rw [hc₈] at hl₈
  have hstep₈ : step (stage2Calls stage2SubCalls) stage2Body (openS₇ C s r b) =
      .jump (openS₈ C s r b) :=
    openIfEndIITerm C (openS₇ C s r b) hl₇.inv'.pc_eq
      (hl₇.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
      (hl₇.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
      hreadL hreadC hguard₈
  have hs₈ : s₈ = openS₈ C s r b := Ctrl.jump.inj (hl₈.step.symm.trans hstep₈)
  rw [hs₈] at hl₈
  -- 9. `out_reserve.exit.i.i`: the tag byte and the length word
  have htight : C.events.length ≤ C.k :=
    hl₇.inv'.events_le_of_tight (walkEmitC_of_not_contains (b := "if.end.i.i") (by decide))
  obtain ⟨s₉, hl₉⟩ :=
    WalkLink.out_reserve_exit_i_i G (openC₈ C b) (openS₈ C s r b) hl₈.inv' rfl
      (hl₈.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
      hl₈.inv'.log_base G.evLt
      (openS₈_conv42 C s r b) (openS₈_oval C s r b) (openS₈_addiii C s r b)
      (hl₈.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
      hev63 hev64len htight hklt
  have hc₉ : { openC₈ C b with
      block := "cleanup478.i", evlen := (openC₈ C b).evlen + 1,
      events := (openC₈ C b).events ++ [EventRecord.tag (ifEnd24St b).toNat] } =
      openC₉ C b := rfl
  rw [hc₉] at hl₉
  have hstep₉ : step (stage2Calls stage2SubCalls) stage2Body (openS₈ C s r b) =
      .jump (openS₉ C s r b) :=
    openOutReserveTerm C (openS₈ C s r b) b hl₈.inv'.pc_eq
      (hl₈.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
      hl₈.inv'.log_base G.evLt (openS₈_conv42 C s r b) (openS₈_oval C s r b)
      (openS₈_addiii C s r b)
      (hl₈.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
      hev63 hev64len
  have hs₉ : s₉ = openS₉ C s r b := Ctrl.jump.inj (hl₉.step.symm.trans hstep₉)
  rw [hs₉] at hl₉
  exact Seg.measure (Seg.tail hl₅ (Seg.tail hl₆' (Seg.tail hl₇ (Seg.tail hl₈
    (Seg.tail hl₉ (Seg.nil hl₉.inv'))))))

/-! ### The composition, counted at nine

The head's four links and the tail's five: the two bytes share the tail, so the
composition's only case split is the head's route. -/

/-- **The container openers' segment**: nine links from the loop head to the merge, at
the opener's own byte. -/
theorem containerOpenSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 9 ∧
      Cd.block = "cleanup478.i" ∧ Cd.k = C.k ∧ C.sp + 1 ≤ Cd.wlen ∧
      sd.pre = some "out_reserve.exit.i.i" ∧
      evalOperand sd (.reg "%inc33.i") = some (.int 32 (BitVec.ofNat 32 (C.sp + 1))) ∧
      evalOperand sd (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
  -- the byte, at the head and at the entry the head's index reads
  have h8' : lookupName s.env "%8" = some (.int 8 b) := by simpa [evalOperand] using h8
  have hbe0 : b = BitVec.ofNat 8 (entryByte G C.k).toNat := by
    have h := Option.some.inj (h8'.symm.trans hInv.iter.reg8)
    simpa using h
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  rcases hopen with hb | hb
  · -- the open bracket
    have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 :=
      hbe0.symm.trans hb
    have hh := openBracketHead G C s hInv hblock (by rw [← hb]; exact h8) hbe
    have ht := openTailSeg G (openHeadC C) (openBrS₄ s) hh.inv' rfl hbe0 hsp519
      (by rw [openBrS₄_mem, openDepthZero_toNat]; exact hrd)
      (by rw [openBrS₄_mem, openBrS₄_next]; exact hpreV)
      r hcall hret hklt
    refine ⟨_, _, hh.trans ht, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · show C.sp + 1 ≤ max (openHeadC C).wlen ((openHeadC C).sp + 1)
      exact le_max_right _ _
    · simp only [evalOperand]
      exact openS₉_inc33 (openHeadC C) (openBrS₄ s) r b
    · simp only [evalOperand]
      rw [openS₉_inc (openHeadC C) (openBrS₄ s) r b]
      exact hh.inv'.inc_reg
    · rw [openS₉_nep (openHeadC C) (openBrS₄ s) r b]
      exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
        (by simp [walkStaticRegs])
  · -- the open brace
    have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123 :=
      hbe0.symm.trans hb
    have hh := openBraceHead G C s hInv hblock (by rw [← hb]; exact h8) hbe
    have ht := openTailSeg G (openHeadC C) (openBcS₄ s) hh.inv' rfl hbe0 hsp519
      (by rw [openBcS₄_mem, openDepthZero_toNat]; exact hrd)
      (by rw [openBcS₄_mem, openBcS₄_next]; exact hpreV)
      r hcall hret hklt
    refine ⟨_, _, hh.trans ht, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · show C.sp + 1 ≤ max (openHeadC C).wlen ((openHeadC C).sp + 1)
      exact le_max_right _ _
    · simp only [evalOperand]
      exact openS₉_inc33 (openHeadC C) (openBcS₄ s) r b
    · simp only [evalOperand]
      rw [openS₉_inc (openHeadC C) (openBcS₄ s) r b]
      exact hh.inv'.inc_reg
    · rw [openS₉_nep (openHeadC C) (openBcS₄ s) r b]
      exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
        (by simp [walkStaticRegs])

/-! ### The arm's result

The merge's index is `%inc.i` — the header's own successor — and its depth is
`%inc33.i`, the push's: an opener consumes an entry and opens a container. -/

/-- **The container openers' dispatch result**: one `merge` alternative of
`WalkDispatchResult`, at the merge the tag's store reaches, priced at `9 + 2 ≤ 32`. -/
theorem containerOpenMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨Cd, sd, hseg, hblk, hkC, hwlen, hpre, hspv, hk2, hnepv⟩ :=
    containerOpenSeg G C s hInv hblock h8 hopen hsp519 hrd hpreV r hcall hret
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  refine WalkDispatchResult.merge Cd sd 9 (C.sp + 1) (C.k + 1)
    "out_reserve.exit.i.i" (.reg "%inc33.i") (.reg "%inc.i") (BitVec.ofNat 64 G.nep)
    hseg hblk hkC hpre ?_ hspv ?_ hk2 hnepv ?_ ?_ ?_ ?_ ?_
  · show phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming = some (.reg "%inc33.i")
    decide
  · show phiIncoming "out_reserve.exit.i.i" cleanupKIncoming = some (.reg "%inc.i")
    decide
  · omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
    omega
  · have h520 : stage2StackExtent = 520 := rfl
    omega
  · exact hwlen
  · show 9 + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k)
    have h1 : C.k + 1 - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, h1]
    omega

/-! ### The depth the opener produces

The merge's depth `phi` is `%inc33.i`, so the merge's successor is a head state one
level deeper.  Both closing steps are the existing ones — `walkBack_step_at` at the
merge's own phi cells, then the header's pass — so the state is a product rather than a
hypothesis. -/

/-- **The opener produces a head state at `C.sp + 1`.**  Stated for a continuing entry,
because the merge's own test must send the walk back to the header for the header's
pass to run: at the last entry the walk leaves the loop instead. -/
theorem containerOpen_depth_one {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcont : C.k + 1 < G.nep) :
    ∃ (Cd' : WalkCarry G) (sd' : State),
      WalkInv G Cd' sd' ∧ Cd'.block = walkLoopHead ∧ Cd'.sp = C.sp + 1 ∧
        Cd'.k = C.k + 1 := by
  obtain ⟨Cd, sd, hseg, hblk, hkC, hwlen, hpre, hspv, hk2, hnepv⟩ :=
    containerOpenSeg G C s hInv hblock h8 hopen hsp519 hrd hpreV r hcall hret
  have hguard : C.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
    exact hcont
  -- the merge's closing step, at its own two phis
  obtain ⟨-, hinvB, -⟩ :=
    walkBack_step_at (calls := stage2Calls stage2SubCalls) (G := G) (C := Cd) (s := sd)
      hseg.inv' hblk hpre
      (by show phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming = some (.reg "%inc33.i")
          decide)
      hspv
      (by show phiIncoming "out_reserve.exit.i.i" cleanupKIncoming = some (.reg "%inc.i")
          decide)
      hk2 hnepv hguard
  -- the header's pass, at the two phi values and the merge's own predecessor
  obtain ⟨s'', hl''⟩ :=
    WalkLink.whileBody (calls := stage2Calls stage2SubCalls) G
      { Cd with block := "while.body.i", inner := walkInnerCap G }
      (cleanup478Out sd (C.sp + 1) (C.k + 1)) hinvB rfl rfl
      (cleanup478Out_k (s := sd) (spv := C.sp + 1) (k2 := C.k + 1))
      (cleanup478Out_sp (s := sd) (spv := C.sp + 1) (k2 := C.k + 1))
      (by show Cd.k < C.k + 1; omega)
      (by show C.k + 1 < G.nep; exact hcont)
      (by show C.sp + 1 ≤ stage2StackExtent
          have h520 : stage2StackExtent = 520 := rfl
          omega)
      (by show C.sp + 1 ≤ Cd.wlen; exact hwlen)
  exact ⟨_, s'', hl''.inv', rfl, rfl, rfl⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.containerOpenSeg
#print axioms LeanLLVM.Refinement.WalkScope.containerOpenMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_depth_one

end WalkScope
end LeanLLVM.Refinement
