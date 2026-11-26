/-
The no-event walk's `}` close at a frame-zero entry: the endpoint entry as data.

`JsonStage2NoEventWalkCycleFrameZero` proves the two `}` arms —
`stage2NoEventWalkFrameZeroBraceTop` (eight blocks, `%sp.4 = 1`) and
`stage2NoEventWalkFrameZeroBraceDeep` (nine blocks, `2 ≤ %sp.4`) — but its
conclusions are `∃ s', Segment … ∧ Nonempty (AfterValueEntry …)`.  The witness
entry is inside a `Nonempty`, so neither its frame word nor its depth can be
read: any consumer sees only that *some* entry exists there.  That is the whole
of the interface gap the residue table records for the brace class's `}`: the
committed cycle source `Stage2NoEventWalkCycleSrc` needs `frame ≠ 0` and
`sp ≠ 0`, and the arm's conclusion cannot supply either, so
`stage2NoEventWalkBraceFrameZeroCloserRow` (`JsonStage2NoEventWalkRowsDischarge`)
takes them as its caller's post, quantified over *every* entry at the endpoint.

This module closes that gap by proving the arms again at the same blocks, with
the endpoint entry returned as data and the words the arm already computes
stated as equations:

* `stage2NoEventWalkFrameZeroBraceTopEntry` — the eight blocks, the endpoint
  entry at depth `0` and frame `0`;
* `stage2NoEventWalkFrameZeroBraceDeepEntry` — the nine blocks, the endpoint
  entry at depth `%sp.4 - 1` and frame the popped byte `bytesToNat bs`;
* `stage2NoEventWalkBraceFrameZeroCloseDeepEntry` — the pair leg and the deep
  arm composed, the same two equations at `k + 3`;
* `stage2NoEventWalkBraceFrameZeroCloserRowOfEntry` — the row, with the
  endpoint's frame and depth read off the entry instead of taken as a post that
  quantifies over states the arm does not produce.

The committed statements are untouched; the new theorems sit beside them.

**Where each premise comes from.**

* The entry source (`h`), the entry index's lane and byte (`hk`, `hbs`), and the
  byte's value (`hbyte`/`hbyte2`) are the caller's staging of the route: the
  head's own facts and the document's bytes.
* The pop (`hpop`, `hpopAddr`, `hbsLen`) is the caller's fact about the stack at
  the endpoint's state, exactly as the committed arm takes it.
* In the row, `hbsNe : bytesToNat bs ≠ 0` is the caller's fact that the tag
  popped from the stack is not the zero byte — the words the stack carries are
  the caller's knowledge, as the depth's non-zero and the comma were before.
  The endpoint's frame word *is* that tag (`…BraceDeepEntry`'s equation), and
  its depth is `%sp.4 - 1`, non-zero at `2 ≤ %sp.4`; neither is assumed.
* The comma at `k + 3`, the price (`jl + 9 ≤ 96`) and the index bounds are the
  caller's, as the committed row states them.

The top-level endpoint (`%sp.4 = 1`) is the terminal lane's: its entry is at
depth zero and frame zero (`…BraceTopEntry`), so the cycle source does not apply
there and no continuation is stated for it.

The arm's blocks are the committed denotations of
`JsonStage2NoEventWalkCycleFrameZero`; nothing about a block is restated here.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDischarge

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The depth the decrement gives

`%dec = %sp.4 + 4294967295` is the `i32` register the closer's `phi` reads back as
the next entry's depth; its value is `%sp.4 - 1` in `Nat`, and it is non-zero
whenever `2 ≤ %sp.4`. -/

/-- **The decremented depth is the source depth less one.** -/
theorem stage2NoEventWalkDec_toNat {sp : Nat} (hspLt : sp < 2 ^ 32) (hspPos : 1 ≤ sp) :
    (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat = sp - 1 := by
  rw [stage2NoEventWalkOfNat_add 32 sp 4294967295, BitVec.toNat_ofNat]
  have h2 : sp + 4294967295 = (sp - 1) + 1 * 2 ^ 32 := by omega
  rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- **The decremented depth is non-zero** at `2 ≤ %sp.4`. -/
theorem stage2NoEventWalkDec_ne_zero {sp : Nat} (hspLt : sp < 2 ^ 32) (hspTwo : 2 ≤ sp) :
    (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
  rw [stage2NoEventWalkDec_toNat hspLt (by omega)]
  omega

/-! ### The top-level `}` arm, at its endpoint entry

The same eight blocks as `stage2NoEventWalkFrameZeroBraceTop`, returning the
endpoint `AfterValueEntry` at `k + 1`, with its depth and frame words stated:
`close_obj`'s zero-depth arm writes `%dec = 0` and the immediate `0`, so the
entry's `sp` and `frame` are both zero. -/

/-- **The frame-zero `}` step at the top level, entry exposed** (`%sp.4 = 1`):
eight blocks from the entry at `k` to the next `after_value` entry at `k + 1`,
at the close-brace carry, the endpoint's depth and frame both zero. -/
theorem stage2NoEventWalkFrameZeroBraceTopEntry {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    (hspOne : h.sp = 1)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125) :
    ∃ (s' : State) (e : Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s'),
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry K) s' 8 ∧
      e.frame = 0 ∧ e.sp = 0 := by
  obtain ⟨s3, hseg3, hpc3, hpre3, h53, hinc, hcmp, hframe3, hk6, hsp4, htok, hterms,
    halen, harena, hbase3, hinv3, hcount, htrace, hbpos, hmem3⟩ :=
    stage2NoEventWalkFrameZeroToThen384 h hk hbs
  have hbyte' : BitVec.ofNat 8 byte.toNat = (BitVec.ofNat 8 125) := by rw [hbyte]
  -- `if.then384`
  let r4 : State := stage2NoEventWalkNext s3.env s3 "NodeBlock35"
  have h53r4 : lookupName r4.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r4, stage2NoEventWalkNext]
    exact h53
  have l4 : Stage2NoEventWalkLink calls K mem s3 K r4 :=
    stage2NoEventWalkLink_br hinv3 (by rw [hpc3]; exact ifThen384Block_find)
      (by rw [ifThen384Block]; exact denoteCode_nil calls (stateAt s3.env s3)) rfl
  -- `NodeBlock35`: 125 is not below 125
  let r5 : State := stage2NoEventWalkNext (cells (nodeBlock35Cells 0) r4.env) r4
    "LeafBlock33"
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_false l4.inv'
      (by rw [show r4.pc = "NodeBlock35" from rfl]; exact nodeBlock35Block_find)
      (nodeBlock35_denote (calls := calls) (env := r4.env) (s := r4)
        (y := BitVec.ofNat 8 byte.toNat) (c := 0) h53r4 (by rw [hbyte']; decide))
      rfl (by simp only [r5, nodeBlock35Cells, cells, lookupName_cons_self])
  have h53r5 : lookupName r5.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r5, stage2NoEventWalkNext, cells, nodeBlock35Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r4
  -- `LeafBlock33`: the byte is the close brace
  let r6 : State := stage2NoEventWalkNext (cells (leafBlock33Cells 1) r5.env) r5
    "do.body391"
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock33" from rfl]; exact leafBlock33Block_find)
      (leafBlock33_denote (calls := calls) (env := r5.env) (s := r5)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r5 (by rw [hbyte']; decide))
      rfl (by simp only [r6, leafBlock33Cells, cells, lookupName_cons_self])
  -- `do.body391`: the counts
  have htok6 : lookupName r6.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hterms6 : lookupName r6.env "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  let r7 : State := stage2NoEventWalkNext
    (cells (doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      r6.env) r6 "close_obj"
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_br l6.inv'
      (by rw [show r6.pc = "do.body391" from rfl]; exact doBody391Block_find)
      (doBody391_denote (calls := calls) (env := r6.env) (s := r6)
        (tok := BitVec.ofNat 64 K.tok) (terms := BitVec.ofNat 64 K.terms)
        htok6 hterms6)
      rfl
  -- the carry after the count store
  have hinvC : Stage2NoEventWalkInv (stage2NoEventWalkCloseBraceCarry K) mem r7 :=
    (Stage2NoEventWalkInv.count (h := l7.inv') (t := 1) (c := 2)
      (Stage2NoEventWalkInv.tok_add_le l7.inv' hcount
        (by have := h.klt; omega))).mem_congr rfl
  -- the closer's six `phi`s at the `do.body391` edge
  have hsp7 : lookupName r7.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp4
  have hinc7 : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have htok7 : lookupName r7.env "%inc392" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hterms7 : lookupName r7.env "%add393" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells, lookupName_cons_self]
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hdecA : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat = 0 := by
    rw [hspOne]
    decide
  -- the closer's zero-depth arm
  let sA : State := stage2NoEventWalkNext
    (cells (closeObjTail (BitVec.ofNat 32 h.sp) ++
      braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) r7.env) r7 "after_value"
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem r7
      (stage2NoEventWalkCloseBraceCarry K) sA :=
    link_closeObj_doBody391_zero hinvC rfl rfl hsp7 hinc7 halen7 harena7 hterms7 htok7
      hdecA
  -- the run, at the eight blocks
  have hrun : ∀ n, runFuel calls (8 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody sA := by
    intro n
    rw [show 8 + n = 3 + (1 + (1 + (1 + (1 + (1 + n))))) from by omega]
    rw [hseg3.run (1 + (1 + (1 + (1 + (1 + n))))),
      stage2NoEventWalkLink_runFuel l4, stage2NoEventWalkLink_runFuel l5,
      stage2NoEventWalkLink_runFuel l6, stage2NoEventWalkLink_runFuel l7,
      stage2NoEventWalkLink_runFuel l8]
  -- the endpoint's cells
  have hdecS : lookupName sA.env "%dec"
      = some (.int 32 (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, List.cons_append, List.nil_append]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hk4S : lookupName sA.env "%k.4"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halenS : lookupName sA.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harenaS : lookupName sA.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htermsS : lookupName sA.env "%terms.6"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokS : lookupName sA.env "%tokens.6"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups at the endpoint
  have hb8 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName sA.env n = some v := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    have h4 := stage2NoEventCycleBase (K := K) h3
      (cs := closeObjTail (BitVec.ofNat 32 h.sp) ++
        braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
          (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
          (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    intro n v hv
    exact h4 n v hv
  have hword0 : BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295 =
      BitVec.ofNat 32 0 := by
    rw [hspOne]
    decide
  -- the endpoint's dispatch selection at the `close_obj` edge
  have hsel : PhiSelects (stateAt sA.env sA) "close_obj" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 0)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 0)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).tok))] := by
    refine PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 0))) (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stage2NoEventConstToValue_int,
        stage2NoEventWalkCloseBraceCarry, stateAt, evalOperand, hdecS,
        hword0, hk4S, halenS, harenaS, htermsS, htokS, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- the endpoint's trace
  have hbsClose : K.bs[lane]? = some (0x7D : UInt8) := by
    have hy : byte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hbyte]; decide)
    simpa [hy] using hbs
  have htraceC : Stage2NoEventWalkTrace (stage2NoEventWalkCloseBraceCarry K) :=
    Stage2NoEventWalkTrace.closeBrace htrace hbsClose
  refine ⟨sA, ⟨l8.inv', rfl, 0, by decide, 0, by decide, ?_,
      ⟨"close_obj", rfl, hsel⟩, hb8, hbpos, htraceC⟩,
    ⟨hrun, l8.inv'⟩, rfl, rfl⟩
  exact Stage2NoEventWalkCount.step (a := 1) (b := 1) hcount rfl rfl (by omega)

/-! ### The nested `}` arm, at its endpoint entry

The same nine blocks as `stage2NoEventWalkFrameZeroBraceDeep`, returning the
endpoint `AfterValueEntry` at `k + 1` with its two words stated: the pop's byte
`bytesToNat bs` is the frame word, and `%dec` is the depth one lower. -/

/-- **The frame-zero `}` step at a nested depth, entry exposed** (`2 ≤ %sp.4`):
nine blocks, the `if.then343` pop included, from the entry at `k` to the next
one at `k + 1`, at the close-brace carry, the endpoint's frame the popped byte
and its depth `%sp.4 - 1`. -/
theorem stage2NoEventWalkFrameZeroBraceDeepEntry {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    (hspTwo : 2 ≤ h.sp)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125)
    {a : Nat} {bs : List UInt8}
    (hpop : readBytes s.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr K.stk
      (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1) :
    ∃ (s' : State) (e : Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s'),
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry K) s' 9 ∧
      e.frame = bytesToNat bs ∧ e.sp = h.sp - 1 := by
  obtain ⟨s3, hseg3, hpc3, hpre3, h53, hinc, hcmp, hframe3, hk6, hsp4, htok, hterms,
    halen, harena, hbase3, hinv3, hcount, htrace, hbpos, hmem3⟩ :=
    stage2NoEventWalkFrameZeroToThen384 h hk hbs
  have hbyte' : BitVec.ofNat 8 byte.toNat = (BitVec.ofNat 8 125) := by rw [hbyte]
  let r4 : State := stage2NoEventWalkNext s3.env s3 "NodeBlock35"
  have h53r4 : lookupName r4.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r4, stage2NoEventWalkNext]
    exact h53
  have l4 : Stage2NoEventWalkLink calls K mem s3 K r4 :=
    stage2NoEventWalkLink_br hinv3 (by rw [hpc3]; exact ifThen384Block_find)
      (by rw [ifThen384Block]; exact denoteCode_nil calls (stateAt s3.env s3)) rfl
  let r5 : State := stage2NoEventWalkNext (cells (nodeBlock35Cells 0) r4.env) r4
    "LeafBlock33"
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_false l4.inv'
      (by rw [show r4.pc = "NodeBlock35" from rfl]; exact nodeBlock35Block_find)
      (nodeBlock35_denote (calls := calls) (env := r4.env) (s := r4)
        (y := BitVec.ofNat 8 byte.toNat) (c := 0) h53r4 (by rw [hbyte']; decide))
      rfl (by simp only [r5, nodeBlock35Cells, cells, lookupName_cons_self])
  have h53r5 : lookupName r5.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r5, stage2NoEventWalkNext, cells, nodeBlock35Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r4
  let r6 : State := stage2NoEventWalkNext (cells (leafBlock33Cells 1) r5.env) r5
    "do.body391"
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock33" from rfl]; exact leafBlock33Block_find)
      (leafBlock33_denote (calls := calls) (env := r5.env) (s := r5)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r5 (by rw [hbyte']; decide))
      rfl (by simp only [r6, leafBlock33Cells, cells, lookupName_cons_self])
  have htok6 : lookupName r6.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hterms6 : lookupName r6.env "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  let r7 : State := stage2NoEventWalkNext
    (cells (doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      r6.env) r6 "close_obj"
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_br l6.inv'
      (by rw [show r6.pc = "do.body391" from rfl]; exact doBody391Block_find)
      (doBody391_denote (calls := calls) (env := r6.env) (s := r6)
        (tok := BitVec.ofNat 64 K.tok) (terms := BitVec.ofNat 64 K.terms)
        htok6 hterms6)
      rfl
  have hinvC : Stage2NoEventWalkInv (stage2NoEventWalkCloseBraceCarry K) mem r7 :=
    (Stage2NoEventWalkInv.count (h := l7.inv') (t := 1) (c := 2)
      (Stage2NoEventWalkInv.tok_add_le l7.inv' hcount
        (by have := h.klt; omega))).mem_congr rfl
  have hsp7 : lookupName r7.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp4
  have hinc7 : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have htok7 : lookupName r7.env "%inc392" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hterms7 : lookupName r7.env "%add393" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells, lookupName_cons_self]
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hstk7 : lookupName r7.env "%stk" = some (.ptr K.stk) := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    exact h3 "%stk" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hdecB : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat ≠ 0 :=
    stage2NoEventWalkDec_ne_zero h.spLt hspTwo
  -- the closer's live arm
  let s9 : State := stage2NoEventWalkNext
    (cells (closeObjTail (BitVec.ofNat 32 h.sp) ++
      braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) r7.env) r7 "if.then343"
  have hsp16 : lookupName s9.env "%sp.2"
      = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [s9, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem r7
      (stage2NoEventWalkCloseBraceCarry K) s9 :=
    link_closeObj_doBody391_live hinvC rfl rfl hsp7 hinc7 halen7 harena7 hterms7 htok7
      hdecB
  -- the pop
  let sA : State := stage2NoEventWalkNext
    (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells a ++ closeIdxCells
        (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294)) s9.env) s9 "after_value"
  have hstk9 : lookupName s9.env "%stk" = some (.ptr K.stk) := by
    simp only [s9, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk7
  have l9 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem s9
      (stage2NoEventWalkCloseBraceCarry K) sA :=
    link_ifThen343 l8.inv' rfl hsp16 hstk9
      (by simpa only [s9, r7, r6, r5, r4, stage2NoEventWalkNext, hmem3] using hpop) hpopAddr
  have hrun : ∀ n, runFuel calls (9 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody sA := by
    intro n
    rw [show 9 + n = 3 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))) from by omega]
    rw [hseg3.run (1 + (1 + (1 + (1 + (1 + (1 + n)))))),
      stage2NoEventWalkLink_runFuel l4, stage2NoEventWalkLink_runFuel l5,
      stage2NoEventWalkLink_runFuel l6, stage2NoEventWalkLink_runFuel l7,
      stage2NoEventWalkLink_runFuel l8, stage2NoEventWalkLink_runFuel l9]
  -- the endpoint's cells
  have h49S : lookupName sA.env "%49"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    rw [lookupName_cons_self]
  have hdecS : lookupName sA.env "%dec"
      = some (.int 32 (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4S : lookupName sA.env "%k.4"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halenS : lookupName sA.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harenaS : lookupName sA.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htermsS : lookupName sA.env "%terms.6"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokS : lookupName sA.env "%tokens.6"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups at the endpoint
  have hb10 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName sA.env n = some v := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    have h4 := stage2NoEventCycleBase (K := K) h3
      (cs := closeObjTail (BitVec.ofNat 32 h.sp) ++
        braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
          (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
          (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    have h5 := stage2NoEventCycleBase (K := K) h4
      (cs := ("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a ++ closeIdxCells
          (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294))
      (names := ["%49", "%arrayidx346", "%idxprom345", "%sub344"]) rfl (by decide)
    intro n v hv
    exact h5 n v hv
  -- the endpoint's dispatch selection at the `if.then343` edge
  have hsel : PhiSelects (stateAt sA.env sA) "if.then343" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 (bytesToNat bs))),
       ("%sp.4", .int 32 (BitVec.ofNat 32
         (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).tok))] := by
    refine PhiSelects.cons (op := .reg "%49") (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stage2NoEventWalkCloseBraceCarry, stateAt, evalOperand, h49S,
        hdecS, hk4S, halenS, harenaS, htermsS, htokS, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbsClose : K.bs[lane]? = some (0x7D : UInt8) := by
    have hy : byte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hbyte]; decide)
    simpa [hy] using hbs
  have htraceC : Stage2NoEventWalkTrace (stage2NoEventWalkCloseBraceCarry K) :=
    Stage2NoEventWalkTrace.closeBrace htrace hbsClose
  refine ⟨sA, ⟨l9.inv', rfl,
      (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat,
      (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).isLt, bytesToNat bs,
      stage2NoEventWalkBytesToNat_lt hbsLen, ?_,
      ⟨"if.then343", rfl, hsel⟩, hb10, hbpos, htraceC⟩,
    ⟨hrun, l9.inv'⟩, rfl, stage2NoEventWalkDec_toNat h.spLt (by omega)⟩
  exact Stage2NoEventWalkCount.step (a := 1) (b := 1) hcount rfl rfl (by omega)

/-! ### The pair route and the `}` arm, at the endpoint entry

The composed route `JsonStage2NoEventWalkBraceFrameZeroPair` proves as
`Nonempty`; here the deep composition returns the entry with the same two
equations at `k + 3`. -/

/-- **The pair route and the `}` arm at a nested pair, entry exposed**: the
thirteen-block pair leg and the nine-block close as one segment to `after_value`
at `k + 3`, at the composed carry, with the endpoint's frame word the popped
tag and its depth `%sp.4 - 1`. -/
theorem stage2NoEventWalkBraceFrameZeroCloseDeepEntry {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State} {jl lane2 : Nat}
    {byte2 : UInt8} {a : Nat} {bs : List UInt8}
    (hleg : Stage2NoEventWalkSegment calls mem K s
      (stage2NoEventWalkBracePairCarry K) sE jl)
    (hsrc : Stage2NoEventWalkFrameZeroSrc calls mem
      (stage2NoEventWalkBracePairCarry K) (k + 2) sE)
    (hspTwo : 2 ≤ hsrc.sp)
    (hk2 : (stage2NoEventWalkBracePairCarry K).ent[k + 2]? = some lane2)
    (hbs2 : (stage2NoEventWalkBracePairCarry K).bs[lane2]? = some byte2)
    (hbyte2 : byte2.toNat = 125)
    (hpop : readBytes sE.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr (stage2NoEventWalkBracePairCarry K).stk
      (BitVec.ofNat 32 hsrc.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1) :
    ∃ (s'' : State) (e : Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 3) s''),
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) s'' (jl + 9) ∧
      e.frame = bytesToNat bs ∧ e.sp = hsrc.sp - 1 := by
  obtain ⟨s', e, hseg, hf, hs⟩ :=
    stage2NoEventWalkFrameZeroBraceDeepEntry hsrc hspTwo hk2 hbs2 hbyte2 hpop hpopAddr
      hbsLen
  exact ⟨s', e, hleg.trans hseg, hf, hs⟩

/-! ### The row, at the exposed endpoint

The committed row `stage2NoEventWalkBraceFrameZeroCloserRow` asks its caller for
a post over *every* entry at the endpoint, because the arm's `Nonempty` witness
gives it none at the state the arm actually produces.  Here the entry is data
and its two words are the arm's own: the frame word is the popped tag, so
`hbsNe` makes it non-zero; the depth is `%sp.4 - 1`, non-zero at `2 ≤ %sp.4`.
The composition to the head at `k + 4` is
`stage2NoEventWalkBraceFrameZeroCloseToHead`, unchanged. -/

/-- **The `}` class's row, at the exposed endpoint.**  The pair leg, the deep
`}` arm and the committed cycle composed: from the head at `k` to the head at
`k + 4`, at the step's plus the cycle's price.  The endpoint's frame word is the
popped tag, non-zero by the caller's `hbsNe`; its depth is `hsrc.sp - 1`,
non-zero at `2 ≤ hsrc.sp`.  The comma at `k + 3`, the price (`jl + 9 ≤ 96`) and
the index bounds are the caller's, as in the committed row. -/
noncomputable def stage2NoEventWalkBraceFrameZeroCloserRowOfEntry {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry}
    {k : Nat} {s sE : State} {jl lane2 : Nat} {byte2 : UInt8}
    {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (hleg : Stage2NoEventWalkSegment calls mem K s
      (stage2NoEventWalkBracePairCarry K) sE jl)
    (hsrc : Stage2NoEventWalkFrameZeroSrc calls mem
      (stage2NoEventWalkBracePairCarry K) (k + 2) sE)
    (hspTwo : 2 ≤ hsrc.sp)
    (hk2 : (stage2NoEventWalkBracePairCarry K).ent[k + 2]? = some lane2)
    (hbs2 : (stage2NoEventWalkBracePairCarry K).bs[lane2]? = some byte2)
    (hbyte2 : byte2.toNat = 125)
    (hpop : readBytes sE.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr (stage2NoEventWalkBracePairCarry K).stk
      (BitVec.ofNat 32 hsrc.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1)
    (hbsNe : bytesToNat bs ≠ 0)
    (hjl : jl + 9 ≤ 96)
    (hk3 : k + 3 < K.nep)
    (hkAddr : k + 4 < 2 ^ 63)
    (hklt : k + 4 < K.nep)
    (hcomma : ∀ lane,
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).ent[k + 3]? =
        some lane →
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).bs.getD lane 0
        = 44) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨s'', e, hseg, hframe, hspv⟩ :=
    stage2NoEventWalkBraceFrameZeroCloseDeepEntry hleg hsrc hspTwo hk2 hbs2 hbyte2
      hpop hpopAddr hbsLen
  have hframeNe : e.frame ≠ 0 := by rw [hframe]; exact hbsNe
  have hspNe : e.sp ≠ 0 := by rw [hspv]; omega
  obtain ⟨s', p, hp⟩ :=
    stage2NoEventWalkBraceFrameZeroCloseToHead h (by omega) hk3 hseg e hframeNe hspNe
      hkAddr
      (by simpa only [stage2NoEventWalkCloseBraceCarry,
        stage2NoEventWalkBracePairCarry] using hklt) hcomma
  exact ⟨Stage2NoEventWalkRow.cont
    (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
    (k + 4) s' (jl + 9 + p) hp rfl rfl rfl (by omega) hklt⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkDec_toNat
#print axioms stage2NoEventWalkDec_ne_zero
#print axioms stage2NoEventWalkFrameZeroBraceTopEntry
#print axioms stage2NoEventWalkFrameZeroBraceDeepEntry
#print axioms stage2NoEventWalkBraceFrameZeroCloseDeepEntry
#print axioms stage2NoEventWalkBraceFrameZeroCloserRowOfEntry

end LeanLLVM.Refinement
