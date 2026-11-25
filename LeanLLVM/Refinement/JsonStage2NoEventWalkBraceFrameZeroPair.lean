/-
The no-event walk's `{}` arm at a frame-zero head: the pair route the `]` class
has and the `}` class lacked.

`JsonStage2NoEventWalkRowsBrace` states the empty object pair's route only
together with `hfrPos : 1 ≤ fr`: its endpoint is a `Stage2NoEventWalkCycleSrc`,
whose `frameNe` field is the popped stack byte (`bytesToNat bs = fr`).  The
committed leg's *blocks* store `fr` and read it back but never test its
positivity or read the endpoint's separator; the frame positivity enters only at
the endpoint bundle, and the `hcomma` premise only in the `CycleSrc`'s `comma`
field.  So the same thirteen blocks prove the same
route from a head whose `%frame.0.ph1402` is zero, provided the endpoint is the
shape a zero frame word admits: `Stage2NoEventWalkFrameZeroSrc`.

That shape is the one the tree already has, and it is exactly what the `}` arm
consumes (`JsonStage2NoEventWalkCycleFrameZero`):

* `stage2NoEventWalkBracePairLegFrameZero` — the pair's thirteen blocks from the
  head at `{` to `after_value`'s entry at `k + 2`, at the pair's carry
  (`tok + 2`, `terms + 3`), with the endpoint a `FrameZeroSrc` whose frame word
  is zero and whose depth is the head's (`sp ≥ 1`).  **Proved here**; every
  block it uses is an existing denotation (`…BracePrologue`, `link_nodeBlock21_false`,
  `link_leafBlock19_true`, `link_ifThen81_of_bound`, `link_closeObj_live`,
  `link_ifThen343`).
* the `}` arm — `after_value → if.end369 → if.end378 → if.then384 → NodeBlock35
  → LeafBlock33 → do.body391 → close_obj`, then `close_obj`'s zero-depth arm at
  the top level or its `if.then343` pop one depth down.  **An existing
  denotation**: `stage2NoEventWalkFrameZeroBraceDeep` (nine blocks, `2 ≤ sp`)
  and `stage2NoEventWalkFrameZeroBraceTop` (eight blocks, `sp = 1`), both in
  `…CycleFrameZero`.  Nothing about it is restated here; the composition below
  only names where it enters.
* **not in this tree**: a frame-zero `after_value` cycle back to a head.  The
  committed cycle sources (`Stage2NoEventWalkCycleSrc`, `…of_afterValue`) all
  demand `frame ≠ 0`, and no lemma returns from the `}` arm's next `after_value`
  entry to a `NodeBlock5` head.  A `Stage2NoEventWalkRow.cont` for the `}` class
  therefore cannot be stated from this route alone; what is stated is the
  segment to the next `after_value` entry and the price of the three entries it
  consumes, plus the bridge that turns that entry back into the same
  `FrameZeroSrc` the pair leg takes, so a closer chain iterates.

The composed route is `13 + 9 = 22` blocks at a nested pair (`2 ≤ sp`) and
`13 + 8 = 21` at the top-level one (`sp = 1`), with the carry
`tok + 3`, `terms + 5` — the pair's two events and three terms, then the `}`'s
one event and two terms (`do.body391`'s `%inc392 = %tokens + 1` and
`%add393 = %terms + 2`, `…CycleFrameZero:391`).  The potential reads none of
those fields, so the three-entry advance is payable from three entries'
allowance (`96`).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleFrameZero

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

/-! ### The pair's carry

The `{}` pair's counts are the thirteen blocks': `if.then81` adds two tokens and
three terms (`%inc84 = %tokens + 2`, `%add85 = %terms + 3`), and `close_obj`
changes none.  This is `…RowsBrace`'s own carry, named here because that module
defines it only inside the leg. -/

/-- **The empty object pair's carry**: two events and three terms. -/
def stage2NoEventWalkBracePairCarry (K : Stage2NoEventWalkCarry) :
    Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 2, terms := K.terms + 3 }

/-- **The pair's carry leaves the potential alone.** -/
theorem stage2NoEventWalkBracePairCarry_potential (K : Stage2NoEventWalkCarry)
    (k : Nat) :
    stage2NoEventWalkPotential (stage2NoEventWalkBracePairCarry K) k =
      stage2NoEventWalkPotential K k := rfl

/-! ### The pair route at a frame-zero head

The committed leg (`stage2NoEventWalkBracePairLeg`) differs in six binders: it
takes `hfrPos : 1 ≤ fr`, `hfrLt`, `hcomma`, `hbsVal`, `hbsLen` and `hk1`, where
this route takes the head's zero frame word (`hfrH` at `0`) and the popped
byte's value (`hbsZero`).  The positivity and the separator are consumed by its
endpoint bundle (`CycleSrc.frameNe` from `hbsVal`, and `CycleSrc.comma`); the
thirteen blocks consume neither.  At `fr = 0` the endpoint is a `FrameZeroSrc` instead: the same
state facts with `frame = 0` in place of `1 ≤ frame`, and no separator premise —
the `}` arm reads the separator itself at the endpoint's index. -/

/-- **The empty object pair's route at a zero frame word**: thirteen blocks from
the head to `after_value`'s entry at `k + 2`, at the pair's carry, ending at a
`Stage2NoEventWalkFrameZeroSrc` (frame word zero, the head's depth).

`hbsZero : bytesToNat bs = 0` is the popped stack byte's value, i.e. the push's
`fr = 0` read back; it is `hbsVal` of the committed leg at `fr = 0`.  The
head's own frame reading is `%frame.0.ph1402 = 0`. -/
theorem stage2NoEventWalkBracePairLegFrameZero {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 0)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 0).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 0).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 0).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsZero : bytesToNat bs = 0)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    ∃ (s' : State) (Kc : Stage2NoEventWalkCarry),
      Kc = stage2NoEventWalkBracePairCarry K ∧
      Stage2NoEventWalkSegment calls mem K s Kc s' 13 ∧
      Nonempty (Stage2NoEventWalkFrameZeroSrc calls mem Kc (k + 2) s') := by
  classical
  let Kc : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 3 }
  let spv : BitVec 32 := BitVec.ofNat 32 sp
  let k64 : BitVec 64 := BitVec.ofNat 64 k
  let termsv : BitVec 64 := BitVec.ofNat 64 K.terms
  let tokv : BitVec 64 := BitVec.ofNat 64 K.tok
  -- the head's eight links, exported
  obtain ⟨⟨S8, hseg8, hmem8, -, P⟩⟩ :=
    stage2NoEventWalkBracePrologue (calls := calls) h hk hbs hb
    hspH hfrH hspPos hspLe hspLt hkbound hk63 hlaneW hval4lt hbyte1W
  have hstk8 : lookupName S8.env "%stk" = some (.ptr K.stk) :=
    P.hbase "%stk" (.ptr K.stk) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  -- the closer's dispatch
  have h11_8 : lookupName S8.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    rw [stage2NoEventWalkBytesToNat_single]
    exact P.h11
  have h11slt : evalICmp .slt (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (0 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S9 := stage2NoEventWalkNext (("%Pivot22", .int 1 0) :: S8.env) S8 "LeafBlock19"
  have L9 : Stage2NoEventWalkLink calls K mem S8 K S9 :=
    link_nodeBlock21_false P.inv P.pc h11_8 h11slt
  have h11_9 : lookupName S9.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h11_8
  have h11eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (1 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S10 := stage2NoEventWalkNext (("%SwitchLeaf20", .int 1 1) :: S9.env) S9 "if.then81"
  have L10 : Stage2NoEventWalkLink calls K mem S9 K S10 :=
    link_leafBlock19_true L9.inv' rfl h11_9 h11eq
  have hk10 : lookupName S10.env "%k.0.lcssa1086" = some (.int 64 k64) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hk
  have htok10 : lookupName S10.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.htokPhi
  have htr10 : lookupName S10.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S10, S9, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.htermsPhi
  have hk64nat : k64.toNat = k := by
    simp only [k64, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  have hcount10 : Stage2NoEventWalkCount K k64.toNat := by
    rw [hk64nat]; exact P.count
  have hkb : k64.toNat + 2 ≤ K.nep := by rw [hk64nat]; omega
  -- the pair's count store
  let S11 := stage2NoEventWalkNext (ifThen81Out S10.env k64 tokv termsv) S10 "close_obj"
  have L11 : Stage2NoEventWalkLink calls K mem S10 Kc S11 :=
    link_ifThen81_of_bound L10.inv' rfl rfl hk10 htok10 htr10 hcount10 hkb
  -- the live closer's operands
  let sp2 : BitVec 32 := spv + BitVec.ofNat 32 1
  have hsp11 : lookupName S11.env "%inc24" = some (.int 32 sp2) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [P.hinc24]
    simp only [sp2, spv, stage2NoEventWalkOfNat_add]
  have hk4c11 : lookupName S11.env "%inc82"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms11 : lookupName S11.env "%add85"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    rw [lookupName_cons_self]
  have htoks11 : lookupName S11.env "%inc84"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen11 : lookupName S11.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.halen
  have harena11 : lookupName S11.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.harena
  have hsp2nat : sp2.toNat = sp + 1 := by
    have h1 : spv.toNat = sp := by
      simp only [spv, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hspLt]
    simp only [sp2, BitVec.toNat_add, h1]
    rw [show (BitVec.ofNat 32 1 : BitVec 32).toNat = 1 from by decide,
      Nat.mod_eq_of_lt (by omega : sp + 1 < 2 ^ 32)]
  have hdecEq : (sp2 + BitVec.ofNat 32 4294967295).toNat = sp := by
    rw [BitVec.toNat_add, hsp2nat,
      show (BitVec.ofNat 32 4294967295 : BitVec 32).toNat = 4294967295 from by decide]
    have h2 : sp + 1 + 4294967295 = sp + 1 * 2 ^ 32 := by
      show sp + 1 + 4294967295 = sp + 1 * 4294967296
      omega
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hspLt]
  have hdecne : (sp2 + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [hdecEq]; omega
  let S12 := stage2NoEventWalkNext
    (cells (closeObjTail sp2 ++ braceCloseObjCells sp2
      (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
      (tokv + BitVec.ofNat 64 2)) S11.env) S11 "if.then343"
  have L12 : Stage2NoEventWalkLink calls Kc mem S11 Kc S12 :=
    link_closeObj_live L11.inv' rfl rfl hsp11 hk4c11 halen11 harena11 hterms11 htoks11
      hdecne
  -- the pop
  let a343 : Nat := bracePopAddr K sp
  have hsp12 : lookupName S12.env "%sp.2" = some (.int 32 sp2) := by
    simp only [S12, stage2NoEventWalkNext, closeObjTail, braceCloseObjCells, cells,
      List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hstk12 : lookupName S12.env "%stk" = some (.ptr K.stk) := by
    simp only [S12, S11, S10, S9, stage2NoEventWalkNext, ifThen81Out, cells,
      closeObjTail, braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk8
  have ha343 : a343 = closeReadAddr K.stk
      (sp2 + BitVec.ofNat 32 4294967294).toNat := by
    simp only [a343, sp2, spv, bracePopAddr]
  have hbytePop' : readBytes S12.mem a343 1 = some bs := by
    have h12 : S12.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
        (natToBytes ((BitVec.ofNat 8 0).toNat) 1) := by
      simp only [S12, S11, S10, S9, stage2NoEventWalkNext]
      exact hmem8
    rw [h12]
    exact hbytePop
  let S13 := stage2NoEventWalkNext
    (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      S12.env) S12 "after_value"
  have L13 : Stage2NoEventWalkLink calls Kc mem S12 Kc S13 :=
    link_ifThen343 L12.inv' rfl hsp12 hstk12 hbytePop' ha343
  -- the run, at the five remaining links' own fuel
  have hrun : ∀ n, runFuel calls (5 + n) stage2NoEventBody S8 =
      runFuel calls n stage2NoEventBody S13 := by
    intro n
    rw [show 5 + n = 1 + (1 + (1 + (1 + (1 + n)))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11, stage2NoEventWalkLink_runFuel L12,
      stage2NoEventWalkLink_runFuel L13]
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc S13 13 :=
    hseg8.trans ⟨hrun, L13.inv'⟩
  -- the pair's trace
  have hbsOpen : K.bs[lane]? = some (0x7B : UInt8) := by
    have hy : byte = (0x7B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [hy] using hbs
  have hbsClose : K.bs[next]? = some (0x7D : UInt8) := by
    have hy : nextByte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
    simpa [hy] using hbs1
  have htrace' : Stage2NoEventWalkTrace Kc :=
    Stage2NoEventWalkTrace.emptyObject htrace hbsOpen hbsClose
  -- the endpoint's after-value selection at the `if.then343` edge
  have h49 : lookupName S13.env "%49"
      = some (.int 8 (BitVec.ofNat 8 0)) := by
    simp only [S13, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells,
      List.cons_append, List.nil_append]
    rw [lookupName_cons_self, hbsZero]
  have hdec13 : lookupName S13.env "%dec"
      = some (.int 32 (sp2 + BitVec.ofNat 32 4294967295)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4c13 : lookupName S13.env "%k.4"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen6 : lookupName S13.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harena8 : lookupName S13.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms6 : lookupName S13.env "%terms.6"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htoks6 : lookupName S13.env "%tokens.6"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups through the route's cell layers, from the exported state
  have hbase : Stage2NoEventWalkBaseLookups Kc S13 := by
    have b9 := stage2NoEventCycleBase (K := K) (env := S8.env) P.hbase
      (cs := [("%Pivot22", .int 1 0)]) (names := ["%Pivot22"]) rfl (by decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := [("%SwitchLeaf20", .int 1 1)]) (names := ["%SwitchLeaf20"]) rfl (by decide)
    have b11 := stage2NoEventCycleBase (K := K) b10
      (cs := [("%add85", .int 64 (termsv + BitVec.ofNat 64 3)),
        ("%inc84", .int 64 (tokv + BitVec.ofNat 64 2)),
        ("%inc82", .int 64 (k64 + BitVec.ofNat 64 2))])
      (names := ["%add85", "%inc84", "%inc82"]) rfl (by decide)
    have b12 := stage2NoEventCycleBase (K := K) b11
      (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
        (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
        (tokv + BitVec.ofNat 64 2))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    have b13 := stage2NoEventCycleBase (K := K) b12
      (cs := ("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      (names := ["%49", "%arrayidx346", "%idxprom345", "%sub344"])
      rfl (by decide)
    intro n v hv
    exact b13 n v hv
  refine ⟨S13, Kc, rfl, hseg, ⟨?_⟩⟩
  refine ⟨L13.inv', rfl, 0, by decide, rfl,
    (sp2 + BitVec.ofNat 32 4294967295).toNat, ?_, ?_, ?_, ?_, ?_, ?_,
    hbase, h.bPos, htrace'⟩
  · exact (sp2 + BitVec.ofNat 32 4294967295).isLt
  · exact hdecne
  · omega
  · show k + 2 < K.nep
    omega
  · exact Stage2NoEventWalkCount.step (a := 2) (b := 2) h.count rfl rfl (by omega)
  · refine ⟨"if.then343", rfl, ?_⟩
    refine PhiSelects.cons (op := .reg "%49") (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [Kc, stateAt, evalOperand, h49, hdec13, hk4c13, halen6, harena8,
        hterms6, htoks6, k64, termsv, tokv, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ### The `}` arm composed with the pair route

The arm's denotation is `…CycleFrameZero`'s, not restated here: from a
`FrameZeroSrc` at `k + 2` and the entry there reading `}` (`125`), the deeper
arm is nine blocks to `after_value` at `k + 3` at the close-brace carry, one
depth lower, with the frame word the enclosing tag popped from the stack.  At
`sp = 1` the closer's zero-depth arm ends at depth zero in eight blocks. -/

/-- **The pair route and the `}` arm at a nested pair** (`2 ≤ sp`): `jl + 9`
blocks from the head to `after_value`'s entry at `k + 3`, at the composed carry
(`tok + 3`, `terms + 5`), the depth one lower.  The arm is
`stage2NoEventWalkFrameZeroBraceDeep`, an existing denotation; the separator at
`k + 2` and the arm's own stack pop are the caller's facts at this state's
memory. -/
theorem stage2NoEventWalkBraceFrameZeroCloseDeep {calls : Calls} {mem : Mem}
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
    ∃ s'' : State,
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) s'' (jl + 9) ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 3) s'') := by
  obtain ⟨s', hseg, hdst⟩ :=
    stage2NoEventWalkFrameZeroBraceDeep hsrc hspTwo hk2 hbs2 hbyte2 hpop hpopAddr hbsLen
  exact ⟨s', hleg.trans hseg, hdst⟩

/-- **The pair route and the `}` arm at a top-level pair** (`sp = 1`): `jl + 8`
blocks to `after_value`'s entry at `k + 3`, at the composed carry, the depth
zero.  The arm is `stage2NoEventWalkFrameZeroBraceTop`. -/
theorem stage2NoEventWalkBraceFrameZeroCloseTop {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State} {jl lane2 : Nat}
    {byte2 : UInt8}
    (hleg : Stage2NoEventWalkSegment calls mem K s
      (stage2NoEventWalkBracePairCarry K) sE jl)
    (hsrc : Stage2NoEventWalkFrameZeroSrc calls mem
      (stage2NoEventWalkBracePairCarry K) (k + 2) sE)
    (hspOne : hsrc.sp = 1)
    (hk2 : (stage2NoEventWalkBracePairCarry K).ent[k + 2]? = some lane2)
    (hbs2 : (stage2NoEventWalkBracePairCarry K).bs[lane2]? = some byte2)
    (hbyte2 : byte2.toNat = 125) :
    ∃ s'' : State,
      Stage2NoEventWalkSegment calls mem K s
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) s'' (jl + 8) ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 3) s'') := by
  obtain ⟨s', hseg, hdst⟩ :=
    stage2NoEventWalkFrameZeroBraceTop hsrc hspOne hk2 hbs2 hbyte2
  exact ⟨s', hleg.trans hseg, hdst⟩

/-! ### The composed price

The route consumes three entries (`k`, `k + 1`, `k + 2`'s continuation) and the
closer advances to `k + 3`; the potential is the same at the composed carry, so
any block count up to three entries' allowance (`96`) is payable — `22` for the
nested pair, `21` at the top level. -/

/-- **The `}`-class route's price**: `jl ≤ 96` and `jl + Φ Kc (k+3) ≤ Φ K k`, at
the composed carry. -/
theorem stage2NoEventWalkBraceFrameZeroPairClosePrice {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {jl : Nat} (hjl : jl ≤ 96)
    (hk3 : k + 3 < K.nep) :
    jl + stage2NoEventWalkPotential
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 3) ≤
      stage2NoEventWalkPotential K k := by
  have hpot : stage2NoEventWalkPotential
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) (k + 3) =
      stage2NoEventWalkPotential K (k + 3) := rfl
  rw [hpot]
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 3) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 3)
    (Nat.le_of_lt hk3) hentle
  have h96 : 32 * 3 = 96 := by decide
  rw [h96] at hadd
  omega

/-! ### The endpoint one level up

The `}` arm hands back a `Stage2NoEventWalkAfterValueEntry`, not a
`Stage2NoEventWalkCycleSrc` (which demands a non-zero frame word).  At an object
parent the popped tag is zero, and that entry is the same `FrameZeroSrc` the pair
leg takes at the next index — so the closers chain.  The four facts a
`FrameZeroSrc` needs on top of the entry are the caller's: the frame word's zero,
the depth's non-zero, and the address and liveness bounds. -/

/-- **An after-value entry at a zero frame word is a frame-zero source**, given
the depth's non-zero and the index bounds. -/
def stage2NoEventWalkFrameZeroSrc_of_afterValueEntry {calls : Calls}
    {mem : Mem} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K k s)
    (hframe : h.frame = 0) (hspNe : h.sp ≠ 0)
    (hkAddr : k + 1 < 2 ^ 63) (hklt : k < K.nep) :
    Stage2NoEventWalkFrameZeroSrc calls mem K k s :=
  { inv := h.inv, pc := h.pc, frame := h.frame, frameLt := h.frameLt,
    frameZero := hframe, sp := h.sp, spLt := h.spLt, spNe := hspNe,
    kAddr := hkAddr, klt := hklt, count := h.count, phiRun := h.phiRun,
    baseLookups := h.baseLookups, bPos := h.bPos, trace := h.trace }

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracePairCarry_potential
#print axioms stage2NoEventWalkBracePairLegFrameZero
#print axioms stage2NoEventWalkBraceFrameZeroCloseDeep
#print axioms stage2NoEventWalkBraceFrameZeroCloseTop
#print axioms stage2NoEventWalkBraceFrameZeroPairClosePrice
#print axioms stage2NoEventWalkFrameZeroSrc_of_afterValueEntry

end LeanLLVM.Refinement
