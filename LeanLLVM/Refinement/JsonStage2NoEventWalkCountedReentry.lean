/-
The no-event walk's counted-loop re-entry: the array loop's dispatch after an
element's row, and the two routes into it.

**The loop.**  The pinned body has two headers for one element sequence.  The
first iteration's header is `if.end.peel` (reached from the preheader and from
the walk's backedge `value.outer.backedge`); the later iterations' header is
`if.end`, entered from `if.end327` (non-peeled) or `if.end327.peel`, and it
increments `%tokens.0`/`%terms.0`/`%indvars.iv`/`%inc` and dispatches at
`NodeBlock15`.  `if.end327` is the loop's latch: it reads the entry at `%inc`,
takes `if.then334.loopexit` when that entry's byte is `]`, and otherwise enters
`if.end`.

**The one predecessor.**  `stage2NoEventBody_countedPreds` reads the pinned body's
terminators: the only block naming `if.end327` is `if.end51`, the only block
naming `if.end51` is `if.then35`, the only block naming `if.then35` is
`LeafBlock9`, and `LeafBlock9`'s only predecessor is `NodeBlock13`, itself
reached only from `NodeBlock15`.  So a state at `if.end327`'s entry is
producible only from a `NodeBlock15` dispatch: the non-peeled latch cannot
bootstrap itself, and no element's row ends at it.  The peel's latch
(`if.end327.peel`) is the loop's bootstrap, and the non-peeled one is its
internal continuation.

**What re-enters the loop.**  After an element's row completes, the class lane's
endpoint is `after_value`'s entry (a `Stage2NoEventWalkCycleSrc`), and the shared
cycle (`stage2NoEventWalkCycle_of_afterValue_sp`) returns to the next head at
`NodeBlock5`, carrying that head's depth word at the endpoint's own `sp`.  The
next counted-loop iteration begins there: the head's own dispatch is the route's
first three links (`NodeBlock5` → `NodeBlock` → `LeafBlock1`), and at the byte
`[` it runs to `if.then35.peel`, pushes the frame at `%stk + sp − 1` (four links:
`if.end45.peel`, `if.then47.peel`, `if.end51.peel`, `if.end327.peel`), reads the
entry at `k + 2` at the peeled latch, and `if.end`'s `phi` run hands
`NodeBlock15` the seven cell readings — nine links in all, the committed
`stage2NoEventWalkBracketDescendStep`.

**The staging the descent needs is derived, not supplied.**  The step's premise
is `Stage2NoEventWalkDescendBranch`, whose depth is one pinned `Nat` with its
cell and bounds.  The endpoint carries exactly those: `CycleSrc.sp`, its cell
(the cycle's own tie), `spLt`, `spNe`, and the route's room `sp ≤ 519`.  So the
structure is built at the produced head from the endpoint's own data, and the
descend needs no state fact a row's start does not already have.

**The loop's internal continuation.**  Once a `NodeBlock15` dispatch exists, a
`[` element's route runs `NodeBlock15` → `NodeBlock13` → `LeafBlock9` →
`if.then35` → `if.end51` (the marker `1`) → `if.end327`'s entry, and
`stage2NoEventWalkCountedContinue` composes `if.end327`'s entry read with
`ifEndProduce_fromEnd327` to the next dispatch: two blocks, the seven cells, the
carry's counts advanced by the opener.  The tree states the seven-block form of
the same handoff from the dispatch window as
`stage2NoEventWalkBracketInnerElement`.

**The consequence.**  The counted-loop iteration's dispatch state from an
element's endpoint is produced, with the seven cells at the values below.  What a
continue-row at the endpoint still needs is the element's own route from that
dispatch (the class's `.loopexit` route, `Stage2NoEventWalkBracketInner`'s
obligation) and its price.  The leg's count is the cycle's `p` plus the descend's
nine links, and the credit the cycle proves,
`p + Φ K (k+1) ≤ Φ K k`, certifies only `p` (its own count is eight): the descend's
links are counted by `Stage2NoEventWalkSegment.of_chain`'s existential `j`, so no
claim about them is made here.  Concretely they cost nine, and the two counts
together (17) fit a single entry's `32`, so the row's arithmetic closes once the
inner element advances the index; the tree's
`Stage2NoEventWalkBracketInnerOut.price` is that composition, charging the
descend's links (its `j0`) against the inner advance.  Writing
`Δ = K.ent[k+1] − K.ent[k]` for the entries' document-distance, one entry's
allowance is `Φ K k − Φ K (k+1) = 32 + 8·Δ` (`stage2NoEventWalkPotential_add`);
the remaining model work is the inner element's route at `{`, `"` and scalar,
and at `[` the committed recursion supplies it.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkBracketInner
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDescend

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The latch's only predecessor

The census is over the pinned body's terminators; it is a `decide` because the
body is a parsed value, and it is stated as the list of blocks whose terminator
names each block, so no route argument can leave the five-block chain. -/

/-- **The counted loop's latch has one predecessor chain.**  In the pinned body,
`if.end327`'s only predecessor is `if.end51`, `if.end51`'s only predecessor is
`if.then35`, `if.then35`'s only predecessor is `LeafBlock9`, `LeafBlock9`'s only
predecessor is `NodeBlock13`, and `NodeBlock13`'s only predecessor is
`NodeBlock15`.  A state at the non-peeled latch is therefore producible only from
a `NodeBlock15` dispatch: the peeled `if.end327.peel` is the loop's bootstrap,
and the non-peeled latch is its internal continuation. -/
theorem stage2NoEventBody_countedPreds :
    (stage2NoEventBody.blocks.filter
        (fun bd => "if.end327" ∈ bd.term.targets)).map (·.name) = ["if.end51"] ∧
      (stage2NoEventBody.blocks.filter
        (fun bd => "if.end51" ∈ bd.term.targets)).map (·.name) = ["if.then35"] ∧
      (stage2NoEventBody.blocks.filter
        (fun bd => "if.then35" ∈ bd.term.targets)).map (·.name) = ["LeafBlock9"] ∧
      (stage2NoEventBody.blocks.filter
        (fun bd => "LeafBlock9" ∈ bd.term.targets)).map (·.name) = ["NodeBlock13"] ∧
      (stage2NoEventBody.blocks.filter
        (fun bd => "NodeBlock13" ∈ bd.term.targets)).map (·.name) = ["NodeBlock15"] := by
  decide

/-! ### The loop's internal continuation, at the latch's entry

The entry's own read (`if.end327`'s lane word and byte) is the block's
computation; `if.end`'s six `phi`s and four adds are
`ifEndProduce_fromEnd327`'s.  The two links compose to two steps, and the
dispatch's seven cells are the entry's readings and the counts the header
advanced. -/

/-- **The counted loop's iteration transition, from the latch's entry.**  The
state is at `if.end327`'s entry (the `[` push's target), the entry at `%inc` is not
`]`, and `ifEndProduce_fromEnd327` -- the second half of `ifEnd327_produce`, whose
entry read is this theorem's own first link -- hands back `NodeBlock15` with
`%7`/`%8` the entry's byte and lane, `%k.0 = %inc` the dispatched cursor, `%inc`
advanced by one, and the two counts advanced by the opener (`+1` token, `+3`
terms).  The run is two blocks, so this composes with the
`NodeBlock15`-to-entry route as an iteration.  The state's predecessor is not
read (the block has no `phi`), so the statement pins only the latch's own
readings. -/
theorem stage2NoEventWalkCountedContinue {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {s : State}
    {inc : BitVec 64} {iv tok tr : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end327")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some bs1)
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (htr : lookupName s.env "%terms.0" = some (.int 64 tr))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 93) = 0) :
    ∃ s', Stage2NoEventWalkSegment calls mem K s K s' 2 ∧
      s'.pc = "NodeBlock15" ∧
      lookupName s'.env "%7" = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ∧
      lookupName s'.env "%8" = some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ∧
      lookupName s'.env "%indvars.iv" = some (.int 64 (iv + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%k.0" = some (.int 64 inc) ∧
      lookupName s'.env "%terms.0" = some (.int 64 (tr + BitVec.ofNat 64 3)) ∧
      lookupName s'.env "%tokens.0" = some (.int 64 (tok + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%inc" = some (.int 64 (inc + BitVec.ofNat 64 1)) := by
  classical
  let sM := stage2NoEventWalkNext
    (("%cmp332", .int 1 0) ::
      ("%47", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
      ("%arrayidx330",
        .ptr (b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%46", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328", .ptr (ep + inc.toNat * 4)) :: s.env) s "if.end"
  have L1 : Stage2NoEventWalkLink calls K mem s K sM :=
    link_ifEnd327_false h hpc hinc hep hb hincLt hlane hlanelt hbyte hbit
  have c47 : lookupName sM.env "%47" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [sM, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have c46 : lookupName sM.env "%46" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [sM, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have cIV : lookupName sM.env "%indvars.iv" = some (.int 64 iv) := by
    simp only [sM, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hiv
  have cInc : lookupName sM.env "%inc" = some (.int 64 inc) := by
    simp only [sM, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have cTr : lookupName sM.env "%terms.0" = some (.int 64 tr) := by
    simp only [sM, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have cTok : lookupName sM.env "%tokens.0" = some (.int 64 tok) := by
    simp only [sM, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  obtain ⟨s', L2, hpc', c7, c8, cIV', cK0, cTr', cTok', cInc'⟩ :=
    ifEndProduce_fromEnd327 (calls := calls) L1.inv' rfl
      (by simp only [sM, stage2NoEventWalkNext, hpc])
      c47 c46 cIV cInc cTr cTok
  refine ⟨s', ⟨fun n => ?_, L2.inv'⟩, hpc', c7, c8, cIV', cK0, cTr', cTok', cInc'⟩
  rw [show 2 + n = 1 + (1 + n) from by omega,
    stage2NoEventWalkLink_runFuel L1 (1 + n),
    stage2NoEventWalkLink_runFuel L2 n]

/-! ### The re-entry from an element's endpoint

The endpoint is the class lane's `after_value` state, the shared cycle's source.
The cycle reaches the next head at index `k + 1`, and the additive
`stage2NoEventWalkCycle_of_afterValue_sp` pins that head's `%sp.0.ph1403` at the
endpoint's `sp`.  The endpoint's `spLt`/`spNe` and the route's `sp ≤ 519` are the
pinned staging `Stage2NoEventWalkDescendBranch` carries, so the committed
descend step runs from that head. -/

/-- **The counted-loop iteration's dispatch from an element's endpoint.**  From a
class lane's `after_value` endpoint at index `k`, with the next entry (`k + 1`)
the array opener, the endpoint at a live depth (`1 ≤ sp ≤ 519`), and a further
entry (`k + 2`) that is not `]`, the shared cycle reaches the next head, the
head's dispatch pushes and reads, and the walk stands at `NodeBlock15`
dispatching the entry at `k + 2`: `%7`/`%8` its byte and lane, `%k.0 = k + 2`,
`%inc = k + 3`, the counts advanced by the opener.

The premises, labelled: `src` is the endpoint (the class route's own output,
carrying `sp ≠ 0` and `sp < 2^32`); `hspLe` is the push's room, `sp ≤ 519`;
`hkO`/`hbsO`/`hbO` are the opener at `k + 1` (the document's byte — not a
consequence of `Head`); `hk1`/`hbs1`/`hne` are the entry at `k + 2`; `hlive` is
the stream's room past that entry (`k + 4 < nep`), which is the descend's own
`live` at the head's index.  The cycle's credit is carried, `p + Φ(k+1) ≤ Φ k`. -/
theorem stage2NoEventWalkCountedReentry {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {sE : State}
    (src : Stage2NoEventWalkCycleSrc calls mem K k sE)
    (hspLe : src.sp ≤ 519)
    {lane : Nat} {byte : UInt8}
    (hkO : K.ent[k + 1]? = some lane) (hbsO : K.bs[lane]? = some byte)
    (hbO : byte.toNat = 91)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 2]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hlive : k + 4 < K.nep) :
    ∃ (s1 : State) (p j : Nat),
      Stage2NoEventWalkSegment calls mem K sE K s1 (p + j) ∧
      Stage2NoEventWalkBracketDispatch K (k + 1) s1 next nextByte ∧
      p + stage2NoEventWalkPotential K (k + 1) ≤ stage2NoEventWalkPotential K k := by
  classical
  obtain ⟨sH, p, hcyc, hspH⟩ := stage2NoEventWalkCycle_of_afterValue_sp src
  have hhead : Stage2NoEventWalkHead K mem (k + 1) sH := hcyc.headPriced.seg.head'
  have hclass : Stage2NoEventWalkHeadBracketClass K (k + 1) sH := by
    obtain ⟨hread, h3⟩ := stage2NoEventWalkHeadStagingAt hhead hkO hbsO
    exact ⟨lane, byte, hkO, hbsO, hread, h3, hbO⟩
  -- the descend's staging: the pinned depth is the endpoint's own
  have hbr : Stage2NoEventWalkDescendBranch K (k + 1) sH :=
    { spH := ⟨src.sp, hspH, src.spLt, src.spNe, hspLe⟩
      live := by omega }
  obtain ⟨s1, hchain, hdisp⟩ :=
    stage2NoEventWalkBracketDescendStep hhead hclass hbr hk1 hbs1 hne
  obtain ⟨j, hseg⟩ := Stage2NoEventWalkSegment.of_chain hchain
  exact ⟨s1, p, j, hcyc.headPriced.seg.seg.trans hseg, hdisp, hcyc.headPriced.credit⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventBody_countedPreds
#print axioms stage2NoEventWalkCountedContinue
#print axioms stage2NoEventWalkCountedReentry

end LeanLLVM.Refinement
