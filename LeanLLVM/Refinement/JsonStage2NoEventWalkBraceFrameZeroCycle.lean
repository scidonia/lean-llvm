/-
The no-event walk at a frame-zero `after_value` entry: the close-brace
continuation and where it stops.

`JsonStage2NoEventWalkBraceFrameZeroPair` reaches `after_value`'s entry at a
frame-zero head and runs the `}` arm to the *next* `after_value` entry.  Its
header names the gap that leaves: the after-value cycle source
(`Stage2NoEventWalkCycleSrc`, and `stage2NoEventWalkCycle_of_afterValue` that
consumes it) demands a frame word that is non-zero — the object-member pair's
source (`…CyclePairSrc`/`cycle_of_pair`) is a different source and carries no
frame word at all — so the `}` class had no `Row.cont`.  This module states what
the frame-zero entry actually steps to, at the delta and the carry the arm's
registers give, supplies the bridge the committed cycle needs at the endpoint,
and names the two words the arm's conclusion does not expose.

**The step.**  From an `after_value` entry whose `%frame.6` is zero, the walk
takes `after_value`'s non-terminal edge (`%cmp355`, `%sp.4 ≠ 0`) and `if.end369`'s
live edge to `if.end378`, where the frame test reads one and turns *into* the
byte dispatch at `if.then384` — that is `ifEnd378_denote_frameZero`, the same
block `ifEnd378_denote_cmp` states at an arbitrary test word.  From there the
`}` arm is `JsonStage2NoEventWalkCycleFrameZero`'s:

* `stage2NoEventWalkFrameZeroBraceTop` (eight blocks) at `%sp.4 = 1`, whose
  `close_obj` arm reaches `after_value` at depth zero with frame zero;
* `stage2NoEventWalkFrameZeroBraceDeep` (nine blocks) at `2 ≤ %sp.4`, whose
  `if.then343` arm pops the enclosing tag and reaches `after_value` one depth
  lower with that byte as the frame word.

Both land at the next `after_value` entry at `k + 1`, at
`stage2NoEventWalkCloseBraceCarry`, i.e. one token and two terms heavier: the
`do.body391` pair `%inc392 = %tokens.8 + 1` and `%add393 = %terms.8 + 2`.  (The
thirteen-block pair leg's `%add85` adds *three* terms; that is the pair's count,
not this arm's.)  So the continuation is one entry's worth: delta one, one token,
two terms, and it is priced at one entry's allowance (`32 * 1 = 32`), of which
the arm's eight or nine blocks consume the smaller part.

**What is not in this tree.**  The step does not reach a `NodeBlock5` head, so it
is not a `Stage2NoEventWalkCycle`.  The block on the head route is `if.end378`:
`ifEnd378_denote_cmp` is committed and general, but its instantiation at
`%cmp382 = 0` — the `if.end410` edge, `NodeBlock41` → `LeafBlock37` →
`value.outer.backedge` — requires a non-zero frame word (`ifEnd378_denote`
accordingly takes `hfrNe : fr ≠ 0`), and at `fr = 0` the same block yields
`%cmp382 = 1` and branches to `if.then384`.  The tree therefore has no frame-zero
cycle source, and the `}` class's continuation is the entry above, not a head.

**What closes that gap where it can be closed.**  The pair route's `}` class is
the brace-carried composition, not the bracket's: `…BraceFrameZeroCloseDeep` (or
`…CloseTop`) is the thirteen-block pair leg and the close as one segment to
`after_value(k + 3)` at `stage2NoEventWalkCloseBraceCarry
(stage2NoEventWalkBracePairCarry K)` — the brace pair's `tok + 2, terms + 3` and
the close's `+1, +2`, not `stage2NoEventWalkPairCarry`'s seven terms — and
`…BraceFrameZeroPairClosePrice` prices it at three entries' allowance (`96`).
From that endpoint the committed cycle applies whenever the entry's frame word is
non-zero: `stage2NoEventWalkCycleSrc_of_afterValueEntry` below is the bridge, and
`stage2NoEventWalkBraceFrameZeroCloseToHead` composes it to the head at `k + 4`.

The two words the bridge needs are the caller's.  The endpoint's frame word is
the popped enclosing tag (`bytesToNat bs` in the deep case) and its depth is the
decremented source depth; the committed arm's conclusion
`Nonempty (AfterValueEntry …)` hides both, so neither "non-zero" is readable off
its witness.  The bridge therefore takes them, with the index bounds and the
next entry's comma, as the caller's post — the shape
`JsonStage2NoEventWalkRowsParentCloser` gives its closer source.  At the top
level the endpoint is depth zero and frame zero, so the bridge does not apply
there at all; that route is the terminal lane's.

Every block this module uses is an existing denotation
(`stage2NoEventWalkFrameZeroBraceTop`, `…BraceDeep`,
`stage2NoEventWalkFrameZeroSrc_of_afterValueEntry`,
`stage2NoEventWalkCycle_of_afterValue`, `stage2NoEventWalkPotential_add`,
`stage2NoEventWalkBraceFrameZeroCloseDeep`, `…BraceFrameZeroPairClosePrice`); the
frame-zero step's *source* (an `AfterValueEntry` instead of the bundled
`FrameZeroSrc`), its price, the bridge and the composition are proved here.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceFrameZeroPair

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

/-! ### The bridge the committed cycle needs at a non-zero endpoint

`Stage2NoEventWalkCycleSrc` is the cycle's source.  The committed frame-zero
constructor is `stage2NoEventWalkFrameZeroSrc_of_afterValueEntry`: an
`after_value` entry whose frame word is zero, given the depth's non-zero and the
index bounds, is a frame-zero source.  The complementary case is this one — the
same entry at a non-zero frame word is the committed cycle's source.  Nothing in
the entry changes; only the frame test's direction does. -/

/-- **An `after_value` entry at a non-zero frame word is a cycle source**, given
the depth's non-zero, the next index's address and existence bounds, and the
comma that continues the walk at the entry.  This is the bridge a closer arm's
endpoint needs.  It differs from the committed `FrameZeroSrc` constructor
(`stage2NoEventWalkFrameZeroSrc_of_afterValueEntry`) in three places: `frameNe`
in place of `frameZero`, `k + 1 < K.nep` in place of the source's `k < K.nep`,
and the `comma` field, which the cycle's after-value path reads at its own entry
and which the frame-zero source leaves to the `}` arm. -/
def stage2NoEventWalkCycleSrc_of_afterValueEntry {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K k s)
    (hframeNe : h.frame ≠ 0) (hspNe : h.sp ≠ 0)
    (hkAddr : k + 1 < 2 ^ 63) (hklt : k + 1 < K.nep)
    (hcomma : ∀ lane, K.ent[k]? = some lane → K.bs.getD lane 0 = 44) :
    Stage2NoEventWalkCycleSrc calls mem K k s :=
  { inv := h.inv, pc := h.pc, frame := h.frame, frameLt := h.frameLt,
    frameNe := hframeNe, sp := h.sp, spLt := h.spLt, spNe := hspNe,
    kAddr := hkAddr, klt := hklt, count := h.count, phiRun := h.phiRun,
    baseLookups := h.baseLookups, bPos := h.bPos, trace := h.trace, comma := hcomma }

/-! ### The frame-zero continuation, at the arm's own blocks

The source is the entry itself, not the bundled `FrameZeroSrc`: the frame word is
zero, the depth is non-zero, and the index bounds are the caller's.  The step is
the committed `}` arm, so its count is the arm's and its carry is the arm's. -/

/-- **The frame-zero `}` step at the top level** (`%sp.4 = 1`): eight blocks from
the entry at `k` to the next `after_value` entry at `k + 1`, at the close-brace
carry, priced at one entry's allowance (`8 ≤ 32`). -/
theorem stage2NoEventWalkFrameZeroBraceStepTop {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K k s)
    (hframe : h.frame = 0) (hspNe : h.sp ≠ 0)
    (hkAddr : k + 1 < 2 ^ 63) (hklt : k < K.nep) (hknext : k + 1 < K.nep)
    (hspOne : h.sp = 1)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125) :
    ∃ s' : State,
      Stage2NoEventWalkPricedSegment calls mem K k s
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s' 8 ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s') := by
  let hsrc : Stage2NoEventWalkFrameZeroSrc calls mem K k s :=
    stage2NoEventWalkFrameZeroSrc_of_afterValueEntry h hframe hspNe hkAddr hklt
  obtain ⟨s', hseg, hent⟩ :=
    stage2NoEventWalkFrameZeroBraceTop hsrc hspOne hk hbs hbyte
  refine ⟨s', ⟨hseg, ?_⟩, hent⟩
  -- one entry's allowance pays the arm's eight blocks
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 1) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 1)
    (Nat.le_of_lt hknext) hentle
  have h32 : 32 * 1 = 32 := by decide
  rw [h32] at hadd
  have hpot : stage2NoEventWalkPotential (stage2NoEventWalkCloseBraceCarry K) (k + 1) =
      stage2NoEventWalkPotential K (k + 1) := rfl
  rw [hpot]
  omega

/-- **The frame-zero `}` step at a nested depth** (`2 ≤ %sp.4`): nine blocks,
the `if.then343` pop included, from the entry at `k` to the next one at `k + 1`,
at the close-brace carry, priced at one entry's allowance (`9 ≤ 32`).  The pop's
read is the caller's fact at this state's memory, as it is for the committed
arm. -/
theorem stage2NoEventWalkFrameZeroBraceStepDeep {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K k s)
    (hframe : h.frame = 0) (hspNe : h.sp ≠ 0)
    (hkAddr : k + 1 < 2 ^ 63) (hklt : k < K.nep) (hknext : k + 1 < K.nep)
    (hspTwo : 2 ≤ h.sp)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125)
    {a : Nat} {bs : List UInt8}
    (hpop : readBytes s.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr K.stk
      (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1) :
    ∃ s' : State,
      Stage2NoEventWalkPricedSegment calls mem K k s
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s' 9 ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s') := by
  let hsrc : Stage2NoEventWalkFrameZeroSrc calls mem K k s :=
    stage2NoEventWalkFrameZeroSrc_of_afterValueEntry h hframe hspNe hkAddr hklt
  obtain ⟨s', hseg, hent⟩ :=
    stage2NoEventWalkFrameZeroBraceDeep hsrc hspTwo hk hbs hbyte hpop hpopAddr hbsLen
  refine ⟨s', ⟨hseg, ?_⟩, hent⟩
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 1) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 1)
    (Nat.le_of_lt hknext) hentle
  have h32 : 32 * 1 = 32 := by decide
  rw [h32] at hadd
  have hpot : stage2NoEventWalkPotential (stage2NoEventWalkCloseBraceCarry K) (k + 1) =
      stage2NoEventWalkPotential K (k + 1) := rfl
  rw [hpot]
  omega

/-! ### The continuation to a head, when the enclosing tag is non-zero

A priced step leaves an `after_value` entry at some index `kk`.  When that
entry's frame word is non-zero — the enclosing container is array-like — the
committed cycle applies there, and the composition is a head segment from the
step's source to the head at `kk + 1`.  The frame-zero close reaches the head at
`kk + 1` from `kk = k + 1`; the brace pair's route reaches it from
`kk = k + 3`, the same shape over its longer segment. -/

/-- **A priced step and the committed cycle compose to a head.**  This is the
brace-carried `}` composition's last leg: the step is
`…BraceFrameZeroCloseDeep`'s (or `…CloseTop`'s) segment at `kk = k + 3`, and the
endpoint is its `after_value` entry with the two words the arm does not expose —
the popped enclosing tag as the frame, the decremented depth — supplied by the
caller beside the index bounds and the entry's comma.  The bridge turns the entry
into the committed cycle's source, and the target is the head at `kk + 1`.  The
price is the step's plus the cycle's own (`jl + p`). -/
theorem stage2NoEventWalkAfterValueToHead {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    {Kc : Stage2NoEventWalkCarry} {kk : Nat} {sE : State} {jl : Nat}
    (hstep : Stage2NoEventWalkPricedSegment calls mem K k s Kc kk sE jl)
    (hentry : Stage2NoEventWalkAfterValueEntry calls mem Kc kk sE)
    (hframeNe : hentry.frame ≠ 0) (hspNe : hentry.sp ≠ 0)
    (hkAddr : kk + 1 < 2 ^ 63) (hklt : kk + 1 < Kc.nep)
    (hcomma : ∀ lane, Kc.ent[kk]? = some lane → Kc.bs.getD lane 0 = 44) :
    ∃ (s' : State) (p : Nat),
      Stage2NoEventWalkHeadPricedSegment calls mem K k s Kc (kk + 1) s' (jl + p) := by
  have hsrc : Stage2NoEventWalkCycleSrc calls mem Kc kk sE :=
    stage2NoEventWalkCycleSrc_of_afterValueEntry hentry hframeNe hspNe hkAddr hklt
      hcomma
  obtain ⟨s', p, hcyc⟩ := stage2NoEventWalkCycle_of_afterValue hsrc
  have hp := hcyc.headPriced
  refine ⟨s', p, ⟨⟨hstep.seg.trans hp.seg.seg, hp.seg.head', hp.seg.trace'⟩, ?_⟩⟩
  have h1 := hstep.credit
  have h2 := hp.credit
  omega

/-! ### The pair route's `}` class, to a head

`JsonStage2NoEventWalkBraceFrameZeroPair`'s close is the brace-carried segment —
the thirteen-block pair leg and the `}` arm as one — and its price is three
entries' allowance.  At that endpoint this module's bridge and the committed
cycle finish the route. -/

/-- **The pair route's `}` class reaches a head**: the close segment at the brace
pair's carry (`…BraceFrameZeroCloseDeep`'s twenty-two blocks, or `…CloseTop`'s
twenty-one), priced by `…BraceFrameZeroPairClosePrice`'s three-entry allowance
(`jl ≤ 96`), then the committed cycle at the endpoint's non-zero frame word.  The
endpoint entry's frame word (the popped enclosing tag) and depth are the
caller's, as the arm's statement hides them. -/
theorem stage2NoEventWalkBraceFrameZeroCloseToHead {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State} {jl : Nat}
    (h : Stage2NoEventWalkHead K mem k s) (hjl : jl ≤ 96) (hk3 : k + 3 < K.nep)
    (hclose : Stage2NoEventWalkSegment calls mem K s
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) sE jl)
    (hentry : Stage2NoEventWalkAfterValueEntry calls mem
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)) (k + 3) sE)
    (hframeNe : hentry.frame ≠ 0) (hspNe : hentry.sp ≠ 0)
    (hkAddr : k + 4 < 2 ^ 63)
    (hklt : k + 4 < (stage2NoEventWalkCloseBraceCarry
      (stage2NoEventWalkBracePairCarry K)).nep)
    (hcomma : ∀ lane,
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).ent[k + 3]? =
        some lane →
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).bs.getD lane 0
        = 44) :
    ∃ (s' : State) (p : Nat),
      Stage2NoEventWalkHeadPricedSegment calls mem K k s
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 4) s' (jl + p) := by
  have hprice := stage2NoEventWalkBraceFrameZeroPairClosePrice (mem := mem) h hjl hk3
  exact stage2NoEventWalkAfterValueToHead (kk := k + 3) ⟨hclose, hprice⟩ hentry
    hframeNe hspNe hkAddr hklt hcomma

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkCycleSrc_of_afterValueEntry
#print axioms stage2NoEventWalkFrameZeroBraceStepTop
#print axioms stage2NoEventWalkFrameZeroBraceStepDeep
#print axioms stage2NoEventWalkAfterValueToHead
#print axioms stage2NoEventWalkBraceFrameZeroCloseToHead

end LeanLLVM.Refinement
