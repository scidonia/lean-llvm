/-
The no-event walk's container rows, discharged where the tree's producers exist.

`JsonStage2NoEventWalkRowsReady` splits a bracket or brace head's row by the byte
at `k + 1` into three arms and states one premise per arm.  This module replaces
two of the bracket arms' premises with producers and states the brace class's
`}` route to a head, then re-states the assembly at the reduced premises.

**The bracket descend arm** (`[` head, next byte not `]`).  The head's step to
the continuation dispatch `NodeBlock15` is
`JsonStage2NoEventWalkRowsDescend`'s `stage2NoEventWalkBracketDescendStep`; the
`[` leaf's window, the recursion and the producers are
`JsonStage2NoEventWalkBracketInner`'s (`Stage2NoEventWalkBracketInnerWindow`,
`Stage2NoEventWalkBracketInnerAll`, `stage2NoEventWalkBracketInnerOutCloser`/
`…OutElement`).  The descend row is
`JsonStage2NoEventWalkRowsDescend`'s `…BracketDescendRow_of_inner`, whose inner
obligation `Stage2NoEventWalkBracketInner` is inhabited by the recursion at the
window: for a dispatch state `s1` and prefix count `j0`,
`BracketInnerAll` gives the inner bundle from the window.  What the caller
supplies is the head, its class, the descend staging, the entry at `k + 1` and
its byte, the window at every dispatch state, and the recursion; what is derived
is the row, with the head's own segment and the composed price.

**The bracket closer arm at the comma continuation** (`[` head, next byte `]`).
When the entry at `k + 2` is a comma — `Stage2NoEventWalkPairBranch.comma`, the
separator the shared cycle reads — the committed empty-pair producer
`stage2NoEventWalkBracketRow_of_head` applies: it derives the closer's read, the
post-push entry and document reads, and the pop from `Head`, and needs only the
pair branch's staging and the closer byte.  The complement, an empty pair that
is the last element of its parent, is the parent-closer shape of
`JsonStage2NoEventWalkRowsParentCloser` and is named here, not produced.

**The brace class's `}` route**.  `stage2NoEventWalkBraceFrameZeroCloserRow`
states the `}` class as the frame-zero pair route
(`stage2NoEventWalkBracePairLegFrameZero`'s segment at the pair's carry), the
`}` arm at the pair's endpoint (`stage2NoEventWalkBraceFrameZeroCloseDeep`), the
bridge to a head (`stage2NoEventWalkBraceFrameZeroCloseToHead`) and the row's
`cont`.  The caller's remaining facts are the endpoint entry's frame word and
depth and the comma at `k + 3`, exactly as `JsonStage2NoEventWalkBraceFrameZeroCycle`
states them, beside the arm's own pop staging and index bounds.

**The consequence**.  `stage2NoEventWalkBracketReady_of_discharged` rebuilds
`Stage2NoEventWalkBracketReady` from the closer arm off the comma shape, the
descend supply and the trailing exit; `stage2NoEventWalkRows_assembled_discharged`
re-states the assembly at that producer, with the brace class's three arms and
the string and value producers unchanged.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsAssembled
import LeanLLVM.Refinement.JsonStage2NoEventWalkBracketInner
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsParentCloser
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceFrameZeroCycle

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The bracket descend arm

The head's step to the continuation dispatch is
`JsonStage2NoEventWalkRowsDescend`'s `stage2NoEventWalkBracketDescendStep`; the
inner obligation is `Stage2NoEventWalkBracketInner`, and
`JsonStage2NoEventWalkBracketInner`'s recursion `Stage2NoEventWalkBracketInnerAll`
discharges it at the window.  The two are bridged here. -/

/-- **The bracket descend arm as a row, from the recursion at the window.**  The
committed `stage2NoEventWalkBracketDescendRow_of_inner` reduces the arm to
`Stage2NoEventWalkBracketInner`; the recursion `BracketInnerAll` at the dispatch's
window is that obligation: for every prefix count `j0` and dispatch state `s1`
reached by the head's segment, the pre-supplied window gives the inner bundle.
The caller supplies the window (at every dispatch state, see the field's
docstring) and the recursion; the row is derived.  Coverage note: the window's
`byte91` pins the entry's byte, so this arm is produced where the next entry opens
an **array**; the other opener bytes are not covered here. -/
noncomputable def stage2NoEventWalkBracketDescendRow_of_windowAll
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry}
    {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkDescendBranch K k s)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hwindow : ∀ s1 : State, Stage2NoEventWalkBracketDispatch K k s1 next nextByte →
      Stage2NoEventWalkBracketInnerWindow K mem k s1 next nextByte)
    (hinner : Stage2NoEventWalkBracketInnerAll calls mem K k next nextByte) :
    Stage2NoEventWalkRow calls mem F K k s :=
  stage2NoEventWalkBracketDescendRow_of_inner h hclass hbranch hk1 hbs1 hne
    (fun j0 s1 hdisp _ => hinner s1 (hwindow s1 hdisp) j0)

/-- **The descend arm's supplies**, per head: the route's own staging
(`Stage2NoEventWalkDescendBranch`), the continuation dispatch's window, and the
recursion `Stage2NoEventWalkBracketInnerAll`.  The window and the recursion are
the caller's — the tree's class producers are rooted at `NodeBlock5` heads, and
the inner leaves are the dispatch's `.loopexit` chains. -/
structure Stage2NoEventWalkBracketDescendSupply (calls : Calls) (mem : Mem) where
  /-- The descend's own staging: the pinned depth (its cell, width and the
  push's two bounds) and the stream's room. -/
  branch : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (next : Nat)
      (nextByte : UInt8),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadBracketClass K k s →
    K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte →
    nextByte.toNat ≠ 93 →
    Stage2NoEventWalkDescendBranch K k s
  /-- The `[` leaf's window at **every** state at the dispatch, not only the one
  the head's own segment reaches: `BracketInner`'s obligation takes the reached
  state's segment as a premise, and this supply drops it, so it is strictly
  stronger than the committed obligation — a caller that can establish the
  window only along the reached path cannot use this field. -/
  window : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (next : Nat)
      (nextByte : UInt8),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadBracketClass K k s →
    K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte →
    nextByte.toNat ≠ 93 →
    ∀ s1 : State, Stage2NoEventWalkBracketDispatch K k s1 next nextByte →
      Stage2NoEventWalkBracketInnerWindow K mem k s1 next nextByte
  /-- The recursion: the inner bundle at the window, at every count. -/
  inner : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (next : Nat)
      (nextByte : UInt8),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadBracketClass K k s →
    K.ent[k + 1]? = some next →
    K.bs[next]? = some nextByte →
    nextByte.toNat ≠ 93 →
    Stage2NoEventWalkBracketInnerAll calls mem K k next nextByte

/-! ### The bracket closer arm on the comma continuation

The empty pair's committed producer (`JsonStage2NoEventWalkRowsReady`'s
`stage2NoEventWalkBracketRow_of_head`) is the row at a closer byte, given the
pair branch's staging (`Stage2NoEventWalkPairBranch`).  Its separator field asks
the entry at `k + 2` to be a comma — the shape named here.  The producer below is
that row at one `Stage2NoEventWalkPairBranch` (the five facts survive inside
it), so the closer arm's `hcloser` premise is
inhabited on the comma continuation.  The complement (the entry at `k + 2` is a
parent's `]`/`}`) is `JsonStage2NoEventWalkRowsParentCloser`'s
`Stage2NoEventWalkParentSep` shape and is not produced here. -/

/-- **The bracket closer arm's row on the comma continuation.**  The pair branch's
staging is its own argument now (the pinned depth, the frame's non-zero, the
separator at `k + 2`, the next head's liveness); the closer's byte `93` is the
arm's own.  Every other argument of the committed empty-pair row is derived from
`Head`. -/
noncomputable def stage2NoEventWalkBracketCloserRow_of_comma
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry}
    {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hcl : nextByte.toNat = 93)
    (hg : Stage2NoEventWalkPairBranch K k s) :
    Stage2NoEventWalkRow calls mem F K k s :=
  stage2NoEventWalkBracketRow_of_head h htrace hclass hg
    (fun n b hn hb => by
      have hn' : n = next := by
        rw [hk1] at hn
        exact (Option.some.inj hn).symm
      subst hn'
      have hb' : b = nextByte := by
        rw [hbs1] at hb
        exact (Option.some.inj hb).symm
      rw [hb']
      exact hcl)

/-! ### The brace class's `}` route

The frame-zero pair route (`JsonStage2NoEventWalkBraceFrameZeroPair`'s
`stage2NoEventWalkBracePairLegFrameZero`) ends at a
`Stage2NoEventWalkFrameZeroSrc` at `k + 2`; the `}` arm
(`stage2NoEventWalkFrameZeroBraceDeep`, nine blocks) closes the enclosing object
at the entry `}` there, and `JsonStage2NoEventWalkBraceFrameZeroCycle`'s
`stage2NoEventWalkBraceFrameZeroCloseToHead` turns the endpoint into the head at
`k + 4`.  The row's `cont` is that head segment. -/

/-- **The `}` class's row at a frame-zero pair head.**  The pair route's segment
(at the brace pair's carry, thirteen blocks) and its frame-zero endpoint source,
the entry at `k + 2` reading `}` (`125`), the pull's staging, and the three-entry
price bound; then the arm's endpoint at `k + 3` with the words the arm's
conclusion hides — the popped enclosing tag as the frame (non-zero) and the
decremented depth (non-zero) — and the comma that continues the walk.  The
route's last leg is `stage2NoEventWalkBraceFrameZeroCloseToHead`, and the row is
`Stage2NoEventWalkRow.cont` to the head at `k + 4`.  The endpoint's frame, depth
and comma remain the caller's post, as `JsonStage2NoEventWalkBraceFrameZeroCycle`
states; the top-level close (`sp = 1`) is the terminal lane's and is not this
route. -/
noncomputable def stage2NoEventWalkBraceFrameZeroCloserRow
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry}
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
    (hjl : jl + 9 ≤ 96)
    (hk3 : k + 3 < K.nep)
    (hkAddr : k + 4 < 2 ^ 63)
    (hklt : k + 4 < K.nep)
    (hpost : ∀ (s'' : State),
      (e : Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
        (k + 3) s'') → e.frame ≠ 0 ∧ e.sp ≠ 0)
    (hcomma : ∀ lane,
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).ent[k + 3]? =
        some lane →
      (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K)).bs.getD lane 0
        = 44) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨s'', hseg, hent⟩ :=
    stage2NoEventWalkBraceFrameZeroCloseDeep hleg hsrc hspTwo hk2 hbs2 hbyte2
      hpop hpopAddr hbsLen
  obtain ⟨e⟩ := hent
  obtain ⟨hframeNe, hspNe⟩ := hpost s'' e
  obtain ⟨s', p, hp⟩ :=
    stage2NoEventWalkBraceFrameZeroCloseToHead h
      (by omega) hk3 hseg e hframeNe hspNe hkAddr
      (by simpa only [stage2NoEventWalkCloseBraceCarry,
        stage2NoEventWalkBracePairCarry] using hklt) hcomma
  exact ⟨Stage2NoEventWalkRow.cont
    (stage2NoEventWalkCloseBraceCarry (stage2NoEventWalkBracePairCarry K))
    (k + 4) s' (jl + 9 + p) hp rfl rfl rfl (by omega) hklt⟩

/-! ### The consequence: the bracket class's producer, and the assembly

`stage2NoEventWalkBracketReady_of_routes` takes the closer arm, the descend arm
and the trailing exit.  The descend arm is now the producer above, from its
supply; the closer arm is the comma producer plus a named remainder off that
shape; the trailing exit is unchanged.  The assembly then carries the bracket
producer's new premises in place of the two arms it discharged. -/

/-- **The bracket class's producer at the discharged arms.**  The closer arm is
produced on the comma continuation (`stage2NoEventWalkPairBranch`, whose
`comma` field is the entry at `k + 2` reading `,`) and is the caller's elsewhere
(`hcloserOther` — e.g. the parent-closer shape); the descend arm is
`Stage2NoEventWalkBracketDescendSupply`'s row; the trailing exit is
`htrail`. -/
noncomputable def stage2NoEventWalkBracketReady_of_discharged {calls : Calls}
    {mem : Mem} {F : Nat}
    (hcloserOther : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      ¬ Stage2NoEventWalkPairBranch K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (D : Stage2NoEventWalkBracketDescendSupply calls mem)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkBracketReady calls mem F :=
  fun K k s h htrace hclass => by
    classical
    apply Classical.choice
    obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, hfrLt⟩ := h.spPhiBounded
    by_cases hk2 : K.nep ≤ k + 3
    · exact ⟨htrail K k s sp h htrace hclass hspH hk2⟩
    · have hk2le : k + 2 ≤ K.nep := by omega
      obtain ⟨next, hk1⟩ := h.entSucc hk2le
      have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
      obtain ⟨nextByte, hbs1⟩ := h.inv.docGetElem? hnextLt
      by_cases hcl : nextByte.toNat = 93
      · by_cases hg : Stage2NoEventWalkPairBranch K k s
        · exact ⟨stage2NoEventWalkBracketCloserRow_of_comma h htrace hclass
            hk1 hbs1 hcl hg⟩
        · exact ⟨hcloserOther K k s sp next nextByte h htrace hclass hspH
            hk1 hbs1 hcl hg⟩
      · exact ⟨stage2NoEventWalkBracketDescendRow_of_windowAll h hclass
          (D.branch K k s next nextByte h htrace hclass hk1 hbs1 hcl)
          hk1 hbs1 hcl
          (D.window K k s next nextByte h htrace hclass hk1 hbs1 hcl)
          (D.inner K k s next nextByte h htrace hclass hk1 hbs1 hcl)⟩

/-- **The walk's rows at `stage2GapRecover` and fuel 27, at the reduced bracket
premises.**  This is `JsonStage2NoEventWalkRowsAssembled`'s
`stage2NoEventWalkRows_assembled` with the bracket class's `hcloser`/`hdescend`
replaced by `hcloserOther` and the descend supply `D`; the comma continuation is
consumed by the producer, and the brace, string and value producers are the
assembly's own. -/
noncomputable def stage2NoEventWalkRows_assembled_discharged {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hcloserOther : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      ¬ Stage2NoEventWalkPairBranch K k s →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (D : Stage2NoEventWalkBracketDescendSupply
      (stage2NoEventCalls stage2GapRecover) mem)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkRows_of_ready hstring
    (stage2NoEventWalkBracketReady_of_discharged hcloserOther D htrail)
    (stage2NoEventWalkBraceReady_of_routes hbraceCloser hbraceDescend hbraceTrail)
    hvalue

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracketDescendRow_of_windowAll
#print axioms Stage2NoEventWalkBracketDescendSupply
#print axioms stage2NoEventWalkBracketCloserRow_of_comma
#print axioms stage2NoEventWalkBraceFrameZeroCloserRow
#print axioms stage2NoEventWalkBracketReady_of_discharged
#print axioms stage2NoEventWalkRows_assembled_discharged

end LeanLLVM.Refinement
