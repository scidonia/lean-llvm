/-
The no-event walk's `[]` pair at the shape where its endpoint's separator is the
parent's `]`, and the parent's closer arm that follows it.

`JsonStage2NoEventWalkRowsContainerB`'s `stage2NoEventWalkBracketPairLeg` states
the empty array's eleven-block route only together with
`hcomma : ∀ q, K.ent[k+2]? = some q → K.bs.getD q 0 = 44`: its endpoint is a
`Stage2NoEventWalkCycleSrc`, whose `comma` field is that byte.  The route's own
blocks read the entry at `k + 1` (the pair's `]`) and the popped stack byte;
none of them reads the entry at `k + 2`.  So the same eleven blocks prove the
same route where the entry at `k + 2` is the *parent's* closer, whose document
byte is `]` (`93`) — `JsonStage2NoEventWalkRowsParentCloser`'s
`Stage2NoEventWalkParentSep K k 93`, under which `Stage2NoEventWalkPairBranch`
is refuted outright.  What the endpoint then is, is an `after_value` entry with
no separator read: `stage2NoEventWalkBracketPairAfterValue` below, at the pair's
carry (`tok + 2`, `terms + 7`), exposing the memory the push left and the
entry's frame and depth (`fr`, `sp`).

The entry's dispatch then runs the parent's closer, and the byte decides the
arm.  At a **non-zero** frame word `if.end378`'s test is zero and the walk takes
`if.end410` → `NodeBlock41`, whose `%53 slt 93` is false at `]`; `LeafBlock39`'s
`%53 eq 93` is true, so `do.body417` stores the close-array counts
(`%inc418 = %tokens.8 + 1`, `%add419 = %terms.8 + 4`) and the decremented depth
(`%54 = %sp.4 - 1`), and `close_arr` hands either straight to `after_value` at
depth zero (`%sp.3 = 0`) or through `%sp.3 ≠ 0` to `if.then350`, which pops the
enclosing container's tag.  That is

* `stage2NoEventWalkParentSepArmTop` — eight blocks, `%sp.4 = 1`, ending at the
  depth-zero `after_value` entry;
* `stage2NoEventWalkParentSepArmDeep` — nine blocks, `2 ≤ %sp.4`, ending at the
  entry one depth lower whose frame word is the popped tag.

Both are proved here from the existing denotations: `afterValue_denote`,
`ifEnd378_denote` (the non-zero frame instance), `ifEnd369Block`,
`ifEnd410Block`, `nodeBlock41Instrs`, and — new in this module — the byte-`93`
`NodeBlock41` test, `LeafBlock39`, `do.body417`, and `close_arr`'s seven `phi`s
and depth test at the `do.body417` edge (`closeArrPhiSpecs` is the committed
block's; only the edge and the frame word `%frame.4 = %frame.6` are new).

**The row.**  `stage2NoEventWalkBracketParentSepRow` composes the pair route and
the nested arm into a `Stage2NoEventWalkRow.cont` for the parent-closer shape,
through `JsonStage2NoEventWalkRowsParentCloser`'s
`stage2NoEventWalkBracketParentCloserRow`: the pair's eleven blocks, the arm's
nine, and the committed cycle at `k + 3` once the endpoint there is a cycle
source (`stage2NoEventWalkCycleSrc_of_afterValueEntry`, from the arm's own entry
plus the comma the caller stages at `k + 3`).  The arm's one-entry allowance
(`9 ≤ 32`) is proved here (`stage2NoEventWalkParentSepArmPrice`).

**Premise provenance.**

* the pair route's staging (the post-push entry lane at `k + 1`, its document
  byte, the popped stack byte) — **the caller's**, exactly as for the committed
  leg; the route's price is `stage2NoEventWalkPairRoutePrice`'s two-entry
  allowance.
* `hsep : Stage2NoEventWalkParentSep K k 93` — **the shape itself**: the entry
  at `k + 2` holds the parent's closer.  This is what replaces the committed
  leg's `hcomma`, which it refutes.
* the entry at `k + 2`'s lane and document byte, the `if.end378` read — **read
  off the invariant** (`Inv.entries`, `Inv.doc` and the run's frame), not the
  caller's: `stage2NoEventCycleEnt_lane` and `stage2NoEventCycleOutDoc` supply
  them at the endpoint's memory.
* the nested arm's pop read at the endpoint's memory — **the caller's**: the
  stack is inside the run's regions, so the invariant does not keep it.
* the endpoint at `k + 3`: its frame word (the popped enclosing tag) non-zero,
  its depth non-zero, and the entry's comma — **the caller's residue**, the same
  three facts `…RowsParentCloser` names for its closer source.  They are the
  *next* container's tag and separator, not this shape's, so no route in this
  module can produce them.
* at depth one the arm reaches `%sp.4 = 0`, so the dispatch is the terminal
  lane; its acceptance/refusal evidence is the caller's reference-side supply
  exactly as `…WalkRowsAfterValue`'s `…ZeroRow` takes it, and this module builds
  no terminal row.

**What is not claimed.**  Nothing here produces the separator at `k + 2` or the
enclosing tag at `k + 3`: the tree lacks a producer for both, and the module
says so rather than assuming them away.  The `{}` class is not this module's:
its pair leg carries `terms + 3` and its endpoint bundle is the frame-zero
`}` route, which `JsonStage2NoEventWalkBraceFrameZeroPair` owns.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceFrameZeroCycle
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsParentCloser

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one readBytes_length)
open LeanLLVM.Refinement.BlockEval

/-! ### What the routes hand back

The committed leg's endpoint is a `Nonempty (Stage2NoEventWalkCycleSrc …)`, which
a `Prop` proof cannot project into the `Stage2NoEventWalkRow` (a `Type`).  The
routes here are `def`s returning structures: the endpoint's state and entry are
fields, so the row composes them directly. -/

/-- **The pair route's result** at the parent's closer: the endpoint state, the
eleven-block segment at the pair's carry, the memory the push left, and the
entry it lands on with its frame word and depth. -/
structure Stage2NoEventWalkParentSepPair (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp fr : Nat) where
  /-- The endpoint's state. -/
  s' : State
  /-- The eleven blocks, at the pair's carry. -/
  seg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkPairCarry K) s' 11
  /-- The push's write is the route's only memory change. -/
  memEq : s'.mem = writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
    (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
  /-- The `after_value` entry at `k + 2`. -/
  entry : Stage2NoEventWalkAfterValueEntry calls mem
    (stage2NoEventWalkPairCarry K) (k + 2) s'
  /-- Its frame word is the pair's own pushed tag. -/
  frameEq : entry.frame = fr
  /-- Its depth is the head's. -/
  spEq : entry.sp = sp

/-- **The seven blocks to `close_arr`**, at the closer's carry, with the cells
the closer's `phi` run and its successors read. -/
structure Stage2NoEventWalkParentSepToClose (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp fr : Nat) where
  /-- The state at `close_arr`'s entry. -/
  s' : State
  /-- The entry at `k + 2`'s lane. -/
  lane : Nat
  /-- The seven blocks, at the closer's carry. -/
  seg : Stage2NoEventWalkSegment calls mem K s
    (stage2NoEventWalkCloserCarry K 4) s' 7
  /-- The block the route stops at. -/
  pc : s'.pc = "close_arr"
  /-- And its predecessor. -/
  pre : s'.pre = some "do.body417"
  /-- The invariant at the closer's carry. -/
  inv : Stage2NoEventWalkInv (stage2NoEventWalkCloserCarry K 4) mem s'
  /-- The route writes no memory. -/
  memEq : s'.mem = s.mem
  frame6 : lookupName s'.env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr))
  f54 : lookupName s'.env "%54" =
    some (.int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295))
  inc379 : lookupName s'.env "%inc379" =
    some (.int 64 (BitVec.ofNat 64 (k + 2 + 1)))
  alen : lookupName s'.env "%alen.8" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arena : lookupName s'.env "%arena.10" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  add419 : lookupName s'.env "%add419" =
    some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4))
  inc418 : lookupName s'.env "%inc418" =
    some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
  /-- The entry chain's live-ins survived the route. -/
  base : Stage2NoEventWalkBaseLookups (stage2NoEventWalkCloserCarry K 4) s'
  /-- The entry at `k + 2` is the one the close read. -/
  ent : K.ent[k + 2]? = some lane
  /-- And its byte is the parent's closer. -/
  byte : K.bs[lane]? = some (0x5D : UInt8)

/-- **The nested arm's result**: nine blocks from the entry at `k + 2` to the
entry at `k + 3`, whose frame word (the popped tag) and depth are non-zero. -/
structure Stage2NoEventWalkParentSepDeep (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  s' : State
  seg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkCloserCarry K 4) s' 9
  entry : Stage2NoEventWalkAfterValueEntry calls mem
    (stage2NoEventWalkCloserCarry K 4) (k + 2 + 1) s'
  frameNe : entry.frame ≠ 0
  spNe : entry.sp ≠ 0

/-- **The top-level arm's result**: eight blocks from the entry at `k + 2` to the
depth-zero entry at `k + 3`. -/
structure Stage2NoEventWalkParentSepTop (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  s' : State
  seg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkCloserCarry K 4) s' 8
  entry : Stage2NoEventWalkAfterValueEntry calls mem
    (stage2NoEventWalkCloserCarry K 4) (k + 2 + 1) s'
  spZero : entry.sp = 0

/-! ### The pair route at the parent's `]`

The committed leg's blocks, links, staging and carry, with the endpoint bundle's
separator dropped and the endpoint exposed as the structure above. -/

def stage2NoEventWalkBracketPairAfterValue {calls : Calls}
    {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (h1H : lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkParentSepPair calls mem K k s sp fr := by
  classical
  -- the head's own cells
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    h.bracketCell hk hbs hb
  have hstk : lookupName s.env "%stk" = some (.ptr K.stk) := h.stk
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := h.nepI
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbPtr : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  have hincH : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  -- the values the route's cells carry
  have hkincLt : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt h.inv.nepLt]
    omega
  -- the eleven blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 1) :: S1.env) S1 "LeafBlock1"
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 1) :: S2.env) S2
    "if.then35.peel"
  let S4 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: S3.env) S3
    "if.end45.peel"
  let S5 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 0) :: S4.env) S4
    "if.then47.peel"
  let S6 := stage2NoEventWalkStored
    (("%arrayidx50.peel", .ptr (bracketPushAddr K (BitVec.ofNat 64 sp))) ::
      ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)) ::
      S5.env)
    S5 (writeBytes S5.mem (bracketPushAddr K (BitVec.ofNat 64 sp)) (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
    "if.end51.peel"
  let S7 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S6.env) S6
    "if.end327.peel"
  let S8 := stage2NoEventWalkNext
    (("%cmp332.peel", .int 1 1) ::
      ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) ::
      ("%arrayidx330.peel",
        .ptr (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4)) ::
      S7.env) S7 "if.then334"
  let S9 := stage2NoEventWalkNext
    (cells (ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)) S8.env) S8 "close_arr"
  let S10 := stage2NoEventWalkNext
    (cells (closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
      (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) S9.env) S9 "if.then350"
  -- `if.then350`'s pop: the frame byte at `%stk + (%sp - 1)`, one byte, read at the
  -- address the block computes (`closeReadAddr`), not the push's sign-extended one
  let popCells : List (String × Value) :=
    ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells50 (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) ++
      closeIdxCells50 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295)
  let S11 := stage2NoEventWalkNext (cells popCells S10.env) S10 "after_value"
  -- the links
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3 (by decide)
  have h3a : lookupName (("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' rfl
      h3a (by decide)
  have h3b : lookupName (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env)
      "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3a
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock1_true L2.inv' rfl
      h3b (by decide)
  have hspLe32 : (BitVec.ofNat 32 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
    exact hspLe
  have hspNe32 : (BitVec.ofNat 32 sp).toNat ≠ 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
    omega
  have hsp3 : lookupName S3.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide) hspH))
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifThen35peel L3.inv' rfl
      hsp3 hspLe32
  have hsp4 : lookupName S4.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide)
          (lookupName_cons_other _ _ _ (by decide) hspH)))
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd45peel L4.inv' rfl
      hsp4 hspNe32
  have h1_5 : lookupName S5.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact h1H
  have hfr5 : lookupName S5.env "%frame.0.ph1402"
      = some (.int 8 (BitVec.ofNat 8 fr)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hstk5 : lookupName S5.env "%stk" = some (.ptr K.stk) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have hv1pos : 1 ≤ (BitVec.ofNat 64 sp).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]
    exact hspPos
  have hv1le : (BitVec.ofNat 64 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sp < 2 ^ 64)]
    exact hspLe
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifThen47peel (calls := calls) L5.inv' rfl h1_5 hfr5 hstk5 hv1pos hv1le
  have hinc6 : lookupName S6.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hnep6 : lookupName S6.env "%nep"
      = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd51peel L6.inv'
      rfl
      hinc6 hnep6 hult
  have hinc7 : lookupName S7.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hep7 : lookupName S7.env "%ep" = some (.ptr K.ep) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb7 : lookupName S7.env "%b" = some (.ptr K.b) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hbPtr
  have L8 : Stage2NoEventWalkLink calls K mem S7 K S8 :=
    link_ifEnd327peel (bs1 := [nextByte]) L7.inv'
      rfl
      hinc7 hep7 hb7 hkincLt hlaneW hval4lt hbyte1W
      (by rw [stage2NoEventWalkBytesToNat_single]; exact hb1)
  have hpre8 : S8.pre = some "if.end327.peel" := rfl
  have hsp8 : lookupName S8.env "%sp.0.ph1403"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have hk8 : lookupName S8.env "%k.0.ph1404"
      = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.kEq
  have htr8 : lookupName S8.env "%terms.0.ph1407"
      = some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.termsPhi
  have htok8 : lookupName S8.env "%tokens.0.ph1408"
      = some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h.tokensPhi
  have L9 : Stage2NoEventWalkLink calls K mem S8 (stage2NoEventWalkPairCarry K) S9 :=
    link_ifThen334 L8.inv' rfl hpre8
      hsp8 hk8 htr8 htok8 (Stage2NoEventWalkInv.tok_add_le h.inv h.count hkbound)
  have hpre9 : S9.pre = some "if.then334" := rfl
  have hnd9 : ((ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)).map (·.1)).Nodup := by
    simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have hsp9' : lookupName S9.env "%sp.0.lcssa1096.wide"
      = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%sp.0.lcssa1096.wide") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have hinc335 : lookupName S9.env "%inc335"
      = some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    have hc : lookupName S9.env "%inc335"
        = some (.int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2)) := by
      simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
        stage2NoEventWalkStored]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells
        (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms))
        (n := "%inc335") (v := .int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have h8alen : lookupName S8.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.alenPhi
  have h8arena : lookupName S8.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.arenaPhi
  have halen9 : lookupName S9.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%alen.0.ph1405") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8alen
  have harena9 : lookupName S9.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%arena.0.ph1406") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8arena
  have hadd338 : lookupName S9.env "%add338"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%add338") (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have hinc337 : lookupName S9.env "%inc337"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%inc337") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  have L10 : Stage2NoEventWalkLink calls (stage2NoEventWalkPairCarry K) mem S9 (stage2NoEventWalkPairCarry K) S10 :=
    link_closeArr (calls := calls) (K := (stage2NoEventWalkPairCarry K))
      L9.inv' rfl hpre9 hsp9' hinc335 halen9 harena9 hadd338 hinc337 hspNe32
  have hpre10 : S10.pre = some "close_arr" := rfl
  have hnd10 : ((closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
      (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)).Nodup := by
    simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have hsp10 : lookupName S10.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have h8stk : lookupName S8.env "%stk" = some (.ptr K.stk) := by
    simp only [S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have h9stk : lookupName S9.env "%stk" = some (.ptr K.stk) := by
    simp only [S9, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%stk") (env := S8.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    exact h8stk
  have hstk10 : lookupName S10.env "%stk" = some (.ptr K.stk) := by
    simp only [S10, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%stk") (env := S9.env)
      (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; simp)]
    exact h9stk
  have hbytePop' : readBytes S10.mem
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs :=
    hbytePop
  have L11 : Stage2NoEventWalkLink calls (stage2NoEventWalkPairCarry K) mem S10 (stage2NoEventWalkPairCarry K) S11 :=
    link_ifThen350 (calls := calls) (K := (stage2NoEventWalkPairCarry K)) (s := S10) (stk := K.stk)
      (sp3 := BitVec.ofNat 32 sp)
      (a := closeReadAddr K.stk (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat)
      (bs := bs) L10.inv' rfl hsp10 hstk10 hbytePop' rfl
  -- the run, at the eleven steps' own fuel
  have hrun : ∀ n, runFuel calls (11 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S11 := by
    intro n
    rw [show 11 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
      (1 + n)))))))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8,
      stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11]
  have hseg : Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkPairCarry K) S11 11 :=
    ⟨hrun, L11.inv'⟩
  -- the trace: the pair's two events
  have hbsOpen : K.bs[lane]? = some (0x5B : UInt8) := by
    have hy : byte = (0x5B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [hy] using hbs
  have hbsClose : K.bs[next]? = some (0x5D : UInt8) := by
    have hy : nextByte = (0x5D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
    simpa [hy] using hbs1
  have htrace' : Stage2NoEventWalkTrace (stage2NoEventWalkPairCarry K) :=
    Stage2NoEventWalkTrace.emptyArray htrace hbsOpen hbsClose
  -- the endpoint's after-value selection at the `if.then350` edge
  have hnd11 : (popCells.map (·.1)).Nodup := by
    simp only [popCells, closeGepCells50, closeIdxCells50,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have h50 : lookupName S11.env "%50"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [S11, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := popCells)
      (n := "%50") (v := .int 8 (BitVec.ofNat 8 (bytesToNat bs)))
      (List.mem_cons.mpr (Or.inl rfl)) hnd11
  have hsp11 : lookupName S11.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%sp.3") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (v := .int 32 (BitVec.ofNat 32 sp))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have hk11 : lookupName S11.env "%k.5"
      = some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%k.5") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%k.5") (v := .int 64 (BitVec.ofNat 64 (k + 2)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have halen11 : lookupName S11.env "%alen.7"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%alen.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%alen.7") (v := .int 64 (BitVec.ofNat 64 K.arena.length))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have harena11 : lookupName S11.env "%arena.9"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%arena.9") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%arena.9") (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have hterms11 : lookupName S11.env "%terms.7"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%terms.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%terms.7")
      (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  have htoks11 : lookupName S11.env "%tokens.7"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := popCells)
      (n := "%tokens.7") (env := S10.env)
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells (BitVec.ofNat 32 sp)
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%tokens.7") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd10
  -- base lookups through the route's cell layers
  have hbase : Stage2NoEventWalkBaseLookups (stage2NoEventWalkPairCarry K) S11 := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := h.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot", .int 1 1)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf2", .int 1 1)]) (names := ["%SwitchLeaf2"]) rfl
      (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%exitcond.peel", .int 1 0)]) (names := ["%exitcond.peel"]) rfl
      (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%tobool46.not.peel", .int 1 0)])
      (names := ["%tobool46.not.peel"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%arrayidx50.peel", .ptr (bracketPushAddr K (BitVec.ofNat 64 sp))),
        ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615))])
      (names := ["%arrayidx50.peel", "%4"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := [("%cmp319.not.peel", .int 1 1)]) (names := ["%cmp319.not.peel"]) rfl
      (by decide)
    have b8 := stage2NoEventCycleBase (K := K) b7
      (cs := [("%cmp332.peel", .int 1 1),
        ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))),
        ("%arrayidx330.peel", .ptr (K.b +
          (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
        ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4))])
      (names := ["%cmp332.peel", "%6", "%arrayidx330.peel", "%idxprom329.peel", "%5",
        "%arrayidx328.peel"]) rfl (by decide)
    have b9 := stage2NoEventCycleBase (K := K) b8
      (cs := ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
        (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := (ifThen334AllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 k)
        (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)).map (·.1)) rfl
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (names := (closeArrAllCells (BitVec.ofNat 32 sp) (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)) rfl
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b11 := stage2NoEventCycleBase (K := K) b10
      (cs := popCells) (names := popCells.map (·.1)) rfl
      (by simp only [popCells, closeGepCells50, closeIdxCells50,
        List.map_append, List.map_cons, List.map_nil]; decide)
    exact b11
  have hmem11 : S11.mem = writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    simp only [S11, S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
  have hsel : PhiSelects (stateAt S11.env S11) "if.then350" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 (bytesToNat bs))),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 2))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkPairCarry K).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkPairCarry K).tok))] := by
    refine PhiSelects.cons (op := .reg "%50") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, h50, hsp11, hk11, halen11, harena11,
        hterms11, htoks11, stage2NoEventWalkOfNat_add, stage2NoEventWalkPairCarry]
  exact ⟨S11, hseg, hmem11,
    ⟨L11.inv', rfl, sp, hspLt, bytesToNat bs, stage2NoEventWalkBytesToNat_lt hbsLen,
      Stage2NoEventWalkCount.step (a := 2) (b := 2) h.count rfl rfl (by omega),
      ⟨"if.then350", rfl, hsel⟩, hbase, h.bPos, htrace'⟩,
    by show bytesToNat bs = fr; rw [hbsVal], rfl⟩
/-- **An `after_value` entry, assembled field by field.**  The entry's `phi` run
is the edge's own; this is the record's constructor with the selector list named,
so a route states it once instead of inlining the literal. -/
def stage2NoEventWalkAfterValueEntryOf {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (inv : Stage2NoEventWalkInv K mem s) (pc : s.pc = "after_value")
    (sp : Nat) (spLt : sp < 2 ^ 32) (frame : Nat) (frameLt : frame < 2 ^ 8)
    (count : Stage2NoEventWalkCount K k)
    (p : String) (pre : s.pre = some p)
    (phiRun : PhiSelects (stateAt s.env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 K.tok))])
    (baseLookups : Stage2NoEventWalkBaseLookups K s) (bPos : 1 ≤ K.b)
    (trace : Stage2NoEventWalkTrace K) :
    Stage2NoEventWalkAfterValueEntry calls mem K k s :=
  { inv := inv, pc := pc, sp := sp, spLt := spLt, frame := frame,
    frameLt := frameLt, count := count, phiRun := ⟨p, pre, phiRun⟩,
    baseLookups := baseLookups, bPos := bPos, trace := trace }

/-! ### The parent's `]` at `after_value`: its blocks

At a non-zero frame word `if.end378`'s test is zero, so the walk takes
`if.end410` and `NodeBlock41`; at the byte `]` its `%53 slt 93` is false and
`LeafBlock39`'s `%53 eq 93` is true.  Only `NodeBlock41`'s `,` instance is
denoted in the tree (and `LeafBlock39`/`do.body417` not at all), so the blocks
are pinned and their runs stated here. -/

/-- `NodeBlock41`'s cell at a test word. -/
def parentSepPivotCells (c : BitVec 1) : List (String × Value) :=
  [("%Pivot42", .int 1 c)]

/-- **`NodeBlock41`'s test** at an arbitrary byte and its `slt` word. -/
theorem nodeBlock41_denote_slt (calls : Calls) (env : Env) (s : State)
    {y : BitVec 8} {c : BitVec 1}
    (h53 : lookupName env "%53" = some (.int 8 y))
    (hc : evalICmp .slt y (BitVec.ofNat 8 93) = c) :
    denoteCode calls nodeBlock41Instrs (stateAt env s) =
      some (stateAt (cells (parentSepPivotCells c) env) s) := by
  rw [nodeBlock41Instrs,
    stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := "%Pivot42") (a := "%53") (p := .slt) (w := 8)
      (x := y) (c := BitVec.ofNat 8 93) h53 (is := [])]
  rw [hc]
  simp only [parentSepPivotCells, cells, denoteCode_nil]

/-- `LeafBlock39`: the byte against 93, the array's closer. -/
def leafBlock39Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf40" IPred.eq 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 93))) ]

/-- `LeafBlock39`, pinned. -/
def leafBlock39Block : Block :=
  { name := "LeafBlock39", instrs := leafBlock39Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf40") "do.body417" "if.then428" }

theorem leafBlock39Block_find :
    stage2NoEventBody.findBlock "LeafBlock39" = some leafBlock39Block := by
  decide

/-- `LeafBlock39`'s cell at a test word. -/
def leafBlock39Cells (c : BitVec 1) : List (String × Value) :=
  [("%SwitchLeaf40", .int 1 c)]

/-- **`LeafBlock39`'s test** at an arbitrary byte and its equality word. -/
theorem leafBlock39_denote (calls : Calls) (env : Env) (s : State)
    {y : BitVec 8} {c : BitVec 1}
    (h53 : lookupName env "%53" = some (.int 8 y))
    (hc : evalICmp .eq y (BitVec.ofNat 8 93) = c) :
    denoteCode calls leafBlock39Instrs (stateAt env s) =
      some (stateAt (cells (leafBlock39Cells c) env) s) := by
  rw [leafBlock39Instrs,
    stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := "%SwitchLeaf40") (a := "%53") (p := .eq) (w := 8)
      (x := y) (c := BitVec.ofNat 8 93) h53 (is := [])]
  rw [hc]
  simp only [leafBlock39Cells, cells, denoteCode_nil]

/-- `do.body417`: one token, four terms, and the depth word one lower. -/
def doBody417Instrs : List Instr :=
  [ Instr.binop "%inc418" BinOp.add 64 (Operand.reg "%tokens.8")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%add419" BinOp.add 64 (Operand.reg "%terms.8")
      (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
    Instr.binop "%54" BinOp.add 32 (Operand.reg "%sp.4")
      (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))) ]

/-- `do.body417`, pinned. -/
def doBody417Block : Block :=
  { name := "do.body417", instrs := doBody417Instrs, term := Term.br "close_arr" }

theorem doBody417Block_find :
    stage2NoEventBody.findBlock "do.body417" = some doBody417Block := by
  decide

/-- `do.body417`'s cells, newest first. -/
def doBody417Cells (tok terms : BitVec 64) (sp4 : BitVec 32) :
    List (String × Value) :=
  [("%54", .int 32 (sp4 + BitVec.ofNat 32 4294967295)),
   ("%add419", .int 64 (terms + BitVec.ofNat 64 4)),
   ("%inc418", .int 64 (tok + BitVec.ofNat 64 1))]

/-- **`do.body417`'s counts**: one token, four terms, and the decremented
depth word. -/
theorem doBody417_denote (calls : Calls) (env : Env) (s : State)
    {tok terms : BitVec 64} {sp4 : BitVec 32}
    (htok : lookupName env "%tokens.8" = some (.int 64 tok))
    (hterms : lookupName env "%terms.8" = some (.int 64 terms))
    (hsp : lookupName env "%sp.4" = some (.int 32 sp4)) :
    denoteCode calls doBody417Instrs (stateAt env s) =
      some (stateAt (cells (doBody417Cells tok terms sp4) env) s) := by
  rw [doBody417Instrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc418") (a := "%tokens.8") (w := 64) (x := tok)
    (c := BitVec.ofNat 64 1) htok
    (is := [Instr.binop "%add419" BinOp.add 64 (Operand.reg "%terms.8")
        (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.binop "%54" BinOp.add 32 (Operand.reg "%sp.4")
        (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295)))])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%add419") (a := "%terms.8") (w := 64) (x := terms)
    (c := BitVec.ofNat 64 4)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hterms)
    (is := [Instr.binop "%54" BinOp.add 32 (Operand.reg "%sp.4")
      (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295)))])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%54") (a := "%sp.4") (w := 32) (x := sp4)
    (c := BitVec.ofNat 32 4294967295)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hsp)
    (is := [])]
  simp only [doBody417Cells, cells, denoteCode_nil]

/-! ### `close_arr` at the `do.body417` edge

The committed `close_arr` rows (`…WalkClose`) are the `if.then334` edge's, where
`%frame.4` is the constant one.  On this edge `%frame.4` is `%frame.6`, the
closer's own frame word, so the `phi` cell list is the committed one with that
word as its first cell, and the depth test is the committed one. -/

/-- The `close_arr` cells at the `do.body417` edge, newest first. -/
def parentSepArrCells (frame : BitVec 8) (sp3 : BitVec 32)
    (k5 alen arena terms7 toks : BitVec 64) : List (String × Value) :=
  [("%tobool349.not", .int 1 (evalICmp .eq sp3 (BitVec.ofNat 32 0))),
   ("%tokens.7", .int 64 toks),
   ("%terms.7", .int 64 terms7),
   ("%arena.9", .int 64 arena),
   ("%alen.7", .int 64 alen),
   ("%k.5", .int 64 k5),
   ("%sp.3", .int 32 sp3),
   ("%frame.4", .int 8 frame)]

/-- **`close_arr`'s seven `phi`s at the `do.body417` edge.** -/
theorem closeArrPhi_denote_doBody417 (calls : Calls) (env : Env) (s : State)
    {frame : BitVec 8} {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64}
    (hpre : s.pre = some "do.body417")
    (hframe : lookupName env "%frame.6" = some (.int 8 frame))
    (h54 : lookupName env "%54" = some (.int 32 sp3))
    (hinc379 : lookupName env "%inc379" = some (.int 64 k5))
    (halen : lookupName env "%alen.8" = some (.int 64 alen))
    (harena : lookupName env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName env "%add419" = some (.int 64 terms7))
    (htoks : lookupName env "%inc418" = some (.int 64 toks)) :
    denoteCode calls closeArrPhiInstrs (stateAt env s) =
      some (stateAt (cells (closeArrPhiCells frame sp3 k5 alen arena terms7 toks)
        env) s) := by
  have hsel : PhiSelects (stateAt env s) "do.body417" closeArrPhiSpecs
      [("%frame.4", .int 8 frame), ("%sp.3", .int 32 sp3), ("%k.5", .int 64 k5),
       ("%alen.7", .int 64 alen), ("%arena.9", .int 64 arena),
       ("%terms.7", .int 64 terms7), ("%tokens.7", .int 64 toks)] := by
    refine PhiSelects.cons (op := .reg "%frame.6") (by decide) ?_
      (PhiSelects.cons (op := .reg "%54") (by decide) ?_
        (PhiSelects.cons (op := .reg "%inc379") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.8") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.10") (by decide) ?_
              (PhiSelects.cons (op := .reg "%add419") (by decide) ?_
                (PhiSelects.cons (op := .reg "%inc418") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hframe, h54, hinc379, halen, harena, hterms,
        htoks]
  rw [closeArr_phi_eq, ← List.append_nil (List.map PhiSpec.instr closeArrPhiSpecs)]
  rw [denoteCode_phiRun (s := stateAt env s) (p := "do.body417")
    (specs := closeArrPhiSpecs) (vs := _) (rest := [])
    (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  simp only [closeArrPhiCells, cells, runCells, denoteCode_nil]

/-- **`close_arr`'s depth test at the `do.body417` edge.** -/
theorem closeArr_test_denote_doBody417 (calls : Calls) (env : Env) (s : State)
    {frame : BitVec 8} {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64} :
    denoteCode calls closeArrRest
        (stateAt (cells (closeArrPhiCells frame sp3 k5 alen arena terms7 toks)
          env) s) =
      some (stateAt (cells (parentSepArrCells frame sp3 k5 alen arena terms7 toks)
        env) s) := by
  rw [closeArrRest]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := cells (closeArrPhiCells frame sp3 k5 alen arena terms7 toks) env)
    (s := s)
    (d := "%tobool349.not") (a := "%sp.3") (p := .eq) (w := 32) (x := sp3)
    (c := BitVec.ofNat 32 0)
    (stage2NoEventWalkCells_some
      (cs := closeArrPhiCells frame sp3 k5 alen arena terms7 toks)
      (n := "%sp.3") (v := .int 32 sp3)
      (by simp [closeArrPhiCells])
      (by simp only [closeArrPhiCells, List.map_cons, List.map_nil]; decide))
    (is := [])]
  rw [parentSepArrCells, cells, closeArrPhiCells, denoteCode_nil]

/-- The state `close_arr` delivers at a live depth, on the `do.body417` edge. -/
def parentSepArrState (s2 : State) (frame : BitVec 8) (sp3 : BitVec 32)
    (k5 alen arena terms7 toks : BitVec 64) : State :=
  stage2NoEventWalkNext
    (cells (parentSepArrCells frame sp3 k5 alen arena terms7 toks) s2.env)
    s2 "if.then350"

/-- The same at the zero depth: the direct handoff to `after_value`. -/
def parentSepArrValue (s2 : State) (frame : BitVec 8) (sp3 : BitVec 32)
    (k5 alen arena terms7 toks : BitVec 64) : State :=
  stage2NoEventWalkNext
    (cells (parentSepArrCells frame sp3 k5 alen arena terms7 toks) s2.env)
    s2 "after_value"

/-- **`close_arr` at a live depth, on the `do.body417` edge**: the seven `phi`s,
the test, and the false arm to `if.then350`. -/
theorem link_closeArr_doBody417_live {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {frame : BitVec 8} {sp3 : BitVec 32}
    {k5 alen arena terms7 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_arr")
    (hpre : s.pre = some "do.body417")
    (hframe : lookupName s.env "%frame.6" = some (.int 8 frame))
    (h54 : lookupName s.env "%54" = some (.int 32 sp3))
    (hinc379 : lookupName s.env "%inc379" = some (.int 64 k5))
    (halen : lookupName s.env "%alen.8" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName s.env "%add419" = some (.int 64 terms7))
    (htoks : lookupName s.env "%inc418" = some (.int 64 toks))
    (hdec : sp3.toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (parentSepArrState s frame sp3 k5 alen arena terms7 toks) := by
  have h1 := closeArrPhi_denote_doBody417 (calls := calls) (env := s.env) (s := s)
    hpre hframe h54 hinc379 halen harena hterms htoks
  have h2 := closeArr_test_denote_doBody417 (calls := calls) (env := s.env) (s := s)
    (frame := frame) (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena)
    (terms7 := terms7) (toks := toks)
  have hbit : evalICmp .eq sp3 (BitVec.ofNat 32 0) = (0 : BitVec 1) :=
    stage2NoEventEq0_zero hdec
  refine stage2NoEventWalkLink_condbr_false
    (env' := cells (parentSepArrCells frame sp3 k5 alen arena terms7 toks) s.env)
    h (by rw [hpc]; exact closeArrBlock_find) ?_ rfl ?_
  · rw [closeArr_split,
      denoteCode_append_apply (a := closeArrPhiInstrs) (b := closeArrRest) h1
        (by decide)]
    exact h2
  · simp only [parentSepArrCells, cells, closeArrPhiCells, lookupName_cons_self, hbit]

/-- **`close_arr` at the zero depth, on the `do.body417` edge**: the seven
`phi`s, the test, and the true arm to `after_value`. -/
theorem link_closeArr_doBody417_zero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {frame : BitVec 8} {sp3 : BitVec 32}
    {k5 alen arena terms7 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_arr")
    (hpre : s.pre = some "do.body417")
    (hframe : lookupName s.env "%frame.6" = some (.int 8 frame))
    (h54 : lookupName s.env "%54" = some (.int 32 sp3))
    (hinc379 : lookupName s.env "%inc379" = some (.int 64 k5))
    (halen : lookupName s.env "%alen.8" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName s.env "%add419" = some (.int 64 terms7))
    (htoks : lookupName s.env "%inc418" = some (.int 64 toks))
    (hdec : sp3.toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (parentSepArrValue s frame sp3 k5 alen arena terms7 toks) := by
  have h1 := closeArrPhi_denote_doBody417 (calls := calls) (env := s.env) (s := s)
    hpre hframe h54 hinc379 halen harena hterms htoks
  have h2 := closeArr_test_denote_doBody417 (calls := calls) (env := s.env) (s := s)
    (frame := frame) (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena)
    (terms7 := terms7) (toks := toks)
  have hbit : evalICmp .eq sp3 (BitVec.ofNat 32 0) = (1 : BitVec 1) :=
    stage2NoEventICmp_eq_one (by
      apply BitVec.eq_of_toNat_eq
      rw [hdec]
      rfl)
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (parentSepArrCells frame sp3 k5 alen arena terms7 toks) s.env)
    h (by rw [hpc]; exact closeArrBlock_find) ?_ rfl ?_
  · rw [closeArr_split,
      denoteCode_append_apply (a := closeArrPhiInstrs) (b := closeArrRest) h1
        (by decide)]
    exact h2
  · simp only [parentSepArrCells, cells, closeArrPhiCells, lookupName_cons_self, hbit]

/-! ### The depth word's arithmetic

`%54 = %sp.4 + (2 ^ 32 - 1)` and `if.then350`'s index is one more such
subtraction; both are the `Nat` decrement. -/

/-- **One decrement of a depth word.** -/
theorem stage2NoEventWalkOfNat32_dec (sp : Nat) (h1 : 1 ≤ sp) (hlt : sp < 2 ^ 32) :
    (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat = sp - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by decide : 4294967295 < 2 ^ 32)]
  have h : sp + 4294967295 = (sp - 1) + 1 * 2 ^ 32 := by omega
  rw [h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- **A lookup at a lane inside the document is its `getD` read.** -/
theorem stage2NoEventWalkGetD_getElem? {l : List UInt8} {i : Nat} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ### The trace's close-bracket step

`]` is one event and four terms, exactly `do.body417`'s `%inc418 = %tokens.8 + 1`
and `%add419 = %terms.8 + 4`.  The event is the relation's `T_ARR_END`. -/

/-- **`]` appends to the trace**, with `tok + 1` and `terms + 4`. -/
theorem Stage2NoEventWalkTrace.closeArray {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start : Nat}
    (hbyte : K.bs[start]? = some (0x5D : UInt8)) :
    Stage2NoEventWalkTrace { K with tok := K.tok + 1, terms := K.terms + 4 } := by
  refine h.step (K' := { K with tok := K.tok + 1, terms := K.terms + 4 })
    (stage2NoEventWalkCloseBracketRel hbyte)
    (stage2NoEventArenaBound_markers (es := [ConsumerEvent.kind 4]) ?_) rfl rfl ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    exact ⟨by decide, by decide⟩
  · rfl
  · have h4 : ([ConsumerEvent.kind 4].map ConsumerEvent.terms).sum = 4 := by decide
    rw [h4]

/-! ### The prologue: the entry at `k + 2` to `close_arr`

Seven blocks: the dispatch (`after_value`, `if.end369` at the live-entry test,
`if.end378` at the frame test's zero), `if.end410`, `NodeBlock41` at `]`,
`LeafBlock39` at `]`, and `do.body417`'s count store, which moves the carry to
`stage2NoEventWalkCloserCarry K 4`.  The entry at `k + 2`'s lane and document
byte are read off the invariant; `hsep` is what makes them `]`. -/

/-- **The seven blocks from the entry to `close_arr`.** -/
noncomputable def stage2NoEventWalkParentSepToCloseArr {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeNe : h.frame ≠ 0) (hspNe : h.sp ≠ 0)
    (hsep : Stage2NoEventWalkParentSep K k 93)
    (hklt : k + 2 < K.nep) (hk63 : k + 2 < 2 ^ 63) :
    Stage2NoEventWalkParentSepToClose calls mem K k s h.sp h.frame := by
  classical
  let pEdge : String := Classical.choose h.phiRun
  have hpEdge := Classical.choose_spec h.phiRun
  have hpre : s.pre = some pEdge := hpEdge.1
  have hsel : PhiSelects (stateAt s.env s) pEdge afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 h.frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 h.sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 2))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 K.tok))] := hpEdge.2
  -- the entry at `k + 2` and the document's byte at its lane
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    h.inv.readLanes_off (stage2NoEventCycleOutLane h.inv) h.inv.entries
  let lane : Nat := Classical.choose (stage2NoEventCycleEnt_lane hlanes hklt)
  let bs4 : List UInt8 :=
    Classical.choose (Classical.choose_spec (stage2NoEventCycleEnt_lane hlanes hklt))
  have hent4 := Classical.choose_spec
    (Classical.choose_spec (stage2NoEventCycleEnt_lane hlanes hklt))
  have hget : K.ent[k + 2]? = some lane := hent4.1
  have hread4 : readBytes s.mem (K.ep + 4 * (k + 2)) 4 = some bs4 := hent4.2.1
  have hval4 : bytesToNat bs4 = lane := hent4.2.2.1
  have hlaneLt : lane < 2 ^ 32 := hent4.2.2.2
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by rw [hval4]; exact hlaneLt
  have hins : lane < K.n := h.inv.inside lane (List.mem_of_getElem? hget)
  have hdoc : readBytes s.mem (K.b + lane) 1 = some [K.bs.getD lane 0] :=
    h.inv.readBytes_off (K := K) (a := K.b + lane) (N := 1)
      (bs := [K.bs.getD lane 0]) (stage2NoEventCycleOutDoc h.inv hins) (by
        rw [readBytes_one, readByte_of_readBytes h.inv.doc hins]
        rfl)
  have hbyteX : (K.bs.getD lane 0).toNat = 93 := hsep lane hget
  have hynat : BitVec.ofNat 8 (K.bs.getD lane 0).toNat = BitVec.ofNat 8 93 := by
    rw [hbyteX]
  have hnep : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    h.baseLookups "%nep" _ (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hb : lookupName s.env "%b" = some (.ptr K.b) :=
    h.baseLookups "%b" _ (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) :=
    h.baseLookups "%ep" _ (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  let e1 : Env := cells afterValueDispatchCells
    (cells (afterValuePhiCells h.frame h.sp (k + 2) K.arena.length K.arenaWord
      K.terms K.tok) s.env)
  let r1 : State := stage2NoEventWalkNext e1 s "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.end378"
  let e3 : Env := cells (ifEnd378Cells K.ep K.b lane (k + 2) h.frame
    (K.bs.getD lane 0)) e1
  let r3 : State := stage2NoEventWalkNext e3 r2 "if.end410"
  let r4 : State := stage2NoEventWalkNext e3 r3 "NodeBlock41"
  let e5 : Env := cells (parentSepPivotCells 0) e3
  let r5 : State := stage2NoEventWalkNext e5 r4 "LeafBlock39"
  let e6 : Env := cells (leafBlock39Cells 1) e5
  let r6 : State := stage2NoEventWalkNext e6 r5 "do.body417"
  let e7 : Env := cells (doBody417Cells (BitVec.ofNat 64 K.tok)
    (BitVec.ofNat 64 K.terms) (BitVec.ofNat 32 h.sp)) e6
  let r7 : State := stage2NoEventWalkNext e7 r6 "close_arr"
  -- the dispatch's two cells
  have hcmp355 : lookupName e1 "%cmp355" = some (.int 1 0) := by
    simp only [e1, cells, afterValueDispatchCells, afterValuePhiCells]
    cycle_lk
  have hcmp358 : lookupName e1 "%cmp358" = some (.int 1 1) := by
    simp only [e1, cells, afterValueDispatchCells, afterValuePhiCells]
    cycle_lk
  have hk6_1 : lookupName e1 "%k.6" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [e1, cells, afterValueDispatchCells, afterValuePhiCells]
    cycle_lk
  have hframe6_1 : lookupName e1 "%frame.6" =
      some (.int 8 (BitVec.ofNat 8 h.frame)) := by
    simp only [e1, cells, afterValueDispatchCells, afterValuePhiCells]
    cycle_lk
  have l1 : Stage2NoEventWalkLink calls K mem s K r1 :=
    stage2NoEventWalkLink_condbr_false h.inv (by rw [h.pc]; exact afterValueBlock_find)
      (afterValue_denote (calls := calls) (env := s.env) (s := s) (p := pEdge)
        (fr := h.frame) (sp := h.sp) (k := k + 2) (alen := K.arena.length)
        (arena := K.arenaWord) (terms := K.terms) (tok := K.tok) (nep := K.nep)
        hpre hsel hnep h.spLt hspNe (by omega) hklt h.inv.nepLt)
      rfl hcmp355
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil calls (stateAt e1 r1))
      rfl hcmp358
  have hcmp382_3 : lookupName e3 "%cmp382" = some (.int 1 0) := by
    simp only [e3, cells, ifEnd378Cells]
    cycle_lk
  have l3 : Stage2NoEventWalkLink calls K mem r2 K r3 :=
    stage2NoEventWalkLink_condbr_false l2.inv'
      (by rw [show r2.pc = "if.end378" from rfl]; exact ifEnd378Block_find)
      (ifEnd378_denote (calls := calls) (env := e1) (s := r2)
        (ep := K.ep) (b := K.b) (lane := lane) (k := k + 2) (fr := h.frame)
        (byte := K.bs.getD lane 0) (bs4 := bs4)
        hk6_1 hep hb hframe6_1 hk63 h.frameLt hframeNe hval4 hlaneLt hread4 hdoc)
      rfl hcmp382_3
  have l4 : Stage2NoEventWalkLink calls K mem r3 K r4 :=
    stage2NoEventWalkLink_br l3.inv'
      (by rw [show r3.pc = "if.end410" from rfl]; exact ifEnd410Block_find)
      (by rw [ifEnd410Block]; exact denoteCode_nil calls (stateAt e3 r3)) rfl
  have h53_3 : lookupName e3 "%53" =
      some (.int 8 (BitVec.ofNat 8 (K.bs.getD lane 0).toNat)) := by
    simp only [e3, cells, ifEnd378Cells]
    cycle_lk
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_false l4.inv'
      (by rw [show r4.pc = "NodeBlock41" from rfl]; exact nodeBlock41Block_find)
      (nodeBlock41_denote_slt (calls := calls) (env := e3) (s := r4)
        (y := BitVec.ofNat 8 (K.bs.getD lane 0).toNat) (c := 0) h53_3
        (by rw [hynat]; decide))
      rfl (by
        simp only [r5, e5, stage2NoEventWalkNext, parentSepPivotCells, cells,
          lookupName_cons_self])
  have h53_5 : lookupName e5 "%53" =
      some (.int 8 (BitVec.ofNat 8 (K.bs.getD lane 0).toNat)) := by
    simp only [e5, parentSepPivotCells, cells]
    cycle_lk
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock39" from rfl]; exact leafBlock39Block_find)
      (leafBlock39_denote (calls := calls) (env := e5) (s := r5)
        (y := BitVec.ofNat 8 (K.bs.getD lane 0).toNat) (c := 1) h53_5
        (by rw [hynat]; decide))
      rfl (by
        simp only [r6, e6, stage2NoEventWalkNext, leafBlock39Cells, cells,
          lookupName_cons_self])
  have htok6 : lookupName e6 "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [e6, e5, parentSepPivotCells, leafBlock39Cells, cells]
    cycle_lk
  have hterms6 : lookupName e6 "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [e6, e5, parentSepPivotCells, leafBlock39Cells, cells]
    cycle_lk
  have hsp46 : lookupName e6 "%sp.4" =
      some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [e6, e5, parentSepPivotCells, leafBlock39Cells, cells]
    cycle_lk
  have hcode7 : denoteCode calls doBody417Block.instrs r6 =
      some (stateAt e7 r6) := by
    rw [doBody417Block]
    exact doBody417_denote (calls := calls) (env := e6) (s := r6)
      (tok := BitVec.ofNat 64 K.tok) (terms := BitVec.ofNat 64 K.terms)
      (sp4 := BitVec.ofNat 32 h.sp) htok6 hterms6 hsp46
  have hinv7 : Stage2NoEventWalkInv (stage2NoEventWalkCloserCarry K 4) mem r7 :=
    Stage2NoEventWalkInv.mem_congr
      (Stage2NoEventWalkInv.count (h := l6.inv') (t := 1) (c := 4)
        (Stage2NoEventWalkInv.tok_add_le l6.inv' h.count (by have := hklt; omega)))
      rfl
  have hstep7 : step calls stage2NoEventBody r6 = .jump r7 := by
    have hfind : stage2NoEventBody.findBlock r6.pc = some doBody417Block := by
      rw [show r6.pc = "do.body417" from rfl]
      exact doBody417Block_find
    have hterm : doBody417Block.term = Term.br "close_arr" := by
      rw [doBody417Block]
    have hh := stage2NoEventWalk_step_br (f := stage2NoEventBody) hfind hcode7 hterm
    simpa only [r7, e7, stateAt, stage2NoEventWalkNext] using hh
  have l7 : Stage2NoEventWalkLink calls K mem r6
      (stage2NoEventWalkCloserCarry K 4) r7 :=
    ⟨l6.inv', hstep7, hinv7⟩
  have hrun : ∀ n, runFuel calls (7 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r7 := by
    intro n
    rw [show 7 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel l1, stage2NoEventWalkLink_runFuel l2,
      stage2NoEventWalkLink_runFuel l3, stage2NoEventWalkLink_runFuel l4,
      stage2NoEventWalkLink_runFuel l5, stage2NoEventWalkLink_runFuel l6,
      stage2NoEventWalkLink_runFuel l7]
  -- the cells `close_arr`'s `phi` run reads, at the count store's exit
  have hframe6_7 : lookupName r7.env "%frame.6" =
      some (.int 8 (BitVec.ofNat 8 h.frame)) := by
    simp only [r7, e7, doBody417Cells, e6, e5, parentSepPivotCells, leafBlock39Cells,
      cells, stage2NoEventWalkNext]
    cycle_lk
  have h54_7 : lookupName r7.env "%54" =
      some (.int 32 (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295)) := by
    simp only [r7, e7, e6, e5, parentSepPivotCells, leafBlock39Cells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hinc379_7 : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 2 + 1))) := by
    simp only [r7, e7, e6, e5, e3, ifEnd378Cells, parentSepPivotCells,
      leafBlock39Cells, cells, stage2NoEventWalkNext]
    cycle_lk
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, e7, e6, e5, e3, e1, ifEnd378Cells, parentSepPivotCells,
      leafBlock39Cells, afterValueDispatchCells, afterValuePhiCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, e7, e6, e5, e3, e1, ifEnd378Cells, parentSepPivotCells,
      leafBlock39Cells, afterValueDispatchCells, afterValuePhiCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hterms7 : lookupName r7.env "%add419" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)) := by
    simp only [r7, e7, doBody417Cells, e6, e5, parentSepPivotCells, leafBlock39Cells,
      cells, stage2NoEventWalkNext]
    cycle_lk
  have htoks7 : lookupName r7.env "%inc418" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r7, e7, doBody417Cells, e6, e5, parentSepPivotCells, leafBlock39Cells,
      cells, stage2NoEventWalkNext]
    cycle_lk
  have hbase7 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r7 := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := h.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := afterValuePhiCells h.frame h.sp (k + 2) K.arena.length K.arenaWord
        K.terms K.tok)
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := afterValueDispatchCells) (names := ["%cmp358", "%cmp355"]) rfl
      (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := ifEnd378Cells K.ep K.b lane (k + 2) h.frame (K.bs.getD lane 0))
      (names := ["%53", "%arrayidx386", "%idxprom385", "%cmp382", "%52",
        "%arrayidx380", "%inc379"]) rfl (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := parentSepPivotCells 0) (names := ["%Pivot42"]) rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := leafBlock39Cells 1) (names := ["%SwitchLeaf40"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := doBody417Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms)
        (BitVec.ofNat 32 h.sp))
      (names := ["%54", "%add419", "%inc418"]) rfl (by decide)
    exact b6
  -- the trace's `]`
  have hltLane : lane < K.bs.length := by
    rw [readBytes_length mem K.b K.n (bs := K.bs) h.inv.doc]
    exact hins
  have hbsget : K.bs[lane]? = some (K.bs.getD lane 0) :=
    stage2NoEventWalkGetD_getElem? hltLane
  have hbsClose : K.bs[lane]? = some (0x5D : UInt8) := by
    have hy : (K.bs[lane]?).getD 0 = (0x5D : UInt8) := by
      rw [← List.getD_eq_getElem?_getD]
      exact stage2NoEventWalk_uint8_eq_of_toNat (by rw [hbyteX]; decide)
    simpa [hy] using hbsget
  exact ⟨r7, lane, ⟨hrun, hinv7⟩, rfl, rfl, hinv7, rfl, hframe6_7, h54_7,
    hinc379_7, halen7, harena7, hterms7, htoks7, hbase7, hget, hbsClose⟩

/-! ### The arm's two depths

At `%sp.4 = 1` `close_arr`'s test is true and the arm lands at the depth-zero
entry; above it the test is false, `if.then350` pops the enclosing tag, and the
entry is one depth lower with that byte as its frame word. -/

/-- **The parent's `]` arm at the top level** (`%sp.4 = 1`): eight blocks from the
entry at `k + 2` to the depth-zero entry at `k + 3`.  Its terminal row is the
caller's, exactly as `…WalkRowsAfterValue`'s `…ZeroRow` takes it. -/
noncomputable def stage2NoEventWalkParentSepArmTop {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeNe : h.frame ≠ 0) (hspOne : h.sp = 1)
    (hsep : Stage2NoEventWalkParentSep K k 93)
    (hklt : k + 2 < K.nep) (hk63 : k + 2 < 2 ^ 63) :
    Stage2NoEventWalkParentSepTop calls mem K k s := by
  classical
  obtain ⟨s7, lane, hseg7, hpc7, hpre7, hinv7, hmem7, hframe7, h54_7, hinc7,
    halen7, harena7, hterms7, htoks7, hbase7, hget, hbsClose⟩ :=
    stage2NoEventWalkParentSepToCloseArr h hframeNe (by rw [hspOne]; decide) hsep
      hklt hk63
  have hsp3zero : BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295 =
      BitVec.ofNat 32 0 := by
    rw [hspOne]
    decide
  have hdecZ : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat = 0 := by
    rw [hsp3zero]
    rfl
  let sp3 : BitVec 32 := BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295
  let frame8 : BitVec 8 := BitVec.ofNat 8 h.frame
  let r8 : State := parentSepArrValue s7 frame8 sp3
    (BitVec.ofNat 64 (k + 2 + 1)) (BitVec.ofNat 64 K.arena.length)
    (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
    (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
  have h54_7' : lookupName s7.env "%54" = some (.int 32 sp3) := h54_7
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloserCarry K 4) mem s7
      (stage2NoEventWalkCloserCarry K 4) r8 :=
    link_closeArr_doBody417_zero (K := stage2NoEventWalkCloserCarry K 4)
      hinv7 hpc7 hpre7 hframe7 h54_7' hinc7 halen7 harena7 hterms7 htoks7 hdecZ
  have hrun : ∀ n, runFuel calls (1 + n) stage2NoEventBody s7 =
      runFuel calls n stage2NoEventBody r8 := by
    intro n
    rw [stage2NoEventWalkLink_runFuel l8]
  have hframe4_8 : lookupName r8.env "%frame.4" =
      some (.int 8 frame8) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hsp3_8 : lookupName r8.env "%sp.3" = some (.int 32 sp3) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hk5_8 : lookupName r8.env "%k.5" =
      some (.int 64 (BitVec.ofNat 64 (k + 2 + 1))) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have halen8 : lookupName r8.env "%alen.7" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have harena8 : lookupName r8.env "%arena.9" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hterms8 : lookupName r8.env "%terms.7" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have htoks8 : lookupName r8.env "%tokens.7" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r8, parentSepArrValue, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hbase8 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r8 := by
    have b7 := stage2NoEventCycleBase (K := K) (env := s7.env) hbase7
      (cs := parentSepArrCells frame8 sp3 (BitVec.ofNat 64 (k + 2 + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool349.not", "%tokens.7", "%terms.7", "%arena.9",
        "%alen.7", "%k.5", "%sp.3", "%frame.4"]) rfl (by decide)
    exact b7
  have htrace8 : Stage2NoEventWalkTrace (stage2NoEventWalkCloserCarry K 4) :=
    Stage2NoEventWalkTrace.closeArray h.trace hbsClose
  have hsel8 : PhiSelects (stateAt r8.env r8) "close_arr" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 h.frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp3.toNat)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 2 + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).tok))] := by
    refine PhiSelects.cons (op := .reg "%frame.4") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [frame8, stateAt, evalOperand, hframe4_8, hsp3_8, hk5_8, halen8,
        harena8, hterms8, htoks8, stage2NoEventWalkOfNat_add,
        stage2NoEventWalkCloserCarry, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hpre8 : some s7.pc = some "close_arr" := by rw [hpc7]
  have hcount8 : Stage2NoEventWalkCount (stage2NoEventWalkCloserCarry K 4)
      (k + 2 + 1) :=
    Stage2NoEventWalkCount.step (a := 1) (b := 1) h.count rfl rfl (by omega)
  let hentry8 : Stage2NoEventWalkAfterValueEntry calls mem
      (stage2NoEventWalkCloserCarry K 4) (k + 2 + 1) r8 :=
    stage2NoEventWalkAfterValueEntryOf (calls := calls) (mem := mem)
      (K := stage2NoEventWalkCloserCarry K 4) (k := k + 2 + 1) (s := r8)
      l8.inv' rfl sp3.toNat sp3.isLt h.frame h.frameLt hcount8 "close_arr" hpre8
      hsel8 hbase8 h.bPos htrace8
  exact ⟨r8, hseg7.trans ⟨hrun, l8.inv'⟩, hentry8,
    by show sp3.toNat = 0; exact hdecZ⟩

/-- **The parent's `]` arm at a nested depth** (`2 ≤ %sp.4`): nine blocks, the
`if.then350` pop included, from the entry at `k + 2` to the entry at `k + 3`,
whose frame word is the popped enclosing tag and whose depth is one lower. -/
noncomputable def stage2NoEventWalkParentSepArmDeep {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkAfterValueEntry calls mem K (k + 2) s)
    (hframeNe : h.frame ≠ 0) (hspTwo : 2 ≤ h.sp)
    (hsep : Stage2NoEventWalkParentSep K k 93)
    (hklt : k + 2 < K.nep) (hk63 : k + 2 < 2 ^ 63)
    {a : Nat} {bsP : List UInt8}
    (hpop : readBytes s.mem a 1 = some bsP)
    (hpopAddr : a = closeReadAddr K.stk
      ((BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295) +
        BitVec.ofNat 32 4294967295).toNat)
    (hbsLen : bsP.length = 1) (hbsPNe : bytesToNat bsP ≠ 0) :
    Stage2NoEventWalkParentSepDeep calls mem K k s := by
  classical
  obtain ⟨s7, lane, hseg7, hpc7, hpre7, hinv7, hmem7, hframe7, h54_7, hinc7,
    halen7, harena7, hterms7, htoks7, hbase7, hget, hbsClose⟩ :=
    stage2NoEventWalkParentSepToCloseArr h hframeNe (by omega) hsep hklt hk63
  have hspLt := h.spLt
  have hdec : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [stage2NoEventWalkOfNat32_dec h.sp (by omega) hspLt]
    omega
  let sp3 : BitVec 32 := BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295
  let frame8 : BitVec 8 := BitVec.ofNat 8 h.frame
  let r8 : State := parentSepArrState s7 frame8 sp3
    (BitVec.ofNat 64 (k + 2 + 1)) (BitVec.ofNat 64 K.arena.length)
    (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
    (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
  have h54_7' : lookupName s7.env "%54" = some (.int 32 sp3) := h54_7
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloserCarry K 4) mem s7
      (stage2NoEventWalkCloserCarry K 4) r8 :=
    link_closeArr_doBody417_live (K := stage2NoEventWalkCloserCarry K 4)
      hinv7 hpc7 hpre7 hframe7 h54_7' hinc7 halen7 harena7 hterms7 htoks7 hdec
  -- the pop
  have hsp3_8 : lookupName r8.env "%sp.3" = some (.int 32 sp3) := by
    simp only [r8, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hbase8 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r8 := by
    have b7 := stage2NoEventCycleBase (K := K) (env := s7.env) hbase7
      (cs := parentSepArrCells frame8 sp3 (BitVec.ofNat 64 (k + 2 + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool349.not", "%tokens.7", "%terms.7", "%arena.9",
        "%alen.7", "%k.5", "%sp.3", "%frame.4"]) rfl (by decide)
    exact b7
  have hstk8 : lookupName r8.env "%stk" = some (.ptr K.stk) :=
    hbase8 "%stk" _ (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries,
        stage2NoEventWalkCloserCarry])
  have hr8mem : r8.mem = s.mem := by
    have h1 : r8.mem = s7.mem := rfl
    rw [h1, hmem7]
  have hpop8 : readBytes r8.mem a 1 = some bsP := by
    rw [hr8mem]
    exact hpop
  let r9 : State := bracketRead r8 sp3 a bsP
  have l9 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloserCarry K 4) mem r8
      (stage2NoEventWalkCloserCarry K 4) r9 :=
    link_ifThen350 (K := stage2NoEventWalkCloserCarry K 4) l8.inv' rfl hsp3_8
      hstk8 hpop8 hpopAddr
  have hrun : ∀ n, runFuel calls (2 + n) stage2NoEventBody s7 =
      runFuel calls n stage2NoEventBody r9 := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel l8, stage2NoEventWalkLink_runFuel l9]
  -- the entry's cells at the `if.then350` edge
  have h50 : lookupName r9.env "%50" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bsP))) := by
    simp only [r9, bracketRead, cells, stage2NoEventWalkNext]
    cycle_lk
  have hsp3_9 : lookupName r9.env "%sp.3" = some (.int 32 sp3) := by
    simp only [r9, bracketRead, cells, stage2NoEventWalkNext]
    cycle_lk
  have hk5_9 : lookupName r9.env "%k.5" =
      some (.int 64 (BitVec.ofNat 64 (k + 2 + 1))) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have halen9 : lookupName r9.env "%alen.7" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have harena9 : lookupName r9.env "%arena.9" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hterms9 : lookupName r9.env "%terms.7" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 4)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have htoks9 : lookupName r9.env "%tokens.7" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r9, r8, bracketRead, parentSepArrState, parentSepArrCells, cells,
      stage2NoEventWalkNext]
    cycle_lk
  have hbase9 : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkCloserCarry K 4) r9 := by
    have b8 := stage2NoEventCycleBase (K := K) (env := r8.env) hbase8
      (cs := ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295))
      (names := (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)).map
          (·.1)) rfl
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)
    exact b8
  have htrace9 : Stage2NoEventWalkTrace (stage2NoEventWalkCloserCarry K 4) :=
    Stage2NoEventWalkTrace.closeArray h.trace hbsClose
  have hsel9 : PhiSelects (stateAt r9.env r9) "if.then350" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 (bytesToNat bsP))),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp3.toNat)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 2 + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 (stage2NoEventWalkCloserCarry K 4).tok))] := by
    refine PhiSelects.cons (op := .reg "%50") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, h50, hsp3_9, hk5_9, halen9, harena9, hterms9,
        htoks9, stage2NoEventWalkOfNat_add, stage2NoEventWalkCloserCarry,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcount9 : Stage2NoEventWalkCount (stage2NoEventWalkCloserCarry K 4)
      (k + 2 + 1) :=
    Stage2NoEventWalkCount.step (a := 1) (b := 1) h.count rfl rfl (by omega)
  let hentry9 : Stage2NoEventWalkAfterValueEntry calls mem
      (stage2NoEventWalkCloserCarry K 4) (k + 2 + 1) r9 :=
    stage2NoEventWalkAfterValueEntryOf (calls := calls) (mem := mem)
      (K := stage2NoEventWalkCloserCarry K 4) (k := k + 2 + 1) (s := r9)
      l9.inv' rfl sp3.toNat sp3.isLt (bytesToNat bsP)
      (stage2NoEventWalkBytesToNat_lt hbsLen) hcount9 "if.then350" rfl hsel9
      hbase9 h.bPos htrace9
  refine ⟨r9, hseg7.trans ⟨hrun, l9.inv'⟩, hentry9, ?_, ?_⟩
  · show bytesToNat bsP ≠ 0
    exact hbsPNe
  · show sp3.toNat ≠ 0
    exact hdec

/-! ### The arm's price

The arm advances one entry, from `k + 2` to `k + 3`, so its count is payable from
one entry's allowance whatever its own block count (eight or nine): the potential
reads neither `tok` nor `terms`, so the closer's carry is the pair carry's at the
same index. -/

/-- **The arm's price**: any count up to one entry's allowance (`32`) is payable
from `Φ K (k+2)` to `Φ (closerCarry K 4) (k+3)`. -/
theorem stage2NoEventWalkParentSepArmPrice {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (hinv : Stage2NoEventWalkInv K mem s) (hk3 : k + 3 < K.nep)
    {p : Nat} (hp : p ≤ 32) :
    p + stage2NoEventWalkPotential (stage2NoEventWalkCloserCarry K 4) (k + 3) ≤
      stage2NoEventWalkPotential K (k + 2) := by
  have hpot : stage2NoEventWalkPotential (stage2NoEventWalkCloserCarry K 4) (k + 3) =
      stage2NoEventWalkPotential K (k + 3) := rfl
  rw [hpot, show k + 3 = k + 2 + 1 from by omega]
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent hinv.entries
  have hentle : K.ent.getD (k + 2) 0 ≤ K.ent.getD (k + 3) 0 :=
    stage2NoEventEnt_getD_le hinv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k + 2) (d := 1)
    (by omega) hentle
  have h32 : 32 * 1 = 32 := by decide
  rw [h32] at hadd
  omega

/-! ### The row

The pair's eleven blocks, the arm's nine, and the committed cycle at `k + 3`,
composed through `JsonStage2NoEventWalkRowsParentCloser`'s
`stage2NoEventWalkBracketParentCloserRow`.  The endpoint at `k + 3` is a cycle
source built from the arm's own entry plus the comma the caller stages there. -/

/-- **The empty array's row at the parent's `]`**, at a nested depth
(`2 ≤ sp`): the head at `[`, its pair's `]` at `k + 1`, the parent's `]` at
`k + 2`, and the continuing walk from the committed cycle at `k + 3`.

The pair route's staging is the committed leg's (the post-push entry lane and
document byte at `k + 1`, the popped stack byte); the shape's separator is
`hsep`; the parent arm's pop at the endpoint's memory is the caller's; and the
endpoint's frame word (the popped enclosing tag), its depth and the comma at
`k + 3` are the caller's residue. -/
noncomputable def stage2NoEventWalkBracketParentSepRow {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (h1H : lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrPos : 1 ≤ fr) (hspTwo : 2 ≤ sp)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hsep : Stage2NoEventWalkParentSep K k 93)
    {bsP : List UInt8}
    (hbytePopP : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        ((BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295) +
          BitVec.ofNat 32 4294967295).toNat) 1 = some bsP)
    (hbsPLen : bsP.length = 1) (hbsPNe : bytesToNat bsP ≠ 0)
    (hcomma3 : ∀ lane', (stage2NoEventWalkCloserCarry
        (stage2NoEventWalkPairCarry K) 4).ent[k + 3]? = some lane' →
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4).bs.getD
        lane' 0 = 44)
    (hlt : k + 3 < K.nep) (hk4lt : k + 4 < K.nep) (hk63 : k + 4 < 2 ^ 63) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  -- the pair route
  obtain ⟨sE, hsegP, hmemE, eE, hEfr, hEsp⟩ :=
    stage2NoEventWalkBracketPairAfterValue (calls := calls) h htrace hk hbs hb hk1
      hbs1 hb1 hspH hfrH h1H hspPos hspLe hspLt hkbound hlaneW hval4lt hbyte1W
      hbytePop hbsLen hbsVal (by omega)
  have hframeNe : eE.frame ≠ 0 := by rw [hEfr]; omega
  have hspTwoE : 2 ≤ eE.sp := by rw [hEsp]; exact hspTwo
  have hkltE : k + 2 < (stage2NoEventWalkPairCarry K).nep := by
    show k + 2 < K.nep
    omega
  have hk63E : k + 2 < 2 ^ 63 := by omega
  -- the parent's `]` arm
  obtain ⟨sE', hsegA, eE', hframeNeE, hspNeE⟩ :=
    stage2NoEventWalkParentSepArmDeep (K := stage2NoEventWalkPairCarry K) (k := k)
      (s := sE) eE hframeNe hspTwoE hsep hkltE hk63E
      (a := closeReadAddr K.stk
        ((BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295) +
          BitVec.ofNat 32 4294967295).toNat)
      (by rw [hmemE]; exact hbytePopP)
      (by rw [hEsp]; simp only [stage2NoEventWalkPairCarry])
      hbsPLen hbsPNe
  -- the endpoint one level up, as the committed cycle's source
  have hsrc' : Stage2NoEventWalkCycleSrc calls mem
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4)
      (k + 2 + 1) sE' :=
    stage2NoEventWalkCycleSrc_of_afterValueEntry eE' hframeNeE hspNeE
      (by show (k + 2 + 1) + 1 < 2 ^ 63; omega)
      (by
        show (k + 2 + 1) + 1 < (stage2NoEventWalkCloserCarry
          (stage2NoEventWalkPairCarry K) 4).nep
        show (k + 2 + 1) + 1 < K.nep
        omega)
      (by
        intro lane' hl'
        exact hcomma3 lane'
          (by rwa [show k + 2 + 1 = k + 3 from by omega] at hl'))
  have hsrc : Stage2NoEventWalkCycleSrc calls mem
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) (k + 3) sE' := by
    simpa only [show k + 2 + 1 = k + 3 from by omega] using hsrc'
  -- the arm's one-entry allowance
  have hpprice : 9 + stage2NoEventWalkPotential
      (stage2NoEventWalkCloserCarry (stage2NoEventWalkPairCarry K) 4) (k + 3) ≤
      stage2NoEventWalkPotential (stage2NoEventWalkPairCarry K) (k + 2) :=
    stage2NoEventWalkParentSepArmPrice (K := stage2NoEventWalkPairCarry K) eE.inv
      (by show k + 3 < K.nep; omega) (p := 9) (by decide)
  exact stage2NoEventWalkBracketParentCloserRow h hsegP hsegA hpprice hsrc

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracketPairAfterValue
#print axioms nodeBlock41_denote_slt
#print axioms leafBlock39_denote
#print axioms doBody417_denote
#print axioms closeArrPhi_denote_doBody417
#print axioms closeArr_test_denote_doBody417
#print axioms link_closeArr_doBody417_live
#print axioms link_closeArr_doBody417_zero
#print axioms stage2NoEventWalkOfNat32_dec
#print axioms stage2NoEventWalkGetD_getElem?
#print axioms Stage2NoEventWalkTrace.closeArray
#print axioms stage2NoEventWalkParentSepToCloseArr
#print axioms stage2NoEventWalkParentSepArmTop
#print axioms stage2NoEventWalkParentSepArmDeep
#print axioms stage2NoEventWalkParentSepArmPrice
#print axioms stage2NoEventWalkBracketParentSepRow

end LeanLLVM.Refinement
