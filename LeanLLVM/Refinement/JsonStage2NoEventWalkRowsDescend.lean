/-
The no-event walk's container descend arm.

`JsonStage2NoEventWalkRowsReady` divides a bracket or brace head's row by the byte
at `k + 1`: the closer byte takes the empty pair's route, a missing entry the
trailing exit, and **every other byte the descend**.  The closer arm is produced
in-tree; the descend arm has no producer.  This module states that arm as a
route, proves the parts of it the tree's blocks already contain, and names the
parts it does not.

**The route.**  At a `[` head the body pushes the frame (`if.then35.peel`,
`if.end45.peel`, `if.then47.peel`), tests the byte at `k + 1` (`if.end51.peel`,
`if.end327.peel`), and on a byte that is not `]` runs `if.end`'s six `phi`s and
four adds and hands `NodeBlock15` the byte and its lane at index `k + 1`.  At a
`{` head the same shape runs through `if.then9`, the push, and `if.end74`, whose
next-entry read hands `NodeBlock21` the byte at `k + 1` and its lane.

`NodeBlock15` and `NodeBlock21` are the *continuation* dispatch: their class
tables are the head's (`34`/`91`/`123`/else), but their leaves are the
`.loopexit` entries, not the head block.  The descend arm's row is the head's
segment to that dispatch, then the inner element's producer at the class the
dispatch selects, then the class's own return to the next head (the shared
`after_value` cycle, or the object-member pair's `d = 4` cycle).

**What is a hypothesis, not a consequence.**  The entry at `k + 1` and its
document byte — `hk1 : K.ent[k + 1]? = some next`, `hbs1 : K.bs[next]? = some
nextByte` — are **hypotheses** of every statement here; `Inv` supplies only their
existence (`Head.entSucc`/`…closerEntry` derive it from room), never the value.
The descend's staging (`Stage2NoEventWalkDescendBranch`) is a route fact in the
same sense: the seed head has depth and frame zero, so no head carries it.

**What is proved here.**

* `stage2NoEventWalkBracketDescendStep` — the bracket head's chain to the
  continuation dispatch `NodeBlock15`, with the byte, its lane, the advanced
  index, the two counts and the base lookups.  The push, the entry reads, the
  document byte and the `]` test are all derived from `Head` and the invariants;
  nothing is taken as memory staging.  This is the seam
  `stage2NoEventWalkBracketDescendRow_of_inner` consumes.
* `stage2NoEventWalkBraceDescendRow_quote` — the brace descend arm as a row at
  the opening quote.  It re-enters at the committed head-level route
  (`JsonStage2NoEventWalkKeyRoute`'s `stage2NoEventWalkKeyRoute_of_head`: the
  brace prologue, `NodeBlock21`'s quote arm, `LeafBlock17`'s test and the key's
  eighteen blocks) and takes the pair cycle from
  `stage2NoEventWalkCycle_of_pair_price`, whose three steps are named; the
  composed price `18 + 3 ≤ 128` is proved here, so the row has no price premise.
  The brace head's own prefix is therefore **not** a separate export: the
  committed route already states it, and a second one would be an export nothing
  consumes.

**What is named, not proved.**

* `Stage2NoEventWalkDescendBranch` — the descend's own staging: the push's stack
  discipline and the stream's room.  It is a route fact: the seed head has depth
  zero, so no head carries it.
* `Stage2NoEventWalkBracketInner` — the bracket descend's inner element's
  producer.  The tree's class producers are rooted at `NodeBlock5` heads; from
  `NodeBlock15`'s `.loopexit` leaves only the dispatch chains exist, so the
  inner routes for `[`, `{`, `"` and the scalar are not in this tree.  The
  predicate states exactly what they must supply: the inner segment, the
  after-value endpoint's bundle, the shared cycle, and the composed price.
* `Stage2NoEventWalkBraceDescendRefusal` — the brace descend's non-quote branch.
  `LeafBlock17`'s and `LeafBlock19`'s false arms (to `if.then94`'s refusal) are
  not linked in this tree, and the refusal's exit evidence
  (`Stage2NoEventWalkExit.refuse`) is the caller's post.  Its current form is
  `Nonempty (Stage2NoEventWalkExit …)`, which is **weaker than the branch**: it
  also admits `Exit.accept`.  The honest form is the `refuse` constructor's own
  fields; that rewrite waits on `Stage2NoEventWalkExit`'s move from `Prop` to
  `Type` (it must carry the reference facts), which a sibling lane is making.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsReady
import LeanLLVM.Refinement.JsonStage2NoEventWalkKeyRoute

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
open LeanLLVM.Refinement.JsonEntrySteps
  (readBytes_writeBytes_frame readBytes_length)

/-! ### Two lookups through the cell builder

`cells` is a right fold whose cons equation is definitional; these restate the
two canonical sites' lemmas so this module imports neither. -/

/-- A list-level lookup reads through the builder. -/
private theorem descendCellsSome :
    ∀ (cs : List (String × Value)) (n : String) (env : Env) {v : Value},
      lookupName cs n = some v → lookupName (cells cs env) n = some v
  | [], n, env, v, h => by simp only [lookupName_nil] at h; cases h
  | (k, w) :: cs, n, env, v, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h
        cases h
        exact lookupName_cons_self k w (cells cs env)
      · simp only [lookupName_cons_ne w cs hkn] at h
        simp only [cells, lookupName_cons_ne w (cells cs env) hkn]
        exact descendCellsSome cs n env h

/-- **`if.end`'s dispatch readings.**  The four adds and the six phis, at the
names `NodeBlock15` reads them by. -/
theorem ifEndAllCells_dispatch (v7 : BitVec 8) (v8 : BitVec 32)
    (ivIn k0 termsIn toksIn : BitVec 64) (env : Env) :
    lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%7"
        = some (.int 8 v7) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%8"
        = some (.int 32 v8) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%k.0"
        = some (.int 64 k0) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%tokens.0"
        = some (.int 64 (toksIn + BitVec.ofNat 64 1)) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%terms.0"
        = some (.int 64 (termsIn + BitVec.ofNat 64 3)) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%inc"
        = some (.int 64 (k0 + BitVec.ofNat 64 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact descendCellsSome (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) _ env
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)

/-! ### The descend's own staging

The push branch's facts, at the depth and frame a head carries.  None is a
consequence of `Head`: the seed head's depth and frame are zero
(`loopHeadPhiCellsAt K 0 0 0 0 520`), so `1 ≤ sp` and `1 ≤ fr` are false there, and
the branch names them by exclusion.  The names are `…PairBranch`'s (the push
branch is one branch), minus its `comma`, which is the closer's separator and
not the descend's: at a descend head the entry at `k + 2` is the inner element's
byte, not necessarily a comma. -/

/-- **The descend arm's staging**: the push's stack discipline, the frame, and the
next entry's room. -/
structure Stage2NoEventWalkDescendBranch (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop where
  /-- The push's stack guard: a non-zero depth (`if.end45.peel`'s test). -/
  spNe : ∀ sp, lookupName s.env "%sp.0.ph1403" =
    some (.int 32 (BitVec.ofNat 32 sp)) → sp ≠ 0
  /-- The push's room (`%exitcond.peel`): the route continues below 519 bytes. -/
  spLe : ∀ sp, lookupName s.env "%sp.0.ph1403" =
    some (.int 32 (BitVec.ofNat 32 sp)) → sp ≤ 519
  /-- The next head's room: the descend reads two entries past `k` and the
  cycle then needs the head at `k + 4`'s neighbourhood, so the stream must run at
  least to `k + 3`. -/
  live : k + 3 < K.nep

/-! ### The post-push reads

Both descend routes read the entry at `k + 1` and its document byte at the memory
the push left.  The entry stream and the document are ABI regions, so the push
does not disturb either (`Inv.sep`); the read is the invariant's, framed by the
one stored byte.  The two pushes differ only in their address computation. -/

/-- **The bracket descend's post-push reads**: the entry at `k + 1`, its lane, its
document byte, and the byte's value. -/
theorem stage2NoEventWalkBracketDescendReads {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    {sp fr : Nat}
    (_hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32) :
    ∃ bs4 : List UInt8,
      readBytes (writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
        (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
        (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4 ∧
      bytesToNat bs4 = next ∧ bytesToNat bs4 < 2 ^ 32 ∧
      readBytes (writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
        (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
        (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
        = some [nextByte] := by
  have hpush : bracketPushAddr K (BitVec.ofNat 64 sp) = K.stk + (sp - 1) :=
    stage2NoEventWalkBracketPushAddr_eq K hspPos hspLt
  have hk1lt : k + 1 < K.nep := by
    have hlen : K.ent.length = K.nep :=
      readLanes32_length mem K.ep K.nep K.ent h.inv.entries
    have hi : k + 1 < K.ent.length := (List.getElem?_eq_some_iff.mp hk1).1
    omega
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep) (n := K.nep)
    (l := K.ent) h.inv.entriesAt
  obtain ⟨q, bs4, hq, hread4, hval4q⟩ := hget (k + 1) hk1lt
  have hqnext : q = next := by
    rw [hq] at hk1
    exact Option.some.inj hk1
  have hval4 : bytesToNat bs4 = next := by rw [hval4q, hqnext]
  have hk1toNat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := h.inv.nepLt; omega)
  have hlaneW : readBytes (writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4 := by
    rw [hpush,
      show K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4 = K.ep + 4 * (k + 1) from by
        rw [hk1toNat]; omega]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.ep + 4 * (k + 1)) 4 ?_).trans hread4
    rcases h.inv.stackEpOrder with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := h.inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by
    rw [hval4]
    omega
  have hnext64 : (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat = next := by
    rw [hval4, stage2NoEventSignExtend_toNat (by omega : next < 2 ^ 64)]
  have hbyte1W : readBytes (writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte] := by
    rw [hnext64, hpush]
    have hgd : K.bs.getD next 0 = nextByte := by
      rw [List.getD_eq_getElem?_getD, hbs1]; rfl
    have hreadDoc : readBytes s.mem (K.b + next) 1 = some [nextByte] := by
      have hbyte := h.inv.docByte hnextLt
      rw [hgd] at hbyte
      simp [readBytes, hbyte]
    refine (readBytes_writeBytes_frame s.mem (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)
      (K.stk + (sp - 1)) (K.b + next) 1 ?_).trans hreadDoc
    rcases h.inv.stackDocOrder with hord | hord
    · right
      rw [stage2NoEventWalkNatToBytes_one_length]
      omega
    · left; omega
  exact ⟨bs4, hlaneW, hval4, hval4lt, hbyte1W⟩

/-! ### The continuation dispatch's windows

What the two dispatches read from the descend's handoff.  These are the
producer's interface: an inner element's route starts from a state with these
readings, and this module proves the readings at the head's own chain's target. -/

/-- **The bracket continuation dispatch's window**: `NodeBlock15` after `if.end`,
with the next entry's byte and lane, the advanced index, and the two counts. -/
structure Stage2NoEventWalkBracketDispatch (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) (lane : Nat) (byte : UInt8) : Prop where
  pc : s.pc = "NodeBlock15"
  pre : s.pre = some "if.end"
  byte : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 byte.toNat))
  lane : lookupName s.env "%8" = some (.int 32 (BitVec.ofNat 32 lane))
  index : lookupName s.env "%k.0" = some (.int 64 (BitVec.ofNat 64 (k + 1)))
  inc : lookupName s.env "%inc" = some (.int 64 (BitVec.ofNat 64 (k + 2)))
  tokens : lookupName s.env "%tokens.0" =
    some (.int 64 (BitVec.ofNat 64 (K.tok + 1)))
  terms : lookupName s.env "%terms.0" =
    some (.int 64 (BitVec.ofNat 64 (K.terms + 3)))
  baseLookups : Stage2NoEventWalkBaseLookups K s

/-! ### The bracket descend's step

The head's own three-block dispatch, the four push blocks, `if.end327.peel`'s
`]` test at the byte's negation, and `if.end`'s handoff.  The reads are
`stage2NoEventWalkBracketDescendReads`'s; the byte test is the premise. -/

/-- **The bracket descend's first half**: from a `[` head with the descend's
staging and an entry at `k + 1` whose byte is not `]`, the walk reaches the
continuation dispatch `NodeBlock15` with the next entry's readings. -/
theorem stage2NoEventWalkBracketDescendStep {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkDescendBranch K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93) :
    ∃ s1 : State,
      Stage2NoEventWalkChain calls mem K s K s1 ∧
      Stage2NoEventWalkBracketDispatch K k s1 next nextByte := by
  classical
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, -⟩ := h.spPhiBounded
  have hspPos : 1 ≤ sp := by have := hbranch.spNe sp hspH; omega
  have hspLe : sp ≤ 519 := hbranch.spLe sp hspH
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    h.bracketCell hent hbs hb
  let S := stage2NoEventWalkAt
    (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) s "if.then35.peel" "LeafBlock1"
  have HD : Stage2NoEventWalkChain calls mem K s K S :=
    stage2NoEventRow_bracket h.inv h.pc h3
  have hspS : lookupName S.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%sp.0.ph1403" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hspH
  have hfrS : lookupName S.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%frame.0.ph1402" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hfrH
  have h1S : lookupName S.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%1" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h1H
  have hstkS : lookupName S.env "%stk" = some (.ptr K.stk) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%stk" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h.stk
  have hnepS : lookupName S.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%nep" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h.nepI
  have hinc0 : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  have hincS : lookupName S.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%inc.peel" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hinc0
  have hnepLt : K.nep < 2 ^ 64 := h.inv.nepLt
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := h.inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hnepDoc : K.nep ≤ 2 ^ 32 := le_trans h.inv.nepLe hmaxDoc
  have hk1nep : k + 1 < K.nep := by
    have hl := hbranch.live
    omega
  have hk1max : k + 1 < 2 ^ 32 := by omega
  have hposS : (BitVec.ofNat 32 sp).toNat ≠ 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]; omega
  have hle : (BitVec.ofNat 32 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]; omega
  have hpos : 1 ≤ (BitVec.ofNat 64 sp).toNat := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hspLt (by decide : (2:Nat)^32 < 2^64))]
    omega
  have hle1 : (BitVec.ofNat 64 sp).toNat ≤ 519 := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hspLt (by decide : (2:Nat)^32 < 2^64))]
    omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true :=
    BitVec.ult_iff_toNat_lt.2 (by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt hnepLt]
      omega)
  let SP := stage2NoEventWalkStoredAt
    (("%cmp319.not.peel", .int 1 1) ::
      ("%arrayidx50.peel",
        .ptr (K.stk + (BitVec.signExtend 64
          (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
      ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)) ::
      ("%tobool46.not.peel", .int 1 0) ::
      ("%exitcond.peel", .int 1 0) :: S.env)
    S (writeBytes S.mem
      (K.stk + (BitVec.signExtend 64
        (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)).toNat)
      (natToBytes (BitVec.ofNat 8 fr).toNat 1)) "if.end327.peel" "if.end51.peel"
  have LP : Stage2NoEventWalkChain calls mem K S K SP :=
    stage2NoEventRow_bracketPush (Stage2NoEventWalkChain.inv HD) rfl hspS h1S hfrS
      hstkS hincS hnepS hle hposS hpos hle1 hult
  have hincSP : lookupName SP.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincS
  have hepSP : lookupName SP.env "%ep" = some (.ptr K.ep) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.epPtr
  have hbSP : lookupName SP.env "%b" = some (.ptr K.b) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.bPtr
  have hmemSP : SP.mem = writeBytes s.mem (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1) := by
    simp only [SP, S, stage2NoEventWalkStoredAt, stage2NoEventWalkAt,
      bracketPushAddr]
  obtain ⟨bs4, hlaneW, hval4, hval4lt, hbyte1W⟩ :=
    stage2NoEventWalkBracketDescendReads h hk1 hbs1 hspH hspPos hspLe hspLt
  have hbytes1 : bytesToNat ([nextByte] : List UInt8) = nextByte.toNat :=
    stage2NoEventWalkBytesToNat_single nextByte
  have hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte])) (BitVec.ofNat 8 93) = 0 := by
    rw [hbytes1]
    refine stage2NoEvent_eq_zero_of_ne ?_
    intro hh
    apply hne
    have := congrArg BitVec.toNat hh
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by have := nextByte.toNat_lt; simpa using this :
        nextByte.toNat < 2 ^ 8),
      Nat.mod_eq_of_lt (by decide : 93 < 2 ^ 8)] at this
    exact this
  have hincLt : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  let SP2 := stage2NoEventWalkNext
    (("%cmp332.peel", .int 1 0) ::
      ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) ::
      ("%arrayidx330.peel",
        .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4)) ::
      SP.env) SP "if.end"
  have L3 : Stage2NoEventWalkLink calls K mem SP K SP2 := by
    have hh := link_ifEnd327peel_false (calls := calls) (K := K) (mem := mem) (s := SP)
      (inc := BitVec.ofNat 64 (k + 1)) (ep := K.ep) (b := K.b)
      (bs4 := bs4) (bs1 := [nextByte])
      (Stage2NoEventWalkChain.inv LP) rfl hincSP hepSP hbSP hincLt
      (by rw [hmemSP]; exact hlaneW)
      hval4lt (by rw [hmemSP]; exact hbyte1W) hbit
    simpa only [SP2] using hh
  have h6 : lookupName SP2.env "%6" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [SP2, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have h5 : lookupName SP2.env "%5" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [SP2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h1SP2 : lookupName SP2.env "%1" =
      some (.int 64 (BitVec.ofNat 64 sp)) := by
    simp only [SP2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1S
  have hincSP2 : lookupName SP2.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [SP2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincSP
  have htrSP2 : lookupName SP2.env "%terms.0.ph1407" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [SP2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.termsPhi
  have htokSP2 : lookupName SP2.env "%tokens.0.ph1408" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [SP2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.tokensPhi
  let k0 : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let v7 : BitVec 8 := BitVec.ofNat 8 (bytesToNat [nextByte])
  let v8 : BitVec 32 := BitVec.ofNat 32 (bytesToNat bs4)
  let ivIn : BitVec 64 := BitVec.ofNat 64 sp
  let toksIn : BitVec 64 := BitVec.ofNat 64 K.tok
  let termsIn : BitVec 64 := BitVec.ofNat 64 K.terms
  let S3 := stage2NoEventWalkNext
    (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) SP2.env) SP2 "NodeBlock15"
  have L4 : Stage2NoEventWalkLink calls K mem SP2 K S3 := by
    have hh := link_ifEnd_fromEnd327Peel (calls := calls) (K := K) (mem := mem)
      (s := SP2) (v7 := v7) (v8 := v8) (ivIn := ivIn) (k0 := k0)
      (termsIn := termsIn) (toksIn := toksIn)
      L3.inv' rfl
      (by simp only [SP2, SP, stage2NoEventWalkNext, stage2NoEventWalkStoredAt])
      h6 h5 h1SP2 hincSP2 htrSP2 htokSP2
    simpa only [S3] using hh
  refine ⟨S3, Stage2NoEventWalkChain.trans HD (Stage2NoEventWalkChain.trans LP
    (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.tail L4
      (Stage2NoEventWalkChain.nil L4.inv')))), ?_⟩
  have hW := ifEndAllCells_dispatch v7 v8 ivIn k0 termsIn toksIn SP2.env
  have h7 : lookupName S3.env "%7" = some (.int 8 v7) := by
    simp only [S3, stage2NoEventWalkNext]
    exact hW.1
  have h8 : lookupName S3.env "%8" = some (.int 32 v8) := by
    simp only [S3, stage2NoEventWalkNext]
    exact hW.2.1
  have hk0 : lookupName S3.env "%k.0" = some (.int 64 k0) := by
    simp only [S3, stage2NoEventWalkNext]
    exact hW.2.2.1
  have hinc : lookupName S3.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S3, stage2NoEventWalkNext]
    have h := hW.2.2.2.2.2
    have hsum : k0 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 2) := by
      simp only [k0, stage2NoEventOfNatAdd]
    rw [hsum] at h
    exact h
  have htok : lookupName S3.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S3, stage2NoEventWalkNext]
    have h := hW.2.2.2.1
    have hsum : toksIn + BitVec.ofNat 64 1 = BitVec.ofNat 64 (K.tok + 1) := by
      simp only [toksIn, stage2NoEventOfNatAdd]
    rw [hsum] at h
    exact h
  have htrm : lookupName S3.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) := by
    simp only [S3, stage2NoEventWalkNext]
    have h := hW.2.2.2.2.1
    have hsum : termsIn + BitVec.ofNat 64 3 = BitVec.ofNat 64 (K.terms + 3) := by
      simp only [termsIn, stage2NoEventOfNatAdd]
    rw [hsum] at h
    exact h
  have hA := stage2NoEventCycleBase (K := K) (env := s.env) h.baseLookups
    (cs := [("%SwitchLeaf2", .int 1 1), ("%Pivot", .int 1 1),
      ("%Pivot6", .int 1 0)])
    (names := ["%SwitchLeaf2", "%Pivot", "%Pivot6"]) rfl (by decide)
  have hC := stage2NoEventCycleBase (K := K) hA
    (cs := [("%cmp319.not.peel", .int 1 1),
      ("%arrayidx50.peel", .ptr (K.stk + (BitVec.signExtend 64
        (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)).toNat)),
      ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)),
      ("%tobool46.not.peel", .int 1 0), ("%exitcond.peel", .int 1 0)])
    (names := ["%cmp319.not.peel", "%arrayidx50.peel", "%4",
      "%tobool46.not.peel", "%exitcond.peel"]) rfl (by decide)
  have hD := stage2NoEventCycleBase (K := K) hC
    (cs := [("%cmp332.peel", .int 1 0), ("%6", .int 8 v7),
      ("%arrayidx330.peel", .ptr (K.b + (BitVec.signExtend 64
        (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4))])
    (names := ["%cmp332.peel", "%6", "%arrayidx330.peel", "%idxprom329.peel",
      "%5", "%arrayidx328.peel"]) rfl (by decide)
  have hbase := stage2NoEventCycleBase (K := K) hD
    (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
    (names := ["%inc", "%indvars.iv", "%terms.0", "%tokens.0", "%tokens.0.in",
      "%terms.0.in", "%k.0", "%indvars.iv.in", "%8", "%7"]) rfl (by decide)
  exact
    { pc := by simp only [S3, stage2NoEventWalkNext]
      pre := by simp only [S3, SP2, stage2NoEventWalkNext]
      byte := by rw [h7]; simp only [v7, hbytes1]
      lane := by rw [h8]; simp only [v8, hval4]
      index := by rw [hk0]
      inc := hinc
      tokens := htok
      terms := htrm
      baseLookups := hbase }

/-! ### The bracket descend's inner producer

The previous section proves the head's own segment to the continuation dispatch;
this section states what the *inner element* must supply from there, and what row
follows when it does.

The tree's class producers (`…StringReady`, `…ValueReady`, the container rows) are
rooted at `NodeBlock5` heads; from `NodeBlock15`'s `.loopexit` leaves the tree has
only the dispatch chains (`stage2NoEventRow_loopExitBracket`, `…Brace`,
`…String`, `…loopScalar`).  The inner routes — `[` at `if.then35`'s non-peeled
push (the `if.end51` store of the marker `1` has no link in this tree), `{` at
`if.then9.loopexit`, `"` at `string_value.loopexit`, and the scalar at
`scalar.loopexit` — are therefore **not in this tree**.  `…BracketInner` is
exactly their obligation: the inner segment, the endpoint's `CycleSrc`, the shared
cycle, and the composed price.  Its four cases are the dispatch's classes; a
producer for any one of them inhabits it at that class's byte.

The price is inside the premise because the prefix's count is `Segment.of_chain`'s
existential: the caller composes it with its inner route's count and the cycle's
own credit, and only the caller knows the inner count. -/

/-- **The bracket descend's inner element's producer's output**: the inner
class's route from the continuation dispatch to its `after_value` endpoint, the
endpoint's bundle, the shared cycle, and the composed price. -/
structure Stage2NoEventWalkBracketInnerOut (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s1 : State) (j0 : Nat) : Type where
  Kc : Stage2NoEventWalkCarry
  kc : Nat
  sE : State
  s' : State
  j1 : Nat
  p : Nat
  seg : Stage2NoEventWalkSegment calls mem K s1 Kc sE j1
  src : Stage2NoEventWalkCycleSrc calls mem Kc kc sE
  cyc : Stage2NoEventWalkCycle calls mem Kc kc sE 1 s' p
  hnep : Kc.nep = K.nep
  ha12 : Kc.a12 = K.a12
  hn0 : Kc.next0 = K.next0
  hlt : k < kc + 1
  price : j0 + j1 + p + stage2NoEventWalkPotential Kc (kc + 1) ≤
    stage2NoEventWalkPotential K k

/-- **The bracket descend's inner element's producer**, at the continuation
dispatch: from any state on the dispatch's window, reached by a `j0`-step segment,
the inner class's route reaches an `after_value` endpoint with its bundle and the
shared cycle, and the composed price fits the head's credit.  This is the
descend arm's remaining premise; the four dispatch classes' routes are not in
this tree. -/
def Stage2NoEventWalkBracketInner (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (next : Nat)
    (nextByte : UInt8) : Prop :=
  ∀ (j0 : Nat) (s1 : State),
    Stage2NoEventWalkBracketDispatch K k s1 next nextByte →
    Stage2NoEventWalkSegment calls mem K s K s1 j0 →
    Nonempty (Stage2NoEventWalkBracketInnerOut calls mem K k s1 j0)

/-- **The bracket descend arm as a row**: the head's step to the continuation
dispatch (proved here), the inner element's producer (the premise), and the class
cycle's return to the next head.  The composed segment is the head's, and the row
is its `cont`. -/
noncomputable def stage2NoEventWalkBracketDescendRow_of_inner {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkDescendBranch K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hinner : Stage2NoEventWalkBracketInner calls mem K k s next nextByte) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨s1, hchain, hdisp⟩ :=
    stage2NoEventWalkBracketDescendStep h hclass hbranch hk1 hbs1 hne
  obtain ⟨j0, hseg0⟩ := Stage2NoEventWalkSegment.of_chain hchain
  obtain ⟨I⟩ := hinner j0 s1 hdisp hseg0
  exact ⟨Stage2NoEventWalkRow.cont I.Kc (I.kc + 1) I.s' (j0 + I.j1 + I.p)
    { seg :=
        { seg := (hseg0.trans I.seg).trans I.cyc.headPriced.seg.seg
          head' := I.cyc.headPriced.seg.head'
          trace' := I.cyc.headPriced.seg.trace' }
      credit := I.price }
    I.hnep I.ha12 I.hn0 I.hlt (by rw [← I.hnep]; exact I.src.klt)⟩

/-! ### The brace descend's row at the opening quote

The object-member route is in the tree: `stage2NoEventWalkKeyRoute_of_head` runs
the head's prologue, `NodeBlock21`'s quote arm, `LeafBlock17`'s test and the key's
own eighteen blocks to `if.end303`'s entry, yielding the pair endpoint's
`Stage2NoEventWalkPairSrc`.  The pair cycle is the tree's
`stage2NoEventWalkCycle_of_pair_price`, whose three steps are now named, so the
row pays the key route's eighteen and the cycle's three against the four-entry
advance (`Φ(k+4) + 128 ≤ Φ k`, and `21 ≤ 128`).  No price premise remains. -/

/-- **The brace descend arm as a row at the opening quote**: the committed
head-level member route (`…KeyRoute_of_head`) and the priced pair cycle
(`…Cycle_of_pair_price`), with the composed price proved here. -/
noncomputable def stage2NoEventWalkBraceDescendRow_quote {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    {nextByte : UInt8}
    (hb1 : nextByte.toNat = 34)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs4)).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)]
      (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
        (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) s.next = some r0)
    (hstartMem : r0.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
    (hstartNext : r0.next = s.next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + bytesToNat bs4),
       .int 64 (keySub (bytesToNat bs4) (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes
        (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
          (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { s with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next
      = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  obtain ⟨sE, hseg18, hpairNe⟩ :=
    stage2NoEventWalkKeyRoute_of_head (calls := calls) h hent hbs hb hb1
      hspH hfrH hspPos hspLe hspLt hlaneW hval4lt hbyte1W hvAddr hvNext hscratch
      r0 hstart hstartMem hstartNext r hcall hrRet hcallInv lend hlend hlendMem
      htraceEnd hcolon
  obtain ⟨s', hcyc⟩ :=
    stage2NoEventWalkCycle_of_pair_price (calls := calls) (mem := mem) (K := _)
      (k := k) (s := sE) (Classical.choice hpairNe)
  -- the composed price: 18 + 3 against the four-entry advance
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 4) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) h.inv.order (d := 0) (i := k) (j := k + 4)
      (by omega) (by rw [hlen]; omega)
  have hk4 : k + 4 ≤ K.nep := by omega
  have hdrop := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 4) hk4 hent
  have hpotEq : stage2NoEventWalkPotential
      (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
      (k + 4) = stage2NoEventWalkPotential K (k + 4) := rfl
  have hprice : 18 + 3 + stage2NoEventWalkPotential
      (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
      (k + 4) ≤ stage2NoEventWalkPotential K k := by
    rw [hpotEq]
    omega
  exact ⟨Stage2NoEventWalkRow.cont
    (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
    (k + 4) s' (18 + 3)
    { seg :=
        { seg := hseg18.trans hcyc.headPriced.seg.seg
          head' := hcyc.headPriced.seg.head'
          trace' := hcyc.headPriced.seg.trace' }
      credit := hprice }
    rfl rfl rfl (by omega) hvNext⟩

/-! ### The brace descend's other branch: the caller's post

`NodeBlock21`'s other bytes reach `LeafBlock19` (`125`, but that is the closer
arm's), or `LeafBlock17`'s false arm, i.e. `if.then94`'s zero stores and
`cleanup580`'s `ret 0`.  Neither false-arm link is in this tree, and the terminal
row's evidence (`Stage2NoEventWalkExit.refuse`'s run and boundary) is the
caller's post.  The interface below is what such a caller supplies; it is not a
claim that the branch runs. -/

/-- **The brace descend's refusal branch is terminal**: the caller's exit evidence
gives the row. -/
def Stage2NoEventWalkBraceDescendRefusal (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Prop :=
  Nonempty (Stage2NoEventWalkExit calls mem F K k s)

/-- **The refusal branch's row**, from the caller's exit evidence. -/
noncomputable def stage2NoEventWalkBraceDescendRow_of_refusal {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrefuse : Stage2NoEventWalkBraceDescendRefusal calls mem F K k s) :
    Stage2NoEventWalkRow calls mem F K k s :=
  Stage2NoEventWalkRow.terminal (Classical.choice hrefuse)

/-! ### Axiom footprints -/

#print axioms ifEndAllCells_dispatch
#print axioms stage2NoEventWalkBracketDescendReads
#print axioms stage2NoEventWalkBracketDescendStep
#print axioms stage2NoEventWalkBracketDescendRow_of_inner
#print axioms stage2NoEventWalkBraceDescendRow_quote
#print axioms stage2NoEventWalkBraceDescendRow_of_refusal

end LeanLLVM.Refinement
