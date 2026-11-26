/-
The no-event walk's depth-zero container descend.

`JsonStage2NoEventWalkRowsDescend` proves the descend arm's step at a depth the
head's push can serve: the marker store at `%stk + (%sp - 1)` needs `1 ≤ sp`,
and the arm's staging predicate `Stage2NoEventWalkDescendBranch` states the push's
stack discipline (`sp ≠ 0`, `sp ≤ 519`, `1 ≤ fr` is not needed) and the cycle's
room (`k + 3 < K.nep`).  The seed head has depth zero (`%sp.0.ph1403 = 0`,
`%frame.0.ph1402 = 0`), and `Stage2NoEventWalkRowsAssembly` refutes every premise
that names a positive depth there, so a document whose first entry opens `[` and
whose second entry is not `]` has no producer at the state the walk starts in.

**The seed head is the only depth-zero head, and it is reachable.**  The two
edges into `if.end.peel` (`value.outer.backedge`) carry `%sp.0.ph.be = %sp.4` from
`LeafBlock37` and `%sp.1` from `if.end303`; the first is reached only through
`if.end369`'s `%sp.4 ≠ 0` edge, and the second is `%inc24 = %sp + 1` or a
`%sp.4` of the same kind, so every head after the seed has a positive depth.  The
depth-zero close arms (`if.end327.peel`'s `]` at `%sp = 0`, `if.end19`'s zero
test for `{`) reach `after_value` with `%sp.4 = 0`, whose only successors are
`if.then357`'s terminal dispatch (`if.then360`'s refusal, `accept`).  So the
depth-zero container descend occurs exactly at the seed head — the state
`stage2NoEventWalkSeedRun` reaches — and the fixture's precondition admits
`bs = "[1]"` (`ent = [0, 1, 2]`, `n = 3`): its first byte is `[`, its second is
`1`, and `%sp = %frame = 0`.  The case is reachable, and the walk demands a row
there.

**What the depth-zero arm does not need.**  At `%sp = 0` the `[` route ducks the
push: `if.end45.peel`'s `%tobool46.not.peel` is one and `if.then47.peel` is never
entered, so no marker is written and no stack address is read.  `if.end327.peel`
then reads the entry at `k + 1` and its document byte from the head's own memory.
The continuation dispatch (`if.end`'s thirteen bindings, `NodeBlock15`) is the
positive arm's window: `%7`, `%8`, `%k.0 = k + 1`, `%inc = k + 2`, the two counts,
and `%indvars.iv = %1 + 1`, where `%1 = 0` at the seed.  So the depth-zero step
reaches the *same* `Stage2NoEventWalkBracketDispatch`, and the inner element's
producer — `Stage2NoEventWalkBracketInner`, the tree's missing inner route — is
shared rather than restated.

**The arm's premise shape.**  `Stage2NoEventWalkZeroDescendBranch` names the one
route fact the arm has beyond `Head`: the depth word is zero.  It is a premise
shape sibling to `Stage2NoEventWalkDescendBranch`, not a weakening of it: the
positive predicate is untouched, and the arm's row is
`Stage2NoEventWalkBracketZeroDescendRow_of_inner`, a `cont` row of the same form
as the positive arm's.  `stage2NoEventWalkBracketDescendRow_of_cell` takes the
head's depth word and the positive staging, and splits on the word's residue
(a `Decidable` case, so it eliminates into the row's `Type`): at a zero residue
the zero branch is the head's own cell and the row is this module's, at a
non-zero residue the positive arm's.  A class producer fills
`stage2NoEventWalkBracketReady_of_routes`'s `hdescend` slot with it: the
depth-zero case is the head's own cell and this module's row, and the positive
arm's staging is the caller's route fact.  The slot's *other* premises are not
this arm's to supply — the inner element's route
(`Stage2NoEventWalkBracketInner`) is shared with the positive arm, so it is the
caller's at every depth.

**Why the positive predicate cannot cover it.**  `DescendBranch`'s `live` is
`k + 3 < K.nep`, the pair cycle's four-entry room.  A depth-zero head at the
document `[1]` has `k = 0` and `K.nep = 3`, so even a positive depth would not
supply `live`; and its `sp ≠ 0` field is the seed's own refutation
(`stage2NoEventWalkSeedHead_noDescend`).  The two predicates are disjoint, and
this module covers the side the tree left out.

**What stays a hypothesis.**  The inner element's route
(`Stage2NoEventWalkBracketInner`) — the tree has the dispatch chains from
`NodeBlock15`'s `.loopexit` leaves but no producer for the four classes' inner
routes — and, at positive depth, the push's staging.  Nothing else: the step's
reads, the index arithmetic, the two counts and the base lookups are derived
here from `Head`, the class predicate and the invariant.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDescend
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval (cells)

/-! ### The depth-zero arm's staging

At `%sp = 0` the bracket route does not push, so the arm's only fact beyond
`Head` is the depth word itself.  The witness is pinned the way
`Stage2NoEventWalkDescendBranch.spH` pins its own: one `Nat` with its cell and its
value, so a second cell equation at the same word recovers the residue.
-/

/-- **The depth-zero descend arm's staging**: the depth word is zero.  There is
no push to bound, so `Stage2NoEventWalkDescendBranch`'s `sp ≠ 0`, `sp ≤ 519` and
`live` have no counterpart here, and the fact is about the state alone — it names
no carry and no index.  The witness is a representative and its zero residue, so
a second cell equation at the same word recovers the residue. -/
def Stage2NoEventWalkZeroDescendBranch (s : State) : Prop :=
  ∃ sp : Nat,
    lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      sp % 2 ^ 32 = 0

/-- **The zero depth at any representative**: the cell equation at the state's
own word has a zero residue. -/
theorem Stage2NoEventWalkZeroDescendBranch.sp_zero {s : State}
    (h : Stage2NoEventWalkZeroDescendBranch s)
    {sp' : Nat}
    (h' : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp'))) :
    sp' % 2 ^ 32 = 0 := by
  obtain ⟨sp, hsp, hz⟩ := h
  have heq : BitVec.ofNat 32 sp' = BitVec.ofNat 32 sp := by
    have hh := Option.some.inj (h'.symm.trans hsp)
    simpa using hh
  have hnat := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hnat
  rw [hnat]
  exact hz

/-- **The zero branch's cell at zero.** -/
theorem Stage2NoEventWalkZeroDescendBranch.spH0 {s : State}
    (h : Stage2NoEventWalkZeroDescendBranch s) :
    lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 0)) := by
  obtain ⟨sp, hsp, hz⟩ := h
  have heq : BitVec.ofNat 32 sp = BitVec.ofNat 32 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod]
    exact hz
  rw [← heq]
  exact hsp

/-- **The zero branch at any representative whose residue is zero.** -/
theorem Stage2NoEventWalkZeroDescendBranch.of_cell {s : State} {sp : Nat}
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hz : sp % 2 ^ 32 = 0) :
    Stage2NoEventWalkZeroDescendBranch s :=
  ⟨sp, hsp, hz⟩

/-- **The zero branch at a state whose depth cell reads zero**, at the canonical
representative. -/
theorem Stage2NoEventWalkZeroDescendBranch.of_zero {s : State}
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 0))) :
    Stage2NoEventWalkZeroDescendBranch s :=
  ⟨0, hsp, Nat.zero_mod _⟩

/-! ### The entry and the byte, at the head's own memory

Without the push there is nothing to frame: the entry at `k + 1` and its document
byte are the invariant's reads at the head's memory.
-/

/-- **The depth-zero descend arm's reads**: the entry at `k + 1`, its lane, the
document's byte there, and the byte's value. -/
theorem stage2NoEventWalkBracketZeroDescendReads {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte) :
    ∃ bs4 : List UInt8,
      readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4 ∧
      bytesToNat bs4 = next ∧ bytesToNat bs4 < 2 ^ 32 ∧
      readBytes s.mem
        (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
        = some [nextByte] := by
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
  have hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4
      = some bs4 := by
    rw [hk1toNat]
    have hfour : K.ep + (k + 1) * 4 = K.ep + 4 * (k + 1) := by omega
    rw [hfour]
    exact hread4
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := h.inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hnextLt : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by
    rw [hval4]
    omega
  have hnext64 : (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat
      = next := by
    rw [hval4, stage2NoEventSignExtend_toNat (by omega : next < 2 ^ 64)]
  have hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte] := by
    rw [hnext64]
    have hgd : K.bs.getD next 0 = nextByte := by
      rw [List.getD_eq_getElem?_getD, hbs1]
      rfl
    have hreadDoc : readBytes s.mem (K.b + next) 1 = some [nextByte] := by
      have hbyte := h.inv.docByte hnextLt
      rw [hgd] at hbyte
      simp [readBytes, hbyte]
    exact hreadDoc
  exact ⟨bs4, hlane, hval4, hval4lt, hbyte1⟩

/-! ### The depth-zero descend's step

The head's three-block dispatch, `if.then35.peel`'s bound test at the zero depth,
`if.end45.peel`'s zero arm (no push), `if.end51.peel`'s room test,
`if.end327.peel`'s `]` test at the byte's negation, and `if.end`'s handoff to the
continuation dispatch.  The target window is the positive arm's own
(`Stage2NoEventWalkBracketDispatch`), so the inner element's producer is shared.
-/

/-- **The depth-zero descend's first half**: from a `[` head at depth zero and an
entry at `k + 1` whose byte is not `]`, the walk reaches the continuation
dispatch `NodeBlock15` with the next entry's readings. -/
theorem stage2NoEventWalkBracketZeroDescendStep {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkZeroDescendBranch s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93) :
    ∃ s1 : State,
      Stage2NoEventWalkChain calls mem K s K s1 ∧
      Stage2NoEventWalkBracketDispatch K k s1 next nextByte := by
  classical
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  obtain ⟨sp, fr, hspH, hfrH, h1H, hspLt, -⟩ := h.spPhiBounded
  have hspZero : sp = 0 := by
    have hres := hbranch.sp_zero hspH
    rw [Nat.mod_eq_of_lt hspLt] at hres
    exact hres
  subst hspZero
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    h.bracketCell hent hbs hb
  let S := stage2NoEventWalkAt
    (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) s "if.then35.peel" "LeafBlock1"
  have HD : Stage2NoEventWalkChain calls mem K s K S :=
    stage2NoEventRow_bracket h.inv h.pc h3
  have hspS : lookupName S.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%sp.0.ph1403" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hspH
  have h1S : lookupName S.env "%1" = some (.int 64 (BitVec.ofNat 64 0)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%1" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h1H
  have hinc0 : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  have hincS : lookupName S.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%inc.peel" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hinc0
  have hnepS : lookupName S.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%nep" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h.nepI
  have hnepLt : K.nep < 2 ^ 64 := h.inv.nepLt
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := h.inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hk1nep : k + 1 < K.nep := by
    have hlen : K.ent.length = K.nep :=
      readLanes32_length mem K.ep K.nep K.ent h.inv.entries
    have hi : k + 1 < K.ent.length := (List.getElem?_eq_some_iff.mp hk1).1
    omega
  have hk1max : k + 1 < 2 ^ 32 := by
    have hnepDoc : K.nep ≤ 2 ^ 32 := le_trans h.inv.nepLe hmaxDoc
    omega
  have hincLt0 : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true :=
    BitVec.ult_iff_toNat_lt.2 (by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt hnepLt]
      omega)
  -- the zero-depth chain to `if.end327.peel`, no stack write
  let Z := stage2NoEventWalkNext
    (("%cmp319.not.peel", .int 1 1) ::
      ("%tobool46.not.peel", .int 1 1) ::
      ("%exitcond.peel", .int 1 0) :: S.env)
    (stage2NoEventWalkNext
      (("%tobool46.not.peel", .int 1 1) ::
        ("%exitcond.peel", .int 1 0) :: S.env)
      (stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: S.env)
        S "if.end45.peel") "if.end51.peel")
    "if.end327.peel"
  have LZ : Stage2NoEventWalkChain calls mem K S K Z := by
    have hh := stage2NoEventRow_bracketZero (calls := calls) (K := K) (mem := mem)
      (s := S) (sp := BitVec.ofNat 32 0) (inc := BitVec.ofNat 64 (k + 1))
      (nep := BitVec.ofNat 64 K.nep)
      (Stage2NoEventWalkChain.inv HD) rfl hspS hincS hnepS (by decide) rfl hult
    simpa only [Z] using hh
  have hmemS : S.mem = s.mem := by simp only [S, stage2NoEventWalkAt]
  have hmemZ : Z.mem = s.mem := by
    simp only [Z, stage2NoEventWalkNext]
    exact hmemS
  have hincZ : lookupName Z.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincS
  have hepZ : lookupName Z.env "%ep" = some (.ptr K.ep) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact stage2NoEventWalkBracketDispEnv_lookup (s := s) (by decide) (by decide)
      (by decide) h.epPtr
  have hbZ : lookupName Z.env "%b" = some (.ptr K.b) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact stage2NoEventWalkBracketDispEnv_lookup (s := s) (by decide) (by decide)
      (by decide) h.bPtr
  have h1Z : lookupName Z.env "%1" = some (.int 64 (BitVec.ofNat 64 0)) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1S
  have htrZ : lookupName Z.env "%terms.0.ph1407" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact stage2NoEventWalkBracketDispEnv_lookup (s := s) (by decide) (by decide)
      (by decide) h.termsPhi
  have htokZ : lookupName Z.env "%tokens.0.ph1408" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [Z, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact stage2NoEventWalkBracketDispEnv_lookup (s := s) (by decide) (by decide)
      (by decide) h.tokensPhi
  obtain ⟨bs4, hlane, hval4, hval4lt, hbyte1⟩ :=
    stage2NoEventWalkBracketZeroDescendReads h hk1 hbs1
  have hbytes1 : bytesToNat ([nextByte] : List UInt8) = nextByte.toNat :=
    stage2NoEventWalkBytesToNat_single nextByte
  have hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte])) (BitVec.ofNat 8 93)
      = 0 := by
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
  have hincLt : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := hincLt0
  let Z2 := stage2NoEventWalkNext
    (("%cmp332.peel", .int 1 0) ::
      ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) ::
      ("%arrayidx330.peel",
        .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4)) ::
      Z.env) Z "if.end"
  have L3 : Stage2NoEventWalkLink calls K mem Z K Z2 := by
    have hh := link_ifEnd327peel_false (calls := calls) (K := K) (mem := mem) (s := Z)
      (inc := BitVec.ofNat 64 (k + 1)) (ep := K.ep) (b := K.b)
      (bs4 := bs4) (bs1 := [nextByte])
      (Stage2NoEventWalkChain.inv LZ) rfl hincZ hepZ hbZ hincLt
      (by rw [hmemZ]; exact hlane)
      hval4lt (by rw [hmemZ]; exact hbyte1) hbit
    simpa only [Z2] using hh
  have h6 : lookupName Z2.env "%6" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [Z2, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have h5 : lookupName Z2.env "%5" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [Z2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h1Z2 : lookupName Z2.env "%1" = some (.int 64 (BitVec.ofNat 64 0)) := by
    simp only [Z2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1Z
  have hincZ2 : lookupName Z2.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [Z2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincZ
  have htrZ2 : lookupName Z2.env "%terms.0.ph1407" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [Z2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htrZ
  have htokZ2 : lookupName Z2.env "%tokens.0.ph1408" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [Z2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokZ
  let k0 : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let v7 : BitVec 8 := BitVec.ofNat 8 (bytesToNat [nextByte])
  let v8 : BitVec 32 := BitVec.ofNat 32 (bytesToNat bs4)
  let ivIn : BitVec 64 := BitVec.ofNat 64 0
  let toksIn : BitVec 64 := BitVec.ofNat 64 K.tok
  let termsIn : BitVec 64 := BitVec.ofNat 64 K.terms
  let S3 := stage2NoEventWalkNext
    (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) Z2.env) Z2 "NodeBlock15"
  have L4 : Stage2NoEventWalkLink calls K mem Z2 K S3 := by
    have hh := link_ifEnd_fromEnd327Peel (calls := calls) (K := K) (mem := mem)
      (s := Z2) (v7 := v7) (v8 := v8) (ivIn := ivIn) (k0 := k0)
      (termsIn := termsIn) (toksIn := toksIn)
      L3.inv' rfl
      (by simp only [Z2, Z, stage2NoEventWalkNext])
      h6 h5 h1Z2 hincZ2 htrZ2 htokZ2
    simpa only [S3] using hh
  refine ⟨S3, Stage2NoEventWalkChain.trans HD (Stage2NoEventWalkChain.trans LZ
    (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.tail L4
      (Stage2NoEventWalkChain.nil L4.inv')))), ?_⟩
  have hW := ifEndAllCells_dispatch v7 v8 ivIn k0 termsIn toksIn Z2.env
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
  have hB := stage2NoEventCycleBase (K := K) hA
    (cs := [("%cmp319.not.peel", .int 1 1),
      ("%tobool46.not.peel", .int 1 1), ("%exitcond.peel", .int 1 0)])
    (names := ["%cmp319.not.peel", "%tobool46.not.peel", "%exitcond.peel"])
    rfl (by decide)
  have hC := stage2NoEventCycleBase (K := K) hB
    (cs := [("%cmp332.peel", .int 1 0), ("%6", .int 8 v7),
      ("%arrayidx330.peel", .ptr (K.b + (BitVec.signExtend 64
        (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
      ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4))])
    (names := ["%cmp332.peel", "%6", "%arrayidx330.peel", "%idxprom329.peel",
      "%5", "%arrayidx328.peel"]) rfl (by decide)
  have hbase := stage2NoEventCycleBase (K := K) hC
    (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
    (names := ["%inc", "%indvars.iv", "%terms.0", "%tokens.0", "%tokens.0.in",
      "%terms.0.in", "%k.0", "%indvars.iv.in", "%8", "%7"]) rfl (by decide)
  exact
    { pc := by simp only [S3, stage2NoEventWalkNext]
      pre := by simp only [S3, Z2, stage2NoEventWalkNext]
      byte := by rw [h7]; simp only [v7, hbytes1]
      lane := by rw [h8]; simp only [v8, hval4]
      index := by rw [hk0]
      inc := hinc
      tokens := htok
      terms := htrm
      baseLookups := hbase }

/-! ### The depth-zero descend arm as a row

The same row form as the positive arm's: the head's step to the continuation
dispatch, the inner element's producer (the shared premise), and the class
cycle's return to the next head, composed into a `cont`. -/

/-- **The depth-zero descend arm as a row**: the head's step to the continuation
dispatch (proved above), the inner element's producer (the premise, shared with
the positive arm), and the class cycle's return to the next head. -/
noncomputable def stage2NoEventWalkBracketZeroDescendRow_of_inner {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkZeroDescendBranch s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hinner : Stage2NoEventWalkBracketInner calls mem K k s next nextByte) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨s1, hchain, hdisp⟩ :=
    stage2NoEventWalkBracketZeroDescendStep h hclass hbranch hk1 hbs1 hne
  obtain ⟨j0, hseg0⟩ := Stage2NoEventWalkSegment.of_chain hchain
  obtain ⟨I⟩ := hinner j0 s1 hdisp hseg0
  exact ⟨Stage2NoEventWalkRow.cont I.Kc (I.kc + 1) I.s' (j0 + I.j1 + I.p)
    { seg :=
        { seg := (hseg0.trans I.seg).trans I.cyc.headPriced.seg.seg
          head' := I.cyc.headPriced.seg.head'
          trace' := I.cyc.headPriced.seg.trace' }
      credit := I.price }
    I.hnep I.ha12 I.hn0 I.hlt (by rw [← I.hnep]; exact I.src.klt)⟩

/-- **The descend arm's row at whichever depth the head holds**: the depth-zero
route when the head's own depth word reads zero, the positive route otherwise.
The split is on the word's residue, `Decidable` and so eliminable into the row's
`Type`; at a zero residue the zero staging is the head's own cell
(`Stage2NoEventWalkZeroDescendBranch.of_cell`), and at a non-zero residue the
positive staging is the route's.  A class producer fills
`stage2NoEventWalkBracketReady_of_routes`'s `hdescend` slot with this: the
depth-zero case costs the head and the class, the positive case costs the
positive staging, and both cost the shared inner route
(`hinner : Stage2NoEventWalkBracketInner`) — the slot's third premise, which the
positive arm also takes. -/
noncomputable def stage2NoEventWalkBracketDescendRow_of_cell {calls : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hinner : Stage2NoEventWalkBracketInner calls mem K k s next nextByte)
    {sp : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpos : sp % 2 ^ 32 ≠ 0 → Stage2NoEventWalkDescendBranch K k s) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  by_cases hz : sp % 2 ^ 32 = 0
  · exact stage2NoEventWalkBracketZeroDescendRow_of_inner h hclass
      (Stage2NoEventWalkZeroDescendBranch.of_cell hspH hz) hk1 hbs1 hne hinner
  · exact stage2NoEventWalkBracketDescendRow_of_inner h hclass (hpos hz) hk1 hbs1 hne
      hinner

/-! ### The case is reachable: the zero-depth `[` head's route

The arm is not a spare case.  The seed head is at depth zero
(`stage2NoEventWalkSeedHead_sp`), the record's precondition admits the document
`[1]` (`bs = [91, 49, 93]`, `ent = [0, 1, 2]`, `n = 3`: `stage2NoEventPre` reads
`bs` and the strictly increasing, in-document lanes as data), and
`stage2NoEventWalkSeedRun` reaches `NodeBlock5` for every `0 < nep`.  At such a
head the walk's own byte read makes the class the bracket's and the entry at
`k + 1` the `1`, so the descend arm is the row the walk demands and the positive
staging is uninhabited.  The theorem below states that at a zero-depth head with
those readings, together with the run this module's step takes from it.
-/

/-- **A zero-depth head admits no positive descend staging**: the committed
producer's `sp ≠ 0` field is refuted by the head's own depth cell. -/
theorem stage2NoEventWalkZeroHead_noDescend {K : Stage2NoEventWalkCarry} {k : Nat}
    {s : State} (h : Stage2NoEventWalkDescendBranch K k s)
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 0))) :
    False := by
  obtain ⟨sp, hspH, hlt, hne, -⟩ := h.spH
  have heq : BitVec.ofNat 32 0 = BitVec.ofNat 32 sp := by
    have hh := Option.some.inj (hsp.symm.trans hspH)
    simpa using hh
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt hlt] at hnat
  have hzero : sp = 0 := by
    rw [Nat.zero_mod] at hnat
    exact hnat.symm
  exact hne hzero

/-- **A zero-depth `[` head's descend route.**  At a head whose depth reads zero,
whose first entry opens `[`, and whose second entry is not `]`, the head is in
the bracket class, the zero staging holds, the positive staging does not, and the
walk runs this module's depth-zero descend to the continuation dispatch.  The
seed head of a document beginning `[1` is such a head. -/
theorem stage2NoEventWalkZeroHead_bracketDescendRoute {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (hhead : Stage2NoEventWalkHead K mem 0 s)
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 0)))
    {lane : Nat} {byte0 : UInt8}
    (h0 : K.ent[0]? = some lane) (hb0 : K.bs[lane]? = some byte0)
    (hb0' : byte0.toNat = 91)
    {next : Nat} {nextByte : UInt8}
    (h1 : K.ent[1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93) :
    Stage2NoEventWalkHeadBracketClass K 0 s ∧
      Stage2NoEventWalkZeroDescendBranch s ∧
      (¬ Stage2NoEventWalkDescendBranch K 0 s) ∧
      ∃ s1 : State,
        Stage2NoEventWalkChain calls mem K s K s1 ∧
        Stage2NoEventWalkBracketDispatch K 0 s1 next nextByte := by
  obtain ⟨hread, h3⟩ := stage2NoEventWalkHeadStagingAt hhead h0 hb0
  have hclass : Stage2NoEventWalkHeadBracketClass K 0 s :=
    ⟨lane, byte0, h0, hb0, hread, h3, hb0'⟩
  have hzero : Stage2NoEventWalkZeroDescendBranch s :=
    Stage2NoEventWalkZeroDescendBranch.of_zero hsp
  exact ⟨hclass, hzero, fun hp => stage2NoEventWalkZeroHead_noDescend hp hsp,
    stage2NoEventWalkBracketZeroDescendStep hhead hclass hzero h1 hbs1 hne⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkZeroDescendBranch
#print axioms Stage2NoEventWalkZeroDescendBranch.sp_zero
#print axioms Stage2NoEventWalkZeroDescendBranch.spH0
#print axioms Stage2NoEventWalkZeroDescendBranch.of_cell
#print axioms Stage2NoEventWalkZeroDescendBranch.of_zero
#print axioms stage2NoEventWalkBracketZeroDescendReads
#print axioms stage2NoEventWalkBracketZeroDescendStep
#print axioms stage2NoEventWalkBracketZeroDescendRow_of_inner
#print axioms stage2NoEventWalkBracketDescendRow_of_cell
#print axioms stage2NoEventWalkZeroHead_noDescend
#print axioms stage2NoEventWalkZeroHead_bracketDescendRoute

end LeanLLVM.Refinement
