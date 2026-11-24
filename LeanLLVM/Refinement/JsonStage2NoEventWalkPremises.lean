/-
The no-event walk's completion, from the premises a dispatch supplies.

`JsonStage2NoEventWalkTraverse` proves the loop finishes from the seed's run to the
post-read head `NodeBlock5`, the invariant there and one step per head visit; this
module states the premises that step is written against, produces them from the
record's precondition and the staging, and turns them into the walk's obligation.

**Two layers, because they answer different questions.**

* `Stage2NoEventWalkExit` and `Stage2NoEventWalkRows` are the dispatch's data: the
  terminal route's accumulators, parse relation, counts and report, and the row that
  either closes a count-class cycle to the next head or takes a terminal route.  They
  are assumed, never proved here, exactly as the certified walk's class groups are:
  the terminal arms' own runs (`JsonStage2NoEventWalkTerminal`) are what a producer
  reads to fill them.
* `Stage2NoEventWalkPremises` is the `WalkPremises`-shaped statement the completion
  consumes: at every staging the record admits, a carry and a head state, the seed's
  conclusion at `EntryState`, the seed run to the head, the invariant and its read
  facts there, and the step.

`stage2NoEventWalkPremises_of_rows` builds the second from the first and the lane's
already-proved seed (`stage2NoEventWalkInv_seed`, `stage2NoEventWalkSeedRun`), so the
only data the dispatch still owes is the rows.  `stage2NoEventWalkObligation_of_premises`
derives both conjuncts of `Satisfies` — completion and the post at every behaviour —
and takes no post rule beside the premises: the flush and terminal branches carry the
boundary at their own outcomes, and `runFuel_outcome_unique` carries it to every
behaviour of the run.

**The gap is a parameter of the premises and the obligation, and the seed route is the
default model's.**  `stage2NoEventWalkSeedRun` is stated at an arbitrary selection; the
flush route is proved at `stage2NoEventCalls stage2GapRecover` (`JsonStage2NoEventWalk-
Segment`'s flush lemmas), which is the tree's model of `od_gap_recover` and the record's
own default.  So `stage2NoEventWalkPremises_of_rows` produces the premises at that
selection, while `stage2NoEventWalkObligation_of_premises` is stated at any selection a
premises statement names.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkTraverse
import LeanLLVM.Refinement.JsonStage2NoEventWalkSeed

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The dispatch's data

The terminal route's evidence is the three terminal arms' supply: the accumulators the
acceptance's stores read (`Stage2NoEventWalkAcc`), the parse relation and the fold facts
the acceptance's boundary needs (`Stage2NoEvent K.bs K.arena obs toks`, the count and the
sum), the run to the return and its price, and the report.  It is stated at a head state
because that is where a terminal route starts; the state's own terminal block is what the
route's run reaches.

`Stage2NoEventWalkAcc`'s names are the loop-exit merge's, not the head's: `%idxprom.lcssa`,
`%tokens.8`, `%terms.8` and `%arena.10` are bound at `if.end545` (and `%idxprom.lcssa` at
its `scalar` arms), so the accumulator field belongs at the terminal state's supply and
cannot be a fact of `NodeBlock5`.  The head's carried counts are its own `phi` names
(`%tokens.0.ph1408`, `%terms.0.ph1407`, `%arena.0.ph1406`), which the invariant does not
state either; the step's producers read them. -/

/-- **A terminal route's evidence at one head state.**  The count, the verdict word, the
memory the route returns and its price, the accumulators and the acceptance's parse
relation with its counts, and the walk's report at the returned memory.  All fields are
the terminal arms' own supply; nothing here is derived from the invariant. -/
structure Stage2NoEventWalkExit (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The route's counted steps, and its credit. -/
  q : Nat
  /-- The verdict the route returns. -/
  v : BitVec 64
  /-- The memory the route returns. -/
  m : Mem
  /-- The route's price is inside the head's credit plus the finalisation allowance. -/
  cost : q ≤ stage2NoEventWalkPotential K k + F
  /-- The route's run, at the segment and the returning step. -/
  run : runFuel calls (q + 2) stage2NoEventBody s =
    some (.ret (some (.int 64 v)) m)
  /-- The terminal state's register readings, as the acceptance's stores read them. -/
  acc : Stage2NoEventWalkAcc K s
  /-- The consumer's events, in order. -/
  obs : List ConsumerEvent
  /-- The reference parser's tokens. -/
  toks : List Token
  /-- The events are the document's, at the parser's tokens. -/
  rel : Stage2NoEvent K.bs K.arena obs toks
  /-- The count is the events' length. -/
  obsLen : obs.length = K.tok
  /-- The sum is the events' per-record contribution. -/
  termsEq : K.terms = (obs.map ConsumerEvent.terms).sum
  /-- The walk's report at the returned memory. -/
  report : Stage2NoEventRun K.a12 mem m
  /-- The record's boundary holds where the route returns. -/
  bound : stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 v)

/-- **The dispatch's row at a head**, as data: either the count class's cycle-closing
segment to the next head — the price is the potential's, and the three static numbers do
not move — or a terminal route with its evidence.  Which side is taken is the entry's own
class, so the field is one value of this type and not a per-class table: a table would
have to name the body's dispatched classes, and those rows are the dispatch's to produce,
not this module's to invent. -/
inductive Stage2NoEventWalkRow (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type
  /-- The count class's cycle-closing segment to the next head. -/
  | cont (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat)
      (seg : Stage2NoEventWalkPricedSegment calls mem K k s K' k' s' p)
      (hnep : K'.nep = K.nep) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
      (hk' : lookupName s'.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k')))
      (hpc' : s'.pc = "NodeBlock5") (hlt : k < k') (hk'lt : k' < K.nep) :
      Stage2NoEventWalkRow calls mem F K k s
  /-- The terminal route, with its evidence. -/
  | terminal (exit : Stage2NoEventWalkExit calls mem F K k s) :
      Stage2NoEventWalkRow calls mem F K k s

/-- **The dispatch's rows at a head.**  From a head carrying `k < nep`, one row: the
continuing class's segment or a terminal route. -/
structure Stage2NoEventWalkRows (calls : Calls) (mem : Mem) (F : Nat) where
  row : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkInv K mem s →
    s.pc = "NodeBlock5" →
    lookupName s.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k)) →
    k < K.nep →
    Stage2NoEventWalkRow calls mem F K k s

/-- **The step, from the row.**  The terminal side's boundary is the exit evidence's;
the continuing side is the row's segment with its three static equalities. -/
theorem stage2NoEventWalkStep_of_rows {calls : Calls} {mem : Mem} {F : Nat}
    (h : Stage2NoEventWalkRows calls mem F) :
    Stage2NoEventWalkStep calls mem F := by
  intro K k s hInv hpc hk hklt
  cases h.row K k s hInv hpc hk hklt with
  | cont K' k' s' p seg hnep ha12 hn0 hk' hpc' hlt hk'lt =>
      exact Or.inl ⟨K', k', s', p, seg, hnep, ha12, hn0, hk', hpc', hlt, hk'lt⟩
  | terminal exit =>
      exact Or.inr ⟨exit.q, exit.v, exit.m, exit.cost, exit.run, exit.bound⟩

/-! ### The empty entry stream's route -/

/-- **The flush route at the memory and cursor it is used at.**  The entry block's true
arm, the three zero stores and the document's length, inside the record's finalisation
allowance, with the record's boundary at the returned memory.  The boundary is part of
the supply because the route leaves the loop: no step states it, so the flush is the one
non-step branch of the completion and its post is read here.

The form is the certified `WalkFlushAt`'s, with the boundary added: `nep = 0` implies a
run of at most the allowance at the entry state.  The state is the one the premises
name, so the route is read at the caller's own staging. -/
def Stage2NoEventWalkFlushAt (calls : Calls) (mem : Mem) (next : Nat)
    (a12 : List Value) (stk e c d : Nat) (nep : Nat) (K : Stage2NoEventWalkCarry) :
    Prop :=
  nep = 0 →
    ∃ (q : Nat) (m : Mem), q ≤ stage2NoEventFinalisationAllowance ∧
      runFuel calls q stage2NoEventBody
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
        some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)

/-! ### The premises -/

/-- **What a dispatch supplies, and nothing else.**  At every staging the record
admits: a carry whose static numbers are the argument list's and the four staged
objects' (the seed's own conclusion), the invariant at the entry state, and either the
empty stream's flush or a nonempty stream's seed run to `NodeBlock5` with the invariant
and its read facts there and the loop's step.

The loop branch's run is the seed producer's statement at exactly the head it reports:
`pc = "NodeBlock5"`, `%k.0.ph1404 = 0`, the invariant at the head, and the three reads
the head's first lane and document byte make — `Inv.entries`, `Inv.inside` and
`Inv.doc`, at the staging's memory `mem` (the invariant's fields are stated there, and
the head's run keeps them by its frame), named here as the loop's own input so a
producer need not unfold the invariant to see what it hands the dispatch.  The carry's
field equalities are the seed's conclusion, including `K.xj = K.next0`; the initial
readings are the seed's, so the terminal's post is read at the readings the loop has
moved, not at these.

The `Step` is the counted loop's interface (`JsonStage2NoEventWalkTraverse`): the
continuing branch is a priced segment to the next head, the terminal branch completes
inside the head's credit plus `F`.  The premise names `F = 27`, so the seed's three
steps and the finalisation's two fit the record's `32` (`3 + 27 + 2 = 32`). -/
def Stage2NoEventWalkPremises (gap : Calls := stage2GapRecover) (stk e c d : Nat) : Prop :=
  ∀ (a12 : List Value) (mem : Mem) (next : Nat),
    Γ_stage2_noevent.pre a12 mem next →
    stage2NoEventStagedPre a12 mem next stk e c d →
    ∃ (K : Stage2NoEventWalkCarry),
      K.a12 = a12 ∧ K.stk = stk ∧ K.e = e ∧ K.c = c ∧ K.d = d ∧
      K.next0 = next ∧ K.xj = K.next0 ∧
      K.tok = 0 ∧ K.terms = 0 ∧ K.arena = [] ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) ∧
      ((K.nep = 0 ∧
          Stage2NoEventWalkFlushAt (stage2NoEventCalls gap) mem next a12 stk e c d
            K.nep K) ∨
        (0 < K.nep ∧
          ∃ (sHead : State),
            (∀ n, runFuel (stage2NoEventCalls gap) (3 + n) stage2NoEventBody
                (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
              runFuel (stage2NoEventCalls gap) n stage2NoEventBody sHead) ∧
            Stage2NoEventWalkInv K mem sHead ∧
            sHead.pc = "NodeBlock5" ∧
            lookupName sHead.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 0)) ∧
            readLanes32 mem K.ep K.nep = some K.ent ∧
            (∀ q ∈ K.ent, q < K.n) ∧
            readBytes mem K.b K.n = some K.bs ∧
            Stage2NoEventWalkStep (stage2NoEventCalls gap) mem 27))

/-- **The record's budget carries the finalisation allowance.**  The empty stream's
route costs at most the allowance, and the record's budget is at least it at every
argument list: the ABI list's three read counts are the only terms subtracted from
the two counted charges, so the allowance's `32` is a lower bound. -/
theorem stage2NoEventBudget_ge_finalisation {a12 : List Value} {mem : Mem}
    {b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat}
    (hargs : a12 = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap), .ptr tokensOut,
      .ptr valuesOut, .ptr sumOut, .ptr err])
    (hnLt : n < 2 ^ 64) (hneLt : nep < 2 ^ 64) (hnxLt : nxp < 2 ^ 64) :
    stage2NoEventFinalisationAllowance ≤ stage2NoEventBudget a12 mem := by
  rw [hargs]
  simp only [stage2NoEventBudget, stage2NoEventEntryAllowance,
    stage2NoEventByteAllowance, stage2NoEventPositionAllowance,
    stage2NoEventFinalisationAllowance, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hnLt, Nat.mod_eq_of_lt hneLt, Nat.mod_eq_of_lt hnxLt]
  omega

/-! ### The premises from the record and the rows

The seed's conclusion is `JsonStage2NoEventWalkInv`'s, and the run to the head is
`JsonStage2NoEventWalkSeed`'s.  Both are at the entry state the staging names; the only
fact the seed does not hand back is `1 ≤ K.b`, which is the record's and is recovered
from the two decompositions of the argument list (`stage2NoEventAbiList_eq`).  The
flush route is the segment module's, at the default selection. -/

/-- **The premises from the row bundle.**  The zero branch is the flush route read at
the seed's invariant and parameters; the nonempty branch is the seed run, whose head is
the seed producer's, with the step derived from the row. -/
theorem stage2NoEventWalkPremises_of_rows {stk e c d : Nat}
    (hrows : ∀ (a12 : List Value) (mem : Mem) (next : Nat),
      Γ_stage2_noevent.pre a12 mem next →
      stage2NoEventStagedPre a12 mem next stk e c d →
      Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkPremises stage2GapRecover stk e c d := by
  intro a12 mem next hpre hstaged
  -- the seed's carry and invariant
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj, hKtok, hKterms, hKarena,
    hInvEntry⟩ := stage2NoEventWalkInv_seed hpre hstaged
  -- the record's own witnesses, for `1 ≤ b`
  have hpre' := hpre
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc, hb1, htail, hentries, horder, hinside, hesc,
    hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt, hscLt,
    hneLt, hnxLt, hsep, hwater⟩ := hpre'
  -- the two decompositions of the argument list are one list
  have hAbiPre : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err = a12 := by
    simpa only [Stage2NoEventAbiList] using hargs.symm
  have hAbiInv : Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch
      K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err = K.a12 := by
    simpa only [Stage2NoEventAbiList] using hInvEntry.args_eq.symm
  have hAbi : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err =
      Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
        K.tokensOut K.valuesOut K.sumOut K.err := by
    rw [hAbiPre, ← hK12, hAbiInv]
  obtain ⟨hbK, -⟩ := stage2NoEventAbiList_eq hAbi hnLt hInvEntry.nLt hscLt
    hInvEntry.scratchcapLt hneLt hInvEntry.nepLt hnxLt hInvEntry.nxpLt
  have hb1K : 1 ≤ K.b := hbK ▸ hb1
  have hKxj0 : K.xj = K.next0 := by rw [hKn0]; exact hKxj
  -- the parameters at the entry state, at the seed's carry
  have hpar : Stage2NoEventWalkParams K
      (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) := by
    simpa only [stage2NoEventEntryState, ← hK12, ← hKstk, ← hKe, ← hKc, ← hKd]
      using stage2NoEventEntry_params (K := K) (mem := mem) (next := next)
        hInvEntry.args_eq
  refine ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj0, hKtok, hKterms, hKarena,
    hInvEntry, ?_⟩
  by_cases hzero : K.nep = 0
  · -- the empty entry stream: the entry block's true arm and the flush
    have hflush := stage2NoEventWalkFlushRoute (K := K) (mem := mem)
      (s := EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next)
      hInvEntry hpar rfl (by simpa [EntryState] using hKn0.symm) hKxj0 hb1K hzero
    refine Or.inl ⟨hzero, ?_⟩
    intro _
    obtain ⟨m, hrun, hb⟩ := hflush
    exact ⟨stage2NoEventFlushSteps, m, stage2NoEventFlushSteps_le_finalisation,
      hrun, hb⟩
  · -- entries left: the seed's run to the post-read head
    have hseed := stage2NoEventWalkSeedRun (gap := stage2GapRecover) (K := K) (mem := mem)
      (s0 := EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next)
      hInvEntry hpar rfl (by simpa [EntryState] using hKn0.symm) hKxj0 hb1K (Nat.pos_of_ne_zero hzero)
    obtain ⟨sHead, hrun, hInvHead, hpc, hk0⟩ := hseed
    refine Or.inr ⟨Nat.pos_of_ne_zero hzero, sHead, hrun, hInvHead, hpc, hk0,
      hInvHead.entries, hInvHead.inside, hInvHead.doc, ?_⟩
    exact stage2NoEventWalkStep_of_rows (hrows a12 mem next hpre hstaged)

/-! ### A fixed post at the completion's outcome carries to every behaviour -/

/-- **The post at the run's outcome carries to every behaviour.**  A completion at any
fuel pins the run's outcome; a behaviour at another fuel is the same outcome or the
undefined one, and the undefined outcome is excluded by the completion.  The post is the
record's, not a rule of its own: it is stated at the outcome the completion reaches. -/
theorem stage2NoEventPost_of_completion {calls : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {sE : State} {B : Nat} {oGood : Outcome}
    (hcom : runFuel calls B stage2NoEventBody sE = some oGood)
    (hgood : Γ_stage2_noevent.post args mem next oGood) :
    ∀ o, BehFromState calls stage2NoEventBody sE o →
      Γ_stage2_noevent.post args mem next o := by
  intro o hbeh
  rcases hbeh with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hEq : oGood = Outcome.ub := (runFuel_outcome_unique hn hcom).symm
    rw [hEq] at hgood
    exact hgood.elim
  · have hEq := runFuel_outcome_unique hn hcom
    rw [hEq]
    exact hgood

/-! ### The obligation

`Satisfies`'s two conjuncts are the completion at the record's budget and the post at
every behaviour.  The premises give both routes; the budget identity is the record's
own (`Γ_stage2_noevent_at` reads the twelve-slot prefix, and the adapter appends the
four staging objects), and the post is the boundary at the completion's outcome. -/

/-- **The walk's obligation, from the premises.**  No post rule beside the premises: the
flush carries its boundary and the step's terminal branch carries its own, and
`stage2NoEventPost_of_completion` carries that one outcome to every behaviour of the
run.  The zero branch's budget is the finalisation allowance, which
`stage2NoEventBudget` carries at every argument list; the nonempty branch's is
`potential + 32`, bounded by `32·nep + 8·n + 32` and that by the record's budget. -/
theorem stage2NoEventWalkObligation_of_premises {gap : Calls} {stk e c d : Nat}
    (h : Stage2NoEventWalkPremises gap stk e c d) :
    Stage2NoEventWalkObligation gap stk e c d := by
  intro args mem next hpre
  obtain ⟨a12, rfl, hpre12, hstaged⟩ := hpre
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj, hKtok, hKterms,
    hKarena, hInvEntry, hbr⟩ := h a12 mem next hpre12 hstaged
  have hlen : a12.length = 12 := stage2NoEventPre_length hpre12
  have htake : (stage2NoEventArgs a12 stk e c d).take 12 = a12 :=
    stage2NoEventArgs_take12 a12 hlen stk e c d
  have hbudget : (Γ_stage2_noevent_at stk e c d).budget
      (stage2NoEventArgs a12 stk e c d) mem = stage2NoEventBudget a12 mem := by
    change Γ_stage2_noevent.budget
      (List.take 12 (stage2NoEventArgs a12 stk e c d)) mem = stage2NoEventBudget a12 mem
    rw [htake]
    rfl
  -- the ABI witnesses the budget's lower bound reads
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc12, hb1, htail, hentries, horder, hinside,
    hesc, hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt,
    hscLt, hneLt, hnxLt, hsep, hwater⟩ := hpre12
  refine ⟨?_, ?_⟩
  · rcases hbr with ⟨hzero, hflush⟩ | ⟨hpos, sHead, hseed, hInvHead, hpc, hk0,
      hentries, hinside, hdoc, hstep⟩
    · -- the empty entry stream
      obtain ⟨q, m, hq, hrun, hb⟩ := hflush hzero
      have hqbudget : q ≤ stage2NoEventBudget a12 mem :=
        le_trans hq (stage2NoEventBudget_ge_finalisation hargs hnLt hneLt hnxLt)
      exact ⟨some (.int 64 0), m, by
        rw [hbudget]
        exact runFuel_mono_le hqbudget hrun⟩
    · -- entries left: the seed run, the loop, and the budget
      obtain ⟨q, v, m, hq, hrun, hb⟩ :=
        stage2NoEventWalkLoopFinishes hstep K 0 sHead hInvHead hpc hk0 hpos
      have hcost : 3 + (q + 2) ≤ stage2NoEventBudget a12 mem := by
        have hpot := stage2NoEventWalkPotential_le K 0
        have hble := stage2NoEventWalkBudget_le (mem := mem) (s := sHead) hInvHead
        rw [hK12] at hble
        omega
      have htotal : runFuel (stage2NoEventCalls gap) (3 + (q + 2)) stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) := by
        rw [hseed (q + 2)]
        exact hrun
      exact ⟨some (.int 64 v), m, by
        rw [hbudget]
        exact runFuel_mono_le hcost htotal⟩
  · intro o hbeh
    change Γ_stage2_noevent.post
      (List.take 12 (stage2NoEventArgs a12 stk e c d)) mem next o
    rw [htake]
    rcases hbr with ⟨hzero, hflush⟩ | ⟨hpos, sHead, hseed, hInvHead, hpc, hk0,
      hentries, hinside, hdoc, hstep⟩
    · -- the flush's boundary at the completion's outcome
      obtain ⟨q, m, hq, hrun, hb⟩ := hflush hzero
      have hqbudget : q ≤ stage2NoEventBudget a12 mem :=
        le_trans hq (stage2NoEventBudget_ge_finalisation hargs hnLt hneLt hnxLt)
      have hcom : runFuel (stage2NoEventCalls gap) (stage2NoEventBudget a12 mem)
          stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 0)) m) :=
        runFuel_mono_le hqbudget hrun
      have hgood : Γ_stage2_noevent.post a12 mem next
          (.ret (some (.int 64 0)) m) := by
        show stage2NoEventBoundary a12 mem next m (.int 64 0)
        simpa only [hK12, hKn0] using hb
      exact stage2NoEventPost_of_completion hcom hgood o hbeh
    · -- the terminal branch's boundary at the completion's outcome
      obtain ⟨q, v, m, hq, hrun, hb⟩ :=
        stage2NoEventWalkLoopFinishes hstep K 0 sHead hInvHead hpc hk0 hpos
      have hcost : 3 + (q + 2) ≤ stage2NoEventBudget a12 mem := by
        have hpot := stage2NoEventWalkPotential_le K 0
        have hble := stage2NoEventWalkBudget_le (mem := mem) (s := sHead) hInvHead
        rw [hK12] at hble
        omega
      have htotal : runFuel (stage2NoEventCalls gap) (3 + (q + 2)) stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) := by
        rw [hseed (q + 2)]
        exact hrun
      have hcom : runFuel (stage2NoEventCalls gap) (stage2NoEventBudget a12 mem)
          stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) :=
        runFuel_mono_le hcost htotal
      have hgood : Γ_stage2_noevent.post a12 mem next
          (.ret (some (.int 64 v)) m) := by
        show stage2NoEventBoundary a12 mem next m (.int 64 v)
        simpa only [hK12, hKn0] using hb
      exact stage2NoEventPost_of_completion hcom hgood o hbeh

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkStep_of_rows
#print axioms stage2NoEventWalkPremises_of_rows
#print axioms stage2NoEventPost_of_completion
#print axioms stage2NoEventWalkObligation_of_premises

end LeanLLVM.Refinement
