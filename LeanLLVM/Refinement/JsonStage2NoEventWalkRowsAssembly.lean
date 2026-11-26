/-
The no-event walk's rows, assembled at the state the program actually reaches.

`Stage2NoEventWalkRows` (`JsonStage2NoEventWalkPremises`) is a caller-supplied
bundle: one `row` per head.  `JsonStage2NoEventWalkRowsAssemble`'s
`stage2NoEventWalkRows_of_classes` is the row *function* — it reads the head's
class from the entry lane and the document's byte and hands the head to that
class's producer — but it is stated at an abstract `mem` and nothing rooted it in
a state the record's own precondition produces.  This module does that:

* `stage2NoEventWalkSeedEntry` is the seed's carry and invariant at
  `Γ_stage2_noevent.pre` and the four staged objects, with the two facts the seed
  run still needs beyond the invariant (`1 ≤ K.b` and the entry parameters);
* `stage2NoEventWalkRowsAtStart` is the rows function at the record's own
  selection (`stage2GapRecover`, fuel `27`), the four class producers being its
  arguments;
* `stage2NoEventWalkRows_of_start` produces the carry, the invariant at the entry
  state, the base lookups (`readLanes32` on the entry stream, `readBytes` on the
  document) and the rows bundle `R` at the same memory, equal to the function —
  and, on the program's nonempty-stream branch, the seed head `NodeBlock5` with
  its run and with `R.row` there equal to `stage2NoEventWalkSeedRow`, i.e. the
  trace there is `of_zeros` and is not supplied;
* `stage2NoEventWalkReferenceRun_of_start` hands that bundle to
  `stage2NoEventWalkReferenceRun_spec`, so a consumer of the reference run no
  longer supplies the bundle, the head or the trace at the start state.

**What a consumer still supplies.**  The four class producers
(`Stage2NoEventWalk{String,Bracket,Brace,Value}Ready`), each at its own route
staging: the class's continuation route to the next head (the pair cycle, the
string route, the value arm) or its terminal exit.  The accept exit's
`Stage2NoEventWalkReferenceFacts` — the record trace's relation and widths, the
read-back `obs = consumeRecords`, the used-extent clause, and the parser's token
tie, with the two count equations that the wall leaves the deployment
(`JsonStage2NoEventWalkCountsTie`) — ride in those producers' terminal rows
(`Stage2NoEventWalkExit.accept`'s `facts`, the depth-zero `hrefAcc`); the refusal
verdict rides in `refused`/`hdata`.  None of that is computed here.

**What a consumer no longer supplies.**  The bundle `Stage2NoEventWalkRows`, the
head `Stage2NoEventWalkHead K mem 0 sHead` and the trace
`Stage2NoEventWalkTrace K`: the precondition and the staged objects produce the
carry and the invariant, the seed run produces the head and the run to it, and
the trace at that head is `Stage2NoEventWalkTrace.of_zeros` from the seed's own
counters.

**The seed head is at depth zero, and that is where the class producers stop.**
`stage2NoEventWalkSeedRun` reaches `NodeBlock5` with `%sp.0.ph1403 = 0` and
`%frame.0.ph1402 = 0` (`loopHeadPhiCellsAt K 0 0 0 0 520`).  Every container class
producer in this tree needs a positive depth: the pair rows
(`stage2NoEventWalkRow_cont_bracketPair`/`…BracePair`, and their class reductions
`stage2NoEventWalkBracketRow_of_class`/`…BraceRow_of_class`) take
`1 ≤ sp`, `sp < 2 ^ 32`, `1 ≤ fr`, `fr < 2 ^ 8`, and the descend rows
(`stage2NoEventWalkBracketDescendRow_of_inner`, the brace descend rows) take
`Stage2NoEventWalkDescendBranch`/`…PairBranch`, whose `spH` field is `sp ≠ 0`.
At the seed head all four are refuted (the lemmas at the end of this module), so
the *container* classes' continuation and descend cases have no producer there:
a document whose first entry opens `[` or `{` and whose next entry is not the
closer (with room in the stream) is the case the tree does not cover.  The
close-pair cases (`[]`, `{}`) are the depth-zero arm's, and the scalar/string
cases at depth zero are terminal, so their rows are exactly the producers'
terminal exits carrying the deployment's facts above.  The obstruction is stated
as facts, not worked around: nothing here claims a row at a state no producer
covers.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsAssemble
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsReady
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDescend
import LeanLLVM.Refinement.JsonStage2NoEventWalkTraceRun
import LeanLLVM.Refinement.JsonStage2NoEventWalkReference

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

/-! ### The seed's carry at the record's precondition

`stage2NoEventWalkInv_seed` gives the carry and the invariant; the seed run also
needs `1 ≤ K.b` (the record's own, recovered from the two decompositions of the
argument list, as `stage2NoEventWalkPremises_of_rows` does) and the entry
parameters.  Both are packaged here so the start-state theorem is one `obtain`.
-/

/-- **The carry the program enters at**, with its invariant and the two facts
the seed run reads beyond it. -/
theorem stage2NoEventWalkSeedEntry {stk e c d : Nat} {a12 : List Value}
    {mem : Mem} {next : Nat}
    (hpre : Γ_stage2_noevent.pre a12 mem next)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d) :
    ∃ K : Stage2NoEventWalkCarry,
      K.a12 = a12 ∧ K.stk = stk ∧ K.e = e ∧ K.c = c ∧ K.d = d ∧ K.next0 = next ∧
      K.tok = 0 ∧ K.terms = 0 ∧ K.arena = [] ∧ 1 ≤ K.b ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) ∧
      Stage2NoEventWalkParams K
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) := by
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, -, hKtok, hKterms, hKarena,
    hInvEntry⟩ := stage2NoEventWalkInv_seed hpre hstaged
  -- the record's own witnesses, for `1 ≤ b`
  have hpre' := hpre
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc, hb1, htail, hentries, horder, hinside, hesc,
    hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt, hscLt,
    hneLt, hnxLt, hsep, hwater⟩ := hpre'
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
  have hpar : Stage2NoEventWalkParams K
      (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) := by
    simpa only [stage2NoEventEntryState, ← hK12, ← hKstk, ← hKe, ← hKc, ← hKd]
      using stage2NoEventEntry_params (K := K) (mem := mem) (next := next)
        hInvEntry.args_eq
  exact ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKtok, hKterms, hKarena, hb1K,
    hInvEntry, hpar⟩

/-! ### The seed head's depth and frame words

The seed run's environment is the head's read layer over the `phi` layer over the
entry state's base cells, and the `phi` layer is
`loopHeadPhiCellsAt K 0 0 0 0 520`: the depth and the frame are the immediates
zero.  These are the two words that make the container continuation producers
unavailable at the seed head.
-/

/-- **A `phi` cell of the seed head's environment.** -/
theorem stage2NoEventWalkSeedPhiLookup {K : Stage2NoEventWalkCarry} {base : Env}
    {lane : Nat} {byte : UInt8} {n : String} {v : Value}
    (hnot : n ∉ loopHeadReadCellNames)
    (hmem : (n, v) ∈ loopHeadPhiCellsAt K 0 0 0 0 520) :
    lookupName (cells (loopHeadReadCellsAt K 0 0 0 0 520 lane byte)
      (cells (loopHeadPhiCellsAt K 0 0 0 0 520) base)) n = some v := by
  rw [cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; exact hnot)]
  exact cells_lookup_of_mem _ _ hmem (by rw [loopHeadPhiCellsAt_names]; decide)

/-- **The seed head's depth word is zero.** -/
theorem stage2NoEventWalkSeedHead_sp {K : Stage2NoEventWalkCarry} {base : Env}
    {sHead : State} {lane : Nat} {byte : UInt8}
    (henv : sHead.env = cells (loopHeadReadCellsAt K 0 0 0 0 520 lane byte)
      (cells (loopHeadPhiCellsAt K 0 0 0 0 520) base)) :
    lookupName sHead.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 0)) := by
  rw [henv]
  exact stage2NoEventWalkSeedPhiLookup (by rw [loopHeadReadCellNames]; decide)
    (by simp [loopHeadPhiCellsAt])

/-- **The seed head's frame word is zero.** -/
theorem stage2NoEventWalkSeedHead_fr {K : Stage2NoEventWalkCarry} {base : Env}
    {sHead : State} {lane : Nat} {byte : UInt8}
    (henv : sHead.env = cells (loopHeadReadCellsAt K 0 0 0 0 520 lane byte)
      (cells (loopHeadPhiCellsAt K 0 0 0 0 520) base)) :
    lookupName sHead.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 0)) := by
  rw [henv]
  exact stage2NoEventWalkSeedPhiLookup (by rw [loopHeadReadCellNames]; decide)
    (by simp [loopHeadPhiCellsAt])

/-! ### The rows function at the record's selection

`stage2NoEventWalkRows_of_classes` is the function; this names it at the
selection the record uses (`stage2GapRecover`, fuel `27`), so the start-state
theorem and its consumer corollary speak about one definition.  Its cases are the
head table's four classes; the seed head is the index-zero case of the same
function, and `stage2NoEventWalkRowsAtStart_row_seed` records that the trace it
takes there is the seed's derived one.
-/

/-- **The walk's rows at the record's selection**, from one producer per head
class. -/
noncomputable def stage2NoEventWalkRowsAtStart {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracket : Stage2NoEventWalkBracketReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbrace : Stage2NoEventWalkBraceReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkRows_of_classes hstring hbracket hbrace hvalue

/-- **The row at the seed head is the seed row.**  The function's row at
`k = 0` and the seed carry's zeros is `stage2NoEventWalkSeedRow`'s: the trace
argument is `of_zeros`, so the caller of the bundle supplies no events there. -/
theorem stage2NoEventWalkRowsAtStart_row_seed {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracket : Stage2NoEventWalkBracketReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbrace : Stage2NoEventWalkBraceReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    {K : Stage2NoEventWalkCarry} {s : State}
    (hhead : Stage2NoEventWalkHead K mem 0 s)
    (htok : K.tok = 0) (hterms : K.terms = 0) (harena : K.arena = []) :
    (stage2NoEventWalkRowsAtStart hstring hbracket hbrace hvalue).row K 0 s hhead
        (Stage2NoEventWalkTrace.of_zeros htok hterms harena) =
      stage2NoEventWalkSeedRow
        (stage2NoEventWalkRowsAtStart hstring hbracket hbrace hvalue)
        hhead htok hterms harena := rfl

/-! ### The assembly at the start state

The carry, the entry-state invariant, the two base reads and the bundle at the
same memory, which is the function; on the nonempty branch, the seed head with
its run, its zero depth and frame, and the bundle's row there, which is the seed
row.
-/

/-- **The rows at the start state the program reaches.**  From the record's
precondition and the staged objects, at the four class producers: the seed's
carry, the invariant at the entry state, the entry stream's and the document's
base reads, and a rows bundle at the same memory which *is*
`stage2NoEventWalkRowsAtStart` — and, when the stream is not empty, the seed head
with the run to it, its zero depth and frame, and the bundle's row there, which
is `stage2NoEventWalkSeedRow`'s.  The trace is `of_zeros`, not a caller's. -/
theorem stage2NoEventWalkRows_of_start {stk e c d : Nat} {a12 : List Value}
    {mem : Mem} {next : Nat}
    (hpre : Γ_stage2_noevent.pre a12 mem next)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d)
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracket : Stage2NoEventWalkBracketReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbrace : Stage2NoEventWalkBraceReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    ∃ (K : Stage2NoEventWalkCarry) (htok : K.tok = 0) (hterms : K.terms = 0)
      (harena : K.arena = [])
      (R : Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27),
      K.a12 = a12 ∧ K.stk = stk ∧ K.e = e ∧ K.c = c ∧ K.d = d ∧ K.next0 = next ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) ∧
      readLanes32 mem K.ep K.nep = some K.ent ∧
      readBytes mem K.b K.n = some K.bs ∧
      R = stage2NoEventWalkRowsAtStart hstring hbracket hbrace hvalue ∧
      (0 < K.nep →
        ∃ (sHead : State) (hHead : Stage2NoEventWalkHead K mem 0 sHead),
          (∀ n, runFuel (stage2NoEventCalls stage2GapRecover) (3 + n)
              stage2NoEventBody
                (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem
                  next) =
            runFuel (stage2NoEventCalls stage2GapRecover) n stage2NoEventBody sHead) ∧
          lookupName sHead.env "%sp.0.ph1403" =
            some (.int 32 (BitVec.ofNat 32 0)) ∧
          lookupName sHead.env "%frame.0.ph1402" =
            some (.int 8 (BitVec.ofNat 8 0)) ∧
          R.row K 0 sHead hHead
              (Stage2NoEventWalkTrace.of_zeros htok hterms harena) =
            stage2NoEventWalkSeedRow R hHead htok hterms harena) := by
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKtok, hKterms, hKarena, hb1K,
    hInv, hpar⟩ := stage2NoEventWalkSeedEntry hpre hstaged
  refine ⟨K, hKtok, hKterms, hKarena,
    stage2NoEventWalkRowsAtStart hstring hbracket hbrace hvalue,
    hK12, hKstk, hKe, hKc, hKd, hKn0, hInv, hInv.entries, hInv.doc, rfl, ?_⟩
  intro hpos
  obtain ⟨sHead, lane, byte, hrun, hHead, -, henv⟩ :=
    stage2NoEventWalkSeedRun (gap := stage2GapRecover) (K := K) (mem := mem)
      (s0 := EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next)
      hInv hpar rfl (by simpa [EntryState] using hKn0.symm) hb1K hpos
      hKtok hKterms hKarena
  exact ⟨sHead, hHead, hrun,
    stage2NoEventWalkSeedHead_sp henv, stage2NoEventWalkSeedHead_fr henv,
    stage2NoEventWalkRowsAtStart_row_seed hstring hbracket hbrace hvalue
      hHead hKtok hKterms hKarena⟩

/-! ### What the reference run's consumer reads at the start state

The spec's conclusion, named as one abbreviation so the corollary and its
docstring agree.  Its accept disjunct returns the parse equality and the
`Stage2NoEventWalkReferenceFacts` the terminal row carries; its refusal disjunct
returns the run and the boundary.  Nothing here produces those facts.
-/

/-- **The reference run's conclusion at a head**, as
`stage2NoEventWalkReferenceRun_spec` states it. -/
abbrev Stage2NoEventWalkReferenceRunAt (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Prop :=
  (∃ (q : Nat) (m : Mem) (arena : List UInt8) (obs : List ConsumerEvent)
      (toks : List Token) (t : Tape)
      (parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t)
      (facts : Stage2NoEventWalkReferenceFacts K.bs arena obs toks t),
      q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
      runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 (Stage2NoEventWalkReferenceWord K.bs))) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m
        (.int 64 (Stage2NoEventWalkReferenceWord K.bs)) ∧
      Stage2NoEvent K.bs arena obs toks ∧
      Stage2Records K.bs arena facts.rs toks ∧
      obs = consumeRecords K.bs arena facts.rs ∧
      (eventsOfBytes K.bs (facts.rs.map EventRecord.encodedBytes).flatten arena).bind
          valueOfEvents = scalarCanonValueOfBytes K.bs) ∨
    (∃ (q : Nat) (m : Mem),
      q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
      runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0))

/-- **The reference run at the start state.**  The rows, the head and the trace
are the ones `stage2NoEventWalkRows_of_start` produces — the consumer supplies
the four class producers and nothing else at this tier.  The accept disjunct's
`parsed`, relation, records, read-back and value equation are the terminal row's
carried data (the deployment's), not something this theorem computes. -/
theorem stage2NoEventWalkReferenceRun_of_start {stk e c d : Nat} {a12 : List Value}
    {mem : Mem} {next : Nat}
    (hpre : Γ_stage2_noevent.pre a12 mem next)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d)
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracket : Stage2NoEventWalkBracketReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbrace : Stage2NoEventWalkBraceReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    ∃ (K : Stage2NoEventWalkCarry) (htok : K.tok = 0) (hterms : K.terms = 0)
      (harena : K.arena = []),
      K.a12 = a12 ∧ K.next0 = next ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) ∧
      (0 < K.nep →
        ∃ sHead : State,
          Stage2NoEventWalkHead K mem 0 sHead ∧
          Stage2NoEventWalkReferenceRunAt
            (stage2NoEventCalls stage2GapRecover) mem 27 K 0 sHead) := by
  obtain ⟨K, htok, hterms, harena, R, hK12, -, -, -, -, hKn0, hInv,
    -, -, -, hseed⟩ := stage2NoEventWalkRows_of_start hpre hstaged hstring
      hbracket hbrace hvalue
  refine ⟨K, htok, hterms, harena, hK12, hKn0, hInv, ?_⟩
  intro hpos
  obtain ⟨sHead, hHead, _, -, -, -⟩ := hseed hpos
  refine ⟨sHead, hHead, ?_⟩
  exact stage2NoEventWalkReferenceRun_spec
    (calls := stage2NoEventCalls stage2GapRecover) (mem := mem) (F := 27)
    (K := K) (k := 0) (s := sHead) R hHead
    (Stage2NoEventWalkTrace.of_zeros htok hterms harena)

/-! ### The obstruction: the container producers at the seed head

`Stage2NoEventWalkDescendBranch`/`…PairBranch` pin the depth as a nonzero `Nat`
(the push's stack discipline), and the pair rows take `1 ≤ sp`, `sp < 2 ^ 32`,
`1 ≤ fr`, `fr < 2 ^ 8`.  The seed head's `phi` layer is `0` for both words, so
each of those premises is refuted there.  A `[`/`{` head whose next entry is not
the closer is therefore outside every container producer of this tree at the
seed head; the depth-zero closer cases (`[]`, `{}`) are the separate `…ZeroRow`
reductions, whose terminal exits carry the deployment's facts.
-/

/-- **A depth cell at zero admits no bounded positive representative.** -/
theorem stage2NoEventWalkSeedHead_noPosDepth {sHead : State}
    (hspZ : lookupName sHead.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0))) :
    ¬ ∃ sp : Nat,
      lookupName sHead.env "%sp.0.ph1403" =
          some (.int 32 (BitVec.ofNat 32 sp)) ∧
        sp < 2 ^ 32 ∧ 1 ≤ sp := by
  rintro ⟨sp, hsp, hlt, hpos⟩
  have heq : BitVec.ofNat 32 sp = BitVec.ofNat 32 0 := by
    have hh := Option.some.inj (hsp.symm.trans hspZ)
    simpa using hh
  have hmod := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hmod
  simp at hmod
  omega

/-- **A frame cell at zero admits no bounded positive representative.** -/
theorem stage2NoEventWalkSeedHead_noPosFrame {sHead : State}
    (hfrZ : lookupName sHead.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 0))) :
    ¬ ∃ fr : Nat,
      lookupName sHead.env "%frame.0.ph1402" =
          some (.int 8 (BitVec.ofNat 8 fr)) ∧
        fr < 2 ^ 8 ∧ 1 ≤ fr := by
  rintro ⟨fr, hfr, hlt, hpos⟩
  have heq : BitVec.ofNat 8 fr = BitVec.ofNat 8 0 := by
    have hh := Option.some.inj (hfr.symm.trans hfrZ)
    simpa using hh
  have hmod := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hmod
  simp at hmod
  omega

/-- **The descend branch is uninhabited at the seed head.** -/
theorem stage2NoEventWalkSeedHead_noDescend {K : Stage2NoEventWalkCarry}
    {sHead : State}
    (hspZ : lookupName sHead.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0))) :
    ¬ Stage2NoEventWalkDescendBranch K 0 sHead := by
  intro h
  exact (h.sp_ne hspZ) rfl

/-- **The pair branch is uninhabited at the seed head.** -/
theorem stage2NoEventWalkSeedHead_noPair {K : Stage2NoEventWalkCarry}
    {sHead : State}
    (hspZ : lookupName sHead.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0))) :
    ¬ Stage2NoEventWalkPairBranch K 0 sHead := by
  intro h
  exact (h.sp_ne hspZ) rfl

/-- **The pair rows' two words are uninhabited at the seed head.**
`stage2NoEventWalkRow_cont_bracketPair`/`…BracePair` (and their class
reductions) take the depth and frame as `Nat` witnesses with
`sp < 2 ^ 32`, `1 ≤ sp`, `fr < 2 ^ 8`, `1 ≤ fr`; at the seed head no such pair
exists. -/
theorem stage2NoEventWalkSeedHead_noPairWords {sHead : State}
    (hspZ : lookupName sHead.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hfrZ : lookupName sHead.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 0))) :
    ¬ ∃ sp fr : Nat,
      lookupName sHead.env "%sp.0.ph1403" =
          some (.int 32 (BitVec.ofNat 32 sp)) ∧
        lookupName sHead.env "%frame.0.ph1402" =
          some (.int 8 (BitVec.ofNat 8 fr)) ∧
        sp < 2 ^ 32 ∧ 1 ≤ sp ∧ fr < 2 ^ 8 ∧ 1 ≤ fr := by
  rintro ⟨sp, fr, hsp, hfr, hspLt, hspPos, hfrLt, hfrPos⟩
  exact stage2NoEventWalkSeedHead_noPosDepth hspZ ⟨sp, hsp, hspLt, hspPos⟩

/-- **All four container premises fail at the seed head.**  The two branch
predicates and the two bounded positive words the pair rows take are exactly what
the tree's container producers read. -/
theorem stage2NoEventWalkSeedHead_noContainer {K : Stage2NoEventWalkCarry}
    {sHead : State}
    (hspZ : lookupName sHead.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hfrZ : lookupName sHead.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 0))) :
    (¬ Stage2NoEventWalkDescendBranch K 0 sHead) ∧
      (¬ Stage2NoEventWalkPairBranch K 0 sHead) ∧
      (¬ ∃ sp : Nat,
        lookupName sHead.env "%sp.0.ph1403" =
            some (.int 32 (BitVec.ofNat 32 sp)) ∧
          sp < 2 ^ 32 ∧ 1 ≤ sp) ∧
      (¬ ∃ fr : Nat,
        lookupName sHead.env "%frame.0.ph1402" =
            some (.int 8 (BitVec.ofNat 8 fr)) ∧
          fr < 2 ^ 8 ∧ 1 ≤ fr) :=
  ⟨stage2NoEventWalkSeedHead_noDescend hspZ,
    stage2NoEventWalkSeedHead_noPair hspZ,
    stage2NoEventWalkSeedHead_noPosDepth hspZ,
    stage2NoEventWalkSeedHead_noPosFrame hfrZ⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkSeedEntry
#print axioms stage2NoEventWalkSeedPhiLookup
#print axioms stage2NoEventWalkSeedHead_sp
#print axioms stage2NoEventWalkSeedHead_fr
#print axioms stage2NoEventWalkRowsAtStart_row_seed
#print axioms stage2NoEventWalkRows_of_start
#print axioms stage2NoEventWalkReferenceRun_of_start
#print axioms stage2NoEventWalkSeedHead_noPosDepth
#print axioms stage2NoEventWalkSeedHead_noPosFrame
#print axioms stage2NoEventWalkSeedHead_noDescend
#print axioms stage2NoEventWalkSeedHead_noPair
#print axioms stage2NoEventWalkSeedHead_noPairWords
#print axioms stage2NoEventWalkSeedHead_noContainer

end LeanLLVM.Refinement
