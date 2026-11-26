/-
The no-event walk's decision, against the reference decoder's verdict.

`JsonStage2NoEventWalkReference.stage2NoEventWalkReferenceRun_spec` pins the run's
word on the accept route — one, together with the reference's parse, its record
data and the boundary at that word; the word is the parse's outcome by definition
on that arm.  Two ties are missing.  First, the refusal disjunct returns only the
run and the boundary, so the walk's zero is never tied to a parser refusal.
Second, no converse takes a run's word back to the parse.  This module states and
proves both, and the accept route's own converse.

# The sharp statement

The walk's returned word is the reference's word
(`stage2NoEventWalkReferenceWord`, one exactly when `parseBytes` accepts and zero
exactly when it refuses).  `stage2NoEventWalkDecisionWord` proves it at one fuel,
inside the potential's credit, with the boundary at that same word: the run's
verdict *is* the reference decoder's verdict, not merely one of two words.

From it, both directions of the decision are corollaries at the rows' own
hypotheses (**the rows**, **the head**, **the trace**):

* `stage2NoEventWalkAccepts_iff` — the walk accepts (its run returns one inside
  the credit) **iff** the reference accepts the document
  (`∃ t, parseBytes … = .ok t`).
* `stage2NoEventWalkRefuses_iff` — the walk refuses (its run returns zero) **iff**
  the reference refuses it, and the right-hand side is the refusal's *witness*
  (`∃ e, parseBytes … = .error e`).

Both directions hold, and they hold for the same reason: `runFuel_outcome_unique`
makes the word the run returns independent of the fuel, so the word theorem's
`q + 2` pins every completing run's word.  There is no verdict gap between the two
sides at the rows: the tree's dispatch decides by the entry's bytes, and the
rows'-carried `parsed`/`refused` fields are what tie that decision to the
reference's.

# What the conditional does not claim

The hypotheses are **the rows**, not the admitted domain.  `Stage2NoEventAdmitted`
(`JsonStage2NoEventAdmission`) gives the reference's parse at the document and no
reference-side fact besides it; it does not produce a row.  So the *unconditional*
reading — "the reference accepts the document, therefore the walk's run returns
one" from the domain's clauses alone — is not this theorem's conclusion: the
decision tie is stated at the rows, and the producer of a row is the deployment's
obligation, not a document predicate.  The accept row's reference-side data is the
parse's: `Stage2NoEventWalkReferenceFacts` reduces to the record supply by
`stage2NoEventWalkReferenceFacts_iff_supply`, and
`JsonStage2NoEventWalkRecordSupplyOfParse` builds that supply from
`parseBytes … = .ok t`'s tokens, so `Stage2NoEventReferenceRecords` holds at every
admitted document (`Stage2NoEventAdmitted.referenceRecords`).  What remains the
deployment's is the two count equations, `JsonStage2NoEventWalkCountsTie`'s pair:
the tree does not compute the walk's registers, and at a chosen supply the term sum
is the trace's own, not a relation-side quantity; the bounded witness separates two
derivations with `obs` free.  The verdict tie does not
choose between relations of the parse's records, and nothing here claims an
obstruction at any document.

What *is* unconditional at the admitted domain, given a caller's rows, is one: the
word is one and no refusal exists (`stage2NoEventWalkDecision_admitted`).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSupplies

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### Reading a verdict word out of an outcome

The run's word is a `Value.int 64`, and `Value.int` is a dependent constructor
(the width is an argument), so the equality of outcomes is read through `HEq`.
Both uses below are at width `64`, where `eq_of_heq` is the word's equality. -/

/-- **The returned `64`-bit word is injective.**  Two completing runs whose
returned words are `64`-bit integers agree at those words; the memory and the
width index are not part of the conclusion. -/
theorem stage2NoEventWalkRet_int_eq {v w : BitVec 64} {m m' : Mem}
    (h : Outcome.ret (some (.int 64 v)) m = Outcome.ret (some (.int 64 w)) m') :
    v = w := by
  rw [Outcome.ret.injEq, Option.some.injEq, Value.int.injEq] at h
  exact eq_of_heq h.1.2

/-! ### The reference's word, read as the decoder's verdict

`Stage2NoEventWalkReferenceWord` is the reference's accept/refuse as the ABI's
word.  Its two values are the two verdicts; the equivalences below say so in the
parser's own vocabulary, so a decision can be stated on `parseBytes` rather than
on the word. -/

/-- **The parser's result is an acceptance or a refusal.**  A case split at the
`ParseResult`, stated so the two word lemmas below need only the existing
`_of_ok`/`_of_error` facts. -/
theorem stage2NoEventWalkParseResult_cases {bs : List UInt8} :
    (∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t) ∨
      (∃ e : ParseError,
        parseBytes Limits.default (ByteString.literal bs) = .error e) := by
  cases h : parseBytes Limits.default (ByteString.literal bs) with
  | ok t => exact Or.inl ⟨t, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

/-- **The reference's word is one exactly at an accepted document.** -/
theorem stage2NoEventWalkReferenceWord_eq_one_iff {bs : List UInt8} :
    Stage2NoEventWalkReferenceWord bs = 1 ↔
      ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t := by
  rcases stage2NoEventWalkParseResult_cases (bs := bs) with ⟨t, ht⟩ | ⟨e, he⟩
  · rw [stage2NoEventWalkReferenceWord_of_ok ht]
    exact ⟨fun _ => ⟨t, ht⟩, fun _ => rfl⟩
  · rw [stage2NoEventWalkReferenceWord_of_error ⟨e, he⟩]
    exact ⟨fun h => absurd h (by decide),
      fun ⟨t, ht⟩ => by rw [he] at ht; cases ht⟩

/-- **The reference's word is zero exactly at a refused document**, with the
parser's error as the witness. -/
theorem stage2NoEventWalkReferenceWord_eq_zero_iff {bs : List UInt8} :
    Stage2NoEventWalkReferenceWord bs = 0 ↔
      Stage2NoEventWalkParseRefusal bs := by
  rcases stage2NoEventWalkParseResult_cases (bs := bs) with ⟨t, ht⟩ | ⟨e, he⟩
  · rw [stage2NoEventWalkReferenceWord_of_ok ht]
    exact ⟨fun h => absurd h (by decide),
      fun ⟨e, he⟩ => by rw [ht] at he; cases he⟩
  · rw [stage2NoEventWalkReferenceWord_of_error ⟨e, he⟩]
    exact ⟨fun _ => ⟨e, he⟩, fun _ => rfl⟩

/-! ### The walk's decision, carried out of the loop

The loop's strong recursion with the terminal row's *verdict* evidence: the
accept route's parse equality, and the refusal route's parser error, both at the
head's document.  The continuing row keeps the document read, so the evidence
travels back along it by the same `hdoc` the existing terminal recursion derives.

This mirrors `stage2NoEventWalkReferenceRun_terminal`'s strong recursion over the
same rows, and it is deliberately a second copy: that theorem collapses both arms
to the run, its price and the boundary, so it cannot hand a consumer the terminal
route's verdict evidence.  This one narrows each disjunct to exactly the verdict —
the returned word and the parser fact behind it — and adds nothing else, so no
record trace or value equation is carried; those remain
`stage2NoEventWalkReferenceRun_spec`'s business.  The two copies should move
together if the row interface changes. -/

/-- **The run's terminal verdict, with the reference's own witness.**  From a head
the run completes inside the potential plus `F`, returning one with the parser's
tape and parse equality, or zero with the parser's error. -/
theorem stage2NoEventWalkDecisionRun {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem) (t : Tape),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 1)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 1) ∧
        parseBytes Limits.default (ByteString.literal K.bs) = .ok t) ∨
      (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 0)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) ∧
        Stage2NoEventWalkParseRefusal K.bs) := by
  have key : ∀ (m : Nat) (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      K.nep - k = m → Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      (∃ (q : Nat) (mr : Mem) (t : Tape),
          q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
          runFuel calls (q + 2) stage2NoEventBody s =
            some (.ret (some (.int 64 1)) mr) ∧
          stage2NoEventBoundary K.a12 mem K.next0 mr (.int 64 1) ∧
          parseBytes Limits.default (ByteString.literal K.bs) = .ok t) ∨
        (∃ (q : Nat) (mr : Mem),
          q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
          runFuel calls (q + 2) stage2NoEventBody s =
            some (.ret (some (.int 64 0)) mr) ∧
          stage2NoEventBoundary K.a12 mem K.next0 mr (.int 64 0) ∧
          Stage2NoEventWalkParseRefusal K.bs) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro K k s hm hhead htrace
        cases hrows.row K k s hhead htrace with
        | cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt =>
            -- the continuing row keeps the document word
            have hdoc : K'.bs = K.bs := by
              have hl : Stage2NoEventAbiList K'.b K'.n K'.ep K'.nep K'.xp K'.nxp
                  K'.scratch K'.scratchcap K'.tokensOut K'.valuesOut K'.sumOut K'.err =
                  Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch
                    K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err := by
                simp only [Stage2NoEventAbiList]
                rw [← seg.seg.head'.inv.args_eq, ha12, hhead.inv.args_eq]
              obtain ⟨hb, hn, -⟩ :=
                stage2NoEventAbiList_eq hl seg.seg.head'.inv.nLt hhead.inv.nLt
                  seg.seg.head'.inv.scratchcapLt hhead.inv.scratchcapLt
                  seg.seg.head'.inv.nepLt hhead.inv.nepLt seg.seg.head'.inv.nxpLt
                  hhead.inv.nxpLt
              have hd : readBytes mem K'.b K'.n = some K'.bs := seg.seg.head'.inv.doc
              rw [hb, hn] at hd
              exact Option.some.inj (hd.symm.trans hhead.inv.doc)
            have hmeas : K'.nep - k' < m := by omega
            have hcredit := seg.credit
            rcases ih (K'.nep - k') hmeas K' k' s' rfl seg.seg.head' seg.seg.trace'
              with
              ⟨q, mr, t, hq, hrun, hb, hparsed⟩ | ⟨q, mr, hq, hrun, hb, href⟩
            · refine Or.inl ⟨p + q, mr, t, by omega, ?_, ?_, ?_⟩
              · rw [show p + q + 2 = p + (q + 2) from by omega,
                  seg.seg.seg.run (q + 2)]
                exact hrun
              · rw [← ha12, ← hn0]
                exact hb
              · rw [← hdoc]
                exact hparsed
            · refine Or.inr ⟨p + q, mr, by omega, ?_, ?_, ?_⟩
              · rw [show p + q + 2 = p + (q + 2) from by omega,
                  seg.seg.seg.run (q + 2)]
                exact hrun
              · rw [← ha12, ← hn0]
                exact hb
              · rw [← hdoc]
                exact href
        | terminal exit =>
            cases exit with
            | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen
                termsEq report bound t parsed facts =>
                refine Or.inl ⟨q, m, t, by omega, run, ?_, parsed⟩
                rw [ha12, hn0] at bound
                exact bound
            | refuse q m sT route cost run ev _trace obs toks rel obsLen termsEq
                report bound refused =>
                exact Or.inr ⟨q, m, by omega, run, bound, refused⟩
  exact key (K.nep - k) K k s rfl hhead htrace

/-! ### The verdict tie -/

/-- **The run's word is the reference decoder's word.**  At one fuel inside the
potential's credit, the walk returns exactly
`Stage2NoEventWalkReferenceWord K.bs`, and its boundary is stated at that word.
The accept route's word is one because the parser accepted at the row's tape; the
refusal route's is zero because the parser's error is the row's carried
witness. -/
theorem stage2NoEventWalkDecisionWord {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    ∃ (q : Nat) (m : Mem),
      q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
      runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 (Stage2NoEventWalkReferenceWord K.bs))) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m
        (.int 64 (Stage2NoEventWalkReferenceWord K.bs)) := by
  rcases stage2NoEventWalkDecisionRun hrows hhead htrace with
    ⟨q, m, t, hq, hrun, hb, hparsed⟩ | ⟨q, m, hq, hrun, hb, hrefused⟩
  · have hw := stage2NoEventWalkReferenceWord_of_ok hparsed
    exact ⟨q, m, hq, by rw [hw]; exact hrun, by rw [hw]; exact hb⟩
  · have hw := stage2NoEventWalkReferenceWord_of_error hrefused
    exact ⟨q, m, hq, by rw [hw]; exact hrun, by rw [hw]; exact hb⟩

/-- **The walk accepts exactly the documents the reference decoder admits.**  The
left side is the walk's own decision — a run that returns one inside the
potential's credit — and the right side the reference's (`parseBytes` accepts).
Forward, the run's word is the reference's word by outcome uniqueness; backward,
the word is one and the word theorem produces the run. -/
theorem stage2NoEventWalkAccepts_iff {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 1)) m)) ↔
      ∃ t : Tape, parseBytes Limits.default (ByteString.literal K.bs) = .ok t := by
  constructor
  · rintro ⟨q, m, -, hrun⟩
    obtain ⟨qw, mw, -, hrunw, -⟩ := stage2NoEventWalkDecisionWord hrows hhead htrace
    have hEq := runFuel_outcome_unique hrun hrunw
    have h1 : (1 : BitVec 64) = Stage2NoEventWalkReferenceWord K.bs :=
      stage2NoEventWalkRet_int_eq hEq
    exact stage2NoEventWalkReferenceWord_eq_one_iff.mp h1.symm
  · rintro ⟨t, ht⟩
    obtain ⟨q, m, hq, hrun, -⟩ := stage2NoEventWalkDecisionWord hrows hhead htrace
    have hw : Stage2NoEventWalkReferenceWord K.bs = 1 :=
      stage2NoEventWalkReferenceWord_of_ok ht
    rw [hw] at hrun
    exact ⟨q, m, hq, hrun⟩

/-- **The walk refuses exactly the documents the reference decoder refuses**, and
the right side carries the parser's error.  Forward, the run's zero word is the
reference's word by outcome uniqueness; backward, the refusal makes the word zero
and the word theorem produces the zero run. -/
theorem stage2NoEventWalkRefuses_iff {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 0)) m)) ↔
      Stage2NoEventWalkParseRefusal K.bs := by
  constructor
  · rintro ⟨q, m, -, hrun⟩
    obtain ⟨qw, mw, -, hrunw, -⟩ := stage2NoEventWalkDecisionWord hrows hhead htrace
    have hEq := runFuel_outcome_unique hrun hrunw
    have h0 : (0 : BitVec 64) = Stage2NoEventWalkReferenceWord K.bs :=
      stage2NoEventWalkRet_int_eq hEq
    exact stage2NoEventWalkReferenceWord_eq_zero_iff.mp h0.symm
  · intro hrefused
    obtain ⟨q, m, hq, hrun, -⟩ := stage2NoEventWalkDecisionWord hrows hhead htrace
    have hw : Stage2NoEventWalkReferenceWord K.bs = 0 :=
      stage2NoEventWalkReferenceWord_of_error hrefused
    rw [hw] at hrun
    exact ⟨q, m, hq, hrun⟩

/-! ### The admitted domain

`Stage2NoEventAdmitted` gives the reference's parse and its word one; it does not
give the rows.  With a caller's rows at the document, the walk's word is one and
no refusal exists. -/

/-- **At an admitted document, the walk's word is one.**  The domain's parse makes
the reference's word one, and the word theorem carries it to the run.

The three conjuncts do not need the same hypotheses.  The first two — the word is
one and no refusal exists — follow from `hadm` and the document tie `hK` alone;
they mention no state, so the rows, head and trace are not their hypotheses.  The
third, the run at word one, is the row-dependent one: it is
`stage2NoEventWalkDecisionWord` read at the admission's word.  A caller that wants
only the verdict therefore does not need the rows; a caller that wants the run
does, and admission produces none of them. -/
theorem stage2NoEventWalkDecision_admitted {bs : List UInt8}
    (hadm : Stage2NoEventAdmitted bs)
    {calls : Calls} {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat}
    {s : State} (hK : K.bs = bs)
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    Stage2NoEventWalkReferenceWord K.bs = 1 ∧
      ¬ Stage2NoEventWalkParseRefusal K.bs ∧
      ∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 1)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 1) := by
  have hw : Stage2NoEventWalkReferenceWord K.bs = 1 := by
    rw [hK]; exact hadm.referenceWord_eq_one
  refine ⟨hw, ?_, ?_⟩
  · rw [hK]; exact hadm.not_parseRefusal
  · obtain ⟨q, m, hq, hrun, hb⟩ := stage2NoEventWalkDecisionWord hrows hhead htrace
    rw [hw] at hrun hb
    exact ⟨q, m, hq, hrun, hb⟩

/-! ### The accept route's reference-side obligation

The decision tie is indexed by **the rows**, and the accept row's reference data
is the parse's.  `JsonStage2NoEventWalkRecordSupplyOfParse` derives a
relation-satisfying trace from `parseBytes … = .ok t`'s tokens, so
`Stage2NoEventReferenceRecords` holds at every admitted document
(`Stage2NoEventAdmitted.referenceRecords`); which trace is chosen is harmless, as
the transfer chain's `value` holds for every facts value at the same document.
What remains the deployment's is the two count equations — the walk's
counted-token and term registers against that trace
(`JsonStage2NoEventWalkCountsTie`, whose bounded witness separates two
derivations with `obs` free).  The verdict tie is independent of which relation
supplies the records. -/

/-- **An accept supply gives the record obligation.**  The bridge from the accept
route's data to the one-statement obligation: the supply's tape, its parse equality
and its record trace are `Stage2NoEventReferenceRecords`. -/
theorem stage2NoEventWalkAccept_obligation {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') :
    Stage2NoEventReferenceRecords K.bs K'.arena :=
  ⟨s.t, s.parsed, ⟨s.recordsSupply⟩⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkRet_int_eq
#print axioms stage2NoEventWalkParseResult_cases
#print axioms stage2NoEventWalkReferenceWord_eq_one_iff
#print axioms stage2NoEventWalkReferenceWord_eq_zero_iff
#print axioms stage2NoEventWalkDecisionRun
#print axioms stage2NoEventWalkDecisionWord
#print axioms stage2NoEventWalkAccepts_iff
#print axioms stage2NoEventWalkRefuses_iff
#print axioms stage2NoEventWalkDecision_admitted
#print axioms stage2NoEventWalkAccept_obligation

end LeanLLVM.Refinement
