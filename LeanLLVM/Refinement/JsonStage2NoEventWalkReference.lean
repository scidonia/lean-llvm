/-
The no-event walk's reference-side facts, carried as data.

The walk's rows report `ConsumerEvent`s and the parser's tokens; the transfer
chain (`eventsOfBytes_valueOfEvents_scalar`) reads an `EventRecord` trace and the
parser's tape.  What connects the two is the identity `obs = consumeRecords bs
arena rs` together with the record widths, the used-extent clause and the token
tie.  These are the **reference run's** facts: they are produced by the reference
execution of the same document, not by the walk, and not by the relation.

**Why they are carried and not quantified.**  The relation leaves a string's
`len` free above the decoded slice — `stage2NoEvent_str_len_free` derives
`Stage2NoEvent bs arena (.str key len' off cs :: es) (.string s :: toks)` for
every `len'` whose `take` decodes — so nothing of this shape is a consequence of
a `Stage2NoEvent` derivation.  The refutation's own words: *"The arena form's
`len` is free above the decoded slice: the same token has a derivation at every
`len` whose `take` decodes.  Two such lengths give two different events (their
`terms` differ), so `obs` is not a function of `toks` and the clause at a run's
`obs` is not yet a statement about a record trace `rs`."*  A fact of the shape
below therefore may not be quantified over `Stage2NoEvent`: at a derivation with
a free `len`, `BodiesWithin` can fail while every derivation-side hypothesis
holds.

**What replaces the refuted bridge.**  `Stage2NoEventWalkReferenceFacts` is the
structure the reference run supplies for one acceptance, indexed by that
acceptance's own `(document, arena, observations, tokens, tape)`.
`stage2NoEventWalkReference_valueOfEvents` reads the committed chain at it.
`Stage2NoEventWalkReferenceRows` is the row bundle with those facts **carried in
the accept constructor**, at the witnesses that constructor binds: the accept
route's reference facts travel with the row, so the walk theorem that consumes
them is stated on this augmented row type and never quantifies over a
`Stage2NoEvent` derivation.  `Stage2NoEventWalkReferenceRows.toRows` forgets the
facts back to the assembly's `Stage2NoEventWalkRows`.

The three hypothesis classes, labelled at each statement: the facts and their
fields are **carried data**; `hparse` is **the repository's standing premise**
(the reference parser accepts the document); the rows, the head and the trace are
**the wiring** (the per-class producers' output, the seed run's own evidence).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises
import LeanLLVM.Refinement.JsonEventBridgeFinal

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The reference run's facts for one acceptance

The structure holds exactly what `eventsOfBytes_valueOfEvents_scalar` consumes at
one document, arena, observation list and token list, plus the token tie: the
records and the relation at them, the consumer identity, the record widths, the
used-extent clause and the tape's token list.  The emitted stream is not a field:
it is the records' encoding (`rs.map EventRecord.encodedBytes).flatten`, so the
transfer chain's `hev` is definitional. -/

/-- **The reference run's facts at an acceptance.**  The record trace the
reference run emitted for this document and arena, the relation at the parser's
tokens, the identity `obs = consumeRecords`, the record widths, the used-extent
clause on the reported events, and the parser's token tie.  All of it is
**carried data**: it is the reference execution's, and — as
`stage2NoEvent_str_len_free` shows — it is not a consequence of `Stage2NoEvent`,
so it may not be quantified over derivations.  Stated at the acceptance's own
`(bs, arena, obs, toks, t)`, so the walk's witnesses select it. -/
structure Stage2NoEventWalkReferenceFacts (bs arena : List UInt8)
    (obs : List ConsumerEvent) (toks : List Token) (t : Tape) : Type where
  /-- The emitted record trace the reference run produced.  **carried data**. -/
  rs : List EventRecord
  /-- The record trace is the document's relation at the parser's tokens.
  **carried data**. -/
  records : Stage2Records bs arena rs toks
  /-- The walk's report is the record trace read back by the consumer.
  **carried data**. -/
  consume : obs = consumeRecords bs arena rs
  /-- Every record fits the field widths its bytes are written at.
  **carried data**. -/
  bounded : ∀ r ∈ rs, r.Bounded
  /-- Every reported string's body lies inside the source it names.
  **carried data**. -/
  within : ∀ e ∈ obs, e.BodiesWithin bs arena
  /-- The parser's tape carries exactly the tokens the relation is at.
  **carried data**. -/
  tokens : t.tokens = toks

/-- **The facts transport to an equal document.**  A continuing row keeps the
document read (`Stage2NoEventWalkReferenceHead_doc_eq`), so the terminal
acceptance's facts are the run's facts at the start head's document. -/
def Stage2NoEventWalkReferenceFacts.cast {bs bs' : List UInt8} {arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (h : bs = bs') (f : Stage2NoEventWalkReferenceFacts bs arena obs toks t) :
    Stage2NoEventWalkReferenceFacts bs' arena obs toks t := by
  subst h
  exact f

/-! ### The transfer chain at the facts

The committed chain, applied: the emitted stream's value is the reference's
canonical value.  This is the corollary the walk's accept route calls. -/

/-- **The route's value is the reference value, from the carried facts.**  At one
acceptance — the facts are **carried data**, the parse is **the repository's
standing premise** — the emitted stream's value equals
`scalarCanonValueOfBytes` at the document.  The statement is
`eventsOfBytes_valueOfEvents_scalar` with its record and token premises projected
from the structure; nothing is weakened or added. -/
theorem stage2NoEventWalkReference_valueOfEvents {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (facts : Stage2NoEventWalkReferenceFacts bs arena obs toks t)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    (eventsOfBytes bs (facts.rs.map EventRecord.encodedBytes).flatten arena).bind
        valueOfEvents = scalarCanonValueOfBytes bs :=
  eventsOfBytes_valueOfEvents_scalar facts.records facts.consume facts.within
    facts.bounded hparse facts.tokens rfl

/-! ### The row bundle with the facts carried

The refuted bridge was a function of a derivation; these types carry the facts in
the accept constructor instead, at the witnesses that constructor binds.  The
remaining constructors are the assembly's, unchanged, so the only difference from
`Stage2NoEventWalkRow` is the facts field. -/

/-- **A row with the acceptance's reference facts.**  The continuing side is the
assembly's priced head segment; the accept side is the terminal route with the
reference facts at its own `(K'.arena, obs, toks)` — **carried data** — and the
refuse side is the route's own evidence.  The document of the facts is the row's
own `K.bs`; `…Facts.cast` moves them along a continuing row's document read. -/
inductive Stage2NoEventWalkReferenceRow (t : Tape) (calls : Calls) (mem : Mem)
    (F : Nat) (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type
  /-- The count class's cycle-closing segment to the next head.  **the wiring**. -/
  | cont (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat)
      (seg : Stage2NoEventWalkHeadPricedSegment calls mem K k s K' k' s' p)
      (hnep : K'.nep = K.nep) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
      (hlt : k < k') (hk'lt : k' < K.nep) :
      Stage2NoEventWalkReferenceRow t calls mem F K k s
  /-- The accepted arm: verdict one, the trace, the boundary, and the reference
  run's facts at this acceptance. -/
  | accept (K' : Stage2NoEventWalkCarry) (q : Nat) (m : Mem) (sT : State)
      (route : Stage2NoEventWalkRunTo calls s sT)
      (cost : q ≤ stage2NoEventWalkPotential K k + F)
      (run : runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 1)) m))
      (htok : K.tok < K'.tok) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
      (acc : Stage2NoEventWalkAcceptAcc K' sT)
      (obs : List ConsumerEvent) (toks : List Token)
      (rel : Stage2NoEvent K.bs K'.arena obs toks)
      (obsLen : obs.length = K'.tok)
      (termsEq : K'.terms = (obs.map ConsumerEvent.terms).sum)
      (report : Stage2NoEventRun K'.a12 mem m)
      (bound : stage2NoEventBoundary K'.a12 mem K'.next0 m (.int 64 1))
      (facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t) :
      Stage2NoEventWalkReferenceRow t calls mem F K k s
  /-- The refused arm: verdict zero, the route's evidence and the boundary. -/
  | refuse (q : Nat) (m : Mem) (sT : State)
      (route : Stage2NoEventWalkRunTo calls s sT)
      (cost : q ≤ stage2NoEventWalkPotential K k + F)
      (run : runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 0)) m))
      (ev : Stage2NoEventWalkRefusalEvidence K sT)
      (obs : List ConsumerEvent) (toks : List Token)
      (rel : Stage2NoEvent K.bs K.arena obs toks)
      (obsLen : obs.length = K.tok)
      (termsEq : K.terms = (obs.map ConsumerEvent.terms).sum)
      (report : Stage2NoEventRun K.a12 mem m)
      (bound : stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) :
      Stage2NoEventWalkReferenceRow t calls mem F K k s

/-- **The dispatch's rows, with the facts carried.**  From a head, one row of the
augmented type; the accept route's reference facts ride in that row.  **the
wiring**: this bundle is what the per-class producers supply, and
`…toRows` forgets the facts back to the assembly's. -/
structure Stage2NoEventWalkReferenceRows (t : Tape) (calls : Calls) (mem : Mem)
    (F : Nat) where
  /-- The row at a head.  **the wiring**. -/
  row : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkReferenceRow t calls mem F K k s

/-- **Forgetting the carried facts yields the assembled rows.** -/
def Stage2NoEventWalkReferenceRows.toRows {t : Tape} {calls : Calls} {mem : Mem}
    {F : Nat} (h : Stage2NoEventWalkReferenceRows t calls mem F) :
    Stage2NoEventWalkRows calls mem F where
  row K k s hhead htrace :=
    match h.row K k s hhead htrace with
    | .cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt =>
        .cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt
    | .accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen termsEq
        report bound _facts =>
        .terminal (.accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel
          obsLen termsEq report bound)
    | .refuse q m sT route cost run ev obs toks rel obsLen termsEq report bound =>
        .terminal (.refuse q m sT route cost run ev obs toks rel obsLen termsEq report
          bound)

/-! ### The document survives the continuing rows

The same read as the walk theorem's: a continuing row keeps the argument list's
document word, so two heads at the shared memory read the same bytes. -/

/-- **The document read is the same at two heads of one run.**  Two heads at the
shared memory with one argument list read the same document bytes. -/
theorem stage2NoEventWalkReferenceHead_doc_eq {K K' : Stage2NoEventWalkCarry}
    {mem : Mem} {k k' : Nat} {s s' : State}
    (h : Stage2NoEventWalkHead K mem k s) (h' : Stage2NoEventWalkHead K' mem k' s')
    (ha12 : K'.a12 = K.a12) : K'.bs = K.bs := by
  have hl : Stage2NoEventAbiList K'.b K'.n K'.ep K'.nep K'.xp K'.nxp K'.scratch
      K'.scratchcap K'.tokensOut K'.valuesOut K'.sumOut K'.err =
      Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
        K.tokensOut K.valuesOut K.sumOut K.err := by
    simp only [Stage2NoEventAbiList]
    rw [← h'.inv.args_eq, ha12, h.inv.args_eq]
  obtain ⟨hb, hn, -⟩ :=
    stage2NoEventAbiList_eq hl h'.inv.nLt h.inv.nLt h'.inv.scratchcapLt
      h.inv.scratchcapLt h'.inv.nepLt h.inv.nepLt h'.inv.nxpLt h.inv.nxpLt
  have hdoc : readBytes mem K'.b K'.n = some K'.bs := h'.inv.doc
  rw [hb, hn] at hdoc
  exact Option.some.inj (hdoc.symm.trans h.inv.doc)

/-! ### The run's terminal route, with the facts kept

The loop's strong recursion over the augmented rows, keeping what the accept row
carries: its trace, its counts, and the reference run's facts at that trace, at
the start head's document.  The price and the boundary are unchanged. -/

/-- **The walk's run, from a head, ends at one of the two terminal routes, and
the accepted one carries the reference facts.**  Strong recursion on the entries
left; the continuing row shortens `nep - k` and its segment's credit pays the
difference.  The facts are **carried data**; transport along the continuing rows'
document read is `…Facts.cast`. -/
theorem stage2NoEventWalkReferenceRun_terminal {t : Tape} {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkReferenceRows t calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem) (K' : Stage2NoEventWalkCarry)
        (obs : List ConsumerEvent) (toks : List Token)
        (_facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 1)) m) ∧
        Stage2NoEvent K.bs K'.arena obs toks ∧
        obs.length = K'.tok ∧
        K'.terms = (obs.map ConsumerEvent.terms).sum ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 1)) ∨
      (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 0)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) := by
  have key : ∀ (m : Nat) (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      K.nep - k = m → Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      (∃ (q : Nat) (mr : Mem) (K' : Stage2NoEventWalkCarry)
          (obs : List ConsumerEvent) (toks : List Token)
          (_facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t),
          q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
          runFuel calls (q + 2) stage2NoEventBody s =
            some (.ret (some (.int 64 1)) mr) ∧
          Stage2NoEvent K.bs K'.arena obs toks ∧
          obs.length = K'.tok ∧
          K'.terms = (obs.map ConsumerEvent.terms).sum ∧
          stage2NoEventBoundary K.a12 mem K.next0 mr (.int 64 1)) ∨
        (∃ (q : Nat) (mr : Mem),
          q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
          runFuel calls (q + 2) stage2NoEventBody s =
            some (.ret (some (.int 64 0)) mr) ∧
          stage2NoEventBoundary K.a12 mem K.next0 mr (.int 64 0)) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro K k s hm hhead htrace
        cases hrows.row K k s hhead htrace with
        | cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt =>
            have hmeas : K'.nep - k' < m := by omega
            have hdoc : K'.bs = K.bs :=
              stage2NoEventWalkReferenceHead_doc_eq hhead seg.seg.head' ha12
            have hcredit := seg.credit
            rcases ih (K'.nep - k') hmeas K' k' s' rfl seg.seg.head' seg.seg.trace'
              with
              ⟨q, mr, K'', obs, toks, hfacts, hq, hrun, hrel, hobsLen, hterms, hb⟩ |
                ⟨q, mr, hq, hrun, hb⟩
            · refine Or.inl ⟨p + q, mr, K'', obs, toks, hfacts.cast hdoc, by omega, ?_,
                ?_, hobsLen, hterms, ?_⟩
              · rw [show p + q + 2 = p + (q + 2) from by omega,
                  seg.seg.seg.run (q + 2)]
                exact hrun
              · rw [← hdoc]
                exact hrel
              · rw [← ha12, ← hn0]
                exact hb
            · refine Or.inr ⟨p + q, mr, by omega, ?_, ?_⟩
              · rw [show p + q + 2 = p + (q + 2) from by omega,
                  seg.seg.seg.run (q + 2)]
                exact hrun
              · rw [← ha12, ← hn0]
                exact hb
        | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen
            termsEq report bound facts =>
            refine Or.inl ⟨q, m, K', obs, toks, facts, by omega, run, rel, obsLen,
              termsEq, ?_⟩
            rw [ha12, hn0] at bound
            exact bound
        | refuse q m sT route cost run ev obs toks rel obsLen termsEq report bound =>
            exact Or.inr ⟨q, m, by omega, run, bound⟩
  exact key (K.nep - k) K k s rfl hhead htrace

/-! ### The reference's word

The parser's own accept/refuse, as the ABI's word: one when `parseBytes` accepts,
zero when it refuses. -/

/-- **The reference's word for a document.** -/
def Stage2NoEventWalkReferenceWord (bs : List UInt8) : BitVec 64 :=
  match parseBytes Limits.default (ByteString.literal bs) with
  | .ok _ => 1
  | .error _ => 0

/-- **The reference's word at an accepted document.** -/
theorem stage2NoEventWalkReferenceWord_of_ok {bs : List UInt8} {t : Tape}
    (h : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    Stage2NoEventWalkReferenceWord bs = 1 := by
  unfold Stage2NoEventWalkReferenceWord
  rw [h]

/-! ### The walk's run, to the reference's word and value

The accept route stated against the carried facts, replacing the refuted bridge:
the row bundle is the augmented one, and no `Stage2NoEvent` derivation is
quantified over. -/

/-- **The no-event walk, from a head, reaches the reference's word and value.**

Hypotheses: `hrows` and `hhead`, `htrace` are **the wiring** (the producers' row
bundle and the seed run's head/evidence); `hparse` is **the repository's standing
premise** (the reference parser accepts the document); the facts are **carried
data** — they ride in the accept row, indexed by its own witnesses, not in a
hypothesis over derivations.

On the accepted route the run returns one, the reference's word is one, and
`stage2NoEventWalkReference_valueOfEvents` reads the emitted stream's value as
`scalarCanonValueOfBytes` at `K.bs`.  On the refused route the run returns zero.
The refusal's agreement with the parser stays unstated: the refuse row carries no
fact about `parseBytes`. -/
theorem stage2NoEventWalkReferenceRun_spec {t : Tape} {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkReferenceRows t calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hparse : parseBytes Limits.default (ByteString.literal K.bs) = .ok t) :
    (∃ (q : Nat) (m : Mem) (arena : List UInt8) (obs : List ConsumerEvent)
        (toks : List Token)
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
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) := by
  have hword : Stage2NoEventWalkReferenceWord K.bs = 1 :=
    stage2NoEventWalkReferenceWord_of_ok hparse
  rcases stage2NoEventWalkReferenceRun_terminal hrows hhead htrace with
    ⟨q, m, K', obs, toks, facts, hq, hrun, hrel, -, -, hb⟩ |
      ⟨q, m, hq, hrun, hb⟩
  · refine Or.inl ⟨q, m, K'.arena, obs, toks, facts, hq, ?_, ?_, hrel,
      facts.records, facts.consume, ?_⟩
    · rw [hword]
      exact hrun
    · rw [hword]
      exact hb
    · exact stage2NoEventWalkReference_valueOfEvents facts hparse
  · exact Or.inr ⟨q, m, hq, hrun, hb⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkReferenceFacts.cast
#print axioms stage2NoEventWalkReference_valueOfEvents
#print axioms Stage2NoEventWalkReferenceRows.toRows
#print axioms stage2NoEventWalkReferenceHead_doc_eq
#print axioms stage2NoEventWalkReferenceRun_terminal
#print axioms stage2NoEventWalkReferenceWord_of_ok
#print axioms stage2NoEventWalkReferenceRun_spec

end LeanLLVM.Refinement
