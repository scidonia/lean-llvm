/-
The no-event walk's reference-side facts, read off the accept route.

The walk's rows report `ConsumerEvent`s and the parser's tokens; the transfer
chain (`eventsOfBytes_valueOfEvents_scalar`) reads an `EventRecord` trace and the
parser's tape.  What connects the two is the identity `obs = consumeRecords bs
arena rs` together with the record widths, the used-extent clause and the token
tie.  These are the **reference run's** facts: they are produced by the reference
execution of the same document, not by the walk, and not by the relation.

**Where they live.**  `Stage2NoEventWalkReferenceFacts` is declared beside the
exit that carries it, in `JsonStage2NoEventWalkPremises`: the exit is `Type`, and
its accept constructor binds the parser's tape and the facts at the acceptance's
own `(bs, arena, obs, toks)`.  So the walk theorem is stated on the assembly's
own row bundle, `Stage2NoEventWalkRows`, and reads the facts from the terminal
constructor of the row it lands on — no second row type, no forgetting map.

**Why they are carried and not quantified.**  The relation leaves a string's
`len` free above the decoded slice — `stage2NoEvent_str_len_free` derives
`Stage2NoEvent bs arena (.str key len' off cs :: es) (.string s :: toks)` for
every `len'` whose `take` decodes — so nothing of this shape is a consequence of
a `Stage2NoEvent` derivation.  The refutation's own words: *"The arena form's
`len` is free above the decoded slice: the same token has a derivation at every
`len` whose `take` decodes.  Two such lengths give two different events (their
`terms` differ), so `obs` is not a function of `toks` and the clause at a run's
`obs` is not yet a statement about a record trace `rs`."*  A fact of that shape
therefore may not be quantified over `Stage2NoEvent`: at a derivation with a free
`len`, `BodiesWithin` can fail while every derivation-side hypothesis holds.

**The two hypothesis classes, labelled at each statement.**

* **the rows** — `hrows : Stage2NoEventWalkRows calls mem F`, the assembly's
  bundle; its terminal rows carry the exit whose accept arm carries the tape, the
  parse equality at it, and the facts at the acceptance's own witnesses.
* **the head tier** — `hhead` and `htrace`: a head (the invariant, the
  parameters, the index below the entry count and the head block's read values)
  and the walk's accumulated output evidence there.

**What a caller must produce.**  The rows (the per-class producers' output, whose
accept terminals are built at the reference parser's own tape) and the head with
its trace (the seed run's evidence).  There is no separate supply: the tie
between the facts' tape and the parser's result is the accept constructor's
`parsed` field, carried per acceptance.  A hypothesis over the open facts type
cannot state that tie — the structure's only tape field is `t.tokens = toks`, so
a facts value re-indexes at any tape with the same token list, and a `∀` over the
type is refuted by that re-indexing — which is why the tie is a field.

The deleted alternative was a parallel augmented row type that fixed one tape for
the whole run; the exit already carries the tape, the facts and the parse
equality, so that copy was duplicated behaviour.
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


/-- **The facts transport to an equal document.**  A continuing row keeps the
document read (the recursion's two-heads-one-document step), so the terminal
acceptance's facts are the run's facts at the start head's document. -/
def Stage2NoEventWalkReferenceFacts.cast {bs bs' : List UInt8} {arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (h : bs = bs') (f : Stage2NoEventWalkReferenceFacts bs arena obs toks t) :
    Stage2NoEventWalkReferenceFacts bs' arena obs toks t := by
  subst h
  exact f

/-! ### The transfer chain at the facts -/

/-- **The route's value is the reference value, from the carried facts.**  At one
acceptance — the facts and the parse equality are the accept row's carried data —
the emitted stream's value equals `scalarCanonValueOfBytes` at the document.  The
statement is `eventsOfBytes_valueOfEvents_scalar` with its record and token
premises projected from the structure; nothing is weakened or added. -/
theorem stage2NoEventWalkReference_valueOfEvents {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (facts : Stage2NoEventWalkReferenceFacts bs arena obs toks t)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    (eventsOfBytes bs (facts.rs.map EventRecord.encodedBytes).flatten arena).bind
        valueOfEvents = scalarCanonValueOfBytes bs :=
  eventsOfBytes_valueOfEvents_scalar facts.records facts.consume facts.within
    facts.bounded hparse facts.tokens rfl

/-! ### The run's terminal route, reading the row's facts

The loop's strong recursion over the assembly's rows, keeping what the accept
row carries: its tape, its trace's counts and the reference run's facts at that
tape, at the start head's document.  The price and the boundary are unchanged.
-/

/-- **The walk's run, from a head, ends at one of the two terminal routes, and
the accepted one carries the reference facts.**  Strong recursion on the entries
left; the continuing row shortens `nep - k` and its segment's credit pays the
difference.  The facts come from the terminal row's accept constructor — **the
rows** — and travel along the continuing rows' document read by
`Stage2NoEventWalkReferenceFacts.cast`. -/
theorem stage2NoEventWalkReferenceRun_terminal {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem) (K' : Stage2NoEventWalkCarry) (arena : List UInt8)
        (obs : List ConsumerEvent) (toks : List Token) (t : Tape)
        (parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t)
        (_facts : Stage2NoEventWalkReferenceFacts K.bs arena obs toks t),
        q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
        runFuel calls (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 1)) m) ∧
        Stage2NoEvent K.bs arena obs toks ∧
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
      (∃ (q : Nat) (mr : Mem) (K' : Stage2NoEventWalkCarry) (arena : List UInt8)
          (obs : List ConsumerEvent) (toks : List Token) (t : Tape)
          (parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t)
          (_facts : Stage2NoEventWalkReferenceFacts K.bs arena obs toks t),
          q + 2 ≤ stage2NoEventWalkPotential K k + F + 2 ∧
          runFuel calls (q + 2) stage2NoEventBody s =
            some (.ret (some (.int 64 1)) mr) ∧
          Stage2NoEvent K.bs arena obs toks ∧
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
              ⟨q, mr, K'', arena, obs, toks, t, hparsed, hfacts, hq, hrun, hrel,
                  hobsLen, hterms, hb⟩ |
                ⟨q, mr, hq, hrun, hb⟩
            · refine Or.inl ⟨p + q, mr, K'', arena, obs, toks, t, ?_,
                hfacts.cast hdoc, by omega, ?_, ?_, hobsLen, hterms, ?_⟩
              · rw [← hdoc]
                exact hparsed
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
        | terminal exit =>
            cases exit with
            | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen
                termsEq report bound t parsed facts =>
                refine Or.inl ⟨q, m, K', K'.arena, obs, toks, t, parsed, facts,
                  by omega, run, rel, obsLen, termsEq, ?_⟩
                rw [ha12, hn0] at bound
                exact bound
            | refuse q m sT route cost run ev _trace obs toks rel obsLen termsEq
                report bound _refused =>
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

/-- **The reference's word at a refused document.**  Every refusal shape maps to
zero, so a row carrying the parser's refusal reads the reference's word as the
run's. -/
theorem stage2NoEventWalkReferenceWord_of_error {bs : List UInt8}
    (h : Stage2NoEventWalkParseRefusal bs) :
    Stage2NoEventWalkReferenceWord bs = 0 := by
  obtain ⟨e, he⟩ := h
  unfold Stage2NoEventWalkReferenceWord
  rw [he]

/-! ### The walk's run, to the reference's word and value

The accept route stated at the facts the terminal row carries: the bundle is the
assembly's, and no `Stage2NoEvent` derivation is quantified over. -/

/-- **The no-event walk, from a head, reaches the reference's word and value.**

Hypotheses, each labelled:

* `hrows : Stage2NoEventWalkRows calls mem F` — **the rows**;
* `hhead` and `htrace` — **the head tier** (the head and the walk's output
  evidence there).

No hypothesis ties the facts' tape to the parser's result: that tie is the accept
row's own `parsed` field, which the conclusion returns beside the facts.  It
cannot be a hypothesis — the facts' only tape field is `t.tokens = toks`, so the
structure re-indexes at any tape with the same token list, and a `∀` over it is
refuted by exactly that re-indexing.

On the accepted route the run returns one, the reference's word is one, and
`stage2NoEventWalkReference_valueOfEvents` reads the emitted stream's value as
`scalarCanonValueOfBytes` at `K.bs`, with the facts and the parse equality the
terminal row's accept constructor carries.  On the refused route the run returns
zero, and the conclusion is stated in the run's own word.  The reference's zero
word at that arm is **not** exposed by this conclusion — the refuse row carries
`refused`, but the disjunct here returns only the run and the boundary — so a
consumer ties it through the row bundle's `refuse` row with
`stage2NoEventWalkReferenceWord_of_error`.

**What a caller must produce**: the rows (accept terminals built at the reference
parse's tape, each carrying its own parse equality) and the head with its trace.
Nothing else: the accept arm's value equation reads the equality the row carries,
so there is no supply to discharge beside the rows. -/
theorem stage2NoEventWalkReferenceRun_spec {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hrows : Stage2NoEventWalkRows calls mem F)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
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
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) := by
  rcases stage2NoEventWalkReferenceRun_terminal hrows hhead htrace with
    ⟨q, m, K', arena, obs, toks, t, parsed, facts, hq, hrun, hrel, -, -, hb⟩ |
      ⟨q, m, hq, hrun, hb⟩
  · have hword : Stage2NoEventWalkReferenceWord K.bs = 1 :=
      stage2NoEventWalkReferenceWord_of_ok parsed
    refine Or.inl ⟨q, m, arena, obs, toks, t, parsed, facts, hq, ?_, ?_, hrel,
      facts.records, facts.consume, ?_⟩
    · rw [hword]
      exact hrun
    · rw [hword]
      exact hb
    · exact stage2NoEventWalkReference_valueOfEvents facts parsed
  · exact Or.inr ⟨q, m, hq, hrun, hb⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkReferenceFacts.cast
#print axioms stage2NoEventWalkReference_valueOfEvents
#print axioms stage2NoEventWalkReferenceRun_terminal
#print axioms stage2NoEventWalkReferenceWord_of_ok
#print axioms stage2NoEventWalkReferenceWord_of_error
#print axioms stage2NoEventWalkReferenceRun_spec

end LeanLLVM.Refinement
