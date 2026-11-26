/-
The acceptance's two count equations: a relation-side half and a run-side half.

`Stage2NoEventWalkReferenceAccept` (`JsonStage2NoEventWalkPremises`) carries two
equations beside the relation, the parse and the reference facts:
`obs.length = K'.tok` and `K'.terms = (obs.map ConsumerEvent.terms).sum`. This
module settles which side of the deployment boundary each of them is on. The
answer is not the same for the two.

**The length equation is half relation, half run.** The relation alone fixes its
left side: every non-separator token carries exactly one event and the two
separators carry none, so `obs.length` is the document's non-separator token count
(`Stage2NoEvent.length_nonSeparators`). At that reading the carried equation is
*exactly* `K'.tok = (Token.nonSeparators toks).length` — a statement about the
walk's counted-token register, of which the tree's invariant carries only
`K.tok ≤ K.n` (`Stage2NoEventWalkInv.tokLe`) and the loop's index carries only an
over-count (`Stage2NoEventWalkCount`). Nothing in the tree computes that register
from the document.

**The terms equation has no relation-side half at all.** `EventRecord.terms` is
the record's fields' sum and `ConsumerEvent.terms` its read-back's, and the two
agree record for record (`EventRecord.terms_consume`); so given the boundary's
read-back identity `obs = consumeRecords bs arena rs` the carried equation is
*exactly* `K'.terms = (rs.map EventRecord.terms).sum` — the walk's term register
against the reference trace's own term sum. But the relation does not determine
the observations' sum `(obs.map ConsumerEvent.terms).sum` — which the read-back
identity carries to the records' sum — even up to a function of its parameters,
and it fails at an **arena-bound** derivation: `stage2NoEvent_str_len_free` leaves
the arena offset free, and at the document `"\/"` with the two-byte arena
`[0x2F, 0x2F]` the offsets `0` and `1` at length one both read the body, both
satisfy `Stage2NoEventArenaBound`, and give one event each, of equal length and
different `terms` sums (`countsTieDoc_terms_two_derivations`). Hence no function
of `(bs, arena, toks)` returns the sum (`stage2NoEvent_terms_not_functionable`),
and the tie is not implied by the relation plus its own length half even at
arena-bound derivations (`stage2NoEventWalkCountsTie_not_relation_determined`).

**The route produces the tie at its own event list, and at no other.** The walk
tier's `Stage2NoEventWalkTrace` (`JsonStage2NoEventWalkInv`) is an inductive whose
fields are the two equations, and it is *inhabited* at the all-zero carry with the
empty list (`Stage2NoEventWalkTrace.empty` below); `Stage2NoEventWalkTrace.step`
(`JsonStage2NoEventWalkContainers`) preserves the pair along every route, taking
the count and term deltas as hypotheses. So a walk from that seed proves the two
equations at the event list it accumulates — the events of the records it writes.
The acceptance, however, states them at the reference's *read-back*
`consumeRecords bs arena rs`, which the walk's route never names. The two lists
coincide only through the boundary's consumer projection (`obs =
consumeRecords bs arena rs`, the facts' `consume` field), and the relation cannot
supply that identity: `stage2NoEvent_str_len_free` is exactly the failure of any
relation-side bridge from a token list to its event list. That is the precise
sense in which the acceptance's equations are carried data: they are a route
theorem only about the route's own list, and the deployment must supply the trace
and the read-back identity that place them at the list the acceptance reports.

**The characterisation.** At an accept supply the two equations hold if and only
if the walk's two registers are the document's non-separator count and the record
trace's term sum (`stage2NoEventWalkAccept_counts_iff`). That is the pair a
deployment establishes by running the reference: the count by counting the walk's
counted routes over the document's tokens, and the sum by its term register over
the reference's records.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkInv
import LeanLLVM.Refinement.JsonStage2NoEventWalkSupplies

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The tie

The pair `Stage2NoEventWalkReferenceAccept` carries, at its own observation list.
`Stage2NoEventWalkTrace` (`JsonStage2NoEventWalkInv`) is the same pair as one
predicate; this is its carrier-free form, so the classification below can state
each half separately. -/

/-- **The two count equations.**  The walk's counted-token register is the
observation count, and its term register is the observations' term sum. -/
def Stage2NoEventWalkCountsTie (K' : Stage2NoEventWalkCarry)
    (obs : List ConsumerEvent) : Prop :=
  obs.length = K'.tok ∧ K'.terms = (obs.map ConsumerEvent.terms).sum

/-! ### The relation determines the length

Every non-separator token carries one event and a separator carries none, so the
relation fixes the observation count at the token list, and the carried length
equation reduces to a statement about `K'.tok` alone. -/

/-- **The relation fixes the observation count.**  The carried length equation is
equivalent to the register's being the document's non-separator token count, with
no reference data in the statement. -/
theorem stage2NoEventWalk_length_iff {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token}
    {K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEvent bs arena obs toks) :
    obs.length = K'.tok ↔ K'.tok = (Token.nonSeparators toks).length := by
  rw [Stage2NoEvent.length_nonSeparators h]
  exact eq_comm

/-- **The length is a function of the relation's parameters.**  The contrast with
the term sum below: the relation's `(bs, arena, toks)` do compute this side. -/
theorem stage2NoEvent_length_functionable :
    ∀ (bs arena : List UInt8) (obs : List ConsumerEvent) (toks : List Token),
      Stage2NoEvent bs arena obs toks →
        obs.length = (Token.nonSeparators toks).length :=
  fun _ _ _ _ h => Stage2NoEvent.length_nonSeparators h

/-! ### The read-back keeps the record's terms

The consumer's event carries the record's `tag`, `len` and `payload` unchanged,
so its per-event contribution is the record's.  This is what makes the term
equation a comparison with the reference trace's records rather than with the
observations. -/

/-- **The read-back's term sum is the trace's own term sum.** -/
theorem consumeRecords_terms_map (bs arena : List UInt8) (rs : List EventRecord) :
    (consumeRecords bs arena rs).map ConsumerEvent.terms =
      rs.map EventRecord.terms := by
  simp only [consumeRecords, List.map_map]
  exact List.map_congr_left fun r _ => EventRecord.terms_consume bs arena r

/-- **The term half, read through the read-back.**  Under the boundary's identity
`obs = consumeRecords bs arena rs`, the carried equation is the walk's register
against the record trace's term sum. -/
theorem stage2NoEventWalk_terms_iff {bs arena : List UInt8}
    {obs : List ConsumerEvent} {rs : List EventRecord}
    {K' : Stage2NoEventWalkCarry} (hobs : obs = consumeRecords bs arena rs) :
    K'.terms = (obs.map ConsumerEvent.terms).sum ↔
      K'.terms = (rs.map EventRecord.terms).sum := by
  rw [hobs, consumeRecords_terms_map]

/-! ### The characterisation at a derivation and at an accept supply

The classification the module proves: the tie is the pair of register-versus-data
comparisons, with the relation contributing only the count's data side. -/

/-- **The tie in the relation's own vocabulary.**  Under a derivation, the tie is
exactly "the register is the document's non-separator count" and "the register is
the observations' term sum"; the length half has no further content, and the term
half's right side is the observations, which the relation does not fix. -/
theorem stage2NoEventWalkCountsTie_iff {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEvent bs arena obs toks) :
    Stage2NoEventWalkCountsTie K' obs ↔
      K'.tok = (Token.nonSeparators toks).length ∧
        K'.terms = (obs.map ConsumerEvent.terms).sum :=
  ⟨fun htie => ⟨(stage2NoEventWalk_length_iff (K' := K') h).mp htie.1, htie.2⟩,
   fun hp => ⟨(stage2NoEventWalk_length_iff (K' := K') h).mpr hp.1, hp.2⟩⟩

/-- **The tie at an accept supply.**  The relation's tokens are the reference
tape's and the observations are the read-back, so the tie is exactly the pair of
register comparisons the deployment establishes: the counted-token register
against the document's non-separator count, and the term register against the
record trace's term sum. -/
theorem stage2NoEventWalkAccept_counts_iff {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') :
    Stage2NoEventWalkCountsTie K'
        (consumeRecords K.bs K'.arena s.recordsSupply.rs) ↔
      K'.tok = (Token.nonSeparators s.t.tokens).length ∧
        K'.terms = (s.recordsSupply.rs.map EventRecord.terms).sum := by
  have hrel := s.relation
  constructor
  · rintro ⟨hlen, hterms⟩
    exact ⟨(stage2NoEventWalk_length_iff (K' := K') hrel).mp hlen,
      (stage2NoEventWalk_terms_iff (obs := consumeRecords K.bs K'.arena
          s.recordsSupply.rs) (rs := s.recordsSupply.rs) (K' := K') rfl).mp hterms⟩
  · rintro ⟨htok, hterms⟩
    exact ⟨(stage2NoEventWalk_length_iff (K' := K') hrel).mpr htok,
      (stage2NoEventWalk_terms_iff (obs := consumeRecords K.bs K'.arena
          s.recordsSupply.rs) (rs := s.recordsSupply.rs) (K' := K') rfl).mpr hterms⟩

/-- **What the deployment adds.**  A record supply plus the tie at its read-back is
an inhabitant of the accept interface, and by
`stage2NoEventWalkReferenceAccept_iff` nothing more is needed.  This is the
positive direction of the classification: the equations are the additional
fields, not consequences of the supply. -/
theorem stage2NoEventWalkReferenceAccept_of_supply_tie {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K')
    (h : Stage2NoEventWalkCountsTie K'
      (consumeRecords K.bs K'.arena s.recordsSupply.rs)) :
    Nonempty (Stage2NoEventWalkReferenceAccept K K') :=
  (stage2NoEventWalkReferenceAccept_iff K K').mpr ⟨s, h.1, h.2⟩

/-! ### The register-side freedom

Neither register is a function of the relation.  The count is bounded, not
computed; the term register has no tree-side bound at all. -/

/-- **The count bound does not pin the count.**  `Stage2NoEventWalkCount` is just
`K.tok ≤ k`, so at a carry whose `tok` is a parameter it bounds that parameter and
reads nothing off the document. -/
theorem stage2NoEventWalkCount_iff (K : Stage2NoEventWalkCarry) (t k : Nat) :
    Stage2NoEventWalkCount { K with tok := t } k ↔ t ≤ k :=
  Iff.rfl

/-- **The trace carries the tie, it does not compute it.**  Every inhabitant of
`Stage2NoEventWalkTrace` is a source `obs` with the derivation, the two equations
and the arena bound; the two equations are constructor fields. -/
theorem Stage2NoEventWalkTrace.exists_countsTie {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) :
    ∃ (obs : List ConsumerEvent) (toks : List Token),
      Stage2NoEvent K.bs K.arena obs toks ∧
        Stage2NoEventWalkCountsTie K obs ∧
        Stage2NoEventArenaBound K.arena obs := by
  cases h with
  | intro obs toks rel obsLen termsEq arenaBound =>
      exact ⟨obs, toks, rel, ⟨obsLen, termsEq⟩, arenaBound⟩

/-- **The empty trace is inhabited.**  At the all-zero carry with the empty
document and arena the trace is the empty relation, both counts zero.  A route
starting here produces the tie at the event list it accumulates, which is the
one sense in which the equations are a route theorem — and it is a statement about
the route's own list, not the acceptance's reference read-back. -/
theorem Stage2NoEventWalkTrace.empty :
    Stage2NoEventWalkTrace
      { a12 := [], next0 := 0, b := 0, n := 0, ep := 0, nep := 0, xp := 0, nxp := 0,
        scratch := 0, scratchcap := 0, tokensOut := 0, valuesOut := 0, sumOut := 0,
        err := 0, bs := [], ent := [], stk := 0, d := 0, xj := 0, e := 0, c := 0,
        tok := 0, terms := 0, arena := [], arenaWord := 0, nextEnd := 0 } :=
  Stage2NoEventWalkTrace.intro [] [] Stage2NoEvent.nil rfl rfl
    (by intro e he; cases he)

/-! ### The relation does not determine the terms

The refutation is at one concrete document.  `"\/"` is a string token whose body
is the escape `\/`: the tape's reading of the token is the one code point `0x2F`,
and the arena form can read that code point off a two-byte arena at either offset,
`(off, len) = (0, 1)` or `(1, 1)`.  Both are **arena-bound** (`0 + 1 ≤ 2` and
`1 + 1 ≤ 2`), so each is an event list a `Stage2NoEventWalkTrace.step` may take:
the bound the trace tier requires does not exclude either.  The two derivations
carry one event each, equal in length, and their `terms` differ by the offset, so
`stage2NoEvent_str_len_free` (`JsonEventBridge`) is realised at a witness the tree
can name and the bounded step can take. -/

/-- The document `"\/"`: quote, backslash, slash, quote. -/
def countsTieDoc : List UInt8 := [0x22, 0x5C, 0x2F, 0x22]

/-- The document's decoded body, written twice: the second copy is what lets the
arena form read the body at two offsets. -/
def countsTieArena : List UInt8 := [0x2F, 0x2F]

/-- **The token's code points.**  The body is the escape `\/`, so its reading is
the single code point `0x2F`. -/
theorem countsTieDoc_codePoints : bodyCodePoints countsTieDoc ⟨0, 4⟩ = some [0x2F] := by
  decide

/-- **The arena at offset `0`** reads the body at length one. -/
theorem countsTieArena_off_zero :
    escapeCodePoints ((countsTieArena.drop 0).take 1) = some [0x2F] := by
  decide

/-- **And at offset `1`**, with the same length. -/
theorem countsTieArena_off_one :
    escapeCodePoints ((countsTieArena.drop 1).take 1) = some [0x2F] := by
  decide

/-- **A single string event is inside the arena bound** exactly when its offset and
length end inside the arena. -/
theorem stage2NoEventArenaBound_str_singleton (arena : List UInt8) (key : Bool)
    (len field : Nat) (cs : List Nat) (h : field + len ≤ arena.length) :
    Stage2NoEventArenaBound arena [ConsumerEvent.str key len field cs] := by
  intro e he _ _
  rw [List.mem_singleton] at he
  rw [he]
  show field + len ≤ arena.length
  exact h

/-- **Two arena-bound derivations at one document, arena and token list, with equal
lengths and different term sums.**  The difference is the free arena offset: the
events are `str true 1 0 [0x2F]` and `str true 1 1 [0x2F]`, whose contributions
are `6` and `7`, and both pass `Stage2NoEventArenaBound` at the two-byte arena
(`0 + 1 ≤ 2`, `1 + 1 ≤ 2`). -/
theorem countsTieDoc_terms_two_derivations :
    ∃ (obs obs' : List ConsumerEvent) (toks : List Token),
      Stage2NoEvent countsTieDoc countsTieArena obs toks ∧
      Stage2NoEvent countsTieDoc countsTieArena obs' toks ∧
      Stage2NoEventArenaBound countsTieArena obs ∧
      Stage2NoEventArenaBound countsTieArena obs' ∧
      obs.length = obs'.length ∧
      (obs.map ConsumerEvent.terms).sum ≠ (obs'.map ConsumerEvent.terms).sum := by
  refine ⟨[ConsumerEvent.str true 1 0 [0x2F]],
    [ConsumerEvent.str true 1 1 [0x2F]], [.string ⟨0, 4⟩], ?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact Stage2NoEvent.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 0)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_zero Stage2NoEvent.nil
  · exact Stage2NoEvent.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 1)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_one Stage2NoEvent.nil
  · exact stage2NoEventArenaBound_str_singleton countsTieArena true 1 0 [0x2F]
      (by decide)
  · exact stage2NoEventArenaBound_str_singleton countsTieArena true 1 1 [0x2F]
      (by decide)
  · decide

/-- **No producer of the observations' term sum from the relation's parameters.**
A function of `(bs, arena, toks)` returning `(obs.map ConsumerEvent.terms).sum`
would have to return both `6` and `7` at the witness above. -/
theorem stage2NoEvent_terms_not_functionable :
    ¬ ∃ T : List UInt8 → List UInt8 → List Token → Nat,
        ∀ (bs arena : List UInt8) (obs : List ConsumerEvent) (toks : List Token),
          Stage2NoEvent bs arena obs toks →
            (obs.map ConsumerEvent.terms).sum = T bs arena toks := by
  rintro ⟨T, hT⟩
  obtain ⟨obs, obs', toks, h, h', -, -, -, hne⟩ := countsTieDoc_terms_two_derivations
  exact hne (by rw [hT countsTieDoc countsTieArena obs toks h,
    hT countsTieDoc countsTieArena obs' toks h'])

/-- **The relation does not determine the event list itself.**  A function of
`(bs, arena, toks)` returning the observations would have to return both
`str true 1 0 [0x2F]` and `str true 1 1 [0x2F]` at the witness.  This is
`stage2NoEvent_str_len_free` (`JsonEventBridge`) as a non-functionability: the
read-back identity the acceptance uses cannot be a relation-side theorem either. -/
theorem stage2NoEvent_obs_not_functionable :
    ¬ ∃ F : List UInt8 → List UInt8 → List Token → List ConsumerEvent,
        ∀ (bs arena : List UInt8) (obs : List ConsumerEvent) (toks : List Token),
          Stage2NoEvent bs arena obs toks → obs = F bs arena toks := by
  rintro ⟨F, hF⟩
  obtain ⟨obs, obs', toks, h, h', -, -, -, hne⟩ := countsTieDoc_terms_two_derivations
  have h1 := hF countsTieDoc countsTieArena obs toks h
  have h2 := hF countsTieDoc countsTieArena obs' toks h'
  have hEq : obs = obs' := by rw [h1, h2]
  exact hne (by rw [hEq])

/-- **The tie is not implied by the relation and its own length half, even at
arena-bound derivations.**  A register can satisfy the tie at one arena-bound
derivation (its count is the common length and its term register that derivation's
sum) and fail it at another arena-bound derivation at the same document, arena and
tokens, because the two sums differ while the lengths agree.  So the bounded trace
the deployment carries can fail the tie; this is the precise sense in which the
term equation is the run's data. -/
theorem stage2NoEventWalkCountsTie_not_relation_determined :
    ¬ (∀ (bs arena : List UInt8) (obs obs' : List ConsumerEvent)
        (toks : List Token) (K' : Stage2NoEventWalkCarry),
        Stage2NoEvent bs arena obs toks → Stage2NoEvent bs arena obs' toks →
        Stage2NoEventArenaBound arena obs → Stage2NoEventArenaBound arena obs' →
        obs.length = obs'.length →
        Stage2NoEventWalkCountsTie K' obs →
        Stage2NoEventWalkCountsTie K' obs') := by
  intro hall
  obtain ⟨obs, obs', toks, h, h', hb, hb', hlen, hne⟩ :=
    countsTieDoc_terms_two_derivations
  let K' : Stage2NoEventWalkCarry :=
    { a12 := [], next0 := 0, b := 0, n := 0, ep := 0, nep := 0, xp := 0, nxp := 0,
      scratch := 0, scratchcap := 0, tokensOut := 0, valuesOut := 0, sumOut := 0,
      err := 0, bs := countsTieDoc, ent := [], stk := 0, d := 0, xj := 0, e := 0,
      c := 0, tok := obs.length, terms := (obs.map ConsumerEvent.terms).sum,
      arena := countsTieArena, arenaWord := 0, nextEnd := 0 }
  have htie : Stage2NoEventWalkCountsTie K' obs := ⟨rfl, rfl⟩
  have hboth := hall countsTieDoc countsTieArena obs obs' toks K' h h' hb hb' hlen htie
  exact hne hboth.2

/-- **The route's own term delta is not pinned by the relation and the count
delta.**  `Stage2NoEventWalkTrace.step` takes `htok : K'.tok = K.tok + evs.length`
and `hterms : K'.terms = K.terms + (evs.map ConsumerEvent.terms).sum`.  At one
`(bs, arena, toks)` two **arena-bound** candidate event lists of equal length —
the same count delta — have different sums, so the relation plus `htok` does not
give `hterms`: the term store a route records is not a function of the relation and
the count it stores beside it. -/
theorem stage2NoEvent_step_terms_delta_not_relation_determined :
    ¬ (∀ (bs arena : List UInt8) (evs evs' : List ConsumerEvent)
        (toks : List Token),
        Stage2NoEvent bs arena evs toks → Stage2NoEvent bs arena evs' toks →
        Stage2NoEventArenaBound arena evs → Stage2NoEventArenaBound arena evs' →
        evs.length = evs'.length →
        (evs.map ConsumerEvent.terms).sum = (evs'.map ConsumerEvent.terms).sum) := by
  intro hall
  obtain ⟨obs, obs', toks, h, h', hb, hb', hlen, hne⟩ :=
    countsTieDoc_terms_two_derivations
  exact hne (hall countsTieDoc countsTieArena obs obs' toks h h' hb hb' hlen)

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalk_length_iff
#print axioms stage2NoEvent_length_functionable
#print axioms consumeRecords_terms_map
#print axioms stage2NoEventWalk_terms_iff
#print axioms stage2NoEventWalkCountsTie_iff
#print axioms stage2NoEventWalkAccept_counts_iff
#print axioms stage2NoEventWalkReferenceAccept_of_supply_tie
#print axioms stage2NoEventWalkCount_iff
#print axioms Stage2NoEventWalkTrace.exists_countsTie
#print axioms Stage2NoEventWalkTrace.empty
#print axioms stage2NoEventArenaBound_str_singleton
#print axioms countsTieDoc_terms_two_derivations
#print axioms stage2NoEvent_terms_not_functionable
#print axioms stage2NoEvent_obs_not_functionable
#print axioms stage2NoEventWalkCountsTie_not_relation_determined
#print axioms stage2NoEvent_step_terms_delta_not_relation_determined

end LeanLLVM.Refinement
