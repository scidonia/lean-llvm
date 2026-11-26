/-
Whether the walk's two counters are the reference's read-back.

`JsonStage2NoEventWalkCountsTie` states the acceptance's pair
`obs.length = K'.tok` and `K'.terms = (obs.map ConsumerEvent.terms).sum` and shows
what the relation fixes.  This module asks the remaining question: is the pair, at
`obs = consumeRecords bs arena rs`, a theorem about the walk's run — or is it only
the boundary's carried choice?  The answer splits the pair cleanly.

**The length half is a theorem.**  `consumeRecords` is a map, so its length is the
record trace's, and `Stage2Records.length_nonSeparators` already computes that as
the document's non-separator token count.  Nothing reference-dependent survives:
`consumeRecords_length_eq_nonSeparators`.

**The composition half is a theorem, and it is the whole of the walk's accounting.**
The walk maintains the pair in one place only.  `Stage2NoEventWalkTrace`'s `intro`
constructor carries `obsLen` and `termsEq` — the pair at the seed's event list —
and `Stage2NoEventWalkTrace.step` carries, at each route, the two register deltas
`htok : K'.tok = K.tok + evs.length` and
`hterms : K'.terms = K.terms + (evs.map ConsumerEvent.terms).sum`, which are
exactly the counts the row's own stores write.  Composing them is
`stage2NoEventWalkCountsTie_steps`: a seed tie plus a chain's accumulated delta is
the tie at the seed list followed by the chain's events.  So the walk's accounting
does produce the pair — at the event list *it* accumulates, which is the trace's
induction data.

**The read-back half is not.**  The run stores three reading words and no event
(`JsonStage2NoEventWalkTraceRun`), so `obs` is not read back from a state; and even
handed the event list, the identity `obs = consumeRecords bs arena rs` is not a
function of the document, the arena and the parser's tokens.  The obstruction is at
the record trace, not the relation: at the document `"\/"` and the two-byte arena
the single string token has both the arena record `str true 1 0` and
`str true 1 1`, each `Stage2Records` at that token, each fitting the record widths
and the extent clause, with read-backs of equal length and different term sums
(`stage2NoEventRecords_terms_two_derivations`,
`stage2NoEventWalkRecordsSupply_terms_two_derivations`).  Hence no function of
`(bs, arena, tokens)` returns the read-back's term sum
(`stage2NoEventReadback_terms_not_functionable`): a carry whose counters tie to one
supply's read-back fails the tie at the other
(`stage2NoEventWalkCountsTie_readback_not_determined`).  That is a statement wall,
not a proof failure — the boundary's `consume` field and the chosen `rs` are what
place the pair at the reference's observations, and `stage2NoEventWalkReferenceAccept`
is exactly that data.

**Where the accept gets it.**  The accept exit carries its own report at the
read-back: the facts' `consume` field is the identity, so the acceptance's two
equations are `Stage2NoEventWalkCountsTie` at `consumeRecords …`
(`stage2NoEventWalkReferenceAccept_countsTie`).  Nothing here removes the trace
parameter from the rows: the event list is induction data, and the tie's right side
is the boundary's.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkCountsTie
import LeanLLVM.Refinement.JsonStage2NoEventWalkTraceRun

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The length half, at the read-back

The record trace's length is the observation count, and the record relation
already names it.  So the carried length equation has no reference-side content
beyond the counted-token register itself. -/

/-- **The read-back's length is the non-separator token count.**  `consumeRecords`
is a map, and `Stage2Records.length_nonSeparators` computes the trace's length. -/
theorem consumeRecords_length_eq_nonSeparators {bs arena : List UInt8}
    {rs : List EventRecord} {toks : List Token}
    (h : Stage2Records bs arena rs toks) :
    (consumeRecords bs arena rs).length = (Token.nonSeparators toks).length := by
  simp only [consumeRecords, List.length_map]
  exact Stage2Records.length_nonSeparators h

/-- **The read-back's length is a function of the relation's tokens.**  The
record-level form of `stage2NoEvent_length_functionable`. -/
theorem consumeRecords_length_functionable :
    ∀ (bs arena : List UInt8) (rs : List EventRecord) (toks : List Token),
      Stage2Records bs arena rs toks →
        (consumeRecords bs arena rs).length = (Token.nonSeparators toks).length :=
  fun _ _ _ _ h => consumeRecords_length_eq_nonSeparators h

/-! ### Composing the walk's accounting

The pair lives in the trace: the seed's `intro` carries it, and each route's
`step` carries the two register deltas.  The induction that composes a chain is
below; it never touches a state, only the counters the rows store. -/

/-- **A route's step is the pair's one-link extension.**  `htok` and `hterms` are
`Stage2NoEventWalkTrace.step`'s own hypotheses: the counts the row's stores write.
Given the pair at the source list, they give it at the appended list. -/
theorem stage2NoEventWalkCountsTie_step {K K' : Stage2NoEventWalkCarry}
    {obs evs : List ConsumerEvent}
    (h : Stage2NoEventWalkCountsTie K obs)
    (htok : K'.tok = K.tok + evs.length)
    (hterms : K'.terms = K.terms + (evs.map ConsumerEvent.terms).sum) :
    Stage2NoEventWalkCountsTie K' (obs ++ evs) := by
  obtain ⟨hobsLen, hobsSum⟩ := h
  constructor
  · rw [List.length_append, hobsLen, htok]
  · rw [List.map_append, List.sum_append, ← hobsSum, ← hterms]

/-- **The pair composes along a chain of routes.**  A seed pair at `obs₀`, and a
chain whose accumulated stores move the registers by the concatenation of its
per-route event lists, give the pair at the seed list followed by that
concatenation.  This is the induction `Stage2NoEventWalkTrace.step` performs along
the run, stated at the registers alone: the seed's half is the trace's
`obsLen`/`termsEq`, every later half is a route's `htok`/`hterms`. -/
theorem stage2NoEventWalkCountsTie_steps {obs₀ : List ConsumerEvent}
    {K₀ K : Stage2NoEventWalkCarry} (evss : List (List ConsumerEvent))
    (h₀ : Stage2NoEventWalkCountsTie K₀ obs₀)
    (htok : K.tok = K₀.tok + evss.flatten.length)
    (hterms : K.terms = K₀.terms + (evss.flatten.map ConsumerEvent.terms).sum) :
    Stage2NoEventWalkCountsTie K (obs₀ ++ evss.flatten) := by
  obtain ⟨hobsLen, hobsSum⟩ := h₀
  constructor
  · rw [List.length_append, hobsLen, htok]
  · rw [List.map_append, List.sum_append, ← hobsSum, ← hterms]

/-! ### The accept's pair is the read-back's

The accept exit carries its report together with the facts, whose `consume` field
is the read-back identity.  So the acceptance's two equations are the pair at
`consumeRecords …` — this is what the carried data places, and it is all of it. -/

/-- **The accept's carried data gives the pair at the read-back.**  Destructuring
`Stage2NoEventWalkReferenceAccept` and keeping the facts' `consume` identity, the
two equations become a `Stage2NoEventWalkCountsTie` at the supply's read-back. -/
theorem stage2NoEventWalkReferenceAccept_countsTie {K K' : Stage2NoEventWalkCarry}
    (a : Stage2NoEventWalkReferenceAccept K K') :
    ∃ s : Stage2NoEventWalkAcceptSupply K K',
      Stage2NoEventWalkCountsTie K'
        (consumeRecords K.bs K'.arena s.recordsSupply.rs) := by
  obtain ⟨t, obs, toks, ⟨rel, hlen, hsum, parsed⟩, facts⟩ := a
  refine ⟨⟨t, parsed, facts.toSupply⟩, ?_, ?_⟩
  · show (consumeRecords K.bs K'.arena facts.rs).length = K'.tok
    rw [← facts.consume]
    exact hlen
  · show K'.terms = ((consumeRecords K.bs K'.arena facts.rs).map
        ConsumerEvent.terms).sum
    rw [← facts.consume]
    exact hsum

/-! ### The read-back half is not determined

The relation fixes neither the observation list nor its term sum; the same is true
at the record trace, which is the boundary's own vocabulary.  The witness is the
document `"\/"` and the two-byte arena `[0x2F, 0x2F]`: the string token's body
reads at arena offsets `0` and `1`, both inside the arena bound, and the two
records `str true 1 0` and `str true 1 1` are both `Stage2Records` at the token
with equal length and different `terms`. -/

/-- **Two record traces at one document, arena and token list.**  Equal record
counts, different term sums.  Both are the arena form at the free offset, so both
are `Stage2Records` at the same `.string` token. -/
theorem stage2NoEventRecords_terms_two_derivations :
    ∃ (bs arena : List UInt8) (toks : List Token) (rs rs' : List EventRecord),
      Stage2Records bs arena rs toks ∧
      Stage2Records bs arena rs' toks ∧
      rs.length = rs'.length ∧
      (rs.map EventRecord.terms).sum ≠ (rs'.map EventRecord.terms).sum := by
  refine ⟨countsTieDoc, countsTieArena, [.string ⟨0, 4⟩],
    [EventRecord.str true 1 0], [EventRecord.str true 1 1], ?_, ?_, rfl, ?_⟩
  · exact Stage2Records.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 0)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_zero Stage2Records.nil
  · exact Stage2Records.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 1)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_one Stage2Records.nil
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EventRecord.terms, ite_true]
    omega

/-- **The read-backs have equal length and different term sums.**  The record-level
witness read through the consumer, which preserves both. -/
theorem consumeRecords_terms_two_derivations :
    ∃ (bs arena : List UInt8) (toks : List Token) (rs rs' : List EventRecord),
      Stage2Records bs arena rs toks ∧
      Stage2Records bs arena rs' toks ∧
      (consumeRecords bs arena rs).length =
        (consumeRecords bs arena rs').length ∧
      ((consumeRecords bs arena rs).map ConsumerEvent.terms).sum ≠
        ((consumeRecords bs arena rs').map ConsumerEvent.terms).sum := by
  obtain ⟨bs, arena, toks, rs, rs', h, h', hlen, hne⟩ :=
    stage2NoEventRecords_terms_two_derivations
  refine ⟨bs, arena, toks, rs, rs', h, h', ?_, ?_⟩
  · simp only [consumeRecords, List.length_map, hlen]
  · rw [consumeRecords_terms_map, consumeRecords_terms_map]
    exact hne

/-- **No function of the document, arena and tokens returns the read-back's term
sum.**  This is the obstruction in the deployment's own vocabulary: the reference
trace is the parse's, the tokens are the tape's, and still the sum is not a
function of them.  So the pair's term half cannot be computed from the run's
inputs; only the boundary's chosen record trace fixes it. -/
theorem stage2NoEventReadback_terms_not_functionable :
    ¬ ∃ T : List UInt8 → List UInt8 → List Token → Nat,
        ∀ (bs arena : List UInt8) (rs : List EventRecord) (toks : List Token),
          Stage2Records bs arena rs toks →
            ((consumeRecords bs arena rs).map ConsumerEvent.terms).sum =
              T bs arena toks := by
  rintro ⟨T, hT⟩
  obtain ⟨bs, arena, toks, rs, rs', h, h', -, hne⟩ :=
    stage2NoEventRecords_terms_two_derivations
  have h1 := hT bs arena rs toks h
  have h2 := hT bs arena rs' toks h'
  have hmap : (rs.map EventRecord.terms).sum = ((consumeRecords bs arena rs).map
      ConsumerEvent.terms).sum := by
    rw [consumeRecords_terms_map]
  have hmap' : (rs'.map EventRecord.terms).sum = ((consumeRecords bs arena rs').map
      ConsumerEvent.terms).sum := by
    rw [consumeRecords_terms_map]
  exact hne (hmap.trans (h1.trans (h2.symm.trans hmap'.symm)))

/-- **One carry, two read-backs: the pair holds at one and fails at the other.**
A carry whose registers are one supply's read-back length and term sum satisfies
the pair there; a second record trace at the same document, arena and tokens has a
read-back of the same length and a different sum, so the pair fails at it.  The
walk's accounting cannot choose between them. -/
theorem stage2NoEventWalkCountsTie_readback_not_determined :
    ∃ (bs arena : List UInt8) (toks : List Token) (rs rs' : List EventRecord)
      (K' : Stage2NoEventWalkCarry),
      Stage2Records bs arena rs toks ∧
      Stage2Records bs arena rs' toks ∧
      (consumeRecords bs arena rs).length =
        (consumeRecords bs arena rs').length ∧
      Stage2NoEventWalkCountsTie K' (consumeRecords bs arena rs) ∧
      ¬ Stage2NoEventWalkCountsTie K' (consumeRecords bs arena rs') := by
  obtain ⟨bs, arena, toks, rs, rs', h, h', hlen, hne⟩ :=
    consumeRecords_terms_two_derivations
  refine ⟨bs, arena, toks, rs, rs',
    { a12 := [], next0 := 0, b := 0, n := 0, ep := 0, nep := 0, xp := 0, nxp := 0,
      scratch := 0, scratchcap := 0, tokensOut := 0, valuesOut := 0, sumOut := 0,
      err := 0, bs := bs, ent := [], stk := 0, d := 0, xj := 0, e := 0, c := 0,
      tok := (consumeRecords bs arena rs).length,
      terms := ((consumeRecords bs arena rs).map ConsumerEvent.terms).sum,
      arena := arena, arenaWord := 0, nextEnd := 0 },
    h, h', hlen, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨-, hsum⟩
  exact hne hsum

/-! ### The obstruction survives the supply's side conditions

A `Stage2NoEventWalkRecordsSupply` also asks the records fit their field widths and
the reported strings lie inside the sources they name.  Both witnesses do: the
records are length one at an offset inside the arena, and the extent clause is
`off + 1 ≤ 2` at `off ∈ {0, 1}`.  So the choice is between two genuine supplies at
one tape, not between two malformed ones. -/

/-- **A string record fits the widths** at a length and span inside them. -/
theorem EventRecord.bounded_str (key : Bool) {len span : Nat}
    (hlen : len < 2 ^ 32) (hspan : span < 2 ^ 64) :
    EventRecord.Bounded (.str key len span) :=
  ⟨hlen, hspan⟩

/-- **A string event's body lies inside the arena** when its field is the clear-bit
arena offset and its extent ends inside the arena. -/
theorem ConsumerEvent.bodiesWithin_str_arena (bs arena : List UInt8) (key : Bool)
    (len field : Nat) (cs : List Nat) (hlo : field < 2 ^ 63)
    (h : field + len ≤ arena.length) :
    ConsumerEvent.BodiesWithin bs arena (.str key len field cs) := by
  intro _
  show (if field < 2 ^ 63 then field + len ≤ arena.length
    else (field - 2 ^ 63) + len ≤ bs.length)
  rw [if_pos hlo]
  exact h

/-- **The consumer's reading of the offset-zero record.** -/
theorem consume_countsTie_str_zero :
    EventRecord.consume countsTieDoc countsTieArena (EventRecord.str true 1 0) =
      ConsumerEvent.str true 1 0 [0x2F] := by
  simp only [EventRecord.consume, stringConsumer]
  rw [if_pos (by decide : (0 : Nat) < 2 ^ 63), countsTieArena_off_zero]
  rfl

/-- **The consumer's reading of the offset-one record.** -/
theorem consume_countsTie_str_one :
    EventRecord.consume countsTieDoc countsTieArena (EventRecord.str true 1 1) =
      ConsumerEvent.str true 1 1 [0x2F] := by
  simp only [EventRecord.consume, stringConsumer]
  rw [if_pos (by decide : (1 : Nat) < 2 ^ 63), countsTieArena_off_one]
  rfl

/-- **The tape the concrete witness reads at.** -/
def countsTieTape : Tape :=
  { input := ByteString.literal countsTieDoc, tokens := [.string ⟨0, 4⟩] }

/-- **Two record supplies at one tape.**  The supplies differ only in the arena
offset their single record carries; both pass the record widths and the extent
clause, and their read-backs have equal length and different term sums. -/
theorem stage2NoEventWalkRecordsSupply_terms_two_derivations :
    ∃ s s' : Stage2NoEventWalkRecordsSupply countsTieDoc countsTieArena countsTieTape,
      s.rs.length = s'.rs.length ∧
      ((consumeRecords countsTieDoc countsTieArena s.rs).map
          ConsumerEvent.terms).sum ≠
        ((consumeRecords countsTieDoc countsTieArena s'.rs).map
          ConsumerEvent.terms).sum := by
  have hrec0 : Stage2Records countsTieDoc countsTieArena [EventRecord.str true 1 0]
      countsTieTape.tokens :=
    Stage2Records.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 0)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_zero Stage2Records.nil
  have hrec1 : Stage2Records countsTieDoc countsTieArena [EventRecord.str true 1 1]
      countsTieTape.tokens :=
    Stage2Records.strArena (key := true) (s := ⟨0, 4⟩) (len := 1) (off := 1)
      (cs := [0x2F]) (by decide) (by decide) countsTieDoc_codePoints (by decide)
      countsTieArena_off_one Stage2Records.nil
  have hb0 : ∀ r ∈ [EventRecord.str true 1 0], r.Bounded := by
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact EventRecord.bounded_str true (by decide) (by decide)
  have hb1 : ∀ r ∈ [EventRecord.str true 1 1], r.Bounded := by
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact EventRecord.bounded_str true (by decide) (by decide)
  have hw0 : ∀ e ∈ consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 0],
      e.BodiesWithin countsTieDoc countsTieArena := by
    intro e he
    rw [show consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 0] =
        [ConsumerEvent.str true 1 0 [0x2F]] from by
      simp only [consumeRecords, List.map_cons, List.map_nil,
        consume_countsTie_str_zero]] at he
    rw [List.mem_singleton] at he
    rw [he]
    exact ConsumerEvent.bodiesWithin_str_arena countsTieDoc countsTieArena true 1 0
      [0x2F] (by decide) (by decide)
  have hw1 : ∀ e ∈ consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 1],
      e.BodiesWithin countsTieDoc countsTieArena := by
    intro e he
    rw [show consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 1] =
        [ConsumerEvent.str true 1 1 [0x2F]] from by
      simp only [consumeRecords, List.map_cons, List.map_nil,
        consume_countsTie_str_one]] at he
    rw [List.mem_singleton] at he
    rw [he]
    exact ConsumerEvent.bodiesWithin_str_arena countsTieDoc countsTieArena true 1 1
      [0x2F] (by decide) (by decide)
  refine ⟨{ rs := [EventRecord.str true 1 0], records := hrec0,
            bounded := hb0, within := hw0 },
          { rs := [EventRecord.str true 1 1], records := hrec1,
            bounded := hb1, within := hw1 }, rfl, ?_⟩
  show ((consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 0]).map
      ConsumerEvent.terms).sum ≠
    ((consumeRecords countsTieDoc countsTieArena [EventRecord.str true 1 1]).map
      ConsumerEvent.terms).sum
  rw [consumeRecords_terms_map, consumeRecords_terms_map]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EventRecord.terms, ite_true]
  omega

/-! ### Axiom footprints -/

#print axioms consumeRecords_length_eq_nonSeparators
#print axioms consumeRecords_length_functionable
#print axioms stage2NoEventWalkCountsTie_step
#print axioms stage2NoEventWalkCountsTie_steps
#print axioms stage2NoEventWalkReferenceAccept_countsTie
#print axioms stage2NoEventRecords_terms_two_derivations
#print axioms consumeRecords_terms_two_derivations
#print axioms stage2NoEventReadback_terms_not_functionable
#print axioms stage2NoEventWalkCountsTie_readback_not_determined
#print axioms EventRecord.bounded_str
#print axioms ConsumerEvent.bodiesWithin_str_arena
#print axioms consume_countsTie_str_zero
#print axioms consume_countsTie_str_one
#print axioms stage2NoEventWalkRecordsSupply_terms_two_derivations

end LeanLLVM.Refinement
