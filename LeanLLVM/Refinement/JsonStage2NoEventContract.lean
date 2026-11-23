/-
The no-event stage-2 entry's record, `Γ_stage2_noevent`.

`kernel/json/stage2_noevent.h` declares one entry point,
`leanllvm_json_stage2_noevent`, whose twelve arguments are the certified unit's
first six pairs with the arena and event stream replaced by a caller-staged
`scratch` buffer, and whose last four slots are the consumer's three readings and
the refusal word:

    b, n, ep, nep, xp, nxp, scratch, scratchcap, tokens, values, sum, err

`kernel/json/stage2_noevent.c` is its body: the certified walk's per-entry
dispatch with the event stores replaced by the consumer's accumulations.  This
module states the record that entry point satisfies.  The body is pinned in
`JsonStage2NoEventIR`; the stores theorem and the walk's obligation are in
`JsonStage2NoEventBody`.

# What the post is

The accepted arm carries an **existential arena list**: the decoded string bodies
in document order, fixed by the run's events and not read back from memory.  The
entry materialises no arena, so there is no memory region to read it from — the
certified post's `arena_read : readBytes m w.dst w.ndst' = some w.arena` has no
analogue here, and inventing one would claim a write the run does not make.  The
list is the fold's `arenaSum` input at the consumer boundary, and its relation to
the document and the events is `Stage2NoEvent`.

The three reading words are stated at what a word can carry:

* `tokens` and `values` are counts at most the document's length, and `n < 2 ^ 64`
  is a pre clause, so each word holds its count exactly.  The post states the
  count, its bound by `n`, and the count's width, so the word's value *is* the
  reading rather than a residue of it;
* `sum` is not bounded by `n` — a number's payload is a whole sixty-four-bit
  word — so the universal fact is the modular one:
  `*sum = (byteSum arena + Σ terms) mod 2 ^ 64`, which holds for every accepted
  call.  Equality with the mathematical sum is the stronger, separate condition
  `sum < 2 ^ 64`; the differential's committed corpus satisfies it, and a
  consumer that needs the exact value supplies it
  (`stage2NoEventBoundary_sum_exact`).  A corpus bound is not a premise of the
  post, because a corpus cannot justify a universal claim.

The post also reads the **document** the run was given: `readBytes mem b n = some
bs`.  This is a read of the caller's staged input, not a claim that the run wrote
anywhere, and it is what anchors the accepted arm's relation — without it
`Stage2NoEvent bs arena obs toks` would quantify a `bs` unrelated to the bytes the
caller staged, and the events would not be the *document's*.

**No destination and no event region.**  The presence clause covers the four
output words and nothing else, and the frame covers the caller's staged objects
and the run's own stack interval.  There is no `dst` and no `ev` anywhere in the
record: that absence *is* the no-event property, since a post with no region for
the destination or the event buffer is a theorem that the run wrote neither.

# What this module does not claim

The post is the *shape* the run must satisfy.  That the pinned body produces it
is `stage2NoEventRun_boundary` at a walk report, and the report itself is
`Stage2NoEventWalkObligation` — stated and not inhabited, at the certified walk's
depth, and narrower than `Stage2WalkObligation`: it is conditional on a contract
at `od_gap_recover`, which this tree does not yet supply.  The consumer-boundary
agreement (the fold over the events is the certified consumer's reading) is
`JsonStage2NoEventBody`'s corollary of Item 1's `stage2Boundary_noEventConsumer`.
-/
import LeanLLVM.Refinement.JsonStage2NoEvent
import LeanLLVM.Refinement.JsonStage2Contract

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The staged extents

The four objects the flattening appends to the body are the entry's own locals,
read from the pinned fixture: the container stack `%stk`, the refusal record
`%e`, the cursor record `%c`, and the number path's output slot `%d`.  The
extents are `stage2-noevent.staging.tsv`'s `llvm.lifetime.start` sizes, and
`JsonStage2NoEventIR` asserts the same four numbers against the pin at
elaboration, so a fixture that resized one fails there rather than leaving this
record describing an object the body no longer has. -/

/-- `%stk`: the container stack, `MAXD` bytes (`stage2.c:192`). -/
def stage2NoEventStackExtent : Nat := 520

/-- `%e`: the refusal record, 24 bytes (kind, offset, message word). -/
def stage2NoEventErrorExtent : Nat := 24

/-- `%c`: the cursor record, 1192 bytes. -/
def stage2NoEventCursorExtent : Nat := 1192

/-- `%d`: the number path's output slot, one eight-byte word. -/
def stage2NoEventNumExtent : Nat := 8

/-- The four staged objects' regions, in the pinned body's parameter order. -/
def stage2NoEventStagedRegions (stk e c d : Nat) : List (Nat × Nat) :=
  [(stk, stage2NoEventStackExtent), (e, stage2NoEventErrorExtent),
   (c, stage2NoEventCursorExtent), (d, stage2NoEventNumExtent)]

/-- **The addresses the entry writes**: the three reading words and the refusal
slot.  The post's presence clause and its frame are stated at this list, and the
list is the whole of it — no destination, no event stream, no arena. -/
def stage2NoEventWrites (tokensOut valuesOut sumOut err : Nat) : List (Nat × Nat) :=
  [(tokensOut, 8), (valuesOut, 8), (sumOut, 8), (err, 8)]

/-- **The records the run's own stores reach**: the caller's scratch buffer (the
decoded string bodies land there) and the four staged objects.  It is the no-event
analogue of the certified walk's scratch list; the arena and the event stream are
absent by construction. -/
def stage2NoEventRunRegions (scratch scratchcap stk e c d : Nat) : List (Nat × Nat) :=
  (scratch, scratchcap) :: stage2NoEventStagedRegions stk e c d

/-- **The caller's staged objects**: the document with its readable tail, the entry
and escape streams, the scratch buffer, and the four output words.  The document's
entry is `n + stage2ReadTail` because the decoder reads past the last body, and
the scratch's entry is its capacity, because the decoder's reserve is charged
against it. -/
def stage2NoEventRegions (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
    sumOut err : Nat) : List (Nat × Nat) :=
  [(b, n + stage2ReadTail), (ep, 4 * nep), (xp, 4 * nxp), (scratch, scratchcap)] ++
    stage2NoEventWrites tokensOut valuesOut sumOut err

/-! ### The precondition -/

/-- The caller's staging for the no-event entry, at `stage2_noevent.h`'s twelve
arguments.  Every clause is one the certified record states, with the arena and
event capacities replaced by the scratch's:

* the document is readable, with the decoder's read-past tail;
* the entry stream is `readLanes32`-readable, in document order, inside the
  document;
* the escape list's bytes are staged;
* the scratch buffer is staged and has room for the document plus the decoder's
  slack — a shortfall is the body's `__builtin_trap`, never a refusal, exactly as
  the certified unit's two reserves are;
* the four output words are staged and separate from every input the run reads
  and from each other;
* the document's positions fit the 32-bit entry words, and the document, the
  scratch capacity, and the two counts are their eight-byte argument words;
* the watermark: every staged object ends at or below the allocator cursor the
  call is made at, which is what makes the body's own `alloca`s fresh. -/
def stage2NoEventPre (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∃ (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat)
    (bs : List UInt8) (ent : List Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
            .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
            .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap),
            .ptr tokensOut, .ptr valuesOut, .ptr sumOut, .ptr err] ∧
    readBytes mem b n = some bs ∧
    HasBytes mem (b + n) stage2ReadTail ∧
    readLanes32 mem ep nep = some ent ∧
    ent.Pairwise (· < ·) ∧
    (∀ q ∈ ent, q < n) ∧
    HasBytes mem xp (4 * nxp) ∧
    HasBytes mem scratch scratchcap ∧
    n + stage2ArenaReserve ≤ scratchcap ∧
    HasBytes mem tokensOut 8 ∧ HasBytes mem valuesOut 8 ∧
    HasBytes mem sumOut 8 ∧ HasBytes mem err 8 ∧
    n ≤ stage2MaxDocument ∧
    n < 2 ^ 64 ∧ scratchcap < 2 ^ 64 ∧ nep < 2 ^ 64 ∧ nxp < 2 ^ 64 ∧
    DisjointRegions
      (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
        valuesOut sumOut err) ∧
    (∀ r ∈ stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
        valuesOut sumOut err, r.1 + r.2 ≤ next)

/-- **The staging of the four objects the flattening appends.**  The body writes
its container stack, its refusal record, its cursor record, and — through the
number path — `%d`'s slot, so a record that left them unstaged would contradict
its own region claim one step in.  The twelve-argument ABI cannot name them, so
the adapter is where the staging is stated: their presence, their separation from
every staged input and output, and the watermark that places them below the
allocator cursor the call is made at. -/
def stage2NoEventStagedPre (args : List Value) (mem : Mem) (next : Nat)
    (stk e c d : Nat) : Prop :=
  (∀ r ∈ stage2NoEventStagedRegions stk e c d, HasBytes mem r.1 r.2) ∧
  ∃ (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
            .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
            .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap),
            .ptr tokensOut, .ptr valuesOut, .ptr sumOut, .ptr err] ∧
    DisjointRegions
      (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
        valuesOut sumOut err ++ stage2NoEventStagedRegions stk e c d) ∧
    (∀ r ∈ stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
        valuesOut sumOut err, r.1 + r.2 ≤ next) ∧
    (∀ r ∈ stage2NoEventStagedRegions stk e c d, r.1 + r.2 ≤ next)

/-! ### The post -/

/-- **The no-event entry's boundary.**  The accepted arm carries the run's
verdict, the document it read, the token count and the existential arena the fold
sums, and the three writing words at what a word can carry; the refusal arm
carries zeros in all three and the run's offset in `*err`; the frame covers the
caller's staged objects and the run's own stack interval, never a destination or
an event region.

`tok` is the count the three reading words carry on acceptance; `terms` is the
events' per-record contribution, and the post states it as the fold over the
witness's own `obs` rather than as a free number.  `nextEnd` is the allocator
cursor the run's stack writes reached; it is a witness because the allocator is
the callee's. -/
def stage2NoEventBoundary (args : List Value) (mem : Mem) (next : Nat)
    (m : Mem) (v : Value) : Prop :=
  ∃ (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat)
    (verdict : BitVec 64) (tok terms : Nat) (bs arena : List UInt8)
    (obs : List ConsumerEvent) (toks : List Token) (stk e c d nextEnd : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
            .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
            .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap),
            .ptr tokensOut, .ptr valuesOut, .ptr sumOut, .ptr err] ∧
    -- the return carries the ABI's verdict word and no other value
    v = .int 64 verdict ∧
    -- the ABI's verdict
    (verdict = 0 ∨ verdict = 1) ∧
    -- **the document the run read**: the caller's staged input, which is what
    -- anchors the accepted arm's relation.  This is a read of the caller's
    -- object, not a claim that the run wrote anywhere; the write claims are the
    -- three words, `*err` on refusal, and the frame.
    readBytes mem b n = some bs ∧
    -- **the accepted arm**: the three words hold the reading
    (verdict = 1 →
      readBytes m tokensOut 8 = some (wordBytes 8 tok) ∧
      readBytes m valuesOut 8 = some (wordBytes 8 tok) ∧
      readBytes m sumOut 8 =
        some (wordBytes 8 ((byteSum arena + terms) % 2 ^ 64)) ∧
      -- the counts are the document's, hence below the word's width
      tok ≤ n ∧ tok < 2 ^ 64 ∧
      -- the existential arena is the events', at the parser's tokens
      Stage2NoEvent bs arena obs toks ∧
      obs.length = tok ∧
      terms = (obs.map ConsumerEvent.terms).sum) ∧
    -- **the refusal arm**: the three words are zero, and `*err` carries the offset
    (verdict = 0 →
      readBytes m tokensOut 8 = some (wordBytes 8 0) ∧
      readBytes m valuesOut 8 = some (wordBytes 8 0) ∧
      readBytes m sumOut 8 = some (wordBytes 8 0) ∧
      ∃ eo : Nat, eo ≤ n ∧ readBytes m err 8 = some (wordBytes 8 eo)) ∧
    -- and unchanged on acceptance, because nothing writes it
    (verdict = 1 → readBytes m err 8 = readBytes mem err 8) ∧
    -- presence at the four output words, and nothing else
    (∀ a, inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) a →
      present m a) ∧
    -- silence outside the run's whole touched extent: the four output words, the
    -- caller's scratch, the four staged objects, and the stack interval
    (next ≤ nextEnd ∧
      UnchangedOutside mem m
        (stage2NoEventWrites tokensOut valuesOut sumOut err ++
          (stage2NoEventRunRegions scratch scratchcap stk e c d ++
            [(next, nextEnd - next)])))

/-- What the run leaves at the caller's staging, at the outcome it produces.
`.ub` is refused by the match, and a return that carries no value or a value of
another shape is outside `stage2NoEventBoundary`'s `v = .int 64 verdict`. -/
def stage2NoEventPost (args : List Value) (mem : Mem) (next : Nat)
    (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some v) m => stage2NoEventBoundary args mem next m v
  | .ret none _ => False

/-! ### The boundary by name

The post quantifies its witnesses as a flat tuple, so a consumer that reads
several of them destructures by position and a witness added anywhere shifts
every later one in every consumer at once.  The two structures below name the
tuple's components in the idiom `Stage2BoundaryWitness`/`Stage2BoundaryFacts`
use: the lemmas named here are the only place the positional form is written, a
new witness is one field in each structure, and a new clause one field of the
facts. -/

/-- **The witnesses of `stage2NoEventBoundary`, by name.** -/
structure Stage2NoEventWitness where
  b : Nat
  n : Nat
  ep : Nat
  nep : Nat
  xp : Nat
  nxp : Nat
  scratch : Nat
  scratchcap : Nat
  tokensOut : Nat
  valuesOut : Nat
  sumOut : Nat
  err : Nat
  verdict : BitVec 64
  /-- The count the three reading words carry on acceptance. -/
  tok : Nat
  /-- The events' per-record contribution to the sum: `Σ tag + len + payload`. -/
  terms : Nat
  /-- The document's bytes, as the run read them. -/
  bs : List UInt8
  /-- The decoded string bodies, in document order: the fold's arena input.  It is
  a list, not a memory region, because the entry materialises no arena. -/
  arena : List UInt8
  /-- The consumer's events, in order. -/
  obs : List ConsumerEvent
  /-- The reference parser's tokens. -/
  toks : List Token
  /-- The container stack `%stk`. -/
  stk : Nat
  /-- The refusal record `%e`. -/
  e : Nat
  /-- The cursor record `%c`. -/
  c : Nat
  /-- The number path's output slot `%d`. -/
  d : Nat
  /-- The allocator cursor the run's stack writes reached. -/
  nextEnd : Nat

/-- **The conjuncts of `stage2NoEventBoundary`, at named witnesses.**  Each field
is one clause of the post, stated at `w`'s components; the frame's `next ≤ nextEnd`
is split from the silence claim so the two read separately. -/
structure Stage2NoEventFacts (w : Stage2NoEventWitness) (args : List Value)
    (mem : Mem) (next : Nat) (m : Mem) (v : Value) : Prop where
  /-- The arguments are the twelve slots `stage2_noevent.h` names. -/
  args_eq : args = [.ptr w.b, .int 64 (BitVec.ofNat 64 w.n), .ptr w.ep,
    .int 64 (BitVec.ofNat 64 w.nep), .ptr w.xp, .int 64 (BitVec.ofNat 64 w.nxp),
    .ptr w.scratch, .int 64 (BitVec.ofNat 64 w.scratchcap), .ptr w.tokensOut,
    .ptr w.valuesOut, .ptr w.sumOut, .ptr w.err]
  /-- The return carries the ABI's verdict word and no other value. -/
  value_eq : v = .int 64 w.verdict
  /-- The ABI's verdict. -/
  verdict_range : w.verdict = 0 ∨ w.verdict = 1
  /-- The document the run read: the caller's staged input. -/
  doc : readBytes mem w.b w.n = some w.bs
  /-- The token word, on acceptance. -/
  accept_tokens : w.verdict = 1 →
    readBytes m w.tokensOut 8 = some (wordBytes 8 w.tok)
  /-- The value word, on acceptance: the declared build mode's `values = tokens`. -/
  accept_values : w.verdict = 1 →
    readBytes m w.valuesOut 8 = some (wordBytes 8 w.tok)
  /-- The sum word, on acceptance: the modular fact. -/
  accept_sum : w.verdict = 1 →
    readBytes m w.sumOut 8 =
      some (wordBytes 8 ((byteSum w.arena + w.terms) % 2 ^ 64))
  /-- The count is at most the document's length. -/
  accept_tok_le : w.verdict = 1 → w.tok ≤ w.n
  /-- And therefore inside the word's width: the count is exact. -/
  accept_tok_lt : w.verdict = 1 → w.tok < 2 ^ 64
  /-- The run's events are the document's, at the parser's tokens. -/
  accept_rel : w.verdict = 1 → Stage2NoEvent w.bs w.arena w.obs w.toks
  /-- The count is the events' count. -/
  accept_len : w.verdict = 1 → w.obs.length = w.tok
  /-- The contribution is the fold's over the events. -/
  accept_terms : w.verdict = 1 → w.terms = (w.obs.map ConsumerEvent.terms).sum
  /-- The token word, on refusal: zero. -/
  refuse_tokens : w.verdict = 0 →
    readBytes m w.tokensOut 8 = some (wordBytes 8 0)
  /-- The value word, on refusal: zero. -/
  refuse_values : w.verdict = 0 →
    readBytes m w.valuesOut 8 = some (wordBytes 8 0)
  /-- The sum word, on refusal: zero. -/
  refuse_sum : w.verdict = 0 →
    readBytes m w.sumOut 8 = some (wordBytes 8 0)
  /-- The refusal word, written exactly on refusal. -/
  refuse_word : w.verdict = 0 →
    ∃ eo : Nat, eo ≤ w.n ∧ readBytes m w.err 8 = some (wordBytes 8 eo)
  /-- The refusal word, unchanged on acceptance. -/
  accept_word : w.verdict = 1 → readBytes m w.err 8 = readBytes mem w.err 8
  /-- Presence at the four output words. -/
  present : ∀ a, inRegions (stage2NoEventWrites w.tokensOut w.valuesOut w.sumOut
    w.err) a → present m a
  /-- The caller's cursor lies inside the stack region the run kept. -/
  next_le : next ≤ w.nextEnd
  /-- Silence outside the run's whole touched extent. -/
  frame : UnchangedOutside mem m
    (stage2NoEventWrites w.tokensOut w.valuesOut w.sumOut w.err ++
      (stage2NoEventRunRegions w.scratch w.scratchcap w.stk w.e w.c w.d ++
        [(next, w.nextEnd - next)]))

/-- **The boundary's witnesses, from the post.**  This is the only place the
post's existential is unpacked. -/
theorem stage2NoEventBoundary_witness {args : List Value} {mem : Mem} {next : Nat}
    {m : Mem} {v : Value} (h : stage2NoEventBoundary args mem next m v) :
    ∃ w : Stage2NoEventWitness, Stage2NoEventFacts w args mem next m v := by
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, verdict, tok, terms, bs, arena, obs, toks, stk, e, c, d,
    nextEnd, hargs, hval, hvr, hdoc, hacc, hrefuse, hword, hpresent, hnext,
    hframe⟩ := h
  exact ⟨
    { b := b, n := n, ep := ep, nep := nep, xp := xp, nxp := nxp,
      scratch := scratch, scratchcap := scratchcap, tokensOut := tokensOut,
      valuesOut := valuesOut, sumOut := sumOut, err := err, verdict := verdict,
      tok := tok, terms := terms, bs := bs, arena := arena, obs := obs,
      toks := toks, stk := stk, e := e, c := c, d := d, nextEnd := nextEnd },
    { args_eq := hargs, value_eq := hval, verdict_range := hvr, doc := hdoc,
      accept_tokens := fun hv => (hacc hv).1,
      accept_values := fun hv => (hacc hv).2.1,
      accept_sum := fun hv => (hacc hv).2.2.1,
      accept_tok_le := fun hv => (hacc hv).2.2.2.1,
      accept_tok_lt := fun hv => (hacc hv).2.2.2.2.1,
      accept_rel := fun hv => (hacc hv).2.2.2.2.2.1,
      accept_len := fun hv => (hacc hv).2.2.2.2.2.2.1,
      accept_terms := fun hv => (hacc hv).2.2.2.2.2.2.2,
      refuse_tokens := fun hv => (hrefuse hv).1,
      refuse_values := fun hv => (hrefuse hv).2.1,
      refuse_sum := fun hv => (hrefuse hv).2.2.1,
      refuse_word := fun hv => (hrefuse hv).2.2.2,
      accept_word := hword, present := hpresent, next_le := hnext,
      frame := hframe }⟩

/-- **The post, from named witnesses.**  This is the only place the post's
existential is built from named components. -/
theorem stage2NoEventBoundary_of_witness {args : List Value} {mem : Mem}
    {next : Nat} {m : Mem} {v : Value} {w : Stage2NoEventWitness}
    (h : Stage2NoEventFacts w args mem next m v) :
    stage2NoEventBoundary args mem next m v := by
  refine ⟨w.b, w.n, w.ep, w.nep, w.xp, w.nxp, w.scratch, w.scratchcap,
    w.tokensOut, w.valuesOut, w.sumOut, w.err, w.verdict, w.tok, w.terms,
    w.bs, w.arena, w.obs, w.toks, w.stk, w.e, w.c, w.d, w.nextEnd, h.args_eq,
    h.value_eq, h.verdict_range, h.doc, ?_, ?_, h.accept_word, h.present, h.next_le,
    h.frame⟩
  · intro hacc
    exact ⟨h.accept_tokens hacc, h.accept_values hacc, h.accept_sum hacc,
      h.accept_tok_le hacc, h.accept_tok_lt hacc, h.accept_rel hacc,
      h.accept_len hacc, h.accept_terms hacc⟩
  · intro hrej
    exact ⟨h.refuse_tokens hrej, h.refuse_values hrej, h.refuse_sum hrej,
      h.refuse_word hrej⟩

/-- **The post and its named form are the same statement.** -/
theorem stage2NoEventBoundary_iff {args : List Value} {mem : Mem} {next : Nat}
    {m : Mem} {v : Value} :
    stage2NoEventBoundary args mem next m v ↔
      ∃ w : Stage2NoEventWitness, Stage2NoEventFacts w args mem next m v :=
  ⟨stage2NoEventBoundary_witness, fun ⟨_, h⟩ => stage2NoEventBoundary_of_witness h⟩

/-- **The exact sum, from the modular word.**  The post's sum word holds the
mathematical sum modulo `2 ^ 64`; when the sum fits the word, the word *is* the
sum.  This is the separate condition a consumer that needs the exact reading
supplies — the committed corpus satisfies it by construction, and no universal
statement can. -/
theorem stage2NoEventBoundary_sum_exact {args : List Value} {mem : Mem}
    {next : Nat} {m : Mem} {v : Value} {w : Stage2NoEventWitness}
    (h : Stage2NoEventFacts w args mem next m v) (hacc : w.verdict = 1)
    (hbound : byteSum w.arena + w.terms < 2 ^ 64) :
    readBytes m w.sumOut 8 = some (wordBytes 8 (byteSum w.arena + w.terms)) := by
  rw [h.accept_sum hacc, Nat.mod_eq_of_lt hbound]

/-! ### The budget -/

/-- One entry's allowance: the dispatch arm, the accumulations and the per-body
constants of the decoder's call. -/
def stage2NoEventEntryAllowance : Nat := 32

/-- One document byte's allowance: the gap and body scans and the decoder's
`n / 64` per-body term. -/
def stage2NoEventByteAllowance : Nat := 8

/-- One escape position's allowance: the expander's scan and its decode walk. -/
def stage2NoEventPositionAllowance : Nat := 32

/-- The initialisation, the end-of-stream checks and the terminal stores. -/
def stage2NoEventFinalisationAllowance : Nat := 32

/-- The no-event walk's fuel, as a term of the arguments the ABI carries: one
allowance per entry, per document byte and per escape position, plus the
finalisation blocks.  It is `stage2Budget`'s term read at this entry's arguments;
the memory parameter is not read, and the scratch capacity is not a term because
the reserve is one comparison. -/
def stage2NoEventBudget (args : List Value) (_mem : Mem) : Nat :=
  match args with
  | [.ptr _, .int 64 n, .ptr _, .int 64 nep, .ptr _, .int 64 nxp, .ptr _,
     .int 64 _, .ptr _, .ptr _, .ptr _, .ptr _] =>
      stage2NoEventEntryAllowance * nep.toNat + stage2NoEventByteAllowance * n.toNat +
        stage2NoEventPositionAllowance * nxp.toNat + stage2NoEventFinalisationAllowance
  | _ => 0

/-! ### The record -/

/-- **The no-event stage-2 unit's boundary record**, `Γ_stage2_noevent`: the
staging above, the walk's fuel term, and the boundary projection of the run's
outcome.  It is the record `satisfies_calls_stage2_noevent` turns into the
`CallSatisfies` a pipeline slot takes. -/
def Γ_stage2_noevent : MemContract where
  budget := stage2NoEventBudget
  pre := stage2NoEventPre
  post := stage2NoEventPost

/-! ### Axiom footprints -/

#print axioms stage2NoEventBoundary_witness
#print axioms stage2NoEventBoundary_of_witness
#print axioms stage2NoEventBoundary_iff
#print axioms stage2NoEventBoundary_sum_exact

end LeanLLVM.Refinement
