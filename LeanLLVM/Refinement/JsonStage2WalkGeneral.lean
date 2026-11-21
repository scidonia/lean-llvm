/-
The general document's row, over the staged entry stream.

The rows in `JsonStage2WalkRowSteps` and `JsonStage2WalkRowArms` are documents:
`[1,2]` and `["ab","cd"]` each fix their tokens, their entry lanes and their
carries, and compose the arms' net effects at those carries.  What they share is
the loop's shape — one arm per token, the index moving past that token's entries —
and what differs between them is how many entries a token costs.  A token's start
lane is an entry of the staged stream; a string's closing quote is a second one
(`kernel/json/stage2.h:60`, `Token.entryLanes`).  The number document's five
tokens are five entries, the string document's five are seven, and the walk's
carry counts lanes while the row counts tokens.

This module states and proves the row at that generality:

* `WalkTraceStepAt` is one token's revolution at the staged stream: the token the
  step consumes, the entry advance that token costs — `Token.entryLanes [tok]`'s
  length, so one lane for a start and two for a string — and the correspondence at
  the next token.  Its three producers are the arms' own forms:
  `WalkTraceStepAt.emit` for a one-lane token that appends its record,
  `WalkTraceStepAt.separator` for a comma or a colon, which appends none, and
  `WalkTraceStepAt.emit_two` for a string's two lanes: the arm's merge keeps the
  index and appends its record, and the header's `%inc208.i` then moves the index
  past the closing quote;
* `WalkTraceChainAt` is a run of such steps, indexed by the token count and
  carrying both the index the run starts at and the index it ends at, so a chain's
  entry advance is the lanes of the tokens it consumed (`k_eq`) and its end index is
  the start plus its length (`end_eq`).  `WalkTraceChainAt.of_steps` is the
  induction: a step at every head token composes for any number of tokens, and
  `WalkTraceChainAt.traceRow` reads the end as the row;
* `walkTraceRow_of_quoteSteps` is the general row: at any tape and geometry the
  staging supplies (`WalkAlignQuoted`), with a step at every token index and the
  seed's correspondence, the walk reaches the whole document's row and the end of
  the staged stream;
* the payload arms produce their steps at the tape's own tokens:
  `stepAt_number` is the numeral's decomposition and lexeme read-back,
  `stepAt_string_plain` the plain form's body read-back, and `stepAt_string_arena`
  the write-back form's arena slice.  A container's record is the tape's own span
  and byte (`stepAt_punct`), and a literal's step is `WalkTraceStepAt.emit` at the
  record `tokenRecord_null_of_tape`, `tokenRecord_true_of_tape` or
  `tokenRecord_false_of_tape` gives.

**The string-free staging is the entry-stream one.**  Where no token is a string
the two streams coincide (`Token.entryLanes_stringFree`): the lane list is the
tokens' starts, `WalkAlignQuoted` implies `WalkAlign`
(`WalkAlign.of_alignQuoted_stringFree`), and the row is
`walkTraceRow_of_revolutions`'s (`walkTraceRow_of_revolutions_quoteFree`).  That is
the case the containers', the literals', the numbers' and the separators' rows are
stated in, and the general chain's one-lane steps are its steps.

**What the row still takes.**  It is about the walk's trace, so the facts that
name a run's state stay premises: the seed's correspondence, and at every token the
arm's own net effect — for a container or a literal the record its span gives, for
a payload the read-back the arm's choice of form supplies, and for every arm the
carry it reaches and the index its back edge leaves.  The arms' `WalkInv`s, their
bundles and their `WalkSegment`s are not read here: `JsonStage2WalkRowArms`'
`numberArmSegment`, `stringArmSegment` and `stringArenaArmSegment` compose a head's
bundle to those carries and expose the merge's kept index and appended record, and
the header's back edge then supplies the index the step advances by — the two
equations `stepAt_number`, `stepAt_string_plain` and `stepAt_string_arena` take.

The document `[1,"ab"]` is the mixed instance: a number, a comma and a string in
one bracket, so one step costs two lanes among steps that cost one.  Its row is
`row_numberStringDocument`.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRowSteps
import LeanLLVM.Refinement.JsonStage2WalkRowArms

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The lanes a token costs

A token's entry count is `Token.entryLanes [tok]`'s length: one lane at its start
and, at a string, its closing quote beside it.  The two readings below turn that
length into the arithmetic a chain's advance uses. -/

/-- **One token's lane count.**  A start lane, and a string's close lane after it. -/
theorem Token.entryLanes_singleton_length (tok : Token) :
    (Token.entryLanes [tok]).length = 1 + (Token.closeLane tok).length := by
  rw [Token.entryLanes_cons, Token.entryLanes_nil, List.length_cons, List.length_append,
    List.length_nil]
  omega

/-- **The lane count of a list's head and tail.**  The count of a staged list is its
head's lanes and the rest's, which is what a chain's index advance adds up. -/
theorem Token.entryLanes_length_cons (tok : Token) (rest : List Token) :
    (Token.entryLanes (tok :: rest)).length =
      (Token.entryLanes [tok]).length + (Token.entryLanes rest).length := by
  rw [Token.entryLanes_cons, List.length_cons, List.length_append,
    Token.entryLanes_singleton_length]
  omega

/-- **A token at an index is the dropped list's head.**  The token a step reads is
the one the chain's drop names, so the lane count the step advances by is that
token's. -/
theorem list_drop_eq_cons_of_getElem? {α : Type} {l : List α} {j : Nat} {tok : α}
    (h : l[j]? = some tok) : l.drop j = tok :: l.drop (j + 1) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hj, hget]

/-- **`take (n + 1)` of a dropped list.**  The token there, and the remaining `n`
from the index after it: the split a chain's advance is read through. -/
theorem list_take_succ_drop_eq_cons {α : Type} {l : List α} {j n : Nat} {tok : α}
    (h : l[j]? = some tok) :
    (l.drop j).take (n + 1) = tok :: (l.drop (j + 1)).take n := by
  rw [list_drop_eq_cons_of_getElem? h, List.take_succ_cons]

/-! ### One token's revolution

The step is the trace half of a revolution at the staged stream: the token, the
lanes it costs, and the correspondence one token on.  The entry index is not part
of the statement — a step reads the carry it starts at — but the token's lane count
is, because that is the advance the string arm makes and the one-lane arms do not.
-/

/-- **One token's step at the staged stream.**  The step consumes the tape's token
at the index, the index advances by that token's lanes, and the trace is the records
of the tokens before the next one.  The token is a constructor argument rather than
a projected field: a step is a proposition about the run, and its token is read by
case analysis, as `WalkRevolution`'s are. -/
inductive WalkTraceStepAt {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C C' : WalkCarry G) (j : Nat) : Prop where
  /-- The consumed token, the tape's reading of it, the entry advance it costs, and
  the correspondence one token on. -/
  | intro (tok : Token) (htok : t.tokens[j]? = some tok)
      (k' : C'.k = C.k + (Token.entryLanes [tok]).length)
      (trace : WalkTracePrefixAt G arena t C' (j + 1)) :
      WalkTraceStepAt G arena t C C' j

namespace WalkTraceStepAt

/-- **The step's trace.** -/
theorem trace_of {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j : Nat} (h : WalkTraceStepAt G arena t C C' j) :
    WalkTracePrefixAt G arena t C' (j + 1) := by
  obtain ⟨_, _, _, htrace⟩ := h
  exact htrace

/-- **A one-lane step that appends its record.**  A token that is not a string costs
one entry, and its arm appends one record: `WalkTracePrefixAt.emit_advance`'s
append and advance, read as a step. -/
theorem emit {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j : Nat} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefixAt G arena t C j) (htok : t.tokens[j]? = some tok)
    (hns : ∀ sp : Span, tok ≠ .string sp)
    (hrec : TokenRecord G.bs arena r tok)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events ++ [r]) :
    WalkTraceStepAt G arena t C C' j :=
  WalkTraceStepAt.intro tok htok
    (by
      rw [hk, Token.entryLanes_start (rest := []) hns]
      simp [Token.entryLanes_nil])
    (WalkTracePrefixAt.emit_advance h htok hrec rfl hev)

/-- **A separator's step.**  A comma or a colon costs one entry and appends no
record, so the index moves and the correspondence does not change. -/
theorem separator {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j : Nat} {p : Punct} {s : Span}
    (h : WalkTracePrefixAt G arena t C j)
    (htok : t.tokens[j]? = some (.punct p s)) (hp : p = .comma ∨ p = .colon)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events) :
    WalkTraceStepAt G arena t C C' j :=
  WalkTraceStepAt.intro (.punct p s) htok
    (by
      rw [hk, Token.entryLanes_start (rest := []) (by intro sp h; cases h)]
      simp [Token.entryLanes_nil])
    (WalkTracePrefixAt.advance_separator h htok hp rfl hev)

/-- **A string's step, its two lanes.**  The arm's merge keeps the entry index and
appends the record (`Cd`); the header's `%inc208.i` then takes the closing quote, so
the index advances by two and the token index by one. -/
theorem emit_two {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C Cd C' : WalkCarry G} {j : Nat} {sp : Span} {r : EventRecord}
    (h : WalkTracePrefixAt G arena t C j)
    (htok : t.tokens[j]? = some (.string sp))
    (hrec : TokenRecord G.bs arena r (.string sp))
    (hkC : Cd.k = C.k) (hevC : Cd.events = C.events ++ [r])
    (hk' : C'.k = Cd.k + 2) (hev' : C'.events = Cd.events) :
    WalkTraceStepAt G arena t C C' j :=
  WalkTraceStepAt.intro (.string sp) htok
    (by
      rw [hk', hkC, Token.entryLanes_string]
      simp [Token.entryLanes_nil])
    (WalkTracePrefixAt.emit_two h htok hrec hkC hevC hk' hev').1

/-- **The one-lane step a `WalkTraceStep` gives.**  At a staging whose entries are
the token starts, a one-entry revolution is a one-lane step; the token it
consumes is the one the trace correspondence is read at.  This is how the
entry-stream engine's steps enter the token-indexed chain. -/
theorem of_step {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hns : ∀ sp : Span, tok ≠ .string sp)
    (hrec : TokenRecord G.bs arena r tok)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events ++ [r]) :
    WalkTraceStepAt G arena t C C' C.k :=
  emit (WalkTracePrefixAt.of_prefix h) htok hns hrec hk hev

end WalkTraceStepAt

/-! ### The run of revolutions, at the token index

`WalkTraceChainAt` is the token-indexed chain: `n` steps from token index `j` to
`j end`, carrying both indices because a string's step moves the token index by one
and the entry index by two.  Its advance is the lanes of the tokens it consumed and
its end index is its start plus its length, so the row is read at the whole list. -/

/-- **A run of revolutions at the token index.**  `n` steps from the carry `C` at
token index `j` to `C'` at `jend`. -/
inductive WalkTraceChainAt {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape) :
    Nat → Nat → WalkCarry G → WalkCarry G → Nat → Prop
  /-- No steps: the carry and the index stand. -/
  | zero (j : Nat) (C : WalkCarry G) : WalkTraceChainAt G arena t 0 j C C j
  /-- One step, then the rest. -/
  | succ {n j jend : Nat} {C C' C'' : WalkCarry G}
      (h : WalkTraceStepAt G arena t C C' j)
      (hs : WalkTraceChainAt G arena t n (j + 1) C' C'' jend) :
      WalkTraceChainAt G arena t (n + 1) j C C'' jend

namespace WalkTraceChainAt

/-- **The chain carries the correspondence.** -/
theorem carries {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n j jend : Nat} {C C' : WalkCarry G}
    (h : WalkTraceChainAt G arena t n j C C' jend) :
    WalkTracePrefixAt G arena t C j → WalkTracePrefixAt G arena t C' jend := by
  intro hpre
  induction h with
  | zero j C => exact hpre
  | succ hstep _ ih => exact ih (WalkTraceStepAt.trace_of hstep)

/-- **The chain's end index.**  `n` steps from `j` reach `j + n`. -/
theorem end_eq {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n j jend : Nat} {C C' : WalkCarry G}
    (h : WalkTraceChainAt G arena t n j C C' jend) : jend = j + n := by
  induction h with
  | zero j C => simp
  | succ _ _ ih => rw [ih]; omega

/-- **The chain's entry advance.**  `n` steps from `j` consume exactly the tokens
`j` to `j + n`, so the index moves by their staged lanes. -/
theorem k_eq {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n j jend : Nat} {C C' : WalkCarry G}
    (h : WalkTraceChainAt G arena t n j C C' jend) :
    C'.k = C.k + (Token.entryLanes ((t.tokens.drop j).take n)).length := by
  induction h with
  | zero j C => simp [Token.entryLanes_nil]
  | @succ n j jend C C' C'' hstep hs ih =>
      obtain ⟨tok, htok, hk, _⟩ := hstep
      rw [ih, hk]
      have hsplit : (Token.entryLanes ((t.tokens.drop j).take (n + 1))).length =
          (Token.entryLanes [tok]).length +
            (Token.entryLanes ((t.tokens.drop (j + 1)).take n)).length := by
        rw [list_take_succ_drop_eq_cons htok]
        exact Token.entryLanes_length_cons tok _
      rw [hsplit]
      omega

/-- **The row at the chain's end.**  A chain that ends at the whole token list has
the row as its trace. -/
theorem traceRow {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n j jend : Nat} {C C' : WalkCarry G}
    (h : WalkTraceChainAt G arena t n j C C' jend)
    (hpre : WalkTracePrefixAt G arena t C j) (hend : jend = t.tokens.length) :
    WalkTraceRow G.bs arena t C'.events :=
  WalkTracePrefixAt.toTraceRow (carries h hpre) hend

/-- **The induction over tokens.**  A step at every head token composes for any
number of tokens: from index `j`, `m` steps reach a carry and an index, as long as
`j + m` is the whole list. -/
theorem of_steps {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    (hstep : ∀ (j : Nat) (C : WalkCarry G), j < t.tokens.length →
      WalkTracePrefixAt G arena t C j → ∃ C', WalkTraceStepAt G arena t C C' j) :
    ∀ (m j : Nat) (C : WalkCarry G), j + m = t.tokens.length →
      WalkTracePrefixAt G arena t C j →
      ∃ C' jend, WalkTraceChainAt G arena t m j C C' jend := by
  intro m
  induction m with
  | zero =>
      intro j C _ hpre
      exact ⟨C, j, WalkTraceChainAt.zero j C⟩
  | succ m ih =>
      intro j C hle hpre
      have hj : j < t.tokens.length := by omega
      obtain ⟨C', hstep'⟩ := hstep j C hj hpre
      have hle' : (j + 1) + m = t.tokens.length := by omega
      obtain ⟨C'', jend, hchain⟩ := ih (j + 1) C' hle' (WalkTraceStepAt.trace_of hstep')
      exact ⟨C'', jend, WalkTraceChainAt.succ hstep' hchain⟩

end WalkTraceChainAt

/-- **The general document's row.**  At a tape and geometry the quote-inclusive
staging supplies, a step at every token index and the seed's correspondence give the
walk's row at the end of the staged stream: the chain's entry advance is the lanes
of the whole token list, which the staging's entry count is. -/
theorem walkTraceRow_of_quoteSteps {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ : WalkCarry G}
    (hal : WalkAlignQuoted G t)
    (hstep : ∀ (j : Nat) (C : WalkCarry G), j < t.tokens.length →
      WalkTracePrefixAt G arena t C j → ∃ C', WalkTraceStepAt G arena t C C' j)
    (hk₀ : C₀.k = 0) (hpre₀ : WalkTracePrefixAt G arena t C₀ 0) :
    ∃ (C : WalkCarry G), C.k = G.nep ∧ WalkTraceRow G.bs arena t C.events := by
  obtain ⟨C, jend, hchain⟩ :=
    WalkTraceChainAt.of_steps hstep t.tokens.length 0 C₀ (Nat.zero_add _) hpre₀
  have hend : jend = t.tokens.length := by
    rw [WalkTraceChainAt.end_eq hchain]
    omega
  have hk : C.k = C₀.k +
      (Token.entryLanes ((t.tokens.drop 0).take t.tokens.length)).length :=
    WalkTraceChainAt.k_eq hchain
  refine ⟨C, ?_, WalkTraceChainAt.traceRow hchain hpre₀ hend⟩
  rw [hk, hk₀, List.drop_zero, List.take_length, hal.nep]
  exact Nat.zero_add _

/-! ### The payload arms' steps at the tape's tokens

Each payload arm's record is the tape's, with the arm's choice of form as the
read-back: the numeral's decomposition, the plain form's raw body, or the
write-back form's arena slice.  The arm's own net effect — the merge carry it keeps
and the back edge that advances — is stated beside each, and `emit_two` reads the
string's two lanes from it.

The three theorems take the tape's `decodeTape` and the staging's document; the
span facts the record constructors need are the tape's own (`tape_bodyCodePoints`
and the span bookkeeping the `TokenRecord` constructors carry), so only the arm's
payload read-back is left. -/

/-- **The number arm's step.**  The numeral's record is `strtodSpec`'s bits of a
well-formed decomposition whose lexeme is the span's bytes; the arm appends it and
keeps the index at its merge, and the back edge moves the entry index one on. -/
theorem stepAt_number {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C C' : WalkCarry G} {j : Nat} {v : JSON.Value} {sp : Span}
    (hal : WalkAlignQuoted G t) (hpre : WalkTracePrefixAt G arena t C j)
    (hdec : decodeTape t = some v) (htok : t.tokens[j]? = some (.number sp))
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : d.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start))
    (hk : C'.k = C.k + 1)
    (hev : C'.events = C.events ++ [EventRecord.number (strtodSpec d).toBits]) :
    WalkTraceStepAt G arena t C C' j :=
  WalkTraceStepAt.emit hpre htok (by intro s h; cases h)
    (tokenRecord_number_of_tape hdec hal.input (List.mem_of_getElem? htok) hwf hlex) hk hev

/-- **The plain string arm's step, its two lanes.**  The span opens and closes with
the quotation mark, its body's code points are the grammar's
(`tape_bodyCodePoints`), and the arm's raw body reads back to them — its own choice
of form.  The record's length is the body's extent (`%sub260.i`) and its offset the
body's start with the top bit set (`strOr`); the merge keeps the index and the back
edge takes the closing quote. -/
theorem stepAt_string_plain {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C Cd C' : WalkCarry G} {j : Nat} {v : JSON.Value} {sp : Span}
    (hal : WalkAlignQuoted G t) (hpre : WalkTracePrefixAt G arena t C j)
    (hdec : decodeTape t = some v) (htok : t.tokens[j]? = some (.string sp))
    (hquote : sp.start + 2 ≤ sp.stop)
    (hbody : ∀ cs : List Nat, bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((G.bs.drop (sp.start + 1)).take (sp.stop - sp.start - 2)) =
        some cs)
    (hkC : Cd.k = C.k)
    (hevC : Cd.events = C.events ++
      [EventRecord.str false (sp.stop - sp.start - 2) (plainSpan (sp.start + 1))])
    (hk' : C'.k = Cd.k + 2) (hev' : C'.events = Cd.events) :
    WalkTraceStepAt G arena t C C' j := by
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  have hspan : sp.stop = sp.start + 2 + (sp.stop - sp.start - 2) := by omega
  exact WalkTraceStepAt.emit_two hpre htok
    (tokenRecord_string_plain_of_tape hdec hal.input (List.mem_of_getElem? htok)
      hspan hcode (hbody cs hcode))
    hkC hevC hk' hev'

/-- **The write-back string arm's step, its two lanes.**  The span holds its two
quotes, and the arm's arena slice at its decoded length and offset reads back to the
span's code points — the escape unit's answer.  The record is that slice's form, and
the two lanes are `emit_two`'s. -/
theorem stepAt_string_arena {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C Cd C' : WalkCarry G} {j : Nat} {v : JSON.Value} {sp : Span} {len off : Nat}
    (hal : WalkAlignQuoted G t) (hpre : WalkTracePrefixAt G arena t C j)
    (hdec : decodeTape t = some v) (htok : t.tokens[j]? = some (.string sp))
    (hquote : sp.start + 2 ≤ sp.stop) (hoff : off < 2 ^ 63)
    (harena : ∀ cs : List Nat, bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((arena.drop off).take len) = some cs)
    (hkC : Cd.k = C.k)
    (hevC : Cd.events = C.events ++ [EventRecord.str false len off])
    (hk' : C'.k = Cd.k + 2) (hev' : C'.events = Cd.events) :
    WalkTraceStepAt G arena t C C' j := by
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  exact WalkTraceStepAt.emit_two hpre htok
    (tokenRecord_string_arena_of_tape hdec hal.input (List.mem_of_getElem? htok)
      hquote hoff hcode (harena cs hcode))
    hkC hevC hk' hev'

/-! ### The containers' steps

A container is one lane, and its record is the document's byte at its span.  The
tape's own span discipline makes the span one byte (`checkSpans_mem`), so the four
containers' records need neither the alignment nor the walk's state: the document's
byte at the span is the punctuation's (`punctByte`), and `TokenRecord`'s container
constructor gives the tag (`punctTag`).  A literal's step is `WalkTraceStepAt.emit`
at its record, which `tokenRecord_null_of_tape`, `tokenRecord_true_of_tape` and
`tokenRecord_false_of_tape` give from the tape. -/

/-- **A container's step, its record from the tape's span.**  The span is one byte
and the document's byte there is the punctuation's; the record is `TokenRecord`'s
container constructor at that byte, and the step is `emit`'s one lane. -/
theorem stepAt_punct {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C C' : WalkCarry G} {j : Nat} {p : Punct} {s : Span}
    (hspans : spansWellFormed t = true)
    (hpre : WalkTracePrefixAt G arena t C j)
    (htok : t.tokens[j]? = some (.punct p s))
    (hp : p = .openBrace ∨ p = .closeBrace ∨ p = .openBracket ∨ p = .closeBracket)
    (hbyte : G.bs[s.start]? = some (punctByte p))
    (hk : C'.k = C.k + 1)
    (hev : C'.events = C.events ++ [EventRecord.tag (punctTag p)]) :
    WalkTraceStepAt G arena t C C' j := by
  obtain ⟨-, -, hdisc⟩ := checkSpans_mem (prev := 0) hspans (List.mem_of_getElem? htok)
  have hstop : s.stop = s.start + 1 := hdisc p s rfl
  refine WalkTraceStepAt.emit hpre htok (by intro sp h; cases h) ?_ hk hev
  rcases hp with rfl | rfl | rfl | rfl
  · exact TokenRecord.openBrace hbyte hstop
  · exact TokenRecord.closeBrace hbyte hstop
  · exact TokenRecord.openBracket hbyte hstop
  · exact TokenRecord.closeBracket hbyte hstop

/-! ### The string-free staging is the entry stream's

Where no token is a string the staged lane list is the tokens' starts, so the two
stagings say the same thing and `walkTraceRow_of_revolutions` states the row.  The
two readings below are that coincidence: the lane count and the start lane at an
index. -/

/-- **A string-free list's lane count is its token count.** -/
theorem Token.entryLanes_length_of_no_string :
    ∀ (toks : List Token), (∀ u ∈ toks, ∀ sp : Span, u ≠ .string sp) →
      (Token.entryLanes toks).length = toks.length
  | [], _ => rfl
  | tok :: rest, hfree => by
      have htok : ∀ sp : Span, tok ≠ .string sp :=
        fun sp hs => hfree tok (List.mem_cons_self ..) sp hs
      have hrest : ∀ u ∈ rest, ∀ sp : Span, u ≠ .string sp :=
        fun u hu sp hs => hfree u (List.mem_cons_of_mem _ hu) sp hs
      rw [Token.entryLanes_start htok, List.length_cons,
        Token.entryLanes_length_of_no_string rest hrest, List.length_cons]

/-- **A string-free list's lane at an index is its token's start.** -/
theorem Token.entryLanes_getElem?_start_of_no_string :
    ∀ (toks : List Token), (∀ u ∈ toks, ∀ sp : Span, u ≠ .string sp) →
      ∀ (k : Nat) (tok : Token), toks[k]? = some tok →
        (Token.entryLanes toks)[k]? = some (.start tok)
  | [], _, k, tok, h => by simp at h
  | tok :: rest, hfree, 0, tok', h => by
      simp only [List.getElem?_cons_zero] at h
      obtain rfl := Option.some.inj h
      rw [Token.entryLanes_start
        (fun sp hs => hfree tok (List.mem_cons_self ..) sp hs)]
      rfl
  | tok :: rest, hfree, k + 1, tok', h => by
      simp only [List.getElem?_cons_succ] at h
      have hu : ∀ sp : Span, tok ≠ .string sp :=
        fun sp hs => hfree tok (List.mem_cons_self ..) sp hs
      have hrest : ∀ u ∈ rest, ∀ sp : Span, u ≠ .string sp :=
        fun u hu' sp hs => hfree u (List.mem_cons_of_mem _ hu') sp hs
      rw [Token.entryLanes_start hu, List.getElem?_cons_succ]
      exact Token.entryLanes_getElem?_start_of_no_string rest hrest k tok' h

/-- **The staging's two forms coincide where no token is a string.**  The lane
positions are the token starts (`Token.entryLanes_stringFree`), so the
quote-inclusive clause is the entry-stream clause: the entry count is the token
count, each entry names its token's start, and the class byte is the one the start
lane's clause supplies. -/
theorem WalkAlign.of_alignQuoted_stringFree {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (hal : WalkAlignQuoted G t)
    (hfree : ∀ tok ∈ t.tokens, ∀ sp : Span, tok ≠ .string sp) : WalkAlign G t := by
  have hlen : G.nep = t.tokens.length := by
    rw [hal.nep, Token.entryLanes_length_of_no_string t.tokens hfree]
  have hpos : G.ent = t.tokens.map (fun tok => tok.span.start) := by
    rw [hal.ent, Token.entryLanes_stringFree hfree]
  have hlane : ∀ (k : Nat) (tok : Token), t.tokens[k]? = some tok →
      (Token.entryLanes t.tokens)[k]? = some (.start tok) :=
    fun k tok h => Token.entryLanes_getElem?_start_of_no_string t.tokens hfree k tok h
  have hstartEq : ∀ (k : Nat) (tok : Token), t.tokens[k]? = some tok →
      entryPos G k = tok.span.start := by
    intro k tok htok
    unfold entryPos
    rw [hpos, List.getD_eq_getElem?_getD, List.getElem?_map, htok]
    rfl
  refine ⟨hal.input, hlen, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < t.tokens.length := by omega
    have htok : t.tokens[k]? = some t.tokens[k] := List.getElem?_eq_getElem hk'
    have hstart : entryPos G k = (t.tokens[k]).span.start := hstartEq k _ htok
    obtain ⟨b, hbs, -⟩ := hal.class hk (hlane k _ htok)
    exact ⟨t.tokens[k], b, htok, hstart.symm, by rw [hstart]; exact hbs⟩
  · intro k hk tok b htok hbs
    have hlane' := hlane k tok htok
    obtain ⟨b', hbs', hcls⟩ := hal.class hk hlane'
    have hstart : entryPos G k = tok.span.start := hstartEq k tok htok
    have hb : b' = b := by
      rw [hstart] at hbs
      rw [hbs'] at hbs
      exact Option.some.inj hbs
    rw [hb] at hcls
    exact hcls
  · intro k hk
    have hk' : k + 1 < t.tokens.length := by omega
    have htok : t.tokens[k + 1]? = some t.tokens[k + 1] := List.getElem?_eq_getElem hk'
    exact ⟨t.tokens[k + 1], htok,
      (hstartEq (k + 1) _ htok).symm⟩

/-- **The row at a string-free document is the entry-stream engine's.**  At a
staging whose tokens are not strings, `walkTraceRow_of_revolutions` applies to the
alignment the staging implies: the general document's row is the existing
revolution engine's, at the same tape and the same seed. -/
theorem walkTraceRow_of_revolutions_quoteFree {m0 : Mem} {G : WalkGeom m0}
    {arena : List UInt8} {t : Tape} {C₀ : WalkCarry G}
    (hal : WalkAlignQuoted G t)
    (hfree : ∀ tok ∈ t.tokens, ∀ sp : Span, tok ≠ .string sp)
    (hstep : ∀ (C : WalkCarry G), C.k < G.nep → WalkTracePrefix G arena t C →
      ∃ C', WalkTraceStep G arena t C C')
    (hk₀ : C₀.k = 0) (hpre₀ : WalkTracePrefix G arena t C₀) :
    ∃ (C : WalkCarry G), C.k = G.nep ∧ WalkTraceRow G.bs arena t C.events :=
  walkTraceRow_of_revolutions hstep (WalkAlign.of_alignQuoted_stringFree hal hfree)
    hk₀ hpre₀

/-! ### The document `[1,"ab"]`

One bracket, a numeral, a comma and a string: five tokens at six staged lanes,
because the string's closing quote is an entry of its own.  The number's step costs
one lane, the comma's one, and the string's two, so this is the smallest document
whose chain mixes the two advances.  The tokens are

`[`, `1`, `,`, `"ab"`, `]` at `⟨0,1⟩`, `⟨1,2⟩`, `⟨2,3⟩`, `⟨3,7⟩`, `⟨7,8⟩`, and the
lanes are `[0, 1, 2, 3, 6, 7]` — the string's start at three and its closing quote
at six.

The carries are the seed, the opener's, the numeral's, the comma's, the string's
merge `Cd` and back edge, and the closer's.  The three one-lane records are the
document's own bytes (the containers' by `TokenRecord`'s constructors, the
numeral's by `strtodSpec` at `decimalOne`), and the string's is the plain arm's at
the span's extent `7 - 3 - 2 = 2` and body start `4`. -/

/-- The document `[1,"ab"]`'s bytes. -/
def numberStringDocumentBytes : List UInt8 :=
  [0x5B, 0x31, 0x2C, 0x22, 0x61, 0x62, 0x22, 0x5D]

/-- **The document `[1,"ab"]`'s row.**  The chain's five steps — one lane each at
the opener, the numeral, the comma and the closer, and two at the string — end at
the whole token list, and the row is the four records the arms append.  The
string's merge carry `Cd` keeps the entry index and appends its record, and the back
edge moves the index past the closing quote; those two equations are the arm's, as
the numeral's record and the containers' are their own. -/
theorem row_numberStringDocument {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ Cd C₄ C₅ : WalkCarry G} {v : JSON.Value}
    (hal : WalkAlignQuoted G t)
    (hbs : G.bs = numberStringDocumentBytes)
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .number ⟨1, 2⟩,
      .punct .comma ⟨2, 3⟩, .string ⟨3, 7⟩, .punct .closeBracket ⟨7, 8⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefixAt G arena t C₀ 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hk₂ : C₂.k = C₁.k + 1)
    (hev₂ : C₂.events = C₁.events ++
      [EventRecord.number (strtodSpec decimalOne).toBits])
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hkC : Cd.k = C₃.k)
    (hevC : Cd.events = C₃.events ++ [EventRecord.str false 2 (plainSpan 4)])
    (hk₄ : C₄.k = Cd.k + 2) (hev₄ : C₄.events = Cd.events)
    (hk₅ : C₅.k = C₄.k + 1) (hev₅ : C₅.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.number (strtodSpec decimalOne).toBits,
        EventRecord.str false 2 (plainSpan 4), EventRecord.tag 4] : List EventRecord) := by
  -- the seed's records are empty
  have hC₀nil : C₀.events = [] := by
    have hlen : C₀.events.length = 0 := by
      have h := WalkTracePrefixAt.length hpre₀
      rw [Token.recordTokens_zero, List.length_nil] at h
      exact h
    exact List.eq_nil_of_length_eq_zero hlen
  -- the opener's step, at the document's own bytes
  have htok₀ : t.tokens[0]? = some (.punct .openBracket ⟨0, 1⟩) := by
    rw [htokens]; rfl
  have hrec₀ : TokenRecord G.bs arena (.tag 3) (.punct .openBracket ⟨0, 1⟩) := by
    rw [hbs]
    exact TokenRecord.openBracket (by decide) (by decide)
  have hstepO : WalkTraceStepAt G arena t C₀ C₁ 0 :=
    WalkTraceStepAt.emit hpre₀ htok₀ (by intro s h; cases h) hrec₀ hk₁ hev₁
  -- the numeral's step
  have htok₁ : t.tokens[1]? = some (.number ⟨1, 2⟩) := by
    rw [htokens]; rfl
  have hlex : decimalOne.lexeme.data.toList = (G.bs.drop 1).take (2 - 1) := by
    rw [decimalOne_lexeme, hbs]
    rfl
  have hstepN : WalkTraceStepAt G arena t C₁ C₂ 1 :=
    stepAt_number hal (WalkTraceStepAt.trace_of hstepO) hdec htok₁ decimalOne_wellFormed
      hlex hk₂ hev₂
  -- the comma's step
  have htok₂ : t.tokens[2]? = some (.punct .comma ⟨2, 3⟩) := by
    rw [htokens]; rfl
  have hstepC : WalkTraceStepAt G arena t C₂ C₃ 2 :=
    WalkTraceStepAt.separator (WalkTraceStepAt.trace_of hstepN) htok₂ (Or.inl rfl) hk₃ hev₃
  -- the string's step, its two lanes
  have htok₃ : t.tokens[3]? = some (.string ⟨3, 7⟩) := by
    rw [htokens]; rfl
  have hquote : (⟨3, 7⟩ : Span).start + 2 ≤ (⟨3, 7⟩ : Span).stop := by decide
  have hbody : ∀ cs : List Nat, bodyCodePoints G.bs ⟨3, 7⟩ = some cs →
      escapeCodePoints ((G.bs.drop (3 + 1)).take (7 - 3 - 2)) = some cs := by
    intro cs hcs
    rw [hbs] at hcs
    have h : bodyCodePoints numberStringDocumentBytes ⟨3, 7⟩ = some [97, 98] := by decide
    rw [h] at hcs
    obtain rfl := Option.some.inj hcs
    rw [hbs]
    decide
  have hstepS : WalkTraceStepAt G arena t C₃ C₄ 3 :=
    stepAt_string_plain hal (WalkTraceStepAt.trace_of hstepC) hdec htok₃ hquote hbody
      hkC hevC hk₄ hev₄
  -- the closer's step
  have htok₄ : t.tokens[4]? = some (.punct .closeBracket ⟨7, 8⟩) := by
    rw [htokens]; rfl
  have hrec₄ : TokenRecord G.bs arena (.tag 4) (.punct .closeBracket ⟨7, 8⟩) := by
    rw [hbs]
    exact TokenRecord.closeBracket (by decide) (by decide)
  have hstepK : WalkTraceStepAt G arena t C₄ C₅ 4 :=
    WalkTraceStepAt.emit (WalkTraceStepAt.trace_of hstepS) htok₄ (by intro s h; cases h) hrec₄
      hk₅ hev₅
  -- the run of five steps, and the row at its end
  have hchain : WalkTraceChainAt G arena t 5 0 C₀ C₅ 5 :=
    WalkTraceChainAt.succ hstepO (WalkTraceChainAt.succ hstepN
      (WalkTraceChainAt.succ hstepC (WalkTraceChainAt.succ hstepS
        (WalkTraceChainAt.succ hstepK (WalkTraceChainAt.zero 5 C₅)))))
  have hrow : WalkTraceRow G.bs arena t C₅.events :=
    WalkTraceChainAt.traceRow hchain hpre₀ (by rw [htokens]; rfl)
  -- the trace is the four records
  have hC₅ : C₅.events =
      [EventRecord.tag 3, EventRecord.number (strtodSpec decimalOne).toBits,
        EventRecord.str false 2 (plainSpan 4), EventRecord.tag 4] := by
    rw [hev₅, hev₄, hevC, hev₃, hev₂, hev₁, hC₀nil]
    simp
  rwa [hC₅] at hrow

/-! ### Axiom footprints

The row engine is constructive: the chain's induction and the arms' steps carry
`propext` and `Quot.sound` through the list and `Option` lemmas, and nothing else.
The lane-count readings are `propext` alone. -/

/-- info: 'LeanLLVM.Refinement.walkTraceRow_of_quoteSteps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkTraceRow_of_quoteSteps

/-- info: 'LeanLLVM.Refinement.row_numberStringDocument' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_numberStringDocument

/-- info: 'LeanLLVM.Refinement.WalkAlign.of_alignQuoted_stringFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkAlign.of_alignQuoted_stringFree

/-- info: 'LeanLLVM.Refinement.walkTraceRow_of_revolutions_quoteFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkTraceRow_of_revolutions_quoteFree

/-- info: 'LeanLLVM.Refinement.WalkTraceStepAt.emit_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkTraceStepAt.emit_two

/-- info: 'LeanLLVM.Refinement.WalkTraceChainAt.k_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkTraceChainAt.k_eq

/-- info: 'LeanLLVM.Refinement.stepAt_string_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepAt_string_plain

/-- info: 'LeanLLVM.Refinement.Token.entryLanes_length_of_no_string' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.entryLanes_length_of_no_string

/-- info: 'LeanLLVM.Refinement.stepAt_punct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stepAt_punct

end LeanLLVM.Refinement
