/-
The execution-indexed producer: `hsem` from the walk's record trace.

`pipeline_satisfies_stage2` (`JsonStage2Spec`) takes the parser half at the run's
own outcome as a premise, and `JsonStage2Spec` proves the two semantic
correspondences at named boundary witnesses.  What that module does **not** have
is the *producer* of the premise: a theorem that, at each outcome an execution
produces, assembles the parser half from the evidence the run itself supplies.
This module is that producer, and it names the one thing the run cannot yet
supply.

# The two vocabularies, and which one the walk speaks

The specification's relation is stated over **bytes**: `Stage2EventRel bs arena
evs toks` consumes `tagRecord`, `numberRecordBytes` and `strRecordBytes` from
`evs`.  The walk does not carry bytes; it carries a trace, and the trace is a
`List EventRecord` (`JsonStage2Body`): the loop's invariant states the event
stream's written suffix as `(C.events.map EventRecord.encodedBytes).flatten`, and
`encodedBytes` is what the emitter writes.  So the interface between the walk
and the relation is a relation over **records**, `Stage2Records`, and
`Stage2Records.toEventRel` transports it to the byte-level relation.  That
transport is the first thing this module proves, and it is what makes the
per-arm evidence of a walk proof composable: a walk step relates one record to
one token, `Stage2Records.append` concatenates, and the flattening happens once.

The record relation's constructors are the value classes: each fixes the record
shape, the tag and the payload that class's record must carry, and the two
separators get a constructor that consumes no record.

| class | record | token | payload the record must carry |
|---|---|---|---|
| `null`, `true`, `false` | `tag 10`, `tag 8`, `tag 9` | `.null`, `.bool`, `.bool` | the literal's four or five bytes at the span |
| containers | `tag 1`–`tag 4` | `.punct` | the brace or bracket's one byte |
| strings, plain | `str key len (plainSpan …)` | `.string` | the body's code points, read off the document |
| strings, escaped | `str key len off` | `.string` | the arena slice's code points |
| numbers | `number (strtodSpec d).toBits` | `.number` | the lexeme, the span and `strtodSpec` |

The number row is the one whose payload is a *computed* value rather than bytes
of the document, and that is where the numeric arm's boundary sits — see below.

# What the producer proves, and the one premise it names

`Stage2OutcomeEvidence` is the evidence at one outcome: the document the
arguments name, the run's own answer — an accepted tape with the UTF-8 stage's
passed test and the record trace related to that tape's tokens, or a refusal at
no accepting tape with the policy's word at the refusal slot.  Every other clause
of `ParserHalf` is *derived* here:

* the decoded value, its validity and the span discipline come from the parser's
  own correctness theorem (`decodeTape_correct`, `tape_valid`), so **no accepted
  run's output is left merely related: the value is `decodeTape`'s** and the
  relation is what ties the emitted records to the tokens that value came from;
* the byte-level relation comes from `Stage2Records.toEventRel`;
* the acceptance equivalence comes from the outcome's verdict, its two-valuedness
  and the parser's answer at that verdict — it is never asserted over a verdict
  the run did not return.

The evidence is deliberately weaker than `ParserHalf`: it names no value, no
`ValidDocument`, no `spansWellFormed`, and not the equivalence.  What it does
name is the thing this tree has no theorem for: that the records the walk
emitted are the *reference parser's* tokens.  The walk's trace records each
event's shape and payload; that those shapes and payloads are the tokens of
`parseBytes` at that document is the walk's token correspondence, and it is a
row-per-arm obligation of the walk proof, not a consequence of the boundary
post — `stage2Post` says the verdict is two-valued and nothing more
(`JsonStage2Contract`).

# The numeric arm's boundary, named as a staging boundary

`stage2NumFast` (`JsonStage2Body`) is the *model* the walk's `num_fast_el1` slot
is answered by, and at a well-formed lexeme its eight bytes are `strtodSpec`'s
(`stage2NumFast_writes_strtodSpec`, from `numFastEmitted_strtodSpec`).  So the
number row of the table above costs no arithmetic *at the model*.

The pinned helper body is a different statement, and its boundary is a staging
boundary rather than a numeric defect:

* `stage2Calls noCalls` answers none of `num_d8_el1`, `num_el_el1`,
  `stk_mul_u64`, and at each of their sites the helper body's `step` is `ub`
  (`JsonStage2NumFastArm`), so a *body-level* conversion proof is not reachable
  at the call environment the walk's contracts are proved in;
* a body-level proof therefore needs a `Calls` selection that answers the three
  callees and a staging that stages the two tables (`NUMF_EL1_P10`,
  `NUMF_EL1_POW10`).  Both are supplied now, in
  `JsonStage2NumFastCalls`: `stage2NumFastCalls` answers the three callees (each
  modelled from its measured C text), the three sites' steps are jumps at it
  rather than `ub`, and `numFastTables_holds` is `NumFastTables` at a concrete
  staging.  What `NumFastBodyArm` still needs is the conversion's *run* — the
  three digit runs' arms, the inlined tier-1 arithmetic, and the tier-2
  kernel's exactness bound — not its environment; and the arm's statement
  itself needs an entry hypothesis first, since its hypotheses are facts about
  the environment and the memory only: `numFastBodyArm_at_pc` reads the arm at
  an arbitrary program counter and `numFastBodyArm_false_at_divBody` refutes it
  at `while.body232.i.i` with the residual cell unbound, so `s.pc = "entry"` is
  the statement's repair; and
* at the walk's own selection the slot is answered by the model instead
  (`stage2Calls stage2SubCalls "num_fast_el1"` is `stage2NumFast`), which is why
  the number *class* is covered here while the conversion's body is not.

`stage2Calls_noCalls_numFast` states the arm-level consequence of the first
bullet at the stage-2 selection's own vocabulary — the three callees' sites are
`JsonStage2NumFastArm`'s, and the slot is `stage2Calls`'s — with
`stage2Calls_subCalls_numFast` as the control that the same reading answers the
model at `stage2SubCalls`.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2Spec
import LeanLLVM.Refinement.JsonStage2NumFastArm
import LeanLLVM.JSON.Correct

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)

/-! ### The walk's trace, related record by record

`EventRecord` is the walk's own vocabulary (`JsonStage2Body`), and the invariant
states the written suffix of the event stream as its flattening.  The relation
below is `Stage2EventRel` with the record at the head instead of the bytes, so a
walk step proves one constructor and the byte-level relation is a theorem rather
than a restatement. -/

/-- The stage-2 event stream's relation at the walk's own trace: the document
`bs`, the arena prefix, a `List EventRecord` and the parser's tokens.  Each
constructor is one record class, and its hypotheses are the document-side or
parser-side facts that class's record must carry. -/
inductive Stage2Records (bs arena : List UInt8) : List EventRecord → List Token → Prop where
  /-- No records, no tokens. -/
  | nil : Stage2Records bs arena [] []
  /-- A comma separator has no record. -/
  | comma {s : Span} {rs : List EventRecord} {toks : List Token}
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena rs (.punct .comma s :: toks)
  /-- A colon separator has no record. -/
  | colon {s : Span} {rs : List EventRecord} {toks : List Token}
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena rs (.punct .colon s :: toks)
  /-- `{` (`T_OBJ = 1`) at a one-byte span. -/
  | openBrace {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7B) (hspan : s.stop = s.start + 1)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 1 :: rs) (.punct .openBrace s :: toks)
  /-- `}` (`T_OBJ_END = 2`). -/
  | closeBrace {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7D) (hspan : s.stop = s.start + 1)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 2 :: rs) (.punct .closeBrace s :: toks)
  /-- `[` (`T_ARR = 3`). -/
  | openBracket {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5B) (hspan : s.stop = s.start + 1)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 3 :: rs) (.punct .openBracket s :: toks)
  /-- `]` (`T_ARR_END = 4`). -/
  | closeBracket {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5D) (hspan : s.stop = s.start + 1)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 4 :: rs) (.punct .closeBracket s :: toks)
  /-- `true` (`T_TRUE = 8`) at the four-byte literal span. -/
  | trueTag {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65])
      (hspan : s.stop = s.start + 4)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 8 :: rs) (.bool true s :: toks)
  /-- `false` (`T_FALSE = 9`) at the five-byte literal span. -/
  | falseTag {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbytes : (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
      (hspan : s.stop = s.start + 5)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 9 :: rs) (.bool false s :: toks)
  /-- `null` (`T_NULL = 10`) at the four-byte literal span. -/
  | nullTag {s : Span} {rs : List EventRecord} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
      (hspan : s.stop = s.start + 4)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.tag 10 :: rs) (.null s :: toks)
  /-- A number (`T_NUM = 7`): the payload is `strtodSpec`'s eight bytes of a
  well-formed lexeme at the token's own span. -/
  | number {s : Span} {rs : List EventRecord} {toks : List Token} {d : Decimal}
      (hwf : d.wellFormed)
      (hspan : s.stop = s.start + d.lexeme.length)
      (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d.lexeme.data.toList)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.number (strtodSpec d).toBits :: rs)
        (.number s :: toks)
  /-- A key or string written in the plain form. -/
  | strPlain {key : Bool} {s : Span} {rs : List EventRecord} {toks : List Token}
      {len : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.stop = s.start + 2 + len)
      (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs)
      (hcode : bodyCodePoints bs s = some cs)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.str key len (plainSpan (s.start + 1)) :: rs)
        (.string s :: toks)
  /-- A key or string written in the arena form. -/
  | strArena {key : Bool} {s : Span} {rs : List EventRecord} {toks : List Token}
      {len off : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.start + 2 ≤ s.stop)
      (hcode : bodyCodePoints bs s = some cs)
      (hbelow : off < 2 ^ 63)
      (harena : escapeCodePoints ((arena.drop off).take len) = some cs)
      (h : Stage2Records bs arena rs toks) :
      Stage2Records bs arena (EventRecord.str key len off :: rs) (.string s :: toks)

namespace Stage2Records

/-- Concatenating two related record/token pairs concatenates both sides: a walk
step relates one record, and the run's trace is built by appending. -/
theorem append {bs arena : List UInt8} {rs₁ : List EventRecord}
    {toks₁ : List Token} (h₁ : Stage2Records bs arena rs₁ toks₁)
    {rs₂ : List EventRecord} {toks₂ : List Token}
    (h₂ : Stage2Records bs arena rs₂ toks₂) :
    Stage2Records bs arena (rs₁ ++ rs₂) (toks₁ ++ toks₂) :=
  Stage2Records.rec
    (motive := fun rs toks _ =>
      Stage2Records bs arena (rs ++ rs₂) (toks ++ toks₂))
    h₂
    (fun _ ih => Stage2Records.comma ih)
    (fun _ ih => Stage2Records.colon ih)
    (fun hb hs _ ih => Stage2Records.openBrace hb hs ih)
    (fun hb hs _ ih => Stage2Records.closeBrace hb hs ih)
    (fun hb hs _ ih => Stage2Records.openBracket hb hs ih)
    (fun hb hs _ ih => Stage2Records.closeBracket hb hs ih)
    (fun hb hs _ ih => Stage2Records.trueTag hb hs ih)
    (fun hb hs _ ih => Stage2Records.falseTag hb hs ih)
    (fun hb hs _ ih => Stage2Records.nullTag hb hs ih)
    (fun hwf hs hlex _ ih => Stage2Records.number hwf hs hlex ih)
    (fun hq hs hbody hcode _ ih => Stage2Records.strPlain hq hs hbody hcode ih)
    (fun hq hs hcode hbelow harena _ ih =>
      Stage2Records.strArena hq hs hcode hbelow harena ih)
    h₁

/-- **The record trace is the emitted byte stream.**  `encodedBytes` is what each
record's emitter writes, so flattening the trace is the stream and the relation
transports unchanged: this is the bridge between the walk's carry and
`Stage2EventRel`. -/
theorem toEventRel {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} (h : Stage2Records bs arena rs toks) :
    Stage2EventRel bs arena (rs.map EventRecord.encodedBytes).flatten toks := by
  induction h with
  | nil => exact Stage2EventRel.nil
  | comma _ ih => exact Stage2EventRel.comma ih
  | colon _ ih => exact Stage2EventRel.colon ih
  | openBrace hb hs _ ih => exact Stage2EventRel.openBrace hb hs ih
  | closeBrace hb hs _ ih => exact Stage2EventRel.closeBrace hb hs ih
  | openBracket hb hs _ ih => exact Stage2EventRel.openBracket hb hs ih
  | closeBracket hb hs _ ih => exact Stage2EventRel.closeBracket hb hs ih
  | trueTag hb hs _ ih => exact Stage2EventRel.trueTag hb hs ih
  | falseTag hb hs _ ih => exact Stage2EventRel.falseTag hb hs ih
  | nullTag hb hs _ ih => exact Stage2EventRel.nullTag hb hs ih
  | number hwf hs hlex _ ih => exact Stage2EventRel.number hwf hs hlex ih
  | strPlain hq hs hbody hcode _ ih =>
      exact Stage2EventRel.strPlain hq hs hbody hcode ih
  | strArena hq hs hcode hbelow harena _ ih =>
      exact Stage2EventRel.strArena hq hs hcode hbelow harena ih

end Stage2Records

/-- The record trace at the byte-level relation, named for the producer's
statement: the emitted stream is the trace's flattening. -/
theorem stage2EventRel_of_records {bs arena evs : List UInt8}
    {rs : List EventRecord} {toks : List Token}
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten)
    (h : Stage2Records bs arena rs toks) :
    Stage2EventRel bs arena evs toks :=
  hev ▸ Stage2Records.toEventRel h

/-! ### The numeric arm's boundary

The number record's payload is a computed value, and the tree has two statements
about it: the model's (`stage2NumFast` writes `numFastEmitted`'s bits, which are
`strtodSpec`'s at a well-formed lexeme) and the body's (`numFastBody` at the
walk's environment, whose three out-of-line callees are unanswered).  The first
is what the relation's number constructor consumes; the second is where a
body-level conversion proof stops. -/

/-- **The walk's number slot is unanswered at `noCalls`.**  `stage2Calls`
forwards every symbol it does not answer itself, so the numeric arm's slot at the
selection that answers nothing is `none` — the fact `JsonStage2NumFastArm` reads
at the helper body, stated here at the selection's own vocabulary. -/
theorem stage2Calls_noCalls_numFast (args : List Value) (mem : Mem) (next : Nat) :
    stage2Calls noCalls "num_fast_el1" args mem next = none := rfl

/-- **The control: the walk's own selection answers the slot with the model.**
Without this, `stage2Calls_noCalls_numFast` would be consistent with
`num_fast_el1` being absent from every selection. -/
theorem stage2Calls_subCalls_numFast (args : List Value) (mem : Mem) (next : Nat) :
    stage2Calls stage2SubCalls "num_fast_el1" args mem next =
      stage2NumFast args mem next :=
  stage2Calls_num_fast_el1 args mem next

/-- **The model's number record is `strtodSpec`'s.**  At a well-formed lexeme,
`stage2NumFast`'s accepted arm writes the eight bytes the relation's number
constructor names.  This is the model's statement: the helper *body* is
`JsonStage2NumFastArm`'s, and its conversion is `ub` at the walk's selection. -/
theorem stage2NumFast_writes_strtodSpec {p out err : Nat} {n : BitVec 64} {mem : Mem}
    {next : Nat} {d : Decimal} (hwf : d.wellFormed)
    (hread : readBytes mem p n.toNat = some d.lexeme.data.toList)
    (hscan : (numLexScan d.lexeme.data.toList).2 = true) :
    stage2NumFast [.ptr p, .int 64 n, .ptr out, .ptr err] mem next =
      some { ret := .int 32 (BitVec.ofNat 32 1),
             mem := writeBytes mem out (wordBytes 8 (strtodSpec d).toBits),
             next := next } := by
  simp only [stage2NumFast, hread, hscan, ite_true, ByteString.literal_data_toList,
    numberPayload_eq_strtodSpec d hwf]

/-! ### The policy on both paths

`ParserHalf`'s third conjunct reads the refusal word at the returned memory.  On
the walk's refusal path the word is the policy's value; on the accept path the
word is the caller's, untouched by the run, and the policy holds for *every*
word because the accepted document is a valid UTF-8 prefix and the parser
returned a tape rather than a refusal. -/

/-- The refusal word is the policy's, at the memory the run returned. -/
def RefusalOffsetPolicy (bs : List UInt8) (m : Mem) (err : Nat) : Prop :=
  ∀ e : Nat, readBytes m err 8 = some (wordBytes 8 e) → RefusalOffset bs e

/-- **The accept path's policy, derived rather than assumed.**  Both of
`RefusalOffset`'s clauses are vacuous at an accepted, UTF-8-valid document: no
refusal constructor is reached (`hok` and `hparse` are incompatible), and the
second clause's hypothesis is the stage's own passed test. -/
theorem refusalOffset_of_parseOk {bs : List UInt8} {t : Tape} {e : Nat}
    (hok : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hutf8 : utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length))) :
    RefusalOffset bs e := by
  refine ⟨?_, fun hbad => absurd hutf8 hbad⟩
  intro _ r hparse
  rw [hparse] at hok
  exact absurd hok (by simp)

/-! ### The parser half from the run's own evidence

Two producers, one per verdict the run can return.  Each is stated at the
boundary's own reads — the arena at the extent the record names, which is the
used prefix — and each derives what `ParserHalf` demands beyond them. -/

/-- **The accepted verdict's parser half.**  The tape is the parser's; the value,
its validity and the span discipline are `decodeTape_correct` and `tape_valid`;
the byte-level relation is the record trace's; the equivalence holds at `1`
because the run returned `1`; and the policy is derived, not assumed, from the
accept and the stage's passed UTF-8 test (`refusalOffset_of_parseOk`).  Nothing
here is quantified over a verdict the run did not produce. -/
theorem parserHalf_accept {bs : List UInt8} {verdict : BitVec 64} {m : Mem}
    {dst ev err ndst' nev' : Nat} {t : Tape} {rs : List EventRecord}
    {arena evs : List UInt8}
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hdst : readBytes m dst ndst' = some arena)
    (hev : readBytes m ev nev' = some evs)
    (hrecs : evs = (rs.map EventRecord.encodedBytes).flatten)
    (hrel : Stage2Records bs arena rs t.tokens)
    (hutf8 : utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length)))
    (hv : verdict = 1) :
    ParserHalf stage2EventRel bs verdict m dst ev err ndst' nev' := by
  obtain ⟨v, hdec, hin, hvalid⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  refine ⟨⟨fun _ => ⟨t, hparse⟩, fun _ => hv⟩, ?_,
    fun _ _ => refusalOffset_of_parseOk hparse hutf8⟩
  intro _
  exact ⟨t, v, arena, evs, hparse, hin, hdec, hdst, hev,
    stage2EventRel_of_records hrecs hrel, (tape_valid t v hdec).1, hvalid⟩

/-- **The refused verdict's parser half.**  The parser has no accepting tape at
the document and the run returned `0`, so the equivalence holds by parity; the
accepted clause is vacuous; and the refusal word is the policy's. -/
theorem parserHalf_refuse {bs : List UInt8} {verdict : BitVec 64} {m : Mem}
    {dst ev err ndst' nev' : Nat}
    (hno : ¬ ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hpol : RefusalOffsetPolicy bs m err)
    (hv : verdict = 0) :
    ParserHalf stage2EventRel bs verdict m dst ev err ndst' nev' := by
  have hne : ¬ (verdict = 1) := by
    rw [hv]
    decide
  refine ⟨⟨fun h => absurd h hne, fun hex => absurd hex hno⟩, ?_, hpol⟩
  intro h
  exact absurd h hne

/-! ### The evidence at one outcome

The evidence is indexed by the outcome exactly as `ParserHalfForOutcome` is, so
the producer is asked only at outcomes an execution produces.  It carries the
document and the run's answer — and not the value, the validity, the span
discipline or the acceptance equivalence, which the producers above derive. -/

/-- **The evidence the producer turns into the parser half**, at one outcome of
the run: the document the arguments name (`base` and the length argument) and the
walk's answer — an accepted tape, the UTF-8 stage's passed test and the record
trace related to the tape's tokens, or a refusal at no accepting tape with the
policy's word at the refusal slot. -/
def Stage2OutcomeEvidence (base : Nat) (args : List Value) (mem : Mem)
    (ndst' nev' : Nat) (o : Outcome) : Prop :=
  match o, args with
  | .ret (some (.int 64 verdict)) m,
    [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _,
     .int 64 _, .ptr _, .ptr _, .ptr dst, .int 64 _, .ptr _, .ptr ev, .int 64 _,
     .ptr _, .ptr err, .int 64 _] =>
      ∃ bs : List UInt8,
        n.toNat = bs.length ∧
        readBytes mem base n.toNat = some bs ∧
        ((verdict = 1 ∧
            utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length)) ∧
            ∃ (t : Tape) (rs : List EventRecord) (arena evs : List UInt8),
              parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
              readBytes m dst ndst' = some arena ∧
              readBytes m ev nev' = some evs ∧
              evs = (rs.map EventRecord.encodedBytes).flatten ∧
              Stage2Records bs arena rs t.tokens) ∨
          (verdict = 0 ∧
            RefusalOffsetPolicy bs m err ∧
            ¬ ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t))
  | _, _ => False

/-- **The evidence is the parser half at the run's own outcome.**  This is the
whole producer: the outcome's shape is the specification's, so the evidence lands
on the same match, and each disjunct is one of the two producers above. -/
theorem parserHalfForOutcome_of_evidence {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome}
    (h : Stage2OutcomeEvidence base args mem ndst' nev' o) :
    ParserHalfForOutcome stage2EventRel base args mem ndst' nev' o := by
  unfold Stage2OutcomeEvidence at h
  split at h
  · obtain ⟨bs, hlen, hread, hcase⟩ := h
    unfold ParserHalfForOutcome
    refine ⟨bs, hlen, hread, ?_⟩
    rcases hcase with ⟨hv, hutf8, t, rs, arena, evs, hparse, hdst, hev, hrecs, hrel⟩ |
      ⟨hv, hpol, hno⟩
    · exact parserHalf_accept hparse hdst hev hrecs hrel hutf8 hv
    · exact parserHalf_refuse hno hpol hv
  · exact h.elim

/-- **`hsem`, produced.**  This is `pipeline_satisfies_stage2`'s premise at
`stage2EventRel`, assembled at each outcome from the evidence above: the staging,
the run and the extent record are consumed only to index the evidence, and every
clause of the parser half is derived. -/
theorem hsem_of_evidence {calls : Calls} {f : Function} {tab base : Nat}
    (hev : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      Stage2OutcomeEvidence base args mem ndst' nev' o) :
    ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      ParserHalfForOutcome stage2EventRel base args mem ndst' nev' o :=
  fun args mem next o ndst' nev' hst hbeh hext =>
    parserHalfForOutcome_of_evidence (hev args mem next o ndst' nev' hst hbeh hext)

/-- **The producer applied where the bridge consumes it.**  `hsem_of_evidence`
is `pipeline_satisfies_stage2`'s second premise, and this theorem is that
application: the specification's record follows from the units' record and the
per-outcome evidence, with `stage2EventRel` instantiated.  It is the check that
the produced statement is the one the bridge asks for rather than a lookalike. -/
theorem pipeline_satisfies_stage2_of_evidence {calls : Calls} {f : Function}
    {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hev : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      Stage2OutcomeEvidence base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline_stage2 tab base) :=
  pipeline_satisfies_stage2 hunits (hsem_of_evidence hev)

/-! ### The record trace is inhabited

The evidence's record half is not a vacuous relation: the scalar and container
rows of the table are instantiated below at concrete documents, with the emitted
bytes computed rather than assumed.  What is *not* instantiated here is the
parser half's parser side: the tape `parseBytes` returns carries its own token
list, and that list is the walk's obligation rather than a fact this module can
read off `parseRef_complete` — `tests/counterexamples/parser-half-outcome.lean`
instantiates `ParserHalfForOutcome` at two real runs by supplying the relation
itself, which is the same separation. -/

/-- The document `null`. -/
def nullDoc : List UInt8 := [0x6E, 0x75, 0x6C, 0x6C]

/-- The event byte `null`'s record writes. -/
theorem null_event_bytes :
    (([EventRecord.tag 10] : List EventRecord).map EventRecord.encodedBytes).flatten =
      [0x0A] := by
  decide

/-- **One record, one token.**  The `null` document's record trace relates to the
parser's `null` token at the literal's four-byte span. -/
theorem null_records :
    Stage2Records nullDoc []
      ([EventRecord.tag 10] : List EventRecord) [.null ⟨0, 4⟩] :=
  Stage2Records.nullTag (s := ⟨0, 4⟩) (by decide) (by decide) Stage2Records.nil

/-- The byte-level relation the trace produces: the flattening is `out_tag`'s own
byte, and the relation is the instantiated one. -/
theorem null_eventRel :
    Stage2EventRel nullDoc [] [0x0A] [.null ⟨0, 4⟩] :=
  stage2EventRel_of_records (evs := [0x0A]) null_event_bytes.symm null_records

/-- The document `[null,null]`. -/
def pairDoc : List UInt8 :=
  [0x5B, 0x6E, 0x75, 0x6C, 0x6C, 0x2C, 0x6E, 0x75, 0x6C, 0x6C, 0x5D]

/-- **Containers and separators.**  The array's two brackets bracket the
elements' records, and its comma consumes no record — the token list is the
parser's own, separators included, and the record list is the walk's. -/
theorem pair_records :
    Stage2Records pairDoc []
      ([EventRecord.tag 3, EventRecord.tag 10, EventRecord.tag 10,
        EventRecord.tag 4] : List EventRecord)
      [.punct .openBracket ⟨0, 1⟩, .null ⟨1, 5⟩, .punct .comma ⟨5, 6⟩,
       .null ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩] :=
  Stage2Records.openBracket (s := ⟨0, 1⟩) (by decide) (by decide)
    (Stage2Records.nullTag (s := ⟨1, 5⟩) (by decide) (by decide)
      (Stage2Records.comma
        (Stage2Records.nullTag (s := ⟨6, 10⟩) (by decide) (by decide)
          (Stage2Records.closeBracket (s := ⟨10, 11⟩) (by decide) (by decide)
            Stage2Records.nil))))

/-- The trace's flattening at the container document: four one-byte records. -/
theorem pair_event_bytes :
    ((([EventRecord.tag 3, EventRecord.tag 10, EventRecord.tag 10,
        EventRecord.tag 4] : List EventRecord).map EventRecord.encodedBytes).flatten) =
      [0x03, 0x0A, 0x0A, 0x04] := by
  decide

/-- The byte-level relation at the container document. -/
theorem pair_eventRel :
    Stage2EventRel pairDoc [] [0x03, 0x0A, 0x0A, 0x04]
      [.punct .openBracket ⟨0, 1⟩, .null ⟨1, 5⟩, .punct .comma ⟨5, 6⟩,
       .null ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩] :=
  stage2EventRel_of_records (evs := [0x03, 0x0A, 0x0A, 0x04]) pair_event_bytes.symm pair_records

/-- **Composition is `append`.**  A walk step relates one record to one token, so
two related traces concatenate; the separators ride along without a record. -/
theorem pair_records_composed :
    Stage2Records pairDoc []
      (([EventRecord.tag 3] ++ [EventRecord.tag 10, EventRecord.tag 10,
        EventRecord.tag 4]) : List EventRecord)
      ([.punct .openBracket ⟨0, 1⟩] ++
        [.null ⟨1, 5⟩, .punct .comma ⟨5, 6⟩, .null ⟨6, 10⟩,
         .punct .closeBracket ⟨10, 11⟩]) :=
  Stage2Records.append
    (Stage2Records.openBracket (s := ⟨0, 1⟩) (by decide) (by decide)
      Stage2Records.nil)
    (Stage2Records.nullTag (s := ⟨1, 5⟩) (by decide) (by decide)
      (Stage2Records.comma
        (Stage2Records.nullTag (s := ⟨6, 10⟩) (by decide) (by decide)
          (Stage2Records.closeBracket (s := ⟨10, 11⟩) (by decide) (by decide)
            Stage2Records.nil))))

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.Stage2Records.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2Records.append

/-- info: 'LeanLLVM.Refinement.Stage2Records.toEventRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2Records.toEventRel

/-- info: 'LeanLLVM.Refinement.stage2EventRel_of_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_of_records

/-- info: 'LeanLLVM.Refinement.stage2Calls_noCalls_numFast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Calls_noCalls_numFast

/-- info: 'LeanLLVM.Refinement.stage2Calls_subCalls_numFast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Calls_subCalls_numFast

/-- info: 'LeanLLVM.Refinement.stage2NumFast_writes_strtodSpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2NumFast_writes_strtodSpec

/-- info: 'LeanLLVM.Refinement.refusalOffset_of_parseOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_of_parseOk

/-- info: 'LeanLLVM.Refinement.parserHalf_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalf_accept

/-- info: 'LeanLLVM.Refinement.parserHalf_refuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalf_refuse

/-- info: 'LeanLLVM.Refinement.Stage2OutcomeEvidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Stage2OutcomeEvidence

/-- info: 'LeanLLVM.Refinement.parserHalfForOutcome_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalfForOutcome_of_evidence

/-- info: 'LeanLLVM.Refinement.hsem_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hsem_of_evidence

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_stage2_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_stage2_of_evidence

/-- info: 'LeanLLVM.Refinement.null_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms null_records

/-- info: 'LeanLLVM.Refinement.null_eventRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms null_eventRel

/-- info: 'LeanLLVM.Refinement.pair_records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pair_records

/-- info: 'LeanLLVM.Refinement.pair_eventRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pair_eventRel

/-- info: 'LeanLLVM.Refinement.pair_records_composed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pair_records_composed

end LeanLLVM.Refinement
