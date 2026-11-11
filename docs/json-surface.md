# The JSON surface

This document describes the JSON language the demonstration is proved against:
what it accepts, what it refuses, and which theorems establish the
correspondence.  It is written from the definitions in `LeanLLVM/JSON/`, and every
claim below names the declaration that carries it.

## It is not a BNF grammar, and that is deliberate

The specification is a **reading relation**, not a grammar.  Each production of
RFC 8259 becomes an inductive predicate over **bytes and positions**:

```lean
inductive ValueAt (m : Strictness) (bs : Bytes) : Nat → Value → Nat → Prop
```

read as *"at byte `i`, `bs` begins a value `v` ending at byte `j`"*.  Every
constructor names the production it implements — `ValueAt.array` is documented
`§2 begin-array = ws %x5B ws … end-array = ws %x5D ws`, `ValueAt.number` is `§6
number`, `ValueAt.true` is `§3 true = %x74.72.75.65`.

**Why not a grammar.**  A BNF production denotes a string; a parser needs the
*ends*.  `NumberAt bs i j` fixes both, so the maximal-run question ("where does
this number stop?") is a proposition about two indices rather than a property a
parser has to infer.  The predicates below are that grammar with its positions
made explicit, and the BNF is recoverable from each constructor by reading its
docstring — which is where the RFC production is quoted.

## The surface, as RFC 8259 writes it

```bnf
JSON-text   = ws value ws
value       = false / null / true / object / array / number / string
object      = begin-object [ member *( value-separator member ) ] end-object
member      = string name-separator value
array       = begin-array [ value *( value-separator value ) ] end-array
number      = [ minus ] int [ frac ] [ exp ]
int         = zero / ( digit1-9 *DIGIT )
frac        = decimal-point 1*DIGIT
exp         = e [ minus / plus ] 1*DIGIT
string      = quotation-mark *char quotation-mark
ws          = *( space / tab / line-break )
```

| production | declaration |
|---|---|
`JSON-text` | `TextAt` — with `skipFrom bs 0 = i` and `skipFrom bs j = bs.length`, so trailing non-whitespace has **no derivation** |
`value` | `ValueAt` — one constructor per alternative |
`array`, `object` | `ValueAt.array`/`.object` over `ArrBody`/`ObjBody` |
`*( value-separator value )` | `Elems`/`Members` — **a trailing separator has no derivation** (`Elems.last` versus `Elems.cons`) |
`member` | `Member`, with the `:` and the whitespace on both sides as separate premises |
`int`, `frac`, `exp` | `IntPart`, `Digits0`, `Digits`, `ExpPart`, composed by `NumBody` |
`number` | `RfcNumber` = `[ minus ] NumBody`, and `NumberAt` for the range |
`string` | `StringAt`, over the two-character escapes in `EscVal` and the code points of RFC 3629 |

**Two languages, one parser.**  `RfcText bs v` is RFC 8259 **as written** —
unpaired surrogate escapes included, duplicate names included, any depth.  The
language the parser is *proved* to accept is the restriction RFC 7493 §2.1 asks
for:

```lean
def ValidDocument (bs : Bytes) (v : Value) : Prop := RfcText bs v ∧ Policy v
```

`Policy` is the character constraint (`Value.charPolicy`); the two are separated
so that the difference between "valid JSON" and "what this parser accepts" is a
named conjunction rather than a silent narrowing.

## The theorems, in the order a reading is justified

**The tape carries the meaning, not a private decoding.**

```lean
theorem tape_valid (t : Tape) (v : Value) (h : decodeTape t = some v) :
    spansWellFormed t = true ∧ ValidDocument t.input v
```

Read: any tape that decodes to a value is a **well-spanned** tape whose input,
with that value, satisfies the surface above.  `spansWellFormed` is what makes
the tape's offsets answerable — a decoded value could otherwise name byte ranges
nothing checked.

**The parser produces only valid documents.**

```lean
theorem decodeTape_correct (l : Limits) (bs : Bytes) (t : Tape)
    (h : parseBytes l bs = .ok t) :
    ∃ v : Value, decodeTape t = some v ∧ t.input = bs ∧ ValidDocument bs v
```

This is the soundness direction: acceptance implies a value, and that the input
read back is the input given.  The converse — that every valid document is
accepted — is bounded by `Limits`, and **the bounds are refusals with reasons,
not silent truncation**: `ParseResult` has exactly two cases, `ok` and `error`,
so an input over `maxInput`, a byte-order mark, trailing data, or exhaustion of
`maxDepth`/`maxTokens` each yields an `error` carrying its cause.  There is no
third outcome in which the parser returns something a caller could mistake for
a value.

**The fast scanner says the same thing as the simple one.**

```lean
theorem scan_simd_refines_scalar (bs : Bytes) :
    (∀ q cs stop, bs[q]? = some 0x22 → scanCharsEnd bs (q + 1) 0 = .ok (cs, stop) →
      scanStringBlocks bs q = .ok stop.val) ∧ …
```

The block scanner is the one the emitted kernel runs; `scanCharsEnd` is the
byte-at-a-time reference. **Agreement is a theorem, so the SIMD shape is not
trusted to agree with the reference — it is proved to.**

**And the scanner cannot accept what the grammar refuses.**  In the refinement layer,
`envForScanWindow_refuses_valid` and `not_klTailByte_last_of_validPrefix` are the
two directions that let a window verdict be read as a statement about the
document: the first says a window the unit calls invalid is not a valid prefix,
the second that a valid prefix's last byte cannot be the killer lane.

## What the emitted units are proved to satisfy

Each translation unit carries its own record — a precondition, a postcondition,
and a `Satisfies` theorem relating the pinned emitted body to them:

| unit | theorem |
|---|---|
mask constructor | `masks_satisfies`, and `masksStaged_satisfies` at the staged shape |
entry position emitter | `entry_pos8_satisfies` (`entry_pos8_refines` at the IR level) |
entry byte emitter | `entry_b8_satisfies` (`entry_b8_refines`) |
UTF-8 verdict | `utf8_satisfies` (`utf8_stage_refines`, `_chars`, `_mod0`, `_zero`) |
escape positions | `escape_positions_satisfies` |
escape expansion | `escape_expand_satisfies`, conditional on three runs |
batch | `xl_batch_satisfies` |
assembled pipeline | `pipeline_satisfies`, conditional on the body's loop |

**And the assembled pipeline is connected to the surface**: `Sigma_pipeline` is
the spec-relative post, `pipeline_units_finalisation` derives it from the units'
composition given the parser half, and `ParserHalf` names exactly the three
conjuncts no unit post supplies.  `pipelineUnitsPost_not_imp_Sigma` is the
witness that the units' post alone does **not** imply the specification — which
is why the finalisation takes the precondition.

## Where the surface stops

Three things are **named and owed**, and no reading of this document should take
them as discharged:

1. **`Γ_stage2` does not exist.**  The stage-2 record is what supplies the
   pipeline's post clauses about the arena, the event stream and the cursors, so
   `pipeline_satisfies` keeps a hypothesis for them.  Deferred, not missing.
2. **`ParserHalf`'s number conjunct is unbuilt.**  The emitted event records a
   number as **eight bytes of a double**; the model keeps the **source lexeme**.
   `LeanLLVM.JSON.Strtod` states the lexeme-to-double specification
   (`strtodSpec`, with its rounding property, and the record's payload as
   `toBits (strtodSpec ·)`), but the emitted `num_fast`/`strtod` conversion is
   not shown to compute it — no run of emitted code is modelled and there is no
   counterpart in Vellvm.  The record states the correspondence as a parameter
   (`EventStreamRel`) rather than asserting an equality that is false.
3. **The refused document's offset is per stage.**  `RefusalOffset` distinguishes a
   UTF-8-owned refusal, where the caller reports the document's end, from a
   walk-owned one, which carries the parser's own position — because the two
   differ, and a sentence quantifying over both would be false.
