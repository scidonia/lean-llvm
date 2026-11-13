# The JSON route's residue

The fast path answers the documents its admission admits; every other document
is answered by the scalar reference parser once, and never pre-filtered.  This
page measures the other side of that boundary: **which** documents fall back,
**by which clause**, and what share of the JSON documents a producer would emit
takes the fast path at all.  The unit is documents, not time; every row states
its construction, and the page's numbers are one run of
[`probes/json/route/residue.sh`](../probes/json/route/residue.sh), recorded at
`0045f06` with the route rebuilt from the worktree's sources.

The decision measured is the one the route takes: `--admit <file> 1` prints the
two-phase decision, the clause that refused, the measured nesting and the
policy class on one line, and the script asserts on every row that the decision
is the library's `admission` (the row's `agree=1`).  The reference's verdict on
the same bytes is read from `leanllvm-json`, built from this revision; the
script runs it twice, the second time with the first reading written back as
the expectation, so the reading is reproduced and not only recorded.  Every
constructed document's expected reference verdict is asserted against the
printed one.

## The residue, by the admission clause that refused

Unit: documents.  The clause is the one `KernelRefusal` names: `emptyInput`,
`inputTooLong`, the measured `depthBound`, and the two character-policy
constructors.  A document the clauses admit is `admitted` here whether or not
the object accepts it — the admission is the pipeline's domain, not a syntax
check.

| set | docs | admitted | empty | inputTooLong | depthBound | policy: unpairedSurrogate | policy: noncharacter | unsupported |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| corpus (`tests/json/corpus`, one per manifest row) | 130 | 115 | 1 | 0 | 0 | 6 | 8 | 0 |
| scenario (`check.sh`'s generated rows) | 135 | 129 | 1 | 1 | 3 | 1 | 0 | 0 |
| bench (`bench.sh`'s corpus + `scale-4096.json`) | 11 | 10 | 0 | 0 | 1 | 0 | 0 | 0 |
| plausible (the constructed shapes below) | 14 | 8 | 0 | 1 | 3 | 1 | 1 | 0 |
| **total** | **290** | **262** | **2** | **2** | **7** | **8** | **9** | **0** |

The five constructors are the whole refusal vocabulary: no row is refused for
an "unsupported domain" reason, because `admission` has no such clause.  A
document whose *syntax* the object will refuse is not residue — the admission
admits it and the object answers, with `verdict=0`, on the fast path.  That is
why this table's residue is smaller than the set of documents that are not
JSON: of the 290 rows, 59 are not a JSON text, and 55 of those 59 are admitted
and take the fast path, the object refusing them with `verdict=0`.  The four
that are not admitted are the two empty documents, the over-bound document, and
the scenario's `quote-after-refused`, whose second body is a policy refusal.

Two rows are worth reading as their own finding:

* the scenario's over-bound document is 1,048,577 zero bytes; the clause that
  refuses it is the length clause, and the reference's own verdict is
  `inputTooLong`;
* the scenario's `quote-after-refused` document (`"\q" "\uD800"`) is refused by
  the **character policy** at byte 6, not by syntax at byte 2: the policy scan
  runs at every quote byte in document order, which is the reference's own
  rule.

## The fast-path share

Unit: documents.  "Valid" is the reference's own acceptance under
`Limits.default`, with two documented exceptions: the fourteen corpus rows the
reference refuses only under RFC 7493's character policy (lone and reversed
surrogates, noncharacters, escaped and raw — the class the policy clause
exists for) and the three corpus rows a non-default profile refuses
(`depthExceeded` under `depth2`, `outOfCapacity` under `tok4`, `inputTooLong`
under `in8`, each accepted under `default`) are valid JSON inputs.  The sweep's
120 random documents carry no validity claim: they are in the residue table and
in no share.

| population | docs | valid | unknown | fast (valid) | share |
|---|---:|---:|---:|---:|---:|
| corpus | 130 | 79 | 0 | 65 | 82.3% |
| scenario (route rows) | 135 | 8 | 120 | 5 | 62.5% |
| bench | 11 | 11 | 0 | 10 | 90.9% |
| plausible (constructed) | 14 | 13 | 0 | 7 | 53.8% |
| constructed = bench + plausible | 25 | 24 | 0 | 17 | 70.8% |
| constructed + corpus | 155 | 103 | 0 | 82 | 79.6% |
| every set | 290 | 111 | 0 | 87 | 78.4% |

Each share is `fast(valid) / valid` for the population named on its row, in
documents.  The population is the construction: the corpus is small syntax
fixtures, the bench is ten generated payloads plus the repository's 178-object
document, and the plausible set is the fourteen constructed documents below.
There is no claim that these mixes are a sample of the world.

**The residue of the 111 valid documents is 24**, and it splits:

| clause | valid documents | of which |
|---|---:|---|
| `inputTooLong` | 1 | a valid 1,048,577-byte array |
| `depthBound` | 7 | the scenario's 129, 520 and 521; the bench's 129; the plausible class's 129, 256 and 520 |
| policy: `unpairedSurrogate` | 7 | six corpus rows plus one 256 KiB string |
| policy: `noncharacter` | 9 | eight corpus rows plus one 256 KiB string |

So the residue of the valid population is dominated by the character policy
(16 of 24) and deep nesting (7 of 24); the length bound costs one document.  An
input bound that admits 1 MiB exactly admits most real payloads; a depth of 128
is what excludes the deep-but-valid class, and `scale-4096` — 179 opener bytes at
a nesting depth of 2 — is on the fast path, so opener bytes are not the
residue.

## The constructed plausible-document classes

The corpus does not carry these shapes, so each is constructed here.  Sizes are
bytes; the reference verdict is `leanllvm-json`'s on the same bytes.

| class | docs | valid | fast | bytes | reference verdict | admission |
|---|---:|---:|---:|---|---|---|
| all-whitespace | 1 | 0 | 0 | 65,536 | `invalid` | fast path (`verdict=0`) |
| whitespace-wrapped | 1 | 1 | 1 | 102,407 | `accept` | fast path |
| deep (129, 256, 520 nested arrays) | 3 | 3 | 0 | 258–1,040 | `depthExceeded` | `depthBound` |
| long-string (262,144 ASCII bytes) | 1 | 1 | 1 | 262,148 | `accept` | fast path |
| long-string-policy (`\uD800` / raw U+FFFF after 262,144 ASCII bytes) | 2 | 2 | 0 | 262,151–262,154 | `invalid` | `unpairedSurrogate@262146`, `noncharacter@262146` |
| escaped-heavy (100,000 `\u00e9`; 1,000 escaped quotes; 1,000 surrogate pairs; 1,000 raw two-byte characters) | 4 | 4 | 4 | 2,004–600,004 | `accept` | fast path |
| large (an array of 209,715 numbers at exactly 1,048,576 bytes, and the same plus one space) | 2 | 2 | 1 | 1,048,576–1,048,577 | `accept`, `inputTooLong` | fast path, `inputTooLong` |

Constructions, one line each, as the script writes them:

| document | construction |
|---|---|
| `ws-only-64k` | 65,536 space bytes and no value — not a JSON text; admitted and answered on the fast path with `verdict=0 err=65536` |
| `ws-wrapped-100k` | `[1,2,3]` with 51,200 spaces before and after — whitespace around a JSON text is legal, and the admission does not look at it |
| `deep-129`, `deep-256`, `deep-520` | 129, 256, 520 nested arrays (520 is the object's own stage-2 stack bound); all refused at the measured depth |
| `str-256k-ascii` | `["` + 262,144 `a` + `"]` |
| `str-256k-u-d800` | `["` + 262,144 `a` + `\uD800` + `"]` — a syntactically legal escape, refused only by the character policy |
| `str-256k-raw-noncharacter` | `["` + 262,144 `a` + raw U+FFFF (EF BF BF) + `"]` |
| `esc-heavy-u00e9` | 100,000 `\u00e9` escapes in one string |
| `esc-heavy-quotes` | 1,000 escaped quotes; the reference's policy scan is quadratic in them, which is why this one is 1,000 and not 100,000 |
| `large-at-bound` | 209,715 copies of `1234` in an array, exactly 1,048,576 bytes |
| `large-over-bound` | the same array plus one trailing space, 1,048,577 bytes — still a JSON text, refused by the length clause |
| `surrogate-pairs-1000` | 1,000 `\uD83D\uDE00` pairs in one string |
| `unicode-2byte-1000` | 1,000 raw two-byte characters in one string |

The constructed share is the one number the corpus cannot give: **17 of 24**
valid documents (70.8%) when the bench and the constructed classes are taken
together, **7 of 13** (53.8%) if the plausible classes are read alone.  The
figure is construction-dependent and the construction is on the row: the deep
class is 3 of the 14 plausible documents, and counting the depth boundary once
(129 alone) instead of three times makes the constructed population 17 of 22
(77.3%).  What does not move is the class-level finding: every valid document
that is *not* deep, over-bound, or policy-carrying takes the fast path — 17 of
the 17 such documents in these sets, including 1 MiB arrays, 600 KiB
escaped-heavy strings, raw UTF-8 and surrogate pairs.

## What this does and does not establish

It establishes the route's decision on 290 documents with the reference's own
verdict beside it, the class of every refusal among them, and the fact that no
row is refused for a reason outside `KernelRefusal`'s five constructors.  The
validity column is the measurement's only judgment: it is asserted against the
reference for every row whose expected verdict is stated, and `?` for the swept
documents, which is why those 120 rows enter no share.

It does not establish a rate for the world.  The corpora are the repository's;
the plausible classes are constructed, one or three documents per shape, and
their share is a statement about those documents.  The policy rows are the
reference's RFC 7493 choice, so a producer that emits lone surrogates or
noncharacters falls back by construction; a producer that does not never pays
that clause.  The depth class is the same kind of statement at 128.  A document
outside these sets is decided by `admission`'s definition and not by a row
here.

It also does not price the fallback.  The fallback's cost on the boundary
documents is on [the stage timings page](json-route-stage-timings.md); this page
says how often each clause sends a document there.
