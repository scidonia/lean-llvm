# The JSON pipeline's Lean call route

The review's step D: a Lean program that stages the document the assembled
pipeline's record demands and calls the native object.  The contract is
`LeanLLVM/JsonCallRoute.lean`; this directory is its executable route.

| File | What it is |
|---|---|
| `RouteMain.lean` | the standalone Lean entry point: it takes the document decision in two phases — the adapter's native facts (the maximum structural nesting and the policy-candidate flag), then the probe's own native character-policy scan (`policy.c`) where that flag is set — and falls back to `parseBytes` for every document that decision refuses (one shell, not two).  It stages the document in the record's shape on the fast path, calls the object through the adapter, and prints one of the three outcomes.  `--stages` splits the route into its stages and the outcome stage into its five parts; `--admit` prints the two-phase decision beside the library's `admission` and the library's `policyRefusal` on the same bytes; `--consume` reads the fast path's result without printing, as a fold and as a per-token value array |
| `shim.c` | the adapter: validates the staging, allocates its zero-filled buffers (`leanllvm_route_zeroed`: one allocation and one `memset` each, in place of `Array.replicate`'s boxed fill), copies the caller's `ByteArray`s into the object's ABI (the document window is handed over in place, because the object only reads it), fills the entry unit's POS8 table, calls `leanllvm_json_pipeline`, and returns the tagged result.  It also runs phase one of the admission — the walk over the document's structural delimiter sequence, whose maximum is the depth clause's number and whose lane list goes through the proved depth counter — phase two's wrapper over the policy scan, and the depth pass the admission record reports |
| `policy.c`, `policy.h` | phase two of the admission: the character-policy scan, native, reproducing `policyRefusal`'s decisions branch for branch — the class and the byte — over the document's bytes, with a screen that answers a document no policy refusal is possible in without visiting a position.  Its `policy_step` is also the body scan phase one walks (`leanllvm_route_body_stop`), so the depth clause's string spans and the policy class array are one reading of a body |
| `driver.c` | a C caller that stages the document identically and prints the same three lines, for the fidelity comparison |
| `build.sh` | compiles the six kernel units, the proved depth counter (`tests/v16/depth_count.ll`), the policy scan, the adapter and the program, links them (the program's library modules link from their emitted C), and asserts every symbol the adapter calls is imported and defined |
| `check.sh` | the route scenario: fidelity against `driver.c` on every admitted row, each fallback answer against the manifest, the empty/over-bound/opener-rich documents, the depth boundary, the depth clause's own documents and a fixed-seed malformed sweep, the fourteen-row policy class, the three outcomes' distinctness, the two-phase decision's agreement with `admission` on every row — at the refusal's class and byte, and at the measured depth wherever the walk ran — with a control that must report a disagreement, and the consumer mode's reading of a five-event fixture |
| `bench.sh` | the route's per-stage timings, the outcome stage's five parts, the consumer rows, the object's -O2/-O3 pair taken paired against a drift control, the boundary rows' two paths, and the simdjson reference arm; the record is [the stage timings page](../../../docs/json-route-stage-timings.md) |
| `bench/simdjson-baseline.cc` | the reference arm: simdjson 4.6.11 on-demand over the same documents, its `padded_string` staging and its `iterate` plus full value traversal timed apart |
| `correspondence.sh` | the stage-2 artifact correspondence: the flags, the derivation steps, which bodies are identical under the transform, and what is left over |
| `DomainCheck.lean` | the library shell's `documentDecision` and `checkRoute`, elaborated from source: every admission clause on both sides, both fallback outcomes, the fourteen-row policy class, and the layout checks |

## The three outcomes

The decision is the library's `LeanLLVM.JsonKernelDomain.admission`, taken in two
phases: the native facts about the bytes (non-empty, inside the input bound, no
deeper nesting than the bound admits, and whether any byte could carry a
character-policy refusal), then the native character-policy scan where that last
flag is set.  Its clauses are the certified checkers whose certificates are in
`LeanLLVM/JsonKernelCertificate.lean`, and the two-phase decision is asserted
against `admission` itself on every corpus row by `check.sh` — verdict and
reason, and the reason of a policy refusal carries the byte it is reported at.
The library's own `policyRefusal` is not on this path: it is the oracle
`--admit` measures and prints beside the native answer.  A document takes exactly
one of three paths, and the output distinguishes them:

* **the fast path** (`verdict=...` on stdout).  The decision admits the
  document, the program stages it, and the native object answers; the
  observation, the arena and the event stream are printed.  This is the only
  path that calls the object.
* **the fallback's refusal** (`refused: ...` on stderr, exit 2).  The decision
  does not admit the document and the scalar reference parser refuses it; the
  reason and position printed are `parseBytes`'s own.
* **the fallback's acceptance** (`fallback=accepted tokens=<n> decoded=<0|1>`).
  The decision does not admit the document and the reference parser accepts it;
  the tape is the answer, and `decoded` reports whether `decodeTape` gave a
  value.

The fallback is the reference parser for every document the domain does not
admit, and for no other document: it is not consulted before the decision and
not on the fast path.  The domain is exactly what the certified checkers decide,
so the open/closed question of the fast path's totality is a question about
those clauses and nothing else.  The decision is `admission`'s because
`--admit`'s two readings are compared row by row; what makes the native side
equal to `admission` is argued clause by clause in the adapter's comment (the
delimiter mask marks every structural byte wherever it falls, and a quote byte
is either unescaped or preceded by a backslash), and observed, not proved —
the counting routine is new code with no refinement theorem yet.

## Commands

```bash
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonKernelDomain LeanLLVM.JSON.Parse
nix develop -c bash probes/json/route/build.sh
nix develop -c bash probes/json/route/check.sh
"$PWD/probes/json/route/build/leanllvm-json-route" --consume tests/json/corpus/depth-two-ok.json 21
"$PWD/probes/json/route/build/leanllvm-json-route" --admit tests/json/corpus/depth-two-ok.json 21
nix develop -c bash probes/json/route/correspondence.sh
bash probes/json/route/bench.sh 21        # re-executes itself under a 6 GiB scope
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonCallRoute
nix develop -c bash probes/install/lake-locked.sh env lean probes/json/route/DomainCheck.lean
```

`build.sh` prints `ok: .../leanllvm-json-route`; it fails if `nm` does not show
`leanllvm_json_pipeline`, `leanllvm_json_entry_table`, `leanllvm_json_s1_masks`
and `depth_count` imported by the adapter and defined by the executable, so a
build that lost a call or the table's initialisation is a red rather than a
pass.  It compiles the program with
`lake env lean -c` because the program imports the library's decision and parser;
the first command builds their Lean modules and their emitted C, and `build.sh`
stops with that command in its message when they are absent.  `correspondence.sh`
prints the artifact relation; its output is recorded in
[the correspondence page](../../../docs/json-route-artifact-correspondence.md).
`DomainCheck.lean` needs the library's oleans, which the fifth command builds.

`build.sh` takes two knobs, both defaulting to the build the route ships:
`OPT` is the optimisation level of the six kernel translation units (the
route's object) with the adapter and every other flag held fixed, and
`TIMING=1` compiles the adapter with the stage instrument `--stages` reports.
The instrument is a compile-time gate: the ordinary adapter contains no clock
read, which `build.sh` asserts with `nm` rather than assuming.  `bench.sh` uses
`OPT` for the -O2/-O3 pair and `TIMING=1` for the stage rows.

## The stage report, and the consumer's reading

`--stages <file> <reps>` reports one median per stage and, for the fast path,
five medians for the outcome stage's parts: `outcome_decode_ns` (the tagged
header and its seven words), `outcome_slice_ns` (the two payloads cut out),
`outcome_header_ns`, `outcome_arena_ns` and `outcome_events_ns` (each line built
and written).  Their per-repetition sum is `outcome_ns`, so the five clock reads
that divide them are inside the stage.  `hex_arena_ns` and `hex_events_ns`
rebuild the same two payload lines with the write removed, after the stage's
timed window; the difference between a payload part and its hex figure is that
line's write.  The parts price the route's own reporting, not the object.

The admission stage is the two-phase decision and reports its split:
`admission_ns` is both phases, `admission_native_ns` is phase one's native call
(including the `@[extern]` call and the nine-word header decode) and
`admission_policy_ns` is phase two — the native policy scan, including its own
`@[extern]` call and six-word header decode — present only on the rows whose walk
saw a candidate byte; `admission_policy_ns=-` is a row where the phase was
skipped.  A row also carries the facts the decision was taken on:
`admission_depth` (the maximum structural nesting the depth clause compares),
`admission_candidate`, `admission_blocks` and `admission_clause`.

`--admit <file> <reps> [<native depth>]` is the agreement probe rather than a
route: it runs phase one, the depth pass, the two-phase decision, the library's
`admission` and the library's own `policyRefusal` on the same bytes, and prints
one line with both verdicts, both reasons, the depth each side measured, the
candidate flag, both policy readings (`policy_native` is the native scan's
answer, `policy_oracle` the reference's), the depth pass's facts, and the medians
of phase one, the depth pass, the native phase two, the reference's scan, the
certified predicate and the two-phase total.  `check.sh` reads the verdicts,
reasons and depths out of that line and compares them itself: a policy refusal's
reason carries its byte, so that comparison covers the class and the position,
and `native_depth`/`certified_depth` cover the depth clause's number rather than
its class alone.  The
optional third argument is the native side's depth bound; it defaults to
`kernelMaxDepth`, and the scenario's control is the only caller that moves it.

`--consume <file> <reps>` is the production reader's number: it runs the fast
path once per repetition and reads the result without printing — the header by
index, the event stream record by record at the widths `kernel/json/stage2.h`
documents — as a fold that keeps no per-token object (`consume_fold_ns`) and as
one that materialises an event record per token (`consume_values_ns`).  The two
alternate which goes first.  The mode exits 5 unless both readings count the
same tokens, land exactly on the event stream's end and produce the same
checksum, so a row reports a reading that was checked rather than a duration
alone.

## Observed

`check.sh`, over the 122 default-profile manifest rows, the boundary documents,
the depth clause's own documents and its fixed-seed sweep:

```text
the two-phase admission against the certified predicate, by row class
(class is verdict/reason/candidate/policy; rows is how many rows it covers;
the rows are every manifest row and the boundary documents)

class                                          rows
0/depthBound/0/0                                  3
0/emptyInput/0/0                                  2
0/inputTooLong/0/0                                1
0/noncharacter@1/1/1                              8
0/unpairedSurrogate@1/1/1                         6
0/unpairedSurrogate@6/1/1                         1
1/none/0/0                                       78
1/none/1/1                                      166

ok: 122 default-profile rows: 107 fast-path row(s) agree with the driver on the observation, arena and events (22 arena byte(s) over 9 row(s), 1138 event byte(s) over 70 row(s)); fast path accept 59, invalid 48; fallback refusals 14, fallback accepts 0; divergence 0; empty excluded 1; 8 non-default-profile rows skipped; depth 128 fast, 129/520/521 fall back with depthExceeded; the opener-rich string takes the fast path; 14 policy rows fall back with the reference reasons; two-phase admission agrees with `admission` on 265 row(s), the measured depth compared wherever the walk ran (policy candidate 181, policy scan run 181; control failures 0); the depth gate carries 11 hand-written row(s) and 120 swept document(s) agree with `docDepth`, the proved counter and the accumulator ending at the same depth on every row; 1 consumer-mode fixture read as 5 tokens at ndst=1 nev=25 with agreeing readings
```

The class table is the agreement gate's own row set, grouped: every manifest row
whatever its profile (the decision is about the bytes, and a profile only selects
which rows the fidelity comparison runs), the empty, over-bound and four depth
documents, the depth clause's eleven documents, and the 120 swept documents.  The
verdict, the reason and — wherever the native walk measured one — the depth are
the same on all 265: `1/none/*` are the admitted rows, `0/depthBound/0/*` the
depth boundary, `0/*@1/1/1` the fourteen policy rows, where the walk saw a
candidate and the native scan ran and refused.  A policy reason carries the byte
the refusal is reported at (`0/noncharacter@1/1/1` is a noncharacter at byte 1),
and that byte is the reference's: the two decisions are compared as
`KernelRefusal` values, so the gate would report a native scan that named the
right class at the wrong byte as a disagreement.  `0/unpairedSurrogate@6/1/1` is
the quote-after-refused document: its first body is a bad escape, which ends the
depth walk's token sequence at byte 0, and the refusal the reference reports is at
the *second* quote's body, byte 6 — the candidate flag is not the walk's
frontier but the document's quote bytes, so the phase still runs.  The rate is
what the native unit was for: 181 of 265 rows carry a quote or a backslash byte,
and every one of them pays the scan.

- the 107 admitted rows — 59 the manifest calls `accept` and 48 `invalid` —
  take the fast path, and the Lean route and the C driver print the same three
  lines on every one: verdict, four cursors and error offset; the arena and the
  event stream are compared byte for byte, so equal lengths and a shared verdict
  cannot conceal different values.  The comparison is field-wise: a verdict
  disagreement, a value disagreement (naming the stream and the first differing
  byte) and a metadata disagreement are separate diagnostics.  Between the route
  and the driver no difference is allowed, because both call the same object
  with the same staging;
- divergence is 0: every fast-path row's verdict agrees with the reference's,
  and every fallback row's answer *is* the reference's;
- the 14 `invalid` rows the object accepts and the reference refuses under its
  **character policy** fall back, and the fallback refuses them with the
  reference's own reason and byte.  The class is: lone and out-of-range
  surrogate escapes (`lone-dead.json`, `lone-d800.json`, `double-high.json`,
  `high-char.json`, `reversed-pair.json`, `lone-dc00.json`) and noncharacters,
  escaped and raw (`nc-fdd0.json`, `nc-fffe.json`, `nc-ffff.json`,
  `nc-pair-max.json`, `nc-raw-fdd0.json`, `nc-raw-fffe.json`,
  `nc-raw-10ffff.json`, `nc-raw-1fffe.json`).  RFC 7493 §2.1 is the reference's
  policy, and `DomainCheck.lean` pins both the class and the shell's decision;
- the empty document falls back and is refused with `unexpected end at 0`; an
  over-bound document falls back and is refused with `input too long`;
- the four depth probes: 128 is admitted and the object accepts it; 129, 520 and
  521 are outside the domain and fall back with the reference's `depthExceeded`.
  The driver is still run at 129 and 520, and it accepts — that class is the
  reason the depth clause exists, and the route no longer calls the object
  there;
- the opener-rich document — a string carrying 129 `[` bytes — measures 0 and
  **takes the fast path**, and the object accepts it with the driver's own
  observation.  That row is the disagreement the previous rule produced: the
  opener-count rule measured 129 and sent it to the fallback while `admission`
  admitted it;
- the depth clause's own eleven rows, each asserted against a hand-written
  measurement as well as against `docDepth`: the opener-rich string (0), 200
  shallow sibling containers (2, with 401 opener bytes), `]] [[` (0 — the prefix
  sums go negative, where a counter clamped at zero would read 2), an
  unterminated body and a bad-escape body (2 each, the sequence ending at the
  quote), the quote-after-refused policy row (0, refused at byte 6), a body with
  escaped quotes and 200 `[` bytes (1), two bodies straddling a 64-byte block
  boundary (1 each), and the 128/129 boundary (128, 129);
- the sweep: 120 documents of 1–200 bytes drawn by a fixed-seed Lehmer generator
  from the bytes the rule branches on (both bracket directions, quotes,
  backslashes, escape and hex letters, spaces, `:`), compared row by row on
  verdict, reason and measured depth.  Its first run is what found the
  classifier's in-string mask to be a different reading of a string from the
  reference scan's: a top-level `"` opens a body `structTokensFrom` skips but the
  mask does not, so the fold is the walk's own;
- the depth pass reports the proved counter's recombined final depth and the
  walk's accumulator beside it, and the gate requires them equal on every row:
  two arithmetics over one structural lane list, neither of which the other
  derives;
- the consumer mode reads `["\n",123,true]` — an array, an escaped string (one
  arena byte), a number, `true` and the array's close — as 5 tokens over 25
  event bytes with one arena byte, and its fold and values readings agree on the
  token count and the checksum.  The record widths it decodes at are the ones
  `stage2.h` documents, so a width change that left the object's stream
  unreadable is a red rather than a shorter row.

The byte comparison is not vacuous: the run counts the bytes it compared and the
rows that carried any, and fails when either arm is empty.  Every assertion above
has a cut that makes it fail; the cuts and their observed output are recorded
below.

## The controls

Eight cuts: five cut the probe's shell, two cut the native policy scan, and one
restores the depth clause's previous rule.  Each was applied one at a time and
rebuilt, and the tree was restored and rebuilt after each — the final run above
is the restored build's.  The first four cut the probe's shell (`RouteMain.run`)
at the decision's *consumer* rather than in `admission` itself because the clause
definitions carry the certificate's proofs: removing a clause there replaces a
proof, which is a build failure rather than an assertion failure, and the point
of these controls is that the scenario notices a document taking the wrong path.
The fifth cuts the consumer mode's record-width table.  The last three cut native
code in place — `policy.c` twice, `shim.c` once — each built into its own
`BUILD_DIR` and run with `ROUTE=` pointing at that build, so the shipped build
was never the one under test.

| Control | Cut | First observed red |
|---|---|---|
| depth-129 falls back | `.error (.depthBound _) => runFast …` | `FAIL: depth 129: expected the fallback's depthExceeded refusal (exit 0)` (and 520, 521, the opener-rich document) |
| a policy-violating document falls back | `.error (.unpairedSurrogate _) \| .error (.noncharacter _) => runFast …` | `FAIL: the fallback refuses a different policy class than the one pinned`, `FAIL: expected 14 policy refusals, saw 0`, and the fourteen rows counted as divergences |
| over-length falls back | `.error (.inputTooLong _) => runFast …` | `FAIL: the over-bound document was not the fallback's refusal (exit 0)` |
| a policy-clean in-domain document takes the fast path | `.ok () => … runFallback doc` (with `runFast` still referenced from a branch that is not taken, so the link step keeps the call) | `FAIL: the fast-path arm is empty (accept 0, invalid 0)`, `FAIL: no compared row carried arena bytes…`, and the depth-128 row losing its observation |
| the consumer decodes the record widths | `eventWidth`: `tag == 7 then 9` → `then 1` (a number read as a one-byte record) | `FAIL: --consume read the five-event document as: … tokens=13 values=13 …` and `FAIL: 1 assertion(s) failed over 122 default-profile rows` |
| the native scan raises the surrogate class | `policy.c`: the high-surrogate branch's `if (cv >= 0xD800u && cv <= 0xDBFFu)` → `if (0)`, so a `\uD800` form is accepted as an ordinary character | `FAIL: lone-d800.json: the two-phase decision and the certified predicate differ` — also `double-high`, `high-char`, and `pair-d834`/`pair-i-json`, where a *valid* pair is now refused because its low half is read as unpaired — then `FAIL: expected 14 policy refusals, saw 11` and `FAIL: 3 default-profile rows still diverge from the reference: lone-d800.json double-high.json high-char.json`; 9 assertions failed |
| the native scan reports the refusal's byte | `policy.c`: `policy_refusal_pos` returns `i - s` (the body-relative offset) instead of `i` | every one of the fourteen policy rows: `FAIL: <row>: the two-phase decision and the certified predicate differ`, with the row itself `policy_native=unpairedSurrogate@0 policy_oracle=unpairedSurrogate@1 … reason=unpairedSurrogate@0 certified_reason=unpairedSurrogate@1 agree=0` |
| the depth clause's number | `shim.c`: `depth_measure` keeps the walk and its lane list, and sets the clause's number to the previous rule's opener-byte count over the whole document (string bodies included) instead of the maximum it tracked | `FAIL: opener-rich: the two-phase decision and the certified predicate differ` with `native_depth=129 certified_depth=0`; also `siblings` (201 against 2), `escaped` (201 against 1), `straddle-body`/`straddle-quote`, and 113 of the 120 swept rows; `FAIL: the opener-rich document did not take the fast path`, and the depth gate's own expectations `FAIL: <row>: measured depth native=… certified=…, expected …`; 129 assertions |

The first attempt at the fifth cut — routing *all* documents to the fallback —
failed the build instead (`build: the executable does not define
leanllvm_json_pipeline`), because Lean's compiler eliminated the unused extern
call; that is a scaffolding failure, not a red, which is why the recorded cut
keeps a live reference to `runFast`.

The seventh cut is the control for the byte being part of the compared value:
without it, the gate would pass a scan that named the right class at the wrong
position, which is exactly the near-miss a comparison of class names alone
cannot see.

The eighth cut is the control for the depth clause: it keeps everything the new
measurement does — the walk, the lane list, the proved counter beside it — and
moves the clause's number alone back to the rule it replaced, so the red is the
number and not the machinery.  It fires in three ways, and all three are wanted:
the row comparison (`native_depth` against `certified_depth`), the route taking
the fallback for a document the domain admits, and the depth gate's hand-written
expectations.  The opener-rich row is also the witness that the row
comparison is not a comparison of class names: on the cut it reads
`native_depth=129 certified_depth=0` with `reason=depthBound` against
`certified_reason=none`, and `neg-prefix` is a row where the verdict and the
reason agree on both sides (`1`/`none`) and only the number differs (`2` against
`0`) — a red only because the depth is compared.

The agreement gate's controls are not cuts: they are inputs the comparator must
catch, and they run inside the scenario rather than in a throwaway copy.

| Control | What is moved | Observed |
|---|---|---|
| the comparator catches a disagreement | `--admit [1,2] 5 0`: the native depth bound set to zero, so one opener is refused natively while `admission` admits it | the shell's own comparison reports the two decisions differ, the row's `agree=0`, `native=0 native_clause=3 certified=1 reason=none` |
| the shipped route uses the native bound | `--doc depth-128.json 127`: the route's own decision with the bound one below 128 | the route takes the fallback (`fallback=accepted`, no `verdict=` line) instead of the fast path, so the path is the native decision's |
| the candidate detector fires both ways | `"a"` (a raw quote), `[1,2]` (no quote), `\"` (an escaped quote and no raw one) | `candidate=1`, `candidate=0`, `candidate=1`: the flag is not a detector that always fires, nor one that never does |

## The decision's two phases, and where they could differ

Phase one is new code, and its claims are argued in `shim.c` and observed rather
than proved.  The measure is the maximum running depth over the document's
structural delimiter sequence: a `"` opens a string body that the walk skips to
the reference body scan's stop (`leanllvm_route_body_stop`, `policy_step`
walked), a body that scan refuses ends the sequence, and every other byte is a
token if it is one of `{`/`[`/`}`/`]`, stepped and tracked for the maximum.  The
walk reads the bytes it folds and does **not** use the mask unit's `in_string`
lane, because that lane is the classifier's unescaped-quote reading: a top-level
`\"` opens a body `structTokensFrom` skips and the classifier does not, and the
gate's fixed-seed sweep contains the document that says so.  The candidate flag
is the walk's own reading of the bytes it visits — every body is opened by a
quote the walk sees — so a document with a quote byte always sets it, including
after a body the walk stopped at.

`check.sh`'s agreement gate is the observation: 265 rows, the two verdicts, the
two reasons and, wherever the walk measured it, the two depths compared in the
shell.  The proved counter is run over the same structural lane list and its
recombined final depth is compared against the walk's accumulator on every row;
the maximum itself is the walk's, since neither of the counter's two statistics
determines one.

Phase two is the native character-policy scan (`policy.c`), run only where that
candidate flag is set.  The reference's own `policyRefusal` is the oracle:
`--admit` runs it on the same bytes and prints both readings, and the gate
compares the two decisions — class and byte — on every row.

The rule it reproduces is `policyRefusal`'s: run the reference's body scanner
(`scanCharsEnd`) at every byte that is `"`, and report the first body scan that
refuses with `.unpairedSurrogate off` or `.noncharacter off`.  Every other
refusal a body scan can report — a control byte, bad UTF-8, a bad escape, the
document ending — makes that quote's scan report nothing, and the scan from the
*next* quote still runs; that is why a quote byte inside a body (an escaped `\"`)
is a scan start of its own, and why a scan can reach a refusal an earlier scan
stopped short of.

`policy.c`'s `policy_step` is `scanCharsAt`'s branch structure: the same accept
sets, the same lookahead, the same order in which a refusal is raised.  Its
answer depends only on the position a scan starts at — every refusal it reports
is a document position, and the scanner's fuel (`bs.size - i`) cannot end a scan
that advances at least one byte per step before the byte lookups end it — so one
backward pass fills `cls[i]` (`cls[i]` is either raised at `i` or is `cls[next]`
for the single position the step continues at) and the forward pass reads
`cls[q + 1]` at every quote byte in document order, which is `policyRefusal`'s
`findSome?` order.  The quote bytes come from the mask unit's lanes: `quote` is
the block's unescaped quotes, and an escaped quote is a `backslash` lane's next
byte, which is why the mask unit is the block pass and not a second classifier.

The screen is what makes the phase cheap.  A character-policy refusal is
possible only where a `5C 75` pair or a byte at or above `0xEF` occurs:
`unpairedSurrogate` is raised in the `\u` branch and nowhere else, `EscVal`'s
eight characters are all below `0x80` and so cannot be noncharacters, and every
noncharacter's UTF-8 form leads with `0xEF..0xF4`.  A document with neither is
answered without visiting a position, so an ASCII document and a document of
`\n` escapes both leave phase two as one pass over the bytes; a document that
carries a `\u` or a high byte pays the exact scan.  The screen is a necessary
condition, so it cannot hide a refusal, and a document it lets through pays the
scan (measured in [the stage timings page](../../../docs/json-route-stage-timings.md),
which also carries the candidate-heavy row set the corpus was extended with).

What is not proved: the **body-level** correspondence — this unit is not in
`kernel/json/` and its emitted body carries `switch`, `insertvalue`/
`extractvalue` and an anonymous-struct return, all outside the modelled
fragment, so a fixture refinement needs those forms modelled or the fixture
rewritten, and neither exists yet.  At the model level the agreement **is**
proved: `LeanLLVM/Refinement/JsonPolicyModel.lean` writes the emission's
transition (`policyStep`) beside the reference's (`scanCharsFrom`) in the
emission's branch order, and proves the step-by-step equivalence
(`policyStep_spec`), the walk (`policyWalk_spec`), the classifier
(`policyClass_refClass`) and the backward fill (`policyClass_backward`),
bridged to the reference's own error values by `Scan.scanCharsEnd_error`,
each pinned at `[propext, Quot.sound]`.  What establishes the *C body* is observation, in three readings: the gate's
265 rows (verdict, reason, and the refusal's byte); the candidate-heavy corpus
the bench measures, whose rows the gate's comparison also covers where they
overlap; and two differential sweeps against the oracle — 1547 random documents
drawn from the bytes the rule branches on (534 with the scan run, 29 policy
refusals), and 3618 documents that place every escape form (a surrogate pair,
each lone half, escaped and raw noncharacters, truncated forms) at every offset
0..200, so each straddles a 64-byte block boundary twice.  Zero disagreements in
either, at class and at byte.  The oracle is the library's own `policyRefusal`,
so these compare against the reference's scan and not against a second reading of
this page.  A document outside those sets is decided by the same argument and not
by an assertion.  The depth clause's *predicate* is certified: the bridge
(`JsonKernelCertificate.depth_bridge_core`) proves the counter's verdict and the
reference's `depthExceeded` agree, so `admission` is the reference's decision on
this clause by proof.  What is observed is the *native measurement*: the walk is
new code with no refinement theorem, and the gate compares its number against
`docDepth` on every row where it ran — the 11 hand-written depth documents and
the 120 swept documents among them.  A balanced document whose string bodies
carry many `[`/`{` bytes is admitted (`scale-4096.json` holds 179 opener bytes at
a nesting depth of 2); a document nested past the bound is refused at the number
it nests to; and a document whose prefix depth goes negative is measured at 0,
which a clamped running counter would not be.

## The adapter's tagged result, and why nothing is clamped

`shim.c` returns ten header words and then the payloads: `tag detail want got`,
then `verdict nk nxp ndst nev err`.  The tag names the class — the object ran
and accepted, the object ran and refused, a staging precondition failed before
the call, a staging copy could not be allocated, or a returned cursor exceeded
its capacity — and `detail`/`want`/`got` name the failing check with its
expected and observed numbers.  `RouteMain.lean` prints the observation for the
first two classes as before, and reports the last three on stderr at exit 3, 4
and 5.

The admission call returns a header of its own, nine words and no payload:
`tag detail want got depth candidate blocks verdict clause`.  `detail`,
`want` and `got` are the failed precondition's when the tag is the failure class;
otherwise `got` is the measured maximum structural nesting and `depth` the same
number (the clause's comparison is `want`/`got`), `candidate` the policy flag,
`blocks` the document's 64-byte block count, `verdict` the native clauses'
decision, and `clause` which of them refused (`0` none, `1` empty, `2` over-long,
`3` too deep).  On the empty and over-long clauses `depth` and `got` are zero and
mean nothing: the decision returns before the walk runs.  The policy scan's header is six words, no payload:
`tag detail want got class pos` — `class` is `0` for a document the character
policy admits, `1` for an unpaired surrogate escape and `2` for a noncharacter,
`pos` the byte the reference names (meaningful only when `class` is not `0`), and
`want` the document's length; a class array that could not be allocated is tag
`3` and is reported at exit 4 rather than read as an admitted document.  The
depth pass's header is nine words: `tag detail want got final sum structurals
max walk_final` — the proved counter's recombined final depth and prefix-depth
sum over the structural lane list, the number of tokens in it, the walk's maximum
(the clause's number), and the walk's own final depth.  `final` and `walk_final`
are the same value by two arithmetics, and the gate requires them equal; `final`
and `sum` are signed and are read back as such, so a document whose prefix depth
goes negative reports the negative number.

The document window is the one buffer the adapter does not copy.  Every unit's
document parameter is `const`, so the object only reads it; the adapter hands the
caller's bytes over and checks, before the call, that the window carries the
document's whole last 64-byte block (`PC_WINDOW_BLOCKS`), which is what the mask
unit reads unconditionally.  The other thirteen buffers are written by the
object, so they keep their own allocations, and the window is neither freed nor
written by the adapter.

Two properties are the point:

- **No clamping.**  A cursor larger than its capacity means the object stored
  past a buffer.  The cursor is checked before a byte is copied out, and the
  result is an internal contract violation; a clamped cursor would present the
  corruption as a shorter, well-formed observation.  The same reason puts every
  buffer's extent and the capacity arithmetic *before* the call: a check after
  the call cannot repair a store that has already left the buffer.
- **Initialisation is the adapter's setup, not the caller's obligation.**  The
  entry emitter reads the unit's own static POS8 table, so it has to be filled
  before the first call; `route_init` calls `leanllvm_json_entry_table` once per
  process from inside the adapter.  The earlier shape asked the Lean program for
  the table and consumed the call's result, because written as a pure `@[extern]`
  with an unused result the compiler eliminated the call and left the table
  zeroed — every container refused.  A caller cannot observe the table, so the
  obligation belonged here: `route_init` is an ordinary external call with side
  effects this translation unit cannot prove away, and `build.sh` asserts the
  symbol is still imported and defined.

## What this does and does not establish

It establishes that a Lean program reaches the native object, that the staging
it builds is the one the record asks for (by agreement with an independent C
caller), that the object's observation, arena and event stream are the ones the
route prints byte for byte, that the document decision is the library's
certified predicate — the two-phase native decision agreeing with `admission` in
verdict, reason and measured depth on every corpus row, with a control that must
disagree — and that the fast path is taken exactly where it admits, and that
every other document is answered once by the reference parser — with the
reference's reason and byte for the policy class, its `depthExceeded` past 128,
and `input too long` past the bound.
`DomainCheck.lean` additionally proves by elaboration that the shell's decision
is `admission`'s (`documentDecision_admitted`) and that the certificate's clauses
follow from it (`admitted_documentDomain`, `routeSpecPre`).

What the two-phase decision adds beyond that is measured, not proved: the depth
walk, the candidate flag and the native policy scan are new code with no
refinement theorem, the clause-by-clause argument for their equality with
`admission`'s is in `shim.c` and `policy.c`, and `check.sh` observes the equality
on every row it has — including the byte a policy refusal names and the number
the depth clause measures — with the reference's own `policyRefusal` and the
library's own `docDepth` as the oracles beside it in `--admit`.  A document
outside that corpus is decided by the same argument's reasoning and not by an
assertion, which is why the differential sweeps the two-phase section records are
reported as a reading of the scan and not as a proof of it.

It does not establish that the object executes the pinned body the theorems are
about: the refinement theorem speaks about the parsed AST and `Mem`, and the
compiler/FFI step from that to the linked object is the trust boundary
`docs/contract.md` rows 8 and 9 record — `correspondence.sh` records exactly
how far the two emissions are from each other, which is that they are not the
same text.  It does not compare the payload values with the reference tape's
values either: the fast path prints the object's bytes and the fallback prints
its own answer, and the two are compared only where the domain certificate says
they must agree.  The object itself still accepts the fourteen: `Sigma_pipeline`
states the reference parser's predicate, and the object's verdict is the RFC
one, which is why `Sigma_pipeline` remains a statement rather than a theorem
about the linked object.
