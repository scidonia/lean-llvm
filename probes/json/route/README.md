# The JSON pipeline's Lean call route

The review's step D: a Lean program that stages the document the assembled
pipeline's record demands and calls the native object.  The contract is
`LeanLLVM/JsonCallRoute.lean`; this directory is its executable route.

| File | What it is |
|---|---|
| `RouteMain.lean` | the standalone Lean entry point: it imports the library's `admission` decision and its `parseBytes` fallback (one shell, not two), stages the document in the record's shape on the fast path, calls the object through the adapter, and prints one of the three outcomes |
| `shim.c` | the adapter: validates the staging, copies the caller's `ByteArray`s into the object's ABI, fills the entry unit's POS8 table, calls `leanllvm_json_pipeline`, and returns the tagged result |
| `driver.c` | a C caller that stages the document identically and prints the same three lines, for the fidelity comparison |
| `build.sh` | compiles the six kernel units, the adapter and the program, links them (the program's library modules link from their emitted C), and asserts the two symbols the adapter calls are imported and defined |
| `check.sh` | the route scenario: fidelity against `driver.c` on every admitted row, each fallback answer against the manifest, the empty/over-bound/opener-rich documents, the depth boundary, the fourteen-row policy class, and the three outcomes' distinctness |
| `bench.sh` | the route's per-stage timings, the object's -O2/-O3 pair taken paired against a drift control, the fallback's price, and the simdjson reference arm; the record is [the stage timings page](../../../docs/json-route-stage-timings.md) |
| `bench/simdjson-baseline.cc` | the reference arm: simdjson 4.6.11 on-demand over the same documents, its `padded_string` staging and its `iterate` plus full value traversal timed apart |
| `correspondence.sh` | the stage-2 artifact correspondence: the flags, the derivation steps, which bodies are identical under the transform, and what is left over |
| `DomainCheck.lean` | the library shell's `documentDecision` and `checkRoute`, elaborated from source: every admission clause on both sides, both fallback outcomes, the fourteen-row policy class, and the layout checks |

## The three outcomes

The decision is the library's, `LeanLLVM.JsonKernelDomain.admission`, and its
clauses are the certified checkers whose certificates are in
`LeanLLVM/JsonKernelCertificate.lean`.  A document takes exactly one of three
paths, and the output distinguishes them:

* **the fast path** (`verdict=...` on stdout).  `admission` admits the document,
  the program stages it, and the native object answers; the observation, the
  arena and the event stream are printed.  This is the only path that calls the
  object.
* **the fallback's refusal** (`refused: ...` on stderr, exit 2).  `admission`
  does not admit the document and the scalar reference parser refuses it; the
  reason and position printed are `parseBytes`'s own.
* **the fallback's acceptance** (`fallback=accepted tokens=<n> decoded=<0|1>`).
  `admission` does not admit the document and the reference parser accepts it;
  the tape is the answer, and `decoded` reports whether `decodeTape` gave a
  value.

The fallback is the reference parser for every document the domain does not
admit, and for no other document: it is not consulted before the decision and
not on the fast path.  The domain is exactly what the certified checkers decide,
so the open/closed question of the fast path's totality is a question about
those clauses and nothing else.

## Commands

```bash
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonKernelDomain LeanLLVM.JSON.Parse
nix develop -c bash probes/json/route/build.sh
nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/correspondence.sh
bash probes/json/route/bench.sh 21        # re-executes itself under a 6 GiB scope
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonCallRoute
nix develop -c bash probes/install/lake-locked.sh env lean probes/json/route/DomainCheck.lean
```

`build.sh` prints `ok: .../leanllvm-json-route`; it fails if `nm` does not show
`leanllvm_json_pipeline` and `leanllvm_json_entry_table` imported by the adapter
and defined by the executable, so a build that lost the call or the table's
initialisation is a red rather than a pass.  It compiles the program with
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

## Observed

`check.sh`, over the 122 default-profile manifest rows and then the boundary
cases:

```text
ok: 122 default-profile rows: 107 fast-path row(s) agree with the driver on the observation, arena and events (22 arena byte(s) over 9 row(s), 1125 event byte(s) over 69 row(s)); fast path accept 59, invalid 48; fallback refusals 14, fallback accepts 0; divergence 0; empty excluded 1; 8 non-default-profile rows skipped; depth 128 fast, 129/520/521 fall back with depthExceeded; 14 policy rows fall back with the reference reasons
```

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
- the opener-rich document — a string carrying 129 `[` bytes — is accepted by
  the reference and outside the domain, because the opener-count clause counts
  bytes rather than nesting.  It falls back and the fallback accepts it with a
  decoded value: the clause's conservatism narrows the domain and never changes
  an answer.

The byte comparison is not vacuous: the run counts the bytes it compared and the
rows that carried any, and fails when either arm is empty.  Every assertion above
has a cut that makes it fail; the cuts and their observed output are recorded
below.

## The controls

Four cuts, each applied to the probe's shell (`RouteMain.run`) in a throwaway
copy and rebuilt, one at a time; the tree was restored and rebuilt after each,
and the final run above is the restored build's.  The cut is at the decision's
*consumer* rather than in `admission` itself because the clause definitions carry
the certificate's proofs: removing a clause there replaces a proof, which is a
build failure rather than an assertion failure, and the point of these controls
is that the scenario notices a document taking the wrong path.

| Control | Cut | First observed red |
|---|---|---|
| depth-129 falls back | `.error (.depthBound _) => runFast …` | `FAIL: depth 129: expected the fallback's depthExceeded refusal (exit 0)` (and 520, 521, the opener-rich document) |
| a policy-violating document falls back | `.error (.unpairedSurrogate _) \| .error (.noncharacter _) => runFast …` | `FAIL: the fallback refuses a different policy class than the one pinned`, `FAIL: expected 14 policy refusals, saw 0`, and the fourteen rows counted as divergences |
| over-length falls back | `.error (.inputTooLong _) => runFast …` | `FAIL: the over-bound document was not the fallback's refusal (exit 0)` |
| a policy-clean in-domain document takes the fast path | `.ok () => … runFallback doc` (with `runFast` still referenced from a branch that is not taken, so the link step keeps the call) | `FAIL: the fast-path arm is empty (accept 0, invalid 0)`, `FAIL: no compared row carried arena bytes…`, and the depth-128 row losing its observation |

The first attempt at the last cut — routing *all* documents to the fallback —
failed the build instead (`build: the executable does not define
leanllvm_json_pipeline`), because Lean's compiler eliminated the unused extern
call; that is a scaffolding failure, not a red, which is why the recorded cut
keeps a live reference to `runFast`.

## The fallback, and where it could differ

There is no second policy scan in the probe any more.  `RouteMain.lean` imports
`admission` and `parseBytes` from the library, so the decision and the
fallback's answer are the reference's own compiled definitions, not a
transcription: `DomainCheck.lean` pins the class against the parser itself, and
`check.sh` pins the executable's reason and byte for all fourteen rows.

The one limitation is the one the clause's own docstring states: the depth
clause is an opener *count*, so it is conservative.  A balanced document whose
string bodies carry more than 128 `[`/`{` bytes is refused by `admission` and
answered by the fallback — never wrongly, because the fallback is the reference
parser, and `check.sh` asserts exactly that case.  Replacing the count with the
stage-1 depth counter is a deletion of one clause and its certificate, not a
renegotiation of this shell.

## The adapter's tagged result, and why nothing is clamped

`shim.c` returns ten header words and then the payloads: `tag detail want got`,
then `verdict nk nxp ndst nev err`.  The tag names the class — the object ran
and accepted, the object ran and refused, a staging precondition failed before
the call, a staging copy could not be allocated, or a returned cursor exceeded
its capacity — and `detail`/`want`/`got` name the failing check with its
expected and observed numbers.  `RouteMain.lean` prints the observation for the
first two classes as before, and reports the last three on stderr at exit 3, 4
and 5.

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
certified predicate and the fast path is taken exactly where it admits, and that
every other document is answered once by the reference parser — with the
reference's reason and byte for the policy class, its `depthExceeded` past 128,
`input too long` past the bound, and its accepted tape for the opener-rich
document.  `DomainCheck.lean` additionally proves by elaboration that the
shell's decision is `admission`'s (`documentDecision_admitted`) and that the
certificate's clauses follow from it (`admitted_documentDomain`,
`routeSpecPre`).

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
