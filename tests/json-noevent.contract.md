# No-event entry routes

`kernel/json/stage2_noevent.c` is an additive stage-2 entry: it walks the same
entry stream `kernel/json/stage2.h` describes, validates the same grammar and
string bodies with the certified unit's own helper text, and writes no event
record and no arena.  It reports the reading the unchanged consumer
(`probes/json/route/cost-profile/cost-profile.c`'s `fold_result`, build mode)
makes of the certified route's event stream and arena, in three output slots.

`kernel/json/pipeline_noevent.c` is the assembled pipeline built on it: it
keeps `kernel/json/pipeline.c`'s stage-1 block loop, entry emitter, escape list
and UTF-8 document-level verdict text unchanged, replaces the destination and
event triplets with one caller-staged scratch buffer, and calls the entry
above for its stage-2 walk.  It writes the three reading slots, `nk` and
`nxp`; it writes no arena and no event stream.  The three slots are pure
outputs and are zeroed at entry, before the block loop, so a refusal from
either the UTF-8 gate (which returns before the tail) or the walk leaves zero
in all three.

The route compares the additive entries with the certified route through an
external process, `probes/json/noevent_driver.c`, at two boundaries:

    nix develop -c bash tests/json-noevent/check.sh

At `--route stage2` (the default) the driver calls
`leanllvm_json_pipeline` for the entry stream and the escape list only, then
calls both stage-2 entries on the same stage-1 output, so the comparison is at
the stage-2 boundary.  At `--route pipeline` each side runs its own stage 1:
`leanllvm_json_pipeline` followed by the unchanged fold against
`leanllvm_json_pipeline_noevent`, so the entry stream's cursor `nk` and the
escape list's count `nxp` are compared as well as the verdict, the refusal
offset and the reading.  `--arm list` supplies the pipeline's escape list to
both sides; `--arm nolist` passes `nxp = 0` to both sides and is confined to
documents that carry no backslash and no control byte inside a string; the
plain form admits such a byte, so the arm's domain is stated and the corpus
keeps those documents `list`-only.  One row per document:

    <path>  <accept|refuse>  <1|0>  <err|->  <tokens|->  <values|->  <sum|->

At the pipeline boundary the row carries two more columns, `nk` and `nxp`.

A row is emitted only when both sides agree.  A disagreement is a `FAIL` line
carrying both readings, and the process exits 3; exit 2 is a setup fault (an
unreadable document, a backslash in the no-list arm, a consumer fold that did
not walk the event stream).

## The corpus

`tests/json-noevent/corpus` holds 69 documents, `corpus/manifest.tsv` with
one expected row per document, `spec.tsv` recording the arms, refusal class and
(for a copy) repository origin of 63 documents (the six seeded whitespace
documents come from `seed`, not `spec.tsv`), `generate.sh`, and `seed` holding
the fixed seed `20261123`.

The manifest's columns are the document path, its arms (`both`, `list` or
`pipeline`), its class, its verdict, the refusal offset, `tokens`, `values`,
the sum as 16 lowercase hex digits, the document's SHA-256, and its origin (or
`-`).  `both` runs in both arms of both routes; `list` carries an escape or a
control byte and runs in the `list` arm of both routes; `pipeline` is the UTF-8
stage's document-level refusal, which stage 2 never sees, and runs in both
pipeline arms only.  The check verifies every document's digest against the
manifest and the document set against the manifest's, then runs `generate.sh`
into a temporary directory and requires the documents and the manifest to be
reproduced byte for byte.  A copied document's digest was verified against its
origin when the generator wrote it, and the manifest pins that digest; the
check re-verifies the copy.

Composition: 37 accepted documents and 32 refusing documents.  The stage-2
route runs 68 documents: 54 in both arms and 14 (the escape- or control-bearing
ones) in the `list` arm only.  The pipeline route runs those 68 plus the one
`pipeline`-arm document in both of its arms, so 69 documents in `list` and 55
in `nolist`.  The accepted set covers the three literals, numbers (including
`-0`, `-1` and arrays), plain strings and keys, nested containers, whitespace
variation, a plain string carrying a valid raw multi-byte UTF-8 body
(`acc-utf8-raw`), and escaped bodies (`\n`, `\"`, `\u00e9`, a surrogate pair),
with the escaped-body arms ordering plain and escaped bodies both ways.  The
refusing set covers every class `kernel/json/stage2.h` names — the structural,
number, literal and string-body rules and the end-of-stream rules `unclosed`,
`no-value` and `unterminated` (8 literal, 5 number, 5 unclosed, 5 structural, 3
string-body, 3 unterminated, 2 no-value) — including the literal pathologies
`tru`, `truth`, `truE`, `nul`, `nullx`, `fals`, `falsey`, a valid literal
whose last byte is the document's (`[true`, refused at the document end), and
the trailing-comma structural refusals `{"a":1,}` (offset 7) and `[1,]`
(offset 3).  One
further document, `refuse-utf8-gate`, is the pipeline level's own class: a
string whose body is the invalid two-byte `C0 AF` sequence, refused by the
UTF-8 stage at the document's end (offset `n` = 4).  `acc-utf8-raw` is its
affirmative control, so the gate is shown to distinguish a valid sequence from
an invalid one rather than merely to refuse.  Fourteen documents are copied
from `tests/json/corpus` and `tests/json-adv/corpus` so the route is exercised
over the repository's own fixtures.  Six documents are the seeded whitespace
family: `[` with seed-derived gaps around `1`, each distinguished by its
leading gap.

An accepted document's reading is derived by `generate.sh` from the document's
own bytes and the encoding `kernel/json/stage2.h` states.  The raw multi-byte
body of `acc-utf8-raw` is a plain string span, so it contributes a span record
and no arena bytes; the invalid `refuse-utf8-gate` document's offset is the
generator's own byte count of the document it writes.  The generator's
numbers are looked up by exact lexeme in a pinned table, so a document that
introduces a number the table does not carry is refused by the generator rather
than read with a guessed bit pattern.  Every accepted document's exact sum is
below `2 ^ 64`: the corpus keeps at most one plain (unescaped) key or string per
accepted document, at most one number beside it (two when it has no plain
record), and no payload whose pattern would push the sum past the word; the
generator accumulates in two 32-bit limbs and fails on a document whose exact
sum reaches `2 ^ 64`, so the bound is enforced and not merely intended.

## NE1 — the new entry agrees with the certified entry and the unchanged fold

- **Actor:** `probes/json/noevent_driver.c`, run as an external process over
  the committed corpus.
- **Given:** the corpus's 68 stage-2-route documents, the manifest's pins, the
  stage-2 route's two arms, and the kernel objects compiled from
  `kernel/json/{s1_block,entry,utf8,escape,stage2,pipeline,stage2_noevent,
  pipeline_noevent}.c` at the measured compiler line
  (`-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
  -falign-functions=64`).
- **When:** the operator runs `tests/json-noevent/check.sh`.  It runs the
  driver once per arm and compares every row, in corpus order, with the
  manifest's pinned row.
- **Then:** on each arm the driver exits 0, writes nothing to stderr, and
  prints exactly one row per arm document; every row's verdict matches the
  manifest's; an accepted row carries the manifest's `tokens`, `values` and sum
  (compared as the 16-hex-digit word), and `values` equals `tokens`; a refusing
  row carries the manifest's offset and `-` in all three reading columns.
- **Why:** the row is the externally observable agreement of the two entries at
  the C ABI, and the manifest is a fixture pinned independently of the driver
  (the generator derives the accepted readings from the encoding, never by
  running the driver).  The check's own defect object removes the record
  payload from the sum accumulator; it must redden the accepted string-bearing
  rows, leave every refusing row and every number-only row green, and exit 3 —
  so the comparison is shown to notice a wrong arithmetic and to notice it in
  one assertion family.

## NE2 — the pipeline entry agrees end to end, stage 1 included

- **Actor:** `probes/json/noevent_driver.c --route pipeline`, run as an
  external process over the committed corpus.
- **Given:** the corpus's 69 documents (the 68 stage-2 documents plus
  `refuse-utf8-gate`), the manifest's pins, both pipeline arms, and the kernel
  objects at the measured compiler line.  Each side runs its own stage 1: the
  reference is `leanllvm_json_pipeline` followed by the unchanged fold, the
  subject is `leanllvm_json_pipeline_noevent`.
- **When:** the operator runs `tests/json-noevent/check.sh`.  It runs the
  driver under `--route pipeline` once per arm and compares every row, in
  corpus order, with the manifest's pinned row; the driver compares `nk` and
  `nxp` between the two entries and emits a row only when they agree.
- **Then:** on each arm the driver exits 0, writes nothing to stderr, and
  prints exactly one row per arm document with nine columns: the verdict, the
  refusal offset, the three readings as in NE1, then `nk` and `nxp`.  An
  accepted row carries the manifest's `tokens`, `values` and sum; a refusing
  row carries the manifest's offset and `-` readings.  `nxp` is zero in the
  `nolist` arm (the arm clears the escape-list bit on both sides) and positive
  for every escape-bearing (`list`-arm) document in the `list` arm; `nk` and
  `nxp` are decimal words.  A refusal from either class — the UTF-8 gate's
  document-level one (`refuse-utf8-gate`, offset `n` = 4) or the walk's — leaves
  zero in all three sentinel-prefilled slots.
- **Why:** the pipeline entry is not the stage-2 entry with a different caller:
  it owns the entry stream's cursor and the escape list's count, and a defect
  in either stage-1 output would be invisible at the stage-2 boundary, where
  both entries are handed the same stage-1 output.  The check's own defect
  objects show the boundary biting: passing `nxp = 0` to the stage-2 tail
  leaves `nk` and `nxp` agreeing while an accepted escape-bearing document's
  reading moves, and deleting the entry's pre-zero leaves the sentinel on the
  UTF-8 gate's refusal.  The corpus's valid and invalid raw multi-byte bodies
  pin the gate's affirmative and negative controls.

## NE3 — the refusal slots and the first-error offset

- **Actor:** the same driver, with the three reading slots pre-filled with
  `0xDEADBEEFDEADBEEF` before each call.
- **Given:** at least one document in every refusal class `stage2.h` names; the
  driver pre-fills the slots and prints `FAIL … refusal slots: expected zero`
  when a refusal leaves them untouched.
- **When:** the check runs the corpus in both arms and reads the refused rows,
  then runs the defect object below.
- **Then:** every refused document's row carries the certified entry's offset
  (the driver compares the two entries' `*err` directly, and the manifest pins
  the same offset) and `-` in all three reading columns; that the entry wrote
  the declared zeros is observed by the driver's sentinel check — exit 0 and no
  `FAIL … refusal slots` line — which the defect object below shows firing.
  The defect object deletes the three stores and must print
  `got 16045690984833335023/16045690984833335023/16045690984833335023` — the
  sentinel — on refusing documents, exit 3, and leave every accepting row
  unchanged.
- **Why:** a sentinel pre-fill is what separates "the entry wrote the declared
  zeros" from "the entry never touched the slot"; the two are indistinguishable
  in a zero-initialised buffer.  The offset comparison and the pinned offsets
  make the refusal half observable at the same boundary as the accepted half.

## NE6 — the object's dependency census

- **Actor:** the check, over the object built from
  `kernel/json/stage2_noevent.c` at the measured compiler line.
- **Given:** `nm` on that object.
- **When:** the check reads the defined global symbols and the undefined
  project symbols (names beginning `leanllvm_json_`).
- **Then:** the defined globals are exactly
  `leanllvm_json_stage2_noevent` and `leanllvm_json_stage2_noevent_lib`, and
  the undefined project set is exactly `leanllvm_json_escape_expand`.  The
  census control appends a `static`, `used` reference to the stage-1 symbol
  `leanllvm_json_s1_masks` to a copy of the source and compiles it: the object
  builds, its defined-global set is unchanged, and the same census reports the
  widened undefined set and fails.
- **Why:** the entry may depend on the escape unit the certified unit itself
  calls and on nothing else of the project's; a stage-1 or stage-2 ABI symbol
  appearing there would make the unit part of a different link.

## NE4 — the current ABI is byte-identical at the base

- **Actor:** the check, with `git` and the two source-identity arms.
- **Given:** the base revision `66159e24b93d7f78139d08a8d1794f32ae12e777`,
  the certification revision rather than the branch tip, and the protected set
  `kernel/json/stage2.c`, `kernel/json/stage2.h`,
  `kernel/json/pipeline.c`, `kernel/json/pipeline.h`,
  `probes/install/ir/stage2.candidate.ll` and
  `probes/install/ir/json-pipeline.candidate.ll`.
- **When:** the check compares each path's bytes with the base blob, and runs
  `kernel/json/identity/source-identity.sh --unit stage2 --arms-only` and
  `--unit pipeline --arms-only`.
- **Then:** no byte of the protected set differs, and both identity arms exit 0
  with `ok: the unit defines exactly its one ABI symbol` and
  `ok: source identity holds (<unit>)`.  The detector's positive control is a
  throwaway copy of `kernel/json/stage2.c` with one byte changed: it must fail
  the same comparison, and an unchanged copy must pass it.
- **Why:** the additive entry is only additive if the shipped route's ABI
  artefacts and its two one-symbol censuses are untouched; the comparison
  passes trivially at the pre-start state, so the one-byte control is what
  shows the detector can fail.  The protected set is exactly those six ABI
  artefacts.  The shipped route's build list, `probes/json/route/build.sh`, is
  not compared: that clause was superseded rather than narrowed to fit a
  change.  The build list selects sources and flags and protects no ABI byte,
  and the coverage it stood for now belongs to NE8, which holds the event arm
  byte-identical per document to the base binary, together with the build
  list's own `nm` assertions over the assembled link.  The one-byte identity
  control remains this scenario's evidence that the comparison can fail.

## NE5 — the model's relation-level pair, with its controls

- **Actor:** the Lean check `tests/json-noevent.lean`, elaborated against
  `LeanLLVM`'s public interface.  No C process, compiler, service, clock or
  network is reached.
- **Given:** the model's own vocabulary — `Stage2NoEvent`, `noEventFold`, and the
  two documents `nullDoc` and `trueDoc`.
- **When:** the operator runs
  `nix develop -c lake env lean tests/json-noevent.lean`.
- **Then:** `nullDoc_noEvent` and `trueDoc_noEvent` establish the relation at the
  empty arena for the two documents; five `#guard`s give each fold's token count,
  its sum, and the inequality of the two readings; the arena-load-bearing control
  shows the fold reading its arena argument rather than ignoring it; and the
  distinct-documents control shows the two witnesses are not one input counted
  twice.
- **Why:** the relation is what the boundary record's accepted arm states, so the
  pair and its controls pin the model's own vocabulary.  That either document's
  run presents the view the obstruction's fixed literal names is the current ABI
  post's claim, exercised by the differential — this file does not establish it,
  and the model has no refusal relation from which a refusal witness could be
  taken.

## NE7 — the route's no-event arm agrees with its C caller and the certified event arm

- **Actor:** `probes/json/route/build/leanllvm-json-route --consume-noevent` and
  `probes/json/route/build/driver --noevent`, as external processes over the
  committed corpus; the same route binary on the certified event arm (`--doc`
  and `--consume-events`; `--arm events --consume` names the same arm) is the
  reference for the words the arm reports.
- **Given:** the 69 documents of `tests/json-noevent/corpus` (the corpus NE1–NE6
  read, so the two boundaries share one domain and its refusal classes), the
  manifest's verdicts and refusal offsets, and the route's build artefacts.  The
  route binary and the C caller are the build step's outputs
  (`nix develop -c bash probes/json/route/build.sh`); an absent one is a setup
  fault that names that command, not an assertion result.
- **When:** the operator runs `tests/json-noevent/check.sh`.  For every document
  it runs the route's no-event arm, the C caller's no-event arm, the event arm's
  consumer read (`--consume-events`) and the event arm's observation (`--doc`),
  and compares the lines.
- **Then:** the arm is entered on the 68 documents the admission admits (the
  empty document is the one it does not enter; the C caller refuses that
  document at its own entry with exit 2 and `refused: empty input`).  On each
  admitted document the route exits 0 and prints one `reading` line, the C
  caller exits 0 with empty stderr and prints the identical line, character for
  character, and that line's `verdict`, `nk`, `nxp` and `err` equal the event
  arm's observation of the same document.  On an acceptance the line's
  `tokens`, `values` and `sum` equal the event arm's consumer reading of the
  event stream and arena (`tokens`, `values`, `foldsum`), `tokens` and `values`
  agree and are non-zero, and the event arm's two readings agree with each
  other.  On a refusal the line's three words are zero, and `err` is the
  certified offset — the event arm's own `err` and the manifest's pinned
  offset — while the event arm's consumer may still read the prefix events a
  walk refusal left behind, which is why the reading equality is an
  acceptance's.  The verdict word agrees with the manifest's verdict.
- **Why:** the three actors are independent implementations of one reading: the
  shipped route's adapter, the C caller, and the certified event arm plus its
  unchanged consumer fold.  The event arm is the reference rather than a fourth
  opinion, so a shared mistake between the additive arm and the C caller would
  still be visible.  A staged cut that wires the arm's reading to zeros leaves
  the event arm untouched (NE8 stays green) and makes the route refuse its own
  reading at exit 5 on the first acceptance (`an acceptance's reading is
  tokens=0 values=0`); a cut that offsets the arm's count keeps exit 0 and
  fires this comparison instead.  Both are built from a copy of `shim.c` in a
  throwaway tree, so nothing in the working tree moves.

## NE8 — the certified event arm is unchanged

- **Actor:** the same route binary on its event arm (`--doc <file>`), as an
  external process.
- **Given:** `tests/json-noevent/base-event-rows.tsv`, which records the base
  revision `691ca12dc1b6afa8e05ff5828003fdadd15c9c1c`, the base binary's
  SHA-256 `86fbb06b3ab8d498e7edc73ee49abae5484ac66f1f12b9345aa2cbf5ac901e40`,
  and one row per document the base route answered on that arm: the document's
  repository path, its exit word, the six observation words, the SHA-256 of the
  decoded arena payload, the SHA-256 of the decoded event payload, the
  document's SHA-256, and the SHA-256 of the base route's whole stdout.
- **When:** the operator runs `tests/json-noevent/check.sh`.  It reads the
  artifact's provenance lines, requires its 183 rows and their document set to
  be intact, then runs the event arm on every row's document and compares it
  with the row.
- **Then:** every document's current digest is the row's; the event arm exits
  with the row's exit word; its whole stdout hashes to the row's stdout digest;
  its observation line is the row's six words exactly; and the arena and event
  payload lines decode to bytes whose SHA-256 equal the row's payload digests.
  The rows are the corpus for this scenario: a document the base route answered
  is compared, and no expectation is invented for a document outside them.
- **Why:** the no-event arm is additive only if the certified arm's bytes do not
  move.  The base rows pin the arm's externally visible output per document,
  including both payloads, so a change to the object's event stream, the
  adapter's header, or the route's report is a red at the document that carries
  it.  The record's cut changes the event arm's own `nev` word in the printed
  observation (a copy of `RouteMain.lean` in a throwaway tree): NE8 fires on
  that document's observation line and its stdout digest, while NE7 stays
  green because the no-event arm and its reference reading do not read that
  word.

## NE9 — the gap model's case table

- **Actor:** the Lean check `tests/json-noevent.lean`, elaborated against
  `LeanLLVM`'s public interface.  No C process, compiler, service, clock or
  network is reached.
- **Given:** `gapRecoverWrite`, the rule `od_gap_recover`'s text states over the
  document window `[0, ip)` and the token's `pos`: no write when the first loop
  reaches `ip`, and otherwise the first-byte decision — a refused number at
  `pos + ei` with tag `gapTagNumber`, a refused literal at `pos + ei` with
  `gapTagLiteral`, a non-scalar refusal at `pos` with `gapTagScalar`, and the
  last site's second-token refusal at `s2` with `gapTagExtra`.  Also
  `gapAfterLoop`, the same decision taken at an already-computed `ee`, and the
  six witness windows `"true"`, `"1e x"`, `"tru x"`, `"[ x"`, `"12 3"` and
  `"true "`.
- **When:** the operator runs
  `nix develop -c lake env lean tests/json-noevent.lean`.
- **Then:** each of the six rows answers the text's offset and tag: no write for
  `"true"` at `ip = 4`, `pos = 0`; the number tag at `2` for `"1e x"` (`4`,
  `0`); the literal tag at `3` for `"tru x"` (`4`, `0`); the scalar tag at `0`
  for `"[ x"` (`3`, `0`); the extra-token tag at `3` for `"12 3"` (`4`, `0`);
  and the extra-token tag at `5` — `ip` itself — for `"true "` (`5`, `0`), whose
  gap is trailing whitespace.  The `ee == ip` control takes the no-write row's
  `ee` through `gapAfterLoop` and gets the extra-token refusal at `4`, so the
  guard changes the answer rather than restating it.  The mutation control
  guards the last site with `off = ip` — the guarded transcription the text does
  not have — and the five other rows keep the rule's answers while `"true "`
  answers no write, so the row that pins the unconditional write fails against
  the mutation.
- **Expected failure:** a logged judgment.  The rule is a new definition, so
  there is no revision at which these assertions existed and failed; no staged
  cut is claimed as a red.  The evidence is the table's mutation control, which
  elaborates on every run and fails `"true "` against the guarded transcription,
  and the build of the module the check reads
  (`nix develop -c lake build LeanLLVMTest`).
- **Why:** `od_gap_recover` overwrites its refusal record, so the observable at
  the call boundary is the last site the text reaches.  The state that
  distinguishes the text's rule from a guarded transcription — a valid token
  whose gap is trailing whitespace, written at `ip` — is not on either caller's
  path: each caller re-validates the same segment and refuses before `err_set`
  (the certified unit's `od_scalar_value` guard and the no-event caller's own
  scalar block), so the differential cannot reach it.  The case table is where
  that state is pinned.
- **Not claimed:** that the compiled object executes the rule — the pin ties the
  rule to `kernel/json/stage2.c`'s lines, and the transcription-to-instructions
  distance is `docs/contract.md` §7.6's trust row.

## NE10 — the literal chain's case table

- **Actor:** the Lean check `tests/json-noevent.lean`, elaborated against
  `LeanLLVM`'s public interface.  No C process, compiler, service, clock or
  network is reached.
- **Given:** `neLitCheck`, the rule the emitted literal compare computes — the
  first differing byte's offset, the token's length when it ends inside the
  literal, and the literal's width when the token runs past it — the three packed
  immediates `neLitTrue`/`neLitFalse`/`neLitNull`, and `stage2NoEventLitChain_run`,
  the body statement that from `if.end519` the pinned chain reaches
  `if.then527` with the rule's offset, or `if.end545` with `none`, and writes
  nothing.  The rule's identity with the certified `lit_check` is
  `neLitCheck_eq_litCheck`.  The token is the document window the chain reads,
  `n = ee - idx` bytes from the literal's start, so a refusing row's value is
  the C text's `pos + ei`.
- **When:** the operator runs
  `nix develop -c lake env lean tests/json-noevent.lean`.
- **Then:** the accepted tokens answer `none`: `true` against `neLitTrue`,
  `false` against `neLitFalse`, and `null` against `neLitNull`.  `tru`, `truth`
  and `truE` answer offset `3` against `true`; `nul` answers `3` against `null`;
  `nullx` answers `4`; `fals` answers `4` against `false`; and `falsey` answers
  `5`.  The literal ending the document, `[true`, carries the complete token
  `true`, which the rule accepts (`none`); the document's refusal at `5` is the
  end-of-stream rule at `n`, the walk's, and this table does not restate it as
  the chain's.  The expected values are load-bearing: a changed immediate in the
  first refusal row (`3` to `4`) is not the rule's answer, so a stale or
  mistranscribed expectation fails its row.  On the fixture side the IR pin's
  own mutant `stage2NoEventSrcMutated` changes one immediate in the body text,
  still parses, and is not `stage2NoEventBody`, so the rows are about the
  committed text and a one-word change bites.
- **Expected failure:** a logged judgment.  The chain's rule is a new definition
  and this table is its first statement, so there is no revision at which these
  assertions existed and failed; no staged cut is claimed as a red.  The
  evidence is the table's mutation control, which elaborates on every run, and
  the build of the module the check reads
  (`nix develop -c lake build LeanLLVMTest`).
- **Why:** the emitted compare is a region of the pinned 167-block body, and its
  offsets are the token-relative `ei` the refusal path later adds to the token's
  position.  The chain is proved as a run to its two exit blocks rather than a
  `Satisfies` at a function (there is no `ret` in the region), and its refusal
  arm states the phi's selection at the entry state rather than the cell, which
  the refusal block itself binds.  The table pins the rule the compare computes,
  separately from the walk that composes the rest of the refusal.
- **Not claimed:** the refusal block's own writes — `%off = ei + %idxprom`, the
  `od_gap_recover` call and the error word — are the walk's, and this table stops
  at the offset the chain leaves.  A complete literal at the document's end is
  accepted by the compare; the document-level refusal at the end-of-stream is
  the walk's rule and is pinned by the differential (NE1/NE2), not here.  That
  the compiled object executes the rule is `docs/contract.md` §7.6's trust row.

## NE11 — the installer certificate

- **Actor:** the installer selector `probes/install/select.sh`, run as its own CLI
  over an isolated manifest, certificate and manifest-named inputs in a private
  temporary directory.  The compiler, linker, symbol tools and proof producer are
  the route's existing local shims; no compiler, linker, proof checker, network
  or clock is reached, and nothing outside the temporary directory is written.
- **Given:** the no-event stage-2 entry's committed fixture
  `probes/install/ir/stage2-noevent.candidate.ll`, whose `define` names the
  exported symbol `leanllvm_json_stage2_noevent`; a manifest that binds the
  unit's object, fixture and marker with their digests, the global comma-mask
  pair for the baseline control, and the unit's own covering theorem and
  contract — `LeanLLVM.Refinement.stage2NoEventWalkObligation_of_staging`,
  whose `#print axioms` pin is
  `[propext, Classical.choice, Quot.sound]`, and
  `LeanLLVM.Refinement.stage2NoEventBoundary`; and a certificate derived from
  those inputs.  The certificate's fields are the producer's seventeen: the
  unit's object, fixture and marker hashes, both operands' object, fixture and
  marker hashes, the covering theorem, the theorem's checked axiom footprint,
  the contract, the target, the data layout and the toolchain revision.
- **When:** the operator runs
  `bash tests/json-noevent-select-gate.sh --strict` (and `--strict-theorem`,
  `--strict-hash`, `--no-body-theorem`, `--fallback-hash` for the four
  refusals).
- **Then:**
  - **a — publication and acceptance.** A strict `noevent` request whose
    certificate carries those fields exits 0, the selection record names
    `noevent`, its `noevent_sha256` is the manifest's and the object's own
    digest, its `proof_sha256` is the certificate's digest, and its `theorem`
    and `contract` are the unit's.  The object handed to the linker is the
    manifest's no-event object, and the published certificate's `axioms` field
    is the covering theorem's pinned footprint.
  - **b — another unit's theorem.** The same request against a certificate whose
    `theorem` names `LeanLLVM.Refinement.CommaMaskIR.IR_refines`, with the
    manifest's digest of the certificate rewritten to the changed bytes, is
    refused with status 1, emits no output, does not record the unit, and the
    refusal's detail names the value used and the unit's theorem.
  - **c — a mismatched object hash.**  The same request against a certificate
    whose `unit_object_sha256` value has been exchanged with its own
    `baseline_object_sha256` value — every hash token still in the file, the
    field-to-file relation broken — is refused with the certificate-invalid
    reason, again after the manifest digest is rewritten.
  - **d — the non-strict fallback.**  The (c) certificate with `STRICT=0` exits
    0, records the baseline, links the baseline object and not the no-event
    object, and records the reason `proof rejected: invalid certificate;
    installed baseline fallback`.
  - **e — the strict gate.**  A manifest that binds only the unconditional
    boundary corollary `LeanLLVM.Refinement.stage2NoEventBoundary_consumer` —
    the statement a unit without the C8 body theorem would have to name — with
    a certificate derived for that manifest, does not offer the strict install:
    the request is refused and the refusal names the unit's required body
    theorem.  The strict install is offered only with the C8 body theorem.
- **Expected failure:** before the unit's certificate and the selector's
  `noevent` branch exist, the strict request is refused as `unknown unit
  noevent`: no certificate is published for the unit, the selection record
  publishes none of the unit's fields, and the refusal modes do not carry the
  certificate-invalid reason or name the field value they used.  Every mode
  fails at its own assertion; a setup fault exits 3 and is never read as one.
- **Why:** the certificate is the installation path's proof of what is being
  installed.  A selector that accepts a unit without a certificate, or a
  certificate that names another unit's statement or another object's hash,
  would install bytes no proof covers.  The negative cases carry the same
  tokens as the valid certificate, and the manifest's outer digest is repaired
  before each, so only the field-to-file relation can decide them.  The gate in
  (e) is what stops a certificate that names only the unconditional boundary
  statement from being read as covering the body.
- **Not claimed:** that the compiled object executes the rule.  The certificate
  binds a hash, a fixture, a theorem and a rebuild; it does not relate the
  object's instructions to the model.  The C8 body theorem's premise tier — the
  dispatch's rows — is a hypothesis, and the gap helper's body faithfulness is
  the `stage2GapRecover` row of `docs/contract.md` §7.6.  The certificate's own
  derivation from the imported proof graph is the end-to-end
  `probes/install/check.sh` route; NE11 observes the selector's decisions on a
  certificate with those fields and the producer's byte-identical output in the
  same run.

## NE12 — the shipped default's dispatch is the no-event arm

- **Actor:** `probes/json/route/build/leanllvm-json-route`, invoked from the
  shell as an external caller over one corpus document,
  `tests/json/corpus/depth-two-ok.json` (the five-event document the route's
  own consumer check stages).
- **Given:** the route binary the build step produces
  (`nix develop -c bash probes/json/route/build.sh`); an absent binary is a
  setup fault naming that command, not an assertion result.
- **When:** the operator runs `tests/json-noevent/check.sh`.  It invokes the
  binary under the shipped default spelling (`--consume`), under the arm's
  spelled-out name (`--consume-noevent`), under the alternate spelling
  (`--arm noevent --consume`), under the certified event arm's alternate
  spelling (`--arm events --consume`) and its own flag (`--consume-events`),
  and under two spellings that name different arms.
- **Then:** `--consume` exits 0 and its stdout is one `reading` line;
  `--consume-noevent` exits 0 and prints the identical line, so the shipped
  default's reading is the no-event arm's; and `--arm noevent --consume` exits
  0 and prints that same line, so the alternate spelling names the same arm.
  `--arm events --consume` exits 0, writes no stdout, and its stderr `row`'s
  `path` is `fast`, its `walked` is 1, and its `path`, `verdict`, `ndst`,
  `nev`, `tokens`, `values`, `walked`, `foldsum` and `valuessum` equal
  `--consume-events`'s row on the same document — while its `tokens` and
  `foldsum` equal the no-event reading's `tokens` and `sum` — so the event
  spelling reaches the certified consumer and reads the same document.  A
  `--arm` word that contradicts the mode's own spelling — `--arm events
  --consume-noevent` and `--arm noevent --consume-events` — exits 1 and prints
  `route: --arm and the mode's spelling name different arms`.
- **Expected failure:** at `f1a739acb6` plain `--consume` is the event arm's
  consumer read: it writes its `row` line to stderr and nothing to stdout,
  `--consume-noevent` is not a mode, and `--arm` is not a word.  The equality
  assertion fires at its own line —
  `FAIL: --consume is not the no-event arm on depth-two-ok.json` — carrying the
  default spelling's empty stdout and the spelled-out name's refusal, rather
  than failing at a setup step.
- **Why:** the default spelling is the arm a caller gets without knowing that
  arms exist.  A reading reached only by the spelled-out name would leave the
  shipped default on the other arm while every explicit row stayed green, and
  the equality between the default's line and the arm's is what observes the
  difference.

## The red, as observed

Each cut was applied to a throwaway copy of the tree (rsync without `.lake`,
with the worktree's `.git` pointer), and each cut tree was rebuilt there with
`probes/json/route/build.sh` before its route ran; no cut reused an earlier
build.
The cut builds require a private `XDG_CACHE_HOME`, because the shared Lake
cache's stamps are pruned under these copies and a build that reuses them stops
before the route.  Every cut tree compiled: a compile failure would have
stopped the route before its assertion and would not have counted.  The uncut
control in the same command reached exit 0 with every `ok` line.

| Cut | Build | Scenario | Firing assertion |
|---|---|---|---|
| NE1: `terms += (uint64_t)(t) + (uint64_t)(ol)` (the record payload omitted) | exit 0 | exit 1 | `FAIL: the driver exited 3 on the stage2/list route/arm`, then `FAIL … reading: reference 1/1/9223372036854775818, no-event 1/1/9` on `acc-string`, `acc-utf8-raw` and nine further accepted record-bearing documents; number-only rows and every refusing row stay green |
| NE2 A: `xp, *nxp` replaced by `xp, 0` in the stage-2 tail | exit 0 | exit 1 | `FAIL: the driver exited 3 on the pipeline/list route/arm`, then `FAIL … reading: pipeline 1/1/214, no-event 1/1/9223372036854775819` on `acc-esc-string` and the other escape-bearing documents; no `nk:` or `nxp:` line fires, and every escape-free row stays green |
| NE2 B: the entry's three pre-zero stores deleted (deviation 11) | exit 0 | exit 1 | `FAIL: the driver exited 3 on the pipeline/list route/arm`, then `FAIL … refusal slots: expected zero, got 16045690984833335023/16045690984833335023/16045690984833335023` on `refuse-utf8-gate` only; every accepting row and every walk refusal stays green |
| NE3: the three refusal stores deleted | exit 0 | exit 1 | `FAIL: the driver exited 3 on the stage2/list route/arm`, then `FAIL … refusal slots: expected zero, got 16045690984833335023/16045690984833335023/16045690984833335023`; every accepting row stays green |
| NE4: one byte of `kernel/json/stage2.c` changed (a comment line appended) | exit 0 | exit 1 | `kernel/json/stage2.c differs from 66159e24…`, `FAIL: a protected artefact differs from the base revision` |
| NE6: a stage-1 reference appended to `stage2_noevent.c` | exit 0 | exit 1 | the census prints `leanllvm_json_escape_expand` and `leanllvm_json_s1_masks` among the undefined project symbols, then `FAIL: the no-event object's symbol census is not the declared one` |
| NE7 zeros: the no-event arm's reading wired to zeros in `shim.c` | exit 0 | exit 1 | `FAIL: --consume-noevent exited 5 on documents/acc-empty-object`, then `route: --consume-noevent: an acceptance's reading is tokens=0 values=0; the two counts must agree and be non-zero` |
| NE7 offset: the arm's `tokens` and `values` each incremented in `shim.c` | exit 0 | exit 1 | `FAIL: the route and the C caller print different readings on documents/acc-empty-object`, then `route: … tokens=3 values=3 …` against `driver: … tokens=2 values=2 …` |
| NE8: the event arm's printed `nev` word changed (a copy of `RouteMain.lean`) | exit 0 | exit 1 | `FAIL: tests/json/corpus/bom.json: the event arm's stdout digest bc50ca33… is not the base row's e6d851f1…` |
| NE12: the route program at `f1a739acb6` (plain `--consume` the event arm's consumer read, no `--consume-noevent` and no `--arm`) in a throwaway copy | exit 0 | exit 1 | `FAIL: --consume is not the no-event arm on depth-two-ok.json`, then `--consume: (exit 0)` with no stdout against `--consume-noevent: (exit 1)`; the rows after the arm's first comparison are not reached |

The two NE7 cuts and the NE8 cut are independent at their own assertions.
Under the NE7 zeros cut the event arm still reproduces all 183 base rows with 0
mismatches, so NE8 does not witness the no-event arm's reading.  Under the NE8
cut the route's no-event arm and the C caller still print one identical reading
on every admitted document, so NE7 is green and only the event arm's frozen
output moves.

The same cuts are built inside the route from copies of the committed sources,
so a green run also exercises each negative control without touching the tree:
the sum cut, the refusal-store cut, the two pipeline cuts and the stage-1
reference are compiled in the temporary directory and their firing assertions
are checked on every run.  The identity control's one byte is changed in a
temporary copy, and the route's own driver arms over the unmodified objects are
the affirmative controls.

## What the route does not claim

The route compares two implementations at each of two boundaries — the stage-2
ABI and the assembled pipeline — over a sampled corpus; it does not prove the
new bodies refine the model, and it says nothing about a document the corpus
does not carry.  The `nolist` arm is the plain span form: a document that
carries a backslash is excluded, and a document carrying a control byte inside
a string is run in the `list` arm only, because the escape list is what carries
the control positions and the plain form accepts them.  The shared corpus gives
one `nxp` shape to both routes, so the pipeline's stage-1 list is sampled by
the same documents; the UTF-8 gate is sampled by one invalid and one valid raw
multi-byte body.  The byte identity covers the listed artefact set only, and
the symbol census is the object's, not the assembled link's.
