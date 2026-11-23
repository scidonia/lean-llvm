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
- **Given:** the base revision `66159e24b93d7f78139d08a8d1794f32ae12e777` and
  the protected set `kernel/json/stage2.c`, `kernel/json/stage2.h`,
  `kernel/json/pipeline.c`, `kernel/json/pipeline.h`,
  `probes/install/ir/stage2.candidate.ll`,
  `probes/install/ir/json-pipeline.candidate.ll` and the shipped route's build
  list `probes/json/route/build.sh`.
- **When:** the check compares each path's bytes with the base blob, and runs
  `kernel/json/identity/source-identity.sh --unit stage2 --arms-only` and
  `--unit pipeline --arms-only`.
- **Then:** no byte of the protected set differs, and both identity arms exit 0
  with `ok: the unit defines exactly its one ABI symbol` and
  `ok: source identity holds (<unit>)`.  The detector's positive control is a
  throwaway copy of `kernel/json/stage2.c` with one byte changed: it must fail
  the same comparison, and an unchanged copy must pass it.
- **Why:** the additive entry is only additive if the shipped route's bytes and
  its two one-symbol censuses are untouched; the comparison passes trivially at
  the pre-start state, so the one-byte control is what shows the detector can
  fail.

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

## The red, as observed

Each cut was applied to a throwaway copy of the tree (rsync without `.lake`,
with the worktree's `.git` pointer) and the route was run there with the
command above.  Every cut tree compiled: a compile failure would have stopped
the route before its assertion and would not have counted.  The uncut control
in the same command reached exit 0 with every `ok` line.

| Cut | Build | Scenario | Firing assertion |
|---|---|---|---|
| NE1: `terms += (uint64_t)(t) + (uint64_t)(ol)` (the record payload omitted) | exit 0 | exit 1 | `FAIL: the driver exited 3 on the stage2/list route/arm`, then `FAIL … reading: reference 1/1/9223372036854775818, no-event 1/1/9` on `acc-string`, `acc-utf8-raw` and nine further accepted record-bearing documents; number-only rows and every refusing row stay green |
| NE2 A: `xp, *nxp` replaced by `xp, 0` in the stage-2 tail | exit 0 | exit 1 | `FAIL: the driver exited 3 on the pipeline/list route/arm`, then `FAIL … reading: pipeline 1/1/214, no-event 1/1/9223372036854775819` on `acc-esc-string` and the other escape-bearing documents; no `nk:` or `nxp:` line fires, and every escape-free row stays green |
| NE2 B: the entry's three pre-zero stores deleted (deviation 11) | exit 0 | exit 1 | `FAIL: the driver exited 3 on the pipeline/list route/arm`, then `FAIL … refusal slots: expected zero, got 16045690984833335023/16045690984833335023/16045690984833335023` on `refuse-utf8-gate` only; every accepting row and every walk refusal stays green |
| NE3: the three refusal stores deleted | exit 0 | exit 1 | `FAIL: the driver exited 3 on the stage2/list route/arm`, then `FAIL … refusal slots: expected zero, got 16045690984833335023/16045690984833335023/16045690984833335023`; every accepting row stays green |
| NE4: one byte of `kernel/json/stage2.c` changed (a comment line appended) | exit 0 | exit 1 | `kernel/json/stage2.c differs from 66159e24…`, `FAIL: a protected artefact differs from the base revision` |
| NE6: a stage-1 reference appended to `stage2_noevent.c` | exit 0 | exit 1 | the census prints `leanllvm_json_escape_expand` and `leanllvm_json_s1_masks` among the undefined project symbols, then `FAIL: the no-event object's symbol census is not the declared one` |

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
