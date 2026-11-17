# The native route's artifact boundaries

The artifact a user invokes is `probes/json/route/`: a Lean program
(`RouteMain.lean`), a C adapter (`shim.c`), the six kernel translation units
compiled from `kernel/json/*.c`, the proved stage-1 depth counter
(`tests/v16/depth_count.ll`), and the probe's two policy translation units
(`policy.c`, and `escape_guard.h`'s scan inside the adapter).  This page records
what each of the proofs is *about*, what each object actually is, and where the
distance between the two is a named assumption rather than a theorem.

For every forwarded helper it states whether the correctness theorem covers the
emitted body or a model of the behaviour; it records the fixture-capture
rewrites and the staged ABI, the helper call boundaries and how the installed
object differs from an inlined native build, and the exact implementation each
theorem covers — with hash and rebuild checks identified as identity evidence
rather than as compiler-preservation theorems.

The trust boundary itself is stated at the end, and the route is the only place
in this tree that *executes* the certified bodies; nothing in this page implies
that the Lean compiler, clang, the LLVM backend, the linker or the C library is
verified.  The route's measurements are the stage timings page
(`docs/json-route-stage-timings.md`) and the units harness
(`tests/json-units-bench/`); the semantics of the stage-2 output are
`LeanLLVM/Refinement/JsonStage2Spec.lean`'s relation and the caller's decode in
`LeanLLVM/JsonCallRoute.lean`.

## What is installed, and what the proofs read

Two different artifacts come from one source tree.  The proof layer parses an
emitted-ir *fixture* with `include_str`, pins it to an AST with a compiled
`#guard`, and states its theorem about that AST.  The route compiles the C
source at its own line and installs the object.  The two are the same program
only under the assumptions this page lists.

| Installed object | Source | Route's flags | Build step |
|---|---|---|---|
| `pipeline.o` | `kernel/json/pipeline.c` | `-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64` | `build.sh` |
| `s1_block.o` | `kernel/json/s1_block.c` | the same | `build.sh` |
| `entry.o` | `kernel/json/entry.c` | the same | `build.sh` |
| `escape.o` | `kernel/json/escape.c` | the same | `build.sh` |
| `utf8.o` | `kernel/json/utf8.c` | the same | `build.sh` |
| `stage2.o` | `kernel/json/stage2.c` | the same | `build.sh` |
| `depth_count.o` | `tests/v16/depth_count.ll` | `clang -c` at the install's line | `build.sh` |
| `policy.o` | `probes/json/route/policy.c` | `-O2` + `leanc --print-cflags` | `build.sh` |
| `shim.o` | `probes/json/route/shim.c` | `-O2` + `leanc --print-cflags` | `build.sh` |
| `RouteMain.o` | `probes/json/route/RouteMain.lean` | Lean's compiler (`lake env lean -c`), then `leanc -c` | `build.sh` |

The proofs read:

| Unit | Fixture (`include_str`) | Pinned by | Emission |
|---|---|---|---|
| pipeline | `probes/install/ir/json-pipeline.candidate.ll` | `JsonPipelineIR` | `-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-*` |
| s1 masks | `probes/install/ir/json-s1-masks.candidate.ll` | `JsonS1MasksIR` | the same |
| entry | `probes/install/ir/json-entry.candidate.ll` | `JsonEntryIR` | the same |
| escape | `probes/install/ir/json-escape.candidate.ll` | `JsonEscapeIR` | the same |
| utf8 | `probes/install/ir/json-utf8.candidate.ll` | `JsonUtf8IR` | the same |
| stage 2 | `probes/install/ir/stage2.candidate.ll` | `JsonStage2IR` | the same, plus the transform below |
| depth counter | `tests/v16/depth_count.ll` | `DepthCountRefine` | the installed text *is* the fixture |

The flag relation is the same for all six kernel units and is measured for
stage 2 by `probes/json/route/correspondence.sh`: the codegen token sets are
equal except the optimisation level, and `-fno-discard-value-names` is not an
instruction change.  For the other five the relation is *recorded* — the
capture header's line against `build.sh`'s — and not measured by a script; the
route's `-O2`/`-O3` pair prices the level's performance difference on the same
documents, and no semantic claim rests on the two emissions being equal.

## The stage-2 fixture: rewrites, staged ABI, and what the object does instead

`probes/install/ir/capture-stage2.sh` derives `stage2.candidate.ll` from
`kernel/json/stage2.c` in five recorded steps:

1. the source transform: `noinline` on eleven helpers, `s2_walk` forced inline,
   and the `EL_ENTRY` macro line;
2. `opt -passes=lower-switch`;
3. the token strip (`stage2.strip.tsv`);
4. the eight staging allocas `%d.i %c.i %ctype.i %cst.i %t352.i %s %z %e`
   appended as `ptr` parameters (`stage2.staging.tsv`);
5. three instruction rewrites, and every callee's definition replaced by a
   declaration (`stage2.rewrites.tsv`).

Step 4 is the staged ABI: the body the proofs run takes its stack objects as
parameters, so the walk's contracts are stated at a staging the caller supplies.
The route's object has those objects as stack slots, and the adapter does not
pass them.  The distance is not renamed away: it is the staging's own
assumption, and `docs/contract.md` §7.7 and
`docs/json-route-artifact-correspondence.md` record it.

Step 5 is the helper call boundary: the fixture *declares* the six helpers
`s2_walk` calls and the proof's environment (`stage2SubCalls`) answers them as
contracts.  The correspondence script measures what the installed object does
instead: of the eleven helper bodies, three emit an identical body at `-O2` and
`-O3` under the transform, six differ, and two are not emitted at either level;
the fixture keeps ten helper call sites where both untransformed emissions keep
none.  So the object inlines every helper the fixture leaves out of line, and
the helper contracts are *not* the object's call boundaries.  A statement about
the object's walk therefore needs the helper code's correctness *in place*, not
only at the fixture's calls.

## Per forwarded helper: body or model

Six helpers are forwarded by name from the walk.  The table is
`docs/contract.md` §7.6's, read at the route: **proved (body)** means the
captured `define` block of that helper, pinned to an AST and run at the
contract's staging, satisfies its contract; **assumed (model)** means the
contract is proved of a transcription of the source, and the body-to-model
distance is the trust row.

| Helper | Contract | Basis at the emitted body | What remains |
|---|---|---|---|
| `s2_init` | `s2InitContract` | proved (body): `s2InitBody_run`, `s2InitBody_contract` | body-to-object: ledger row 8 |
| `s2_value_pos` | `s2ValuePosContract` | proved (body): `s2ValuePosBody_contract`, three arms | row 8 |
| `s2_after_value` | `s2AfterValueContract` | proved (body): `s2AfterValueBody_contract`, two arms | row 8 |
| `s2_string_body` | `s2StringBodyContract` | proved (body), under the expander clause | the expander call's decoded bytes are the escape unit's post; the body writes `%outn.i`, `%xj.i` and the error record, four body-allocated objects in no staged region |
| `od_scalar_value` | `s2ScalarValueContract` | assumed (model): body pinned whole, no body-level proof (obstructed) | the number arm's conversion; row 8 |
| `num_fast_el1` | `s2NumFastContract` | assumed (model): body pinned block by block; refusal arm proved of the body, conversion arm open | the numeric correspondence below; at the walk's `Calls` its three callees are `ub`, so the walk-level statement is `NumFastBodyArm`'s |

The six helpers' *caller-side* footprints are `HelperContract.framed`'s, and
`docs/contract.md` §7.6 states the four body-allocated objects (`%ei.i`,
`%root_done.i`, `%xj.i`, `%outn.i`) that a walk invariant's region claim must
name because they are not among the staged objects.

The forwarded helpers that are *not* stage-2's own are the units the pipeline
calls, and the route calls them through the pipeline exactly as `pipeline.c`
does:

| Call in the installed object | Callee's theorem | Basis | Note |
|---|---|---|---|
| `leanllvm_json_s1_masks` | `s1_masks_refines` | proved (body) | six masks and the carry at the body's registers, under the five intrinsics' `Calls`; the intrinsic models are ledger row 4 |
| `leanllvm_json_entry_pos8` / `_b8` | `entry_pos8_refines`, `entry_b8_refines` | proved (body) | the fixture takes the POS8 table as a parameter (`%tab`); the object reads its own `xl_pos8`, filled by `leanllvm_json_entry_table`; the two tables' identity is observed, not proved |
| `leanllvm_json_escape_list` | `JsonEscapeListContract`'s theorem | proved (body) | the position-list body, per block |
| `leanllvm_json_escape_expand` | `escape_expand_satisfies_unconditional` | proved (body) | the expander's decoded bytes and their length bound; called by stage 2 |
| `leanllvm_json_utf8` | `utf8_stage_refines` | proved (body) | the unit's word under its `Calls` |
| `leanllvm_json_stage2` | the stage-2 assembly theorem at `stage2Boundary` | proved (fixture) | see the helper table; the boundary's two arena extents are `ndstU ≤ ndst'` |
| `leanllvm_json_pipeline` | `pipeline_satisfies_at_stage2_of_exitStage2` | proved (fixture) | its post is `pipelineUnitsPost`; the semantic half is `Sigma_pipeline`'s |
| `depth_count` | `depth_count_refines` | proved (body) | the installed text *is* the pinned fixture, so no emission gap |
| `leanllvm_route_body_stop`, `leanllvm_route_policy_scan` | none | assumed (native) | `policy.c` is new code reproducing `policyRefusal`; the agreement is observed (`--admit` and `check.sh`), and it is phase two of the route's decision |
| `leanllvm_json_entry_table` | none | assumed (native) | the table's fill is the entry unit's own `xl_pos8_init`; the object's table is the source of the identity above |

## Numeric operations, and the one approximation

The arena and the event stream are the route's semantic output, and the number
record's payload is the only place an approximation could hide.  The
specification is `strtodSpec` (nearest, ties to even); the emitted conversion is
`num_fast_el1`'s three tiers.

- Tier 1 and tier 2 are IEEE binary64 multiply/divide and the 128-bit kernel;
  tier 3 is the correctly-rounded conversion from a 768-digit window with a
  sticky bit, which replaced the platform `strtod` (the object does not call
  libc's `strtod`; `nm -u stage2.o` shows `memset`, `__memcpy_chk` and
  `__stack_chk_fail` and nothing else).
- `LeanLLVM/StrtodRefine.lean` states the refinement obligation as
  `EmittedConversionRefines`, with the three branches covering the well-formed
  lexemes (`branch_cover`, `branch_disjoint`) and reads it universally at that
  partition.  It proves the *statement's shape*, not the conversion.
  `LeanLLVM/StrtodTier3.lean` models the sticky window and proves the four facts
  the obligation rests on (the 768-digit boundary bound, the sticky bit's
  sufficiency, the magnitude clamps and the rounding), and
  `LeanLLVM/StrtodReader.lean` and `LeanLLVM/ElGuardRefine.lean` carry the
  reader and the exponent guard.  The emitted body's agreement with those
  models, and tiers 1 and 2's arguments, are `NumberArmOwed` — stated and owed,
  not claimed.
- At the walk's `Calls` selection the conversion's three callees are `ub`, so
  the walk-level statement takes `NumFastBodyArm`; a run of the object answers
  them, and that is the numeric trust row, not a theorem.

Everything else in the object is exact integer and lane arithmetic: the masks,
the entry words, the escape positions and bytes, the UTF-8 verdict, the depth
fold and the event records.  The one lane convention that differs from LLVM is
`cttz`'s poison corner (`docs/contract.md` §7.1 item 1), admissible because no
clause reads that lane.

## Fixture normalisation: what was removed

Each unit's capture records its removals per item (`json-{entry,escape,s1-masks,
utf8,pipeline}.{strip,rewrites}.tsv`, `stage2.*.tsv`); the comma-mask pair and
the classifier record theirs by class.  The normalisation is ledger row 5: the
claim that removing those tokens leaves the computed value unchanged is outside
the kernel's reach, and it is per item rather than a proof.  Entry's `nuw`,
`nsw`, `nneg` and `disjoint` are stripped and the widening is recorded as “not
re-established”.  The entry fixture's table becomes its `%tab` parameter
(`json-entry.table.tsv`), which is the rewrite the route's table identity rests
on.

## The caller's side: what the wrapper establishes, and how it decodes

`LeanLLVM/JsonCallRoute.lean` states the wrapper's obligations in the record's
own vocabulary, and the executable establishes them at the pieces that can see
the numbers:

| Obligation | Where it is established |
|---|---|
| the document is inside the certified domain | `documentDecision` / `admission` in the program; `routePre`'s first clause; `documentDecision_admitted` and `admitted_documentDomain` are the proofs |
| presence, capacities, padding | the shell allocates the record's shape (`stage`), each buffer at the record's capacity with the three prefix bytes and the 32-byte readable tail; the adapter checks the same clauses (`shim.c`'s precondition list) and the Lean clauses are `RouteRefusal`'s |
| separation | the adapter owns the addresses, and each staged buffer is its own live allocation held across the call, so the regions are pairwise disjoint by the allocator's disjointness rather than by a runtime comparison; the adapter checks each buffer's extent against its capacity (`shim.c`'s `PC_*` clauses, mirrored by `preconditionName`), and `layoutRefusal` with `layoutRefusal_none` is the Lean form of the same clause list |
| lifetimes | the adapter copies the caller's `ByteArray`s into its own buffers and copies the result out before freeing them; the caller's view (`RouteView`) owns `List UInt8`, so nothing aliases the staging after the call.  This is `shim.c`'s code, not a Lean term |
| cursor bounds and the 64-bit widths | `routePre`'s capacity, cursor-room, document-bound, address-width and signed-cursor clauses; `routePre_of_checkRoute_ok` turns the check into the precondition |

The decode is where the wrapper reads the object's answer, and it is stated
against the proved relation rather than a byte count:

- `decodeRouteCall` reads the adapter's ten-word header, checks the length
  against the two extents, and cuts the arena at the **used** extent and the
  event stream at the **reported cursor**; `decodeRouteCall_bytes` proves it
  recovers the record's own verdict, extents and payloads.
- `decodeRecords` reads the event stream back into the trace: each record's
  first byte names its class and width, so no walk state is needed.
  `decodeRecords_flatten` proves it returns the trace's records.
- `routeView_decodes` composes the two with the relation:
  `Stage2Records bs arena rs t.tokens` and
  `evs = (rs.map EventRecord.encodedBytes).flatten` give the decoded rows, the
  record-for-record agreement with the parser's tokens (separators excepted,
  `TokenRecord`), the byte-level relation `Stage2EventRel bs arena evs t.tokens`
  (`stage2EventRel_of_records` at the same stream), the skeleton
  (`parseSkeleton`) and `decodeTape`'s value.
- The executable's `--consume` reader is the same table — a key or string
  thirteen bytes, a number nine, every other tag one — and it exits 5 unless the
  fold and the materialising reading count the same tokens, produce the same
  checksum, and land exactly on the stream's end.  `check.sh` pins that on the
  consumer fixture, so the program's reader and the proved one are checked
  against the same widths.
- `routePost_outputs` names the post's two payload reads, so the caller's
  `out` and `evs` are the post's own rather than a second witness.

What the decode does **not** supply is the walk's trace-to-stream equation
(`evs = (rs.map EventRecord.encodedBytes).flatten`) and the arena operand: both
are hypotheses of `routeView_decodes`, exactly as `JsonStage2TokenCorrespondence`
states them as the remaining row (the entry stream's positions against the
parser's token starts).  The wrapper's decode is a reader of the relation, not a
second production of the trace.

## Identity evidence, and what it is not

Three kinds of check exist, and none of them is a compiler-preservation theorem:

- **Text pins.**  Each proof module `include_str`s its fixture and a compiled
  `#guard` requires `parseModule` of that text to be the stated AST; a mutated
  fixture makes the pin fail (`probes/install/check.sh`).  The pin binds the
  proof to the committed bytes; it says nothing about the object.
- **Rebuild and hash.**  `probes/install/select.sh` rebuilds a unit from its
  fixtures, compares the object hash with the manifest, and reproduces the
  certificate; `probes/install/identity/inventory.sh` regenerates each fixture
  and its inventories and compares them byte for byte.  A byte-equal rebuild
  shows the object is that fixture's compilation under that toolchain; it does
  not show the instructions the machine executes.
- **Observation.**  The route's `check.sh` compares the Lean route's output with
  a C driver's on every admitted corpus row (observation, arena, events, byte
  for byte), the `--admit` mode compares the two-phase decision with `admission`
  row by row, and `correspondence.sh` re-derives the stage-2 artifact relation
  and fails when a structural claim in it stops holding.  These are runs, not
  proofs; they are the evidence that the artifact is the one the page names.

The route's own build asserts what a lost call would hide: `build.sh` checks
with `nm` that the adapter imports `leanllvm_json_pipeline`,
`leanllvm_json_entry_table`, the mask unit, `depth_count`, the depth walk and
the policy scan, and that the executable defines each — a build that lost a call
is a red, not a shorter route.

## The trust boundary, stated

A first useful deployment of this route trusts the following, and none of them
is verified by the theorems:

1. the Lean kernel and the three approved axioms (ledger row 1);
2. the LLVM semantics model, the intrinsic lane models and the fixture
   normalisation (rows 2–5);
3. clang, the LLVM backend, the assembler and the linker, for both the -O3
   fixture emissions and the route's -O2 objects (row 8);
4. the Lean compiler and runtime, for `RouteMain.lean` and its `@[extern]`
   calls: the ABI agreement is observed at link and run (row 9), and Lean's
   compilation of the wrapper is not proved to preserve its meaning;
5. the adapter (`shim.c`), the policy scan (`policy.c`) and the entry table's
   fill, which are new code with no refinement theorem; their agreement with
   the library's decisions is observed (`--admit`, `check.sh`, `guard.sh`);
6. libc's `malloc`, `memset`, `memcpy` and the stack protector, which the
   adapter and two kernel units call;
7. the object's inlining of the six stage-2 helpers and of the pipeline's
   unit calls, and the numeric conversion's emitted body (the obligation above).

What is *not* required is verification of the whole Lean compiler or of clang:
the proofs stand on their fixtures and the relation, and the deployment claim is
the one this page licenses — the route reports the object's observation, the
object is that source's compilation under the named flags, and the proofs relate
that source's fixtures to the reference parser under the rows above.  A reader
who needs more needs one of those rows closed, and the row names the evidence
that would close it.

## The route's cost, measured on the units harness's corpus

The measurement is `probes/json/route/bench-corpus.sh`, which reads the corpus
`tests/json-units-bench/bench.sh` generated (the same seed, sizes and tiling;
`tests/json-units-bench/build/corpus`) and runs the route's own `--stages` and
`--consume` modes: three trials of twenty-one repetitions per document, each
trial pinned with `taskset` to one CPU, exactly the units harness's shape.  The
route binary is the `TIMING=1` build, so the adapter's three intervals are
inside stages; the ordinary build reads no clock (`build.sh` asserts that with
`nm`).  Observed on 18 November 2026, host `Linux 6.17.0-1033-oem x86_64`,
`Intel(R) Core(TM) Ultra 7 268V`, governor `powersave`, CPUs 0 and 4.

Three facts about the rows, because their names can mislead:

- `decode+print` is the reporting mode's outcome stage: the `be64` header decode
  (which materialises the result's list at every byte it reads), the payload
  slices and the two hex lines written to stdout.  It is the *route's
  reporting*, not the object's work and not the production reader's; the
  `--consume` rows below are the production reader.
- `staging`, `copy-in`, `call` and `copy-out` are the application's cost: the
  record's sixteen zero-filled buffers, the adapter's copy into the object's
  ABI, the object's call, and the result copy.  The document read
  (`IO.FS.readBinFile`) is outside every stage and is not in `total`.
- A `path=fallback` row is a document the route's domain refuses: the reference
  parser answers it and the object is not called.  The 4 MiB documents are all
  of that class because the route's input bound is one mebibyte
  (`LeanLLVM.JSON.Limits.default`); the units' rows do measure 4 MiB, the
  route's do not, and that difference is the bound rather than a unit's cost.

### The stage split (CPU 0; ns, medians of the three trial medians)

| document | bytes | path | admission | staging | copy-in | call | copy-out | decode+print | total | ns/byte | trial ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `route-s1-64k` | 65,536 | fast | 178,566 | 179,228 | 50,420 | 20,469 | 230 | 80,952 | 511,006 | 7.80 | 1.01 |
| `route-u8-64k` | 65,536 | fast | 126,706 | 172,100 | 52,259 | 17,093 | 198 | 31,148 | 408,838 | 6.24 | 1.06 |
| `syn-dense-64k` | 65,536 | fast | 77,177 | 62,001 | 152,217 | 100,552 | 4,012 | 46,693,758 | 47,092,994 | 718.58 | 1.01 |
| `syn-strings-64k` | 65,536 | fast | 263,439 | 69,395 | 127,301 | 46,815 | 2,511 | 23,200,124 | 23,734,699 | 362.16 | 1.02 |
| `syn-utf8-64k` | 65,536 | fast | 412,360 | 53,702 | 57,197 | 25,501 | 1,267 | 8,487,430 | 9,122,900 | 139.20 | 1.03 |
| `syn-dense-4m` | 4,194,304 | fallback | 559 | – | – | – | – | 2,465 | 3,506 | – | 1.04 |
| `syn-strings-4m` | 4,194,304 | fallback | 561 | – | – | – | – | 2,325 | 3,574 | – | 1.09 |
| `syn-utf8-4m` | 4,194,304 | fallback | 541 | – | – | – | – | 2,425 | 3,416 | – | 1.05 |

The trial ratio is the largest trial median divided by the smallest, over the
three trials; the within-row spread `(p90-p10)/median` is 3–9 % on the printing
rows and 60–90 % on the tiny rows, where the printing jitter is larger than the
work.  The second device (CPU 4) is 1.55–1.71× slower on the same rows — e.g.
`syn-dense-64k` totals 80,400,389 ns, 1,226.81 ns/byte — which is why both
devices are reported rather than one being averaged into the other.

The dominant number is `decode+print`, and it is the reporting path's: the
`be64` header read traverses the whole result's list for every byte of every
word, so a 132,638-byte event stream costs 38 ms to read seven words and then
7 ms to print.  The production reader avoids it (`--consume` decodes the header
by index), and pays:

### The production reader (CPU 0; ns, the three trials; tokens = decoded records)

| document | verdict | tokens | fold (three trials) | materialising (three trials) |
|---|---|---|---|---|
| `route-s1-64k` | 0 (refused) | 19 | 415 / 401 / 412 | 757 / 839 / 764 |
| `route-u8-64k` | 0 (refused) | 0 | 157 / 169 / 146 | 151 / 154 / 164 |
| `syn-dense-64k` | 1 | 16,182 | 165,080 / 158,463 / 162,264 | 263,879 / 266,050 / 254,363 |
| `syn-strings-64k` | 1 | 687 | 96,761 / 98,999 / 98,206 | 100,089 / 100,207 / 105,186 |
| `syn-utf8-64k` | 1 | 1,859 | 28,040 / 29,132 / 27,729 | 37,293 / 37,664 / 36,830 |

So the caller's own cost for a 64 KiB accepted document is the staging and the
adapter's copies and call — 0.14–0.32 ms in the rows above — plus the consumer's
reading, 28–165 µs (`consume_fold_ns`) or 37–266 µs if one materialises a record
per token; the object's call is 17–101 µs of that, and the rest is the
application's staging.  A refused document costs its admission and its empty
reading (157–415 ns of fold on CPU 0), and a document outside the bound is
refused at the same decision, about 3.5 µs after the read.

### The units' rows on the same documents (CPU 0; GB/s medians)

| document | s1_masks | entry_pos8 | entry_b8 | utf8 gated |
|---|---|---|---|---|
| `route-s1-64k` | 12.740 | 11.755 | 5.515 | 83.592 |
| `route-u8-64k` | 13.202 | 12.166 | 7.889 | 24.976 |
| `syn-dense-64k` | 13.642 | 12.596 | 6.642 | 88.923 |
| `syn-strings-64k` | 11.449 | 13.094 | 32.670 | 88.923 |
| `syn-utf8-64k` | 12.536 | 13.479 | 26.826 | 21.382 |

These are one unit's pass over the document, not a decomposition of the route's
call: the pipeline runs the mask unit on every block, an entry emitter per
block, the UTF-8 stage once, the escape list where the arm selects it, and stage
2 over the entry stream, so the route's call is the composition and a unit's
rate is context rather than a subtrahend.  What the units' rows establish for
this page is the corpus and the discipline: same documents, same pinning, same
trial structure, and the route's numbers are read beside them.

The cost numbers are observations of one build on one host; they are not a claim
about any other machine, and they inherit the trust boundary below.
