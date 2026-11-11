# The JSON pipeline's Lean call route

The review's step D: a Lean program that stages the document the assembled
pipeline's record demands and calls the native object.  The contract is
`LeanLLVM/JsonCallRoute.lean`; this directory is its executable route.

| File | What it is |
|---|---|
| `RouteMain.lean` | the standalone Lean entry point: the record's staging in bytes, the domain shell, the reference's character-policy scan, the call, and the tagged result's report |
| `shim.c` | the adapter: validates the staging, copies the caller's `ByteArray`s into the object's ABI, fills the entry unit's POS8 table, calls `leanllvm_json_pipeline`, and returns the tagged result |
| `driver.c` | a C caller that stages the document identically and prints the same three lines, for the fidelity comparison |
| `build.sh` | compiles the six kernel units, the adapter and the program, links them, and asserts the two symbols the adapter calls are imported and defined |
| `check.sh` | the route scenario: fidelity against `driver.c` over the observation and both payload streams, the shell's refusals including the policy class, the zero-divergence assertion, and the depth boundary |
| `correspondence.sh` | the stage-2 artifact correspondence: the flags, the derivation steps, which bodies are identical under the transform, and what is left over |
| `DomainCheck.lean` | the library shell's `checkRoute`, elaborated from source and exercised at every refusal, the fourteen-row policy class pinned against `documentRefusal` and `parseBytes`, and the depth boundary's two sides |

## Commands

```bash
nix develop -c bash probes/json/route/build.sh
nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/correspondence.sh
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonCallRoute
nix develop -c bash probes/install/lake-locked.sh env lean probes/json/route/DomainCheck.lean
```

`build.sh` prints `ok: .../leanllvm-json-route`; it fails if `nm` does not show
`leanllvm_json_pipeline` and `leanllvm_json_entry_table` imported by the adapter
and defined by the executable, so a build that lost the call or the table's
initialisation is a red rather than a pass.  `correspondence.sh` prints the
artifact relation; its output is recorded in
[the correspondence page](../../../docs/json-route-artifact-correspondence.md).
`DomainCheck.lean` needs the library's oleans, which the fourth command builds.

## Observed

`check.sh`, over the 122 default-profile manifest rows and then the depth
boundary:

```text
ok: 122 default-profile rows: route and driver agree on the observation, arena and events (60 arena byte(s) over 19 row(s), 3125 event byte(s) over 86 row(s)); accept 59, invalid 48, policy refusals 14; divergence 0; empty excluded 1; 8 non-default-profile rows skipped; depth 128/129/520/521 agree, object accepts 128..520 and refuses 521 at 520
```

- the Lean route and the C driver print the same three lines on every row —
  verdict, four cursors and error offset; the arena and the event stream — and
  the two payload lines are compared byte for byte, so equal lengths and a
  shared verdict cannot conceal different values.  The comparison is
  field-wise: a verdict disagreement, a value disagreement (naming the stream
  and the first differing byte) and a metadata disagreement (a cursor, or the
  error offset) are separate diagnostics.  Between the route and the driver no
  difference is allowed, because both call the same object with the same
  staging; the classes distinguish what broke, they do not admit anything.  This
  holds for the fourteen policy rows too, where the object's observation is
  printed before the wrapper refuses;
- 59 `accept` rows are accepted, 48 `invalid` rows report the object's refusal,
  and 14 `invalid` rows are refused by the wrapper with the reference parser's
  reason and byte; the empty corpus document is refused with its reason, and an
  over-bound document is refused with its bound;
- divergence is 0: every default-profile row's verdict agrees with the
  reference's, where before the wrapper's change the object accepted 14
  documents the reference refuses;
- the eight non-default-profile rows (`depth2`, `in8`, `tok4`) are skipped: the
  route is stated at `Limits.default`, and those rows exercise other limits;
- the two callers agree on all four depth probes: 128 and 129 nestings, and the
  native stack's 520 and 521.  The reference accepts 128 and refuses 129
  (`depthExceeded`, pinned by `DomainCheck.lean`); the native walk pushes 520
  frames and refuses the 521st at offset 520.  So the object accepts 129..520,
  where the reference refuses: that class is outside the record's domain
  (`pipelineSpecPre` excludes `.depthExceeded`), the route reports the object's
  observation there, and the scenario asserts it rather than leaving the gap
  implicit.

The byte comparison is not vacuous: the run counts the bytes it compared and
the rows that carried any, and fails when either arm is empty — two empty
payloads agree however the object misbehaved.  Every assertion above has a cut
that makes it fail; the cuts and their observed output are recorded under
[The route boundary's controls](../../../docs/json-route-evidence.md#the-route-boundarys-controls-r1r9).

The fourteen are one class: documents the reference parser refuses under its
**character policy** — lone and out-of-range surrogate escapes
(`lone-dead.json`, `lone-d800.json`, `double-high.json`, `high-char.json`,
`reversed-pair.json`, `lone-dc00.json`) and noncharacters, escaped and raw
(`nc-fdd0.json`, `nc-fffe.json`, `nc-ffff.json`, `nc-pair-max.json`,
`nc-raw-fdd0.json`, `nc-raw-fffe.json`, `nc-raw-10ffff.json`,
`nc-raw-1fffe.json`).  Those are RFC 8259 texts, so the object's verdict is the
RFC verdict and the reference's is stricter; RFC 7493 §2.1 is the reference's
policy, and `DomainCheck.lean` pins both the reference's reason and the
wrapper's.

## The policy scan, and where it could differ

`RouteMain.lean`'s `scanDocument` reads the document's string bodies the way the
reference's `scanChars` reads them — the same escape pairing, the same strict
UTF-8 ranges, the same `IsNoncharacter` predicate — and reports the reference's
reason and byte.  It is a second implementation of the reference's scan, because
the probe is standalone and cannot link the reference parser; `DomainCheck.lean`
pins the class against the parser itself, and `check.sh` pins the executable's
reason and byte for all fourteen rows.

The scan is applied only to a document the object accepted.  That is the class
where the wrapper's verdict can differ from the reference's: a document the
object refused already has a refusal verdict, and the wrapper reports it rather
than substituting a second reason.  On an accepted document the bytes are RFC
JSON, so the bodies the scan walks are the bodies the reference walks.

The ordering is the probe's, and it is what keeps the fidelity instrument: the
object is called and its observation printed for every default-profile row, so
the route/driver agreement is measured on the fourteen policy rows too, and the
refusal is the wrapper's additional verdict on top.  A caller follows
`LeanLLVM.JsonCallRoute.checkRoute`, which refuses the same class *before* the
call — the contract's domain is the stronger statement, and the probe measures
the object's behaviour on the same documents.

The one way the scan could report a reason the reference would not is an object
more lenient than RFC 8259 that accepted a document the reference refuses
syntactically, with a policy-class sequence after the lenient spot.  Both sides
refuse such a document, so the verdict agrees; only the reported reason could
differ.  The corpus shows no such document: the object and the reference agree
on all 122 rows after the fourteen are refused.

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
route prints byte for byte, that the shell refuses the empty document,
over-bound input and the reference's character-policy class before it trusts the
object's verdict, and that the fourteen documents the object accepts and the
reference refuses are refused with the reference's own reason and byte.  It also
measures, rather than inherits, the depth boundary on both sides of the
reference's 128 levels and the native stack's 520.

It does not establish that the object executes the pinned body the theorems are
about: the refinement theorem speaks about the parsed AST and `Mem`, and the
compiler/FFI step from that to the linked object is the trust boundary
`docs/contract.md` rows 8 and 9 record — `correspondence.sh` records exactly
how far the two emissions are from each other, which is that they are not the
same text.  It does not compare the payload values with the reference tape's
values either: both callers run the same object, so their agreement is evidence
about the adapter path and not about the object's meaning.  The object itself
still accepts the fourteen: `Sigma_pipeline` states the reference parser's
predicate, and the object's verdict is the RFC one, which is why
`Sigma_pipeline` remains a statement rather than a theorem about the linked
object.
