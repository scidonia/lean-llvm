# The JSON pipeline's Lean call route

The review's step D: a Lean program that stages the document the assembled
pipeline's record demands and calls the native object.  The contract is
`LeanLLVM/JsonCallRoute.lean`; this directory is its executable route.

| File | What it is |
|---|---|
| `RouteMain.lean` | the standalone Lean entry point: the record's staging in bytes, the domain shell, the reference's character-policy scan, and the call |
| `shim.c` | the adapter: copies the caller's `ByteArray`s into the object's ABI, calls `leanllvm_json_pipeline`, returns the observed bytes |
| `driver.c` | a C caller that stages the document identically, for the fidelity comparison |
| `build.sh` | compiles the six kernel units, the adapter and the program, links them, and asserts the symbol is imported and defined |
| `check.sh` | the route scenario: fidelity against `driver.c`, the shell's refusals including the policy class, and the zero-divergence assertion |
| `DomainCheck.lean` | the library shell's `checkRoute`, elaborated from source and exercised at every refusal, and the fourteen-row policy class pinned against `documentRefusal` and `parseBytes` |

## Commands

```bash
nix develop -c bash probes/json/route/build.sh
nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonCallRoute
nix develop -c bash probes/install/lake-locked.sh env lean probes/json/route/DomainCheck.lean
```

`build.sh` prints `ok: .../leanllvm-json-route`; it fails if `nm` does not show
`leanllvm_json_pipeline` imported by the adapter and defined by the executable,
so a build that lost the call is a red rather than a pass.  `DomainCheck.lean`
needs the library's oleans, which the third command builds.

## Observed

`check.sh`, over the 122 default-profile manifest rows:

- the Lean route and the C driver agree on every row (verdict, four cursors,
  error offset), so the wrapper's staging is the record's and its outputs are
  the object's — this holds for the fourteen policy rows too, where the object's
  observation is printed before the wrapper refuses;
- 59 `accept` rows are accepted, 48 `invalid` rows report the object's refusal,
  and 14 `invalid` rows are refused by the wrapper with the reference parser's
  reason and byte; the empty corpus document is refused with its reason, and an
  over-bound document is refused with its bound;
- divergence is 0: every default-profile row's verdict agrees with the
  reference's, where before the wrapper's change the object accepted 14
  documents the reference refuses;
- the eight non-default-profile rows (`depth2`, `in8`, `tok4`) are skipped: the
  route is stated at `Limits.default`, and those rows exercise other limits.

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

## What this does and does not establish

It establishes that a Lean program reaches the native object, that the staging
it builds is the one the record asks for (by agreement with an independent C
caller), that the shell refuses the empty document, over-bound input and the
reference's character-policy class before it trusts the object's verdict, and
that the fourteen documents the object accepts and the reference refuses are
refused with the reference's own reason and byte.  It does not establish that
the object executes the pinned body the theorems are about: the refinement
theorem speaks about the parsed AST and `Mem`, and the compiler/FFI step from
that to the linked object is the trust boundary `docs/contract.md` row 9
records.  The object itself still accepts the fourteen: `Sigma_pipeline` states
the reference parser's predicate, and the object's verdict is the RFC one, which
is why `Sigma_pipeline` remains a statement rather than a theorem about the
linked object.

One implementation note, observed while wiring it: the table initialiser is a
pure `@[extern]` whose result was unused, and the compiler eliminated the call,
leaving the POS8 table zeroed and every container refused.  The route consumes
the result, so the call survives; an adapter that returns nothing observable
must not be written as an unused pure call.
