# The JSON pipeline's Lean call route

The review's step D: a Lean program that stages the document the assembled
pipeline's record demands and calls the native object.  The contract is
`LeanLLVM/JsonCallRoute.lean`; this directory is its executable route.

| File | What it is |
|---|---|
| `RouteMain.lean` | the standalone Lean entry point: the record's staging in bytes, the domain shell, and the call |
| `shim.c` | the adapter: copies the caller's `ByteArray`s into the object's ABI, calls `leanllvm_json_pipeline`, returns the observed bytes |
| `driver.c` | a C caller that stages the document identically, for the fidelity comparison |
| `build.sh` | compiles the six kernel units, the adapter and the program, links them, and asserts the symbol is imported and defined |
| `check.sh` | the route scenario: fidelity against `driver.c`, the shell's refusals, and the reference divergence report |
| `DomainCheck.lean` | the library shell's `checkRoute`, elaborated from source and exercised at every refusal |

## Commands

```bash
nix develop -c bash probes/json/route/build.sh
nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/install/lake-locked.sh env lean probes/json/route/DomainCheck.lean
```

`build.sh` prints `ok: .../leanllvm-json-route`; it fails if `nm` does not show
`leanllvm_json_pipeline` imported by the adapter and defined by the executable,
so a build that lost the call is a red rather than a pass.

## Observed

`check.sh`, over the 122 default-profile manifest rows:

- the Lean route and the C driver agree on every row (verdict, four cursors,
  error offset), so the wrapper's staging is the record's and its outputs are
  the object's;
- 59 `accept` rows are accepted and 62 `invalid` rows refused, except fourteen
  the object accepts; the empty corpus document is refused with its reason, and
  an over-bound document is refused with its bound;
- the eight non-default-profile rows (`depth2`, `in8`, `tok4`) are skipped: the
  route is stated at `Limits.default`, and those rows exercise other limits.

The fourteen divergences are one class: the object accepts documents the
reference parser refuses under its **policy** — lone and out-of-range surrogate
escapes (`lone-d800.json`, `double-high.json`, …) and noncharacters
(`nc-fdd0.json`, `nc-raw-10ffff.json`, …).  Those are RFC texts; the reference's
refusal is `unpairedSurrogate`/`noncharacter`, which `DomainCheck.lean` names.
The pipeline's ABI has no policy slot, so the object's verdict is the RFC
verdict; `Sigma_pipeline` states `parseBytes`'s, and the two differ here.  This
is a finding about the object and the specification, not about the route.

## What this does and does not establish

It establishes that a Lean program reaches the native object, that the staging
it builds is the one the record asks for (by agreement with an independent C
caller), and that the shell refuses the empty document and over-bound input
before any call.  It does not establish that the object executes the pinned body
the theorems are about: the refinement theorem speaks about the parsed AST and
`Mem`, and the compiler/FFI step from that to the linked object is the trust
boundary `docs/contract.md` row 9 records.  It also does not establish the
policy agreement: the object lacks the reference's policy refusals.

One implementation note, observed while wiring it: the table initialiser is a
pure `@[extern]` whose result was unused, and the compiler eliminated the call,
leaving the POS8 table zeroed and every container refused.  The route consumes
the result, so the call survives; an adapter that returns nothing observable
must not be written as an unused pure call.
