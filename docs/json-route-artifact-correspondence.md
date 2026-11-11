# The stage-2 artifact correspondence

The proofs run a stage-2 body and the route links a stage-2 object.  Both come
from `kernel/json/stage2.c`, but they are not the same emission: the proofs'
body is `probes/install/ir/stage2.candidate.ll`, the -O3 emission of a
transformed source, and the route's object is a -O2 compilation of the
untransformed file.  A shared source filename establishes nothing, so this page
records the relation that is actually relied on — the flags, the derivation
steps, which bodies are identical under which transform, and what is left over.

The record is the output of

```bash
nix develop -c bash probes/json/route/correspondence.sh
```

observed on the working tree at `4f94295` plus the change that adds this page,
with Lean 4.35.0 and clang/LLVM 21.1.8 from the flake.  The script re-derives
every measurement and fails when a structural claim in the record stops holding
— a flag beyond the optimisation level, a different transform, a lost helper
call composition — so a stale copy of this page cannot pass as current.  The
scenario's own cuts are recorded in
[The route boundary's controls](json-route-evidence.md#the-route-boundarys-controls-r1r9);
this page's flag relation is cut `R8`.

## The record

```text
## The two artifact paths

| | flags | source | derivation |
|---|---|---|---|
| the proofs' body (`probes/install/ir/stage2.candidate.ll`) | `-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64` | `kernel/json/stage2.c`, `noinline` on eleven helpers, `s2_walk` forced inline | `opt -passes=lower-switch`, the recorded token strip, eight staging allocas flattened to parameters, callees reduced to declarations |
| the route's object (`probes/json/route/build.sh`) | `-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64 -I "$repo/kernel/json"` | the same file, untransformed | none: `clang -c` |

## The flag relation

The codegen token sets are equal except for the optimisation level:

- common: `-falign-functions=64 -falign-loops=64 -march=x86-64-v3 -mpclmul -std=gnu11`
- `build.sh` alone: `-O2`
- `capture-stage2.sh` alone: `-O3`
- ignored as non-codegen: `-S -emit-llvm` (output mode), `-I` and its path (include path), `-fno-discard-value-names` (naming)

The naming flag changes no instruction at the route's own -O2 line: the emission with and without it is identical after register names and block labels are neutralised.

## The normalisation steps

The fixture is derived, not transcribed.  In order: (1) the source transform above, whose counts are two `always_inline` occurrences (the comment's and `s2_walk`'s) and eleven `noinline` helper functions, plus the `EL_ENTRY` macro line; (2) `opt -passes=lower-switch`; (3) the token strip, by the classes `capture-stage2.sh` records in `stage2.strip.tsv`; (4) the eight staging allocas `%d.i %c.i %ctype.i %cst.i %t352.i %s %z %e` appended as `ptr` parameters (`stage2.staging.tsv`); (5) the three instruction rewrites and the callee definitions replaced by declarations (`stage2.rewrites.tsv`).  The comparison below applies steps (1)–(3) to both emissions and then replaces every virtual register with one placeholder and drops block labels, so the two texts are compared instruction by instruction.

## What is identical, and what is not

The eleven helpers, as emitted under the transform at each level:

- identical after the normalisation (3): `num_d8_el1 s2_init s2_value_pos `
- differing (6): `el_exact el_pack num_fast_el1 od_scalar_value s2_after_value s2_string_body `
- not emitted at either level (a `static` function this translation unit no longer references once the callers are out of line): `s2_string_touch touch_bytes`

The walk's own body (`@leanllvm_json_stage2` with `s2_walk` inlined): differs after the same normalisation, 622 lines at -O2 against 615 at -O3.

The helper calls the fixture keeps, per emission of the wrapper block: `10` in the committed fixture, `10` in the transformed -O2 emission, `10` in the transformed -O3 emission, and `0`/`0` in the untransformed -O2/-O3 emissions.  Every helper is `always_inline` before the transform, so the untransformed object has none: the distance between the fixture and the object is the call composition of the transform, not the optimisation level.

## The relation relied on, and its residual

The correspondence between the proof's body and the route's object is these five statements and no more:

1. both artifacts are emitted from `kernel/json/stage2.c`; this is necessary and not sufficient, and it is all that the shared filename gives;
2. their codegen flags differ in the optimisation level alone (`-O2` against `-O3`), measured above, and the naming flag is not an instruction change, measured above;
3. of the eleven helper bodies, 3 are identical between the two levels under the transform after the recorded normalisation, 6 differ, and 2 are not emitted at either level; the walk's body differs;
4. the fixture keeps 10 helper call site(s) where the untransformed emissions keep 0, so the object inlines every helper the fixture leaves out of line;
5. the object's walk text is therefore not the fixture's text: the fixture's body is 937 instruction line(s) against the object's normalised 622.

So the object is not the fixture's function by these measurements: the fixture is the walk's text with the helpers it takes out of line as callees, and the object at -O2 has none of them out of line and a different instruction selection inside the walk.  What the record establishes is the shape of the gap — same source, same code-generating flags but the level, a known transform, and a measured body-by-body difference — so a claim that the linked object computes the fixture's function has to carry the compiler/backend trust row and the helper-contract transfer for the bodies that differ here.  It cannot be inferred from the source filename, and the probe does not claim it.

Unification was not taken: linking the fixture would make the route call a twenty-one-argument body while the driver calls the thirteen-argument ABI, so the two callers would stop being comparable, and the fixture's callees are declarations the proof's environment resolves rather than objects the probe links.
```

## How to read it

Line 1 of the record's relation is all that the shared source gives, and it is
deliberately marked as insufficient.  The load-bearing measurements are 2, 4 and
5: the two flag lines differ in the optimisation level alone and in nothing
else; the fixture keeps ten helper call sites where both untransformed
emissions keep none, so the object inlines the helpers the fixture leaves out of
line; and the resulting texts are different bodies, 937 instruction lines
against the object's 622.

Statement 3 is the one that limits the claim.  Under the same transform, three
of the eleven helpers emit an identical body at -O2 and -O3 after the recorded
normalisation, six do not, and two are not emitted at all because their only
caller is out of line in this translation unit.  The walk's own body differs as
well.  So the object is not the fixture's function by measurement: it is a
compilation of the same source at a neighbouring level with a different call
composition, and any statement that the linked object computes the body the
proofs run has to carry the trust ledger's rows 8 and 9 — native compilation,
and the Lean execution bridge — plus the helper contracts for the bodies that
differ here.

That is why the correspondence is recorded rather than unified.  Linking the
fixture would make the route call a twenty-one-argument body while the driver
calls the thirteen-argument ABI, so the route and the driver would stop being
comparable, and the fixture's callees are declarations the proof's environment
resolves rather than objects the probe links.  The probe's claim stays what the
scenario measures: the route reports *this object's* observation, byte for byte,
and the object's relation to the proved body is the one recorded above and no
stronger.
