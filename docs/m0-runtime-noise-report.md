# M0 report: Lean runtime noise and the replacement seam

Status: evidence report for `docs/lean-vellum-development-programme.md`,
revised after the review in `docs/m0-runtime-noise-review-handoff.md`. No
production code changed. The probes are preserved as fixtures under
`probes/m0/`; the commands below reproduce every observation.

Date: 2026-10-28 (revised).

## 0. Review corrections applied

| Review point | Disposition |
|---|---|
| "the seam must be `@[extern]`" overclaims | Restated: the first implementation uses an opaque declaration; the build preserves the boundary until installation. Installation before inlining and controlled separate compilation remain alternatives. |
| An opaque declaration supplies no baseline | The first work package now names a separately compiled baseline body, a candidate, a refinement theorem, a contextual theorem and an installation record. |
| SWAR mask is not exact | The example is now an exact per-byte mask; the borrow-based counterexample is a regression case. Baseline-to-specification correctness is kept separate from candidate-to-baseline refinement. |
| Semantic acceptance vs coverage conflated | Split into two independent checks; the global "no baseline-shaped instructions" requirement is withdrawn. |
| Pure slice still needs a contextual theorem | Added to the first work package; a bit-vector equality alone is not acceptance. |
| Attribute policy too blunt | Replaced "recompute or drop" with three documented treatments and the poison rule for `range`. |

## 1. Summary

Two findings decide the first work package.

1. **A realistic Lean recogniser does not lower to a small IR unit.** A loop
   over `ByteArray` indexed by `Nat` emits tagged-pointer arithmetic, refcount
   operations, bounds assertions and three bignum runtime calls. The
   translation unit contains 13 function definitions and 9 external
   declarations at `-O1`. The `ByteArray.data.foldl` variant removes the bignum
   calls but still calls `lean_byte_array_data`, `lean_notify_assert` and
   `lean_dec_ref_cold` (11 definitions, 7 declarations).
2. **The first implementation will use an opaque external declaration; the
   build must preserve the intended boundary until certification and
   installation.** At `-O3` in the same translation unit, clang inlines an
   exported Lean definition into its Lean caller: the caller body is the
   recogniser and no call remains. An opaque `@[extern]` declaration has no
   body in the unit, so the call survives. The probe does not establish that
   the extern is the only mechanism: replacing before inlining and controlled
   separate compilation are alternatives.

`@[noinline]` produced no `noinline` attribute in the generated C, the IR, or
`lean.h` in this toolchain. It is not relied on as a boundary mechanism.

## 2. Toolchain and method

| Item | Value |
|---|---|
| Lean | `v4.35.0-rc3` (the repository flake) |
| Clang / LLVM | 21.1.8 (the repository flake) |
| Target | `x86_64-unknown-linux-gnu` (from the emitted `target triple`) |
| Lowering | `lean -c file.c` → `clang -S -emit-llvm` |
| Optimisation levels | `-O1` for inventory, `-O3` for boundary survival |
| Link-time optimisation | not enabled; see §8 |

The fixtures are in `probes/m0/`. From the repository root:

```bash
nix develop -c bash probes/m0/check.sh
```

The script builds the three probes into a temporary directory, asserts the
definition and declaration counts, asserts that the extern call survives at
`-O3`, and runs the SWAR regression guards. The prose below records the same
commands for inspection.

## 3. Probe 1: `Nat`-indexed recogniser

```bash
grep -c '^define'  ProbeO1.ll   # 13
grep -c '^declare' ProbeO1.ll   # 9
grep '^declare' ProbeO1.ll
```

```llvm
declare void @lean_initialize_runtime_module(...)
declare ptr  @initialize_Init(i8)
declare ptr  @initialize_Init_Data_ByteArray(i8)
declare void @lean_notify_assert(ptr, i32, ptr)
declare zeroext i1 @lean_nat_big_lt(ptr, ptr)
declare ptr  @lean_nat_big_add(ptr, ptr)
declare ptr  @lean_big_usize_to_nat(i64)
declare void @lean_dec_ref_cold(ptr)
declare noalias ptr @lean_alloc_small_object_core(i32)
```

The loop body (`l_scan_go`) is a control-flow graph with:

- `getelementptr`, `load`, `store`, `phi`, `br`, `icmp`, `add`, `mul`, `shl`,
  `or`, `and`, `ptrtoint`, `inttoptr`;
- tagged small-integer checks (`and i64 %x, 1`, `inttoptr`),
- refcount manipulation of the `Nat` object and the buffer,
- `lean_nat_big_lt` / `lean_nat_big_add` on the index,
- `lean_notify_assert` on the buffer access,
- `!tbaa` (31 occurrences) and `!prof` (21) metadata,
- `target triple` and `target datalayout`.

## 4. Probe 2: `ByteArray.data.foldl`

```bash
grep -c '^define'  Probe3O1.ll   # 11
grep -c '^declare' Probe3O1.ll   # 7
grep '^declare' Probe3O1.ll
```

```llvm
declare ptr  @lean_byte_array_data(ptr)
declare void @lean_initialize_runtime_module(...)
declare ptr  @initialize_Init(i8)
declare ptr  @initialize_Init_Data_ByteArray(i8)
declare void @lean_notify_assert(ptr, i32, ptr)
declare void @lean_dec_ref_cold(ptr)
declare noalias ptr @lean_alloc_small_object_core(i32)
```

The bignum path is gone, but `lean_byte_array_data`, the bounds assertion and
the refcount remain, and the loop becomes a compiler-named function
`l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00scanFold_spec__0`.
Metadata: 34 `!tbaa`, 31 `!prof`.

## 5. Probe 3: the boundary mechanism and the exact mask

### 5.1 Contract

`commaMask8` classifies one 64-bit word as eight little-endian lanes. Bit
`8*i + 7` is set iff byte `i` equals `0x2C`; all other bits are zero. This is
an exact lane mask, suitable for compaction and for extracting lane indices.

The borrow-based idiom

```text
m = x XOR 0x2C2C2C2C2C2C2C2C
(m - 0x0101010101010101) AND NOT m AND 0x8080808080808080
```

is **not** an exact lane mask. Subtraction is modulo 2^64 and the borrow
crosses lanes. With `x = 0x0000000000002D2C` (comma in lane 0, `0x2D` in lane
1), it returns `0x8080`; the exact mask is `0x0080`. The borrow idiom may be
used as an existence predicate, but then that weaker contract must be stated
and proved; it cannot justify compaction.

The probe uses the no-borrow exact mask:

```lean
@[export leanllvm_comma_mask8]
def commaMask8 (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

def useIt (x : UInt64) : UInt64 := commaMask8 x * 2

@[extern "leanllvm_comma_mask8_ext"]
opaque commaMask8Ext (x : UInt64) : UInt64

def useItExt (x : UInt64) : UInt64 := commaMask8Ext x * 2
```

Baseline-to-specification correctness and candidate-to-baseline refinement are
separate obligations. The exactness of `commaMask8` is a statement about the
function above; a candidate that refines a *different* baseline preserves that
baseline's behaviour, not the intended classification.

### 5.2 Emitted code

`clang -O3` on the generated C:

```llvm
define range(i64 0, -9187201950435737471) i64 @leanllvm_comma_mask8(i64 noundef %0) {
  %2 = and i64 %0, 9187201950435737471
  %3 = xor i64 %2, 3182967604875373612
  %4 = add nuw i64 %3, 9187201950435737471
  %5 = or i64 %4, %0
  %6 = and i64 %5, -9187201950435737472
  %7 = xor i64 %6, -9187201950435737472
  ret i64 %7
}
```

Seven instructions, no calls, no memory. The `range` attribute is a semantic
claim about returned values; see §7.

The exported body is inlined into its same-unit caller, and no call survives:

```llvm
define range(i64 0, 144115188075855872) i64 @l_useIt(i64 noundef %0) {
  %2 = and i64 %0, 35887507618889599
  %3 = xor i64 %2, 12433467206544428
  %4 = add nuw nsw i64 %3, 35887507618889599
  %5 = or i64 %4, %0
  %6 = shl i64 %5, 1
  %7 = and i64 %6, 72340172838076672
  %8 = xor i64 %7, 72340172838076672
  ret i64 %8
}
```

The opaque declaration survives, because the callee has no body in the unit:

```llvm
define range(i64 0, -1) i64 @l_useItExt(i64 noundef %0) {
  %2 = tail call i64 @leanllvm_comma_mask8_ext(i64 noundef %0) #3
  %3 = shl i64 %2, 1
  ret i64 %3
}
```

Both observations are properties of this build configuration. The first
implementation uses the opaque form, preserves the boundary until
installation, and checks the actual application caller. It does not assume the
opaque form is the only possible boundary.

## 6. Inventory and consequences

| Observation | Consequence |
|---|---|
| `Nat` indexing pulls in `lean_nat_big_*` and boxing | Keep `Nat` out of the certified unit; use `UInt64`/`USize` explicitly |
| The unit still carries tagged pointers, refcounts, `lean_notify_assert` | "Few external calls" must be restated as a **closed, contract-bound call set** |
| `@[export]` is inlined into same-unit callers at `-O3` | Preserve the boundary by construction; the opaque declaration is the first mechanism, not the only one |
| `@[noinline]` has no C/IR effect in this toolchain | Do not rely on it without inspecting the emitted output |
| The extern call survives at `-O3` without LTO | First seam: an opaque `@[extern]` with a pure signature and a separately compiled baseline |
| Attributes (`range`, `noundef`, `nonnull`, `noalias`) and `!tbaa`/`!prof` are present | Bind and treat them by policy; see §7 |
| `target triple` and `target datalayout` are present | The manifest must bind them; a candidate compiled for another target is not a replacement |

### 6.1 Semantic acceptance and replacement coverage

These are independent and must be reported separately.

| Check | Question |
|---|---|
| Semantic acceptance | Is every installed candidate covered by a valid certificate and a contextual theorem for the release artifacts? |
| Replacement coverage | Do the application paths targeted for optimisation execute the candidate? |

An inlined copy of the correct baseline elsewhere is not by itself a semantic
failure; it is a coverage limitation. Equally, an identity installation passes
through the build but cannot demonstrate candidate selection from observable
outputs, because the bodies are identical.

Coverage is established by construction: keep the boundary before
installation, record the intended callers and their symbol resolution, and use
inspection or a dedicated diagnostic build to show that representative
executions reach the seam. Do not require a global pattern match that no
baseline-shaped instructions remain; equivalent computations can differ
syntactically, and unrelated code can share syntax.

## 7. Attributes and metadata

Do not adopt a blanket "drop unsupported attributes" policy. LLVM 21's
language reference makes an integer result outside a declared `range` poison,
and assumptions on declarations and call sites may already have influenced
caller optimisation. Removing an attribute from the candidate does not undo
those assumptions in an already-compiled caller.

For each supported attribute or metadata kind, choose and document one of:

1. **Model it** and establish the obligation (for `range`, the returned value
   lies in the interval; for `noundef`, definedness).
2. **Remove or weaken it at a controlled earlier stage**, then rebuild the
   affected callers, recording the semantic justification or the trust
   assumption.
3. **Reject the artifact** until it is supported.

Distinguish semantic information (aliasing constraints, `range`, `noundef`,
`noalias`) from optimisation hints (ordinary branch weights in `!prof`). They
are not one category. Bind target triple, data layout, target features,
signatures, declarations, call-site assumptions and linked contracts into the
certification record; hashes bind artifacts but do not prove an attribute
policy is sound. Check the policy against the pinned LLVM 21 documentation,
not against an unversioned page.

## 8. Adjusted first work package

1. **Reproduce and preserve the probes.** `probes/m0/check.sh` is the durable
   fixture; it asserts the counts, the extern call and the SWAR guards.
2. **Supply a concrete baseline.** The opaque declaration supplies an
   interface, not a body. Compile the baseline (from the Lean definition, or
   from a separately authored implementation with an explicit connection to the
   Lean specification) into a separate object under the seam's symbol; verify
   signature, calling convention, symbol resolution and wrappers. The
   candidate is a second object with the same interface.
3. **Write the contextual theorem before proof automation.** For the pure
   slice, state the local LLVM refinement and the restricted caller/callee
   replacement theorem; a `BitVec` equality is a lemma, not acceptance.
4. **Install, then select.** Demonstrate identity installation, then install a
   structurally different certified body and show that the target paths execute
   it. Report semantic acceptance and coverage separately.
5. **Decide the attribute policy per kind** and bind it, the target
   configuration and the artifact hashes into the manifest.
6. **Then the memory-using loop**, where heap relations, framing and the
   runtime-call contracts enter. That remains the programme's substantive M4
   target; the pure slice is an earlier integration gate.

## 9. Limits

- One toolchain (`Lean v4.35.0-rc3`, clang 21.1.8), one target
  (`x86_64-unknown-linux-gnu`), one probe family, no benchmark.
- The observations are about IR shape, not speed.
- The exact-mask formula is checked on examples, not proved. Its parity proof
  and the proof that a candidate implements it are separate work.
- LTO was not enabled. With LTO, an extern whose definition is in another
  object can be inlined; preserve the boundary before installation, or control
  LTO explicitly.
- `lean -c` emits one C file per module; cross-module callers see the symbol,
  same-module callers may see the inlined body. Inspect the application, not
  only the probe.
- The `initialize_*` declarations are module initialisation, not the hot path;
  they are listed for completeness, not as an obstacle.

## 10. Open questions

- Which call sites in a real application actually reach the seam? Inspect the
  emitted C and IR of the selected app, not only the probe.
- Is the chosen signature raw (`UInt64 → UInt64`) or pointer-plus-length? The
  latter brings bounds and memory into the certificate immediately.
- Which baseline body is installed for the first slice, and what connects it to
  the Lean specification?
- For `UInt64 → UInt64`, which attributes does the baseline carry, and what
  policy applies to each?
- How will coverage be demonstrated for representative executions without
  relying on a global pattern match?
