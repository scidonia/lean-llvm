# M0 report: Lean runtime noise and the replacement seam

Status: evidence report for `docs/lean-vellum-development-programme.md`. No
production code changed. The probes were built in `/tmp/lv-probe`; the sources
and commands below reproduce every observation.

Date: 2026-10-28.

## 1. Summary

Two findings decide the first work package.

1. **A realistic Lean recogniser does not lower to a small IR unit.** A loop
   over `ByteArray` indexed by `Nat` emits tagged-pointer arithmetic, refcount
   operations, bounds assertions and three bignum runtime calls. The
   translation unit contains 13 function definitions and 9 external
   declarations at `-O1`. The `ByteArray.data.foldl` variant removes the bignum
   calls but still calls `lean_byte_array_data`, `lean_notify_assert` and
   `lean_dec_ref_cold` (11 definitions, 7 declarations).
2. **The replacement seam must be an opaque `@[extern]` symbol, not
   `@[export]`.** At `-O3`, clang inlines an exported Lean definition into its
   Lean callers: the caller body is the recogniser and no call remains.
   An `@[extern]` declaration has no body in the translation unit, so the call
   survives (`tail call i64 @leanllvm_classify8_ext(...)`).
   `@[noinline]` produces no `noinline` attribute in the generated C, the IR,
   or `lean.h`.

A pure `UInt64` function is small and call-free (seven instructions), but it is
not by itself the seam. It is the shape the certified candidate should have,
with the call site declared `@[extern]`.

## 2. Toolchain and method

| Item | Value |
|---|---|
| Lean | `v4.35.0-rc3` (the repository flake) |
| Clang / LLVM | 21.1.8 (the repository flake) |
| Target | `x86_64-unknown-linux-gnu` (from the emitted `target triple`) |
| Lowering | `lean -c file.c` → `clang -S -emit-llvm` |
| Optimisation levels | `-O1` for inventory, `-O3` for boundary survival |
| Link-time optimisation | not enabled; see §7 |

Commands are run from the `lean-llvm` checkout so the flake supplies both
tools; the scratch directory is outside the repository.

```bash
mkdir -p /tmp/lv-probe
cat > /tmp/lv-probe/Probe.lean <<'LEAN'
import Init.Data.ByteArray

def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13

def isPunct (b : UInt8) : Bool :=
  b == 44 || b == 58 || b == 123 || b == 125

def classify (b : UInt8) : UInt8 :=
  if isSpace b then 0 else if isPunct b then 1 else 2

def scan (buf : ByteArray) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if i < buf.size then
      go (i + 1) (acc * 3 + (classify (buf.get! i)).toUInt64)
    else acc
  go 0 0

@[noinline] def scanNoInline (buf : ByteArray) : UInt64 := scan buf
LEAN

cat > /tmp/lv-probe/Probe3.lean <<'LEAN'
import Init.Data.ByteArray

def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13

def isPunct (b : UInt8) : Bool :=
  b == 44 || b == 58 || b == 123 || b == 125

def classify (b : UInt8) : UInt8 :=
  if isSpace b then 0 else if isPunct b then 1 else 2

def scanFold (buf : ByteArray) : UInt64 :=
  buf.data.foldl (fun acc b => acc * 3 + (classify b).toUInt64) 0
LEAN

cat > /tmp/lv-probe/Chunk2.lean <<'LEAN'
@[export leanllvm_classify8]
def classify8 (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  (m - 0x0101010101010101) &&& ~~~m &&& 0x8080808080808080

def useIt (x : UInt64) : UInt64 := classify8 x * 2

@[extern "leanllvm_classify8_ext"]
opaque classify8Ext (x : UInt64) : UInt64

def useItExt (x : UInt64) : UInt64 := classify8Ext x * 2
LEAN

nix develop -c bash -c '
  cd /tmp/lv-probe
  lean -c Probe.c Probe.lean
  lean -c Probe3.c Probe3.lean
  lean -c Chunk2.c Chunk2.lean
  clang -O1 -S -emit-llvm -I"$(lean --print-prefix)/include" Probe.c  -o ProbeO1.ll
  clang -O1 -S -emit-llvm -I"$(lean --print-prefix)/include" Probe3.c -o Probe3O1.ll
  clang -O3 -S -emit-llvm -I"$(lean --print-prefix)/include" Chunk2.c -o Chunk2O3.ll
'
```

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

`@[noinline]` on `scanNoInline` did not survive into the C or IR: `grep -n
'noinline' Probe.c ProbeO1.ll` and `grep -rn 'NOINLINE\|noinline'
"$(lean --print-prefix)/include/lean"` return nothing. The function remains in
this translation unit only because no other function calls it.

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

## 5. Probe 3: the boundary mechanism

`Chunk2.lean` defines the same pure classifier twice: once as `@[export
leanllvm_classify8]` with a Lean caller `useIt`, once as an opaque
`@[extern "leanllvm_classify8_ext"]` with a Lean caller `useItExt`.

At `-O3`, the exported body is inlined into its caller:

```llvm
define range(i64 0, 144115188075855871) i64 @l_useIt(i64 noundef %0) {
  %2 = xor i64 %0, 3182967604875373612
  %3 = add i64 %2, 9151031864016699135
  %4 = and i64 %0, 36170086419038336
  %5 = xor i64 %4, 36170086419038336
  %6 = and i64 %5, %3
  %7 = shl nuw nsw i64 %6, 1
  ret i64 %7
}
```

There is no call to `leanllvm_classify8`; replacing that symbol would not affect
`l_useIt`. The exported symbol still exists as its own function, so the
translation unit contains two copies of the body.

The extern call survives, because the callee has no body in the unit:

```llvm
define range(i64 0, -1) i64 @l_useItExt(i64 noundef %0) {
  %2 = tail call i64 @leanllvm_classify8_ext(i64 noundef %0) #3
  %3 = shl i64 %2, 1
  ret i64 %3
}
```

The exported function itself is the intended *shape* of a certified candidate:

```llvm
define range(i64 0, -9187201950435737471) i64 @leanllvm_classify8(i64 noundef %0) {
  %2 = xor i64 %0, 3182967604875373612
  %3 = add i64 %2, -72340172838076673
  %4 = and i64 %0, -9187201950435737472
  %5 = xor i64 %4, -9187201950435737472
  %6 = and i64 %5, %3
  ret i64 %6
}
```

Seven instructions, no calls, no memory, stable name. The `range` attribute is
a semantically relevant claim about returned values, not decoration.

## 6. Inventory and consequences

| Observation | Consequence |
|---|---|
| `Nat` indexing pulls in `lean_nat_big_*` and boxing | Keep `Nat` out of the certified unit; use `UInt64`/`USize` explicitly |
| The unit still carries tagged pointers, refcounts, `lean_notify_assert` | "Few external calls" must be restated as a **closed, contract-bound call set** |
| `@[export]` is inlined into same-unit callers at `-O3` | The seam must be `@[extern]` (opaque), or the installation must run before inlining |
| `@[noinline]` has no C/IR effect | Do not use it as the boundary mechanism |
| The extern call survives at `-O3` without LTO | First seam: an opaque `@[extern]` with a pure signature |
| Attributes (`range`, `noundef`, `nonnull`, `noalias`) and `!tbaa`/`!prof` are present | Artifact fidelity must bind/recompute/drop them, not only hash the bytes |
| `target triple` and `target datalayout` are present | The manifest must bind them; a candidate compiled for another target is not a replacement |

For the programme:

- **M0** should end with a declared seam and a demonstration that the seam
  survives `-O3`, not merely that a function exists.
- **M1** feature list must add tagged-pointer arithmetic, refcount header
  loads/stores, attributes and metadata to the inventory.
- **M2** can certify a pure chunk function with no heap relation; the memory
  loop stays outside the first certificate.
- **M3** needs a post-installation check that no inlined copy of the baseline
  body remains in the unit or binary. Deleting or replacing the symbol is not
  sufficient when the body was inlined.

## 7. Adjusted first work package

1. **Select the seam.** Declare the recogniser `@[extern "leanllvm_recognise"]`
   with a pure signature (for the first slice `UInt64 → UInt64`); verify the
   call is still a call at `-O3` and identify every call site.
2. **Identity replacement.** Build a baseline, install a byte-identical
   candidate at the seam, rebuild, run. Confirm the installed body is the one
   executed (no inlined baseline copy).
3. **First parity certificate.** Prove the scalar SWAR chunk equals its
   specification, install a structurally different chunk (unrolled or vector),
   and measure. This exercises the checker, installer and manifest without
   calls or heap relations.
4. **Then the memory-using loop** of the programme's M4, where the heap
   relation and the runtime-call contracts enter.

## 8. Limits

- One toolchain (`Lean v4.35.0-rc3`, clang 21.1.8), one target
  (`x86_64-unknown-linux-gnu`), one probe family, no benchmark.
- The observations are about IR shape, not speed.
- LTO was not enabled. With LTO, an extern whose definition is in another
  object can be inlined; the programme's "interpose before aggressive
  inlining" applies, or the definition must be marked `noinline` in the
  candidate object.
- `lean -c` emits one C file per module; cross-module callers see the symbol,
  same-module callers may see the inlined body. Both cases need checking.
- The `initialize_*` declarations are module initialisation, not the hot path;
  they are listed for completeness, not as an obstacle.

## 9. Open questions

- Which call sites in a real application actually reach the seam? Inspect the
  emitted C and IR of the selected app, not only the probe.
- Is the chosen signature raw (`UInt64 → UInt64`) or pointer-plus-length? The
  latter brings bounds and memory into the certificate immediately.
- Does the candidate need to reproduce the baseline's `range` attribute? If
  not, it must be dropped; keeping it without a proof is unsound.
- How will the installer detect an inlined baseline copy? Symbol replacement
  alone is insufficient; the acceptance check needs an IR/binary comparison.
