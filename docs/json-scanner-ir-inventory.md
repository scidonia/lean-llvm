# IR inventory — JSON structural recogniser

Spike for J0's "inventory the actual emitted IR before committing to a
semantics subset". Source and commands are reproducible; the scratch lives
outside the repository (`/tmp/jsonscan-spike`).

## What was compiled

A 32-byte block recogniser: load 32 bytes, compare against `" \ : , { } [ ]`,
OR the lane masks, extract one bit per lane.

* **Variant A** — explicit `_mm256_*` intrinsics (`cmpeq_epi8`, `or_si256`,
  `loadu_si256`, `movemask_epi8`).
* **Variant B** — a portable loop with no intrinsics, left to the vectoriser.

```
clang -O2 -mavx2 -S -emit-llvm scan.c -o scan_O2.ll      # 173 lines
clang -O0 -mavx2 -S -emit-llvm scan.c -o scan_O0.ll      # 1731 lines
```

## Variant A (intrinsics) — emitted body, verbatim shape

```llvm
%11 = load <32 x i8>, ptr %10, align 1
%12 = icmp eq <32 x i8> %11, splat (i8 34)      ; ×8, one per structural byte
%14 = or <32 x i1> %12, %13                     ; ×7
%27 = bitcast <32 x i1> %26 to i32              ; the mask extraction
%28 = or i32 %8, %27
%29 = add i64 %7, 32
%30 = icmp ugt i64 %29, %1
```

**No target intrinsics.** `_mm256_movemask_epi8` lowered to a **bitcast of
`<32 x i1>` to `i32`**, and every `_mm256_cmpeq_epi8`/`_mm256_or_si256`
lowered to portable vector `icmp`/`or`. The whole body uses:

|Construct|Count|
|---|---|
|`load <32 x i8>` with `align 1`|1|
|`icmp eq <32 x i8>`, splat operand|8|
|`or <32 x i1>`|7|
|`bitcast <32 x i1> to i32`|1|
|scalar `or`/`add`/`icmp`/`phi`/`br`/`getelementptr`|the rest|

Vector types seen: `<32 x i8>`, `<32 x i1>`.

## Variant B (portable, auto-vectorised) — what the vectoriser chose

```llvm
%23 = load <8 x i8>, ptr %22, align 1
%24 = icmp eq <8 x i8> %23, splat (i8 123)
%28 = and <8 x i8> %23, splat (i8 -33)          ; case folding
%32 = icmp ult <8 x i8> %31, splat (i8 2)
%37 = shl nuw <8 x i32> splat (i32 1), %21
%38 = select <8 x i1> %36, <8 x i32> %37, <8 x i32> zeroinitializer
%44 = tail call i32 @llvm.vector.reduce.or.v8i32(<8 x i32> %39)
```

Vector types: `<8 x i8>`, `<8 x i1>`, `<8 x i32>`. Intrinsics:
`llvm.vector.reduce.or.v8i32`, `llvm.umax.i64`, `llvm.umin.i64`. A scalar tail
load handles the remainder.

## Consequences

1. **The recogniser needs no AVX2 intrinsic, and no shuffle.** Target-specific
   code is confined to the backend, which the programme already trusts, so the
   "AVX2" backend choice affects performance and the trusted compiler, not the
   semantics.
2. **The minimal vector fragment for the intrinsic-style kernel** is:
   * a vector type `vec n ty` (`i8`, `i1`, `i32`),
   * vector constants (`splat`),
   * vector `load`/`store` with an alignment,
   * lane-wise `icmp eq` yielding `vec n i1`,
   * lane-wise `or`/`and` on `vec n i1` and on integer vectors,
   * `bitcast vec n i1 → iN` (the mask extraction),
   * lane-wise `shl`/`lshr`, `trunc`, and `select` on a vector condition only if
     the candidate uses the portable form.
3. **Cross-byte logic can stay scalar.** String state is a prefix-XOR over the
   32-bit quote mask (`x ^= x<<1; x ^= x<<2; x ^= x<<4; x ^= x<<8; x ^= x<<16`),
   and structural parity is a prefix-sum on the mask, both on `i32`/`i64` with
   the ordinary scalar model. That keeps the vector fragment confined to
   classification, which is the part SIMD is actually for.
4. **What is genuinely absent from the model today** (`Ty` has no vector
   constructor): the vector type itself, vector constants, vector loads/stores,
   lane-wise comparisons producing `i1` lanes, lane-wise bitwise operations, and
   the `bitcast` from a predicate vector to an integer. Nothing about shuffles,
   gathers, saturation or target intrinsics is required by this kernel.

## Not yet inventoried

The stateful scanner (`inString` carry, escape-run carry, UTF-8 continuation
state) and the index-emission path will add scalar work and possibly one
additional vector operation for prefix scans. The instrument for that inventory
is the same: compile the candidate, list the opcodes, then extend the fragment
by exactly what appears.
