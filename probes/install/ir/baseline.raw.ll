; probes/install/build/Baseline.c, emitted with
;
;   clang -S -emit-llvm -O0 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Baseline.c
;
; and reduced to the verbatim `define` block of @leanllvm_comma_mask8.
; Nothing inside the block is changed.  The calls are to the `UInt64`
; primitives that `lean.h` defines `static inline`; `LeanLLVM.Semantics` has no
; `call`, so this emission is not parseable.  baseline.ll is the same function
; emitted with those primitives inlined, which is what a production build does.
define i64 @leanllvm_comma_mask8(i64 noundef %0) #0 {
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i64, align 8
  %10 = alloca i64, align 8
  %11 = alloca i64, align 8
  store i64 %0, ptr %2, align 8
  br label %12

12:                                               ; preds = %1
  store i64 3182967604875373612, ptr %3, align 8
  %13 = load i64, ptr %2, align 8
  %14 = load i64, ptr %3, align 8
  %15 = call i64 @lean_uint64_xor(i64 noundef %13, i64 noundef %14)
  store i64 %15, ptr %4, align 8
  store i64 9187201950435737471, ptr %5, align 8
  %16 = load i64, ptr %4, align 8
  %17 = load i64, ptr %5, align 8
  %18 = call i64 @lean_uint64_land(i64 noundef %16, i64 noundef %17)
  store i64 %18, ptr %6, align 8
  %19 = load i64, ptr %6, align 8
  %20 = load i64, ptr %5, align 8
  %21 = call i64 @lean_uint64_add(i64 noundef %19, i64 noundef %20)
  store i64 %21, ptr %7, align 8
  %22 = load i64, ptr %7, align 8
  %23 = load i64, ptr %4, align 8
  %24 = call i64 @lean_uint64_lor(i64 noundef %22, i64 noundef %23)
  store i64 %24, ptr %8, align 8
  %25 = load i64, ptr %8, align 8
  %26 = call i64 @lean_uint64_complement(i64 noundef %25)
  store i64 %26, ptr %9, align 8
  store i64 -9187201950435737472, ptr %10, align 8
  %27 = load i64, ptr %9, align 8
  %28 = load i64, ptr %10, align 8
  %29 = call i64 @lean_uint64_land(i64 noundef %27, i64 noundef %28)
  store i64 %29, ptr %11, align 8
  %30 = load i64, ptr %11, align 8
  ret i64 %30
}
