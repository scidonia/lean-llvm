; probes/install/build/Candidate.c, emitted with
;
;   clang -S -emit-llvm -O0 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Candidate.c
;
; and reduced to the verbatim `define` blocks of @leanllvm_comma_mask8 and
; @l_commaMask8_go.  Nothing inside the blocks is changed.  The exported
; function only calls @l_commaMask8_go, and the loop runs on a boxed `Nat`
; counter: `lean_nat_dec_lt`, `lean_nat_mul`, `lean_nat_add`, `lean_dec`,
; `lean_unsigned_to_nat`, closed by `phi` over a `lean_object*`.  That is
; outside the fragment `LeanLLVM.Semantics` models on three counts (calls,
; heap objects, `phi`), so this emission is not parseable and candidate.ll is
; the lane-by-lane transcription in candidate_lanes.c instead.
define i64 @leanllvm_comma_mask8(i64 noundef %0) #0 {
  %2 = alloca i64, align 8
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  store i64 %0, ptr %2, align 8
  br label %6

6:                                                ; preds = %1
  %7 = call ptr @lean_unsigned_to_nat(i32 noundef 0)
  store ptr %7, ptr %3, align 8
  store i64 0, ptr %4, align 8
  %8 = load i64, ptr %2, align 8
  %9 = load ptr, ptr %3, align 8
  %10 = load i64, ptr %4, align 8
  %11 = call i64 @l_commaMask8_go(i64 noundef %8, ptr noundef %9, i64 noundef %10)
  store i64 %11, ptr %5, align 8
  %12 = load i64, ptr %5, align 8
  ret i64 %12
}

define i64 @l_commaMask8_go(i64 noundef %0, ptr noundef %1, i64 noundef %2) #0 {
  %4 = alloca i64, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca ptr, align 8
  %9 = alloca i8, align 1
  %10 = alloca ptr, align 8
  %11 = alloca i64, align 8
  %12 = alloca i64, align 8
  %13 = alloca i64, align 8
  %14 = alloca i64, align 8
  %15 = alloca i64, align 8
  %16 = alloca i8, align 1
  %17 = alloca i64, align 8
  %18 = alloca i64, align 8
  %19 = alloca i64, align 8
  %20 = alloca ptr, align 8
  %21 = alloca ptr, align 8
  store i64 %0, ptr %4, align 8
  store ptr %1, ptr %5, align 8
  store i64 %2, ptr %6, align 8
  br label %22

22:                                               ; preds = %62, %3
  %23 = call ptr @lean_unsigned_to_nat(i32 noundef 8)
  store ptr %23, ptr %8, align 8
  %24 = load ptr, ptr %5, align 8
  %25 = load ptr, ptr %8, align 8
  %26 = call zeroext i8 @lean_nat_dec_lt(ptr noundef %24, ptr noundef %25)
  store i8 %26, ptr %9, align 1
  %27 = load i8, ptr %9, align 1
  %28 = zext i8 %27 to i32
  %29 = icmp eq i32 %28, 0
  br i1 %29, label %30, label %33

30:                                               ; preds = %22
  %31 = load ptr, ptr %5, align 8
  call void @lean_dec(ptr noundef %31)
  %32 = load i64, ptr %6, align 8
  ret i64 %32

33:                                               ; preds = %22
  %34 = load ptr, ptr %8, align 8
  %35 = load ptr, ptr %5, align 8
  %36 = call ptr @lean_nat_mul(ptr noundef %34, ptr noundef %35)
  store ptr %36, ptr %10, align 8
  %37 = load ptr, ptr %10, align 8
  %38 = call i64 @lean_uint64_of_nat(ptr noundef %37)
  store i64 %38, ptr %11, align 8
  %39 = load ptr, ptr %10, align 8
  call void @lean_dec(ptr noundef %39)
  %40 = load i64, ptr %4, align 8
  %41 = load i64, ptr %11, align 8
  %42 = call i64 @lean_uint64_shift_right(i64 noundef %40, i64 noundef %41)
  store i64 %42, ptr %12, align 8
  store i64 255, ptr %13, align 8
  %43 = load i64, ptr %12, align 8
  %44 = load i64, ptr %13, align 8
  %45 = call i64 @lean_uint64_land(i64 noundef %43, i64 noundef %44)
  store i64 %45, ptr %14, align 8
  store i64 44, ptr %15, align 8
  %46 = load i64, ptr %14, align 8
  %47 = load i64, ptr %15, align 8
  %48 = call zeroext i8 @lean_uint64_dec_eq(i64 noundef %46, i64 noundef %47)
  store i8 %48, ptr %16, align 1
  %49 = load i8, ptr %16, align 1
  %50 = zext i8 %49 to i32
  %51 = icmp eq i32 %50, 0
  br i1 %51, label %52, label %54

52:                                               ; preds = %33
  %53 = load i64, ptr %6, align 8
  store i64 %53, ptr %7, align 8
  br label %62

54:                                               ; preds = %33
  store i64 128, ptr %17, align 8
  %55 = load i64, ptr %17, align 8
  %56 = load i64, ptr %11, align 8
  %57 = call i64 @lean_uint64_shift_left(i64 noundef %55, i64 noundef %56)
  store i64 %57, ptr %18, align 8
  %58 = load i64, ptr %6, align 8
  %59 = load i64, ptr %18, align 8
  %60 = call i64 @lean_uint64_lor(i64 noundef %58, i64 noundef %59)
  store i64 %60, ptr %19, align 8
  %61 = load i64, ptr %19, align 8
  store i64 %61, ptr %7, align 8
  br label %62

62:                                               ; preds = %54, %52
  %63 = call ptr @lean_unsigned_to_nat(i32 noundef 1)
  store ptr %63, ptr %20, align 8
  %64 = load ptr, ptr %5, align 8
  %65 = load ptr, ptr %20, align 8
  %66 = call ptr @lean_nat_add(ptr noundef %64, ptr noundef %65)
  store ptr %66, ptr %21, align 8
  %67 = load ptr, ptr %5, align 8
  call void @lean_dec(ptr noundef %67)
  %68 = load ptr, ptr %21, align 8
  store ptr %68, ptr %5, align 8
  %69 = load i64, ptr %7, align 8
  store i64 %69, ptr %6, align 8
  br label %22
}
