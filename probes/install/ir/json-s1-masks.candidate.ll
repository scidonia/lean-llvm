; The stage-1 classification mask unit as emitted, in the fragment the parser
; reads.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-s1-masks.sh
;
; from kernel/json/s1_block.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to the `define` block of @leanllvm_json_s1_masks.
; `-fno-discard-value-names` is a naming flag: it names values and labels the
; entry block, which the parser requires, and the capture checks that it changes
; no instruction by emitting the source with and without it and comparing the
; two texts with every register name replaced by one placeholder.
;
; The three parameters are written %p, %c and %o.  The capture reads their
; emitted names from the header and substitutes them; it refuses an emission
; whose parameter count is not three.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-s1-masks.strip.tsv; rewritten rather than removed — the parameter names
; and two `poison` lanes — in json-s1-masks.rewrites.tsv.  The lines removed
; from the module carried:
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: readwrite) uwtable "frame-pointer"="all" "min-legal-vector-width"="256" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
;   attributes #1 = { mustprogress nocallback nofree nosync nounwind willreturn memory(none) }
;   attributes #2 = { mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none) }
;
; The fixture's own opcodes and call targets are in json-s1-masks.inventory.
define void @leanllvm_json_s1_masks(ptr %p, ptr %c, ptr %o) {
entry:
  %0 = load <4 x i64>, ptr %p
  %add.ptr = getelementptr inbounds i8, ptr %p, i64 32
  %1 = load <4 x i64>, ptr %add.ptr
  %2 = bitcast <4 x i64> %0 to <32 x i8>
  %3 = bitcast <4 x i64> %1 to <32 x i8>
  %4 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %5 = bitcast <8 x i64> %4 to <64 x i8>
  %6 = icmp eq <64 x i8> %5, splat (i8 34)
  %or.i = bitcast <64 x i1> %6 to i64
  %cmp.i54.i = icmp eq <32 x i8> %2, splat (i8 92)
  %7 = bitcast <32 x i1> %cmp.i54.i to i32
  %conv9.i = zext i32 %7 to i64
  %cmp.i52.i = icmp eq <32 x i8> %3, splat (i8 92)
  %8 = bitcast <32 x i1> %cmp.i52.i to i32
  %conv12.i = zext i32 %8 to i64
  %shl13.i = shl i64 %conv12.i, 32
  %or14.i = or i64 %shl13.i, %conv9.i
  %9 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %10 = bitcast <8 x i64> %9 to <64 x i8>
  %11 = icmp ult <64 x i8> %10, splat (i8 32)
  %12 = bitcast <4 x i64> %0 to <16 x i16>
  %13 = lshr <16 x i16> %12, splat (i16 4)
  %14 = and <32 x i8> %2, splat (i8 15)
  %15 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %14)
  %16 = bitcast <16 x i16> %13 to <32 x i8>
  %17 = and <32 x i8> %16, splat (i8 15)
  %18 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %17)
  %and.i2831.i.i.i = and <32 x i8> %18, %15
  %19 = and <32 x i8> %and.i2831.i.i.i, splat (i8 63)
  %cmp.i25.i.i.i = icmp eq <32 x i8> %19, zeroinitializer
  %20 = bitcast <32 x i1> %cmp.i25.i.i.i to i32
  %not.i.i.i = xor i32 %20, -1
  %cmp.i.i.i.i = icmp ult <32 x i8> %and.i2831.i.i.i, splat (i8 64)
  %21 = bitcast <32 x i1> %cmp.i.i.i.i to i32
  %not18.i.i.i = xor i32 %21, -1
  %22 = bitcast <4 x i64> %1 to <16 x i16>
  %23 = lshr <16 x i16> %22, splat (i16 4)
  %24 = and <32 x i8> %3, splat (i8 15)
  %25 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %24)
  %26 = bitcast <16 x i16> %23 to <32 x i8>
  %27 = and <32 x i8> %26, splat (i8 15)
  %28 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %27)
  %and.i2831.i6.i.i = and <32 x i8> %28, %25
  %29 = and <32 x i8> %and.i2831.i6.i.i, splat (i8 63)
  %cmp.i25.i7.i.i = icmp eq <32 x i8> %29, zeroinitializer
  %30 = bitcast <32 x i1> %cmp.i25.i7.i.i to i32
  %not.i8.i.i = xor i32 %30, -1
  %cmp.i.i9.i.i = icmp ult <32 x i8> %and.i2831.i6.i.i, splat (i8 64)
  %31 = bitcast <32 x i1> %cmp.i.i9.i.i to i32
  %not18.i10.i.i = xor i32 %31, -1
  %conv.i.i = zext i32 %not18.i.i.i to i64
  %conv1.i.i = zext i32 %not18.i10.i.i to i64
  %shl.i.i = shl i64 %conv1.i.i, 32
  %or.i.i = or i64 %shl.i.i, %conv.i.i
  %conv2.i.i = zext i32 %not.i.i.i to i64
  %conv3.i.i = zext i32 %not.i8.i.i to i64
  %shl4.i.i = shl i64 %conv3.i.i, 32
  %or5.i.i = or i64 %shl4.i.i, %conv2.i.i
  %esc_ppar.i = getelementptr inbounds i8, ptr %c, i64 8
  %shl.i61.i = shl i64 %or14.i, 1
  %32 = load i64, ptr %c
  %or.i62.i = or i64 %shl.i61.i, %32
  %not.i.i = xor i64 %or.i62.i, -1
  %and.i.i = and i64 %or14.i, %not.i.i
  %and1.i.i = and i64 %conv9.i, 1
  %and2.i.i = and i64 %32, %and1.i.i
  %or3.i.i = or i64 %and.i.i, %and2.i.i
  %shr.i.i = lshr i64 %or14.i, 1
  %not4.i.i = xor i64 %shr.i.i, -1
  %and5.i.i = and i64 %or14.i, %not4.i.i
  %shl6.i.i = shl i64 %and5.i.i, 1
  %33 = load i64, ptr %esc_ppar.i
  %and7.i.i = and i64 %33, %32
  %xor.i.i = xor i64 %and7.i.i, 6148914691236517205
  %34 = tail call i64 @llvm.x86.bmi.pext.64(i64 %xor.i.i, i64 %or3.i.i)
  %35 = tail call i64 @llvm.x86.bmi.pext.64(i64 6148914691236517205, i64 %and5.i.i)
  %36 = xor i64 %34, %35
  %not10.i.i = xor i64 %36, -1
  %37 = tail call i64 @llvm.x86.bmi.pdep.64(i64 %not10.i.i, i64 %shl6.i.i)
  %cmp.i63.i = icmp ne i64 %or14.i, -1
  %tobool.not.i.i = icmp eq i64 %32, 0
  %or.cond.i.i = select i1 %cmp.i63.i, i1 true, i1 %tobool.not.i.i
  %cond24.i.i = select i1 %or.cond.i.i, i64 0, i64 %33
  %not17.i.i = xor i64 %or14.i, -1
  %38 = tail call i64 @llvm.ctlz.i64(i64 %not17.i.i, i1 false)
  %shr16.i.i = lshr i64 %conv12.i, 31
  %not12.i.i = xor i64 %and1.i.i, -1
  %39 = and i64 %32, %not12.i.i
  %and14.i.i = and i64 %39, %33
  %or15.i.i = or i64 %37, %and14.i.i
  %xor25.i.i = xor i64 %cond24.i.i, %38
  %and26.i.i = and i64 %xor25.i.i, %shr16.i.i
  store i64 %and26.i.i, ptr %esc_ppar.i
  store i64 %shr16.i.i, ptr %c
  %not.i = xor i64 %or15.i.i, -1
  %and.i = and i64 %or.i, %not.i
  %vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0
  %40 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i = extractelement <2 x i64> %40, i64 0
  %im_carry.i = getelementptr inbounds i8, ptr %c, i64 16
  %41 = load i64, ptr %im_carry.i
  %xor.i = xor i64 %vecext.i.i.i, %41
  %shr.i = ashr i64 %xor.i, 63
  store i64 %shr.i, ptr %im_carry.i
  store i64 %and.i, ptr %o
  %delim = getelementptr inbounds i8, ptr %o, i64 8
  store i64 %or5.i.i, ptr %delim
  %in_string = getelementptr inbounds i8, ptr %o, i64 16
  store i64 %xor.i, ptr %in_string
  %ws2 = getelementptr inbounds i8, ptr %o, i64 24
  store i64 %or.i.i, ptr %ws2
  %backslash = getelementptr inbounds i8, ptr %o, i64 32
  store i64 %or14.i, ptr %backslash
  %ctl3 = getelementptr inbounds i8, ptr %o, i64 40
  store <64 x i1> %11, ptr %ctl3
  ret void
}
