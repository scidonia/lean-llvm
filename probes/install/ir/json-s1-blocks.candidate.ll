; The contracted stage-1 block unit as emitted, in the fragment the parser
; reads.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-s1-blocks.sh
;
; from kernel/json/s1_blocks.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to the `define` block of @leanllvm_json_s1_blocks.
; `-fno-discard-value-names` is a naming flag: it names values and labels the
; entry block, which the parser requires, and the capture checks that it changes
; no instruction by emitting the source with and without it and comparing the
; two texts with every register name replaced by one placeholder.
;
; The seven parameters keep the source's names (%b, %n, %ent, %xp, %nxp,
; %xcarry, %arm).  The capture reads their emitted names and refuses an emission
; whose parameter count is not seven; it applies no rename.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-s1-blocks.strip.tsv; rewritten rather than removed — two `poison` lanes —
; in json-s1-blocks.rewrites.tsv.  The lines removed from the module carried:
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   attributes #0 = { nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="256" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
;   attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
;   attributes #2 = { mustprogress nocallback nofree nosync nounwind willreturn memory(none) }
;   attributes #3 = { mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none) }
;   attributes #4 = { nounwind }
;
; The fixture's own opcodes and call targets are in json-s1-blocks.inventory.
define i64 @leanllvm_json_s1_blocks(ptr %b, i64 %n, ptr %ent, ptr %xp, ptr %nxp, ptr %xcarry, i64 %arm) {
entry:
  %shr = lshr i64 %n, 6
  %and = and i64 %n, 63
  %0 = trunc i64 %arm to i32
  %1 = lshr i32 %0, 2
  %conv = and i32 %1, 1
  %cmp4280.not = icmp ult i64 %n, 64
  br i1 %cmp4280.not, label %for.cond.cleanup, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  %tobool = icmp eq i32 %conv, 0
  %and27 = and i64 %arm, 2
  %tobool28.not = icmp eq i64 %and27, 0
  br label %for.body

for.cond.cleanup.loopexit:                        ; preds = %if.end31
  %2 = icmp ne i32 %5, 0
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %entry
  %st.sroa.11.0.lcssa = phi i64 [ 0, %entry ], [ %shr.i, %for.cond.cleanup.loopexit ]
  %st.sroa.7.0.lcssa = phi i64 [ 0, %entry ], [ %conv13.i.i, %for.cond.cleanup.loopexit ]
  %st.sroa.0.0.lcssa = phi i64 [ 0, %entry ], [ %shr.i.i, %for.cond.cleanup.loopexit ]
  %prev_ascii.0.lcssa = phi i1 [ true, %entry ], [ %2, %for.cond.cleanup.loopexit ]
  %u8k.0.lcssa = phi <4 x i64> [ zeroinitializer, %entry ], [ %u8k.1, %for.cond.cleanup.loopexit ]
  %ascii.0.lcssa = phi <4 x i64> [ zeroinitializer, %entry ], [ %or.i169, %for.cond.cleanup.loopexit ]
  %prevS.0.lcssa = phi i64 [ 0, %entry ], [ %shr22, %for.cond.cleanup.loopexit ]
  %tobool32.not = icmp eq i64 %and, 0
  br i1 %tobool32.not, label %if.end83, label %if.then33

for.body:                                         ; preds = %for.body.lr.ph, %if.end31
  %prevS.0288 = phi i64 [ 0, %for.body.lr.ph ], [ %shr22, %if.end31 ]
  %ascii.0287 = phi <4 x i64> [ zeroinitializer, %for.body.lr.ph ], [ %or.i169, %if.end31 ]
  %u8k.0286 = phi <4 x i64> [ zeroinitializer, %for.body.lr.ph ], [ %u8k.1, %if.end31 ]
  %prev_ascii.0285 = phi i32 [ 1, %for.body.lr.ph ], [ %5, %if.end31 ]
  %i.0284 = phi i64 [ 0, %for.body.lr.ph ], [ %inc, %if.end31 ]
  %st.sroa.0.0283 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i.i, %if.end31 ]
  %st.sroa.7.0282 = phi i64 [ 0, %for.body.lr.ph ], [ %conv13.i.i, %if.end31 ]
  %st.sroa.11.0281 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i, %if.end31 ]
  %shl = shl i64 %i.0284, 6
  %add.ptr = getelementptr inbounds i8, ptr %b, i64 %shl
  %3 = load <4 x i64>, ptr %add.ptr
  %add.ptr7 = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %4 = load <4 x i64>, ptr %add.ptr7
  %or.i170 = or <4 x i64> %4, %3
  %5 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i170, <4 x i64> splat (i64 -9187201950435737472))
  %or.i169 = or <4 x i64> %or.i170, %ascii.0287
  %6 = bitcast <4 x i64> %3 to <32 x i8>
  %7 = bitcast <4 x i64> %4 to <32 x i8>
  %8 = shufflevector <4 x i64> %3, <4 x i64> %4, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %9 = bitcast <8 x i64> %8 to <64 x i8>
  %10 = icmp eq <64 x i8> %9, splat (i8 34)
  %or.i171 = bitcast <64 x i1> %10 to i64
  %cmp.i39.i = icmp eq <32 x i8> %6, splat (i8 92)
  %11 = bitcast <32 x i1> %cmp.i39.i to i32
  %conv9.i = zext i32 %11 to i64
  %cmp.i.i = icmp eq <32 x i8> %7, splat (i8 92)
  %12 = bitcast <32 x i1> %cmp.i.i to i32
  %conv12.i = zext i32 %12 to i64
  %shl13.i = shl i64 %conv12.i, 32
  %or14.i = or i64 %shl13.i, %conv9.i
  %and.i.i = and i64 %st.sroa.0.0283, %st.sroa.7.0282
  %shl.i.i = shl i64 %or14.i, 1
  %not.i.i = xor i64 %shl.i.i, -1
  %and1.i.i = and i64 %or14.i, %not.i.i
  %xor.i.i = xor i64 %and.i.i, 6148914691236517205
  %and2.i.i = and i64 %and1.i.i, %xor.i.i
  %xor3.i.i = xor i64 %and2.i.i, %and1.i.i
  %not4.i.i = xor i64 %or14.i, -1
  %add.i.i = add i64 %and2.i.i, %or14.i
  %add5.i.i = add i64 %xor3.i.i, %or14.i
  %and6.i.i = and i64 %not4.i.i, -6148914691236517206
  %and7.i.i = and i64 %and6.i.i, %add.i.i
  %and8.i.i = and i64 %not4.i.i, 6148914691236517205
  %and9.i.i = and i64 %and8.i.i, %add5.i.i
  %and11.i.i = and i64 %and.i.i, %not4.i.i
  %or.i.i = or i64 %and7.i.i, %and11.i.i
  %or12.i.i = or i64 %or.i.i, %and9.i.i
  %cmp.i45.i = icmp ult i64 %add5.i.i, %or14.i
  %conv13.i.i = zext i1 %cmp.i45.i to i64
  %shr.i.i = lshr i64 %conv12.i, 31
  %not.i = xor i64 %or12.i.i, -1
  %and.i = and i64 %or.i171, %not.i
  %13 = bitcast <4 x i64> %3 to <16 x i16>
  %14 = lshr <16 x i16> %13, splat (i16 4)
  %15 = and <32 x i8> %6, splat (i8 15)
  %16 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %15)
  %17 = bitcast <16 x i16> %14 to <32 x i8>
  %18 = and <32 x i8> %17, splat (i8 15)
  %19 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %18)
  %and.i2326.i.i = and <32 x i8> %19, %16
  %20 = and <32 x i8> %and.i2326.i.i, splat (i8 63)
  %cmp.i21.i.i = icmp eq <32 x i8> %20, zeroinitializer
  %21 = bitcast <32 x i1> %cmp.i21.i.i to i32
  %not.i46.i = xor i32 %21, -1
  %22 = bitcast <4 x i64> %4 to <16 x i16>
  %23 = lshr <16 x i16> %22, splat (i16 4)
  %24 = and <32 x i8> %7, splat (i8 15)
  %25 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %24)
  %26 = bitcast <16 x i16> %23 to <32 x i8>
  %27 = and <32 x i8> %26, splat (i8 15)
  %28 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %27)
  %and.i2326.i47.i = and <32 x i8> %28, %25
  %29 = and <32 x i8> %and.i2326.i47.i, splat (i8 63)
  %cmp.i21.i48.i = icmp eq <32 x i8> %29, zeroinitializer
  %30 = bitcast <32 x i1> %cmp.i21.i48.i to i32
  %not.i49.i = xor i32 %30, -1
  %conv16.i = zext i32 %not.i46.i to i64
  %conv17.i = zext i32 %not.i49.i to i64
  %shl18.i = shl i64 %conv17.i, 32
  %or19.i = or i64 %shl18.i, %conv16.i
  %31 = shufflevector <32 x i8> %and.i2326.i.i, <32 x i8> %and.i2326.i47.i, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %32 = icmp eq <64 x i8> %31, zeroinitializer
  %or23.i = bitcast <64 x i1> %32 to i64
  %vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0
  %33 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i = extractelement <2 x i64> %33, i64 0
  %xor.i = xor i64 %vecext.i.i.i, %st.sroa.11.0281
  %shr.i = ashr i64 %xor.i, 63
  %not13 = xor i64 %xor.i, -1
  %34 = or i64 %and.i, %xor.i
  %35 = xor i64 %34, -1
  %and14 = and i64 %or23.i, %35
  %and16 = and i64 %or19.i, %not13
  %shl17 = shl i64 %and14, 1
  %or18 = or i64 %shl17, %prevS.0288
  %not19 = xor i64 %or18, -1
  %and20 = and i64 %and14, %not19
  %36 = or i64 %and16, %and20
  %or21 = or i64 %36, %and.i
  %shr22 = lshr i64 %and14, 63
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.0284
  store i64 %or21, ptr %arrayidx
  %tobool23 = icmp ne i32 %5, 0
  %tobool24 = icmp ne i32 %prev_ascii.0285, 0
  %37 = and i1 %tobool24, %tobool23
  %or.cond107 = select i1 %tobool, i1 %37, i1 false
  br i1 %or.cond107, label %if.end, label %if.then

if.then:                                          ; preds = %for.body
  %add.ptr.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -1
  %38 = load <4 x i64>, ptr %add.ptr.i.i
  %add.ptr3.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -2
  %39 = load <32 x i8>, ptr %add.ptr3.i.i
  %add.ptr5.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -3
  %40 = load <32 x i8>, ptr %add.ptr5.i.i
  %41 = bitcast <4 x i64> %38 to <32 x i8>
  %42 = and <32 x i8> %41, splat (i8 15)
  %43 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %42)
  %44 = bitcast <4 x i64> %38 to <16 x i16>
  %45 = lshr <16 x i16> %44, splat (i16 4)
  %46 = bitcast <16 x i16> %45 to <32 x i8>
  %47 = and <32 x i8> %46, splat (i8 15)
  %48 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %47)
  %and.i3741.i.i = and <32 x i8> %48, %43
  %49 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %18)
  %and.i3542.i.i = and <32 x i8> %and.i3741.i.i, %49
  %and.i35.i.i = bitcast <32 x i8> %and.i3542.i.i to <4 x i64>
  %elt.sat.i40.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %39, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %40, <32 x i8> splat (i8 112))
  %or.i43.i.i = or <32 x i8> %elt.sat.i.i.i, %elt.sat.i40.i.i
  %or.i.i.i = bitcast <32 x i8> %or.i43.i.i to <4 x i64>
  %and.i.i.i = and <4 x i64> %or.i.i.i, splat (i64 -9187201950435737472)
  %xor.i.i.i = xor <4 x i64> %and.i.i.i, %and.i35.i.i
  %add.ptr.i4.i = getelementptr inbounds i8, ptr %add.ptr, i64 31
  %50 = load <4 x i64>, ptr %add.ptr.i4.i
  %add.ptr3.i5.i = getelementptr inbounds i8, ptr %add.ptr, i64 30
  %51 = load <32 x i8>, ptr %add.ptr3.i5.i
  %add.ptr5.i6.i = getelementptr inbounds i8, ptr %add.ptr, i64 29
  %52 = load <32 x i8>, ptr %add.ptr5.i6.i
  %53 = bitcast <4 x i64> %50 to <32 x i8>
  %54 = and <32 x i8> %53, splat (i8 15)
  %55 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %54)
  %56 = bitcast <4 x i64> %50 to <16 x i16>
  %57 = lshr <16 x i16> %56, splat (i16 4)
  %58 = bitcast <16 x i16> %57 to <32 x i8>
  %59 = and <32 x i8> %58, splat (i8 15)
  %60 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %59)
  %and.i3741.i7.i = and <32 x i8> %60, %55
  %61 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %27)
  %and.i3542.i8.i = and <32 x i8> %and.i3741.i7.i, %61
  %and.i35.i9.i = bitcast <32 x i8> %and.i3542.i8.i to <4 x i64>
  %elt.sat.i40.i10.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %51, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %52, <32 x i8> splat (i8 112))
  %or.i43.i12.i = or <32 x i8> %elt.sat.i.i11.i, %elt.sat.i40.i10.i
  %or.i.i13.i = bitcast <32 x i8> %or.i43.i12.i to <4 x i64>
  %and.i.i14.i = and <4 x i64> %or.i.i13.i, splat (i64 -9187201950435737472)
  %xor.i.i15.i = xor <4 x i64> %and.i.i14.i, %and.i35.i9.i
  %62 = or <4 x i64> %xor.i.i.i, %xor.i.i15.i
  %or.i168 = or <4 x i64> %62, %u8k.0286
  br label %if.end

if.end:                                           ; preds = %for.body, %if.then
  %u8k.1 = phi <4 x i64> [ %u8k.0286, %for.body ], [ %or.i168, %if.then ]
  br i1 %tobool28.not, label %if.end31, label %if.then29

if.then29:                                        ; preds = %if.end
  %63 = shufflevector <4 x i64> %3, <4 x i64> %4, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %64 = bitcast <8 x i64> %63 to <64 x i8>
  %65 = icmp ult <64 x i8> %64, splat (i8 32)
  %or.i176 = bitcast <64 x i1> %65 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i, i64 %or.i176, i64 %xor.i, i64 %i.0284, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end31

if.end31:                                         ; preds = %if.then29, %if.end
  %inc = add i64 %i.0284, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.cond.cleanup.loopexit, label %for.body

if.then33:                                        ; preds = %for.cond.cleanup
  %shl35 = and i64 %n, -64
  %add.ptr36 = getelementptr inbounds i8, ptr %b, i64 %shl35
  %66 = load <4 x i64>, ptr %add.ptr36
  %add.ptr40 = getelementptr inbounds i8, ptr %add.ptr36, i64 32
  %67 = load <4 x i64>, ptr %add.ptr40
  %or.i167 = or <4 x i64> %67, %66
  %68 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i167, <4 x i64> splat (i64 -9187201950435737472))
  %or.i166 = or <4 x i64> %or.i167, %ascii.0.lcssa
  %69 = bitcast <4 x i64> %66 to <32 x i8>
  %70 = bitcast <4 x i64> %67 to <32 x i8>
  %71 = shufflevector <4 x i64> %66, <4 x i64> %67, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %72 = bitcast <8 x i64> %71 to <64 x i8>
  %73 = icmp eq <64 x i8> %72, splat (i8 34)
  %or.i182 = bitcast <64 x i1> %73 to i64
  %74 = shufflevector <4 x i64> %66, <4 x i64> %67, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %75 = bitcast <8 x i64> %74 to <64 x i8>
  %76 = icmp eq <64 x i8> %75, splat (i8 92)
  %or14.i188 = bitcast <64 x i1> %76 to i64
  %and.i.i190 = and i64 %st.sroa.0.0.lcssa, %st.sroa.7.0.lcssa
  %shl.i.i191 = shl i64 %or14.i188, 1
  %not.i.i192 = xor i64 %shl.i.i191, -1
  %and1.i.i193 = and i64 %or14.i188, %not.i.i192
  %xor.i.i194 = xor i64 %and.i.i190, 6148914691236517205
  %and2.i.i195 = and i64 %and1.i.i193, %xor.i.i194
  %xor3.i.i196 = xor i64 %and2.i.i195, %and1.i.i193
  %not4.i.i197 = xor i64 %or14.i188, -1
  %add.i.i198 = add i64 %and2.i.i195, %or14.i188
  %add5.i.i199 = add i64 %xor3.i.i196, %or14.i188
  %and6.i.i200 = and i64 %not4.i.i197, -6148914691236517206
  %and7.i.i201 = and i64 %and6.i.i200, %add.i.i198
  %and8.i.i202 = and i64 %not4.i.i197, 6148914691236517205
  %and9.i.i203 = and i64 %and8.i.i202, %add5.i.i199
  %and11.i.i205 = and i64 %and.i.i190, %not4.i.i197
  %or.i.i206 = or i64 %and7.i.i201, %and11.i.i205
  %or12.i.i207 = or i64 %or.i.i206, %and9.i.i203
  %not.i211 = xor i64 %or12.i.i207, -1
  %and.i212 = and i64 %or.i182, %not.i211
  %77 = bitcast <4 x i64> %66 to <16 x i16>
  %78 = lshr <16 x i16> %77, splat (i16 4)
  %79 = and <32 x i8> %69, splat (i8 15)
  %80 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %79)
  %81 = bitcast <16 x i16> %78 to <32 x i8>
  %82 = and <32 x i8> %81, splat (i8 15)
  %83 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %82)
  %and.i2326.i.i213 = and <32 x i8> %83, %80
  %84 = and <32 x i8> %and.i2326.i.i213, splat (i8 63)
  %cmp.i21.i.i214 = icmp eq <32 x i8> %84, zeroinitializer
  %85 = bitcast <32 x i1> %cmp.i21.i.i214 to i32
  %not.i46.i215 = xor i32 %85, -1
  %86 = bitcast <4 x i64> %67 to <16 x i16>
  %87 = lshr <16 x i16> %86, splat (i16 4)
  %88 = and <32 x i8> %70, splat (i8 15)
  %89 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %88)
  %90 = bitcast <16 x i16> %87 to <32 x i8>
  %91 = and <32 x i8> %90, splat (i8 15)
  %92 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %91)
  %and.i2326.i47.i217 = and <32 x i8> %92, %89
  %93 = and <32 x i8> %and.i2326.i47.i217, splat (i8 63)
  %cmp.i21.i48.i218 = icmp eq <32 x i8> %93, zeroinitializer
  %94 = bitcast <32 x i1> %cmp.i21.i48.i218 to i32
  %not.i49.i219 = xor i32 %94, -1
  %conv16.i221 = zext i32 %not.i46.i215 to i64
  %conv17.i222 = zext i32 %not.i49.i219 to i64
  %shl18.i223 = shl i64 %conv17.i222, 32
  %or19.i224 = or i64 %shl18.i223, %conv16.i221
  %95 = shufflevector <32 x i8> %and.i2326.i.i213, <32 x i8> %and.i2326.i47.i217, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %96 = icmp eq <64 x i8> %95, zeroinitializer
  %or23.i228 = bitcast <64 x i1> %96 to i64
  %vecinit1.i.i.i229 = insertelement <2 x i64> zeroinitializer, i64 %and.i212, i64 0
  %97 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i229, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i230 = extractelement <2 x i64> %97, i64 0
  %xor.i232 = xor i64 %vecext.i.i.i230, %st.sroa.11.0.lcssa
  %not55 = xor i64 %xor.i232, -1
  %98 = or i64 %and.i212, %xor.i232
  %99 = xor i64 %98, -1
  %and56 = and i64 %or23.i228, %99
  %and59 = and i64 %or19.i224, %not55
  %shl61 = shl i64 %and56, 1
  %or62 = or i64 %shl61, %prevS.0.lcssa
  %not63 = xor i64 %or62, -1
  %and64 = and i64 %and56, %not63
  %100 = or i64 %and59, %and64
  %or65 = or i64 %100, %and.i212
  %notmask = shl i64 -1, %and
  %sub = xor i64 %notmask, -1
  %and67 = and i64 %or65, %sub
  %arrayidx68 = getelementptr inbounds i64, ptr %ent, i64 %shr
  store i64 %and67, ptr %arrayidx68
  %tobool69 = icmp eq i32 %conv, 0
  %tobool71 = icmp ne i32 %68, 0
  %or.cond108 = select i1 %tobool69, i1 %tobool71, i1 false
  %or.cond109 = select i1 %or.cond108, i1 %prev_ascii.0.lcssa, i1 false
  br i1 %or.cond109, label %if.end77, label %if.then74

if.then74:                                        ; preds = %if.then33
  %add.ptr.i.i234 = getelementptr inbounds i8, ptr %add.ptr36, i64 -1
  %101 = load <4 x i64>, ptr %add.ptr.i.i234
  %add.ptr3.i.i235 = getelementptr inbounds i8, ptr %add.ptr36, i64 -2
  %102 = load <32 x i8>, ptr %add.ptr3.i.i235
  %add.ptr5.i.i236 = getelementptr inbounds i8, ptr %add.ptr36, i64 -3
  %103 = load <32 x i8>, ptr %add.ptr5.i.i236
  %104 = bitcast <4 x i64> %101 to <32 x i8>
  %105 = and <32 x i8> %104, splat (i8 15)
  %106 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %105)
  %107 = bitcast <4 x i64> %101 to <16 x i16>
  %108 = lshr <16 x i16> %107, splat (i16 4)
  %109 = bitcast <16 x i16> %108 to <32 x i8>
  %110 = and <32 x i8> %109, splat (i8 15)
  %111 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %110)
  %and.i3741.i.i237 = and <32 x i8> %111, %106
  %112 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %82)
  %and.i3542.i.i238 = and <32 x i8> %and.i3741.i.i237, %112
  %and.i35.i.i239 = bitcast <32 x i8> %and.i3542.i.i238 to <4 x i64>
  %elt.sat.i40.i.i240 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %102, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i241 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %103, <32 x i8> splat (i8 112))
  %or.i43.i.i242 = or <32 x i8> %elt.sat.i.i.i241, %elt.sat.i40.i.i240
  %or.i.i.i243 = bitcast <32 x i8> %or.i43.i.i242 to <4 x i64>
  %and.i.i.i244 = and <4 x i64> %or.i.i.i243, splat (i64 -9187201950435737472)
  %xor.i.i.i245 = xor <4 x i64> %and.i.i.i244, %and.i35.i.i239
  %add.ptr.i4.i246 = getelementptr inbounds i8, ptr %add.ptr36, i64 31
  %113 = load <4 x i64>, ptr %add.ptr.i4.i246
  %add.ptr3.i5.i247 = getelementptr inbounds i8, ptr %add.ptr36, i64 30
  %114 = load <32 x i8>, ptr %add.ptr3.i5.i247
  %add.ptr5.i6.i248 = getelementptr inbounds i8, ptr %add.ptr36, i64 29
  %115 = load <32 x i8>, ptr %add.ptr5.i6.i248
  %116 = bitcast <4 x i64> %113 to <32 x i8>
  %117 = and <32 x i8> %116, splat (i8 15)
  %118 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %117)
  %119 = bitcast <4 x i64> %113 to <16 x i16>
  %120 = lshr <16 x i16> %119, splat (i16 4)
  %121 = bitcast <16 x i16> %120 to <32 x i8>
  %122 = and <32 x i8> %121, splat (i8 15)
  %123 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %122)
  %and.i3741.i7.i249 = and <32 x i8> %123, %118
  %124 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %91)
  %and.i3542.i8.i250 = and <32 x i8> %and.i3741.i7.i249, %124
  %and.i35.i9.i251 = bitcast <32 x i8> %and.i3542.i8.i250 to <4 x i64>
  %elt.sat.i40.i10.i252 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %114, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i253 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %115, <32 x i8> splat (i8 112))
  %or.i43.i12.i254 = or <32 x i8> %elt.sat.i.i11.i253, %elt.sat.i40.i10.i252
  %or.i.i13.i255 = bitcast <32 x i8> %or.i43.i12.i254 to <4 x i64>
  %and.i.i14.i256 = and <4 x i64> %or.i.i13.i255, splat (i64 -9187201950435737472)
  %xor.i.i15.i257 = xor <4 x i64> %and.i.i14.i256, %and.i35.i9.i251
  %125 = or <4 x i64> %xor.i.i.i245, %xor.i.i15.i257
  %or.i = or <4 x i64> %125, %u8k.0.lcssa
  br label %if.end77

if.end77:                                         ; preds = %if.then33, %if.then74
  %u8k.2 = phi <4 x i64> [ %u8k.0.lcssa, %if.then33 ], [ %or.i, %if.then74 ]
  %and78 = and i64 %arm, 2
  %tobool79.not = icmp eq i64 %and78, 0
  br i1 %tobool79.not, label %if.end83.thread, label %if.then80

if.then80:                                        ; preds = %if.end77
  %126 = shufflevector <4 x i64> %66, <4 x i64> %67, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %127 = bitcast <8 x i64> %126 to <64 x i8>
  %128 = icmp ult <64 x i8> %127, splat (i8 32)
  %or.i264 = bitcast <64 x i1> %128 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i188, i64 %or.i264, i64 %xor.i232, i64 %shr, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end83.thread

if.end83.thread:                                  ; preds = %if.end77, %if.then80
  %129 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %u8k.2, <4 x i64> %u8k.2)
  %cmp85274 = icmp eq i32 %129, 0
  br label %if.end100

if.end83:                                         ; preds = %for.cond.cleanup
  %130 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %u8k.0.lcssa, <4 x i64> %u8k.0.lcssa)
  %cmp85 = icmp eq i32 %130, 0
  %cmp88.not.not = icmp eq i64 %n, 0
  br i1 %cmp88.not.not, label %if.end100, label %if.then94

if.then94:                                        ; preds = %if.end83
  %131 = getelementptr i8, ptr %b, i64 %n
  %arrayidx96 = getelementptr i8, ptr %131, i64 -1
  %132 = load i8, ptr %arrayidx96
  %133 = and i8 %132, -2
  %cmp.i = icmp eq i8 %133, -64
  %cmp3.i = icmp ugt i8 %132, -12
  %134 = or i1 %cmp3.i, %cmp.i
  %or99279 = or i1 %cmp85, %134
  br label %if.end100

if.end100:                                        ; preds = %if.end83.thread, %if.then94, %if.end83
  %ascii.1278 = phi <4 x i64> [ %ascii.0.lcssa, %if.then94 ], [ %ascii.0.lcssa, %if.end83 ], [ %or.i166, %if.end83.thread ]
  %err.0.in = phi i1 [ %or99279, %if.then94 ], [ %cmp85, %if.end83 ], [ %cmp85274, %if.end83.thread ]
  %135 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %ascii.1278, <4 x i64> splat (i64 -9187201950435737472))
  %cmp102 = icmp ne i32 %135, 0
  %conv104 = zext i1 %cmp102 to i64
  %shl105 = select i1 %err.0.in, i64 2, i64 0
  %or106 = or i64 %shl105, %conv104
  ret i64 %or106
}
