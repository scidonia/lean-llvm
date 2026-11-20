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
;   attributes #3 = { nounwind }
;
; The fixture's own opcodes and call targets are in json-s1-blocks.inventory.
define void @leanllvm_json_s1_blocks(ptr %b, i64 %n, ptr %ent, ptr %xp, ptr %nxp, ptr %xcarry, i64 %arm) {
entry:
  %shr = lshr i64 %n, 6
  %and = and i64 %n, 63
  %cmp155.not = icmp ult i64 %n, 64
  br i1 %cmp155.not, label %for.cond.cleanup, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  %and14 = and i64 %arm, 2
  %tobool.not = icmp eq i64 %and14, 0
  br label %for.body

for.cond.cleanup:                                 ; preds = %if.end, %entry
  %st.sroa.11.0.lcssa = phi i64 [ 0, %entry ], [ %shr.i, %if.end ]
  %st.sroa.7.0.lcssa = phi i64 [ 0, %entry ], [ %conv13.i.i, %if.end ]
  %st.sroa.0.0.lcssa = phi i64 [ 0, %entry ], [ %shr.i.i, %if.end ]
  %prevS.0.lcssa = phi i64 [ 0, %entry ], [ %shr13, %if.end ]
  %tobool16.not = icmp eq i64 %and, 0
  br i1 %tobool16.not, label %if.end53, label %if.then17

for.body:                                         ; preds = %for.body.lr.ph, %if.end
  %prevS.0160 = phi i64 [ 0, %for.body.lr.ph ], [ %shr13, %if.end ]
  %i.0159 = phi i64 [ 0, %for.body.lr.ph ], [ %inc, %if.end ]
  %st.sroa.0.0158 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i.i, %if.end ]
  %st.sroa.7.0157 = phi i64 [ 0, %for.body.lr.ph ], [ %conv13.i.i, %if.end ]
  %st.sroa.11.0156 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i, %if.end ]
  %shl = shl i64 %i.0159, 6
  %add.ptr = getelementptr inbounds i8, ptr %b, i64 %shl
  %0 = load <4 x i64>, ptr %add.ptr
  %add.ptr1 = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %1 = load <4 x i64>, ptr %add.ptr1
  %2 = bitcast <4 x i64> %0 to <32 x i8>
  %3 = bitcast <4 x i64> %1 to <32 x i8>
  %4 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %5 = bitcast <8 x i64> %4 to <64 x i8>
  %6 = icmp eq <64 x i8> %5, splat (i8 34)
  %or.i = bitcast <64 x i1> %6 to i64
  %cmp.i39.i = icmp eq <32 x i8> %2, splat (i8 92)
  %7 = bitcast <32 x i1> %cmp.i39.i to i32
  %conv9.i = zext i32 %7 to i64
  %cmp.i.i = icmp eq <32 x i8> %3, splat (i8 92)
  %8 = bitcast <32 x i1> %cmp.i.i to i32
  %conv12.i = zext i32 %8 to i64
  %shl13.i = shl i64 %conv12.i, 32
  %or14.i = or i64 %shl13.i, %conv9.i
  %and.i.i = and i64 %st.sroa.0.0158, %st.sroa.7.0157
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
  %and.i = and i64 %or.i, %not.i
  %9 = bitcast <4 x i64> %0 to <16 x i16>
  %10 = lshr <16 x i16> %9, splat (i16 4)
  %11 = and <32 x i8> %2, splat (i8 15)
  %12 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %11)
  %13 = bitcast <16 x i16> %10 to <32 x i8>
  %14 = and <32 x i8> %13, splat (i8 15)
  %15 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %14)
  %and.i2326.i.i = and <32 x i8> %15, %12
  %16 = and <32 x i8> %and.i2326.i.i, splat (i8 63)
  %cmp.i21.i.i = icmp eq <32 x i8> %16, zeroinitializer
  %17 = bitcast <32 x i1> %cmp.i21.i.i to i32
  %not.i46.i = xor i32 %17, -1
  %18 = bitcast <4 x i64> %1 to <16 x i16>
  %19 = lshr <16 x i16> %18, splat (i16 4)
  %20 = and <32 x i8> %3, splat (i8 15)
  %21 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %20)
  %22 = bitcast <16 x i16> %19 to <32 x i8>
  %23 = and <32 x i8> %22, splat (i8 15)
  %24 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %23)
  %and.i2326.i47.i = and <32 x i8> %24, %21
  %25 = and <32 x i8> %and.i2326.i47.i, splat (i8 63)
  %cmp.i21.i48.i = icmp eq <32 x i8> %25, zeroinitializer
  %26 = bitcast <32 x i1> %cmp.i21.i48.i to i32
  %not.i49.i = xor i32 %26, -1
  %conv16.i = zext i32 %not.i46.i to i64
  %conv17.i = zext i32 %not.i49.i to i64
  %shl18.i = shl i64 %conv17.i, 32
  %or19.i = or i64 %shl18.i, %conv16.i
  %27 = shufflevector <32 x i8> %and.i2326.i.i, <32 x i8> %and.i2326.i47.i, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %28 = icmp eq <64 x i8> %27, zeroinitializer
  %or23.i = bitcast <64 x i1> %28 to i64
  %vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0
  %29 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i = extractelement <2 x i64> %29, i64 0
  %xor.i = xor i64 %vecext.i.i.i, %st.sroa.11.0156
  %shr.i = ashr i64 %xor.i, 63
  %not4 = xor i64 %xor.i, -1
  %30 = or i64 %and.i, %xor.i
  %31 = xor i64 %30, -1
  %and5 = and i64 %or23.i, %31
  %and7 = and i64 %or19.i, %not4
  %shl8 = shl i64 %and5, 1
  %or9 = or i64 %shl8, %prevS.0160
  %not10 = xor i64 %or9, -1
  %and11 = and i64 %and5, %not10
  %32 = or i64 %and7, %and11
  %or12 = or i64 %32, %and.i
  %shr13 = lshr i64 %and5, 63
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.0159
  store i64 %or12, ptr %arrayidx
  br i1 %tobool.not, label %if.end, label %if.then

if.then:                                          ; preds = %for.body
  %33 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %34 = bitcast <8 x i64> %33 to <64 x i8>
  %35 = icmp ult <64 x i8> %34, splat (i8 32)
  %or.i84 = bitcast <64 x i1> %35 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i, i64 %or.i84, i64 %xor.i, i64 %i.0159, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %inc = add i64 %i.0159, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body

if.then17:                                        ; preds = %for.cond.cleanup
  %shl19 = and i64 %n, -64
  %add.ptr20 = getelementptr inbounds i8, ptr %b, i64 %shl19
  %36 = load <4 x i64>, ptr %add.ptr20
  %add.ptr24 = getelementptr inbounds i8, ptr %add.ptr20, i64 32
  %37 = load <4 x i64>, ptr %add.ptr24
  %38 = bitcast <4 x i64> %36 to <32 x i8>
  %39 = bitcast <4 x i64> %37 to <32 x i8>
  %40 = shufflevector <4 x i64> %36, <4 x i64> %37, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %41 = bitcast <8 x i64> %40 to <64 x i8>
  %42 = icmp eq <64 x i8> %41, splat (i8 34)
  %or.i90 = bitcast <64 x i1> %42 to i64
  %43 = shufflevector <4 x i64> %36, <4 x i64> %37, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %44 = bitcast <8 x i64> %43 to <64 x i8>
  %45 = icmp eq <64 x i8> %44, splat (i8 92)
  %or14.i96 = bitcast <64 x i1> %45 to i64
  %and.i.i98 = and i64 %st.sroa.0.0.lcssa, %st.sroa.7.0.lcssa
  %shl.i.i99 = shl i64 %or14.i96, 1
  %not.i.i100 = xor i64 %shl.i.i99, -1
  %and1.i.i101 = and i64 %or14.i96, %not.i.i100
  %xor.i.i102 = xor i64 %and.i.i98, 6148914691236517205
  %and2.i.i103 = and i64 %and1.i.i101, %xor.i.i102
  %xor3.i.i104 = xor i64 %and2.i.i103, %and1.i.i101
  %not4.i.i105 = xor i64 %or14.i96, -1
  %add.i.i106 = add i64 %and2.i.i103, %or14.i96
  %add5.i.i107 = add i64 %xor3.i.i104, %or14.i96
  %and6.i.i108 = and i64 %not4.i.i105, -6148914691236517206
  %and7.i.i109 = and i64 %and6.i.i108, %add.i.i106
  %and8.i.i110 = and i64 %not4.i.i105, 6148914691236517205
  %and9.i.i111 = and i64 %and8.i.i110, %add5.i.i107
  %and11.i.i113 = and i64 %and.i.i98, %not4.i.i105
  %or.i.i114 = or i64 %and7.i.i109, %and11.i.i113
  %or12.i.i115 = or i64 %or.i.i114, %and9.i.i111
  %not.i119 = xor i64 %or12.i.i115, -1
  %and.i120 = and i64 %or.i90, %not.i119
  %46 = bitcast <4 x i64> %36 to <16 x i16>
  %47 = lshr <16 x i16> %46, splat (i16 4)
  %48 = and <32 x i8> %38, splat (i8 15)
  %49 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %48)
  %50 = bitcast <16 x i16> %47 to <32 x i8>
  %51 = and <32 x i8> %50, splat (i8 15)
  %52 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %51)
  %and.i2326.i.i121 = and <32 x i8> %52, %49
  %53 = and <32 x i8> %and.i2326.i.i121, splat (i8 63)
  %cmp.i21.i.i122 = icmp eq <32 x i8> %53, zeroinitializer
  %54 = bitcast <32 x i1> %cmp.i21.i.i122 to i32
  %not.i46.i123 = xor i32 %54, -1
  %55 = bitcast <4 x i64> %37 to <16 x i16>
  %56 = lshr <16 x i16> %55, splat (i16 4)
  %57 = and <32 x i8> %39, splat (i8 15)
  %58 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %57)
  %59 = bitcast <16 x i16> %56 to <32 x i8>
  %60 = and <32 x i8> %59, splat (i8 15)
  %61 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %60)
  %and.i2326.i47.i125 = and <32 x i8> %61, %58
  %62 = and <32 x i8> %and.i2326.i47.i125, splat (i8 63)
  %cmp.i21.i48.i126 = icmp eq <32 x i8> %62, zeroinitializer
  %63 = bitcast <32 x i1> %cmp.i21.i48.i126 to i32
  %not.i49.i127 = xor i32 %63, -1
  %conv16.i129 = zext i32 %not.i46.i123 to i64
  %conv17.i130 = zext i32 %not.i49.i127 to i64
  %shl18.i131 = shl i64 %conv17.i130, 32
  %or19.i132 = or i64 %shl18.i131, %conv16.i129
  %64 = shufflevector <32 x i8> %and.i2326.i.i121, <32 x i8> %and.i2326.i47.i125, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %65 = icmp eq <64 x i8> %64, zeroinitializer
  %or23.i136 = bitcast <64 x i1> %65 to i64
  %vecinit1.i.i.i137 = insertelement <2 x i64> zeroinitializer, i64 %and.i120, i64 0
  %66 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i137, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i138 = extractelement <2 x i64> %66, i64 0
  %xor.i140 = xor i64 %vecext.i.i.i138, %st.sroa.11.0.lcssa
  %not34 = xor i64 %xor.i140, -1
  %67 = or i64 %and.i120, %xor.i140
  %68 = xor i64 %67, -1
  %and35 = and i64 %or23.i136, %68
  %and38 = and i64 %or19.i132, %not34
  %shl40 = shl i64 %and35, 1
  %or41 = or i64 %shl40, %prevS.0.lcssa
  %not42 = xor i64 %or41, -1
  %and43 = and i64 %and35, %not42
  %69 = or i64 %and38, %and43
  %or44 = or i64 %69, %and.i120
  %notmask = shl i64 -1, %and
  %sub = xor i64 %notmask, -1
  %and46 = and i64 %or44, %sub
  %arrayidx47 = getelementptr inbounds i64, ptr %ent, i64 %shr
  store i64 %and46, ptr %arrayidx47
  %and48 = and i64 %arm, 2
  %tobool49.not = icmp eq i64 %and48, 0
  br i1 %tobool49.not, label %if.end53, label %if.then50

if.then50:                                        ; preds = %if.then17
  %70 = shufflevector <4 x i64> %36, <4 x i64> %37, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %71 = bitcast <8 x i64> %70 to <64 x i8>
  %72 = icmp ult <64 x i8> %71, splat (i8 32)
  %or.i147 = bitcast <64 x i1> %72 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i96, i64 %or.i147, i64 %xor.i140, i64 %shr, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end53

if.end53:                                         ; preds = %if.then17, %if.then50, %for.cond.cleanup
  ret void
}
