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
  %cmp2506.not = icmp ult i64 %n, 64
  br i1 %cmp2506.not, label %if.end50, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  %and18 = and i64 %arm, 2
  %tobool.not = icmp eq i64 %and18, 0
  br label %for.body

for.body:                                         ; preds = %for.body.lr.ph, %for.inc
  %prevS.0511 = phi i64 [ 0, %for.body.lr.ph ], [ %shr17, %for.inc ]
  %i.0510 = phi i64 [ 0, %for.body.lr.ph ], [ %inc, %for.inc ]
  %st.sroa.0.0509 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i.i, %for.inc ]
  %st.sroa.9.0508 = phi i64 [ 0, %for.body.lr.ph ], [ %conv13.i.i, %for.inc ]
  %st.sroa.15.0507 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i, %for.inc ]
  %shl = shl i64 %i.0510, 6
  %add.ptr = getelementptr inbounds i8, ptr %b, i64 %shl
  %2 = load <4 x i64>, ptr %add.ptr
  %add.ptr5 = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %3 = load <4 x i64>, ptr %add.ptr5
  %4 = bitcast <4 x i64> %2 to <32 x i8>
  %5 = bitcast <4 x i64> %3 to <32 x i8>
  %6 = shufflevector <4 x i64> %2, <4 x i64> %3, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %7 = bitcast <8 x i64> %6 to <64 x i8>
  %8 = icmp eq <64 x i8> %7, splat (i8 34)
  %or.i286 = bitcast <64 x i1> %8 to i64
  %cmp.i39.i = icmp eq <32 x i8> %4, splat (i8 92)
  %9 = bitcast <32 x i1> %cmp.i39.i to i32
  %conv9.i = zext i32 %9 to i64
  %cmp.i.i = icmp eq <32 x i8> %5, splat (i8 92)
  %10 = bitcast <32 x i1> %cmp.i.i to i32
  %conv12.i = zext i32 %10 to i64
  %shl13.i = shl i64 %conv12.i, 32
  %or14.i = or i64 %shl13.i, %conv9.i
  %and.i.i = and i64 %st.sroa.0.0509, %st.sroa.9.0508
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
  %and.i = and i64 %or.i286, %not.i
  %11 = bitcast <4 x i64> %2 to <16 x i16>
  %12 = lshr <16 x i16> %11, splat (i16 4)
  %13 = and <32 x i8> %4, splat (i8 15)
  %14 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %13)
  %15 = bitcast <16 x i16> %12 to <32 x i8>
  %16 = and <32 x i8> %15, splat (i8 15)
  %17 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %16)
  %and.i2326.i.i = and <32 x i8> %17, %14
  %18 = and <32 x i8> %and.i2326.i.i, splat (i8 63)
  %cmp.i21.i.i = icmp eq <32 x i8> %18, zeroinitializer
  %19 = bitcast <32 x i1> %cmp.i21.i.i to i32
  %not.i46.i = xor i32 %19, -1
  %20 = bitcast <4 x i64> %3 to <16 x i16>
  %21 = lshr <16 x i16> %20, splat (i16 4)
  %22 = and <32 x i8> %5, splat (i8 15)
  %23 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %22)
  %24 = bitcast <16 x i16> %21 to <32 x i8>
  %25 = and <32 x i8> %24, splat (i8 15)
  %26 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %25)
  %and.i2326.i47.i = and <32 x i8> %26, %23
  %27 = and <32 x i8> %and.i2326.i47.i, splat (i8 63)
  %cmp.i21.i48.i = icmp eq <32 x i8> %27, zeroinitializer
  %28 = bitcast <32 x i1> %cmp.i21.i48.i to i32
  %not.i49.i = xor i32 %28, -1
  %conv16.i = zext i32 %not.i46.i to i64
  %conv17.i = zext i32 %not.i49.i to i64
  %shl18.i = shl i64 %conv17.i, 32
  %or19.i = or i64 %shl18.i, %conv16.i
  %29 = shufflevector <32 x i8> %and.i2326.i.i, <32 x i8> %and.i2326.i47.i, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %30 = icmp eq <64 x i8> %29, zeroinitializer
  %or23.i = bitcast <64 x i1> %30 to i64
  %vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0
  %31 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i = extractelement <2 x i64> %31, i64 0
  %xor.i = xor i64 %vecext.i.i.i, %st.sroa.15.0507
  %shr.i = ashr i64 %xor.i, 63
  %not8 = xor i64 %xor.i, -1
  %32 = or i64 %and.i, %xor.i
  %33 = xor i64 %32, -1
  %and9 = and i64 %or23.i, %33
  %and11 = and i64 %or19.i, %not8
  %shl12 = shl i64 %and9, 1
  %or13 = or i64 %shl12, %prevS.0511
  %not14 = xor i64 %or13, -1
  %and15 = and i64 %and9, %not14
  %34 = or i64 %and11, %and15
  %or16 = or i64 %34, %and.i
  %shr17 = lshr i64 %and9, 63
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.0510
  store i64 %or16, ptr %arrayidx
  br i1 %tobool.not, label %if.end, label %if.then

if.then:                                          ; preds = %for.body
  %35 = shufflevector <4 x i64> %2, <4 x i64> %3, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %36 = bitcast <8 x i64> %35 to <64 x i8>
  %37 = icmp ult <64 x i8> %36, splat (i8 32)
  %or.i290 = bitcast <64 x i1> %37 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i, i64 %or.i290, i64 %xor.i, i64 %i.0510, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %or.i285 = or <4 x i64> %3, %2
  %38 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i285, <4 x i64> splat (i64 -9187201950435737472))
  %tobool22.not = icmp eq i32 %38, 0
  br i1 %tobool22.not, label %if.then38, label %for.inc

for.inc:                                          ; preds = %if.end
  %inc = add i64 %i.0510, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.end101, label %for.body

if.then38:                                        ; preds = %if.end
  %add.ptr5.le = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %39 = load <4 x i64>, ptr %add.ptr
  %40 = load <4 x i64>, ptr %add.ptr5.le
  %or.i284 = or <4 x i64> %40, %39
  %add.ptr.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -1
  %41 = load <4 x i64>, ptr %add.ptr.i.i
  %add.ptr3.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -2
  %42 = load <32 x i8>, ptr %add.ptr3.i.i
  %add.ptr5.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -3
  %43 = load <32 x i8>, ptr %add.ptr5.i.i
  %44 = bitcast <4 x i64> %41 to <32 x i8>
  %45 = and <32 x i8> %44, splat (i8 15)
  %46 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %45)
  %47 = bitcast <4 x i64> %41 to <16 x i16>
  %48 = lshr <16 x i16> %47, splat (i16 4)
  %49 = bitcast <16 x i16> %48 to <32 x i8>
  %50 = and <32 x i8> %49, splat (i8 15)
  %51 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %50)
  %and.i3741.i.i = and <32 x i8> %51, %46
  %52 = bitcast <4 x i64> %39 to <16 x i16>
  %53 = lshr <16 x i16> %52, splat (i16 4)
  %54 = bitcast <16 x i16> %53 to <32 x i8>
  %55 = and <32 x i8> %54, splat (i8 15)
  %56 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %55)
  %and.i3542.i.i = and <32 x i8> %and.i3741.i.i, %56
  %and.i35.i.i = bitcast <32 x i8> %and.i3542.i.i to <4 x i64>
  %elt.sat.i40.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %42, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %43, <32 x i8> splat (i8 112))
  %or.i43.i.i = or <32 x i8> %elt.sat.i.i.i, %elt.sat.i40.i.i
  %or.i.i.i = bitcast <32 x i8> %or.i43.i.i to <4 x i64>
  %and.i.i.i = and <4 x i64> %or.i.i.i, splat (i64 -9187201950435737472)
  %xor.i.i.i = xor <4 x i64> %and.i.i.i, %and.i35.i.i
  %add.ptr.i4.i = getelementptr inbounds i8, ptr %add.ptr, i64 31
  %57 = load <4 x i64>, ptr %add.ptr.i4.i
  %add.ptr3.i5.i = getelementptr inbounds i8, ptr %add.ptr, i64 30
  %58 = load <32 x i8>, ptr %add.ptr3.i5.i
  %add.ptr5.i6.i = getelementptr inbounds i8, ptr %add.ptr, i64 29
  %59 = load <32 x i8>, ptr %add.ptr5.i6.i
  %60 = bitcast <4 x i64> %57 to <32 x i8>
  %61 = and <32 x i8> %60, splat (i8 15)
  %62 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %61)
  %63 = bitcast <4 x i64> %57 to <16 x i16>
  %64 = lshr <16 x i16> %63, splat (i16 4)
  %65 = bitcast <16 x i16> %64 to <32 x i8>
  %66 = and <32 x i8> %65, splat (i8 15)
  %67 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %66)
  %and.i3741.i7.i = and <32 x i8> %67, %62
  %68 = bitcast <4 x i64> %40 to <16 x i16>
  %69 = lshr <16 x i16> %68, splat (i16 4)
  %70 = bitcast <16 x i16> %69 to <32 x i8>
  %71 = and <32 x i8> %70, splat (i8 15)
  %72 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %71)
  %and.i3542.i8.i = and <32 x i8> %and.i3741.i7.i, %72
  %and.i35.i9.i = bitcast <32 x i8> %and.i3542.i8.i to <4 x i64>
  %elt.sat.i40.i10.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %58, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %59, <32 x i8> splat (i8 112))
  %or.i43.i12.i = or <32 x i8> %elt.sat.i.i11.i, %elt.sat.i40.i10.i
  %or.i.i13.i = bitcast <32 x i8> %or.i43.i12.i to <4 x i64>
  %and.i.i14.i = and <4 x i64> %or.i.i13.i, splat (i64 -9187201950435737472)
  %xor.i.i15.i = xor <4 x i64> %and.i.i14.i, %and.i35.i9.i
  %or.i.i291 = or <4 x i64> %xor.i.i15.i, %xor.i.i.i
  %inc49 = add i64 %i.0510, 1
  br label %if.end50

if.end50:                                         ; preds = %entry, %if.then38
  %prevS.1491 = phi i64 [ %shr17, %if.then38 ], [ 0, %entry ]
  %st.sroa.0.1489 = phi i64 [ %shr.i.i, %if.then38 ], [ 0, %entry ]
  %st.sroa.9.1487 = phi i64 [ %conv13.i.i, %if.then38 ], [ 0, %entry ]
  %st.sroa.15.1485 = phi i64 [ %shr.i, %if.then38 ], [ 0, %entry ]
  %prev_ascii.0 = phi i32 [ 0, %if.then38 ], [ 1, %entry ]
  %u8k.0 = phi <4 x i64> [ %or.i.i291, %if.then38 ], [ zeroinitializer, %entry ]
  %ascii.0 = phi <4 x i64> [ %or.i284, %if.then38 ], [ zeroinitializer, %entry ]
  %i.1 = phi i64 [ %inc49, %if.then38 ], [ 0, %entry ]
  %cmp52516 = icmp ult i64 %i.1, %shr
  br i1 %cmp52516, label %for.body54.lr.ph, label %for.end101

for.body54.lr.ph:                                 ; preds = %if.end50
  %tobool87 = icmp eq i32 %conv, 0
  %and94 = and i64 %arm, 2
  %tobool95.not = icmp eq i64 %and94, 0
  br label %for.body54

for.body54:                                       ; preds = %for.body54.lr.ph, %if.end98
  %prevS.2524 = phi i64 [ %prevS.1491, %for.body54.lr.ph ], [ %shr85, %if.end98 ]
  %i.2523 = phi i64 [ %i.1, %for.body54.lr.ph ], [ %inc100, %if.end98 ]
  %ascii.1522 = phi <4 x i64> [ %ascii.0, %for.body54.lr.ph ], [ %or.i282, %if.end98 ]
  %u8k.1521 = phi <4 x i64> [ %u8k.0, %for.body54.lr.ph ], [ %u8k.2, %if.end98 ]
  %prev_ascii.1520 = phi i32 [ %prev_ascii.0, %for.body54.lr.ph ], [ %75, %if.end98 ]
  %st.sroa.0.2519 = phi i64 [ %st.sroa.0.1489, %for.body54.lr.ph ], [ %shr.i.i325, %if.end98 ]
  %st.sroa.9.2518 = phi i64 [ %st.sroa.9.1487, %for.body54.lr.ph ], [ %conv13.i.i324, %if.end98 ]
  %st.sroa.15.2517 = phi i64 [ %st.sroa.15.1485, %for.body54.lr.ph ], [ %shr.i348, %if.end98 ]
  %shl56 = shl i64 %i.2523, 6
  %add.ptr57 = getelementptr inbounds i8, ptr %b, i64 %shl56
  %73 = load <4 x i64>, ptr %add.ptr57
  %add.ptr61 = getelementptr inbounds i8, ptr %add.ptr57, i64 32
  %74 = load <4 x i64>, ptr %add.ptr61
  %or.i283 = or <4 x i64> %74, %73
  %75 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i283, <4 x i64> splat (i64 -9187201950435737472))
  %or.i282 = or <4 x i64> %or.i283, %ascii.1522
  %76 = bitcast <4 x i64> %73 to <32 x i8>
  %77 = bitcast <4 x i64> %74 to <32 x i8>
  %78 = shufflevector <4 x i64> %73, <4 x i64> %74, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %79 = bitcast <8 x i64> %78 to <64 x i8>
  %80 = icmp eq <64 x i8> %79, splat (i8 34)
  %or.i297 = bitcast <64 x i1> %80 to i64
  %cmp.i39.i298 = icmp eq <32 x i8> %76, splat (i8 92)
  %81 = bitcast <32 x i1> %cmp.i39.i298 to i32
  %conv9.i299 = zext i32 %81 to i64
  %cmp.i.i300 = icmp eq <32 x i8> %77, splat (i8 92)
  %82 = bitcast <32 x i1> %cmp.i.i300 to i32
  %conv12.i301 = zext i32 %82 to i64
  %shl13.i302 = shl i64 %conv12.i301, 32
  %or14.i303 = or i64 %shl13.i302, %conv9.i299
  %and.i.i305 = and i64 %st.sroa.0.2519, %st.sroa.9.2518
  %shl.i.i306 = shl i64 %or14.i303, 1
  %not.i.i307 = xor i64 %shl.i.i306, -1
  %and1.i.i308 = and i64 %or14.i303, %not.i.i307
  %xor.i.i309 = xor i64 %and.i.i305, 6148914691236517205
  %and2.i.i310 = and i64 %and1.i.i308, %xor.i.i309
  %xor3.i.i311 = xor i64 %and2.i.i310, %and1.i.i308
  %not4.i.i312 = xor i64 %or14.i303, -1
  %add.i.i313 = add i64 %and2.i.i310, %or14.i303
  %add5.i.i314 = add i64 %xor3.i.i311, %or14.i303
  %and6.i.i315 = and i64 %not4.i.i312, -6148914691236517206
  %and7.i.i316 = and i64 %and6.i.i315, %add.i.i313
  %and8.i.i317 = and i64 %not4.i.i312, 6148914691236517205
  %and9.i.i318 = and i64 %and8.i.i317, %add5.i.i314
  %and11.i.i320 = and i64 %and.i.i305, %not4.i.i312
  %or.i.i321 = or i64 %and7.i.i316, %and11.i.i320
  %or12.i.i322 = or i64 %or.i.i321, %and9.i.i318
  %cmp.i45.i323 = icmp ult i64 %add5.i.i314, %or14.i303
  %conv13.i.i324 = zext i1 %cmp.i45.i323 to i64
  %shr.i.i325 = lshr i64 %conv12.i301, 31
  %not.i326 = xor i64 %or12.i.i322, -1
  %and.i327 = and i64 %or.i297, %not.i326
  %83 = bitcast <4 x i64> %73 to <16 x i16>
  %84 = lshr <16 x i16> %83, splat (i16 4)
  %85 = and <32 x i8> %76, splat (i8 15)
  %86 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %85)
  %87 = bitcast <16 x i16> %84 to <32 x i8>
  %88 = and <32 x i8> %87, splat (i8 15)
  %89 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %88)
  %and.i2326.i.i328 = and <32 x i8> %89, %86
  %90 = and <32 x i8> %and.i2326.i.i328, splat (i8 63)
  %cmp.i21.i.i329 = icmp eq <32 x i8> %90, zeroinitializer
  %91 = bitcast <32 x i1> %cmp.i21.i.i329 to i32
  %not.i46.i330 = xor i32 %91, -1
  %92 = bitcast <4 x i64> %74 to <16 x i16>
  %93 = lshr <16 x i16> %92, splat (i16 4)
  %94 = and <32 x i8> %77, splat (i8 15)
  %95 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %94)
  %96 = bitcast <16 x i16> %93 to <32 x i8>
  %97 = and <32 x i8> %96, splat (i8 15)
  %98 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %97)
  %and.i2326.i47.i332 = and <32 x i8> %98, %95
  %99 = and <32 x i8> %and.i2326.i47.i332, splat (i8 63)
  %cmp.i21.i48.i333 = icmp eq <32 x i8> %99, zeroinitializer
  %100 = bitcast <32 x i1> %cmp.i21.i48.i333 to i32
  %not.i49.i334 = xor i32 %100, -1
  %conv16.i336 = zext i32 %not.i46.i330 to i64
  %conv17.i337 = zext i32 %not.i49.i334 to i64
  %shl18.i338 = shl i64 %conv17.i337, 32
  %or19.i339 = or i64 %shl18.i338, %conv16.i336
  %101 = shufflevector <32 x i8> %and.i2326.i.i328, <32 x i8> %and.i2326.i47.i332, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %102 = icmp eq <64 x i8> %101, zeroinitializer
  %or23.i343 = bitcast <64 x i1> %102 to i64
  %vecinit1.i.i.i344 = insertelement <2 x i64> zeroinitializer, i64 %and.i327, i64 0
  %103 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i344, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i345 = extractelement <2 x i64> %103, i64 0
  %xor.i347 = xor i64 %vecext.i.i.i345, %st.sroa.15.2517
  %shr.i348 = ashr i64 %xor.i347, 63
  %not74 = xor i64 %xor.i347, -1
  %104 = or i64 %and.i327, %xor.i347
  %105 = xor i64 %104, -1
  %and75 = and i64 %or23.i343, %105
  %and78 = and i64 %or19.i339, %not74
  %shl80 = shl i64 %and75, 1
  %or81 = or i64 %shl80, %prevS.2524
  %not82 = xor i64 %or81, -1
  %and83 = and i64 %and75, %not82
  %106 = or i64 %and78, %and83
  %or84 = or i64 %106, %and.i327
  %shr85 = lshr i64 %and75, 63
  %arrayidx86 = getelementptr inbounds i64, ptr %ent, i64 %i.2523
  store i64 %or84, ptr %arrayidx86
  %tobool88 = icmp ne i32 %75, 0
  %tobool89 = icmp ne i32 %prev_ascii.1520, 0
  %107 = and i1 %tobool89, %tobool88
  %or.cond189 = select i1 %tobool87, i1 %107, i1 false
  br i1 %or.cond189, label %if.end93, label %if.then90

if.then90:                                        ; preds = %for.body54
  %add.ptr.i.i349 = getelementptr inbounds i8, ptr %add.ptr57, i64 -1
  %108 = load <4 x i64>, ptr %add.ptr.i.i349
  %add.ptr3.i.i350 = getelementptr inbounds i8, ptr %add.ptr57, i64 -2
  %109 = load <32 x i8>, ptr %add.ptr3.i.i350
  %add.ptr5.i.i351 = getelementptr inbounds i8, ptr %add.ptr57, i64 -3
  %110 = load <32 x i8>, ptr %add.ptr5.i.i351
  %111 = bitcast <4 x i64> %108 to <32 x i8>
  %112 = and <32 x i8> %111, splat (i8 15)
  %113 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %112)
  %114 = bitcast <4 x i64> %108 to <16 x i16>
  %115 = lshr <16 x i16> %114, splat (i16 4)
  %116 = bitcast <16 x i16> %115 to <32 x i8>
  %117 = and <32 x i8> %116, splat (i8 15)
  %118 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %117)
  %and.i3741.i.i352 = and <32 x i8> %118, %113
  %119 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %88)
  %and.i3542.i.i353 = and <32 x i8> %and.i3741.i.i352, %119
  %and.i35.i.i354 = bitcast <32 x i8> %and.i3542.i.i353 to <4 x i64>
  %elt.sat.i40.i.i355 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %109, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i356 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %110, <32 x i8> splat (i8 112))
  %or.i43.i.i357 = or <32 x i8> %elt.sat.i.i.i356, %elt.sat.i40.i.i355
  %or.i.i.i358 = bitcast <32 x i8> %or.i43.i.i357 to <4 x i64>
  %and.i.i.i359 = and <4 x i64> %or.i.i.i358, splat (i64 -9187201950435737472)
  %xor.i.i.i360 = xor <4 x i64> %and.i.i.i359, %and.i35.i.i354
  %add.ptr.i4.i361 = getelementptr inbounds i8, ptr %add.ptr57, i64 31
  %120 = load <4 x i64>, ptr %add.ptr.i4.i361
  %add.ptr3.i5.i362 = getelementptr inbounds i8, ptr %add.ptr57, i64 30
  %121 = load <32 x i8>, ptr %add.ptr3.i5.i362
  %add.ptr5.i6.i363 = getelementptr inbounds i8, ptr %add.ptr57, i64 29
  %122 = load <32 x i8>, ptr %add.ptr5.i6.i363
  %123 = bitcast <4 x i64> %120 to <32 x i8>
  %124 = and <32 x i8> %123, splat (i8 15)
  %125 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %124)
  %126 = bitcast <4 x i64> %120 to <16 x i16>
  %127 = lshr <16 x i16> %126, splat (i16 4)
  %128 = bitcast <16 x i16> %127 to <32 x i8>
  %129 = and <32 x i8> %128, splat (i8 15)
  %130 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %129)
  %and.i3741.i7.i364 = and <32 x i8> %130, %125
  %131 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %97)
  %and.i3542.i8.i365 = and <32 x i8> %and.i3741.i7.i364, %131
  %and.i35.i9.i366 = bitcast <32 x i8> %and.i3542.i8.i365 to <4 x i64>
  %elt.sat.i40.i10.i367 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %121, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i368 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %122, <32 x i8> splat (i8 112))
  %or.i43.i12.i369 = or <32 x i8> %elt.sat.i.i11.i368, %elt.sat.i40.i10.i367
  %or.i.i13.i370 = bitcast <32 x i8> %or.i43.i12.i369 to <4 x i64>
  %and.i.i14.i371 = and <4 x i64> %or.i.i13.i370, splat (i64 -9187201950435737472)
  %xor.i.i15.i372 = xor <4 x i64> %and.i.i14.i371, %and.i35.i9.i366
  %132 = or <4 x i64> %xor.i.i.i360, %xor.i.i15.i372
  %or.i281 = or <4 x i64> %132, %u8k.1521
  br label %if.end93

if.end93:                                         ; preds = %for.body54, %if.then90
  %u8k.2 = phi <4 x i64> [ %u8k.1521, %for.body54 ], [ %or.i281, %if.then90 ]
  br i1 %tobool95.not, label %if.end98, label %if.then96

if.then96:                                        ; preds = %if.end93
  %133 = shufflevector <4 x i64> %73, <4 x i64> %74, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %134 = bitcast <8 x i64> %133 to <64 x i8>
  %135 = icmp ult <64 x i8> %134, splat (i8 32)
  %or.i379 = bitcast <64 x i1> %135 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i303, i64 %or.i379, i64 %xor.i347, i64 %i.2523, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end98

if.end98:                                         ; preds = %if.then96, %if.end93
  %inc100 = add i64 %i.2523, 1
  %exitcond537.not = icmp eq i64 %inc100, %shr
  br i1 %exitcond537.not, label %for.end101, label %for.body54

for.end101:                                       ; preds = %for.inc, %if.end98, %if.end50
  %st.sroa.15.2.lcssa = phi i64 [ %st.sroa.15.1485, %if.end50 ], [ %shr.i348, %if.end98 ], [ %shr.i, %for.inc ]
  %st.sroa.9.2.lcssa = phi i64 [ %st.sroa.9.1487, %if.end50 ], [ %conv13.i.i324, %if.end98 ], [ %conv13.i.i, %for.inc ]
  %st.sroa.0.2.lcssa = phi i64 [ %st.sroa.0.1489, %if.end50 ], [ %shr.i.i325, %if.end98 ], [ %shr.i.i, %for.inc ]
  %prev_ascii.1.lcssa = phi i32 [ %prev_ascii.0, %if.end50 ], [ %75, %if.end98 ], [ 1, %for.inc ]
  %u8k.1.lcssa = phi <4 x i64> [ %u8k.0, %if.end50 ], [ %u8k.2, %if.end98 ], [ zeroinitializer, %for.inc ]
  %ascii.1.lcssa = phi <4 x i64> [ %ascii.0, %if.end50 ], [ %or.i282, %if.end98 ], [ zeroinitializer, %for.inc ]
  %prevS.2.lcssa = phi i64 [ %prevS.1491, %if.end50 ], [ %shr85, %if.end98 ], [ %shr17, %for.inc ]
  %tobool102.not = icmp eq i64 %and, 0
  br i1 %tobool102.not, label %if.end153, label %if.then103

if.then103:                                       ; preds = %for.end101
  %shl105 = and i64 %n, -64
  %add.ptr106 = getelementptr inbounds i8, ptr %b, i64 %shl105
  %136 = load <4 x i64>, ptr %add.ptr106
  %add.ptr110 = getelementptr inbounds i8, ptr %add.ptr106, i64 32
  %137 = load <4 x i64>, ptr %add.ptr110
  %or.i280 = or <4 x i64> %137, %136
  %138 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i280, <4 x i64> splat (i64 -9187201950435737472))
  %or.i279 = or <4 x i64> %or.i280, %ascii.1.lcssa
  %139 = bitcast <4 x i64> %136 to <32 x i8>
  %140 = bitcast <4 x i64> %137 to <32 x i8>
  %141 = shufflevector <4 x i64> %136, <4 x i64> %137, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %142 = bitcast <8 x i64> %141 to <64 x i8>
  %143 = icmp eq <64 x i8> %142, splat (i8 34)
  %or.i385 = bitcast <64 x i1> %143 to i64
  %144 = shufflevector <4 x i64> %136, <4 x i64> %137, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %145 = bitcast <8 x i64> %144 to <64 x i8>
  %146 = icmp eq <64 x i8> %145, splat (i8 92)
  %or14.i391 = bitcast <64 x i1> %146 to i64
  %and.i.i393 = and i64 %st.sroa.0.2.lcssa, %st.sroa.9.2.lcssa
  %shl.i.i394 = shl i64 %or14.i391, 1
  %not.i.i395 = xor i64 %shl.i.i394, -1
  %and1.i.i396 = and i64 %or14.i391, %not.i.i395
  %xor.i.i397 = xor i64 %and.i.i393, 6148914691236517205
  %and2.i.i398 = and i64 %and1.i.i396, %xor.i.i397
  %xor3.i.i399 = xor i64 %and2.i.i398, %and1.i.i396
  %not4.i.i400 = xor i64 %or14.i391, -1
  %add.i.i401 = add i64 %and2.i.i398, %or14.i391
  %add5.i.i402 = add i64 %xor3.i.i399, %or14.i391
  %and6.i.i403 = and i64 %not4.i.i400, -6148914691236517206
  %and7.i.i404 = and i64 %and6.i.i403, %add.i.i401
  %and8.i.i405 = and i64 %not4.i.i400, 6148914691236517205
  %and9.i.i406 = and i64 %and8.i.i405, %add5.i.i402
  %and11.i.i408 = and i64 %and.i.i393, %not4.i.i400
  %or.i.i409 = or i64 %and7.i.i404, %and11.i.i408
  %or12.i.i410 = or i64 %or.i.i409, %and9.i.i406
  %not.i414 = xor i64 %or12.i.i410, -1
  %and.i415 = and i64 %or.i385, %not.i414
  %147 = bitcast <4 x i64> %136 to <16 x i16>
  %148 = lshr <16 x i16> %147, splat (i16 4)
  %149 = and <32 x i8> %139, splat (i8 15)
  %150 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %149)
  %151 = bitcast <16 x i16> %148 to <32 x i8>
  %152 = and <32 x i8> %151, splat (i8 15)
  %153 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %152)
  %and.i2326.i.i416 = and <32 x i8> %153, %150
  %154 = and <32 x i8> %and.i2326.i.i416, splat (i8 63)
  %cmp.i21.i.i417 = icmp eq <32 x i8> %154, zeroinitializer
  %155 = bitcast <32 x i1> %cmp.i21.i.i417 to i32
  %not.i46.i418 = xor i32 %155, -1
  %156 = bitcast <4 x i64> %137 to <16 x i16>
  %157 = lshr <16 x i16> %156, splat (i16 4)
  %158 = and <32 x i8> %140, splat (i8 15)
  %159 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %158)
  %160 = bitcast <16 x i16> %157 to <32 x i8>
  %161 = and <32 x i8> %160, splat (i8 15)
  %162 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %161)
  %and.i2326.i47.i420 = and <32 x i8> %162, %159
  %163 = and <32 x i8> %and.i2326.i47.i420, splat (i8 63)
  %cmp.i21.i48.i421 = icmp eq <32 x i8> %163, zeroinitializer
  %164 = bitcast <32 x i1> %cmp.i21.i48.i421 to i32
  %not.i49.i422 = xor i32 %164, -1
  %conv16.i424 = zext i32 %not.i46.i418 to i64
  %conv17.i425 = zext i32 %not.i49.i422 to i64
  %shl18.i426 = shl i64 %conv17.i425, 32
  %or19.i427 = or i64 %shl18.i426, %conv16.i424
  %165 = shufflevector <32 x i8> %and.i2326.i.i416, <32 x i8> %and.i2326.i47.i420, <64 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8, i32 9, i32 10, i32 11, i32 12, i32 13, i32 14, i32 15, i32 16, i32 17, i32 18, i32 19, i32 20, i32 21, i32 22, i32 23, i32 24, i32 25, i32 26, i32 27, i32 28, i32 29, i32 30, i32 31, i32 32, i32 33, i32 34, i32 35, i32 36, i32 37, i32 38, i32 39, i32 40, i32 41, i32 42, i32 43, i32 44, i32 45, i32 46, i32 47, i32 48, i32 49, i32 50, i32 51, i32 52, i32 53, i32 54, i32 55, i32 56, i32 57, i32 58, i32 59, i32 60, i32 61, i32 62, i32 63>
  %166 = icmp eq <64 x i8> %165, zeroinitializer
  %or23.i431 = bitcast <64 x i1> %166 to i64
  %vecinit1.i.i.i432 = insertelement <2 x i64> zeroinitializer, i64 %and.i415, i64 0
  %167 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i432, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i433 = extractelement <2 x i64> %167, i64 0
  %xor.i435 = xor i64 %vecext.i.i.i433, %st.sroa.15.2.lcssa
  %not125 = xor i64 %xor.i435, -1
  %168 = or i64 %and.i415, %xor.i435
  %169 = xor i64 %168, -1
  %and126 = and i64 %or23.i431, %169
  %and129 = and i64 %or19.i427, %not125
  %shl131 = shl i64 %and126, 1
  %or132 = or i64 %shl131, %prevS.2.lcssa
  %not133 = xor i64 %or132, -1
  %and134 = and i64 %and126, %not133
  %170 = or i64 %and129, %and134
  %or135 = or i64 %170, %and.i415
  %notmask = shl i64 -1, %and
  %sub = xor i64 %notmask, -1
  %and137 = and i64 %or135, %sub
  %arrayidx138 = getelementptr inbounds i64, ptr %ent, i64 %shr
  store i64 %and137, ptr %arrayidx138
  %tobool139 = icmp eq i32 %conv, 0
  %tobool141 = icmp ne i32 %138, 0
  %or.cond190 = select i1 %tobool139, i1 %tobool141, i1 false
  %tobool143 = icmp ne i32 %prev_ascii.1.lcssa, 0
  %or.cond191 = select i1 %or.cond190, i1 %tobool143, i1 false
  br i1 %or.cond191, label %if.end147, label %if.then144

if.then144:                                       ; preds = %if.then103
  %add.ptr.i.i437 = getelementptr inbounds i8, ptr %add.ptr106, i64 -1
  %171 = load <4 x i64>, ptr %add.ptr.i.i437
  %add.ptr3.i.i438 = getelementptr inbounds i8, ptr %add.ptr106, i64 -2
  %172 = load <32 x i8>, ptr %add.ptr3.i.i438
  %add.ptr5.i.i439 = getelementptr inbounds i8, ptr %add.ptr106, i64 -3
  %173 = load <32 x i8>, ptr %add.ptr5.i.i439
  %174 = bitcast <4 x i64> %171 to <32 x i8>
  %175 = and <32 x i8> %174, splat (i8 15)
  %176 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %175)
  %177 = bitcast <4 x i64> %171 to <16 x i16>
  %178 = lshr <16 x i16> %177, splat (i16 4)
  %179 = bitcast <16 x i16> %178 to <32 x i8>
  %180 = and <32 x i8> %179, splat (i8 15)
  %181 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %180)
  %and.i3741.i.i440 = and <32 x i8> %181, %176
  %182 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %152)
  %and.i3542.i.i441 = and <32 x i8> %and.i3741.i.i440, %182
  %and.i35.i.i442 = bitcast <32 x i8> %and.i3542.i.i441 to <4 x i64>
  %elt.sat.i40.i.i443 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %172, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i444 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %173, <32 x i8> splat (i8 112))
  %or.i43.i.i445 = or <32 x i8> %elt.sat.i.i.i444, %elt.sat.i40.i.i443
  %or.i.i.i446 = bitcast <32 x i8> %or.i43.i.i445 to <4 x i64>
  %and.i.i.i447 = and <4 x i64> %or.i.i.i446, splat (i64 -9187201950435737472)
  %xor.i.i.i448 = xor <4 x i64> %and.i.i.i447, %and.i35.i.i442
  %add.ptr.i4.i449 = getelementptr inbounds i8, ptr %add.ptr106, i64 31
  %183 = load <4 x i64>, ptr %add.ptr.i4.i449
  %add.ptr3.i5.i450 = getelementptr inbounds i8, ptr %add.ptr106, i64 30
  %184 = load <32 x i8>, ptr %add.ptr3.i5.i450
  %add.ptr5.i6.i451 = getelementptr inbounds i8, ptr %add.ptr106, i64 29
  %185 = load <32 x i8>, ptr %add.ptr5.i6.i451
  %186 = bitcast <4 x i64> %183 to <32 x i8>
  %187 = and <32 x i8> %186, splat (i8 15)
  %188 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %187)
  %189 = bitcast <4 x i64> %183 to <16 x i16>
  %190 = lshr <16 x i16> %189, splat (i16 4)
  %191 = bitcast <16 x i16> %190 to <32 x i8>
  %192 = and <32 x i8> %191, splat (i8 15)
  %193 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %192)
  %and.i3741.i7.i452 = and <32 x i8> %193, %188
  %194 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %161)
  %and.i3542.i8.i453 = and <32 x i8> %and.i3741.i7.i452, %194
  %and.i35.i9.i454 = bitcast <32 x i8> %and.i3542.i8.i453 to <4 x i64>
  %elt.sat.i40.i10.i455 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %184, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i456 = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %185, <32 x i8> splat (i8 112))
  %or.i43.i12.i457 = or <32 x i8> %elt.sat.i.i11.i456, %elt.sat.i40.i10.i455
  %or.i.i13.i458 = bitcast <32 x i8> %or.i43.i12.i457 to <4 x i64>
  %and.i.i14.i459 = and <4 x i64> %or.i.i13.i458, splat (i64 -9187201950435737472)
  %xor.i.i15.i460 = xor <4 x i64> %and.i.i14.i459, %and.i35.i9.i454
  %195 = or <4 x i64> %xor.i.i.i448, %xor.i.i15.i460
  %or.i = or <4 x i64> %195, %u8k.1.lcssa
  br label %if.end147

if.end147:                                        ; preds = %if.then103, %if.then144
  %u8k.3 = phi <4 x i64> [ %u8k.1.lcssa, %if.then103 ], [ %or.i, %if.then144 ]
  %and148 = and i64 %arm, 2
  %tobool149.not = icmp eq i64 %and148, 0
  br i1 %tobool149.not, label %if.end153.thread, label %if.then150

if.then150:                                       ; preds = %if.end147
  %196 = shufflevector <4 x i64> %136, <4 x i64> %137, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %197 = bitcast <8 x i64> %196 to <64 x i8>
  %198 = icmp ult <64 x i8> %197, splat (i8 32)
  %or.i467 = bitcast <64 x i1> %198 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i391, i64 %or.i467, i64 %xor.i435, i64 %shr, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end153.thread

if.end153.thread:                                 ; preds = %if.end147, %if.then150
  %199 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %u8k.3, <4 x i64> %u8k.3)
  %cmp155495 = icmp eq i32 %199, 0
  br label %if.end170

if.end153:                                        ; preds = %for.end101
  %200 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %u8k.1.lcssa, <4 x i64> %u8k.1.lcssa)
  %cmp155 = icmp eq i32 %200, 0
  %cmp158.not.not = icmp eq i64 %n, 0
  br i1 %cmp158.not.not, label %if.end170, label %if.then164

if.then164:                                       ; preds = %if.end153
  %201 = getelementptr i8, ptr %b, i64 %n
  %arrayidx166 = getelementptr i8, ptr %201, i64 -1
  %202 = load i8, ptr %arrayidx166
  %203 = and i8 %202, -2
  %cmp.i = icmp eq i8 %203, -64
  %cmp3.i = icmp ugt i8 %202, -12
  %204 = or i1 %cmp3.i, %cmp.i
  %or169500 = or i1 %cmp155, %204
  br label %if.end170

if.end170:                                        ; preds = %if.end153.thread, %if.then164, %if.end153
  %ascii.2499 = phi <4 x i64> [ %ascii.1.lcssa, %if.then164 ], [ %ascii.1.lcssa, %if.end153 ], [ %or.i279, %if.end153.thread ]
  %err.0.in = phi i1 [ %or169500, %if.then164 ], [ %cmp155, %if.end153 ], [ %cmp155495, %if.end153.thread ]
  %205 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %ascii.2499, <4 x i64> splat (i64 -9187201950435737472))
  %cmp172 = icmp ne i32 %205, 0
  %conv174 = zext i1 %cmp172 to i64
  %shl175 = select i1 %err.0.in, i64 2, i64 0
  %or176 = or i64 %shl175, %conv174
  ret i64 %or176
}
