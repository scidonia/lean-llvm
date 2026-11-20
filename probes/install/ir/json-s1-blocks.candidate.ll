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
  %add = add i64 %n, 63
  %shr = lshr i64 %add, 6
  %cmp34.not = icmp ult i64 %add, 64
  br i1 %cmp34.not, label %for.cond.cleanup, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  %and18 = and i64 %arm, 2
  %tobool.not = icmp eq i64 %and18, 0
  br label %for.body

for.cond.cleanup:                                 ; preds = %if.end20, %entry
  ret void

for.body:                                         ; preds = %for.body.lr.ph, %if.end20
  %prevS.039 = phi i64 [ 0, %for.body.lr.ph ], [ %shr12, %if.end20 ]
  %i.038 = phi i64 [ 0, %for.body.lr.ph ], [ %inc, %if.end20 ]
  %st.sroa.0.037 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i.i, %if.end20 ]
  %st.sroa.5.036 = phi i64 [ 0, %for.body.lr.ph ], [ %conv13.i.i, %if.end20 ]
  %st.sroa.7.035 = phi i64 [ 0, %for.body.lr.ph ], [ %shr.i, %if.end20 ]
  %shl = shl i64 %i.038, 6
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
  %cmp.i54.i = icmp eq <32 x i8> %2, splat (i8 92)
  %7 = bitcast <32 x i1> %cmp.i54.i to i32
  %conv9.i = zext i32 %7 to i64
  %cmp.i52.i = icmp eq <32 x i8> %3, splat (i8 92)
  %8 = bitcast <32 x i1> %cmp.i52.i to i32
  %conv12.i = zext i32 %8 to i64
  %shl13.i = shl i64 %conv12.i, 32
  %or14.i = or i64 %shl13.i, %conv9.i
  %9 = bitcast <4 x i64> %0 to <16 x i16>
  %10 = lshr <16 x i16> %9, splat (i16 4)
  %11 = and <32 x i8> %2, splat (i8 15)
  %12 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %11)
  %13 = bitcast <16 x i16> %10 to <32 x i8>
  %14 = and <32 x i8> %13, splat (i8 15)
  %15 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %14)
  %and.i2831.i.i.i = and <32 x i8> %15, %12
  %16 = and <32 x i8> %and.i2831.i.i.i, splat (i8 63)
  %cmp.i25.i.i.i = icmp eq <32 x i8> %16, zeroinitializer
  %17 = bitcast <32 x i1> %cmp.i25.i.i.i to i32
  %not.i.i.i = xor i32 %17, -1
  %cmp.i.i.i.i = icmp ult <32 x i8> %and.i2831.i.i.i, splat (i8 64)
  %18 = bitcast <32 x i1> %cmp.i.i.i.i to i32
  %not18.i.i.i = xor i32 %18, -1
  %19 = bitcast <4 x i64> %1 to <16 x i16>
  %20 = lshr <16 x i16> %19, splat (i16 4)
  %21 = and <32 x i8> %3, splat (i8 15)
  %22 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0, i8 64, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 -126, i8 20, i8 1, i8 -88, i8 0, i8 0>, <32 x i8> %21)
  %23 = bitcast <16 x i16> %20 to <32 x i8>
  %24 = and <32 x i8> %23, splat (i8 15)
  %25 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 -128, i8 0, i8 65, i8 2, i8 0, i8 48, i8 0, i8 12, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <32 x i8> %24)
  %and.i2831.i6.i.i = and <32 x i8> %25, %22
  %26 = and <32 x i8> %and.i2831.i6.i.i, splat (i8 63)
  %cmp.i25.i7.i.i = icmp eq <32 x i8> %26, zeroinitializer
  %27 = bitcast <32 x i1> %cmp.i25.i7.i.i to i32
  %not.i8.i.i = xor i32 %27, -1
  %cmp.i.i9.i.i = icmp ult <32 x i8> %and.i2831.i6.i.i, splat (i8 64)
  %28 = bitcast <32 x i1> %cmp.i.i9.i.i to i32
  %not18.i10.i.i = xor i32 %28, -1
  %conv.i.i = zext i32 %not18.i.i.i to i64
  %conv1.i.i = zext i32 %not18.i10.i.i to i64
  %shl.i.i = shl i64 %conv1.i.i, 32
  %or.i.i = or i64 %shl.i.i, %conv.i.i
  %conv2.i.i = zext i32 %not.i.i.i to i64
  %conv3.i.i = zext i32 %not.i8.i.i to i64
  %shl4.i.i = shl i64 %conv3.i.i, 32
  %or5.i.i = or i64 %shl4.i.i, %conv2.i.i
  %and.i.i = and i64 %st.sroa.0.037, %st.sroa.5.036
  %shl.i61.i = shl i64 %or14.i, 1
  %not.i.i = xor i64 %shl.i61.i, -1
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
  %or.i62.i = or i64 %and7.i.i, %and11.i.i
  %or12.i.i = or i64 %or.i62.i, %and9.i.i
  %cmp.i63.i = icmp ult i64 %add5.i.i, %or14.i
  %conv13.i.i = zext i1 %cmp.i63.i to i64
  %shr.i.i = lshr i64 %conv12.i, 31
  %not.i = xor i64 %or12.i.i, -1
  %and.i = and i64 %or.i, %not.i
  %vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0
  %29 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %vecinit1.i.i.i, <2 x i64> <i64 -1, i64 0>, i8 0)
  %vecext.i.i.i = extractelement <2 x i64> %29, i64 0
  %xor.i = xor i64 %vecext.i.i.i, %st.sroa.7.035
  %shr.i = ashr i64 %xor.i, 63
  %30 = or i64 %or.i.i, %xor.i
  %31 = or i64 %30, %or5.i.i
  %or4 = or i64 %31, %and.i
  %not = xor i64 %or4, -1
  %not5 = xor i64 %xor.i, -1
  %and = and i64 %or5.i.i, %not5
  %shl7 = shl i64 %not, 1
  %or8 = or i64 %shl7, %prevS.039
  %not9 = xor i64 %or8, -1
  %and10 = and i64 %not9, %not
  %32 = or i64 %and, %and10
  %or11 = or i64 %32, %and.i
  %shr12 = lshr i64 %not, 63
  %sub = sub i64 %n, %shl
  %cmp14 = icmp ult i64 %sub, 64
  %notmask = shl i64 -1, %sub
  %sub16 = xor i64 %notmask, -1
  %and17 = select i1 %cmp14, i64 %sub16, i64 -1
  %e.0 = and i64 %or11, %and17
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.038
  store i64 %e.0, ptr %arrayidx
  br i1 %tobool.not, label %if.end20, label %if.then19

if.then19:                                        ; preds = %for.body
  %33 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  %34 = bitcast <8 x i64> %33 to <64 x i8>
  %35 = icmp ult <64 x i8> %34, splat (i8 32)
  %or25.i = bitcast <64 x i1> %35 to i64
  tail call void @leanllvm_json_escape_list(i64 %or14.i, i64 %or25.i, i64 %xor.i, i64 %i.038, ptr %xp, ptr %nxp, ptr %xcarry)
  br label %if.end20

if.end20:                                         ; preds = %if.then19, %for.body
  %inc = add i64 %i.038, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body
}
