; The UTF-8 unit as emitted, in the fragment the parser reads: the stage
; function @leanllvm_json_utf8, which is the ABI's only entry point.  Regenerate
; with:
;
;   nix develop -c bash probes/install/ir/capture-utf8.sh
;
; from kernel/json/utf8.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to that one `define` block.  `-fno-discard-value-names` is a
; naming flag: it names values and labels the entry block, which the parser
; requires, and the capture checks that it changes no instruction by emitting
; the source with and without it and comparing the two texts with every
; register name replaced by one placeholder.
;
; No other compiler or `opt` pass runs between the emission and this text.  The
; one `opt` invocation checks that the result is well-formed IR and not only a
; text the repository's parser reads, and it runs before the fixture is written:
;
;   opt -passes=verify -disable-output json-utf8.candidate.ll
;
; The emission's three parameters are the ABI's own names (%b, %n, %ungated),
; so the capture renames none; it refuses an emission whose parameter names are
; not those.
;
; There is no table read and no table rewrite.  The unit's three tables are
; `static const` arrays of 32 bytes and `_mm256_load_si256` of each folds to a
; literal `<32 x i8>` lane list in the `pshuf.b` call, so the fixture's
; difference set from the normalised emission is empty.  That is the one
; structural difference from the entry unit's fixture, which had to turn an
; aggregate table global into a parameter; here a `getelementptr` through a
; global is refused rather than rewritten, because it would mean the folding had
; stopped.
;
; The block count is `(n + 63) / 64`, derived from `n` alone: `n` is the
; document's length and the scanned byte string's length, so there is no second
; count for the two to disagree about.  The loop then runs over the document's
; 64-byte blocks and the tail runs once, after it.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-utf8.strip.tsv.  Nothing is rewritten: json-utf8.rewrites.tsv records why
; each kind of rewrite is absent, and its row count is zero.  The lines removed
; from the module carried:
;   source_filename = "kernel/json/utf8.c"
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   (the attribute groups, the three callee declarations and the module
;   metadata nodes are recorded in json-utf8.strip.tsv, where they are removed)
;
; The fixture's own opcodes and call targets are in json-utf8.inventory.
define i64 @leanllvm_json_utf8(ptr %b, i64 %n, i32 %ungated) {
entry:
  %add = add i64 %n, 63
  %div44 = lshr i64 %add, 6
  %cmp74.not = icmp ult i64 %add, 64
  br i1 %cmp74.not, label %for.cond.cleanup, label %for.body.lr.ph
for.body.lr.ph:
  %tobool.not = icmp eq i32 %ungated, 0
  br i1 %tobool.not, label %for.body.us, label %for.body
for.body.us:
  %prev_ascii.077.us = phi i32 [ %2, %if.end14.us ], [ 1, %for.body.lr.ph ]
  %u8k.076.us = phi <4 x i64> [ %u8k.2.us, %if.end14.us ], [ zeroinitializer, %for.body.lr.ph ]
  %bi.075.us = phi i64 [ %inc.us, %if.end14.us ], [ 0, %for.body.lr.ph ]
  %shl.us = shl i64 %bi.075.us, 6
  %add.ptr.us = getelementptr inbounds i8, ptr %b, i64 %shl.us
  %0 = load <4 x i64>, ptr %add.ptr.us
  %add.ptr3.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 32
  %1 = load <4 x i64>, ptr %add.ptr3.us
  %or.i46.us = or <4 x i64> %1, %0
  %2 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %or.i46.us, <4 x i64> splat (i64 -9187201950435737472))
  %tobool9.us = icmp ne i32 %2, 0
  %tobool10.us = icmp ne i32 %prev_ascii.077.us, 0
  %or.cond.us = and i1 %tobool9.us, %tobool10.us
  br i1 %or.cond.us, label %if.end14.us, label %if.then11.us
if.then11.us:
  %add.ptr.i.i48.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 -1
  %3 = load <4 x i64>, ptr %add.ptr.i.i48.us
  %add.ptr3.i.i49.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 -2
  %4 = load <32 x i8>, ptr %add.ptr3.i.i49.us
  %add.ptr5.i.i50.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 -3
  %5 = load <32 x i8>, ptr %add.ptr5.i.i50.us
  %6 = bitcast <4 x i64> %3 to <32 x i8>
  %7 = and <32 x i8> %6, splat (i8 15)
  %8 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %7)
  %9 = bitcast <4 x i64> %3 to <16 x i16>
  %10 = lshr <16 x i16> %9, splat (i16 4)
  %11 = bitcast <16 x i16> %10 to <32 x i8>
  %12 = and <32 x i8> %11, splat (i8 15)
  %13 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %12)
  %and.i3741.i.i51.us = and <32 x i8> %13, %8
  %14 = bitcast <4 x i64> %0 to <16 x i16>
  %15 = lshr <16 x i16> %14, splat (i16 4)
  %16 = bitcast <16 x i16> %15 to <32 x i8>
  %17 = and <32 x i8> %16, splat (i8 15)
  %18 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %17)
  %and.i3542.i.i52.us = and <32 x i8> %and.i3741.i.i51.us, %18
  %and.i35.i.i53.us = bitcast <32 x i8> %and.i3542.i.i52.us to <4 x i64>
  %elt.sat.i40.i.i54.us = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %4, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i55.us = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %5, <32 x i8> splat (i8 112))
  %or.i43.i.i56.us = or <32 x i8> %elt.sat.i.i.i55.us, %elt.sat.i40.i.i54.us
  %or.i.i.i57.us = bitcast <32 x i8> %or.i43.i.i56.us to <4 x i64>
  %and.i.i.i58.us = and <4 x i64> %or.i.i.i57.us, splat (i64 -9187201950435737472)
  %xor.i.i.i59.us = xor <4 x i64> %and.i.i.i58.us, %and.i35.i.i53.us
  %add.ptr.i4.i60.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 31
  %19 = load <4 x i64>, ptr %add.ptr.i4.i60.us
  %add.ptr3.i5.i61.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 30
  %20 = load <32 x i8>, ptr %add.ptr3.i5.i61.us
  %add.ptr5.i6.i62.us = getelementptr inbounds i8, ptr %add.ptr.us, i64 29
  %21 = load <32 x i8>, ptr %add.ptr5.i6.i62.us
  %22 = bitcast <4 x i64> %19 to <32 x i8>
  %23 = and <32 x i8> %22, splat (i8 15)
  %24 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %23)
  %25 = bitcast <4 x i64> %19 to <16 x i16>
  %26 = lshr <16 x i16> %25, splat (i16 4)
  %27 = bitcast <16 x i16> %26 to <32 x i8>
  %28 = and <32 x i8> %27, splat (i8 15)
  %29 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %28)
  %and.i3741.i7.i63.us = and <32 x i8> %29, %24
  %30 = bitcast <4 x i64> %1 to <16 x i16>
  %31 = lshr <16 x i16> %30, splat (i16 4)
  %32 = bitcast <16 x i16> %31 to <32 x i8>
  %33 = and <32 x i8> %32, splat (i8 15)
  %34 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %33)
  %and.i3542.i8.i64.us = and <32 x i8> %and.i3741.i7.i63.us, %34
  %and.i35.i9.i65.us = bitcast <32 x i8> %and.i3542.i8.i64.us to <4 x i64>
  %elt.sat.i40.i10.i66.us = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %20, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i67.us = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %21, <32 x i8> splat (i8 112))
  %or.i43.i12.i68.us = or <32 x i8> %elt.sat.i.i11.i67.us, %elt.sat.i40.i10.i66.us
  %or.i.i13.i69.us = bitcast <32 x i8> %or.i43.i12.i68.us to <4 x i64>
  %and.i.i14.i70.us = and <4 x i64> %or.i.i13.i69.us, splat (i64 -9187201950435737472)
  %xor.i.i15.i71.us = xor <4 x i64> %and.i.i14.i70.us, %and.i35.i9.i65.us
  %35 = or <4 x i64> %xor.i.i.i59.us, %xor.i.i15.i71.us
  %or.i.us = or <4 x i64> %35, %u8k.076.us
  br label %if.end14.us
if.end14.us:
  %u8k.2.us = phi <4 x i64> [ %u8k.076.us, %for.body.us ], [ %or.i.us, %if.then11.us ]
  %inc.us = add i64 %bi.075.us, 1
  %exitcond79.not = icmp eq i64 %inc.us, %div44
  br i1 %exitcond79.not, label %for.cond.cleanup, label %for.body.us
for.cond.cleanup:
  %u8k.0.lcssa = phi <4 x i64> [ zeroinitializer, %entry ], [ %u8k.2.us, %if.end14.us ], [ %or.i47, %for.body ]
  %36 = tail call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %u8k.0.lcssa, <4 x i64> %u8k.0.lcssa)
  %tobool16.not = icmp eq i32 %36, 0
  %tobool17.not = icmp ne i64 %n, 0
  %and = and i64 %n, 63
  %tobool19.not = icmp eq i64 %and, 0
  %or.cond45 = and i1 %tobool17.not, %tobool19.not
  br i1 %or.cond45, label %if.then20, label %if.end24
for.body:
  %u8k.076 = phi <4 x i64> [ %or.i47, %for.body ], [ zeroinitializer, %for.body.lr.ph ]
  %bi.075 = phi i64 [ %inc, %for.body ], [ 0, %for.body.lr.ph ]
  %shl = shl i64 %bi.075, 6
  %add.ptr = getelementptr inbounds i8, ptr %b, i64 %shl
  %37 = load <16 x i16>, ptr %add.ptr
  %add.ptr3 = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %38 = load <16 x i16>, ptr %add.ptr3
  %add.ptr.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -1
  %39 = load <4 x i64>, ptr %add.ptr.i.i
  %add.ptr3.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -2
  %40 = load <32 x i8>, ptr %add.ptr3.i.i
  %add.ptr5.i.i = getelementptr inbounds i8, ptr %add.ptr, i64 -3
  %41 = load <32 x i8>, ptr %add.ptr5.i.i
  %42 = bitcast <4 x i64> %39 to <32 x i8>
  %43 = and <32 x i8> %42, splat (i8 15)
  %44 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %43)
  %45 = bitcast <4 x i64> %39 to <16 x i16>
  %46 = lshr <16 x i16> %45, splat (i16 4)
  %47 = bitcast <16 x i16> %46 to <32 x i8>
  %48 = and <32 x i8> %47, splat (i8 15)
  %49 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %48)
  %and.i3741.i.i = and <32 x i8> %49, %44
  %50 = lshr <16 x i16> %37, splat (i16 4)
  %51 = bitcast <16 x i16> %50 to <32 x i8>
  %52 = and <32 x i8> %51, splat (i8 15)
  %53 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %52)
  %and.i3542.i.i = and <32 x i8> %and.i3741.i.i, %53
  %and.i35.i.i = bitcast <32 x i8> %and.i3542.i.i to <4 x i64>
  %elt.sat.i40.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %40, <32 x i8> splat (i8 96))
  %elt.sat.i.i.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %41, <32 x i8> splat (i8 112))
  %or.i43.i.i = or <32 x i8> %elt.sat.i.i.i, %elt.sat.i40.i.i
  %or.i.i.i = bitcast <32 x i8> %or.i43.i.i to <4 x i64>
  %and.i.i.i = and <4 x i64> %or.i.i.i, splat (i64 -9187201950435737472)
  %xor.i.i.i = xor <4 x i64> %and.i.i.i, %and.i35.i.i
  %add.ptr.i4.i = getelementptr inbounds i8, ptr %add.ptr, i64 31
  %54 = load <4 x i64>, ptr %add.ptr.i4.i
  %add.ptr3.i5.i = getelementptr inbounds i8, ptr %add.ptr, i64 30
  %55 = load <32 x i8>, ptr %add.ptr3.i5.i
  %add.ptr5.i6.i = getelementptr inbounds i8, ptr %add.ptr, i64 29
  %56 = load <32 x i8>, ptr %add.ptr5.i6.i
  %57 = bitcast <4 x i64> %54 to <32 x i8>
  %58 = and <32 x i8> %57, splat (i8 15)
  %59 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53, i8 -25, i8 -93, i8 -125, i8 -125, i8 -117, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -53, i8 -37, i8 -53, i8 -53>, <32 x i8> %58)
  %60 = bitcast <4 x i64> %54 to <16 x i16>
  %61 = lshr <16 x i16> %60, splat (i16 4)
  %62 = bitcast <16 x i16> %61 to <32 x i8>
  %63 = and <32 x i8> %62, splat (i8 15)
  %64 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 2, i8 -128, i8 -128, i8 -128, i8 -128, i8 33, i8 1, i8 21, i8 73>, <32 x i8> %63)
  %and.i3741.i7.i = and <32 x i8> %64, %59
  %65 = lshr <16 x i16> %38, splat (i16 4)
  %66 = bitcast <16 x i16> %65 to <32 x i8>
  %67 = and <32 x i8> %66, splat (i8 15)
  %68 = tail call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> <i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 1, i8 -26, i8 -82, i8 -70, i8 -70, i8 1, i8 1, i8 1, i8 1>, <32 x i8> %67)
  %and.i3542.i8.i = and <32 x i8> %and.i3741.i7.i, %68
  %and.i35.i9.i = bitcast <32 x i8> %and.i3542.i8.i to <4 x i64>
  %elt.sat.i40.i10.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %55, <32 x i8> splat (i8 96))
  %elt.sat.i.i11.i = tail call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %56, <32 x i8> splat (i8 112))
  %or.i43.i12.i = or <32 x i8> %elt.sat.i.i11.i, %elt.sat.i40.i10.i
  %or.i.i13.i = bitcast <32 x i8> %or.i43.i12.i to <4 x i64>
  %and.i.i14.i = and <4 x i64> %or.i.i13.i, splat (i64 -9187201950435737472)
  %xor.i.i15.i = xor <4 x i64> %and.i.i14.i, %and.i35.i9.i
  %or.i.i = or <4 x i64> %xor.i.i.i, %u8k.076
  %or.i47 = or <4 x i64> %or.i.i, %xor.i.i15.i
  %inc = add i64 %bi.075, 1
  %exitcond.not = icmp eq i64 %inc, %div44
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body
if.then20:
  %69 = getelementptr i8, ptr %b, i64 %n
  %arrayidx = getelementptr i8, ptr %69, i64 -1
  %70 = load i8, ptr %arrayidx
  %71 = and i8 %70, -2
  %cmp.i = icmp eq i8 %71, -64
  %cmp3.i = icmp ugt i8 %70, -12
  %72 = or i1 %cmp3.i, %cmp.i
  %or2373 = or i1 %tobool16.not, %72
  br label %if.end24
if.end24:
  %err.0.in = phi i1 [ %or2373, %if.then20 ], [ %tobool16.not, %for.cond.cleanup ]
  %err.0 = zext i1 %err.0.in to i64
  ret i64 %err.0
}
