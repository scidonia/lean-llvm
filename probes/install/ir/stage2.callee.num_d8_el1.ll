; The stage-2 callee `num_d8_el1`, as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; `noinline` on every helper and on `stk_mul_u64`, then the same token strip
; capture-stage2.sh applies.  `num_d8_el1` takes two of the same strip rewrites `num_fast_el1` does — its `llvm.umin.i64` folds to the icmp/select pair and `ashr exact` loses its flag — and one substitution: its three literal vectors carry `poison` in lanes the body overwrites or never reads, and each becomes the defined lane 0, as `capture-escape.sh` does for the hex reader's constants.  `stage2.callees.rewrites.tsv` accounts for every substitution.  Its eight-byte read is the body's own `load i64`, and its two `madd` calls are the x86 intrinsics `escapeCalls` already answers.
;
define i32 @num_d8_el1(ptr %p, ptr %val) {
entry:
  %0 = load i64, ptr %p
  %vecinit1.i = insertelement <2 x i64> <i64 0, i64 0>, i64 %0, i64 0
  %1 = bitcast <2 x i64> %vecinit1.i to <16 x i8>
  %sub.i = add <16 x i8> %1, splat (i8 -48)
  %cmp.i = icmp ult <16 x i8> %sub.i, splat (i8 10)
  %2 = bitcast <16 x i1> %cmp.i to i16
  %3 = and i16 %2, 255
  %cmp.not = icmp eq i16 %3, 255
  br i1 %cmp.not, label %if.end, label %cleanup

if.end:                                           ; preds = %entry
  %4 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %sub.i, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>)
  %5 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %4, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 0, i16 0, i16 0, i16 0>)
  %vecext.i = extractelement <4 x i32> %5, i64 0
  %mul = mul i32 %vecext.i, 10000
  %6 = extractelement <4 x i32> %5, i64 1
  %add = add i32 %mul, %6
  store i32 %add, ptr %val
  br label %cleanup

cleanup:                                          ; preds = %if.end, %entry
  %retval.0 = phi i32 [ 1, %if.end ], [ 0, %entry ]
  ret i32 %retval.0
}
