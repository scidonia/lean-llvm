; The stage-2 callee `num_el_el1`, as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; `noinline` on every helper and on `stk_mul_u64`, then the same token strip
; capture-stage2.sh applies.  `num_el_el1` calls `el_exact` and `el_pack` out of line and reads the `EPOW` table through a global symbol operand, so it is not a closed unit: its fixture needs those two bodies and the table staged before it denotes.  Its one rewrite is the `llvm.ctlz.i64` flag: the emission writes `i1 true` and the fixture holds `i1 false`, because the parser admits only the `false` form and the entry's `%w == 0` return keeps the zero word off the path to the call, so the two flags agree wherever the body executes; `stage2.callees.rewrites.tsv` records the row.
;
define i32 @num_el_el1(i64 %w, i64 %q, ptr %out) {
entry:
  %cmp2 = icmp eq i64 %w, 0
  br i1 %cmp2, label %if.then3, label %if.end4

if.then3:                                         ; preds = %entry
  store double 0.000000e+00, ptr %out
  br label %return

if.end4:                                          ; preds = %entry
  %sub = add i64 %q, 45
  %arrayidx = getelementptr inbounds [91 x %struct.EPow], ptr @EPOW, i64 0, i64 %sub
  %0 = tail call i64 @llvm.ctlz.i64(i64 %w, i1 false)
  %cast = trunc i64 %0 to i32
  %shl = shl i64 %w, %0
  %conv = zext i64 %shl to i128
  %1 = load i64, ptr %arrayidx
  %conv5 = zext i64 %1 to i128
  %mul = mul i128 %conv5, %conv
  %shr = lshr i128 %mul, 64
  %conv6 = trunc i128 %shr to i64
  %shr7 = lshr i64 %conv6, 63
  %conv8 = trunc i64 %shr7 to i32
  %shl9 = shl i64 %shr7, 10
  %or = or i64 %shl9, 1023
  %and = and i64 %or, %conv6
  %shl11 = shl i32 512, %conv8
  %conv12 = zext i32 %shl11 to i64
  %reass.sub = sub i64 %and, %conv12
  %sub14 = add i64 %reass.sub, 2
  %cmp15 = icmp ult i64 %sub14, 3
  br i1 %cmp15, label %if.then18, label %if.end19

if.then18:                                        ; preds = %if.end4
  %2 = load i64, ptr @g_el_window
  %inc = add i64 %2, 1
  store i64 %inc, ptr @g_el_window
  %call = tail call i32 @el_exact(i64 %shl, i32 %cast, ptr %arrayidx, i64 %q, ptr %out)
  br label %return

if.end19:                                         ; preds = %if.end4
  %add = or i64 %shr7, 10
  %shr21 = lshr i64 %conv6, %add
  %cmp22 = icmp samesign ugt i64 %and, %conv12
  %conv23 = zext i1 %cmp22 to i32
  %3 = getelementptr i8, ptr %arrayidx, i64 16
  %arrayidx.val = load i32, ptr %3
  %call24 = tail call i32 @el_pack(i64 %shr21, i32 %conv23, i32 %conv8, i32 %arrayidx.val, i32 %cast, ptr %out)
  br label %return

return:                                           ; preds = %if.end19, %if.then18, %if.then3
  %retval.1 = phi i32 [ 1, %if.then3 ], [ %call, %if.then18 ], [ %call24, %if.end19 ]
  ret i32 %retval.1
}
