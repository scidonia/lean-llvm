; The stage-2 helper `s2_after_value`, as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; `noinline` on every helper except s2_walk, the same token strip
; capture-stage2.sh applies.  od_scalar_value takes the walk's own three
; rewrites — its conversion slot becomes a pointer parameter, its messages
; become `null`, and its one llvm.umin.i64 unfolds — and num_fast_el1 takes
; two of the same kind: its llvm.umin.i64 folds to the icmp/select pair, and
; `ashr exact` loses its flag.  The body is captured and the fragment expresses it.
;
define void @s2_after_value(i32 %sp.0.val, ptr %root_done, ptr %ct, ptr %cs) {
entry:
  %cmp = icmp eq i32 %sp.0.val, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i32 1, ptr %root_done
  br label %return

if.end:                                           ; preds = %entry
  %sub = add i32 %sp.0.val, -1
  %idxprom = zext i32 %sub to i64
  %arrayidx = getelementptr inbounds i8, ptr %ct, i64 %idxprom
  %0 = load i8, ptr %arrayidx
  %cmp1 = icmp eq i8 %0, 1
  %conv3 = select i1 %cmp1, i8 3, i8 1
  %arrayidx5 = getelementptr inbounds i8, ptr %cs, i64 %idxprom
  store i8 %conv3, ptr %arrayidx5
  br label %return

return:                                           ; preds = %if.end, %if.then
  ret void
}
