; The stage-2 helper `s2_value_pos`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; `ashr exact` loses its flag.  s2_string_body takes one: its refusal message
; becomes `null`, because the call boundary has no global table to read the
; symbol's address from.  The body is captured and the fragment expresses it.
;
define i32 @s2_value_pos(i32 %sp, i32 %root_done, ptr %ct, ptr %cs) {
entry:
  %cmp = icmp eq i32 %sp, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %tobool.not = icmp eq i32 %root_done, 0
  br label %return

if.end:                                           ; preds = %entry
  %sub = add i32 %sp, -1
  %idxprom = zext i32 %sub to i64
  %arrayidx = getelementptr inbounds i8, ptr %ct, i64 %idxprom
  %0 = load i8, ptr %arrayidx
  %cmp1 = icmp eq i8 %0, 1
  %arrayidx5 = getelementptr inbounds i8, ptr %cs, i64 %idxprom
  %1 = load i8, ptr %arrayidx5
  br i1 %cmp1, label %if.then3, label %if.end9

if.then3:                                         ; preds = %if.end
  %cmp7 = icmp eq i8 %1, 2
  br label %return

if.end9:                                          ; preds = %if.end
  %2 = and i8 %1, -3
  %narrow = icmp eq i8 %2, 0
  br label %return

return:                                           ; preds = %if.end9, %if.then3, %if.then
  %retval.1.in = phi i1 [ %tobool.not, %if.then ], [ %cmp7, %if.then3 ], [ %narrow, %if.end9 ]
  %retval.1 = zext i1 %retval.1.in to i32
  ret i32 %retval.1
}
