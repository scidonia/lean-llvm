; The stage-2 helper `s2_string_body`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; `ashr exact` loses its flag.  The body is a program of this fragment: its `ptrtoint` pair and its `@.str.14` symbol operand are both modelled, and `JsonStage2HelperIR` pins the AST it parses to.
;
define i32 @s2_string_body(ptr %c, ptr %p, i64 %len, ptr %dst, ptr %outn, ptr %xp, ptr %xj, i64 %nxp) {
entry:
  %ei = alloca i64
  %0 = load ptr, ptr %c
  %sub.ptr.lhs.cast = ptrtoint ptr %p to i64
  %sub.ptr.rhs.cast = ptrtoint ptr %0 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %xj.promoted = load i64, ptr %xj
  %cmp3 = icmp ult i64 %xj.promoted, %nxp
  br i1 %cmp3, label %land.rhs, label %if.then

land.rhs:                                         ; preds = %while.body, %entry
  %inc24 = phi i64 [ %inc, %while.body ], [ %xj.promoted, %entry ]
  %arrayidx = getelementptr inbounds i32, ptr %xp, i64 %inc24
  %1 = load i32, ptr %arrayidx
  %conv = zext i32 %1 to i64
  %cmp1 = icmp ugt i64 %sub.ptr.sub, %conv
  br i1 %cmp1, label %while.body, label %land.lhs.true

while.body:                                       ; preds = %land.rhs
  %inc = add i64 %inc24, 1
  store i64 %inc, ptr %xj
  %exitcond.not = icmp eq i64 %inc, %nxp
  br i1 %exitcond.not, label %if.then, label %land.rhs

land.lhs.true:                                    ; preds = %land.rhs
  %add = add i64 %sub.ptr.sub, %len
  %cmp7 = icmp ugt i64 %add, %conv
  br i1 %cmp7, label %if.end, label %if.then

if.then:                                          ; preds = %land.lhs.true, %while.body, %entry
  store i64 %len, ptr %outn
  br label %cleanup16

if.end:                                           ; preds = %land.lhs.true
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei)
  store i64 0, ptr %ei
  %call = call i64 @leanllvm_json_escape_expand(ptr %p, i64 %len, ptr %dst, ptr %ei, ptr %xp, ptr %xj, i64 %nxp, i64 %sub.ptr.sub)
  %cmp9 = icmp eq i64 %call, -1
  br i1 %cmp9, label %if.then11, label %if.end14

if.then11:                                        ; preds = %if.end
  %2 = load i64, ptr %ei
  %add12 = add i64 %2, %sub.ptr.sub
  %3 = getelementptr i8, ptr %c, i64 1112
  %c.val = load ptr, ptr %3
  store i32 0, ptr %c.val
  %off1.i.i = getelementptr inbounds i8, ptr %c.val, i64 8
  store i64 %add12, ptr %off1.i.i
  %msg2.i.i = getelementptr inbounds i8, ptr %c.val, i64 16
  store ptr @.str.14, ptr %msg2.i.i
  br label %cleanup

if.end14:                                         ; preds = %if.end
  store i64 %call, ptr %outn
  br label %cleanup

cleanup:                                          ; preds = %if.end14, %if.then11
  %retval.0 = phi i32 [ 0, %if.then11 ], [ 2, %if.end14 ]
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  br label %cleanup16

cleanup16:                                        ; preds = %cleanup, %if.then
  %retval.1 = phi i32 [ %retval.0, %cleanup ], [ 1, %if.then ]
  ret i32 %retval.1
}
