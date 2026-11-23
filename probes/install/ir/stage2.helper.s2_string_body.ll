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
; `ashr exact` loses its flag.  s2_string_body takes one: its refusal message
; becomes `null`, because the call boundary has no global table to read the
; symbol's address from.  The body is a program of this fragment: its `ptrtoint` pair is modelled, and `JsonStage2StringBody` pins the AST it parses to and proves the helper contract of that body.  Its refusal message is `null` here — the call boundary carries no global table — so this fixture is not where `Operand.global`'s body-level evidence lives; that evidence is tests/core-extension.lean's acceptance pins.
;
define i32 @s2_string_body(ptr %c, ptr %p, i64 %len, ptr %dst, ptr %outn, ptr %xp, ptr %xj, i64 %nxp) {
entry:
  %ei = alloca i64
  %0 = load ptr, ptr %c
  %sub.ptr.lhs.cast = ptrtoint ptr %p to i64
  %sub.ptr.rhs.cast = ptrtoint ptr %0 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei)
  %tobool.not = icmp eq i64 %nxp, 0
  br i1 %tobool.not, label %if.end16, label %while.cond.preheader

while.cond.preheader:                             ; preds = %entry
  %xj.promoted = load i64, ptr %xj
  %cmp3 = icmp ult i64 %xj.promoted, %nxp
  br i1 %cmp3, label %land.rhs, label %if.then9

land.rhs:                                         ; preds = %while.body, %while.cond.preheader
  %inc24 = phi i64 [ %inc, %while.body ], [ %xj.promoted, %while.cond.preheader ]
  %arrayidx = getelementptr inbounds i32, ptr %xp, i64 %inc24
  %1 = load i32, ptr %arrayidx
  %conv = zext i32 %1 to i64
  %cmp1 = icmp ugt i64 %sub.ptr.sub, %conv
  br i1 %cmp1, label %while.body, label %land.lhs.true

while.body:                                       ; preds = %land.rhs
  %inc = add i64 %inc24, 1
  store i64 %inc, ptr %xj
  %exitcond.not = icmp eq i64 %inc, %nxp
  br i1 %exitcond.not, label %if.then9, label %land.rhs

land.lhs.true:                                    ; preds = %land.rhs
  %add = add i64 %sub.ptr.sub, %len
  %cmp7 = icmp ugt i64 %add, %conv
  br i1 %cmp7, label %if.end, label %if.then9

if.then9:                                         ; preds = %land.lhs.true, %while.body, %while.cond.preheader
  store i64 %len, ptr %outn
  br label %cleanup47

if.end:                                           ; preds = %land.lhs.true
  store i64 0, ptr %ei
  %call = call i64 @leanllvm_json_escape_expand(ptr %p, i64 %len, ptr %dst, ptr %ei, ptr %xp, ptr %xj, i64 %nxp, i64 %sub.ptr.sub)
  %cmp10 = icmp eq i64 %call, -1
  br i1 %cmp10, label %if.then12, label %if.end15

if.then12:                                        ; preds = %if.end
  %2 = load i64, ptr %ei
  %add13 = add i64 %2, %sub.ptr.sub
  %3 = getelementptr i8, ptr %c, i64 1112
  %c.val95 = load ptr, ptr %3
  store i32 0, ptr %c.val95
  %off1.i.i = getelementptr inbounds i8, ptr %c.val95, i64 8
  store i64 %add13, ptr %off1.i.i
  %msg2.i.i = getelementptr inbounds i8, ptr %c.val95, i64 16
  store ptr null, ptr %msg2.i.i
  br label %cleanup47

if.end15:                                         ; preds = %if.end
  store i64 %call, ptr %outn
  br label %cleanup47

if.end16:                                         ; preds = %entry
  %call17 = tail call i64 @z_scan(ptr %p, i64 %len)
  %cmp18 = icmp eq i64 %call17, -1
  br i1 %cmp18, label %if.then20, label %if.end21

if.then20:                                        ; preds = %if.end16
  store i64 %len, ptr %outn
  br label %cleanup47

if.end21:                                         ; preds = %if.end16
  %arrayidx22 = getelementptr inbounds i8, ptr %p, i64 %call17
  %4 = load i8, ptr %arrayidx22
  %cmp24.not = icmp eq i8 %4, 92
  br i1 %cmp24.not, label %if.end29, label %if.then26

if.then26:                                        ; preds = %if.end21
  %add27 = add i64 %call17, %sub.ptr.sub
  %5 = getelementptr i8, ptr %c, i64 1112
  %c.val94 = load ptr, ptr %5
  store i32 0, ptr %c.val94
  %off1.i.i96 = getelementptr inbounds i8, ptr %c.val94, i64 8
  store i64 %add27, ptr %off1.i.i96
  %msg2.i.i97 = getelementptr inbounds i8, ptr %c.val94, i64 16
  store ptr null, ptr %msg2.i.i97
  br label %cleanup47

if.end29:                                         ; preds = %if.end21
  store i64 0, ptr %ei
  %sub = sub i64 %len, %call17
  %add.ptr31 = getelementptr inbounds i8, ptr %dst, i64 %call17
  %call32 = call i64 @leanllvm_json_escape_decode(ptr %arrayidx22, i64 %sub, ptr %add.ptr31, ptr %ei)
  %cmp33 = icmp eq i64 %call32, -1
  br i1 %cmp33, label %if.then35, label %if.end39

if.then35:                                        ; preds = %if.end29
  %add36 = add i64 %call17, %sub.ptr.sub
  %6 = load i64, ptr %ei
  %add37 = add i64 %add36, %6
  %7 = getelementptr i8, ptr %c, i64 1112
  %c.val = load ptr, ptr %7
  store i32 0, ptr %c.val
  %off1.i.i98 = getelementptr inbounds i8, ptr %c.val, i64 8
  store i64 %add37, ptr %off1.i.i98
  %msg2.i.i99 = getelementptr inbounds i8, ptr %c.val, i64 16
  store ptr null, ptr %msg2.i.i99
  br label %cleanup47

if.end39:                                         ; preds = %if.end29
  %tobool40.not = icmp eq i64 %call17, 0
  br i1 %tobool40.not, label %if.end43, label %if.then41

if.then41:                                        ; preds = %if.end39
  call void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %p, i64 %call17, i1 false)
  br label %if.end43

if.end43:                                         ; preds = %if.then41, %if.end39
  %add44 = add i64 %call32, %call17
  store i64 %add44, ptr %outn
  br label %cleanup47

cleanup47:                                        ; preds = %if.end43, %if.then35, %if.then26, %if.then20, %if.end15, %if.then12, %if.then9
  %retval.3 = phi i32 [ 1, %if.then9 ], [ 0, %if.then12 ], [ 2, %if.end15 ], [ 1, %if.then20 ], [ 0, %if.then26 ], [ 0, %if.then35 ], [ 2, %if.end43 ]
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  ret i32 %retval.3
}
