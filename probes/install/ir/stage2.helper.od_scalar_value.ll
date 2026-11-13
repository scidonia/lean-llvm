; The stage-2 helper `od_scalar_value`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; `ashr exact` loses its flag.  The body is captured as the fragment expresses it; its accepted path calls `num_fast_el1`, whose own body is `stage2.helper.num_fast_el1.ll`.
;
define i32 @od_scalar_value(ptr %c, ptr %t, ptr %o, ptr %d) {
entry:
  %ei = alloca i64
  %0 = load ptr, ptr %c
  %1 = load i64, ptr %t
  %arrayidx = getelementptr inbounds i8, ptr %0, i64 %1
  %kind = getelementptr inbounds i8, ptr %t, i64 16
  %2 = load i32, ptr %kind
  br label %NodeBlock

NodeBlock:                                        ; preds = %entry
  %Pivot = icmp slt i32 %2, 7
  br i1 %Pivot, label %LeafBlock, label %LeafBlock1

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i32 %2, 7
  br i1 %SwitchLeaf2, label %if.then4, label %if.end20

LeafBlock:                                        ; preds = %NodeBlock
  %SwitchLeaf = icmp eq i32 %2, 0
  br i1 %SwitchLeaf, label %if.then, label %if.end20

if.then:                                          ; preds = %LeafBlock
  %3 = getelementptr i8, ptr %c, i64 1112
  %c.val95 = load ptr, ptr %3
  store i32 0, ptr %c.val95
  %off1.i.i = getelementptr inbounds i8, ptr %c.val95, i64 8
  store i64 %1, ptr %off1.i.i
  %msg2.i.i = getelementptr inbounds i8, ptr %c.val95, i64 16
  store ptr null, ptr %msg2.i.i
  br label %cleanup64

if.then4:                                         ; preds = %LeafBlock1
  call void @llvm.lifetime.start.p0(i64 8, ptr %d)
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei)
  %end = getelementptr inbounds i8, ptr %t, i64 8
  %4 = load i64, ptr %end
  %sub = sub i64 %4, %1
  %call8 = call i32 @num_fast_el1(ptr %arrayidx, i64 %sub, ptr %d, ptr %ei)
  %tobool.not = icmp eq i32 %call8, 0
  br i1 %tobool.not, label %if.then9, label %if.then14

if.then9:                                         ; preds = %if.then4
  %5 = load i64, ptr %t
  %6 = load i64, ptr %ei
  %add = add i64 %6, %5
  %7 = getelementptr i8, ptr %c, i64 1112
  %c.val94 = load ptr, ptr %7
  store i32 0, ptr %c.val94
  %off1.i.i96 = getelementptr inbounds i8, ptr %c.val94, i64 8
  store i64 %add, ptr %off1.i.i96
  %msg2.i.i97 = getelementptr inbounds i8, ptr %c.val94, i64 16
  store ptr null, ptr %msg2.i.i97
  br label %cleanup

if.then14:                                        ; preds = %if.then4
  %hash.i.i = getelementptr inbounds i8, ptr %o, i64 32
  %8 = load i32, ptr %hash.i.i
  %tobool.not.i.i = icmp eq i32 %8, 0
  br i1 %tobool.not.i.i, label %if.end.i.i, label %if.then.i.i

if.then.i.i:                                      ; preds = %if.then14
  %h1.i.i.i = getelementptr inbounds i8, ptr %o, i64 24
  %9 = load i64, ptr %h1.i.i.i
  %xor.us.i.i.i = xor i64 %9, 7
  %10 = mul i64 %xor.us.i.i.i, -2358710677322311239
  %mul11.i.i.i = add i64 %10, -7046029254386353131
  store i64 %mul11.i.i.i, ptr %h1.i.i.i
  br label %out_tag.exit

if.end.i.i:                                       ; preds = %if.then14
  %11 = getelementptr i8, ptr %o, i64 8
  %o.val.i.i = load i64, ptr %11
  %12 = getelementptr i8, ptr %o, i64 16
  %o.val11.i.i = load i64, ptr %12
  %add.i.i.i = add i64 %o.val.i.i, 1
  %cmp.not.i.i.i = icmp ugt i64 %add.i.i.i, %o.val11.i.i
  br i1 %cmp.not.i.i.i, label %if.end.i.i.i, label %out_reserve.exit.i.i

if.end.i.i.i:                                     ; preds = %if.end.i.i
  tail call void @llvm.trap()
  unreachable

out_reserve.exit.i.i:                             ; preds = %if.end.i.i
  %13 = load ptr, ptr %o
  %add.ptr.i.i = getelementptr inbounds i8, ptr %13, i64 %o.val.i.i
  store i8 7, ptr %add.ptr.i.i
  %14 = load i64, ptr %11
  %add.i.i = add i64 %14, 1
  store i64 %add.i.i, ptr %11
  %.pre = load i32, ptr %hash.i.i
  %15 = icmp eq i32 %.pre, 0
  br label %out_tag.exit

out_tag.exit:                                     ; preds = %out_reserve.exit.i.i, %if.then.i.i
  %tobool.not.i.i99 = phi i1 [ false, %if.then.i.i ], [ %15, %out_reserve.exit.i.i ]
  %16 = load i64, ptr %d
  br i1 %tobool.not.i.i99, label %if.end.i.i104, label %if.then.i.i100

if.then.i.i100:                                   ; preds = %out_tag.exit
  %h1.i.i.i101 = getelementptr inbounds i8, ptr %o, i64 24
  %17 = load i64, ptr %h1.i.i.i101
  %xor.us.i.i.i102 = xor i64 %16, %17
  %18 = mul i64 %xor.us.i.i.i102, -2358710677322311239
  %mul11.i.i.i103 = add i64 %18, -1028001813962170200
  store i64 %mul11.i.i.i103, ptr %h1.i.i.i101
  br label %cleanup

if.end.i.i104:                                    ; preds = %out_tag.exit
  %19 = getelementptr i8, ptr %o, i64 8
  %o.val.i.i105 = load i64, ptr %19
  %20 = getelementptr i8, ptr %o, i64 16
  %o.val11.i.i106 = load i64, ptr %20
  %add.i.i.i107 = add i64 %o.val.i.i105, 8
  %cmp.not.i.i.i108 = icmp ugt i64 %add.i.i.i107, %o.val11.i.i106
  br i1 %cmp.not.i.i.i108, label %if.end.i.i.i113, label %out_reserve.exit.i.i109

if.end.i.i.i113:                                  ; preds = %if.end.i.i104
  tail call void @llvm.trap()
  unreachable

out_reserve.exit.i.i109:                          ; preds = %if.end.i.i104
  %21 = load ptr, ptr %o
  %add.ptr.i.i110 = getelementptr inbounds i8, ptr %21, i64 %o.val.i.i105
  store i64 %16, ptr %add.ptr.i.i110
  %22 = load i64, ptr %19
  %add.i.i112 = add i64 %22, 8
  store i64 %add.i.i112, ptr %19
  br label %cleanup

cleanup:                                          ; preds = %out_reserve.exit.i.i109, %if.then.i.i100, %if.then9
  %retval.0 = phi i32 [ 0, %if.then9 ], [ 1, %if.then.i.i100 ], [ 1, %out_reserve.exit.i.i109 ]
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d)
  br label %cleanup64

if.end20:                                         ; preds = %LeafBlock1, %LeafBlock
  %23 = load i8, ptr %arrayidx
  br label %NodeBlock11

NodeBlock11:                                      ; preds = %if.end20
  %Pivot12 = icmp slt i8 %23, 110
  br i1 %Pivot12, label %LeafBlock3, label %NodeBlock9

NodeBlock9:                                       ; preds = %NodeBlock11
  %Pivot10 = icmp slt i8 %23, 116
  br i1 %Pivot10, label %LeafBlock5, label %LeafBlock7

LeafBlock7:                                       ; preds = %NodeBlock9
  %SwitchLeaf8 = icmp eq i8 %23, 116
  br i1 %SwitchLeaf8, label %if.end39, label %if.else34

LeafBlock5:                                       ; preds = %NodeBlock9
  %SwitchLeaf6 = icmp eq i8 %23, 110
  br i1 %SwitchLeaf6, label %if.then33, label %if.else34

LeafBlock3:                                       ; preds = %NodeBlock11
  %SwitchLeaf4 = icmp eq i8 %23, 102
  br i1 %SwitchLeaf4, label %if.then28, label %if.else34

if.then28:                                        ; preds = %LeafBlock3
  br label %if.end39

if.then33:                                        ; preds = %LeafBlock5
  br label %if.end39

if.else34:                                        ; preds = %LeafBlock7, %LeafBlock5, %LeafBlock3
  %24 = getelementptr i8, ptr %c, i64 1112
  %c.val93 = load ptr, ptr %24
  store i32 0, ptr %c.val93
  %off1.i.i114 = getelementptr inbounds i8, ptr %c.val93, i64 8
  store i64 %1, ptr %off1.i.i114
  %msg2.i.i115 = getelementptr inbounds i8, ptr %c.val93, i64 16
  store ptr null, ptr %msg2.i.i115
  br label %cleanup64

if.end39:                                         ; preds = %LeafBlock7, %if.then33, %if.then28
  %lit.0 = phi ptr [ null, %if.then28 ], [ null, %if.then33 ], [ null, %LeafBlock7 ]
  %ln.0 = phi i64 [ 5, %if.then28 ], [ 4, %if.then33 ], [ 4, %LeafBlock7 ]
  %tag.0 = phi i8 [ 9, %if.then28 ], [ 10, %if.then33 ], [ 8, %LeafBlock7 ]
  %end44 = getelementptr inbounds i8, ptr %t, i64 8
  %25 = load i64, ptr %end44
  %sub46 = sub i64 %25, %1
  %cond.i.min = icmp ult i64 %sub46, %ln.0
  %cond.i = select i1 %cond.i.min, i64 %sub46, i64 %ln.0
  %cmp3.not28.not.i = icmp eq i64 %25, %1
  br i1 %cmp3.not28.not.i, label %for.end.i, label %for.body.i

for.body.i:                                       ; preds = %for.inc.i, %if.end39
  %i.029.i = phi i64 [ %inc.i, %for.inc.i ], [ 0, %if.end39 ]
  %arrayidx.i = getelementptr inbounds i8, ptr %arrayidx, i64 %i.029.i
  %26 = load i8, ptr %arrayidx.i
  %arrayidx6.i = getelementptr inbounds i8, ptr %lit.0, i64 %i.029.i
  %27 = load i8, ptr %arrayidx6.i
  %cmp8.not.i = icmp eq i8 %26, %27
  br i1 %cmp8.not.i, label %for.inc.i, label %if.then49

for.inc.i:                                        ; preds = %for.body.i
  %inc.i = add i64 %i.029.i, 1
  %exitcond.not.i = icmp eq i64 %inc.i, %cond.i
  br i1 %exitcond.not.i, label %for.end.i, label %for.body.i

for.end.i:                                        ; preds = %for.inc.i, %if.end39
  %cmp11.not.i = icmp eq i64 %sub46, %ln.0
  br i1 %cmp11.not.i, label %if.then55, label %if.then49

if.then49:                                        ; preds = %for.end.i, %for.body.i
  %ei40.0.ph = phi i64 [ %cond.i, %for.end.i ], [ %i.029.i, %for.body.i ]
  %add51 = add i64 %ei40.0.ph, %1
  %28 = getelementptr i8, ptr %c, i64 1112
  %c.val = load ptr, ptr %28
  store i32 0, ptr %c.val
  %off1.i.i117 = getelementptr inbounds i8, ptr %c.val, i64 8
  store i64 %add51, ptr %off1.i.i117
  %msg2.i.i118 = getelementptr inbounds i8, ptr %c.val, i64 16
  store ptr null, ptr %msg2.i.i118
  br label %cleanup64

if.then55:                                        ; preds = %for.end.i
  %hash.i.i120 = getelementptr inbounds i8, ptr %o, i64 32
  %29 = load i32, ptr %hash.i.i120
  %tobool.not.i.i121 = icmp eq i32 %29, 0
  br i1 %tobool.not.i.i121, label %if.end.i.i126, label %if.then.i.i122

if.then.i.i122:                                   ; preds = %if.then55
  %h1.i.i.i123 = getelementptr inbounds i8, ptr %o, i64 24
  %30 = load i64, ptr %h1.i.i.i123
  %conv.i.i.i = zext i8 %tag.0 to i64
  %xor.us.i.i.i124 = xor i64 %30, %conv.i.i.i
  %31 = mul i64 %xor.us.i.i.i124, -2358710677322311239
  %mul11.i.i.i125 = add i64 %31, -7046029254386353131
  store i64 %mul11.i.i.i125, ptr %h1.i.i.i123
  br label %cleanup64

if.end.i.i126:                                    ; preds = %if.then55
  %32 = getelementptr i8, ptr %o, i64 8
  %o.val.i.i127 = load i64, ptr %32
  %33 = getelementptr i8, ptr %o, i64 16
  %o.val11.i.i128 = load i64, ptr %33
  %add.i.i.i129 = add i64 %o.val.i.i127, 1
  %cmp.not.i.i.i130 = icmp ugt i64 %add.i.i.i129, %o.val11.i.i128
  br i1 %cmp.not.i.i.i130, label %if.end.i.i.i135, label %out_reserve.exit.i.i131

if.end.i.i.i135:                                  ; preds = %if.end.i.i126
  tail call void @llvm.trap()
  unreachable

out_reserve.exit.i.i131:                          ; preds = %if.end.i.i126
  %34 = load ptr, ptr %o
  %add.ptr.i.i132 = getelementptr inbounds i8, ptr %34, i64 %o.val.i.i127
  store i8 %tag.0, ptr %add.ptr.i.i132
  %35 = load i64, ptr %32
  %add.i.i134 = add i64 %35, 1
  store i64 %add.i.i134, ptr %32
  br label %cleanup64

cleanup64:                                        ; preds = %out_reserve.exit.i.i131, %if.then.i.i122, %if.then49, %if.else34, %cleanup, %if.then
  %retval.3 = phi i32 [ 0, %if.then ], [ %retval.0, %cleanup ], [ 0, %if.else34 ], [ 0, %if.then49 ], [ 1, %if.then.i.i122 ], [ 1, %out_reserve.exit.i.i131 ]
  ret i32 %retval.3
}
