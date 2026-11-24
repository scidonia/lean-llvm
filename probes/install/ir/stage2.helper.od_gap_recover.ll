; The stage-2 helper `od_gap_recover`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; symbol's address from, and od_gap_recover takes three: its llvm.umin.i64
; unfolds, each refusal site's message word becomes that site's tag, and the
; literal compare's three globals become appended pointer parameters.
; The body is captured as the fragment expresses it after its rewrites: its one llvm.umin.i64 unfolds (its literal compare takes an unsigned minimum at i64), each refusal record site stores its tag (`i64 1` number, `2` literal, `3` scalar, `4` extra token) where the text stores the message symbol because nothing loads the word and the model records which site ran, and the literal compare's three `@.str.*` operands become three appended pointer parameters, since a global constant is neither a declaration `parseModule` reads nor a symbol a lone `define` assembles against.  The callee and the two lifetime intrinsics are declared after the body for the same reason.
;
define void @od_gap_recover(ptr %c, i64 %t.0.val, ptr %littrue, ptr %litfalse, ptr %litnull) {
entry:
  %d = alloca double
  %ei = alloca i64
  %0 = load ptr, ptr %c
  %k = getelementptr inbounds i8, ptr %c, i64 32
  %1 = load i64, ptr %k
  %nix = getelementptr inbounds i8, ptr %c, i64 24
  %2 = load i64, ptr %nix
  %cmp = icmp ult i64 %1, %2
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %ix = getelementptr inbounds i8, ptr %c, i64 16
  %3 = load ptr, ptr %ix
  %arrayidx = getelementptr inbounds i32, ptr %3, i64 %1
  %4 = load i32, ptr %arrayidx
  %conv = zext i32 %4 to i64
  br label %cond.end

cond.false:                                       ; preds = %entry
  %n = getelementptr inbounds i8, ptr %c, i64 8
  %5 = load i64, ptr %n
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %conv, %cond.true ], [ %5, %cond.false ]
  %cmp310 = icmp ult i64 %t.0.val, %cond
  br i1 %cmp310, label %land.rhs, label %while.end

land.rhs:                                         ; preds = %while.body, %cond.end
  %ee.011 = phi i64 [ %inc, %while.body ], [ %t.0.val, %cond.end ]
  %arrayidx5 = getelementptr inbounds i8, ptr %0, i64 %ee.011
  %6 = load i8, ptr %arrayidx5
  br label %NodeBlock5

NodeBlock5:                                       ; preds = %land.rhs
  %Pivot6 = icmp slt i8 %6, 13
  br i1 %Pivot6, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock5
  %Pivot = icmp slt i8 %6, 32
  br i1 %Pivot, label %LeafBlock1, label %LeafBlock3

LeafBlock3:                                       ; preds = %NodeBlock
  %SwitchLeaf4 = icmp eq i8 %6, 32
  br i1 %SwitchLeaf4, label %while.end, label %while.body

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i8 %6, 13
  br i1 %SwitchLeaf2, label %while.end, label %while.body

LeafBlock:                                        ; preds = %NodeBlock5
  %.off = add i8 %6, -9
  %SwitchLeaf = icmp ule i8 %.off, 1
  br i1 %SwitchLeaf, label %while.end, label %while.body

while.body:                                       ; preds = %LeafBlock3, %LeafBlock1, %LeafBlock
  %inc = add i64 %ee.011, 1
  %exitcond.not = icmp eq i64 %inc, %cond
  br i1 %exitcond.not, label %cleanup82, label %land.rhs

while.end:                                        ; preds = %LeafBlock3, %LeafBlock1, %LeafBlock, %cond.end
  %ee.0.lcssa = phi i64 [ %t.0.val, %cond.end ], [ %ee.011, %LeafBlock ], [ %ee.011, %LeafBlock1 ], [ %ee.011, %LeafBlock3 ]
  %cmp6 = icmp eq i64 %ee.0.lcssa, %cond
  br i1 %cmp6, label %cleanup82, label %if.end

if.end:                                           ; preds = %while.end
  %arrayidx9 = getelementptr inbounds i8, ptr %0, i64 %t.0.val
  %7 = load i8, ptr %arrayidx9
  %cmp11 = icmp eq i8 %7, 45
  %8 = add i8 %7, -48
  %or.cond = icmp ult i8 %8, 10
  %or.cond127 = or i1 %cmp11, %or.cond
  br i1 %or.cond127, label %if.then19, label %if.else

if.then19:                                        ; preds = %if.end
  call void @llvm.lifetime.start.p0(i64 8, ptr %d)
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei)
  %sub = sub i64 %ee.0.lcssa, %t.0.val
  %call23 = call i32 @num_fast_el1(ptr %arrayidx9, i64 %sub, ptr %d, ptr %ei)
  %tobool24.not.not = icmp eq i32 %call23, 0
  br i1 %tobool24.not.not, label %if.then25, label %if.end67.critedge

if.then25:                                        ; preds = %if.then19
  %e = getelementptr inbounds i8, ptr %c, i64 1112
  %9 = load ptr, ptr %e
  %10 = load i64, ptr %ei
  %add = add i64 %10, %t.0.val
  store i32 0, ptr %9
  %off1.i = getelementptr inbounds i8, ptr %9, i64 8
  store i64 %add, ptr %off1.i
  %msg2.i = getelementptr inbounds i8, ptr %9, i64 16
  store i64 1, ptr %msg2.i
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d)
  br label %cleanup82

if.else:                                          ; preds = %if.end
  br label %NodeBlock15

NodeBlock15:                                      ; preds = %if.else
  %Pivot16 = icmp slt i8 %7, 110
  br i1 %Pivot16, label %LeafBlock7, label %NodeBlock13

NodeBlock13:                                      ; preds = %NodeBlock15
  %Pivot14 = icmp slt i8 %7, 116
  br i1 %Pivot14, label %LeafBlock9, label %LeafBlock11

LeafBlock11:                                      ; preds = %NodeBlock13
  %SwitchLeaf12 = icmp eq i8 %7, 116
  br i1 %SwitchLeaf12, label %if.end48, label %if.else43

LeafBlock9:                                       ; preds = %NodeBlock13
  %SwitchLeaf10 = icmp eq i8 %7, 110
  br i1 %SwitchLeaf10, label %if.then42, label %if.else43

LeafBlock7:                                       ; preds = %NodeBlock15
  %SwitchLeaf8 = icmp eq i8 %7, 102
  br i1 %SwitchLeaf8, label %if.then37, label %if.else43

if.then37:                                        ; preds = %LeafBlock7
  br label %if.end48

if.then42:                                        ; preds = %LeafBlock9
  br label %if.end48

if.else43:                                        ; preds = %LeafBlock11, %LeafBlock9, %LeafBlock7
  %e44 = getelementptr inbounds i8, ptr %c, i64 1112
  %11 = load ptr, ptr %e44
  store i32 0, ptr %11
  %off1.i129 = getelementptr inbounds i8, ptr %11, i64 8
  store i64 %t.0.val, ptr %off1.i129
  %msg2.i130 = getelementptr inbounds i8, ptr %11, i64 16
  store i64 3, ptr %msg2.i130
  br label %cleanup82

if.end48:                                         ; preds = %LeafBlock11, %if.then42, %if.then37
  %lit.0 = phi ptr [ %litfalse, %if.then37 ], [ %litnull, %if.then42 ], [ %littrue, %LeafBlock11 ]
  %ln.0 = phi i64 [ 5, %if.then37 ], [ 4, %if.then42 ], [ 4, %LeafBlock11 ]
  %sub54 = sub i64 %ee.0.lcssa, %t.0.val
  %cond.i.min = icmp ult i64 %sub54, %ln.0
  %cond.i = select i1 %cond.i.min, i64 %sub54, i64 %ln.0
  %cmp3.not28.not.i = icmp eq i64 %ee.0.lcssa, %t.0.val
  br i1 %cmp3.not28.not.i, label %for.end.i, label %for.body.i

for.body.i:                                       ; preds = %for.inc.i, %if.end48
  %i.029.i = phi i64 [ %inc.i, %for.inc.i ], [ 0, %if.end48 ]
  %arrayidx.i = getelementptr inbounds i8, ptr %arrayidx9, i64 %i.029.i
  %12 = load i8, ptr %arrayidx.i
  %arrayidx6.i = getelementptr inbounds i8, ptr %lit.0, i64 %i.029.i
  %13 = load i8, ptr %arrayidx6.i
  %cmp8.not.i = icmp eq i8 %12, %13
  br i1 %cmp8.not.i, label %for.inc.i, label %if.then57

for.inc.i:                                        ; preds = %for.body.i
  %inc.i = add i64 %i.029.i, 1
  %exitcond.not.i = icmp eq i64 %inc.i, %cond.i
  br i1 %exitcond.not.i, label %for.end.i, label %for.body.i

for.end.i:                                        ; preds = %for.inc.i, %if.end48
  %cmp11.not.i = icmp eq i64 %sub54, %ln.0
  br i1 %cmp11.not.i, label %if.end67, label %if.then57

if.then57:                                        ; preds = %for.end.i, %for.body.i
  %ei49.0.ph = phi i64 [ %cond.i, %for.end.i ], [ %i.029.i, %for.body.i ]
  %e58 = getelementptr inbounds i8, ptr %c, i64 1112
  %14 = load ptr, ptr %e58
  %add60 = add i64 %ei49.0.ph, %t.0.val
  store i32 0, ptr %14
  %off1.i131 = getelementptr inbounds i8, ptr %14, i64 8
  store i64 %add60, ptr %off1.i131
  %msg2.i132 = getelementptr inbounds i8, ptr %14, i64 16
  store i64 2, ptr %msg2.i132
  br label %cleanup82

if.end67.critedge:                                ; preds = %if.then19
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d)
  br label %if.end67

if.end67:                                         ; preds = %if.end67.critedge, %for.end.i
  %cmp6919 = icmp ult i64 %ee.0.lcssa, %cond
  br i1 %cmp6919, label %land.rhs71, label %while.end78

land.rhs71:                                       ; preds = %while.body76, %if.end67
  %s2.020 = phi i64 [ %inc77, %while.body76 ], [ %ee.0.lcssa, %if.end67 ]
  %arrayidx72 = getelementptr inbounds i8, ptr %0, i64 %s2.020
  %15 = load i8, ptr %arrayidx72
  br label %NodeBlock26

NodeBlock26:                                      ; preds = %land.rhs71
  %Pivot27 = icmp slt i8 %15, 13
  br i1 %Pivot27, label %LeafBlock17, label %NodeBlock24

NodeBlock24:                                      ; preds = %NodeBlock26
  %Pivot25 = icmp slt i8 %15, 32
  br i1 %Pivot25, label %LeafBlock20, label %LeafBlock22

LeafBlock22:                                      ; preds = %NodeBlock24
  %SwitchLeaf23 = icmp eq i8 %15, 32
  br i1 %SwitchLeaf23, label %while.body76, label %while.end78

LeafBlock20:                                      ; preds = %NodeBlock24
  %SwitchLeaf21 = icmp eq i8 %15, 13
  br i1 %SwitchLeaf21, label %while.body76, label %while.end78

LeafBlock17:                                      ; preds = %NodeBlock26
  %.off18 = add i8 %15, -9
  %SwitchLeaf19 = icmp ule i8 %.off18, 1
  br i1 %SwitchLeaf19, label %while.body76, label %while.end78

while.body76:                                     ; preds = %LeafBlock22, %LeafBlock20, %LeafBlock17
  %inc77 = add i64 %s2.020, 1
  %exitcond24.not = icmp eq i64 %inc77, %cond
  br i1 %exitcond24.not, label %while.end78, label %land.rhs71

while.end78:                                      ; preds = %LeafBlock22, %LeafBlock20, %LeafBlock17, %while.body76, %if.end67
  %s2.0.lcssa = phi i64 [ %ee.0.lcssa, %if.end67 ], [ %cond, %while.body76 ], [ %s2.020, %LeafBlock17 ], [ %s2.020, %LeafBlock20 ], [ %s2.020, %LeafBlock22 ]
  %e79 = getelementptr inbounds i8, ptr %c, i64 1112
  %16 = load ptr, ptr %e79
  store i32 0, ptr %16
  %off1.i137 = getelementptr inbounds i8, ptr %16, i64 8
  store i64 %s2.0.lcssa, ptr %off1.i137
  %msg2.i138 = getelementptr inbounds i8, ptr %16, i64 16
  store i64 4, ptr %msg2.i138
  br label %cleanup82

cleanup82:                                        ; preds = %while.end78, %if.then57, %if.else43, %if.then25, %while.end, %while.body
  ret void
}

; The callee and the intrinsics the body calls, so the fixture assembles.
declare i32 @num_fast_el1(ptr, i64, ptr, ptr)
declare void @llvm.lifetime.start.p0(i64, ptr)
declare void @llvm.lifetime.end.p0(i64, ptr)
