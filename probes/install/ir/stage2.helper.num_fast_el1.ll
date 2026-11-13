; The stage-2 helper `num_fast_el1`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; symbol's address from.  The body is a program of this fragment after its two strip rewrites (the `llvm.umin.i64` fold and the dropped `exact` flag) and with the extent of `%struct.Stk` supplied as the `Layout` `[("Stk", 1568)]` the pin states, which is the number the body own `llvm.lifetime.start` names.  `JsonStage2HelperIR` pins the AST it parses to.
;
define i32 @num_fast_el1(ptr %p, i64 %n, ptr %out, ptr %err) {
entry:
  %dig.i.i = alloca [768 x i8]
  %v.i.i = alloca %struct.Stk
  %v8 = alloca i32
  %v8101 = alloca i32
  %d269 = alloca double
  %cmp.not = icmp eq i64 %n, 0
  br i1 %cmp.not, label %if.end, label %land.lhs.true

land.lhs.true:                                    ; preds = %entry
  %0 = load i8, ptr %p
  %cmp1 = icmp ne i8 %0, 45
  %not.cmp1 = xor i1 %cmp1, true
  %spec.select439 = zext i1 %not.cmp1 to i64
  br label %if.end

if.end:                                           ; preds = %land.lhs.true, %entry
  %tobool274.not = phi i1 [ true, %entry ], [ %cmp1, %land.lhs.true ]
  %i.0 = phi i64 [ 0, %entry ], [ %spec.select439, %land.lhs.true ]
  %cmp3.not = icmp ult i64 %i.0, %n
  br i1 %cmp3.not, label %if.end6, label %if.then5

if.then5:                                         ; preds = %if.end
  store i64 %i.0, ptr %err
  br label %cleanup300

if.end6:                                          ; preds = %if.end
  %arrayidx7 = getelementptr inbounds i8, ptr %p, i64 %i.0
  %1 = load i8, ptr %arrayidx7
  %cmp9 = icmp eq i8 %1, 48
  br i1 %cmp9, label %if.then11, label %if.else

if.then11:                                        ; preds = %if.end6
  %inc12 = add i64 %i.0, 1
  br label %if.end68

if.else:                                          ; preds = %if.end6
  %2 = add i8 %1, -49
  %or.cond = icmp ult i8 %2, 9
  br i1 %or.cond, label %if.then22, label %if.else66

if.then22:                                        ; preds = %if.else
  %3 = and i8 %1, 15
  %conv25 = zext i8 %3 to i64
  %inc26 = add i64 %i.0, 1
  %add563 = add i64 %i.0, 9
  %cmp27564.not = icmp ugt i64 %add563, %n
  br i1 %cmp27564.not, label %while.end, label %while.body.preheader

while.body.preheader:                             ; preds = %if.then22
  call void @llvm.lifetime.start.p0(i64 4, ptr %v8)
  %add.ptr930 = getelementptr inbounds i8, ptr %p, i64 %inc26
  %call931 = call i32 @num_d8_el1(ptr %add.ptr930, ptr %v8)
  %tobool.not932 = icmp eq i32 %call931, 0
  br i1 %tobool.not932, label %cleanup.thread, label %cleanup

while.body:                                       ; preds = %cleanup
  %add29 = add i64 %add29569933, 8
  call void @llvm.lifetime.start.p0(i64 4, ptr %v8)
  %add.ptr = getelementptr inbounds i8, ptr %p, i64 %add568934
  %call = call i32 @num_d8_el1(ptr %add.ptr, ptr %v8)
  %tobool.not = icmp eq i32 %call, 0
  br i1 %tobool.not, label %cleanup.thread, label %cleanup

cleanup.thread:                                   ; preds = %while.body, %while.body.preheader
  %i.1567.lcssa = phi i64 [ %inc26, %while.body.preheader ], [ %add568934, %while.body ]
  %idig.0566.lcssa = phi i64 [ 1, %while.body.preheader ], [ %add29569933, %while.body ]
  %ip.0565.lcssa = phi i64 [ %conv25, %while.body.preheader ], [ %add35, %while.body ]
  call void @llvm.lifetime.end.p0(i64 4, ptr %v8)
  br label %while.end

cleanup:                                          ; preds = %while.body, %while.body.preheader
  %ip.0565935 = phi i64 [ %add35, %while.body ], [ %conv25, %while.body.preheader ]
  %add568934 = phi i64 [ %add, %while.body ], [ %add563, %while.body.preheader ]
  %add29569933 = phi i64 [ %add29, %while.body ], [ 9, %while.body.preheader ]
  %mul = mul i64 %ip.0565935, 100000000
  %4 = load i32, ptr %v8
  %conv34 = zext i32 %4 to i64
  %add35 = add i64 %mul, %conv34
  call void @llvm.lifetime.end.p0(i64 4, ptr %v8)
  %add = add i64 %add568934, 8
  %cmp27 = icmp ule i64 %add, %n
  %cmp30 = icmp samesign ult i64 %add29569933, 12
  %5 = select i1 %cmp27, i1 %cmp30, i1 false
  br i1 %5, label %while.body, label %while.end

while.end:                                        ; preds = %cleanup, %cleanup.thread, %if.then22
  %ip.0562 = phi i64 [ %ip.0565.lcssa, %cleanup.thread ], [ %conv25, %if.then22 ], [ %add35, %cleanup ]
  %idig.0560 = phi i64 [ %idig.0566.lcssa, %cleanup.thread ], [ 1, %if.then22 ], [ %add29569933, %cleanup ]
  %i.1558 = phi i64 [ %i.1567.lcssa, %cleanup.thread ], [ %inc26, %if.then22 ], [ %add568934, %cleanup ]
  %cmp39572 = icmp ult i64 %i.1558, %n
  br i1 %cmp39572, label %land.lhs.true41.preheader, label %if.end68

land.lhs.true41.preheader:                        ; preds = %while.end
  %6 = add i64 %idig.0560, %n
  %7 = sub i64 %6, %i.1558
  br label %land.lhs.true41

land.lhs.true41:                                  ; preds = %if.end62, %land.lhs.true41.preheader
  %i.4575 = phi i64 [ %inc64, %if.end62 ], [ %i.1558, %land.lhs.true41.preheader ]
  %idig.3574 = phi i64 [ %inc63, %if.end62 ], [ %idig.0560, %land.lhs.true41.preheader ]
  %ip.3573 = phi i64 [ %ip.4, %if.end62 ], [ %ip.0562, %land.lhs.true41.preheader ]
  %arrayidx42 = getelementptr inbounds i8, ptr %p, i64 %i.4575
  %8 = load i8, ptr %arrayidx42
  %9 = add i8 %8, -48
  %or.cond440 = icmp ult i8 %9, 10
  br i1 %or.cond440, label %while.body52, label %if.end68

while.body52:                                     ; preds = %land.lhs.true41
  %cmp53 = icmp ult i64 %idig.3574, 19
  br i1 %cmp53, label %if.then55, label %if.end62

if.then55:                                        ; preds = %while.body52
  %mul56 = mul i64 %ip.3573, 10
  %10 = and i8 %8, 15
  %conv60 = zext i8 %10 to i64
  %add61 = add i64 %mul56, %conv60
  br label %if.end62

if.end62:                                         ; preds = %if.then55, %while.body52
  %ip.4 = phi i64 [ %add61, %if.then55 ], [ %ip.3573, %while.body52 ]
  %inc63 = add i64 %idig.3574, 1
  %inc64 = add i64 %i.4575, 1
  %exitcond.not = icmp eq i64 %inc64, %n
  br i1 %exitcond.not, label %if.end230, label %land.lhs.true41

if.else66:                                        ; preds = %if.else
  store i64 %i.0, ptr %err
  br label %cleanup300

if.end68:                                         ; preds = %land.lhs.true41, %while.end, %if.then11
  %ip.5 = phi i64 [ 0, %if.then11 ], [ %ip.0562, %while.end ], [ %ip.3573, %land.lhs.true41 ]
  %idig.4 = phi i64 [ 1, %if.then11 ], [ %idig.0560, %while.end ], [ %idig.3574, %land.lhs.true41 ]
  %i.5 = phi i64 [ %inc12, %if.then11 ], [ %i.1558, %while.end ], [ %i.4575, %land.lhs.true41 ]
  %cmp69 = icmp ult i64 %i.5, %n
  br i1 %cmp69, label %land.lhs.true71, label %if.end144

land.lhs.true71:                                  ; preds = %if.end68
  %arrayidx72 = getelementptr inbounds i8, ptr %p, i64 %i.5
  %11 = load i8, ptr %arrayidx72
  %cmp74 = icmp eq i8 %11, 46
  br i1 %cmp74, label %if.then76, label %if.end144

if.then76:                                        ; preds = %land.lhs.true71
  %inc77 = add i64 %i.5, 1
  %cmp78.not = icmp ult i64 %inc77, %n
  br i1 %cmp78.not, label %lor.lhs.false, label %if.then89

lor.lhs.false:                                    ; preds = %if.then76
  %arrayidx80 = getelementptr inbounds i8, ptr %p, i64 %inc77
  %12 = load i8, ptr %arrayidx80
  %13 = add i8 %12, -58
  %or.cond441 = icmp ult i8 %13, -10
  br i1 %or.cond441, label %if.then89, label %while.cond91.preheader

while.cond91.preheader:                           ; preds = %lor.lhs.false
  %add92582 = add i64 %i.5, 9
  %cmp93583.not = icmp ugt i64 %add92582, %n
  br i1 %cmp93583.not, label %while.end115, label %while.body100.preheader

while.body100.preheader:                          ; preds = %while.cond91.preheader
  call void @llvm.lifetime.start.p0(i64 4, ptr %v8101)
  %add.ptr102938 = getelementptr inbounds i8, ptr %p, i64 %inc77
  %call103939 = call i32 @num_d8_el1(ptr %add.ptr102938, ptr %v8101)
  %tobool104.not940 = icmp eq i32 %call103939, 0
  br i1 %tobool104.not940, label %cleanup112.thread, label %cleanup112

if.then89:                                        ; preds = %lor.lhs.false, %if.then76
  store i64 %inc77, ptr %err
  br label %cleanup300

while.body100:                                    ; preds = %cleanup112
  %add96 = add i64 %add96588941, 8
  call void @llvm.lifetime.start.p0(i64 4, ptr %v8101)
  %add.ptr102 = getelementptr inbounds i8, ptr %p, i64 %add92587942
  %call103 = call i32 @num_d8_el1(ptr %add.ptr102, ptr %v8101)
  %tobool104.not = icmp eq i32 %call103, 0
  br i1 %tobool104.not, label %cleanup112.thread, label %cleanup112

cleanup112.thread:                                ; preds = %while.body100, %while.body100.preheader
  %i.6586.lcssa = phi i64 [ %inc77, %while.body100.preheader ], [ %add92587942, %while.body100 ]
  %fdig.0585.lcssa = phi i64 [ 0, %while.body100.preheader ], [ %add96588941, %while.body100 ]
  %fr.0584.lcssa = phi i64 [ 0, %while.body100.preheader ], [ %add109, %while.body100 ]
  call void @llvm.lifetime.end.p0(i64 4, ptr %v8101)
  br label %while.end115

cleanup112:                                       ; preds = %while.body100, %while.body100.preheader
  %fr.0584943 = phi i64 [ %add109, %while.body100 ], [ 0, %while.body100.preheader ]
  %add92587942 = phi i64 [ %add92, %while.body100 ], [ %add92582, %while.body100.preheader ]
  %add96588941 = phi i64 [ %add96, %while.body100 ], [ 8, %while.body100.preheader ]
  %mul107 = mul i64 %fr.0584943, 100000000
  %14 = load i32, ptr %v8101
  %conv108 = zext i32 %14 to i64
  %add109 = add i64 %mul107, %conv108
  call void @llvm.lifetime.end.p0(i64 4, ptr %v8101)
  %add92 = add i64 %add92587942, 8
  %cmp93 = icmp ule i64 %add92, %n
  %cmp97 = icmp samesign ult i64 %add96588941, 12
  %15 = select i1 %cmp93, i1 %cmp97, i1 false
  br i1 %15, label %while.body100, label %while.end115

while.end115:                                     ; preds = %cleanup112, %cleanup112.thread, %while.cond91.preheader
  %fr.0556 = phi i64 [ %fr.0584.lcssa, %cleanup112.thread ], [ 0, %while.cond91.preheader ], [ %add109, %cleanup112 ]
  %fdig.0554 = phi i64 [ %fdig.0585.lcssa, %cleanup112.thread ], [ 0, %while.cond91.preheader ], [ %add96588941, %cleanup112 ]
  %i.6552 = phi i64 [ %i.6586.lcssa, %cleanup112.thread ], [ %inc77, %while.cond91.preheader ], [ %add92587942, %cleanup112 ]
  %cmp117592 = icmp ult i64 %i.6552, %n
  br i1 %cmp117592, label %land.lhs.true119.preheader, label %if.end144

land.lhs.true119.preheader:                       ; preds = %while.end115
  %16 = add i64 %fdig.0554, %n
  %17 = sub i64 %16, %i.6552
  br label %land.lhs.true119

land.lhs.true119:                                 ; preds = %if.end140, %land.lhs.true119.preheader
  %i.9595 = phi i64 [ %inc142, %if.end140 ], [ %i.6552, %land.lhs.true119.preheader ]
  %fdig.3594 = phi i64 [ %inc141, %if.end140 ], [ %fdig.0554, %land.lhs.true119.preheader ]
  %fr.3593 = phi i64 [ %fr.4, %if.end140 ], [ %fr.0556, %land.lhs.true119.preheader ]
  %arrayidx120 = getelementptr inbounds i8, ptr %p, i64 %i.9595
  %18 = load i8, ptr %arrayidx120
  %19 = add i8 %18, -48
  %or.cond443 = icmp ult i8 %19, 10
  br i1 %or.cond443, label %while.body130, label %if.end144

while.body130:                                    ; preds = %land.lhs.true119
  %cmp131 = icmp ult i64 %fdig.3594, 19
  br i1 %cmp131, label %if.then133, label %if.end140

if.then133:                                       ; preds = %while.body130
  %mul134 = mul i64 %fr.3593, 10
  %20 = and i8 %18, 15
  %conv138 = zext i8 %20 to i64
  %add139 = add i64 %mul134, %conv138
  br label %if.end140

if.end140:                                        ; preds = %if.then133, %while.body130
  %fr.4 = phi i64 [ %add139, %if.then133 ], [ %fr.3593, %while.body130 ]
  %inc141 = add i64 %fdig.3594, 1
  %inc142 = add i64 %i.9595, 1
  %exitcond702.not = icmp eq i64 %inc142, %n
  br i1 %exitcond702.not, label %if.end230, label %land.lhs.true119

if.end144:                                        ; preds = %land.lhs.true119, %while.end115, %land.lhs.true71, %if.end68
  %fr.5 = phi i64 [ 0, %land.lhs.true71 ], [ 0, %if.end68 ], [ %fr.0556, %while.end115 ], [ %fr.3593, %land.lhs.true119 ]
  %fdig.4 = phi i64 [ 0, %land.lhs.true71 ], [ 0, %if.end68 ], [ %fdig.0554, %while.end115 ], [ %fdig.3594, %land.lhs.true119 ]
  %i.10 = phi i64 [ %i.5, %land.lhs.true71 ], [ %i.5, %if.end68 ], [ %i.6552, %while.end115 ], [ %i.9595, %land.lhs.true119 ]
  %cmp145 = icmp ult i64 %i.10, %n
  br i1 %cmp145, label %land.lhs.true147, label %if.end226

land.lhs.true147:                                 ; preds = %if.end144
  %arrayidx148 = getelementptr inbounds i8, ptr %p, i64 %i.10
  %21 = load i8, ptr %arrayidx148
  br label %NodeBlock

NodeBlock:                                        ; preds = %land.lhs.true147
  %Pivot = icmp slt i8 %21, 101
  br i1 %Pivot, label %LeafBlock, label %LeafBlock1

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i8 %21, 101
  br i1 %SwitchLeaf2, label %if.then157, label %if.end226

LeafBlock:                                        ; preds = %NodeBlock
  %SwitchLeaf = icmp eq i8 %21, 69
  br i1 %SwitchLeaf, label %if.then157, label %if.end226

if.then157:                                       ; preds = %LeafBlock1, %LeafBlock
  %inc158 = add i64 %i.10, 1
  %cmp159 = icmp ult i64 %inc158, %n
  br i1 %cmp159, label %land.lhs.true161, label %if.end177

land.lhs.true161:                                 ; preds = %if.then157
  %arrayidx162 = getelementptr inbounds i8, ptr %p, i64 %inc158
  %22 = load i8, ptr %arrayidx162
  br label %NodeBlock7

NodeBlock7:                                       ; preds = %land.lhs.true161
  %Pivot8 = icmp slt i8 %22, 45
  br i1 %Pivot8, label %LeafBlock3, label %LeafBlock5

LeafBlock5:                                       ; preds = %NodeBlock7
  %SwitchLeaf6 = icmp eq i8 %22, 45
  br i1 %SwitchLeaf6, label %if.then171, label %if.end177

LeafBlock3:                                       ; preds = %NodeBlock7
  %SwitchLeaf4 = icmp eq i8 %22, 43
  br i1 %SwitchLeaf4, label %if.then171, label %if.end177

if.then171:                                       ; preds = %LeafBlock5, %LeafBlock3
  %cmp174 = icmp ne i8 %22, 45
  %inc176 = add i64 %i.10, 2
  br label %if.end177

if.end177:                                        ; preds = %LeafBlock5, %LeafBlock3, %if.then171, %if.then157
  %esign.0 = phi i1 [ %cmp174, %if.then171 ], [ true, %if.then157 ], [ true, %LeafBlock3 ], [ true, %LeafBlock5 ]
  %i.11 = phi i64 [ %inc176, %if.then171 ], [ %inc158, %if.then157 ], [ %inc158, %LeafBlock3 ], [ %inc158, %LeafBlock5 ]
  %cmp178.not = icmp ult i64 %i.11, %n
  br i1 %cmp178.not, label %lor.lhs.false180, label %cleanup223

lor.lhs.false180:                                 ; preds = %if.end177
  %arrayidx181 = getelementptr inbounds i8, ptr %p, i64 %i.11
  %23 = load i8, ptr %arrayidx181
  %24 = add i8 %23, -58
  %or.cond444 = icmp ult i8 %24, -10
  br i1 %or.cond444, label %cleanup223, label %land.lhs.true195

land.lhs.true195:                                 ; preds = %if.end216, %lor.lhs.false180
  %i.12604 = phi i64 [ %inc217, %if.end216 ], [ %i.11, %lor.lhs.false180 ]
  %exp10.0603 = phi i64 [ %exp10.1, %if.end216 ], [ 0, %lor.lhs.false180 ]
  %arrayidx196 = getelementptr inbounds i8, ptr %p, i64 %i.12604
  %25 = load i8, ptr %arrayidx196
  %26 = add i8 %25, -48
  %or.cond445 = icmp ult i8 %26, 10
  br i1 %or.cond445, label %while.body206, label %cleanup223.thread

while.body206:                                    ; preds = %land.lhs.true195
  %cmp207 = icmp slt i64 %exp10.0603, 100000
  br i1 %cmp207, label %if.then209, label %if.end216

if.then209:                                       ; preds = %while.body206
  %mul210 = mul i64 %exp10.0603, 10
  %27 = and i8 %25, 15
  %conv214 = zext i8 %27 to i64
  %add215 = add i64 %mul210, %conv214
  br label %if.end216

if.end216:                                        ; preds = %if.then209, %while.body206
  %exp10.1 = phi i64 [ %add215, %if.then209 ], [ %exp10.0603, %while.body206 ]
  %inc217 = add i64 %i.12604, 1
  %exitcond703.not = icmp eq i64 %inc217, %n
  br i1 %exitcond703.not, label %cleanup223.thread, label %land.lhs.true195

cleanup223.thread:                                ; preds = %if.end216, %land.lhs.true195
  %exp10.0.lcssa.ph = phi i64 [ %exp10.0603, %land.lhs.true195 ], [ %exp10.1, %if.end216 ]
  %i.12.lcssa.ph = phi i64 [ %i.12604, %land.lhs.true195 ], [ %n, %if.end216 ]
  %sub221 = sub i64 0, %exp10.0.lcssa.ph
  %spec.select446 = select i1 %esign.0, i64 %exp10.0.lcssa.ph, i64 %sub221
  br label %if.end226

cleanup223:                                       ; preds = %lor.lhs.false180, %if.end177
  store i64 %i.11, ptr %err
  br label %cleanup300

if.end226:                                        ; preds = %LeafBlock1, %LeafBlock, %cleanup223.thread, %if.end144
  %exp10.4 = phi i64 [ 0, %if.end144 ], [ %spec.select446, %cleanup223.thread ], [ 0, %LeafBlock ], [ 0, %LeafBlock1 ]
  %i.14 = phi i64 [ %i.10, %if.end144 ], [ %i.12.lcssa.ph, %cleanup223.thread ], [ %i.10, %LeafBlock ], [ %i.10, %LeafBlock1 ]
  %cmp227.not = icmp eq i64 %i.14, %n
  br i1 %cmp227.not, label %if.end230, label %if.then229

if.then229:                                       ; preds = %if.end226
  store i64 %i.14, ptr %err
  br label %cleanup300

if.end230:                                        ; preds = %if.end226, %if.end140, %if.end62
  %exp10.4731 = phi i64 [ %exp10.4, %if.end226 ], [ 0, %if.end140 ], [ 0, %if.end62 ]
  %idig.4709716730 = phi i64 [ %idig.4, %if.end226 ], [ %idig.4, %if.end140 ], [ %7, %if.end62 ]
  %ip.5708717729 = phi i64 [ %ip.5, %if.end226 ], [ %ip.5, %if.end140 ], [ %ip.4, %if.end62 ]
  %fr.5718728 = phi i64 [ %fr.5, %if.end226 ], [ %fr.4, %if.end140 ], [ 0, %if.end62 ]
  %fdig.4719727 = phi i64 [ %fdig.4, %if.end226 ], [ %17, %if.end140 ], [ 0, %if.end62 ]
  %sub231 = sub i64 %exp10.4731, %fdig.4719727
  %add232 = add i64 %fdig.4719727, %idig.4709716730
  %cmp233 = icmp ult i64 %add232, 20
  %28 = add i64 %sub231, 45
  %29 = icmp ult i64 %28, 91
  %or.cond304 = select i1 %cmp233, i1 %29, i1 false
  br i1 %or.cond304, label %if.then241, label %if.end285

if.then241:                                       ; preds = %if.end230
  %arrayidx242 = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %fdig.4719727
  %30 = load i64, ptr %arrayidx242
  %mul243 = mul i64 %30, %ip.5708717729
  %add244 = add i64 %mul243, %fr.5718728
  %cmp245 = icmp samesign ult i64 %add232, 16
  %31 = add i64 %sub231, 22
  %32 = icmp ult i64 %31, 45
  %or.cond306 = select i1 %cmp245, i1 %32, i1 false
  br i1 %or.cond306, label %if.then253, label %if.end268

if.then253:                                       ; preds = %if.then241
  %cmp254 = icmp sgt i64 %sub231, -1
  %conv256 = uitofp i64 %add244 to double
  br i1 %cmp254, label %cond.true, label %cond.false

cond.true:                                        ; preds = %if.then253
  %arrayidx257 = getelementptr inbounds [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %sub231
  %33 = load double, ptr %arrayidx257
  %mul258 = fmul double %33, %conv256
  br label %cleanup282.thread

cond.false:                                       ; preds = %if.then253
  %sub260 = sub i64 0, %sub231
  %arrayidx261 = getelementptr inbounds [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %sub260
  %34 = load double, ptr %arrayidx261
  %div = fdiv double %conv256, %34
  br label %cleanup282.thread

cleanup282.thread:                                ; preds = %cond.false, %cond.true
  %cond = phi double [ %mul258, %cond.true ], [ %div, %cond.false ]
  %fneg = fneg double %cond
  %cond266 = select i1 %tobool274.not, double %cond, double %fneg
  store double %cond266, ptr %out
  br label %cleanup300

if.end268:                                        ; preds = %if.then241
  call void @llvm.lifetime.start.p0(i64 8, ptr %d269)
  %call270 = call i32 @num_el_el1(i64 %add244, i64 %sub231, ptr %d269)
  %tobool271.not = icmp eq i32 %call270, 0
  br i1 %tobool271.not, label %cleanup282.thread462, label %cleanup282

cleanup282.thread462:                             ; preds = %if.end268
  call void @llvm.lifetime.end.p0(i64 8, ptr %d269)
  br label %if.end285

cleanup282:                                       ; preds = %if.end268
  %35 = load i64, ptr @g_nume1_el
  %inc273 = add i64 %35, 1
  store i64 %inc273, ptr @g_nume1_el
  %36 = load double, ptr %d269
  %fneg276 = fneg double %36
  %cond279 = select i1 %tobool274.not, double %36, double %fneg276
  store double %cond279, ptr %out
  call void @llvm.lifetime.end.p0(i64 8, ptr %d269)
  br label %cleanup300

if.end285:                                        ; preds = %cleanup282.thread462, %if.end230
  %37 = load i64, ptr @g_nume1_slow
  %inc287 = add i64 %37, 1
  store i64 %inc287, ptr @g_nume1_slow
  %38 = load i8, ptr %p
  %cmp1.i = icmp eq i8 %38, 45
  %i.0.i = zext i1 %cmp1.i to i64
  %cmp3.not.i = icmp ugt i64 %n, %i.0.i
  br i1 %cmp3.not.i, label %if.end6.i, label %if.then5.i

if.then5.i:                                       ; preds = %if.end285
  store i64 1, ptr %err
  br label %cleanup300

if.end6.i:                                        ; preds = %if.end285
  %arrayidx7.i = getelementptr inbounds i8, ptr %p, i64 %i.0.i
  %39 = load i8, ptr %arrayidx7.i
  %cmp9.i = icmp eq i8 %39, 48
  br i1 %cmp9.i, label %if.then11.i, label %if.else.i

if.then11.i:                                      ; preds = %if.end6.i
  %inc12.i = select i1 %cmp1.i, i64 2, i64 1
  br label %if.end37.i

if.else.i:                                        ; preds = %if.end6.i
  %40 = add i8 %39, -49
  %or.cond.i = icmp ult i8 %40, 9
  br i1 %or.cond.i, label %land.lhs.true25.i, label %if.else35.i

land.lhs.true25.i:                                ; preds = %while.body.i, %if.else.i
  %i.1262.i = phi i64 [ %inc34.i, %while.body.i ], [ %i.0.i, %if.else.i ]
  %arrayidx26.i = getelementptr inbounds i8, ptr %p, i64 %i.1262.i
  %41 = load i8, ptr %arrayidx26.i
  %42 = add i8 %41, -48
  %or.cond222.i = icmp ult i8 %42, 10
  br i1 %or.cond222.i, label %while.body.i, label %if.end37.i

while.body.i:                                     ; preds = %land.lhs.true25.i
  %inc34.i = add i64 %i.1262.i, 1
  %exitcond.not.i = icmp eq i64 %inc34.i, %n
  br i1 %exitcond.not.i, label %if.then143.i, label %land.lhs.true25.i

if.else35.i:                                      ; preds = %if.else.i
  store i64 %i.0.i, ptr %err
  br label %cleanup300

if.end37.i:                                       ; preds = %land.lhs.true25.i, %if.then11.i
  %i.2.i = phi i64 [ %inc12.i, %if.then11.i ], [ %i.1262.i, %land.lhs.true25.i ]
  %cmp38.i = icmp ult i64 %i.2.i, %n
  br i1 %cmp38.i, label %land.lhs.true40.i, label %if.end77.i

land.lhs.true40.i:                                ; preds = %if.end37.i
  %arrayidx41.i = getelementptr inbounds i8, ptr %p, i64 %i.2.i
  %43 = load i8, ptr %arrayidx41.i
  %cmp43.i = icmp eq i8 %43, 46
  br i1 %cmp43.i, label %if.then45.i, label %if.end77.i

if.then45.i:                                      ; preds = %land.lhs.true40.i
  %inc46.i = add i64 %i.2.i, 1
  %cmp47.not.i = icmp ult i64 %inc46.i, %n
  br i1 %cmp47.not.i, label %lor.lhs.false.i, label %if.then58.i

lor.lhs.false.i:                                  ; preds = %if.then45.i
  %arrayidx49.i = getelementptr inbounds i8, ptr %p, i64 %inc46.i
  %44 = load i8, ptr %arrayidx49.i
  %45 = add i8 %44, -58
  %or.cond223.i = icmp ult i8 %45, -10
  br i1 %or.cond223.i, label %if.then58.i, label %land.lhs.true63.i

if.then58.i:                                      ; preds = %lor.lhs.false.i, %if.then45.i
  store i64 %inc46.i, ptr %err
  br label %cleanup300

land.lhs.true63.i:                                ; preds = %while.body74.i, %lor.lhs.false.i
  %i.3265.i = phi i64 [ %inc75.i, %while.body74.i ], [ %inc46.i, %lor.lhs.false.i ]
  %arrayidx64.i = getelementptr inbounds i8, ptr %p, i64 %i.3265.i
  %46 = load i8, ptr %arrayidx64.i
  %47 = add i8 %46, -48
  %or.cond224.i = icmp ult i8 %47, 10
  br i1 %or.cond224.i, label %while.body74.i, label %if.end77.i

while.body74.i:                                   ; preds = %land.lhs.true63.i
  %inc75.i = add i64 %i.3265.i, 1
  %exitcond306.not.i = icmp eq i64 %inc75.i, %n
  br i1 %exitcond306.not.i, label %if.then143.i, label %land.lhs.true63.i

if.end77.i:                                       ; preds = %land.lhs.true63.i, %land.lhs.true40.i, %if.end37.i
  %i.4.i = phi i64 [ %i.2.i, %land.lhs.true40.i ], [ %i.2.i, %if.end37.i ], [ %i.3265.i, %land.lhs.true63.i ]
  %cmp78.i = icmp ult i64 %i.4.i, %n
  br i1 %cmp78.i, label %land.lhs.true80.i, label %if.end138.i

land.lhs.true80.i:                                ; preds = %if.end77.i
  %arrayidx81.i = getelementptr inbounds i8, ptr %p, i64 %i.4.i
  %48 = load i8, ptr %arrayidx81.i
  br label %NodeBlock13

NodeBlock13:                                      ; preds = %land.lhs.true80.i
  %Pivot14 = icmp slt i8 %48, 101
  br i1 %Pivot14, label %LeafBlock9, label %LeafBlock11

LeafBlock11:                                      ; preds = %NodeBlock13
  %SwitchLeaf12 = icmp eq i8 %48, 101
  br i1 %SwitchLeaf12, label %if.then90.i, label %if.end138.i

LeafBlock9:                                       ; preds = %NodeBlock13
  %SwitchLeaf10 = icmp eq i8 %48, 69
  br i1 %SwitchLeaf10, label %if.then90.i, label %if.end138.i

if.then90.i:                                      ; preds = %LeafBlock11, %LeafBlock9
  %inc91.i = add i64 %i.4.i, 1
  %cmp92.i = icmp ult i64 %inc91.i, %n
  br i1 %cmp92.i, label %land.lhs.true94.i, label %if.end106.i

land.lhs.true94.i:                                ; preds = %if.then90.i
  %arrayidx95.i = getelementptr inbounds i8, ptr %p, i64 %inc91.i
  %49 = load i8, ptr %arrayidx95.i
  br label %NodeBlock19

NodeBlock19:                                      ; preds = %land.lhs.true94.i
  %Pivot20 = icmp slt i8 %49, 45
  br i1 %Pivot20, label %LeafBlock15, label %LeafBlock17

LeafBlock17:                                      ; preds = %NodeBlock19
  %SwitchLeaf18 = icmp eq i8 %49, 45
  br i1 %SwitchLeaf18, label %if.then104.i, label %if.end106.i

LeafBlock15:                                      ; preds = %NodeBlock19
  %SwitchLeaf16 = icmp eq i8 %49, 43
  br i1 %SwitchLeaf16, label %if.then104.i, label %if.end106.i

if.then104.i:                                     ; preds = %LeafBlock17, %LeafBlock15
  %inc105.i = add i64 %i.4.i, 2
  br label %if.end106.i

if.end106.i:                                      ; preds = %LeafBlock17, %LeafBlock15, %if.then104.i, %if.then90.i
  %i.5.i = phi i64 [ %inc105.i, %if.then104.i ], [ %inc91.i, %if.then90.i ], [ %inc91.i, %LeafBlock15 ], [ %inc91.i, %LeafBlock17 ]
  %cmp107.not.i = icmp ult i64 %i.5.i, %n
  br i1 %cmp107.not.i, label %lor.lhs.false109.i, label %if.then119.i

lor.lhs.false109.i:                               ; preds = %if.end106.i
  %arrayidx110.i = getelementptr inbounds i8, ptr %p, i64 %i.5.i
  %50 = load i8, ptr %arrayidx110.i
  %51 = add i8 %50, -58
  %or.cond225.i = icmp ult i8 %51, -10
  br i1 %or.cond225.i, label %if.then119.i, label %land.lhs.true124.i

if.then119.i:                                     ; preds = %lor.lhs.false109.i, %if.end106.i
  store i64 %i.5.i, ptr %err
  br label %cleanup300

land.lhs.true124.i:                               ; preds = %while.body135.i, %lor.lhs.false109.i
  %i.6269.i = phi i64 [ %inc136.i, %while.body135.i ], [ %i.5.i, %lor.lhs.false109.i ]
  %arrayidx125.i = getelementptr inbounds i8, ptr %p, i64 %i.6269.i
  %52 = load i8, ptr %arrayidx125.i
  %53 = add i8 %52, -48
  %or.cond226.i = icmp ult i8 %53, 10
  br i1 %or.cond226.i, label %while.body135.i, label %if.end138.i

while.body135.i:                                  ; preds = %land.lhs.true124.i
  %inc136.i = add i64 %i.6269.i, 1
  %exitcond307.not.i = icmp eq i64 %inc136.i, %n
  br i1 %exitcond307.not.i, label %if.then143.i, label %land.lhs.true124.i

if.end138.i:                                      ; preds = %LeafBlock11, %LeafBlock9, %land.lhs.true124.i, %if.end77.i
  %i.7.i = phi i64 [ %i.4.i, %if.end77.i ], [ %i.6269.i, %land.lhs.true124.i ], [ %i.4.i, %LeafBlock9 ], [ %i.4.i, %LeafBlock11 ]
  %cmp139.not.i = icmp eq i64 %i.7.i, %n
  br i1 %cmp139.not.i, label %if.then143.i, label %if.then141.i

if.then141.i:                                     ; preds = %if.end138.i
  store i64 %i.7.i, ptr %err
  br label %cleanup300

if.then143.i:                                     ; preds = %if.end138.i, %while.body135.i, %while.body74.i, %while.body.i
  call void @llvm.lifetime.start.p0(i64 768, ptr %dig.i.i)
  br label %for.body.outer.i.outer.i

for.body.outer.i.outer.i:                         ; preds = %for.inc.i.i, %if.then143.i
  %i.1725.ph.i.ph.i = phi i64 [ %i.0.i, %if.then143.i ], [ %inc57.i.i, %for.inc.i.i ]
  %R.0724.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %R.4.ph.i.i, %for.inc.i.i ]
  %T.0723.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %T.2.ph.i.i, %for.inc.i.i ]
  %F.0722.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %F.3.ph.i.i, %for.inc.i.i ]
  %lead.0721.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %lead.0721.i287.i, %for.inc.i.i ]
  %top.0720.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %top.4.ph.i.i, %for.inc.i.i ]
  %topn.0719.ph.i.ph.i = phi i64 [ 0, %if.then143.i ], [ %topn.4.ph.i.i, %for.inc.i.i ]
  %in_frac.0718.ph.i.ph.i = phi i32 [ 0, %if.then143.i ], [ %in_frac.2.ph.i.i, %for.inc.i.i ]
  %seen.0717.ph.i.ph.i = phi i32 [ 0, %if.then143.i ], [ %seen.4.ph.i.i, %for.inc.i.i ]
  %sticky.0716.ph.i.ph.i = phi i32 [ 0, %if.then143.i ], [ %sticky.4.ph.i.i, %for.inc.i.i ]
  br label %for.body.outer.i.i

for.body.outer.i.i:                               ; preds = %if.else46.i.thread.i, %for.body.outer.i.outer.i
  %i.1725.ph.i.i = phi i64 [ %i.1725.ph.i.ph.i, %for.body.outer.i.outer.i ], [ %inc57.i344.i, %if.else46.i.thread.i ]
  %T.0723.ph.i.i = phi i64 [ %T.0723.ph.i.ph.i, %for.body.outer.i.outer.i ], [ %T.0723.i.i, %if.else46.i.thread.i ]
  %F.0722.ph.i.i = phi i64 [ %F.0722.ph.i.ph.i, %for.body.outer.i.outer.i ], [ %F.0722.i.i, %if.else46.i.thread.i ]
  %lead.0721.ph.i.i = phi i64 [ %lead.0721.ph.i.ph.i, %for.body.outer.i.outer.i ], [ %lead.0721.i.i, %if.else46.i.thread.i ]
  %in_frac.0718.ph.i.i = phi i32 [ %in_frac.0718.ph.i.ph.i, %for.body.outer.i.outer.i ], [ 1, %if.else46.i.thread.i ]
  %seen.0717.ph.i.i = phi i32 [ %seen.0717.ph.i.ph.i, %for.body.outer.i.outer.i ], [ 0, %if.else46.i.thread.i ]
  %tobool.not.i.i = icmp ne i32 %in_frac.0718.ph.i.i, 0
  %inc18.i.i = zext i1 %tobool.not.i.i to i64
  %arrayidx5.i.peel.i = getelementptr inbounds i8, ptr %p, i64 %i.1725.ph.i.i
  %54 = load i8, ptr %arrayidx5.i.peel.i
  %55 = add i8 %54, -48
  %or.cond.i.peel.i = icmp ult i8 %55, 10
  br i1 %or.cond.i.peel.i, label %if.then13.i.peel.i, label %if.else46.i.i

if.then13.i.peel.i:                               ; preds = %for.body.outer.i.i
  %inc16.i.peel.i = add i64 %T.0723.ph.i.i, 1
  %spec.select.i.peel.i = add i64 %F.0722.ph.i.i, %inc18.i.i
  %tobool20.not.i.peel.i = icmp eq i32 %seen.0717.ph.i.i, 0
  %cmp23.i.peel.i = icmp eq i8 %55, 0
  %or.cond510.i.peel.i = and i1 %tobool20.not.i.peel.i, %cmp23.i.peel.i
  br i1 %or.cond510.i.peel.i, label %for.inc.thread.i.peel.i, label %if.end28.i.i.loopexit609

for.inc.thread.i.peel.i:                          ; preds = %if.then13.i.peel.i
  %inc57798.i.peel.i = add i64 %i.1725.ph.i.i, 1
  %exitcond.not799.i.peel.i = icmp eq i64 %inc57798.i.peel.i, %n
  br i1 %exitcond.not799.i.peel.i, label %if.then59.i.i, label %for.body.i.i

for.body.i.i:                                     ; preds = %for.inc.thread.i.i, %for.inc.thread.i.peel.i
  %i.1725.i.i = phi i64 [ %inc57798.i.i, %for.inc.thread.i.i ], [ %inc57798.i.peel.i, %for.inc.thread.i.peel.i ]
  %T.0723.i.i = phi i64 [ %inc16.i.i, %for.inc.thread.i.i ], [ %inc16.i.peel.i, %for.inc.thread.i.peel.i ]
  %F.0722.i.i = phi i64 [ %spec.select.i.i, %for.inc.thread.i.i ], [ %spec.select.i.peel.i, %for.inc.thread.i.peel.i ]
  %lead.0721.i.in.i = phi i64 [ %lead.0721.i.i, %for.inc.thread.i.i ], [ %lead.0721.ph.i.i, %for.inc.thread.i.peel.i ]
  %lead.0721.i.i = add i64 %lead.0721.i.in.i, 1
  %arrayidx5.i.i = getelementptr inbounds i8, ptr %p, i64 %i.1725.i.i
  %56 = load i8, ptr %arrayidx5.i.i
  %57 = add i8 %56, -48
  %or.cond.i.i = icmp ult i8 %57, 10
  br i1 %or.cond.i.i, label %if.then13.i.i, label %if.else46.i.thread.i

if.then13.i.i:                                    ; preds = %for.body.i.i
  %inc16.i.i = add i64 %T.0723.i.i, 1
  %spec.select.i.i = add i64 %F.0722.i.i, %inc18.i.i
  %cmp23.i.i = icmp eq i8 %57, 0
  br i1 %cmp23.i.i, label %for.inc.thread.i.i, label %if.end28.i.i

if.end28.i.i.loopexit609:                         ; preds = %if.then13.i.peel.i
  %58 = select i1 %cmp23.i.peel.i, i32 %sticky.0716.ph.i.ph.i, i32 1
  br label %if.end28.i.i

if.end28.i.i:                                     ; preds = %if.end28.i.i.loopexit609, %if.then13.i.i
  %inc16.i.lcssa.i = phi i64 [ %inc16.i.peel.i, %if.end28.i.i.loopexit609 ], [ %inc16.i.i, %if.then13.i.i ]
  %spec.select.i.lcssa.i = phi i64 [ %spec.select.i.peel.i, %if.end28.i.i.loopexit609 ], [ %spec.select.i.i, %if.then13.i.i ]
  %cmp23.i.lcssa.i = phi i32 [ %58, %if.end28.i.i.loopexit609 ], [ 1, %if.then13.i.i ]
  %i.1725.i.lcssa292.i = phi i64 [ %i.1725.ph.i.i, %if.end28.i.i.loopexit609 ], [ %i.1725.i.i, %if.then13.i.i ]
  %lead.0721.i.lcssa284.i = phi i64 [ %lead.0721.ph.i.i, %if.end28.i.i.loopexit609 ], [ %lead.0721.i.i, %if.then13.i.i ]
  %.lcssa277.i = phi i8 [ %55, %if.end28.i.i.loopexit609 ], [ %57, %if.then13.i.i ]
  %cmp29.i.i = icmp ult i64 %R.0724.ph.i.ph.i, 768
  br i1 %cmp29.i.i, label %if.then31.i.i, label %for.inc.i.i

if.then31.i.i:                                    ; preds = %if.end28.i.i
  %inc32.i.i = add i64 %R.0724.ph.i.ph.i, 1
  %arrayidx33.i.i = getelementptr inbounds [768 x i8], ptr %dig.i.i, i64 0, i64 %R.0724.ph.i.ph.i
  store i8 %.lcssa277.i, ptr %arrayidx33.i.i
  %cmp34.i.i = icmp ult i64 %topn.0719.ph.i.ph.i, 19
  br i1 %cmp34.i.i, label %if.then36.i.i, label %for.inc.i.i

if.then36.i.i:                                    ; preds = %if.then31.i.i
  %mul.i.i = mul i64 %top.0720.ph.i.ph.i, 10
  %conv37.i.i = zext i8 %.lcssa277.i to i64
  %add.i.i = add i64 %mul.i.i, %conv37.i.i
  %inc38.i.i = add i64 %topn.0719.ph.i.ph.i, 1
  br label %for.inc.i.i

if.else46.i.i:                                    ; preds = %for.body.outer.i.i
  %cmp48.i.i = icmp eq i8 %54, 46
  br i1 %cmp48.i.i, label %for.inc.i.i, label %for.end.i.i

if.else46.i.thread.i:                             ; preds = %for.body.i.i
  %cmp48.i322.i = icmp ne i8 %56, 46
  %inc57.i344.i = add i64 %i.1725.i.i, 1
  %exitcond.not.i345.i = icmp eq i64 %inc57.i344.i, %n
  %or.cond447.i = or i1 %exitcond.not.i345.i, %cmp48.i322.i
  br i1 %or.cond447.i, label %if.then59.i.i, label %for.body.outer.i.i

for.inc.i.i:                                      ; preds = %if.else46.i.i, %if.then36.i.i, %if.then31.i.i, %if.end28.i.i
  %i.1725.i294.i = phi i64 [ %i.1725.i.lcssa292.i, %if.then31.i.i ], [ %i.1725.i.lcssa292.i, %if.then36.i.i ], [ %i.1725.ph.i.i, %if.else46.i.i ], [ %i.1725.i.lcssa292.i, %if.end28.i.i ]
  %lead.0721.i287.i = phi i64 [ %lead.0721.i.lcssa284.i, %if.then31.i.i ], [ %lead.0721.i.lcssa284.i, %if.then36.i.i ], [ %lead.0721.ph.i.i, %if.else46.i.i ], [ %lead.0721.i.lcssa284.i, %if.end28.i.i ]
  %sticky.4.ph.i.i = phi i32 [ %sticky.0716.ph.i.ph.i, %if.then31.i.i ], [ %sticky.0716.ph.i.ph.i, %if.then36.i.i ], [ %sticky.0716.ph.i.ph.i, %if.else46.i.i ], [ %cmp23.i.lcssa.i, %if.end28.i.i ]
  %seen.4.ph.i.i = phi i32 [ 1, %if.then31.i.i ], [ 1, %if.then36.i.i ], [ %seen.0717.ph.i.i, %if.else46.i.i ], [ 1, %if.end28.i.i ]
  %in_frac.2.ph.i.i = phi i32 [ %in_frac.0718.ph.i.i, %if.then31.i.i ], [ %in_frac.0718.ph.i.i, %if.then36.i.i ], [ 1, %if.else46.i.i ], [ %in_frac.0718.ph.i.i, %if.end28.i.i ]
  %topn.4.ph.i.i = phi i64 [ %topn.0719.ph.i.ph.i, %if.then31.i.i ], [ %inc38.i.i, %if.then36.i.i ], [ %topn.0719.ph.i.ph.i, %if.else46.i.i ], [ %topn.0719.ph.i.ph.i, %if.end28.i.i ]
  %top.4.ph.i.i = phi i64 [ %top.0720.ph.i.ph.i, %if.then31.i.i ], [ %add.i.i, %if.then36.i.i ], [ %top.0720.ph.i.ph.i, %if.else46.i.i ], [ %top.0720.ph.i.ph.i, %if.end28.i.i ]
  %F.3.ph.i.i = phi i64 [ %spec.select.i.lcssa.i, %if.then31.i.i ], [ %spec.select.i.lcssa.i, %if.then36.i.i ], [ %F.0722.ph.i.i, %if.else46.i.i ], [ %spec.select.i.lcssa.i, %if.end28.i.i ]
  %T.2.ph.i.i = phi i64 [ %inc16.i.lcssa.i, %if.then31.i.i ], [ %inc16.i.lcssa.i, %if.then36.i.i ], [ %T.0723.ph.i.i, %if.else46.i.i ], [ %inc16.i.lcssa.i, %if.end28.i.i ]
  %R.4.ph.i.i = phi i64 [ %inc32.i.i, %if.then31.i.i ], [ %inc32.i.i, %if.then36.i.i ], [ %R.0724.ph.i.ph.i, %if.else46.i.i ], [ %R.0724.ph.i.ph.i, %if.end28.i.i ]
  %inc57.i.i = add i64 %i.1725.i294.i, 1
  %exitcond.not.i.i = icmp eq i64 %inc57.i.i, %n
  br i1 %exitcond.not.i.i, label %for.end.thread.i.i, label %for.body.outer.i.outer.i

for.inc.thread.i.i:                               ; preds = %if.then13.i.i
  %inc57798.i.i = add i64 %i.1725.i.i, 1
  %exitcond.not799.i.i = icmp eq i64 %inc57798.i.i, %n
  br i1 %exitcond.not799.i.i, label %if.then59.i.i, label %for.body.i.i

for.end.i.i:                                      ; preds = %if.else46.i.i
  %tobool58.not.i.i = icmp eq i32 %seen.0717.ph.i.i, 0
  br i1 %tobool58.not.i.i, label %if.then59.i.i, label %if.then64.i.i

for.end.thread.i.i:                               ; preds = %for.inc.i.i
  %59 = icmp eq i32 %seen.4.ph.i.i, 0
  br i1 %59, label %if.then59.i.i, label %if.end104.i.i

if.then59.i.i:                                    ; preds = %for.end.thread.i.i, %for.end.i.i, %for.inc.thread.i.i, %if.else46.i.thread.i, %for.inc.thread.i.peel.i
  %cond.i.i = select i1 %cmp1.i, double -0.000000e+00, double 0.000000e+00
  br label %if.end291

if.then64.i.i:                                    ; preds = %for.end.i.i
  %inc65.i.i = add i64 %i.1725.ph.i.i, 1
  %cmp66.i.i = icmp ult i64 %inc65.i.i, %n
  br i1 %cmp66.i.i, label %land.lhs.true68.i.i, label %if.end83.i.i

land.lhs.true68.i.i:                              ; preds = %if.then64.i.i
  %arrayidx69.i.i = getelementptr inbounds i8, ptr %p, i64 %inc65.i.i
  %60 = load i8, ptr %arrayidx69.i.i
  br label %NodeBlock25

NodeBlock25:                                      ; preds = %land.lhs.true68.i.i
  %Pivot26 = icmp slt i8 %60, 45
  br i1 %Pivot26, label %LeafBlock21, label %LeafBlock23

LeafBlock23:                                      ; preds = %NodeBlock25
  %SwitchLeaf24 = icmp eq i8 %60, 45
  br i1 %SwitchLeaf24, label %if.then77.i.i, label %if.end83.i.i

LeafBlock21:                                      ; preds = %NodeBlock25
  %SwitchLeaf22 = icmp eq i8 %60, 43
  br i1 %SwitchLeaf22, label %if.then77.i.i, label %if.end83.i.i

if.then77.i.i:                                    ; preds = %LeafBlock23, %LeafBlock21
  %cmp80.i.i = icmp ne i8 %60, 45
  %inc82.i.i = add i64 %i.1725.ph.i.i, 2
  br label %if.end83.i.i

if.end83.i.i:                                     ; preds = %LeafBlock23, %LeafBlock21, %if.then77.i.i, %if.then64.i.i
  %esign.0.i.i = phi i1 [ %cmp80.i.i, %if.then77.i.i ], [ true, %if.then64.i.i ], [ true, %LeafBlock21 ], [ true, %LeafBlock23 ]
  %i.2.i.i = phi i64 [ %inc82.i.i, %if.then77.i.i ], [ %inc65.i.i, %if.then64.i.i ], [ %inc65.i.i, %LeafBlock21 ], [ %inc65.i.i, %LeafBlock23 ]
  %cmp85733.i.i = icmp ult i64 %i.2.i.i, %n
  br i1 %cmp85733.i.i, label %for.body87.i.i.preheader, label %for.end100.i.i

for.body87.i.i.preheader:                         ; preds = %if.end83.i.i
  %61 = sub i64 %n, %i.2.i.i
  %xtraiter = and i64 %61, 3
  %62 = sub i64 %i.2.i.i, %n
  %63 = icmp ugt i64 %62, -4
  br i1 %63, label %for.end100.i.i.loopexit.unr-lcssa, label %for.body87.i.i.preheader.new

for.body87.i.i.preheader.new:                     ; preds = %for.body87.i.i.preheader
  %unroll_iter = and i64 %61, -4
  %invariant.gep = getelementptr i8, ptr %p, i64 1
  %invariant.gep1191 = getelementptr i8, ptr %p, i64 2
  %invariant.gep1193 = getelementptr i8, ptr %p, i64 3
  br label %for.body87.i.i

for.body87.i.i:                                   ; preds = %for.inc98.i.i.3, %for.body87.i.i.preheader.new
  %i.3735.i.i = phi i64 [ %i.2.i.i, %for.body87.i.i.preheader.new ], [ %inc99.i.i.3, %for.inc98.i.i.3 ]
  %e.0734.i.i = phi i64 [ 0, %for.body87.i.i.preheader.new ], [ %e.1.i.i.3, %for.inc98.i.i.3 ]
  %niter = phi i64 [ 0, %for.body87.i.i.preheader.new ], [ %niter.next.3, %for.inc98.i.i.3 ]
  %cmp88.i.i = icmp slt i64 %e.0734.i.i, 1000000
  br i1 %cmp88.i.i, label %if.then90.i.i, label %for.inc98.i.i

if.then90.i.i:                                    ; preds = %for.body87.i.i
  %mul91.i.i = mul i64 %e.0734.i.i, 10
  %arrayidx92.i.i = getelementptr inbounds i8, ptr %p, i64 %i.3735.i.i
  %64 = load i8, ptr %arrayidx92.i.i
  %conv93.i.i = zext i8 %64 to i64
  %sub94.i.i = add i64 %mul91.i.i, -48
  %add96.i.i = add i64 %sub94.i.i, %conv93.i.i
  br label %for.inc98.i.i

for.inc98.i.i:                                    ; preds = %if.then90.i.i, %for.body87.i.i
  %e.1.i.i = phi i64 [ %add96.i.i, %if.then90.i.i ], [ %e.0734.i.i, %for.body87.i.i ]
  %cmp88.i.i.1 = icmp slt i64 %e.1.i.i, 1000000
  br i1 %cmp88.i.i.1, label %if.then90.i.i.1, label %for.inc98.i.i.1

if.then90.i.i.1:                                  ; preds = %for.inc98.i.i
  %mul91.i.i.1 = mul i64 %e.1.i.i, 10
  %gep = getelementptr i8, ptr %invariant.gep, i64 %i.3735.i.i
  %65 = load i8, ptr %gep
  %conv93.i.i.1 = zext i8 %65 to i64
  %sub94.i.i.1 = add i64 %mul91.i.i.1, -48
  %add96.i.i.1 = add i64 %sub94.i.i.1, %conv93.i.i.1
  br label %for.inc98.i.i.1

for.inc98.i.i.1:                                  ; preds = %if.then90.i.i.1, %for.inc98.i.i
  %e.1.i.i.1 = phi i64 [ %add96.i.i.1, %if.then90.i.i.1 ], [ %e.1.i.i, %for.inc98.i.i ]
  %cmp88.i.i.2 = icmp slt i64 %e.1.i.i.1, 1000000
  br i1 %cmp88.i.i.2, label %if.then90.i.i.2, label %for.inc98.i.i.2

if.then90.i.i.2:                                  ; preds = %for.inc98.i.i.1
  %mul91.i.i.2 = mul i64 %e.1.i.i.1, 10
  %gep1192 = getelementptr i8, ptr %invariant.gep1191, i64 %i.3735.i.i
  %66 = load i8, ptr %gep1192
  %conv93.i.i.2 = zext i8 %66 to i64
  %sub94.i.i.2 = add i64 %mul91.i.i.2, -48
  %add96.i.i.2 = add i64 %sub94.i.i.2, %conv93.i.i.2
  br label %for.inc98.i.i.2

for.inc98.i.i.2:                                  ; preds = %if.then90.i.i.2, %for.inc98.i.i.1
  %e.1.i.i.2 = phi i64 [ %add96.i.i.2, %if.then90.i.i.2 ], [ %e.1.i.i.1, %for.inc98.i.i.1 ]
  %cmp88.i.i.3 = icmp slt i64 %e.1.i.i.2, 1000000
  br i1 %cmp88.i.i.3, label %if.then90.i.i.3, label %for.inc98.i.i.3

if.then90.i.i.3:                                  ; preds = %for.inc98.i.i.2
  %mul91.i.i.3 = mul i64 %e.1.i.i.2, 10
  %gep1194 = getelementptr i8, ptr %invariant.gep1193, i64 %i.3735.i.i
  %67 = load i8, ptr %gep1194
  %conv93.i.i.3 = zext i8 %67 to i64
  %sub94.i.i.3 = add i64 %mul91.i.i.3, -48
  %add96.i.i.3 = add i64 %sub94.i.i.3, %conv93.i.i.3
  br label %for.inc98.i.i.3

for.inc98.i.i.3:                                  ; preds = %if.then90.i.i.3, %for.inc98.i.i.2
  %e.1.i.i.3 = phi i64 [ %add96.i.i.3, %if.then90.i.i.3 ], [ %e.1.i.i.2, %for.inc98.i.i.2 ]
  %inc99.i.i.3 = add i64 %i.3735.i.i, 4
  %niter.next.3 = add i64 %niter, 4
  %niter.ncmp.3 = icmp eq i64 %niter.next.3, %unroll_iter
  br i1 %niter.ncmp.3, label %for.end100.i.i.loopexit.unr-lcssa, label %for.body87.i.i

for.end100.i.i.loopexit.unr-lcssa:                ; preds = %for.inc98.i.i.3, %for.body87.i.i.preheader
  %e.1.i.i.lcssa.ph = phi i64 [ poison, %for.body87.i.i.preheader ], [ %e.1.i.i.3, %for.inc98.i.i.3 ]
  %i.3735.i.i.unr = phi i64 [ %i.2.i.i, %for.body87.i.i.preheader ], [ %inc99.i.i.3, %for.inc98.i.i.3 ]
  %e.0734.i.i.unr = phi i64 [ 0, %for.body87.i.i.preheader ], [ %e.1.i.i.3, %for.inc98.i.i.3 ]
  %lcmp.mod.not = icmp eq i64 %xtraiter, 0
  br i1 %lcmp.mod.not, label %for.end100.i.i, label %for.body87.i.i.epil

for.body87.i.i.epil:                              ; preds = %for.inc98.i.i.epil, %for.end100.i.i.loopexit.unr-lcssa
  %i.3735.i.i.epil = phi i64 [ %inc99.i.i.epil, %for.inc98.i.i.epil ], [ %i.3735.i.i.unr, %for.end100.i.i.loopexit.unr-lcssa ]
  %e.0734.i.i.epil = phi i64 [ %e.1.i.i.epil, %for.inc98.i.i.epil ], [ %e.0734.i.i.unr, %for.end100.i.i.loopexit.unr-lcssa ]
  %epil.iter = phi i64 [ %epil.iter.next, %for.inc98.i.i.epil ], [ 0, %for.end100.i.i.loopexit.unr-lcssa ]
  %cmp88.i.i.epil = icmp slt i64 %e.0734.i.i.epil, 1000000
  br i1 %cmp88.i.i.epil, label %if.then90.i.i.epil, label %for.inc98.i.i.epil

if.then90.i.i.epil:                               ; preds = %for.body87.i.i.epil
  %mul91.i.i.epil = mul i64 %e.0734.i.i.epil, 10
  %arrayidx92.i.i.epil = getelementptr inbounds i8, ptr %p, i64 %i.3735.i.i.epil
  %68 = load i8, ptr %arrayidx92.i.i.epil
  %conv93.i.i.epil = zext i8 %68 to i64
  %sub94.i.i.epil = add i64 %mul91.i.i.epil, -48
  %add96.i.i.epil = add i64 %sub94.i.i.epil, %conv93.i.i.epil
  br label %for.inc98.i.i.epil

for.inc98.i.i.epil:                               ; preds = %if.then90.i.i.epil, %for.body87.i.i.epil
  %e.1.i.i.epil = phi i64 [ %add96.i.i.epil, %if.then90.i.i.epil ], [ %e.0734.i.i.epil, %for.body87.i.i.epil ]
  %inc99.i.i.epil = add i64 %i.3735.i.i.epil, 1
  %epil.iter.next = add i64 %epil.iter, 1
  %epil.iter.cmp.not = icmp eq i64 %epil.iter.next, %xtraiter
  br i1 %epil.iter.cmp.not, label %for.end100.i.i, label %for.body87.i.i.epil

for.end100.i.i:                                   ; preds = %for.inc98.i.i.epil, %for.end100.i.i.loopexit.unr-lcssa, %if.end83.i.i
  %e.0.lcssa.i.i = phi i64 [ 0, %if.end83.i.i ], [ %e.1.i.i.lcssa.ph, %for.end100.i.i.loopexit.unr-lcssa ], [ %e.1.i.i.epil, %for.inc98.i.i.epil ]
  %sub102.i.i = sub i64 0, %e.0.lcssa.i.i
  %cond103.i.i = select i1 %esign.0.i.i, i64 %e.0.lcssa.i.i, i64 %sub102.i.i
  br label %if.end104.i.i

if.end104.i.i:                                    ; preds = %for.end100.i.i, %for.end.thread.i.i
  %lead.0721.i286.i = phi i64 [ %lead.0721.ph.i.i, %for.end100.i.i ], [ %lead.0721.i287.i, %for.end.thread.i.i ]
  %sticky.0714.i.i = phi i32 [ %sticky.0716.ph.i.ph.i, %for.end100.i.i ], [ %sticky.4.ph.i.i, %for.end.thread.i.i ]
  %topn.0711.i.i = phi i64 [ %topn.0719.ph.i.ph.i, %for.end100.i.i ], [ %topn.4.ph.i.i, %for.end.thread.i.i ]
  %top.0709.i.i = phi i64 [ %top.0720.ph.i.ph.i, %for.end100.i.i ], [ %top.4.ph.i.i, %for.end.thread.i.i ]
  %F.0705.i.i = phi i64 [ %F.0722.ph.i.i, %for.end100.i.i ], [ %F.3.ph.i.i, %for.end.thread.i.i ]
  %T.0703.i.i = phi i64 [ %T.0723.ph.i.i, %for.end100.i.i ], [ %T.2.ph.i.i, %for.end.thread.i.i ]
  %R.0701.i.i = phi i64 [ %R.0724.ph.i.ph.i, %for.end100.i.i ], [ %R.4.ph.i.i, %for.end.thread.i.i ]
  %exp10.0.i.i = phi i64 [ %cond103.i.i, %for.end100.i.i ], [ 0, %for.end.thread.i.i ]
  %sub105.i.i = sub i64 %exp10.0.i.i, %F.0705.i.i
  %69 = add i64 %lead.0721.i286.i, %R.0701.i.i
  %sub107.i.i = sub i64 %T.0703.i.i, %69
  %add108.i.i = add i64 %sub107.i.i, %sub105.i.i
  %sub109.i.i = add i64 %R.0701.i.i, -1
  %add110.i.i = add i64 %sub109.i.i, %add108.i.i
  %cmp111.i.i = icmp sgt i64 %add110.i.i, 308
  br i1 %cmp111.i.i, label %if.then113.i.i, label %if.end120.i.i

if.then113.i.i:                                   ; preds = %if.end104.i.i
  %spec.select694.i.i = select i1 %cmp1.i, double 0xFFF0000000000000, double 0x7FF0000000000000
  br label %if.end291

if.end120.i.i:                                    ; preds = %if.end104.i.i
  %cmp121.i.i = icmp slt i64 %add110.i.i, -324
  br i1 %cmp121.i.i, label %if.then123.i.i, label %if.end126.i.i

if.then123.i.i:                                   ; preds = %if.end120.i.i
  %cond125.i.i = select i1 %cmp1.i, double -0.000000e+00, double 0.000000e+00
  br label %if.end291

if.end126.i.i:                                    ; preds = %if.end120.i.i
  call void @llvm.lifetime.start.p0(i64 1568, ptr %v.i.i)
  %sticky127.i.i = getelementptr inbounds i8, ptr %v.i.i, i64 1560
  store i32 %sticky.0714.i.i, ptr %sticky127.i.i
  %S128.i.i = getelementptr inbounds i8, ptr %v.i.i, i64 1552
  store i64 %add108.i.i, ptr %S128.i.i
  %n.i.i.i = getelementptr inbounds i8, ptr %v.i.i, i64 768
  %cmp130737.not.i.i = icmp eq i64 %R.0701.i.i, 0
  br i1 %cmp130737.not.i.i, label %if.end151.i.i.sink.split, label %for.body132.i.i

for.cond.cleanup.i.i:                             ; preds = %for.inc143.i.i
  store i32 %78, ptr %n.i.i.i
  %tobool147.not.i.i = icmp eq i32 %cn.1.i.i, 0
  br i1 %tobool147.not.i.i, label %if.end151.i.i, label %if.then148.i.i

for.body132.i.i:                                  ; preds = %for.inc143.i.i, %if.end126.i.i
  %j.0740.i.i = phi i64 [ %inc144.i.i, %for.inc143.i.i ], [ 0, %if.end126.i.i ]
  %cn.0739.i.i = phi i32 [ %cn.1.i.i, %for.inc143.i.i ], [ 0, %if.end126.i.i ]
  %chunk.0738.i.i = phi i64 [ %chunk.1.i.i, %for.inc143.i.i ], [ 0, %if.end126.i.i ]
  %70 = phi i32 [ %78, %for.inc143.i.i ], [ 0, %if.end126.i.i ]
  %mul133.i.i = mul i64 %chunk.0738.i.i, 10
  %arrayidx134.i.i = getelementptr inbounds [768 x i8], ptr %dig.i.i, i64 0, i64 %j.0740.i.i
  %71 = load i8, ptr %arrayidx134.i.i
  %conv135.i.i = zext i8 %71 to i64
  %add136.i.i = add i64 %mul133.i.i, %conv135.i.i
  %inc137.i.i = add i32 %cn.0739.i.i, 1
  %cmp138.i.i = icmp eq i32 %inc137.i.i, 19
  br i1 %cmp138.i.i, label %if.then140.i.i, label %for.inc143.i.i

if.then140.i.i:                                   ; preds = %for.body132.i.i
  %conv.i.i.i = zext i64 %add136.i.i to i128
  %cmp28.i.i.i = icmp sgt i32 %70, 0
  br i1 %cmp28.i.i.i, label %for.body.lr.ph.i.i.i, label %while.cond.preheader.i.i.i

for.body.lr.ph.i.i.i:                             ; preds = %if.then140.i.i
  %wide.trip.count.i.i.i = zext i32 %70 to i64
  %xtraiter1043 = and i64 %wide.trip.count.i.i.i, 3
  %72 = icmp ult i32 %70, 4
  br i1 %72, label %while.cond.preheader.i.i.i.loopexit.unr-lcssa, label %for.body.lr.ph.i.i.i.new

for.body.lr.ph.i.i.i.new:                         ; preds = %for.body.lr.ph.i.i.i
  %unroll_iter1047 = and i64 %wide.trip.count.i.i.i, 2147483644
  br label %for.body.i.i.i

while.cond.preheader.i.i.i.loopexit.unr-lcssa:    ; preds = %for.body.i.i.i, %for.body.lr.ph.i.i.i
  %shr.i.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i.i ], [ %shr.i.i.i.3, %for.body.i.i.i ]
  %indvars.iv.i.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i.i ], [ %indvars.iv.next.i.i.i.3, %for.body.i.i.i ]
  %carry.029.i.i.i.unr = phi i128 [ %conv.i.i.i, %for.body.lr.ph.i.i.i ], [ %shr.i.i.i.3, %for.body.i.i.i ]
  %lcmp.mod1045.not = icmp eq i64 %xtraiter1043, 0
  br i1 %lcmp.mod1045.not, label %while.cond.preheader.i.i.i, label %for.body.i.i.i.epil

for.body.i.i.i.epil:                              ; preds = %for.body.i.i.i.epil, %while.cond.preheader.i.i.i.loopexit.unr-lcssa
  %indvars.iv.i.i.i.epil = phi i64 [ %indvars.iv.next.i.i.i.epil, %for.body.i.i.i.epil ], [ %indvars.iv.i.i.i.unr, %while.cond.preheader.i.i.i.loopexit.unr-lcssa ]
  %carry.029.i.i.i.epil = phi i128 [ %shr.i.i.i.epil, %for.body.i.i.i.epil ], [ %carry.029.i.i.i.unr, %while.cond.preheader.i.i.i.loopexit.unr-lcssa ]
  %epil.iter1044 = phi i64 [ %epil.iter1044.next, %for.body.i.i.i.epil ], [ 0, %while.cond.preheader.i.i.i.loopexit.unr-lcssa ]
  %arrayidx.i.i.i.epil = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i.i.epil
  %73 = load i64, ptr %arrayidx.i.i.i.epil
  %conv2.i.i.i.epil = zext i64 %73 to i128
  %mul.i.i.i.epil = mul i128 %conv2.i.i.i.epil, 10000000000000000000
  %add4.i.i.i.epil = add i128 %mul.i.i.i.epil, %carry.029.i.i.i.epil
  %conv5.i.i.i.epil = trunc i128 %add4.i.i.i.epil to i64
  store i64 %conv5.i.i.i.epil, ptr %arrayidx.i.i.i.epil
  %shr.i.i.i.epil = lshr i128 %add4.i.i.i.epil, 64
  %indvars.iv.next.i.i.i.epil = add i64 %indvars.iv.i.i.i.epil, 1
  %epil.iter1044.next = add i64 %epil.iter1044, 1
  %epil.iter1044.cmp.not = icmp eq i64 %epil.iter1044.next, %xtraiter1043
  br i1 %epil.iter1044.cmp.not, label %while.cond.preheader.i.i.i, label %for.body.i.i.i.epil

while.cond.preheader.i.i.i:                       ; preds = %for.body.i.i.i.epil, %while.cond.preheader.i.i.i.loopexit.unr-lcssa, %if.then140.i.i
  %carry.0.lcssa.i.i.i = phi i128 [ %conv.i.i.i, %if.then140.i.i ], [ %shr.i.i.i.lcssa.ph, %while.cond.preheader.i.i.i.loopexit.unr-lcssa ], [ %shr.i.i.i.epil, %for.body.i.i.i.epil ]
  %tobool.not31.i.i.i = icmp eq i128 %carry.0.lcssa.i.i.i, 0
  br i1 %tobool.not31.i.i.i, label %for.inc143.i.i, label %while.body.us.i.i.i

while.body.us.i.i.i:                              ; preds = %while.cond.preheader.i.i.i
  %conv9.us.i.i.i = trunc i128 %carry.0.lcssa.i.i.i to i64
  %inc12.us.i.i.i = add i32 %70, 1
  %idxprom13.us.i.i.i = sext i32 %70 to i64
  %arrayidx14.us.i.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %idxprom13.us.i.i.i
  store i64 %conv9.us.i.i.i, ptr %arrayidx14.us.i.i.i
  br label %for.inc143.i.i

for.body.i.i.i:                                   ; preds = %for.body.i.i.i, %for.body.lr.ph.i.i.i.new
  %indvars.iv.i.i.i = phi i64 [ 0, %for.body.lr.ph.i.i.i.new ], [ %indvars.iv.next.i.i.i.3, %for.body.i.i.i ]
  %carry.029.i.i.i = phi i128 [ %conv.i.i.i, %for.body.lr.ph.i.i.i.new ], [ %shr.i.i.i.3, %for.body.i.i.i ]
  %niter1048 = phi i64 [ 0, %for.body.lr.ph.i.i.i.new ], [ %niter1048.next.3, %for.body.i.i.i ]
  %arrayidx.i.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i.i
  %74 = load i64, ptr %arrayidx.i.i.i
  %conv2.i.i.i = zext i64 %74 to i128
  %mul.i.i.i = mul i128 %conv2.i.i.i, 10000000000000000000
  %add4.i.i.i = add i128 %mul.i.i.i, %carry.029.i.i.i
  %conv5.i.i.i = trunc i128 %add4.i.i.i to i64
  store i64 %conv5.i.i.i, ptr %arrayidx.i.i.i
  %shr.i.i.i = lshr i128 %add4.i.i.i, 64
  %indvars.iv.next.i.i.i = or i64 %indvars.iv.i.i.i, 1
  %arrayidx.i.i.i.1 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i.i
  %75 = load i64, ptr %arrayidx.i.i.i.1
  %conv2.i.i.i.1 = zext i64 %75 to i128
  %mul.i.i.i.1 = mul i128 %conv2.i.i.i.1, 10000000000000000000
  %add4.i.i.i.1 = add i128 %mul.i.i.i.1, %shr.i.i.i
  %conv5.i.i.i.1 = trunc i128 %add4.i.i.i.1 to i64
  store i64 %conv5.i.i.i.1, ptr %arrayidx.i.i.i.1
  %shr.i.i.i.1 = lshr i128 %add4.i.i.i.1, 64
  %indvars.iv.next.i.i.i.1 = or i64 %indvars.iv.i.i.i, 2
  %arrayidx.i.i.i.2 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i.i.1
  %76 = load i64, ptr %arrayidx.i.i.i.2
  %conv2.i.i.i.2 = zext i64 %76 to i128
  %mul.i.i.i.2 = mul i128 %conv2.i.i.i.2, 10000000000000000000
  %add4.i.i.i.2 = add i128 %mul.i.i.i.2, %shr.i.i.i.1
  %conv5.i.i.i.2 = trunc i128 %add4.i.i.i.2 to i64
  store i64 %conv5.i.i.i.2, ptr %arrayidx.i.i.i.2
  %shr.i.i.i.2 = lshr i128 %add4.i.i.i.2, 64
  %indvars.iv.next.i.i.i.2 = or i64 %indvars.iv.i.i.i, 3
  %arrayidx.i.i.i.3 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i.i.2
  %77 = load i64, ptr %arrayidx.i.i.i.3
  %conv2.i.i.i.3 = zext i64 %77 to i128
  %mul.i.i.i.3 = mul i128 %conv2.i.i.i.3, 10000000000000000000
  %add4.i.i.i.3 = add i128 %mul.i.i.i.3, %shr.i.i.i.2
  %conv5.i.i.i.3 = trunc i128 %add4.i.i.i.3 to i64
  store i64 %conv5.i.i.i.3, ptr %arrayidx.i.i.i.3
  %shr.i.i.i.3 = lshr i128 %add4.i.i.i.3, 64
  %indvars.iv.next.i.i.i.3 = add i64 %indvars.iv.i.i.i, 4
  %niter1048.next.3 = add i64 %niter1048, 4
  %niter1048.ncmp.3 = icmp eq i64 %niter1048.next.3, %unroll_iter1047
  br i1 %niter1048.ncmp.3, label %while.cond.preheader.i.i.i.loopexit.unr-lcssa, label %for.body.i.i.i

for.inc143.i.i:                                   ; preds = %while.body.us.i.i.i, %while.cond.preheader.i.i.i, %for.body132.i.i
  %78 = phi i32 [ %70, %for.body132.i.i ], [ %70, %while.cond.preheader.i.i.i ], [ %inc12.us.i.i.i, %while.body.us.i.i.i ]
  %chunk.1.i.i = phi i64 [ %add136.i.i, %for.body132.i.i ], [ 0, %while.cond.preheader.i.i.i ], [ 0, %while.body.us.i.i.i ]
  %cn.1.i.i = phi i32 [ %inc137.i.i, %for.body132.i.i ], [ 0, %while.cond.preheader.i.i.i ], [ 0, %while.body.us.i.i.i ]
  %inc144.i.i = add i64 %j.0740.i.i, 1
  %exitcond780.not.i.i = icmp eq i64 %inc144.i.i, %R.0701.i.i
  br i1 %exitcond780.not.i.i, label %for.cond.cleanup.i.i, label %for.body132.i.i

if.then148.i.i:                                   ; preds = %for.cond.cleanup.i.i
  %conv.i514.i.i = zext i64 %chunk.1.i.i to i128
  %cmp28.i516.i.i = icmp sgt i32 %78, 0
  br i1 %cmp28.i516.i.i, label %for.body.lr.ph.i525.i.i, label %while.cond.preheader.i517.i.i

for.body.lr.ph.i525.i.i:                          ; preds = %if.then148.i.i
  %idxprom.i.i = sext i32 %cn.1.i.i to i64
  %arrayidx150.i.i = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %idxprom.i.i
  %79 = load i64, ptr %arrayidx150.i.i
  %conv3.i.i.i = zext i64 %79 to i128
  %wide.trip.count.i526.i.i = zext i32 %78 to i64
  %xtraiter1049 = and i64 %wide.trip.count.i526.i.i, 3
  %80 = icmp ult i32 %78, 4
  br i1 %80, label %while.cond.preheader.i517.i.i.loopexit.unr-lcssa, label %for.body.lr.ph.i525.i.i.new

for.body.lr.ph.i525.i.i.new:                      ; preds = %for.body.lr.ph.i525.i.i
  %unroll_iter1053 = and i64 %wide.trip.count.i526.i.i, 2147483644
  br label %for.body.i527.i.i

while.cond.preheader.i517.i.i.loopexit.unr-lcssa: ; preds = %for.body.i527.i.i, %for.body.lr.ph.i525.i.i
  %shr.i535.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i525.i.i ], [ %shr.i535.i.i.3, %for.body.i527.i.i ]
  %indvars.iv.i528.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i525.i.i ], [ %indvars.iv.next.i536.i.i.3, %for.body.i527.i.i ]
  %carry.029.i529.i.i.unr = phi i128 [ %conv.i514.i.i, %for.body.lr.ph.i525.i.i ], [ %shr.i535.i.i.3, %for.body.i527.i.i ]
  %lcmp.mod1051.not = icmp eq i64 %xtraiter1049, 0
  br i1 %lcmp.mod1051.not, label %while.cond.preheader.i517.i.i, label %for.body.i527.i.i.epil

for.body.i527.i.i.epil:                           ; preds = %for.body.i527.i.i.epil, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa
  %indvars.iv.i528.i.i.epil = phi i64 [ %indvars.iv.next.i536.i.i.epil, %for.body.i527.i.i.epil ], [ %indvars.iv.i528.i.i.unr, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa ]
  %carry.029.i529.i.i.epil = phi i128 [ %shr.i535.i.i.epil, %for.body.i527.i.i.epil ], [ %carry.029.i529.i.i.unr, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa ]
  %epil.iter1050 = phi i64 [ %epil.iter1050.next, %for.body.i527.i.i.epil ], [ 0, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa ]
  %arrayidx.i530.i.i.epil = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i528.i.i.epil
  %81 = load i64, ptr %arrayidx.i530.i.i.epil
  %conv2.i531.i.i.epil = zext i64 %81 to i128
  %mul.i532.i.i.epil = mul i128 %conv2.i531.i.i.epil, %conv3.i.i.i
  %add4.i533.i.i.epil = add i128 %mul.i532.i.i.epil, %carry.029.i529.i.i.epil
  %conv5.i534.i.i.epil = trunc i128 %add4.i533.i.i.epil to i64
  store i64 %conv5.i534.i.i.epil, ptr %arrayidx.i530.i.i.epil
  %shr.i535.i.i.epil = lshr i128 %add4.i533.i.i.epil, 64
  %indvars.iv.next.i536.i.i.epil = add i64 %indvars.iv.i528.i.i.epil, 1
  %epil.iter1050.next = add i64 %epil.iter1050, 1
  %epil.iter1050.cmp.not = icmp eq i64 %epil.iter1050.next, %xtraiter1049
  br i1 %epil.iter1050.cmp.not, label %while.cond.preheader.i517.i.i, label %for.body.i527.i.i.epil

while.cond.preheader.i517.i.i:                    ; preds = %for.body.i527.i.i.epil, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa, %if.then148.i.i
  %carry.0.lcssa.i518.i.i = phi i128 [ %conv.i514.i.i, %if.then148.i.i ], [ %shr.i535.i.i.lcssa.ph, %while.cond.preheader.i517.i.i.loopexit.unr-lcssa ], [ %shr.i535.i.i.epil, %for.body.i527.i.i.epil ]
  %tobool.not31.i519.i.i = icmp eq i128 %carry.0.lcssa.i518.i.i, 0
  br i1 %tobool.not31.i519.i.i, label %if.end151.i.i, label %while.body.us.i520.i.i

while.body.us.i520.i.i:                           ; preds = %while.cond.preheader.i517.i.i
  %conv9.us.i521.i.i = trunc i128 %carry.0.lcssa.i518.i.i to i64
  %inc12.us.i522.i.i = add i32 %78, 1
  %idxprom13.us.i523.i.i = sext i32 %78 to i64
  %arrayidx14.us.i524.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %idxprom13.us.i523.i.i
  store i64 %conv9.us.i521.i.i, ptr %arrayidx14.us.i524.i.i
  br label %if.end151.i.i.sink.split

for.body.i527.i.i:                                ; preds = %for.body.i527.i.i, %for.body.lr.ph.i525.i.i.new
  %indvars.iv.i528.i.i = phi i64 [ 0, %for.body.lr.ph.i525.i.i.new ], [ %indvars.iv.next.i536.i.i.3, %for.body.i527.i.i ]
  %carry.029.i529.i.i = phi i128 [ %conv.i514.i.i, %for.body.lr.ph.i525.i.i.new ], [ %shr.i535.i.i.3, %for.body.i527.i.i ]
  %niter1054 = phi i64 [ 0, %for.body.lr.ph.i525.i.i.new ], [ %niter1054.next.3, %for.body.i527.i.i ]
  %arrayidx.i530.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i528.i.i
  %82 = load i64, ptr %arrayidx.i530.i.i
  %conv2.i531.i.i = zext i64 %82 to i128
  %mul.i532.i.i = mul i128 %conv2.i531.i.i, %conv3.i.i.i
  %add4.i533.i.i = add i128 %mul.i532.i.i, %carry.029.i529.i.i
  %conv5.i534.i.i = trunc i128 %add4.i533.i.i to i64
  store i64 %conv5.i534.i.i, ptr %arrayidx.i530.i.i
  %shr.i535.i.i = lshr i128 %add4.i533.i.i, 64
  %indvars.iv.next.i536.i.i = or i64 %indvars.iv.i528.i.i, 1
  %arrayidx.i530.i.i.1 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i536.i.i
  %83 = load i64, ptr %arrayidx.i530.i.i.1
  %conv2.i531.i.i.1 = zext i64 %83 to i128
  %mul.i532.i.i.1 = mul i128 %conv2.i531.i.i.1, %conv3.i.i.i
  %add4.i533.i.i.1 = add i128 %mul.i532.i.i.1, %shr.i535.i.i
  %conv5.i534.i.i.1 = trunc i128 %add4.i533.i.i.1 to i64
  store i64 %conv5.i534.i.i.1, ptr %arrayidx.i530.i.i.1
  %shr.i535.i.i.1 = lshr i128 %add4.i533.i.i.1, 64
  %indvars.iv.next.i536.i.i.1 = or i64 %indvars.iv.i528.i.i, 2
  %arrayidx.i530.i.i.2 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i536.i.i.1
  %84 = load i64, ptr %arrayidx.i530.i.i.2
  %conv2.i531.i.i.2 = zext i64 %84 to i128
  %mul.i532.i.i.2 = mul i128 %conv2.i531.i.i.2, %conv3.i.i.i
  %add4.i533.i.i.2 = add i128 %mul.i532.i.i.2, %shr.i535.i.i.1
  %conv5.i534.i.i.2 = trunc i128 %add4.i533.i.i.2 to i64
  store i64 %conv5.i534.i.i.2, ptr %arrayidx.i530.i.i.2
  %shr.i535.i.i.2 = lshr i128 %add4.i533.i.i.2, 64
  %indvars.iv.next.i536.i.i.2 = or i64 %indvars.iv.i528.i.i, 3
  %arrayidx.i530.i.i.3 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i536.i.i.2
  %85 = load i64, ptr %arrayidx.i530.i.i.3
  %conv2.i531.i.i.3 = zext i64 %85 to i128
  %mul.i532.i.i.3 = mul i128 %conv2.i531.i.i.3, %conv3.i.i.i
  %add4.i533.i.i.3 = add i128 %mul.i532.i.i.3, %shr.i535.i.i.2
  %conv5.i534.i.i.3 = trunc i128 %add4.i533.i.i.3 to i64
  store i64 %conv5.i534.i.i.3, ptr %arrayidx.i530.i.i.3
  %shr.i535.i.i.3 = lshr i128 %add4.i533.i.i.3, 64
  %indvars.iv.next.i536.i.i.3 = add i64 %indvars.iv.i528.i.i, 4
  %niter1054.next.3 = add i64 %niter1054, 4
  %niter1054.ncmp.3 = icmp eq i64 %niter1054.next.3, %unroll_iter1053
  br i1 %niter1054.ncmp.3, label %while.cond.preheader.i517.i.i.loopexit.unr-lcssa, label %for.body.i527.i.i

if.end151.i.i.sink.split:                         ; preds = %while.body.us.i520.i.i, %if.end126.i.i
  %inc12.us.i522.i.i.sink = phi i32 [ %inc12.us.i522.i.i, %while.body.us.i520.i.i ], [ 0, %if.end126.i.i ]
  store i32 %inc12.us.i522.i.i.sink, ptr %n.i.i.i
  br label %if.end151.i.i

if.end151.i.i:                                    ; preds = %if.end151.i.i.sink.split, %while.cond.preheader.i517.i.i, %for.cond.cleanup.i.i
  %pow.i.i = getelementptr inbounds i8, ptr %v.i.i, i64 776
  store i64 1, ptr %pow.i.i
  %n.i539.i.i = getelementptr inbounds i8, ptr %v.i.i, i64 1544
  store i32 1, ptr %n.i539.i.i
  %tobool152.not.i.i = icmp eq i32 %sticky.0714.i.i, 0
  br i1 %tobool152.not.i.i, label %if.else164.i.i, label %if.then153.i.i

if.then153.i.i:                                   ; preds = %if.end151.i.i
  %sub154.i.i = sub i64 0, %add108.i.i
  %cmp155746.i.i = icmp sgt i64 %sub154.i.i, 26
  br i1 %cmp155746.i.i, label %while.body.i.i, label %while.end.thread.i.i

while.body.i.i:                                   ; preds = %stk_mul_u64.exit.i.i, %if.then153.i.i
  %k.0748.i.i = phi i64 [ %sub158.i.i, %stk_mul_u64.exit.i.i ], [ %sub154.i.i, %if.then153.i.i ]
  %inc12.us.i.i745747.i.i = phi i32 [ %inc12.us.i.i744.i.i, %stk_mul_u64.exit.i.i ], [ 1, %if.then153.i.i ]
  %cmp28.i.i.i.i = icmp sgt i32 %inc12.us.i.i745747.i.i, 0
  br i1 %cmp28.i.i.i.i, label %for.body.lr.ph.i.i.i.i, label %stk_mul_u64.exit.i.i

for.body.lr.ph.i.i.i.i:                           ; preds = %while.body.i.i
  %wide.trip.count.i.i.i.i = zext i32 %inc12.us.i.i745747.i.i to i64
  %xtraiter1055 = and i64 %wide.trip.count.i.i.i.i, 3
  %86 = icmp ult i32 %inc12.us.i.i745747.i.i, 4
  br i1 %86, label %while.cond.preheader.i.i.i.i.unr-lcssa, label %for.body.lr.ph.i.i.i.i.new

for.body.lr.ph.i.i.i.i.new:                       ; preds = %for.body.lr.ph.i.i.i.i
  %unroll_iter1060 = and i64 %wide.trip.count.i.i.i.i, 2147483644
  br label %for.body.i.i.i.i

while.cond.preheader.i.i.i.i.unr-lcssa.loopexit:  ; preds = %for.body.i.i.i.i
  %extract.t1091 = trunc i128 %shr.i.i.i.i.3 to i64
  br label %while.cond.preheader.i.i.i.i.unr-lcssa

while.cond.preheader.i.i.i.i.unr-lcssa:           ; preds = %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit, %for.body.lr.ph.i.i.i.i
  %add4.i.i.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i.i.i ], [ %add4.i.i.i.i.3, %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit ]
  %shr.i.i.i.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i.i.i.i ], [ %extract.t1091, %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit ]
  %indvars.iv.i.i.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i.i.i ], [ %indvars.iv.next.i.i.i.i.3, %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit ]
  %carry.029.i.i.i.i.unr = phi i128 [ 0, %for.body.lr.ph.i.i.i.i ], [ %shr.i.i.i.i.3, %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit ]
  %lcmp.mod1057.not = icmp eq i64 %xtraiter1055, 0
  br i1 %lcmp.mod1057.not, label %while.cond.preheader.i.i.i.i, label %for.body.i.i.i.i.epil

for.body.i.i.i.i.epil:                            ; preds = %for.body.i.i.i.i.epil, %while.cond.preheader.i.i.i.i.unr-lcssa
  %indvars.iv.i.i.i.i.epil = phi i64 [ %indvars.iv.next.i.i.i.i.epil, %for.body.i.i.i.i.epil ], [ %indvars.iv.i.i.i.i.unr, %while.cond.preheader.i.i.i.i.unr-lcssa ]
  %carry.029.i.i.i.i.epil = phi i128 [ %shr.i.i.i.i.epil, %for.body.i.i.i.i.epil ], [ %carry.029.i.i.i.i.unr, %while.cond.preheader.i.i.i.i.unr-lcssa ]
  %epil.iter1056 = phi i64 [ %epil.iter1056.next, %for.body.i.i.i.i.epil ], [ 0, %while.cond.preheader.i.i.i.i.unr-lcssa ]
  %arrayidx.i.i.i.i.epil = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i.i.i.epil
  %87 = load i64, ptr %arrayidx.i.i.i.i.epil
  %conv2.i.i.i.i.epil = zext i64 %87 to i128
  %mul.i.i.i.i.epil = mul i128 %conv2.i.i.i.i.epil, 7450580596923828125
  %add4.i.i.i.i.epil = add i128 %mul.i.i.i.i.epil, %carry.029.i.i.i.i.epil
  %conv5.i.i.i.i.epil = trunc i128 %add4.i.i.i.i.epil to i64
  store i64 %conv5.i.i.i.i.epil, ptr %arrayidx.i.i.i.i.epil
  %shr.i.i.i.i.epil = lshr i128 %add4.i.i.i.i.epil, 64
  %indvars.iv.next.i.i.i.i.epil = add i64 %indvars.iv.i.i.i.i.epil, 1
  %epil.iter1056.next = add i64 %epil.iter1056, 1
  %epil.iter1056.cmp.not = icmp eq i64 %epil.iter1056.next, %xtraiter1055
  br i1 %epil.iter1056.cmp.not, label %while.cond.preheader.i.i.i.i.epilog-lcssa, label %for.body.i.i.i.i.epil

while.cond.preheader.i.i.i.i.epilog-lcssa:        ; preds = %for.body.i.i.i.i.epil
  %extract.t1090 = trunc i128 %shr.i.i.i.i.epil to i64
  br label %while.cond.preheader.i.i.i.i

while.cond.preheader.i.i.i.i:                     ; preds = %while.cond.preheader.i.i.i.i.epilog-lcssa, %while.cond.preheader.i.i.i.i.unr-lcssa
  %add4.i.i.i.i.lcssa = phi i128 [ %add4.i.i.i.i.lcssa.ph, %while.cond.preheader.i.i.i.i.unr-lcssa ], [ %add4.i.i.i.i.epil, %while.cond.preheader.i.i.i.i.epilog-lcssa ]
  %shr.i.i.i.i.lcssa.off0 = phi i64 [ %shr.i.i.i.i.lcssa.ph.off0, %while.cond.preheader.i.i.i.i.unr-lcssa ], [ %extract.t1090, %while.cond.preheader.i.i.i.i.epilog-lcssa ]
  %tobool.not31.i.i.i.i = icmp samesign ult i128 %add4.i.i.i.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i.i.i.i, label %stk_mul_u64.exit.i.i, label %while.body.us.i.i.i.i

while.body.us.i.i.i.i:                            ; preds = %while.cond.preheader.i.i.i.i
  %inc12.us.i.i.i.i = add i32 %inc12.us.i.i745747.i.i, 1
  %arrayidx14.us.i.i.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %wide.trip.count.i.i.i.i
  store i64 %shr.i.i.i.i.lcssa.off0, ptr %arrayidx14.us.i.i.i.i
  br label %stk_mul_u64.exit.i.i

for.body.i.i.i.i:                                 ; preds = %for.body.i.i.i.i, %for.body.lr.ph.i.i.i.i.new
  %indvars.iv.i.i.i.i = phi i64 [ 0, %for.body.lr.ph.i.i.i.i.new ], [ %indvars.iv.next.i.i.i.i.3, %for.body.i.i.i.i ]
  %carry.029.i.i.i.i = phi i128 [ 0, %for.body.lr.ph.i.i.i.i.new ], [ %shr.i.i.i.i.3, %for.body.i.i.i.i ]
  %niter1061 = phi i64 [ 0, %for.body.lr.ph.i.i.i.i.new ], [ %niter1061.next.3, %for.body.i.i.i.i ]
  %arrayidx.i.i.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i.i.i
  %88 = load i64, ptr %arrayidx.i.i.i.i
  %conv2.i.i.i.i = zext i64 %88 to i128
  %mul.i.i.i.i = mul i128 %conv2.i.i.i.i, 7450580596923828125
  %add4.i.i.i.i = add i128 %mul.i.i.i.i, %carry.029.i.i.i.i
  %conv5.i.i.i.i = trunc i128 %add4.i.i.i.i to i64
  store i64 %conv5.i.i.i.i, ptr %arrayidx.i.i.i.i
  %shr.i.i.i.i = lshr i128 %add4.i.i.i.i, 64
  %indvars.iv.next.i.i.i.i = or i64 %indvars.iv.i.i.i.i, 1
  %arrayidx.i.i.i.i.1 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i.i.i
  %89 = load i64, ptr %arrayidx.i.i.i.i.1
  %conv2.i.i.i.i.1 = zext i64 %89 to i128
  %mul.i.i.i.i.1 = mul i128 %conv2.i.i.i.i.1, 7450580596923828125
  %add4.i.i.i.i.1 = add i128 %mul.i.i.i.i.1, %shr.i.i.i.i
  %conv5.i.i.i.i.1 = trunc i128 %add4.i.i.i.i.1 to i64
  store i64 %conv5.i.i.i.i.1, ptr %arrayidx.i.i.i.i.1
  %shr.i.i.i.i.1 = lshr i128 %add4.i.i.i.i.1, 64
  %indvars.iv.next.i.i.i.i.1 = or i64 %indvars.iv.i.i.i.i, 2
  %arrayidx.i.i.i.i.2 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i.i.i.1
  %90 = load i64, ptr %arrayidx.i.i.i.i.2
  %conv2.i.i.i.i.2 = zext i64 %90 to i128
  %mul.i.i.i.i.2 = mul i128 %conv2.i.i.i.i.2, 7450580596923828125
  %add4.i.i.i.i.2 = add i128 %mul.i.i.i.i.2, %shr.i.i.i.i.1
  %conv5.i.i.i.i.2 = trunc i128 %add4.i.i.i.i.2 to i64
  store i64 %conv5.i.i.i.i.2, ptr %arrayidx.i.i.i.i.2
  %shr.i.i.i.i.2 = lshr i128 %add4.i.i.i.i.2, 64
  %indvars.iv.next.i.i.i.i.2 = or i64 %indvars.iv.i.i.i.i, 3
  %arrayidx.i.i.i.i.3 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i.i.i.2
  %91 = load i64, ptr %arrayidx.i.i.i.i.3
  %conv2.i.i.i.i.3 = zext i64 %91 to i128
  %mul.i.i.i.i.3 = mul i128 %conv2.i.i.i.i.3, 7450580596923828125
  %add4.i.i.i.i.3 = add i128 %mul.i.i.i.i.3, %shr.i.i.i.i.2
  %conv5.i.i.i.i.3 = trunc i128 %add4.i.i.i.i.3 to i64
  store i64 %conv5.i.i.i.i.3, ptr %arrayidx.i.i.i.i.3
  %shr.i.i.i.i.3 = lshr i128 %add4.i.i.i.i.3, 64
  %indvars.iv.next.i.i.i.i.3 = add i64 %indvars.iv.i.i.i.i, 4
  %niter1061.next.3 = add i64 %niter1061, 4
  %niter1061.ncmp.3 = icmp eq i64 %niter1061.next.3, %unroll_iter1060
  br i1 %niter1061.ncmp.3, label %while.cond.preheader.i.i.i.i.unr-lcssa.loopexit, label %for.body.i.i.i.i

stk_mul_u64.exit.i.i:                             ; preds = %while.body.us.i.i.i.i, %while.cond.preheader.i.i.i.i, %while.body.i.i
  %inc12.us.i.i744.i.i = phi i32 [ %inc12.us.i.i745747.i.i, %while.body.i.i ], [ %inc12.us.i.i745747.i.i, %while.cond.preheader.i.i.i.i ], [ %inc12.us.i.i.i.i, %while.body.us.i.i.i.i ]
  %sub158.i.i = add i64 %k.0748.i.i, -27
  %cmp155.i.i = icmp sgt i64 %k.0748.i.i, 53
  br i1 %cmp155.i.i, label %while.body.i.i, label %while.end.i.i

while.end.i.i:                                    ; preds = %stk_mul_u64.exit.i.i
  store i32 %inc12.us.i.i744.i.i, ptr %n.i539.i.i
  %tobool159.not.i.i = icmp ne i64 %sub158.i.i, 0
  %cmp28.i.i541.i.i = icmp sgt i32 %inc12.us.i.i744.i.i, 0
  %or.cond864.i.i = select i1 %tobool159.not.i.i, i1 %cmp28.i.i541.i.i, i1 false
  br i1 %or.cond864.i.i, label %for.body.lr.ph.i.i542.i.i, label %if.end198.i.i

while.end.thread.i.i:                             ; preds = %if.then153.i.i
  store i32 1, ptr %n.i539.i.i
  %tobool159.not821.i.i = icmp eq i64 %add108.i.i, 0
  br i1 %tobool159.not821.i.i, label %if.end198.i.i, label %for.body.lr.ph.i.i542.i.i

for.body.lr.ph.i.i542.i.i:                        ; preds = %while.end.thread.i.i, %while.end.i.i
  %92 = phi i32 [ 1, %while.end.thread.i.i ], [ %inc12.us.i.i744.i.i, %while.end.i.i ]
  %k.0.lcssa822825.i.i = phi i64 [ %sub154.i.i, %while.end.thread.i.i ], [ %sub158.i.i, %while.end.i.i ]
  %arrayidx162.i.i = getelementptr inbounds [27 x i64], ptr @STK_P5, i64 0, i64 %k.0.lcssa822825.i.i
  %93 = load i64, ptr %arrayidx162.i.i
  %conv3.i.i.i.i = zext i64 %93 to i128
  %wide.trip.count.i.i543.i.i = zext i32 %92 to i64
  %xtraiter1062 = and i64 %wide.trip.count.i.i543.i.i, 3
  %94 = add i32 %92, -1
  %95 = icmp ult i32 %94, 3
  br i1 %95, label %while.cond.preheader.i.i555.i.i.unr-lcssa, label %for.body.lr.ph.i.i542.i.i.new

for.body.lr.ph.i.i542.i.i.new:                    ; preds = %for.body.lr.ph.i.i542.i.i
  %unroll_iter1067 = and i64 %wide.trip.count.i.i543.i.i, 2147483644
  br label %for.body.i.i544.i.i

while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit: ; preds = %for.body.i.i544.i.i
  %extract.t1093 = trunc i128 %shr.i.i552.i.i.3 to i64
  br label %while.cond.preheader.i.i555.i.i.unr-lcssa

while.cond.preheader.i.i555.i.i.unr-lcssa:        ; preds = %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit, %for.body.lr.ph.i.i542.i.i
  %add4.i.i550.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i542.i.i ], [ %add4.i.i550.i.i.3, %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit ]
  %shr.i.i552.i.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i.i542.i.i ], [ %extract.t1093, %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit ]
  %indvars.iv.i.i545.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i542.i.i ], [ %indvars.iv.next.i.i553.i.i.3, %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit ]
  %carry.029.i.i546.i.i.unr = phi i128 [ 0, %for.body.lr.ph.i.i542.i.i ], [ %shr.i.i552.i.i.3, %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit ]
  %lcmp.mod1064.not = icmp eq i64 %xtraiter1062, 0
  br i1 %lcmp.mod1064.not, label %while.cond.preheader.i.i555.i.i, label %for.body.i.i544.i.i.epil

for.body.i.i544.i.i.epil:                         ; preds = %for.body.i.i544.i.i.epil, %while.cond.preheader.i.i555.i.i.unr-lcssa
  %indvars.iv.i.i545.i.i.epil = phi i64 [ %indvars.iv.next.i.i553.i.i.epil, %for.body.i.i544.i.i.epil ], [ %indvars.iv.i.i545.i.i.unr, %while.cond.preheader.i.i555.i.i.unr-lcssa ]
  %carry.029.i.i546.i.i.epil = phi i128 [ %shr.i.i552.i.i.epil, %for.body.i.i544.i.i.epil ], [ %carry.029.i.i546.i.i.unr, %while.cond.preheader.i.i555.i.i.unr-lcssa ]
  %epil.iter1063 = phi i64 [ %epil.iter1063.next, %for.body.i.i544.i.i.epil ], [ 0, %while.cond.preheader.i.i555.i.i.unr-lcssa ]
  %arrayidx.i.i547.i.i.epil = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i545.i.i.epil
  %96 = load i64, ptr %arrayidx.i.i547.i.i.epil
  %conv2.i.i548.i.i.epil = zext i64 %96 to i128
  %mul.i.i549.i.i.epil = mul i128 %conv2.i.i548.i.i.epil, %conv3.i.i.i.i
  %add4.i.i550.i.i.epil = add i128 %mul.i.i549.i.i.epil, %carry.029.i.i546.i.i.epil
  %conv5.i.i551.i.i.epil = trunc i128 %add4.i.i550.i.i.epil to i64
  store i64 %conv5.i.i551.i.i.epil, ptr %arrayidx.i.i547.i.i.epil
  %shr.i.i552.i.i.epil = lshr i128 %add4.i.i550.i.i.epil, 64
  %indvars.iv.next.i.i553.i.i.epil = add i64 %indvars.iv.i.i545.i.i.epil, 1
  %epil.iter1063.next = add i64 %epil.iter1063, 1
  %epil.iter1063.cmp.not = icmp eq i64 %epil.iter1063.next, %xtraiter1062
  br i1 %epil.iter1063.cmp.not, label %while.cond.preheader.i.i555.i.i.epilog-lcssa, label %for.body.i.i544.i.i.epil

while.cond.preheader.i.i555.i.i.epilog-lcssa:     ; preds = %for.body.i.i544.i.i.epil
  %extract.t1092 = trunc i128 %shr.i.i552.i.i.epil to i64
  br label %while.cond.preheader.i.i555.i.i

while.cond.preheader.i.i555.i.i:                  ; preds = %while.cond.preheader.i.i555.i.i.epilog-lcssa, %while.cond.preheader.i.i555.i.i.unr-lcssa
  %add4.i.i550.i.i.lcssa = phi i128 [ %add4.i.i550.i.i.lcssa.ph, %while.cond.preheader.i.i555.i.i.unr-lcssa ], [ %add4.i.i550.i.i.epil, %while.cond.preheader.i.i555.i.i.epilog-lcssa ]
  %shr.i.i552.i.i.lcssa.off0 = phi i64 [ %shr.i.i552.i.i.lcssa.ph.off0, %while.cond.preheader.i.i555.i.i.unr-lcssa ], [ %extract.t1092, %while.cond.preheader.i.i555.i.i.epilog-lcssa ]
  %tobool.not31.i.i556.i.i = icmp ult i128 %add4.i.i550.i.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i.i556.i.i, label %if.end198.i.i, label %while.body.us.i.i557.i.i

while.body.us.i.i557.i.i:                         ; preds = %while.cond.preheader.i.i555.i.i
  %inc12.us.i.i559.i.i = add i32 %92, 1
  %arrayidx14.us.i.i560.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %wide.trip.count.i.i543.i.i
  store i64 %shr.i.i552.i.i.lcssa.off0, ptr %arrayidx14.us.i.i560.i.i
  store i32 %inc12.us.i.i559.i.i, ptr %n.i539.i.i
  br label %if.end198.i.i

for.body.i.i544.i.i:                              ; preds = %for.body.i.i544.i.i, %for.body.lr.ph.i.i542.i.i.new
  %indvars.iv.i.i545.i.i = phi i64 [ 0, %for.body.lr.ph.i.i542.i.i.new ], [ %indvars.iv.next.i.i553.i.i.3, %for.body.i.i544.i.i ]
  %carry.029.i.i546.i.i = phi i128 [ 0, %for.body.lr.ph.i.i542.i.i.new ], [ %shr.i.i552.i.i.3, %for.body.i.i544.i.i ]
  %niter1068 = phi i64 [ 0, %for.body.lr.ph.i.i542.i.i.new ], [ %niter1068.next.3, %for.body.i.i544.i.i ]
  %arrayidx.i.i547.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i545.i.i
  %97 = load i64, ptr %arrayidx.i.i547.i.i
  %conv2.i.i548.i.i = zext i64 %97 to i128
  %mul.i.i549.i.i = mul i128 %conv2.i.i548.i.i, %conv3.i.i.i.i
  %add4.i.i550.i.i = add i128 %mul.i.i549.i.i, %carry.029.i.i546.i.i
  %conv5.i.i551.i.i = trunc i128 %add4.i.i550.i.i to i64
  store i64 %conv5.i.i551.i.i, ptr %arrayidx.i.i547.i.i
  %shr.i.i552.i.i = lshr i128 %add4.i.i550.i.i, 64
  %indvars.iv.next.i.i553.i.i = or i64 %indvars.iv.i.i545.i.i, 1
  %arrayidx.i.i547.i.i.1 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i553.i.i
  %98 = load i64, ptr %arrayidx.i.i547.i.i.1
  %conv2.i.i548.i.i.1 = zext i64 %98 to i128
  %mul.i.i549.i.i.1 = mul i128 %conv2.i.i548.i.i.1, %conv3.i.i.i.i
  %add4.i.i550.i.i.1 = add i128 %mul.i.i549.i.i.1, %shr.i.i552.i.i
  %conv5.i.i551.i.i.1 = trunc i128 %add4.i.i550.i.i.1 to i64
  store i64 %conv5.i.i551.i.i.1, ptr %arrayidx.i.i547.i.i.1
  %shr.i.i552.i.i.1 = lshr i128 %add4.i.i550.i.i.1, 64
  %indvars.iv.next.i.i553.i.i.1 = or i64 %indvars.iv.i.i545.i.i, 2
  %arrayidx.i.i547.i.i.2 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i553.i.i.1
  %99 = load i64, ptr %arrayidx.i.i547.i.i.2
  %conv2.i.i548.i.i.2 = zext i64 %99 to i128
  %mul.i.i549.i.i.2 = mul i128 %conv2.i.i548.i.i.2, %conv3.i.i.i.i
  %add4.i.i550.i.i.2 = add i128 %mul.i.i549.i.i.2, %shr.i.i552.i.i.1
  %conv5.i.i551.i.i.2 = trunc i128 %add4.i.i550.i.i.2 to i64
  store i64 %conv5.i.i551.i.i.2, ptr %arrayidx.i.i547.i.i.2
  %shr.i.i552.i.i.2 = lshr i128 %add4.i.i550.i.i.2, 64
  %indvars.iv.next.i.i553.i.i.2 = or i64 %indvars.iv.i.i545.i.i, 3
  %arrayidx.i.i547.i.i.3 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i553.i.i.2
  %100 = load i64, ptr %arrayidx.i.i547.i.i.3
  %conv2.i.i548.i.i.3 = zext i64 %100 to i128
  %mul.i.i549.i.i.3 = mul i128 %conv2.i.i548.i.i.3, %conv3.i.i.i.i
  %add4.i.i550.i.i.3 = add i128 %mul.i.i549.i.i.3, %shr.i.i552.i.i.2
  %conv5.i.i551.i.i.3 = trunc i128 %add4.i.i550.i.i.3 to i64
  store i64 %conv5.i.i551.i.i.3, ptr %arrayidx.i.i547.i.i.3
  %shr.i.i552.i.i.3 = lshr i128 %add4.i.i550.i.i.3, 64
  %indvars.iv.next.i.i553.i.i.3 = add i64 %indvars.iv.i.i545.i.i, 4
  %niter1068.next.3 = add i64 %niter1068, 4
  %niter1068.ncmp.3 = icmp eq i64 %niter1068.next.3, %unroll_iter1067
  br i1 %niter1068.ncmp.3, label %while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit, label %for.body.i.i544.i.i

if.else164.i.i:                                   ; preds = %if.end151.i.i
  %cmp165.i.i = icmp slt i64 %add108.i.i, 0
  br i1 %cmp165.i.i, label %if.then167.i.i, label %while.cond184.preheader.i.i

while.cond184.preheader.i.i:                      ; preds = %if.else164.i.i
  %n.i.promoted751.i.i = load i32, ptr %n.i.i.i
  %cmp185753.i.i = icmp samesign ugt i64 %add108.i.i, 18
  br i1 %cmp185753.i.i, label %while.body187.i.i, label %while.end190.i.i

if.then167.i.i:                                   ; preds = %if.else164.i.i
  %sub169.i.i = sub i64 0, %add108.i.i
  %cmp171760.i.i = icmp sgt i64 %sub169.i.i, 18
  br i1 %cmp171760.i.i, label %while.body173.i.i, label %while.end176.thread.i.i

while.end176.thread.i.i:                          ; preds = %if.then167.i.i
  store i32 1, ptr %n.i539.i.i
  br label %if.then178.i.i

while.body173.i.i:                                ; preds = %stk_mul_u64.exit583.i.i, %if.then167.i.i
  %k168.0762.i.i = phi i64 [ %sub175.i.i, %stk_mul_u64.exit583.i.i ], [ %sub169.i.i, %if.then167.i.i ]
  %inc12.us.i.i581759761.i.i = phi i32 [ %inc12.us.i.i581758.i.i, %stk_mul_u64.exit583.i.i ], [ 1, %if.then167.i.i ]
  %cmp28.i.i563.i.i = icmp sgt i32 %inc12.us.i.i581759761.i.i, 0
  br i1 %cmp28.i.i563.i.i, label %for.body.lr.ph.i.i564.i.i, label %stk_mul_u64.exit583.i.i

for.body.lr.ph.i.i564.i.i:                        ; preds = %while.body173.i.i
  %wide.trip.count.i.i565.i.i = zext i32 %inc12.us.i.i581759761.i.i to i64
  %xtraiter1083 = and i64 %wide.trip.count.i.i565.i.i, 3
  %101 = icmp ult i32 %inc12.us.i.i581759761.i.i, 4
  br i1 %101, label %while.cond.preheader.i.i577.i.i.unr-lcssa, label %for.body.lr.ph.i.i564.i.i.new

for.body.lr.ph.i.i564.i.i.new:                    ; preds = %for.body.lr.ph.i.i564.i.i
  %unroll_iter1088 = and i64 %wide.trip.count.i.i565.i.i, 2147483644
  br label %for.body.i.i566.i.i

while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit: ; preds = %for.body.i.i566.i.i
  %extract.t1099 = trunc i128 %shr.i.i574.i.i.3 to i64
  br label %while.cond.preheader.i.i577.i.i.unr-lcssa

while.cond.preheader.i.i577.i.i.unr-lcssa:        ; preds = %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit, %for.body.lr.ph.i.i564.i.i
  %add4.i.i572.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i564.i.i ], [ %add4.i.i572.i.i.3, %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit ]
  %shr.i.i574.i.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i.i564.i.i ], [ %extract.t1099, %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit ]
  %indvars.iv.i.i567.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i564.i.i ], [ %indvars.iv.next.i.i575.i.i.3, %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit ]
  %carry.029.i.i568.i.i.unr = phi i128 [ 0, %for.body.lr.ph.i.i564.i.i ], [ %shr.i.i574.i.i.3, %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit ]
  %lcmp.mod1085.not = icmp eq i64 %xtraiter1083, 0
  br i1 %lcmp.mod1085.not, label %while.cond.preheader.i.i577.i.i, label %for.body.i.i566.i.i.epil

for.body.i.i566.i.i.epil:                         ; preds = %for.body.i.i566.i.i.epil, %while.cond.preheader.i.i577.i.i.unr-lcssa
  %indvars.iv.i.i567.i.i.epil = phi i64 [ %indvars.iv.next.i.i575.i.i.epil, %for.body.i.i566.i.i.epil ], [ %indvars.iv.i.i567.i.i.unr, %while.cond.preheader.i.i577.i.i.unr-lcssa ]
  %carry.029.i.i568.i.i.epil = phi i128 [ %shr.i.i574.i.i.epil, %for.body.i.i566.i.i.epil ], [ %carry.029.i.i568.i.i.unr, %while.cond.preheader.i.i577.i.i.unr-lcssa ]
  %epil.iter1084 = phi i64 [ %epil.iter1084.next, %for.body.i.i566.i.i.epil ], [ 0, %while.cond.preheader.i.i577.i.i.unr-lcssa ]
  %arrayidx.i.i569.i.i.epil = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i567.i.i.epil
  %102 = load i64, ptr %arrayidx.i.i569.i.i.epil
  %conv2.i.i570.i.i.epil = zext i64 %102 to i128
  %mul.i.i571.i.i.epil = mul i128 %conv2.i.i570.i.i.epil, 10000000000000000000
  %add4.i.i572.i.i.epil = add i128 %mul.i.i571.i.i.epil, %carry.029.i.i568.i.i.epil
  %conv5.i.i573.i.i.epil = trunc i128 %add4.i.i572.i.i.epil to i64
  store i64 %conv5.i.i573.i.i.epil, ptr %arrayidx.i.i569.i.i.epil
  %shr.i.i574.i.i.epil = lshr i128 %add4.i.i572.i.i.epil, 64
  %indvars.iv.next.i.i575.i.i.epil = add i64 %indvars.iv.i.i567.i.i.epil, 1
  %epil.iter1084.next = add i64 %epil.iter1084, 1
  %epil.iter1084.cmp.not = icmp eq i64 %epil.iter1084.next, %xtraiter1083
  br i1 %epil.iter1084.cmp.not, label %while.cond.preheader.i.i577.i.i.epilog-lcssa, label %for.body.i.i566.i.i.epil

while.cond.preheader.i.i577.i.i.epilog-lcssa:     ; preds = %for.body.i.i566.i.i.epil
  %extract.t1098 = trunc i128 %shr.i.i574.i.i.epil to i64
  br label %while.cond.preheader.i.i577.i.i

while.cond.preheader.i.i577.i.i:                  ; preds = %while.cond.preheader.i.i577.i.i.epilog-lcssa, %while.cond.preheader.i.i577.i.i.unr-lcssa
  %add4.i.i572.i.i.lcssa = phi i128 [ %add4.i.i572.i.i.lcssa.ph, %while.cond.preheader.i.i577.i.i.unr-lcssa ], [ %add4.i.i572.i.i.epil, %while.cond.preheader.i.i577.i.i.epilog-lcssa ]
  %shr.i.i574.i.i.lcssa.off0 = phi i64 [ %shr.i.i574.i.i.lcssa.ph.off0, %while.cond.preheader.i.i577.i.i.unr-lcssa ], [ %extract.t1098, %while.cond.preheader.i.i577.i.i.epilog-lcssa ]
  %tobool.not31.i.i578.i.i = icmp ult i128 %add4.i.i572.i.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i.i578.i.i, label %stk_mul_u64.exit583.i.i, label %while.body.us.i.i579.i.i

while.body.us.i.i579.i.i:                         ; preds = %while.cond.preheader.i.i577.i.i
  %inc12.us.i.i581.i.i = add i32 %inc12.us.i.i581759761.i.i, 1
  %arrayidx14.us.i.i582.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %wide.trip.count.i.i565.i.i
  store i64 %shr.i.i574.i.i.lcssa.off0, ptr %arrayidx14.us.i.i582.i.i
  br label %stk_mul_u64.exit583.i.i

for.body.i.i566.i.i:                              ; preds = %for.body.i.i566.i.i, %for.body.lr.ph.i.i564.i.i.new
  %indvars.iv.i.i567.i.i = phi i64 [ 0, %for.body.lr.ph.i.i564.i.i.new ], [ %indvars.iv.next.i.i575.i.i.3, %for.body.i.i566.i.i ]
  %carry.029.i.i568.i.i = phi i128 [ 0, %for.body.lr.ph.i.i564.i.i.new ], [ %shr.i.i574.i.i.3, %for.body.i.i566.i.i ]
  %niter1089 = phi i64 [ 0, %for.body.lr.ph.i.i564.i.i.new ], [ %niter1089.next.3, %for.body.i.i566.i.i ]
  %arrayidx.i.i569.i.i = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.i.i567.i.i
  %103 = load i64, ptr %arrayidx.i.i569.i.i
  %conv2.i.i570.i.i = zext i64 %103 to i128
  %mul.i.i571.i.i = mul i128 %conv2.i.i570.i.i, 10000000000000000000
  %add4.i.i572.i.i = add i128 %mul.i.i571.i.i, %carry.029.i.i568.i.i
  %conv5.i.i573.i.i = trunc i128 %add4.i.i572.i.i to i64
  store i64 %conv5.i.i573.i.i, ptr %arrayidx.i.i569.i.i
  %shr.i.i574.i.i = lshr i128 %add4.i.i572.i.i, 64
  %indvars.iv.next.i.i575.i.i = or i64 %indvars.iv.i.i567.i.i, 1
  %arrayidx.i.i569.i.i.1 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i575.i.i
  %104 = load i64, ptr %arrayidx.i.i569.i.i.1
  %conv2.i.i570.i.i.1 = zext i64 %104 to i128
  %mul.i.i571.i.i.1 = mul i128 %conv2.i.i570.i.i.1, 10000000000000000000
  %add4.i.i572.i.i.1 = add i128 %mul.i.i571.i.i.1, %shr.i.i574.i.i
  %conv5.i.i573.i.i.1 = trunc i128 %add4.i.i572.i.i.1 to i64
  store i64 %conv5.i.i573.i.i.1, ptr %arrayidx.i.i569.i.i.1
  %shr.i.i574.i.i.1 = lshr i128 %add4.i.i572.i.i.1, 64
  %indvars.iv.next.i.i575.i.i.1 = or i64 %indvars.iv.i.i567.i.i, 2
  %arrayidx.i.i569.i.i.2 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i575.i.i.1
  %105 = load i64, ptr %arrayidx.i.i569.i.i.2
  %conv2.i.i570.i.i.2 = zext i64 %105 to i128
  %mul.i.i571.i.i.2 = mul i128 %conv2.i.i570.i.i.2, 10000000000000000000
  %add4.i.i572.i.i.2 = add i128 %mul.i.i571.i.i.2, %shr.i.i574.i.i.1
  %conv5.i.i573.i.i.2 = trunc i128 %add4.i.i572.i.i.2 to i64
  store i64 %conv5.i.i573.i.i.2, ptr %arrayidx.i.i569.i.i.2
  %shr.i.i574.i.i.2 = lshr i128 %add4.i.i572.i.i.2, 64
  %indvars.iv.next.i.i575.i.i.2 = or i64 %indvars.iv.i.i567.i.i, 3
  %arrayidx.i.i569.i.i.3 = getelementptr inbounds [96 x i64], ptr %pow.i.i, i64 0, i64 %indvars.iv.next.i.i575.i.i.2
  %106 = load i64, ptr %arrayidx.i.i569.i.i.3
  %conv2.i.i570.i.i.3 = zext i64 %106 to i128
  %mul.i.i571.i.i.3 = mul i128 %conv2.i.i570.i.i.3, 10000000000000000000
  %add4.i.i572.i.i.3 = add i128 %mul.i.i571.i.i.3, %shr.i.i574.i.i.2
  %conv5.i.i573.i.i.3 = trunc i128 %add4.i.i572.i.i.3 to i64
  store i64 %conv5.i.i573.i.i.3, ptr %arrayidx.i.i569.i.i.3
  %shr.i.i574.i.i.3 = lshr i128 %add4.i.i572.i.i.3, 64
  %indvars.iv.next.i.i575.i.i.3 = add i64 %indvars.iv.i.i567.i.i, 4
  %niter1089.next.3 = add i64 %niter1089, 4
  %niter1089.ncmp.3 = icmp eq i64 %niter1089.next.3, %unroll_iter1088
  br i1 %niter1089.ncmp.3, label %while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit, label %for.body.i.i566.i.i

stk_mul_u64.exit583.i.i:                          ; preds = %while.body.us.i.i579.i.i, %while.cond.preheader.i.i577.i.i, %while.body173.i.i
  %inc12.us.i.i581758.i.i = phi i32 [ %inc12.us.i.i581759761.i.i, %while.body173.i.i ], [ %inc12.us.i.i581759761.i.i, %while.cond.preheader.i.i577.i.i ], [ %inc12.us.i.i581.i.i, %while.body.us.i.i579.i.i ]
  %sub175.i.i = add i64 %k168.0762.i.i, -19
  %cmp171.i.i = icmp sgt i64 %k168.0762.i.i, 37
  br i1 %cmp171.i.i, label %while.body173.i.i, label %while.end176.i.i

while.end176.i.i:                                 ; preds = %stk_mul_u64.exit583.i.i
  store i32 %inc12.us.i.i581758.i.i, ptr %n.i539.i.i
  %tobool177.not.i.i = icmp eq i64 %sub175.i.i, 0
  br i1 %tobool177.not.i.i, label %if.end198.i.i, label %if.then178.i.i

if.then178.i.i:                                   ; preds = %while.end176.i.i, %while.end176.thread.i.i
  %k168.0.lcssa829.i.i = phi i64 [ %sub169.i.i, %while.end176.thread.i.i ], [ %sub175.i.i, %while.end176.i.i ]
  %arrayidx180.i.i = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %k168.0.lcssa829.i.i
  %107 = load i64, ptr %arrayidx180.i.i
  call void @stk_mul_u64(ptr %pow.i.i, i64 %107)
  br label %if.end198.i.i

while.body187.i.i:                                ; preds = %stk_mul_u64.exit605.i.i, %while.cond184.preheader.i.i
  %k183.0754.i.i = phi i64 [ %sub189.i.i, %stk_mul_u64.exit605.i.i ], [ %add108.i.i, %while.cond184.preheader.i.i ]
  %108 = phi i32 [ %115, %stk_mul_u64.exit605.i.i ], [ %n.i.promoted751.i.i, %while.cond184.preheader.i.i ]
  %cmp28.i.i585.i.i = icmp sgt i32 %108, 0
  br i1 %cmp28.i.i585.i.i, label %for.body.lr.ph.i.i586.i.i, label %stk_mul_u64.exit605.i.i

for.body.lr.ph.i.i586.i.i:                        ; preds = %while.body187.i.i
  %wide.trip.count.i.i587.i.i = zext i32 %108 to i64
  %xtraiter1069 = and i64 %wide.trip.count.i.i587.i.i, 3
  %109 = icmp ult i32 %108, 4
  br i1 %109, label %while.cond.preheader.i.i599.i.i.unr-lcssa, label %for.body.lr.ph.i.i586.i.i.new

for.body.lr.ph.i.i586.i.i.new:                    ; preds = %for.body.lr.ph.i.i586.i.i
  %unroll_iter1074 = and i64 %wide.trip.count.i.i587.i.i, 2147483644
  br label %for.body.i.i588.i.i

while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit: ; preds = %for.body.i.i588.i.i
  %extract.t1095 = trunc i128 %shr.i.i596.i.i.3 to i64
  br label %while.cond.preheader.i.i599.i.i.unr-lcssa

while.cond.preheader.i.i599.i.i.unr-lcssa:        ; preds = %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit, %for.body.lr.ph.i.i586.i.i
  %add4.i.i594.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i586.i.i ], [ %add4.i.i594.i.i.3, %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit ]
  %shr.i.i596.i.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i.i586.i.i ], [ %extract.t1095, %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit ]
  %indvars.iv.i.i589.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i586.i.i ], [ %indvars.iv.next.i.i597.i.i.3, %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit ]
  %carry.029.i.i590.i.i.unr = phi i128 [ 0, %for.body.lr.ph.i.i586.i.i ], [ %shr.i.i596.i.i.3, %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit ]
  %lcmp.mod1071.not = icmp eq i64 %xtraiter1069, 0
  br i1 %lcmp.mod1071.not, label %while.cond.preheader.i.i599.i.i, label %for.body.i.i588.i.i.epil

for.body.i.i588.i.i.epil:                         ; preds = %for.body.i.i588.i.i.epil, %while.cond.preheader.i.i599.i.i.unr-lcssa
  %indvars.iv.i.i589.i.i.epil = phi i64 [ %indvars.iv.next.i.i597.i.i.epil, %for.body.i.i588.i.i.epil ], [ %indvars.iv.i.i589.i.i.unr, %while.cond.preheader.i.i599.i.i.unr-lcssa ]
  %carry.029.i.i590.i.i.epil = phi i128 [ %shr.i.i596.i.i.epil, %for.body.i.i588.i.i.epil ], [ %carry.029.i.i590.i.i.unr, %while.cond.preheader.i.i599.i.i.unr-lcssa ]
  %epil.iter1070 = phi i64 [ %epil.iter1070.next, %for.body.i.i588.i.i.epil ], [ 0, %while.cond.preheader.i.i599.i.i.unr-lcssa ]
  %arrayidx.i.i591.i.i.epil = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i589.i.i.epil
  %110 = load i64, ptr %arrayidx.i.i591.i.i.epil
  %conv2.i.i592.i.i.epil = zext i64 %110 to i128
  %mul.i.i593.i.i.epil = mul i128 %conv2.i.i592.i.i.epil, 10000000000000000000
  %add4.i.i594.i.i.epil = add i128 %mul.i.i593.i.i.epil, %carry.029.i.i590.i.i.epil
  %conv5.i.i595.i.i.epil = trunc i128 %add4.i.i594.i.i.epil to i64
  store i64 %conv5.i.i595.i.i.epil, ptr %arrayidx.i.i591.i.i.epil
  %shr.i.i596.i.i.epil = lshr i128 %add4.i.i594.i.i.epil, 64
  %indvars.iv.next.i.i597.i.i.epil = add i64 %indvars.iv.i.i589.i.i.epil, 1
  %epil.iter1070.next = add i64 %epil.iter1070, 1
  %epil.iter1070.cmp.not = icmp eq i64 %epil.iter1070.next, %xtraiter1069
  br i1 %epil.iter1070.cmp.not, label %while.cond.preheader.i.i599.i.i.epilog-lcssa, label %for.body.i.i588.i.i.epil

while.cond.preheader.i.i599.i.i.epilog-lcssa:     ; preds = %for.body.i.i588.i.i.epil
  %extract.t1094 = trunc i128 %shr.i.i596.i.i.epil to i64
  br label %while.cond.preheader.i.i599.i.i

while.cond.preheader.i.i599.i.i:                  ; preds = %while.cond.preheader.i.i599.i.i.epilog-lcssa, %while.cond.preheader.i.i599.i.i.unr-lcssa
  %add4.i.i594.i.i.lcssa = phi i128 [ %add4.i.i594.i.i.lcssa.ph, %while.cond.preheader.i.i599.i.i.unr-lcssa ], [ %add4.i.i594.i.i.epil, %while.cond.preheader.i.i599.i.i.epilog-lcssa ]
  %shr.i.i596.i.i.lcssa.off0 = phi i64 [ %shr.i.i596.i.i.lcssa.ph.off0, %while.cond.preheader.i.i599.i.i.unr-lcssa ], [ %extract.t1094, %while.cond.preheader.i.i599.i.i.epilog-lcssa ]
  %tobool.not31.i.i600.i.i = icmp ult i128 %add4.i.i594.i.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i.i600.i.i, label %stk_mul_u64.exit605.i.i, label %while.body.us.i.i601.i.i

while.body.us.i.i601.i.i:                         ; preds = %while.cond.preheader.i.i599.i.i
  %inc12.us.i.i603.i.i = add i32 %108, 1
  %arrayidx14.us.i.i604.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %wide.trip.count.i.i587.i.i
  store i64 %shr.i.i596.i.i.lcssa.off0, ptr %arrayidx14.us.i.i604.i.i
  br label %stk_mul_u64.exit605.i.i

for.body.i.i588.i.i:                              ; preds = %for.body.i.i588.i.i, %for.body.lr.ph.i.i586.i.i.new
  %indvars.iv.i.i589.i.i = phi i64 [ 0, %for.body.lr.ph.i.i586.i.i.new ], [ %indvars.iv.next.i.i597.i.i.3, %for.body.i.i588.i.i ]
  %carry.029.i.i590.i.i = phi i128 [ 0, %for.body.lr.ph.i.i586.i.i.new ], [ %shr.i.i596.i.i.3, %for.body.i.i588.i.i ]
  %niter1075 = phi i64 [ 0, %for.body.lr.ph.i.i586.i.i.new ], [ %niter1075.next.3, %for.body.i.i588.i.i ]
  %arrayidx.i.i591.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i589.i.i
  %111 = load i64, ptr %arrayidx.i.i591.i.i
  %conv2.i.i592.i.i = zext i64 %111 to i128
  %mul.i.i593.i.i = mul i128 %conv2.i.i592.i.i, 10000000000000000000
  %add4.i.i594.i.i = add i128 %mul.i.i593.i.i, %carry.029.i.i590.i.i
  %conv5.i.i595.i.i = trunc i128 %add4.i.i594.i.i to i64
  store i64 %conv5.i.i595.i.i, ptr %arrayidx.i.i591.i.i
  %shr.i.i596.i.i = lshr i128 %add4.i.i594.i.i, 64
  %indvars.iv.next.i.i597.i.i = or i64 %indvars.iv.i.i589.i.i, 1
  %arrayidx.i.i591.i.i.1 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i597.i.i
  %112 = load i64, ptr %arrayidx.i.i591.i.i.1
  %conv2.i.i592.i.i.1 = zext i64 %112 to i128
  %mul.i.i593.i.i.1 = mul i128 %conv2.i.i592.i.i.1, 10000000000000000000
  %add4.i.i594.i.i.1 = add i128 %mul.i.i593.i.i.1, %shr.i.i596.i.i
  %conv5.i.i595.i.i.1 = trunc i128 %add4.i.i594.i.i.1 to i64
  store i64 %conv5.i.i595.i.i.1, ptr %arrayidx.i.i591.i.i.1
  %shr.i.i596.i.i.1 = lshr i128 %add4.i.i594.i.i.1, 64
  %indvars.iv.next.i.i597.i.i.1 = or i64 %indvars.iv.i.i589.i.i, 2
  %arrayidx.i.i591.i.i.2 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i597.i.i.1
  %113 = load i64, ptr %arrayidx.i.i591.i.i.2
  %conv2.i.i592.i.i.2 = zext i64 %113 to i128
  %mul.i.i593.i.i.2 = mul i128 %conv2.i.i592.i.i.2, 10000000000000000000
  %add4.i.i594.i.i.2 = add i128 %mul.i.i593.i.i.2, %shr.i.i596.i.i.1
  %conv5.i.i595.i.i.2 = trunc i128 %add4.i.i594.i.i.2 to i64
  store i64 %conv5.i.i595.i.i.2, ptr %arrayidx.i.i591.i.i.2
  %shr.i.i596.i.i.2 = lshr i128 %add4.i.i594.i.i.2, 64
  %indvars.iv.next.i.i597.i.i.2 = or i64 %indvars.iv.i.i589.i.i, 3
  %arrayidx.i.i591.i.i.3 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i597.i.i.2
  %114 = load i64, ptr %arrayidx.i.i591.i.i.3
  %conv2.i.i592.i.i.3 = zext i64 %114 to i128
  %mul.i.i593.i.i.3 = mul i128 %conv2.i.i592.i.i.3, 10000000000000000000
  %add4.i.i594.i.i.3 = add i128 %mul.i.i593.i.i.3, %shr.i.i596.i.i.2
  %conv5.i.i595.i.i.3 = trunc i128 %add4.i.i594.i.i.3 to i64
  store i64 %conv5.i.i595.i.i.3, ptr %arrayidx.i.i591.i.i.3
  %shr.i.i596.i.i.3 = lshr i128 %add4.i.i594.i.i.3, 64
  %indvars.iv.next.i.i597.i.i.3 = add i64 %indvars.iv.i.i589.i.i, 4
  %niter1075.next.3 = add i64 %niter1075, 4
  %niter1075.ncmp.3 = icmp eq i64 %niter1075.next.3, %unroll_iter1074
  br i1 %niter1075.ncmp.3, label %while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit, label %for.body.i.i588.i.i

stk_mul_u64.exit605.i.i:                          ; preds = %while.body.us.i.i601.i.i, %while.cond.preheader.i.i599.i.i, %while.body187.i.i
  %115 = phi i32 [ %108, %while.body187.i.i ], [ %108, %while.cond.preheader.i.i599.i.i ], [ %inc12.us.i.i603.i.i, %while.body.us.i.i601.i.i ]
  %sub189.i.i = add i64 %k183.0754.i.i, -19
  %cmp185.i.i = icmp sgt i64 %k183.0754.i.i, 37
  br i1 %cmp185.i.i, label %while.body187.i.i, label %while.end190.i.i

while.end190.i.i:                                 ; preds = %stk_mul_u64.exit605.i.i, %while.cond184.preheader.i.i
  %116 = phi i32 [ %n.i.promoted751.i.i, %while.cond184.preheader.i.i ], [ %115, %stk_mul_u64.exit605.i.i ]
  %k183.0.lcssa.i.i = phi i64 [ %add108.i.i, %while.cond184.preheader.i.i ], [ %sub189.i.i, %stk_mul_u64.exit605.i.i ]
  store i32 %116, ptr %n.i.i.i
  %tobool191.not.i.i = icmp ne i64 %k183.0.lcssa.i.i, 0
  %cmp28.i.i607.i.i = icmp sgt i32 %116, 0
  %or.cond865.i.i = select i1 %tobool191.not.i.i, i1 %cmp28.i.i607.i.i, i1 false
  br i1 %or.cond865.i.i, label %for.body.lr.ph.i.i608.i.i, label %if.end195.i.i

for.body.lr.ph.i.i608.i.i:                        ; preds = %while.end190.i.i
  %arrayidx194.i.i = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %k183.0.lcssa.i.i
  %117 = load i64, ptr %arrayidx194.i.i
  %conv3.i.i609.i.i = zext i64 %117 to i128
  %wide.trip.count.i.i610.i.i = zext i32 %116 to i64
  %xtraiter1076 = and i64 %wide.trip.count.i.i610.i.i, 3
  %118 = icmp ult i32 %116, 4
  br i1 %118, label %while.cond.preheader.i.i622.i.i.unr-lcssa, label %for.body.lr.ph.i.i608.i.i.new

for.body.lr.ph.i.i608.i.i.new:                    ; preds = %for.body.lr.ph.i.i608.i.i
  %unroll_iter1081 = and i64 %wide.trip.count.i.i610.i.i, 2147483644
  br label %for.body.i.i611.i.i

while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit: ; preds = %for.body.i.i611.i.i
  %extract.t1097 = trunc i128 %shr.i.i619.i.i.3 to i64
  br label %while.cond.preheader.i.i622.i.i.unr-lcssa

while.cond.preheader.i.i622.i.i.unr-lcssa:        ; preds = %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit, %for.body.lr.ph.i.i608.i.i
  %add4.i.i617.i.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i.i608.i.i ], [ %add4.i.i617.i.i.3, %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit ]
  %shr.i.i619.i.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i.i608.i.i ], [ %extract.t1097, %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit ]
  %indvars.iv.i.i612.i.i.unr = phi i64 [ 0, %for.body.lr.ph.i.i608.i.i ], [ %indvars.iv.next.i.i620.i.i.3, %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit ]
  %carry.029.i.i613.i.i.unr = phi i128 [ 0, %for.body.lr.ph.i.i608.i.i ], [ %shr.i.i619.i.i.3, %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit ]
  %lcmp.mod1078.not = icmp eq i64 %xtraiter1076, 0
  br i1 %lcmp.mod1078.not, label %while.cond.preheader.i.i622.i.i, label %for.body.i.i611.i.i.epil

for.body.i.i611.i.i.epil:                         ; preds = %for.body.i.i611.i.i.epil, %while.cond.preheader.i.i622.i.i.unr-lcssa
  %indvars.iv.i.i612.i.i.epil = phi i64 [ %indvars.iv.next.i.i620.i.i.epil, %for.body.i.i611.i.i.epil ], [ %indvars.iv.i.i612.i.i.unr, %while.cond.preheader.i.i622.i.i.unr-lcssa ]
  %carry.029.i.i613.i.i.epil = phi i128 [ %shr.i.i619.i.i.epil, %for.body.i.i611.i.i.epil ], [ %carry.029.i.i613.i.i.unr, %while.cond.preheader.i.i622.i.i.unr-lcssa ]
  %epil.iter1077 = phi i64 [ %epil.iter1077.next, %for.body.i.i611.i.i.epil ], [ 0, %while.cond.preheader.i.i622.i.i.unr-lcssa ]
  %arrayidx.i.i614.i.i.epil = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i612.i.i.epil
  %119 = load i64, ptr %arrayidx.i.i614.i.i.epil
  %conv2.i.i615.i.i.epil = zext i64 %119 to i128
  %mul.i.i616.i.i.epil = mul i128 %conv2.i.i615.i.i.epil, %conv3.i.i609.i.i
  %add4.i.i617.i.i.epil = add i128 %mul.i.i616.i.i.epil, %carry.029.i.i613.i.i.epil
  %conv5.i.i618.i.i.epil = trunc i128 %add4.i.i617.i.i.epil to i64
  store i64 %conv5.i.i618.i.i.epil, ptr %arrayidx.i.i614.i.i.epil
  %shr.i.i619.i.i.epil = lshr i128 %add4.i.i617.i.i.epil, 64
  %indvars.iv.next.i.i620.i.i.epil = add i64 %indvars.iv.i.i612.i.i.epil, 1
  %epil.iter1077.next = add i64 %epil.iter1077, 1
  %epil.iter1077.cmp.not = icmp eq i64 %epil.iter1077.next, %xtraiter1076
  br i1 %epil.iter1077.cmp.not, label %while.cond.preheader.i.i622.i.i.epilog-lcssa, label %for.body.i.i611.i.i.epil

while.cond.preheader.i.i622.i.i.epilog-lcssa:     ; preds = %for.body.i.i611.i.i.epil
  %extract.t1096 = trunc i128 %shr.i.i619.i.i.epil to i64
  br label %while.cond.preheader.i.i622.i.i

while.cond.preheader.i.i622.i.i:                  ; preds = %while.cond.preheader.i.i622.i.i.epilog-lcssa, %while.cond.preheader.i.i622.i.i.unr-lcssa
  %add4.i.i617.i.i.lcssa = phi i128 [ %add4.i.i617.i.i.lcssa.ph, %while.cond.preheader.i.i622.i.i.unr-lcssa ], [ %add4.i.i617.i.i.epil, %while.cond.preheader.i.i622.i.i.epilog-lcssa ]
  %shr.i.i619.i.i.lcssa.off0 = phi i64 [ %shr.i.i619.i.i.lcssa.ph.off0, %while.cond.preheader.i.i622.i.i.unr-lcssa ], [ %extract.t1096, %while.cond.preheader.i.i622.i.i.epilog-lcssa ]
  %tobool.not31.i.i623.i.i = icmp ult i128 %add4.i.i617.i.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i.i623.i.i, label %if.end195.i.i, label %while.body.us.i.i624.i.i

while.body.us.i.i624.i.i:                         ; preds = %while.cond.preheader.i.i622.i.i
  %inc12.us.i.i626.i.i = add i32 %116, 1
  %arrayidx14.us.i.i627.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %wide.trip.count.i.i610.i.i
  store i64 %shr.i.i619.i.i.lcssa.off0, ptr %arrayidx14.us.i.i627.i.i
  store i32 %inc12.us.i.i626.i.i, ptr %n.i.i.i
  br label %if.end195.i.i

for.body.i.i611.i.i:                              ; preds = %for.body.i.i611.i.i, %for.body.lr.ph.i.i608.i.i.new
  %indvars.iv.i.i612.i.i = phi i64 [ 0, %for.body.lr.ph.i.i608.i.i.new ], [ %indvars.iv.next.i.i620.i.i.3, %for.body.i.i611.i.i ]
  %carry.029.i.i613.i.i = phi i128 [ 0, %for.body.lr.ph.i.i608.i.i.new ], [ %shr.i.i619.i.i.3, %for.body.i.i611.i.i ]
  %niter1082 = phi i64 [ 0, %for.body.lr.ph.i.i608.i.i.new ], [ %niter1082.next.3, %for.body.i.i611.i.i ]
  %arrayidx.i.i614.i.i = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.i.i612.i.i
  %120 = load i64, ptr %arrayidx.i.i614.i.i
  %conv2.i.i615.i.i = zext i64 %120 to i128
  %mul.i.i616.i.i = mul i128 %conv2.i.i615.i.i, %conv3.i.i609.i.i
  %add4.i.i617.i.i = add i128 %mul.i.i616.i.i, %carry.029.i.i613.i.i
  %conv5.i.i618.i.i = trunc i128 %add4.i.i617.i.i to i64
  store i64 %conv5.i.i618.i.i, ptr %arrayidx.i.i614.i.i
  %shr.i.i619.i.i = lshr i128 %add4.i.i617.i.i, 64
  %indvars.iv.next.i.i620.i.i = or i64 %indvars.iv.i.i612.i.i, 1
  %arrayidx.i.i614.i.i.1 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i620.i.i
  %121 = load i64, ptr %arrayidx.i.i614.i.i.1
  %conv2.i.i615.i.i.1 = zext i64 %121 to i128
  %mul.i.i616.i.i.1 = mul i128 %conv2.i.i615.i.i.1, %conv3.i.i609.i.i
  %add4.i.i617.i.i.1 = add i128 %mul.i.i616.i.i.1, %shr.i.i619.i.i
  %conv5.i.i618.i.i.1 = trunc i128 %add4.i.i617.i.i.1 to i64
  store i64 %conv5.i.i618.i.i.1, ptr %arrayidx.i.i614.i.i.1
  %shr.i.i619.i.i.1 = lshr i128 %add4.i.i617.i.i.1, 64
  %indvars.iv.next.i.i620.i.i.1 = or i64 %indvars.iv.i.i612.i.i, 2
  %arrayidx.i.i614.i.i.2 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i620.i.i.1
  %122 = load i64, ptr %arrayidx.i.i614.i.i.2
  %conv2.i.i615.i.i.2 = zext i64 %122 to i128
  %mul.i.i616.i.i.2 = mul i128 %conv2.i.i615.i.i.2, %conv3.i.i609.i.i
  %add4.i.i617.i.i.2 = add i128 %mul.i.i616.i.i.2, %shr.i.i619.i.i.1
  %conv5.i.i618.i.i.2 = trunc i128 %add4.i.i617.i.i.2 to i64
  store i64 %conv5.i.i618.i.i.2, ptr %arrayidx.i.i614.i.i.2
  %shr.i.i619.i.i.2 = lshr i128 %add4.i.i617.i.i.2, 64
  %indvars.iv.next.i.i620.i.i.2 = or i64 %indvars.iv.i.i612.i.i, 3
  %arrayidx.i.i614.i.i.3 = getelementptr inbounds [96 x i64], ptr %v.i.i, i64 0, i64 %indvars.iv.next.i.i620.i.i.2
  %123 = load i64, ptr %arrayidx.i.i614.i.i.3
  %conv2.i.i615.i.i.3 = zext i64 %123 to i128
  %mul.i.i616.i.i.3 = mul i128 %conv2.i.i615.i.i.3, %conv3.i.i609.i.i
  %add4.i.i617.i.i.3 = add i128 %mul.i.i616.i.i.3, %shr.i.i619.i.i.2
  %conv5.i.i618.i.i.3 = trunc i128 %add4.i.i617.i.i.3 to i64
  store i64 %conv5.i.i618.i.i.3, ptr %arrayidx.i.i614.i.i.3
  %shr.i.i619.i.i.3 = lshr i128 %add4.i.i617.i.i.3, 64
  %indvars.iv.next.i.i620.i.i.3 = add i64 %indvars.iv.i.i612.i.i, 4
  %niter1082.next.3 = add i64 %niter1082, 4
  %niter1082.ncmp.3 = icmp eq i64 %niter1082.next.3, %unroll_iter1081
  br i1 %niter1082.ncmp.3, label %while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit, label %for.body.i.i611.i.i

if.end195.i.i:                                    ; preds = %while.body.us.i.i624.i.i, %while.cond.preheader.i.i622.i.i, %while.end190.i.i
  store i64 0, ptr %S128.i.i
  br label %if.end198.i.i

if.end198.i.i:                                    ; preds = %if.end195.i.i, %if.then178.i.i, %while.end176.i.i, %while.body.us.i.i557.i.i, %while.cond.preheader.i.i555.i.i, %while.end.thread.i.i, %while.end.i.i
  %reass.sub = sub i64 %add110.i.i, %topn.0711.i.i
  %sub200.i.i = add i64 %reass.sub, 1
  %conv202.i.i = uitofp i64 %top.0709.i.i to double
  br label %while.cond203.i.i

while.cond203.i.i:                                ; preds = %while.body206.i.i, %if.end198.i.i
  %e10.0.i.i = phi i64 [ %sub200.i.i, %if.end198.i.i ], [ %sub219.i.i, %while.body206.i.i ]
  %d201.0.i.i = phi double [ %conv202.i.i, %if.end198.i.i ], [ %mul217.i.i, %while.body206.i.i ]
  %cmp204.i.i = icmp sgt i64 %e10.0.i.i, 0
  br i1 %cmp204.i.i, label %while.body206.i.i, label %while.cond229.i.i.preheader

while.body206.i.i:                                ; preds = %while.cond203.i.i
  %124.min = icmp ult i64 %e10.0.i.i, 22
  %124 = select i1 %124.min, i64 %e10.0.i.i, i64 22
  %arrayidx216.i.i = getelementptr inbounds [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %124
  %125 = load double, ptr %arrayidx216.i.i
  %mul217.i.i = fmul double %d201.0.i.i, %125
  %sub219.i.i = sub i64 %e10.0.i.i, %124
  %.cast.i.i.i = bitcast double %mul217.i.i to i64
  %cmp221.i.i = icmp ugt i64 %.cast.i.i.i, 9218868437227405311
  br i1 %cmp221.i.i, label %while.cond229.i.i.preheader, label %while.cond203.i.i

while.cond229.i.i.preheader:                      ; preds = %while.body206.i.i, %while.cond203.i.i
  %e10.2.i.i.ph = phi i64 [ %e10.0.i.i, %while.cond203.i.i ], [ %sub219.i.i, %while.body206.i.i ]
  %d201.2.i.i.ph = phi double [ %d201.0.i.i, %while.cond203.i.i ], [ %mul217.i.i, %while.body206.i.i ]
  br label %while.cond229.i.i

while.cond229.i.i:                                ; preds = %while.body232.i.i, %while.cond229.i.i.preheader
  %e10.2.i.i = phi i64 [ %add245.i.i, %while.body232.i.i ], [ %e10.2.i.i.ph, %while.cond229.i.i.preheader ]
  %d201.2.i.i = phi double [ %div.i.i, %while.body232.i.i ], [ %d201.2.i.i.ph, %while.cond229.i.i.preheader ]
  %cmp230.i.i = icmp slt i64 %e10.2.i.i, 0
  br i1 %cmp230.i.i, label %while.body232.i.i, label %while.end253.i.i

while.body232.i.i:                                ; preds = %while.cond229.i.i
  %cmp234.i.i = icmp samesign ult i64 %e10.2.i.i, -22
  %.neg.i.i = mul i64 %e10.2.i.i, -4294967296
  %126 = ashr i64 %.neg.i.i, 32
  %idxprom242.i.i = select i1 %cmp234.i.i, i64 22, i64 %126
  %arrayidx243.i.i = getelementptr inbounds [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %idxprom242.i.i
  %127 = load double, ptr %arrayidx243.i.i
  %div.i.i = fdiv double %d201.2.i.i, %127
  %add245.i.i = add i64 %idxprom242.i.i, %e10.2.i.i
  %cmp246.i.i = fcmp oeq double %div.i.i, 0.000000e+00
  br i1 %cmp246.i.i, label %while.end253.i.i, label %while.cond229.i.i

while.end253.i.i:                                 ; preds = %while.body232.i.i, %while.cond229.i.i
  %d201.3.i.i = phi double [ %div.i.i, %while.body232.i.i ], [ %d201.2.i.i, %while.cond229.i.i ]
  %.cast.i629.i.i = bitcast double %d201.3.i.i to i64
  br label %for.cond255.i.i

for.cond255.i.i:                                  ; preds = %for.cond255.i.i.backedge, %while.end253.i.i
  %b.0.i.i = phi i64 [ %.cast.i629.i.i, %while.end253.i.i ], [ %b.0.i.i.be, %for.cond255.i.i.backedge ]
  %cmp256.i.i = icmp eq i64 %b.0.i.i, 0
  br i1 %cmp256.i.i, label %if.then258.i.i, label %if.end264.i.i

if.then258.i.i:                                   ; preds = %for.cond255.i.i
  %call259.i.i = call i32 @stk_cmp(ptr %v.i.i, i64 1, i64 -1075)
  %cmp260.i.i = icmp sgt i32 %call259.i.i, 0
  br i1 %cmp260.i.i, label %for.cond255.i.i.backedge, label %for.end359.i.i

if.end264.i.i:                                    ; preds = %for.cond255.i.i
  %cmp265.i.i = icmp ugt i64 %b.0.i.i, 9218868437227405311
  br i1 %cmp265.i.i, label %if.then267.i.i, label %if.end273.i.i

if.then267.i.i:                                   ; preds = %if.end264.i.i
  %call268.i.i = call i32 @stk_cmp(ptr %v.i.i, i64 18014398509481983, i64 970)
  %cmp269.i.i = icmp slt i32 %call268.i.i, 0
  br i1 %cmp269.i.i, label %for.cond255.i.i.backedge, label %for.end359.i.i

if.end273.i.i:                                    ; preds = %if.end264.i.i
  %shr.i.i = lshr i64 %b.0.i.i, 52
  %cmp275.i.i = icmp samesign ult i64 %b.0.i.i, 4503599627370496
  %and280.i.i = and i64 %b.0.i.i, 4503599627370495
  %or.i.i = or i64 %and280.i.i, 4503599627370496
  %cond282.i.i = select i1 %cmp275.i.i, i64 %b.0.i.i, i64 %or.i.i
  %sub288.i.i = add i64 %shr.i.i, -1075
  %cond290.i.i = select i1 %cmp275.i.i, i64 -1074, i64 %sub288.i.i
  %call291.i.i = call i32 @stk_cmp(ptr %v.i.i, i64 %cond282.i.i, i64 %cond290.i.i)
  %cmp292.i.i = icmp eq i32 %call291.i.i, 0
  br i1 %cmp292.i.i, label %for.end359.i.i, label %if.end295.i.i

if.end295.i.i:                                    ; preds = %if.end273.i.i
  %cmp296.i.i = icmp sgt i32 %call291.i.i, 0
  br i1 %cmp296.i.i, label %if.then298.i.i, label %if.end318.i.i

if.then298.i.i:                                   ; preds = %if.end295.i.i
  %mul299.i.i = shl i64 %cond282.i.i, 1
  %add300.i.i = or i64 %mul299.i.i, 1
  %sub301.i.i = add i64 %cond290.i.i, -1
  %call302.i.i = call i32 @stk_cmp(ptr %v.i.i, i64 %add300.i.i, i64 %sub301.i.i)
  %cmp303.i.i = icmp slt i32 %call302.i.i, 0
  br i1 %cmp303.i.i, label %for.end359.i.i, label %if.end306.i.i

if.end306.i.i:                                    ; preds = %if.then298.i.i
  %cmp307.i.i = icmp eq i32 %call302.i.i, 0
  br i1 %cmp307.i.i, label %if.then309.i.i, label %if.end315.i.i

if.then309.i.i:                                   ; preds = %if.end306.i.i
  %and310.i.i = and i64 %cond282.i.i, 1
  %spec.select507.i.i = add i64 %and310.i.i, %b.0.i.i
  br label %for.end359.i.i

if.end315.i.i:                                    ; preds = %if.end306.i.i
  %inc316.i.i = add i64 %b.0.i.i, 1
  br label %for.cond255.i.i.backedge

if.end318.i.i:                                    ; preds = %if.end295.i.i
  %cmp322.i.i = icmp samesign ugt i64 %cond282.i.i, 4503599627370496
  %or.cond391.i.i = or i1 %cmp275.i.i, %cmp322.i.i
  br i1 %or.cond391.i.i, label %if.then324.i.i, label %if.else328.i.i

if.then324.i.i:                                   ; preds = %if.end318.i.i
  %mul325.i.i = shl i64 %cond282.i.i, 1
  %sub326.i.i = add i64 %mul325.i.i, -1
  %sub327.i.i = add i64 %cond290.i.i, -1
  br label %if.end335.i.i

if.else328.i.i:                                   ; preds = %if.end318.i.i
  %cmp329.i.i = icmp eq i64 %shr.i.i, 1
  %sub333.i.i = add i64 %shr.i.i, -1077
  %spec.select511.i.i = select i1 %cmp329.i.i, i64 9007199254740991, i64 18014398509481983
  %spec.select512.i.i = select i1 %cmp329.i.i, i64 -1075, i64 %sub333.i.i
  br label %if.end335.i.i

if.end335.i.i:                                    ; preds = %if.else328.i.i, %if.then324.i.i
  %J.0.i.i = phi i64 [ %sub326.i.i, %if.then324.i.i ], [ %spec.select511.i.i, %if.else328.i.i ]
  %eB.0.i.i = phi i64 [ %sub327.i.i, %if.then324.i.i ], [ %spec.select512.i.i, %if.else328.i.i ]
  %call336.i.i = call i32 @stk_cmp(ptr %v.i.i, i64 %J.0.i.i, i64 %eB.0.i.i)
  %cmp337.i.i = icmp sgt i32 %call336.i.i, 0
  br i1 %cmp337.i.i, label %for.end359.i.i, label %if.end340.i.i

if.end340.i.i:                                    ; preds = %if.end335.i.i
  %cmp341.i.i = icmp eq i32 %call336.i.i, 0
  br i1 %cmp341.i.i, label %if.then343.i.i, label %if.end348.i.i

if.then343.i.i:                                   ; preds = %if.end340.i.i
  %128 = and i64 %cond282.i.i, 1
  %spec.select508.i.i = sub i64 %b.0.i.i, %128
  br label %for.end359.i.i

if.end348.i.i:                                    ; preds = %if.end340.i.i
  %dec349.i.i = add i64 %b.0.i.i, -1
  br label %for.cond255.i.i.backedge

for.cond255.i.i.backedge:                         ; preds = %if.end348.i.i, %if.end315.i.i, %if.then267.i.i, %if.then258.i.i
  %b.0.i.i.be = phi i64 [ 1, %if.then258.i.i ], [ 9218868437227405311, %if.then267.i.i ], [ %inc316.i.i, %if.end315.i.i ], [ %dec349.i.i, %if.end348.i.i ]
  br label %for.cond255.i.i

for.end359.i.i:                                   ; preds = %if.then343.i.i, %if.end335.i.i, %if.then309.i.i, %if.then298.i.i, %if.end273.i.i, %if.then267.i.i, %if.then258.i.i
  %b.6.i.i = phi i64 [ %spec.select508.i.i, %if.then343.i.i ], [ %spec.select507.i.i, %if.then309.i.i ], [ %b.0.i.i, %if.end273.i.i ], [ %b.0.i.i, %if.then298.i.i ], [ %b.0.i.i, %if.end335.i.i ], [ 9218868437227405312, %if.then267.i.i ], [ 0, %if.then258.i.i ]
  %.cast.i630.i.i = bitcast i64 %b.6.i.i to double
  %fneg363.i.i = fneg double %.cast.i630.i.i
  %cond366.i.i = select i1 %cmp1.i, double %fneg363.i.i, double %.cast.i630.i.i
  call void @llvm.lifetime.end.p0(i64 1568, ptr %v.i.i)
  br label %if.end291

if.end291:                                        ; preds = %for.end359.i.i, %if.then123.i.i, %if.then113.i.i, %if.then59.i.i
  %retval.1.i.i = phi double [ %cond.i.i, %if.then59.i.i ], [ %cond125.i.i, %if.then123.i.i ], [ %cond366.i.i, %for.end359.i.i ], [ %spec.select694.i.i, %if.then113.i.i ]
  call void @llvm.lifetime.end.p0(i64 768, ptr %dig.i.i)
  store double %retval.1.i.i, ptr %out
  br label %cleanup300

cleanup300:                                       ; preds = %if.end291, %if.then141.i, %if.then119.i, %if.then58.i, %if.else35.i, %if.then5.i, %cleanup282, %cleanup282.thread, %if.then229, %cleanup223, %if.then89, %if.else66, %if.then5
  %retval.8 = phi i32 [ 0, %if.then5 ], [ 0, %if.then89 ], [ 0, %if.else66 ], [ 0, %if.then229 ], [ 0, %cleanup223 ], [ 1, %cleanup282 ], [ 1, %cleanup282.thread ], [ 1, %if.end291 ], [ 0, %if.then5.i ], [ 0, %if.then58.i ], [ 0, %if.then119.i ], [ 0, %if.then141.i ], [ 0, %if.else35.i ]
  ret i32 %retval.8
}
