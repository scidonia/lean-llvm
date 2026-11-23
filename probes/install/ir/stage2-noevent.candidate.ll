; The no-event stage-2 entry as emitted, in the fragment `LeanLLVM.Semantics` models.
; Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-noevent.sh
;
; from kernel/json/stage2_noevent.c with kernel/json/stage2.c included under
; its entry rename, emitted at the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names \
;         -fno-slp-vectorize \
;         <the merged source with `noinline` on every helper>
;
; -fno-slp-vectorize is not the measured line: at the measured line clang packs
; the two independent 64-bit counters into <2 x i64>, which changes no value but
; puts vector types in the body.  With the flag the body carries none, which the
; residual check enforces.
;
; then `opt -passes=lower-switch`, then reduced to the one `define` block.
;
; The entry carries no attribute, so it is the body; every helper carries
; `noinline` instead of `always_inline`, so its text stays out of this block.
; The scalar literal compare is body text: the entry packs the literal into an
; integer and compares bytes, because the fragment has no module-global
; representation and the certified `lit_check` takes a `const char *`.
; The literal comparison is `ne_lit`, which packs the literal into an integer.
; That its verdict and offset equal the certified `lit_check`'s is the
; refinement obligation stated over this pinned body and exercised by the
; differential, not a fact of this fixture.
;
; The function's parameters are the twelve-slot ABI in order, followed by the
; four local objects the fragment cannot allocate (see
; stage2-noevent.staging.tsv): %stk, %c, %e, %d.
; The four scalar allocas (%xj, %outn, %outn205, %ei) stay in the body, at the
; types the pin records.
;
; Removed before the parser sees the text, each item with its class in
; stage2-noevent.strip.tsv, and each rewrite in stage2-noevent.rewrites.tsv.
; The entry's guards -- both scratch-capacity checks, their two trap arms, the
; refusal arms' zero stores and the acceptance stores -- are body text and are
; kept.
;
; The inventory of this fixture's opcodes and call targets is
; stage2-noevent.inventory. `opt -passes=verify` accepts it and `leanllvm`
; parses it, both checked by the capture.

define i64 @leanllvm_json_stage2_noevent(ptr %b, i64 %n, ptr %ep, i64 %nep, ptr %xp, i64 %nxp, ptr %scratch, i64 %scratchcap, ptr %tokens_out, ptr %values_out, ptr %sum_out, ptr %err, ptr %stk, ptr %e, ptr %c, ptr %d) {
entry:
  %xj = alloca i64
  %outn = alloca i64
  %outn205 = alloca i64
  %ei = alloca i64
  call void @llvm.lifetime.start.p0(i64 8, ptr %xj)
  store i64 0, ptr %xj
  call void @llvm.lifetime.start.p0(i64 520, ptr %stk)
  call void @llvm.lifetime.start.p0(i64 24, ptr %e)
  call void @llvm.lifetime.start.p0(i64 1192, ptr %c)
  store i32 1, ptr %e
  %off = getelementptr inbounds i8, ptr %e, i64 8
  store i64 0, ptr %off
  %msg = getelementptr inbounds i8, ptr %e, i64 16
  store ptr null, ptr %msg
  %0 = getelementptr inbounds i8, ptr %c, i64 32
  call void @llvm.memset.p0.i64(ptr %0, i8 0, i64 1160, i1 false)
  store ptr %b, ptr %c
  %n2 = getelementptr inbounds i8, ptr %c, i64 8
  store i64 %n, ptr %n2
  %ix = getelementptr inbounds i8, ptr %c, i64 16
  store ptr %ep, ptr %ix
  %nix = getelementptr inbounds i8, ptr %c, i64 24
  store i64 %nep, ptr %nix
  %e3 = getelementptr inbounds i8, ptr %c, i64 1112
  store ptr %e, ptr %e3
  %invariant.gep = getelementptr inbounds i8, ptr %b, i64 1
  %invariant.gep1068 = getelementptr i8, ptr %b, i64 -1
  %k219 = getelementptr inbounds i8, ptr %c, i64 32
  %cmp.not.peel1401.not = icmp eq i64 %nep, 0
  br i1 %cmp.not.peel1401.not, label %if.then, label %if.end.peel.preheader

if.end.peel.preheader:                            ; preds = %entry
  %invariant.gep1650 = getelementptr i8, ptr %scratch, i64 1
  %invariant.gep1652 = getelementptr i8, ptr %scratch, i64 2
  %invariant.gep1654 = getelementptr i8, ptr %scratch, i64 3
  %invariant.gep1656 = getelementptr i8, ptr %scratch, i64 4
  %invariant.gep1658 = getelementptr i8, ptr %scratch, i64 5
  %invariant.gep1660 = getelementptr i8, ptr %scratch, i64 6
  %invariant.gep1662 = getelementptr i8, ptr %scratch, i64 7
  %invariant.gep1664 = getelementptr i8, ptr %scratch, i64 1
  %invariant.gep1666 = getelementptr i8, ptr %scratch, i64 2
  %invariant.gep1668 = getelementptr i8, ptr %scratch, i64 3
  %invariant.gep1670 = getelementptr i8, ptr %scratch, i64 4
  %invariant.gep1672 = getelementptr i8, ptr %scratch, i64 5
  %invariant.gep1674 = getelementptr i8, ptr %scratch, i64 6
  %invariant.gep1676 = getelementptr i8, ptr %scratch, i64 7
  br label %if.end.peel

if.end.peel:                                      ; preds = %value.outer.backedge, %if.end.peel.preheader
  %wide.trip.count1409 = phi i64 [ %wide.trip.count, %value.outer.backedge ], [ 520, %if.end.peel.preheader ]
  %1 = phi i64 [ %45, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %tokens.0.ph1408 = phi i64 [ %tokens.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %terms.0.ph1407 = phi i64 [ %terms.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %arena.0.ph1406 = phi i64 [ %arena.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %alen.0.ph1405 = phi i64 [ %alen.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %k.0.ph1404 = phi i64 [ %k.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %sp.0.ph1403 = phi i32 [ %sp.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %frame.0.ph1402 = phi i8 [ %frame.0.ph.be, %value.outer.backedge ], [ 0, %if.end.peel.preheader ]
  %inc.peel = add i64 %k.0.ph1404, 1
  %arrayidx.peel = getelementptr inbounds i32, ptr %ep, i64 %k.0.ph1404
  %2 = load i32, ptr %arrayidx.peel
  %idxprom.peel = zext i32 %2 to i64
  %arrayidx6.peel = getelementptr inbounds i8, ptr %b, i64 %idxprom.peel
  %3 = load i8, ptr %arrayidx6.peel
  br label %NodeBlock5

NodeBlock5:                                       ; preds = %if.end.peel
  %Pivot6 = icmp slt i8 %3, 91
  br i1 %Pivot6, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock5
  %Pivot = icmp slt i8 %3, 123
  br i1 %Pivot, label %LeafBlock1, label %LeafBlock3

LeafBlock3:                                       ; preds = %NodeBlock
  %SwitchLeaf4 = icmp eq i8 %3, 123
  br i1 %SwitchLeaf4, label %if.then9, label %scalar

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i8 %3, 91
  br i1 %SwitchLeaf2, label %if.then35.peel, label %scalar

LeafBlock:                                        ; preds = %NodeBlock5
  %SwitchLeaf = icmp eq i8 %3, 34
  br i1 %SwitchLeaf, label %string_value, label %scalar

if.then35.peel:                                   ; preds = %LeafBlock1
  %exitcond.peel = icmp ugt i32 %sp.0.ph1403, 519
  br i1 %exitcond.peel, label %if.then38, label %if.end45.peel

if.end45.peel:                                    ; preds = %if.then35.peel
  %tobool46.not.peel = icmp eq i32 %sp.0.ph1403, 0
  br i1 %tobool46.not.peel, label %if.end51.peel, label %if.then47.peel

if.then47.peel:                                   ; preds = %if.end45.peel
  %4 = add i64 %1, -1
  %arrayidx50.peel = getelementptr inbounds i8, ptr %stk, i64 %4
  store i8 %frame.0.ph1402, ptr %arrayidx50.peel
  br label %if.end51.peel

if.end51.peel:                                    ; preds = %if.then47.peel, %if.end45.peel
  %cmp319.not.peel = icmp ult i64 %inc.peel, %nep
  br i1 %cmp319.not.peel, label %if.end327.peel, label %if.then321

if.end327.peel:                                   ; preds = %if.end51.peel
  %arrayidx328.peel = getelementptr inbounds i32, ptr %ep, i64 %inc.peel
  %5 = load i32, ptr %arrayidx328.peel
  %idxprom329.peel = zext i32 %5 to i64
  %arrayidx330.peel = getelementptr inbounds i8, ptr %b, i64 %idxprom329.peel
  %6 = load i8, ptr %arrayidx330.peel
  %cmp332.peel = icmp eq i8 %6, 93
  br i1 %cmp332.peel, label %if.then334, label %if.end

if.then:                                          ; preds = %value.outer.backedge, %entry
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end:                                           ; preds = %if.end327, %if.end327.peel
  %7 = phi i8 [ %47, %if.end327 ], [ %6, %if.end327.peel ]
  %8 = phi i32 [ %46, %if.end327 ], [ %5, %if.end327.peel ]
  %indvars.iv.in = phi i64 [ %indvars.iv, %if.end327 ], [ %1, %if.end327.peel ]
  %k.0 = phi i64 [ %inc, %if.end327 ], [ %inc.peel, %if.end327.peel ]
  %terms.0.in = phi i64 [ %terms.0, %if.end327 ], [ %terms.0.ph1407, %if.end327.peel ]
  %tokens.0.in = phi i64 [ %tokens.0, %if.end327 ], [ %tokens.0.ph1408, %if.end327.peel ]
  %tokens.0 = add i64 %tokens.0.in, 1
  %terms.0 = add i64 %terms.0.in, 3
  %indvars.iv = add i64 %indvars.iv.in, 1
  %inc = add i64 %k.0, 1
  br label %NodeBlock15

NodeBlock15:                                      ; preds = %if.end
  %Pivot16 = icmp slt i8 %7, 91
  br i1 %Pivot16, label %LeafBlock7, label %NodeBlock13

NodeBlock13:                                      ; preds = %NodeBlock15
  %Pivot14 = icmp slt i8 %7, 123
  br i1 %Pivot14, label %LeafBlock9, label %LeafBlock11

LeafBlock11:                                      ; preds = %NodeBlock13
  %SwitchLeaf12 = icmp eq i8 %7, 123
  br i1 %SwitchLeaf12, label %if.then9.loopexit, label %scalar.loopexit

LeafBlock9:                                       ; preds = %NodeBlock13
  %SwitchLeaf10 = icmp eq i8 %7, 91
  br i1 %SwitchLeaf10, label %if.then35, label %scalar.loopexit

LeafBlock7:                                       ; preds = %NodeBlock15
  %SwitchLeaf8 = icmp eq i8 %7, 34
  br i1 %SwitchLeaf8, label %string_value.loopexit, label %scalar.loopexit

if.then9.loopexit:                                ; preds = %LeafBlock11
  %idxprom.le1289 = zext i32 %8 to i64
  %9 = trunc i64 %indvars.iv to i32
  br label %if.then9

if.then9:                                         ; preds = %LeafBlock3, %if.then9.loopexit
  %inc.lcssa1129 = phi i64 [ %inc.peel, %LeafBlock3 ], [ %inc, %if.then9.loopexit ]
  %idxprom.lcssa1108 = phi i64 [ %idxprom.peel, %LeafBlock3 ], [ %idxprom.le1289, %if.then9.loopexit ]
  %frame.0.lcssa1098 = phi i8 [ %frame.0.ph1402, %LeafBlock3 ], [ 1, %if.then9.loopexit ]
  %sp.0.lcssa1092.wide = phi i32 [ %sp.0.ph1403, %LeafBlock3 ], [ %9, %if.then9.loopexit ]
  %k.0.lcssa1086 = phi i64 [ %k.0.ph1404, %LeafBlock3 ], [ %k.0, %if.then9.loopexit ]
  %terms.0.lcssa1080 = phi i64 [ %terms.0.ph1407, %LeafBlock3 ], [ %terms.0, %if.then9.loopexit ]
  %tokens.0.lcssa1074 = phi i64 [ %tokens.0.ph1408, %LeafBlock3 ], [ %tokens.0, %if.then9.loopexit ]
  %cmp10 = icmp ugt i32 %sp.0.lcssa1092.wide, 519
  br i1 %cmp10, label %if.then12, label %if.end19

if.then12:                                        ; preds = %if.then9
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom.lcssa1108, ptr %err
  br label %cleanup580

if.end19:                                         ; preds = %if.then9
  %tobool.not = icmp eq i32 %sp.0.lcssa1092.wide, 0
  br i1 %tobool.not, label %if.end23, label %if.then20

if.then20:                                        ; preds = %if.end19
  %sub = add i32 %sp.0.lcssa1092.wide, -1
  %idxprom21 = zext i32 %sub to i64
  %arrayidx22 = getelementptr inbounds i8, ptr %stk, i64 %idxprom21
  store i8 %frame.0.lcssa1098, ptr %arrayidx22
  br label %if.end23

if.end23:                                         ; preds = %if.then20, %if.end19
  %inc24 = add i32 %sp.0.lcssa1092.wide, 1
  %cmp66.not = icmp ult i64 %inc.lcssa1129, %nep
  br i1 %cmp66.not, label %if.end74, label %if.then68

if.then35:                                        ; preds = %LeafBlock9
  %exitcond = icmp eq i64 %indvars.iv, %wide.trip.count1409
  br i1 %exitcond, label %if.then38.loopexit, label %if.end51

if.then38.loopexit:                               ; preds = %if.then35
  %idxprom.le = zext i32 %8 to i64
  br label %if.then38

if.then38:                                        ; preds = %if.then38.loopexit, %if.then35.peel
  %idxprom.lcssa1110 = phi i64 [ %idxprom.le, %if.then38.loopexit ], [ %idxprom.peel, %if.then35.peel ]
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom.lcssa1110, ptr %err
  br label %cleanup580

if.end51:                                         ; preds = %if.then35
  %arrayidx50 = getelementptr inbounds i8, ptr %stk, i64 %indvars.iv.in
  store i8 1, ptr %arrayidx50
  %cmp319.not = icmp ult i64 %inc, %nep
  br i1 %cmp319.not, label %if.end327, label %if.then321

if.then68:                                        ; preds = %if.end23
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end74:                                         ; preds = %if.end23
  %add = add i64 %terms.0.lcssa1080, 1
  %inc26 = add i64 %tokens.0.lcssa1074, 1
  %arrayidx75 = getelementptr inbounds i32, ptr %ep, i64 %inc.lcssa1129
  %10 = load i32, ptr %arrayidx75
  %idxprom76 = zext i32 %10 to i64
  %arrayidx77 = getelementptr inbounds i8, ptr %b, i64 %idxprom76
  %11 = load i8, ptr %arrayidx77
  br label %NodeBlock21

NodeBlock21:                                      ; preds = %if.end74
  %Pivot22 = icmp slt i8 %11, 125
  br i1 %Pivot22, label %LeafBlock17, label %LeafBlock19

LeafBlock19:                                      ; preds = %NodeBlock21
  %SwitchLeaf20 = icmp eq i8 %11, 125
  br i1 %SwitchLeaf20, label %if.then81, label %if.then94

LeafBlock17:                                      ; preds = %NodeBlock21
  %SwitchLeaf18 = icmp eq i8 %11, 34
  br i1 %SwitchLeaf18, label %key_body, label %if.then94

if.then81:                                        ; preds = %LeafBlock19
  %inc82 = add i64 %k.0.lcssa1086, 2
  %inc84 = add i64 %tokens.0.lcssa1074, 2
  %add85 = add i64 %terms.0.lcssa1080, 3
  br label %close_obj

if.then94:                                        ; preds = %LeafBlock19, %LeafBlock17
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom76, ptr %err
  br label %cleanup580

if.then105:                                       ; preds = %if.end409
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end111:                                        ; preds = %if.end409
  %arrayidx112 = getelementptr inbounds i32, ptr %ep, i64 %inc379
  %12 = load i32, ptr %arrayidx112
  %idxprom113 = zext i32 %12 to i64
  %arrayidx114 = getelementptr inbounds i8, ptr %b, i64 %idxprom113
  %13 = load i8, ptr %arrayidx114
  %cmp116.not = icmp eq i8 %13, 34
  br i1 %cmp116.not, label %key_body, label %if.then118

if.then118:                                       ; preds = %if.end111
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom113, ptr %err
  br label %cleanup580

key_body:                                         ; preds = %LeafBlock17, %if.end111
  %p.0 = phi i32 [ %10, %LeafBlock17 ], [ %12, %if.end111 ]
  %sp.1 = phi i32 [ %inc24, %LeafBlock17 ], [ %sp.4, %if.end111 ]
  %k.1.in = phi i64 [ %k.0.lcssa1086, %LeafBlock17 ], [ %k.6, %if.end111 ]
  %alen.1 = phi i64 [ %alen.0.ph1405, %LeafBlock17 ], [ %alen.8, %if.end111 ]
  %arena.1 = phi i64 [ %arena.0.ph1406, %LeafBlock17 ], [ %arena.10, %if.end111 ]
  %terms.1 = phi i64 [ %add, %LeafBlock17 ], [ %terms.8, %if.end111 ]
  %tokens.1 = phi i64 [ %inc26, %LeafBlock17 ], [ %tokens.8, %if.end111 ]
  %k.1 = add i64 %k.1.in, 2
  call void @llvm.lifetime.start.p0(i64 8, ptr %outn)
  %cmp127.not = icmp ult i64 %k.1, %nep
  br i1 %cmp127.not, label %if.end136, label %if.then129

if.then129:                                       ; preds = %key_body
  %conv130 = zext i32 %p.0 to i64
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  br label %cleanup.thread

if.end136:                                        ; preds = %key_body
  %inc137 = add i64 %k.1.in, 3
  %arrayidx138 = getelementptr inbounds i32, ptr %ep, i64 %k.1
  %14 = load i32, ptr %arrayidx138
  store i64 %inc137, ptr %k219
  %conv140 = zext i32 %14 to i64
  %cmp141.not = icmp ugt i64 %n, %conv140
  %conv152 = zext i32 %p.0 to i64
  br i1 %cmp141.not, label %if.end150, label %if.then143

if.then143:                                       ; preds = %if.end136
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  br label %cleanup.thread

if.end150:                                        ; preds = %if.end136
  %15 = xor i64 %conv152, -1
  %sub154 = add i64 %conv140, %15
  %add155 = add i64 %sub154, 64
  %cmp156 = icmp ugt i64 %add155, %scratchcap
  br i1 %cmp156, label %if.then158, label %if.end159

if.then158:                                       ; preds = %if.end150
  call void @llvm.trap()
  unreachable

if.end159:                                        ; preds = %if.end150
  store i64 0, ptr %outn
  %gep1071 = getelementptr inbounds i8, ptr %invariant.gep, i64 %conv152
  %call161 = call i32 @s2_string_body(ptr %c, ptr %gep1071, i64 %sub154, ptr %scratch, ptr %outn, ptr %xp, ptr %xj, i64 %nxp)
  br label %NodeBlock25

NodeBlock25:                                      ; preds = %if.end159
  %Pivot26 = icmp slt i32 %call161, 1
  br i1 %Pivot26, label %do.body164, label %LeafBlock23

LeafBlock23:                                      ; preds = %NodeBlock25
  %SwitchLeaf24 = icmp eq i32 %call161, 1
  br i1 %SwitchLeaf24, label %do.body172, label %for.cond.preheader

for.cond.preheader:                               ; preds = %LeafBlock23
  %16 = load i64, ptr %outn
  %cmp1811063.not = icmp eq i64 %16, 0
  br i1 %cmp1811063.not, label %for.cond.cleanup, label %for.body.preheader

for.body.preheader:                               ; preds = %for.cond.preheader
  %xtraiter1529 = and i64 %16, 7
  %17 = icmp ult i64 %16, 8
  br i1 %17, label %for.cond.cleanup.loopexit.unr-lcssa, label %for.body.preheader.new

for.body.preheader.new:                           ; preds = %for.body.preheader
  %unroll_iter1533 = and i64 %16, -8
  br label %for.body

do.body164:                                       ; preds = %NodeBlock25
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  %18 = load i64, ptr %off
  br label %cleanup.thread

do.body172:                                       ; preds = %LeafBlock23
  %add175 = add i32 %p.0, 1
  %conv176 = zext i32 %add175 to i64
  %or = add i64 %conv176, -9223372036854775803
  %add177 = add i64 %or, %sub154
  br label %expect_colon

for.cond.cleanup.loopexit.unr-lcssa:              ; preds = %for.body, %for.body.preheader
  %add185.lcssa.ph = phi i64 [ poison, %for.body.preheader ], [ %add185.7, %for.body ]
  %arena.21065.unr = phi i64 [ %arena.1, %for.body.preheader ], [ %add185.7, %for.body ]
  %i.01064.unr = phi i64 [ 0, %for.body.preheader ], [ %inc186.7, %for.body ]
  %lcmp.mod1531.not = icmp eq i64 %xtraiter1529, 0
  br i1 %lcmp.mod1531.not, label %for.cond.cleanup, label %for.body.epil

for.body.epil:                                    ; preds = %for.body.epil, %for.cond.cleanup.loopexit.unr-lcssa
  %arena.21065.epil = phi i64 [ %add185.epil, %for.body.epil ], [ %arena.21065.unr, %for.cond.cleanup.loopexit.unr-lcssa ]
  %i.01064.epil = phi i64 [ %inc186.epil, %for.body.epil ], [ %i.01064.unr, %for.cond.cleanup.loopexit.unr-lcssa ]
  %epil.iter1530 = phi i64 [ %epil.iter1530.next, %for.body.epil ], [ 0, %for.cond.cleanup.loopexit.unr-lcssa ]
  %arrayidx183.epil = getelementptr inbounds i8, ptr %scratch, i64 %i.01064.epil
  %19 = load i8, ptr %arrayidx183.epil
  %conv184.epil = zext i8 %19 to i64
  %add185.epil = add i64 %arena.21065.epil, %conv184.epil
  %inc186.epil = add i64 %i.01064.epil, 1
  %epil.iter1530.next = add i64 %epil.iter1530, 1
  %epil.iter1530.cmp.not = icmp eq i64 %epil.iter1530.next, %xtraiter1529
  br i1 %epil.iter1530.cmp.not, label %for.cond.cleanup, label %for.body.epil

for.cond.cleanup:                                 ; preds = %for.body.epil, %for.cond.cleanup.loopexit.unr-lcssa, %for.cond.preheader
  %arena.2.lcssa = phi i64 [ %arena.1, %for.cond.preheader ], [ %add185.lcssa.ph, %for.cond.cleanup.loopexit.unr-lcssa ], [ %add185.epil, %for.body.epil ]
  %add187 = add i64 %16, %alen.1
  %add190 = add i64 %alen.1, 5
  %add191 = add i64 %add190, %16
  br label %expect_colon

for.body:                                         ; preds = %for.body, %for.body.preheader.new
  %arena.21065 = phi i64 [ %arena.1, %for.body.preheader.new ], [ %add185.7, %for.body ]
  %i.01064 = phi i64 [ 0, %for.body.preheader.new ], [ %inc186.7, %for.body ]
  %niter1534 = phi i64 [ 0, %for.body.preheader.new ], [ %niter1534.next.7, %for.body ]
  %arrayidx183 = getelementptr inbounds i8, ptr %scratch, i64 %i.01064
  %20 = load i8, ptr %arrayidx183
  %conv184 = zext i8 %20 to i64
  %add185 = add i64 %arena.21065, %conv184
  %gep1665 = getelementptr i8, ptr %invariant.gep1664, i64 %i.01064
  %21 = load i8, ptr %gep1665
  %conv184.1 = zext i8 %21 to i64
  %add185.1 = add i64 %add185, %conv184.1
  %gep1667 = getelementptr i8, ptr %invariant.gep1666, i64 %i.01064
  %22 = load i8, ptr %gep1667
  %conv184.2 = zext i8 %22 to i64
  %add185.2 = add i64 %add185.1, %conv184.2
  %gep1669 = getelementptr i8, ptr %invariant.gep1668, i64 %i.01064
  %23 = load i8, ptr %gep1669
  %conv184.3 = zext i8 %23 to i64
  %add185.3 = add i64 %add185.2, %conv184.3
  %gep1671 = getelementptr i8, ptr %invariant.gep1670, i64 %i.01064
  %24 = load i8, ptr %gep1671
  %conv184.4 = zext i8 %24 to i64
  %add185.4 = add i64 %add185.3, %conv184.4
  %gep1673 = getelementptr i8, ptr %invariant.gep1672, i64 %i.01064
  %25 = load i8, ptr %gep1673
  %conv184.5 = zext i8 %25 to i64
  %add185.5 = add i64 %add185.4, %conv184.5
  %gep1675 = getelementptr i8, ptr %invariant.gep1674, i64 %i.01064
  %26 = load i8, ptr %gep1675
  %conv184.6 = zext i8 %26 to i64
  %add185.6 = add i64 %add185.5, %conv184.6
  %gep1677 = getelementptr i8, ptr %invariant.gep1676, i64 %i.01064
  %27 = load i8, ptr %gep1677
  %conv184.7 = zext i8 %27 to i64
  %add185.7 = add i64 %add185.6, %conv184.7
  %inc186.7 = add i64 %i.01064, 8
  %niter1534.next.7 = add i64 %niter1534, 8
  %niter1534.ncmp.7 = icmp eq i64 %niter1534.next.7, %unroll_iter1533
  br i1 %niter1534.ncmp.7, label %for.cond.cleanup.loopexit.unr-lcssa, label %for.body

cleanup.thread:                                   ; preds = %do.body164, %if.then143, %if.then129
  %conv130.sink = phi i64 [ %conv130, %if.then129 ], [ %conv152, %if.then143 ], [ %18, %do.body164 ]
  store i64 %conv130.sink, ptr %err
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn)
  br label %cleanup580

string_value.loopexit:                            ; preds = %LeafBlock7
  %idxprom.le1287 = zext i32 %8 to i64
  %28 = trunc i64 %indvars.iv to i32
  br label %string_value

string_value:                                     ; preds = %LeafBlock, %string_value.loopexit
  %inc.lcssa1130 = phi i64 [ %inc.peel, %LeafBlock ], [ %inc, %string_value.loopexit ]
  %.lcssa1125 = phi i32 [ %2, %LeafBlock ], [ %8, %string_value.loopexit ]
  %idxprom.lcssa1109 = phi i64 [ %idxprom.peel, %LeafBlock ], [ %idxprom.le1287, %string_value.loopexit ]
  %frame.0.lcssa1099 = phi i8 [ %frame.0.ph1402, %LeafBlock ], [ 1, %string_value.loopexit ]
  %sp.0.lcssa1093.wide = phi i32 [ %sp.0.ph1403, %LeafBlock ], [ %28, %string_value.loopexit ]
  %k.0.lcssa1087 = phi i64 [ %k.0.ph1404, %LeafBlock ], [ %k.0, %string_value.loopexit ]
  %terms.0.lcssa1081 = phi i64 [ %terms.0.ph1407, %LeafBlock ], [ %terms.0, %string_value.loopexit ]
  %tokens.0.lcssa1075 = phi i64 [ %tokens.0.ph1408, %LeafBlock ], [ %tokens.0, %string_value.loopexit ]
  call void @llvm.lifetime.start.p0(i64 8, ptr %outn205)
  %cmp207.not = icmp ult i64 %inc.lcssa1130, %nep
  br i1 %cmp207.not, label %if.end216, label %if.then209

if.then209:                                       ; preds = %string_value
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  br label %cleanup287.thread

if.end216:                                        ; preds = %string_value
  %inc217 = add i64 %k.0.lcssa1087, 2
  %arrayidx218 = getelementptr inbounds i32, ptr %ep, i64 %inc.lcssa1130
  %29 = load i32, ptr %arrayidx218
  store i64 %inc217, ptr %k219
  %conv220 = zext i32 %29 to i64
  %cmp221.not = icmp ugt i64 %n, %conv220
  br i1 %cmp221.not, label %if.end230, label %if.then223

if.then223:                                       ; preds = %if.end216
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  br label %cleanup287.thread

if.end230:                                        ; preds = %if.end216
  %30 = xor i64 %idxprom.lcssa1109, -1
  %sub234 = add i64 %conv220, %30
  %add235 = add i64 %sub234, 64
  %cmp236 = icmp ugt i64 %add235, %scratchcap
  br i1 %cmp236, label %if.then238, label %if.end239

if.then238:                                       ; preds = %if.end230
  call void @llvm.trap()
  unreachable

if.end239:                                        ; preds = %if.end230
  store i64 0, ptr %outn205
  %gep = getelementptr inbounds i8, ptr %invariant.gep, i64 %idxprom.lcssa1109
  %call243 = call i32 @s2_string_body(ptr %c, ptr %gep, i64 %sub234, ptr %scratch, ptr %outn205, ptr %xp, ptr %xj, i64 %nxp)
  br label %NodeBlock29

NodeBlock29:                                      ; preds = %if.end239
  %Pivot30 = icmp slt i32 %call243, 1
  br i1 %Pivot30, label %do.body246, label %LeafBlock27

LeafBlock27:                                      ; preds = %NodeBlock29
  %SwitchLeaf28 = icmp eq i32 %call243, 1
  br i1 %SwitchLeaf28, label %do.body254, label %for.cond266.preheader

for.cond266.preheader:                            ; preds = %LeafBlock27
  %31 = load i64, ptr %outn205
  %cmp2671048.not = icmp eq i64 %31, 0
  br i1 %cmp2671048.not, label %for.cond.cleanup269, label %for.body270.preheader

for.body270.preheader:                            ; preds = %for.cond266.preheader
  %xtraiter = and i64 %31, 7
  %32 = icmp ult i64 %31, 8
  br i1 %32, label %for.cond.cleanup269.loopexit.unr-lcssa, label %for.body270.preheader.new

for.body270.preheader.new:                        ; preds = %for.body270.preheader
  %unroll_iter = and i64 %31, -8
  br label %for.body270

do.body246:                                       ; preds = %NodeBlock29
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  %33 = load i64, ptr %off
  br label %cleanup287.thread

do.body254:                                       ; preds = %LeafBlock27
  %add257 = add i32 %.lcssa1125, 1
  %conv258 = zext i32 %add257 to i64
  %or259 = add i64 %conv258, -9223372036854775802
  %add260 = add i64 %or259, %sub234
  br label %cleanup287

for.cond.cleanup269.loopexit.unr-lcssa:           ; preds = %for.body270, %for.body270.preheader
  %add273.lcssa.ph = phi i64 [ poison, %for.body270.preheader ], [ %add273.7, %for.body270 ]
  %i265.01050.unr = phi i64 [ 0, %for.body270.preheader ], [ %inc275.7, %for.body270 ]
  %arena.51049.unr = phi i64 [ %arena.0.ph1406, %for.body270.preheader ], [ %add273.7, %for.body270 ]
  %lcmp.mod.not = icmp eq i64 %xtraiter, 0
  br i1 %lcmp.mod.not, label %for.cond.cleanup269, label %for.body270.epil

for.body270.epil:                                 ; preds = %for.body270.epil, %for.cond.cleanup269.loopexit.unr-lcssa
  %i265.01050.epil = phi i64 [ %inc275.epil, %for.body270.epil ], [ %i265.01050.unr, %for.cond.cleanup269.loopexit.unr-lcssa ]
  %arena.51049.epil = phi i64 [ %add273.epil, %for.body270.epil ], [ %arena.51049.unr, %for.cond.cleanup269.loopexit.unr-lcssa ]
  %epil.iter = phi i64 [ %epil.iter.next, %for.body270.epil ], [ 0, %for.cond.cleanup269.loopexit.unr-lcssa ]
  %arrayidx271.epil = getelementptr inbounds i8, ptr %scratch, i64 %i265.01050.epil
  %34 = load i8, ptr %arrayidx271.epil
  %conv272.epil = zext i8 %34 to i64
  %add273.epil = add i64 %arena.51049.epil, %conv272.epil
  %inc275.epil = add i64 %i265.01050.epil, 1
  %epil.iter.next = add i64 %epil.iter, 1
  %epil.iter.cmp.not = icmp eq i64 %epil.iter.next, %xtraiter
  br i1 %epil.iter.cmp.not, label %for.cond.cleanup269, label %for.body270.epil

for.cond.cleanup269:                              ; preds = %for.body270.epil, %for.cond.cleanup269.loopexit.unr-lcssa, %for.cond266.preheader
  %arena.5.lcssa = phi i64 [ %arena.0.ph1406, %for.cond266.preheader ], [ %add273.lcssa.ph, %for.cond.cleanup269.loopexit.unr-lcssa ], [ %add273.epil, %for.body270.epil ]
  %add278 = add i64 %31, %alen.0.ph1405
  %add281 = add i64 %alen.0.ph1405, 6
  %add282 = add i64 %add281, %31
  br label %cleanup287

for.body270:                                      ; preds = %for.body270, %for.body270.preheader.new
  %i265.01050 = phi i64 [ 0, %for.body270.preheader.new ], [ %inc275.7, %for.body270 ]
  %arena.51049 = phi i64 [ %arena.0.ph1406, %for.body270.preheader.new ], [ %add273.7, %for.body270 ]
  %niter = phi i64 [ 0, %for.body270.preheader.new ], [ %niter.next.7, %for.body270 ]
  %arrayidx271 = getelementptr inbounds i8, ptr %scratch, i64 %i265.01050
  %35 = load i8, ptr %arrayidx271
  %conv272 = zext i8 %35 to i64
  %add273 = add i64 %arena.51049, %conv272
  %gep1651 = getelementptr i8, ptr %invariant.gep1650, i64 %i265.01050
  %36 = load i8, ptr %gep1651
  %conv272.1 = zext i8 %36 to i64
  %add273.1 = add i64 %add273, %conv272.1
  %gep1653 = getelementptr i8, ptr %invariant.gep1652, i64 %i265.01050
  %37 = load i8, ptr %gep1653
  %conv272.2 = zext i8 %37 to i64
  %add273.2 = add i64 %add273.1, %conv272.2
  %gep1655 = getelementptr i8, ptr %invariant.gep1654, i64 %i265.01050
  %38 = load i8, ptr %gep1655
  %conv272.3 = zext i8 %38 to i64
  %add273.3 = add i64 %add273.2, %conv272.3
  %gep1657 = getelementptr i8, ptr %invariant.gep1656, i64 %i265.01050
  %39 = load i8, ptr %gep1657
  %conv272.4 = zext i8 %39 to i64
  %add273.4 = add i64 %add273.3, %conv272.4
  %gep1659 = getelementptr i8, ptr %invariant.gep1658, i64 %i265.01050
  %40 = load i8, ptr %gep1659
  %conv272.5 = zext i8 %40 to i64
  %add273.5 = add i64 %add273.4, %conv272.5
  %gep1661 = getelementptr i8, ptr %invariant.gep1660, i64 %i265.01050
  %41 = load i8, ptr %gep1661
  %conv272.6 = zext i8 %41 to i64
  %add273.6 = add i64 %add273.5, %conv272.6
  %gep1663 = getelementptr i8, ptr %invariant.gep1662, i64 %i265.01050
  %42 = load i8, ptr %gep1663
  %conv272.7 = zext i8 %42 to i64
  %add273.7 = add i64 %add273.6, %conv272.7
  %inc275.7 = add i64 %i265.01050, 8
  %niter.next.7 = add i64 %niter, 8
  %niter.ncmp.7 = icmp eq i64 %niter.next.7, %unroll_iter
  br i1 %niter.ncmp.7, label %for.cond.cleanup269.loopexit.unr-lcssa, label %for.body270

cleanup287.thread:                                ; preds = %do.body246, %if.then223, %if.then209
  %idxprom.lcssa1109.lcssa.sink = phi i64 [ %idxprom.lcssa1109, %if.then209 ], [ %idxprom.lcssa1109, %if.then223 ], [ %33, %do.body246 ]
  store i64 %idxprom.lcssa1109.lcssa.sink, ptr %err
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn205)
  br label %cleanup580

cleanup287:                                       ; preds = %for.cond.cleanup269, %do.body254
  %alen.4 = phi i64 [ %alen.0.ph1405, %do.body254 ], [ %add278, %for.cond.cleanup269 ]
  %arena.6 = phi i64 [ %arena.0.ph1406, %do.body254 ], [ %arena.5.lcssa, %for.cond.cleanup269 ]
  %add260.pn = phi i64 [ %add260, %do.body254 ], [ %add282, %for.cond.cleanup269 ]
  %tokens.4 = add i64 %tokens.0.lcssa1075, 1
  %terms.4 = add i64 %add260.pn, %terms.0.lcssa1081
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn205)
  br label %after_value

expect_colon:                                     ; preds = %for.cond.cleanup, %do.body172
  %alen.2 = phi i64 [ %alen.1, %do.body172 ], [ %add187, %for.cond.cleanup ]
  %arena.3 = phi i64 [ %arena.1, %do.body172 ], [ %arena.2.lcssa, %for.cond.cleanup ]
  %add177.pn = phi i64 [ %add177, %do.body172 ], [ %add191, %for.cond.cleanup ]
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn)
  %cmp295.not = icmp ult i64 %inc137, %nep
  br i1 %cmp295.not, label %if.end303, label %if.then297

if.then297:                                       ; preds = %expect_colon
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end303:                                        ; preds = %expect_colon
  %terms.2 = add i64 %add177.pn, %terms.1
  %tokens.2 = add i64 %tokens.1, 1
  %inc304 = add i64 %k.1.in, 4
  %arrayidx305 = getelementptr inbounds i32, ptr %ep, i64 %inc137
  %43 = load i32, ptr %arrayidx305
  %idxprom306 = zext i32 %43 to i64
  %arrayidx307 = getelementptr inbounds i8, ptr %b, i64 %idxprom306
  %44 = load i8, ptr %arrayidx307
  %cmp309.not = icmp eq i8 %44, 58
  br i1 %cmp309.not, label %value.outer.backedge, label %if.then311

value.outer.backedge:                             ; preds = %LeafBlock37, %if.end303
  %frame.0.ph.be = phi i8 [ %frame.6, %LeafBlock37 ], [ 0, %if.end303 ]
  %sp.0.ph.be = phi i32 [ %sp.4, %LeafBlock37 ], [ %sp.1, %if.end303 ]
  %k.0.ph.be = phi i64 [ %inc379, %LeafBlock37 ], [ %inc304, %if.end303 ]
  %alen.0.ph.be = phi i64 [ %alen.8, %LeafBlock37 ], [ %alen.2, %if.end303 ]
  %arena.0.ph.be = phi i64 [ %arena.10, %LeafBlock37 ], [ %arena.3, %if.end303 ]
  %terms.0.ph.be = phi i64 [ %terms.8, %LeafBlock37 ], [ %terms.2, %if.end303 ]
  %tokens.0.ph.be = phi i64 [ %tokens.8, %LeafBlock37 ], [ %tokens.2, %if.end303 ]
  %45 = zext i32 %sp.0.ph.be to i64
  %umax.max = icmp ugt i32 %sp.0.ph.be, 520
  %umax = select i1 %umax.max, i32 %sp.0.ph.be, i32 520
  %wide.trip.count = zext i32 %umax to i64
  %cmp.not.peel = icmp ult i64 %k.0.ph.be, %nep
  br i1 %cmp.not.peel, label %if.end.peel, label %if.then

if.then311:                                       ; preds = %if.end303
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom306, ptr %err
  br label %cleanup580

if.then321:                                       ; preds = %if.end51, %if.end51.peel
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end327:                                        ; preds = %if.end51
  %arrayidx328 = getelementptr inbounds i32, ptr %ep, i64 %inc
  %46 = load i32, ptr %arrayidx328
  %idxprom329 = zext i32 %46 to i64
  %arrayidx330 = getelementptr inbounds i8, ptr %b, i64 %idxprom329
  %47 = load i8, ptr %arrayidx330
  %cmp332 = icmp eq i8 %47, 93
  br i1 %cmp332, label %if.then334.loopexit, label %if.end

if.then334.loopexit:                              ; preds = %if.end327
  %48 = trunc i64 %indvars.iv to i32
  br label %if.then334

if.then334:                                       ; preds = %if.then334.loopexit, %if.end327.peel
  %sp.0.lcssa1096.wide = phi i32 [ %sp.0.ph1403, %if.end327.peel ], [ %48, %if.then334.loopexit ]
  %k.0.lcssa1090 = phi i64 [ %k.0.ph1404, %if.end327.peel ], [ %k.0, %if.then334.loopexit ]
  %terms.0.lcssa1084 = phi i64 [ %terms.0.ph1407, %if.end327.peel ], [ %terms.0, %if.then334.loopexit ]
  %tokens.0.lcssa1078 = phi i64 [ %tokens.0.ph1408, %if.end327.peel ], [ %tokens.0, %if.then334.loopexit ]
  %inc335 = add i64 %k.0.lcssa1090, 2
  %inc337 = add i64 %tokens.0.lcssa1078, 2
  %add338 = add i64 %terms.0.lcssa1084, 7
  br label %close_arr

close_obj:                                        ; preds = %do.body391, %if.then81
  %sp.2 = phi i32 [ %inc24, %if.then81 ], [ %sp.4, %do.body391 ]
  %k.4 = phi i64 [ %inc82, %if.then81 ], [ %inc379, %do.body391 ]
  %alen.6 = phi i64 [ %alen.0.ph1405, %if.then81 ], [ %alen.8, %do.body391 ]
  %arena.8 = phi i64 [ %arena.0.ph1406, %if.then81 ], [ %arena.10, %do.body391 ]
  %terms.6 = phi i64 [ %add85, %if.then81 ], [ %add393, %do.body391 ]
  %tokens.6 = phi i64 [ %inc84, %if.then81 ], [ %inc392, %do.body391 ]
  %dec = add i32 %sp.2, -1
  %tobool342.not = icmp eq i32 %dec, 0
  br i1 %tobool342.not, label %after_value, label %if.then343

if.then343:                                       ; preds = %close_obj
  %sub344 = add i32 %sp.2, -2
  %idxprom345 = zext i32 %sub344 to i64
  %arrayidx346 = getelementptr inbounds i8, ptr %stk, i64 %idxprom345
  %49 = load i8, ptr %arrayidx346
  br label %after_value

close_arr:                                        ; preds = %do.body417, %if.then334
  %frame.4 = phi i8 [ %frame.6, %do.body417 ], [ 1, %if.then334 ]
  %sp.3 = phi i32 [ %54, %do.body417 ], [ %sp.0.lcssa1096.wide, %if.then334 ]
  %k.5 = phi i64 [ %inc379, %do.body417 ], [ %inc335, %if.then334 ]
  %alen.7 = phi i64 [ %alen.8, %do.body417 ], [ %alen.0.ph1405, %if.then334 ]
  %arena.9 = phi i64 [ %arena.10, %do.body417 ], [ %arena.0.ph1406, %if.then334 ]
  %terms.7 = phi i64 [ %add419, %do.body417 ], [ %add338, %if.then334 ]
  %tokens.7 = phi i64 [ %inc418, %do.body417 ], [ %inc337, %if.then334 ]
  %tobool349.not = icmp eq i32 %sp.3, 0
  br i1 %tobool349.not, label %after_value, label %if.then350

if.then350:                                       ; preds = %close_arr
  %sub351 = add i32 %sp.3, -1
  %idxprom352 = zext i32 %sub351 to i64
  %arrayidx353 = getelementptr inbounds i8, ptr %stk, i64 %idxprom352
  %50 = load i8, ptr %arrayidx353
  br label %after_value

after_value:                                      ; preds = %while.body557, %if.end545, %if.then350, %close_arr, %if.then343, %close_obj, %cleanup287
  %frame.6 = phi i8 [ %frame.0.lcssa1099, %cleanup287 ], [ %49, %if.then343 ], [ 0, %close_obj ], [ %50, %if.then350 ], [ %frame.4, %close_arr ], [ %frame.0.lcssa1097, %if.end545 ], [ %frame.0.lcssa1097, %while.body557 ]
  %sp.4 = phi i32 [ %sp.0.lcssa1093.wide, %cleanup287 ], [ %dec, %if.then343 ], [ %dec, %close_obj ], [ %sp.3, %if.then350 ], [ %sp.3, %close_arr ], [ %sp.0.lcssa1091.wide, %if.end545 ], [ %sp.0.lcssa1091.wide, %while.body557 ]
  %k.6 = phi i64 [ %inc217, %cleanup287 ], [ %k.4, %if.then343 ], [ %k.4, %close_obj ], [ %k.5, %if.then350 ], [ %k.5, %close_arr ], [ %inc.lcssa, %if.end545 ], [ %inc.lcssa, %while.body557 ]
  %alen.8 = phi i64 [ %alen.4, %cleanup287 ], [ %alen.6, %if.then343 ], [ %alen.6, %close_obj ], [ %alen.7, %if.then350 ], [ %alen.7, %close_arr ], [ %alen.0.ph1405, %if.end545 ], [ %alen.0.ph1405, %while.body557 ]
  %arena.10 = phi i64 [ %arena.6, %cleanup287 ], [ %arena.8, %if.then343 ], [ %arena.8, %close_obj ], [ %arena.9, %if.then350 ], [ %arena.9, %close_arr ], [ %arena.0.ph1406, %if.end545 ], [ %arena.0.ph1406, %while.body557 ]
  %terms.8 = phi i64 [ %terms.4, %cleanup287 ], [ %terms.6, %if.then343 ], [ %terms.6, %close_obj ], [ %terms.7, %if.then350 ], [ %terms.7, %close_arr ], [ %terms.12, %if.end545 ], [ %terms.12, %while.body557 ]
  %tokens.8 = phi i64 [ %tokens.4, %cleanup287 ], [ %tokens.6, %if.then343 ], [ %tokens.6, %close_obj ], [ %tokens.7, %if.then350 ], [ %tokens.7, %close_arr ], [ %tokens.12, %if.end545 ], [ %tokens.12, %while.body557 ]
  %cmp355 = icmp eq i32 %sp.4, 0
  %cmp358 = icmp ult i64 %k.6, %nep
  br i1 %cmp355, label %if.then357, label %if.end369

if.then357:                                       ; preds = %after_value
  br i1 %cmp358, label %if.then360, label %accept

if.then360:                                       ; preds = %if.then357
  %arrayidx361 = getelementptr inbounds i32, ptr %ep, i64 %k.6
  %51 = load i32, ptr %arrayidx361
  %conv362 = zext i32 %51 to i64
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %conv362, ptr %err
  br label %cleanup580

if.end369:                                        ; preds = %after_value
  br i1 %cmp358, label %if.end378, label %if.then372

if.then372:                                       ; preds = %if.end369
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %n, ptr %err
  br label %cleanup580

if.end378:                                        ; preds = %if.end369
  %inc379 = add i64 %k.6, 1
  %arrayidx380 = getelementptr inbounds i32, ptr %ep, i64 %k.6
  %52 = load i32, ptr %arrayidx380
  %cmp382 = icmp eq i8 %frame.6, 0
  %idxprom385 = zext i32 %52 to i64
  %arrayidx386 = getelementptr inbounds i8, ptr %b, i64 %idxprom385
  %53 = load i8, ptr %arrayidx386
  br i1 %cmp382, label %if.then384, label %if.end410

if.then384:                                       ; preds = %if.end378
  br label %NodeBlock35

NodeBlock35:                                      ; preds = %if.then384
  %Pivot36 = icmp slt i8 %53, 125
  br i1 %Pivot36, label %LeafBlock31, label %LeafBlock33

LeafBlock33:                                      ; preds = %NodeBlock35
  %SwitchLeaf34 = icmp eq i8 %53, 125
  br i1 %SwitchLeaf34, label %do.body391, label %if.then402

LeafBlock31:                                      ; preds = %NodeBlock35
  %SwitchLeaf32 = icmp eq i8 %53, 44
  br i1 %SwitchLeaf32, label %if.end409, label %if.then402

do.body391:                                       ; preds = %LeafBlock33
  %inc392 = add i64 %tokens.8, 1
  %add393 = add i64 %terms.8, 2
  br label %close_obj

if.then402:                                       ; preds = %LeafBlock33, %LeafBlock31
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom385, ptr %err
  br label %cleanup580

if.end409:                                        ; preds = %LeafBlock31
  %cmp103.not = icmp ult i64 %inc379, %nep
  br i1 %cmp103.not, label %if.end111, label %if.then105

if.end410:                                        ; preds = %if.end378
  br label %NodeBlock41

NodeBlock41:                                      ; preds = %if.end410
  %Pivot42 = icmp slt i8 %53, 93
  br i1 %Pivot42, label %LeafBlock37, label %LeafBlock39

LeafBlock39:                                      ; preds = %NodeBlock41
  %SwitchLeaf40 = icmp eq i8 %53, 93
  br i1 %SwitchLeaf40, label %do.body417, label %if.then428

LeafBlock37:                                      ; preds = %NodeBlock41
  %SwitchLeaf38 = icmp eq i8 %53, 44
  br i1 %SwitchLeaf38, label %value.outer.backedge, label %if.then428

do.body417:                                       ; preds = %LeafBlock39
  %inc418 = add i64 %tokens.8, 1
  %add419 = add i64 %terms.8, 4
  %54 = add i32 %sp.4, -1
  br label %close_arr

if.then428:                                       ; preds = %LeafBlock39, %LeafBlock37
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %idxprom385, ptr %err
  br label %cleanup580

scalar.loopexit:                                  ; preds = %LeafBlock11, %LeafBlock9, %LeafBlock7
  %idxprom.le1291 = zext i32 %8 to i64
  %55 = trunc i64 %indvars.iv to i32
  br label %scalar

scalar:                                           ; preds = %LeafBlock3, %LeafBlock1, %LeafBlock, %scalar.loopexit
  %inc.lcssa = phi i64 [ %inc, %scalar.loopexit ], [ %inc.peel, %LeafBlock ], [ %inc.peel, %LeafBlock1 ], [ %inc.peel, %LeafBlock3 ]
  %idxprom.lcssa = phi i64 [ %idxprom.le1291, %scalar.loopexit ], [ %idxprom.peel, %LeafBlock ], [ %idxprom.peel, %LeafBlock1 ], [ %idxprom.peel, %LeafBlock3 ]
  %.lcssa = phi i8 [ %7, %scalar.loopexit ], [ %3, %LeafBlock ], [ %3, %LeafBlock1 ], [ %3, %LeafBlock3 ]
  %frame.0.lcssa1097 = phi i8 [ 1, %scalar.loopexit ], [ %frame.0.ph1402, %LeafBlock ], [ %frame.0.ph1402, %LeafBlock1 ], [ %frame.0.ph1402, %LeafBlock3 ]
  %sp.0.lcssa1091.wide = phi i32 [ %55, %scalar.loopexit ], [ %sp.0.ph1403, %LeafBlock ], [ %sp.0.ph1403, %LeafBlock1 ], [ %sp.0.ph1403, %LeafBlock3 ]
  %terms.0.lcssa1079 = phi i64 [ %terms.0, %scalar.loopexit ], [ %terms.0.ph1407, %LeafBlock ], [ %terms.0.ph1407, %LeafBlock1 ], [ %terms.0.ph1407, %LeafBlock3 ]
  %tokens.0.lcssa1073 = phi i64 [ %tokens.0, %scalar.loopexit ], [ %tokens.0.ph1408, %LeafBlock ], [ %tokens.0.ph1408, %LeafBlock1 ], [ %tokens.0.ph1408, %LeafBlock3 ]
  %arrayidx6.le1046 = getelementptr inbounds i8, ptr %b, i64 %idxprom.lcssa
  %cmp436 = icmp ult i64 %inc.lcssa, %nep
  br i1 %cmp436, label %cond.true, label %cond.end

cond.true:                                        ; preds = %scalar
  %arrayidx438 = getelementptr inbounds i32, ptr %ep, i64 %inc.lcssa
  %56 = load i32, ptr %arrayidx438
  %conv439 = zext i32 %56 to i64
  br label %cond.end

cond.end:                                         ; preds = %cond.true, %scalar
  %cond = phi i64 [ %conv439, %cond.true ], [ %n, %scalar ]
  %cmp443 = icmp ugt i64 %cond, %idxprom.lcssa
  br i1 %cmp443, label %land.lhs.true, label %if.end457

land.lhs.true:                                    ; preds = %cond.end
  %gep1069 = getelementptr i8, ptr %invariant.gep1068, i64 %cond
  %57 = load i8, ptr %gep1069
  br label %NodeBlock51

NodeBlock51:                                      ; preds = %land.lhs.true
  %Pivot52 = icmp slt i8 %57, 13
  br i1 %Pivot52, label %LeafBlock43, label %NodeBlock49

NodeBlock49:                                      ; preds = %NodeBlock51
  %Pivot50 = icmp slt i8 %57, 32
  br i1 %Pivot50, label %LeafBlock45, label %LeafBlock47

LeafBlock47:                                      ; preds = %NodeBlock49
  %SwitchLeaf48 = icmp eq i8 %57, 32
  br i1 %SwitchLeaf48, label %land.rhs.preheader, label %if.end457

LeafBlock45:                                      ; preds = %NodeBlock49
  %SwitchLeaf46 = icmp eq i8 %57, 13
  br i1 %SwitchLeaf46, label %land.rhs.preheader, label %if.end457

LeafBlock43:                                      ; preds = %NodeBlock51
  %.off = add i8 %57, -9
  %SwitchLeaf44 = icmp ule i8 %.off, 1
  br i1 %SwitchLeaf44, label %land.rhs.preheader, label %if.end457

land.rhs.preheader:                               ; preds = %LeafBlock47, %LeafBlock45, %LeafBlock43
  br label %land.rhs

land.rhs:                                         ; preds = %while.body, %land.rhs.preheader
  %ee.01053 = phi i64 [ %inc456, %while.body ], [ %idxprom.lcssa, %land.rhs.preheader ]
  %arrayidx453 = getelementptr inbounds i8, ptr %b, i64 %ee.01053
  %58 = load i8, ptr %arrayidx453
  br label %NodeBlock62

NodeBlock62:                                      ; preds = %land.rhs
  %Pivot63 = icmp slt i8 %58, 13
  br i1 %Pivot63, label %LeafBlock53, label %NodeBlock60

NodeBlock60:                                      ; preds = %NodeBlock62
  %Pivot61 = icmp slt i8 %58, 32
  br i1 %Pivot61, label %LeafBlock56, label %LeafBlock58

LeafBlock58:                                      ; preds = %NodeBlock60
  %SwitchLeaf59 = icmp eq i8 %58, 32
  br i1 %SwitchLeaf59, label %if.end457, label %while.body

LeafBlock56:                                      ; preds = %NodeBlock60
  %SwitchLeaf57 = icmp eq i8 %58, 13
  br i1 %SwitchLeaf57, label %if.end457, label %while.body

LeafBlock53:                                      ; preds = %NodeBlock62
  %.off54 = add i8 %58, -9
  %SwitchLeaf55 = icmp ule i8 %.off54, 1
  br i1 %SwitchLeaf55, label %if.end457, label %while.body

while.body:                                       ; preds = %LeafBlock58, %LeafBlock56, %LeafBlock53
  %inc456 = add i64 %ee.01053, 1
  %exitcond1170.not = icmp eq i64 %inc456, %cond
  br i1 %exitcond1170.not, label %if.end457, label %land.rhs

if.end457:                                        ; preds = %LeafBlock58, %LeafBlock56, %LeafBlock53, %LeafBlock47, %LeafBlock45, %LeafBlock43, %while.body, %cond.end
  %ee.1 = phi i64 [ %idxprom.lcssa, %cond.end ], [ %cond, %while.body ], [ %ee.01053, %LeafBlock53 ], [ %ee.01053, %LeafBlock56 ], [ %ee.01053, %LeafBlock58 ], [ %cond, %LeafBlock43 ], [ %cond, %LeafBlock45 ], [ %cond, %LeafBlock47 ]
  store i64 %inc.lcssa, ptr %k219
  %cmp462 = icmp eq i8 %.lcssa, 45
  %59 = add i8 %.lcssa, -48
  %or.cond = icmp ult i8 %59, 10
  %or.cond901 = or i1 %cmp462, %or.cond
  br i1 %or.cond901, label %if.then471, label %if.else495

if.then471:                                       ; preds = %if.end457
  call void @llvm.lifetime.start.p0(i64 8, ptr %d)
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei)
  store i64 0, ptr %ei
  %sub475 = sub i64 %ee.1, %idxprom.lcssa
  %call476 = call i32 @num_fast_el1(ptr %arrayidx6.le1046, i64 %sub475, ptr %d, ptr %ei)
  %tobool477.not.not = icmp eq i32 %call476, 0
  br i1 %tobool477.not.not, label %cleanup491.thread, label %cleanup491

cleanup491.thread:                                ; preds = %if.then471
  %60 = load i64, ptr %ei
  %add480 = add i64 %60, %idxprom.lcssa
  store i64 %add480, ptr %off
  call void @od_gap_recover(ptr %c, i64 %idxprom.lcssa)
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  %61 = load i64, ptr %off
  store i64 %61, ptr %err
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d)
  br label %cleanup580

cleanup491:                                       ; preds = %if.then471
  %62 = load i64, ptr %d
  %add489 = add i64 %62, 7
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d)
  br label %if.end545

if.else495:                                       ; preds = %if.end457
  br label %NodeBlock72

NodeBlock72:                                      ; preds = %if.else495
  %Pivot73 = icmp slt i8 %.lcssa, 110
  br i1 %Pivot73, label %LeafBlock64, label %NodeBlock70

NodeBlock70:                                      ; preds = %NodeBlock72
  %Pivot71 = icmp slt i8 %.lcssa, 116
  br i1 %Pivot71, label %LeafBlock66, label %LeafBlock68

LeafBlock68:                                      ; preds = %NodeBlock70
  %SwitchLeaf69 = icmp eq i8 %.lcssa, 116
  br i1 %SwitchLeaf69, label %if.end519, label %if.else510

LeafBlock66:                                      ; preds = %NodeBlock70
  %SwitchLeaf67 = icmp eq i8 %.lcssa, 110
  br i1 %SwitchLeaf67, label %if.then509, label %if.else510

LeafBlock64:                                      ; preds = %NodeBlock72
  %SwitchLeaf65 = icmp eq i8 %.lcssa, 102
  br i1 %SwitchLeaf65, label %if.then504, label %if.else510

if.then504:                                       ; preds = %LeafBlock64
  br label %if.end519

if.then509:                                       ; preds = %LeafBlock66
  br label %if.end519

if.else510:                                       ; preds = %LeafBlock68, %LeafBlock66, %LeafBlock64
  store i64 %idxprom.lcssa, ptr %off
  call void @od_gap_recover(ptr %c, i64 %idxprom.lcssa)
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  %63 = load i64, ptr %off
  store i64 %63, ptr %err
  br label %cleanup580

if.end519:                                        ; preds = %LeafBlock68, %if.then509, %if.then504
  %lit.0 = phi i64 [ 435728179558, %if.then504 ], [ 1819047278, %if.then509 ], [ 1702195828, %LeafBlock68 ]
  %exitcond38.not.i.3 = phi i1 [ false, %if.then504 ], [ true, %if.then509 ], [ true, %LeafBlock68 ]
  %ln.0 = phi i64 [ 5, %if.then504 ], [ 4, %if.then509 ], [ 4, %LeafBlock68 ]
  %tag.0 = phi i64 [ 9, %if.then504 ], [ 10, %if.then509 ], [ 8, %LeafBlock68 ]
  %sub524 = sub i64 %ee.1, %idxprom.lcssa
  %exitcond.not.i = icmp eq i64 %sub524, 0
  br i1 %exitcond.not.i, label %if.then527, label %if.end.i

for.body.i.1:                                     ; preds = %if.end.i
  %exitcond.not.i.1 = icmp eq i64 %sub524, 1
  br i1 %exitcond.not.i.1, label %if.then527, label %if.end.i.1

if.end.i.1:                                       ; preds = %for.body.i.1
  %arrayidx.i.1 = getelementptr inbounds i8, ptr %arrayidx6.le1046, i64 1
  %64 = load i8, ptr %arrayidx.i.1
  %shr.i.1 = lshr i64 %lit.0, 8
  %65 = trunc i64 %shr.i.1 to i8
  %cmp7.not.i.1 = icmp eq i8 %64, %65
  br i1 %cmp7.not.i.1, label %for.body.i.2, label %if.then527

for.body.i.2:                                     ; preds = %if.end.i.1
  %exitcond.not.i.2 = icmp eq i64 %sub524, 2
  br i1 %exitcond.not.i.2, label %if.then527, label %if.end.i.2

if.end.i.2:                                       ; preds = %for.body.i.2
  %arrayidx.i.2 = getelementptr inbounds i8, ptr %arrayidx6.le1046, i64 2
  %66 = load i8, ptr %arrayidx.i.2
  %shr.i.2 = lshr i64 %lit.0, 16
  %67 = trunc i64 %shr.i.2 to i8
  %cmp7.not.i.2 = icmp eq i8 %66, %67
  br i1 %cmp7.not.i.2, label %for.body.i.3, label %if.then527

for.body.i.3:                                     ; preds = %if.end.i.2
  %exitcond.not.i.3 = icmp eq i64 %sub524, 3
  br i1 %exitcond.not.i.3, label %if.then527, label %if.end.i.3

if.end.i.3:                                       ; preds = %for.body.i.3
  %arrayidx.i.3 = getelementptr inbounds i8, ptr %arrayidx6.le1046, i64 3
  %68 = load i8, ptr %arrayidx.i.3
  %shr.i.3 = lshr i64 %lit.0, 24
  %69 = trunc i64 %shr.i.3 to i8
  %cmp7.not.i.3 = icmp eq i8 %68, %69
  br i1 %cmp7.not.i.3, label %for.cond.i.3, label %if.then527

for.cond.i.3:                                     ; preds = %if.end.i.3
  br i1 %exitcond38.not.i.3, label %for.end.i, label %for.body.i.4

for.body.i.4:                                     ; preds = %for.cond.i.3
  %exitcond.not.i.4 = icmp eq i64 %sub524, 4
  br i1 %exitcond.not.i.4, label %if.then527, label %if.end.i.4

if.end.i.4:                                       ; preds = %for.body.i.4
  %arrayidx.i.4 = getelementptr inbounds i8, ptr %arrayidx6.le1046, i64 4
  %70 = load i8, ptr %arrayidx.i.4
  %shr.i.4 = lshr i64 %lit.0, 32
  %71 = trunc i64 %shr.i.4 to i8
  %cmp7.not.i.4 = icmp eq i8 %70, %71
  br i1 %cmp7.not.i.4, label %for.end.i, label %if.then527

if.end.i:                                         ; preds = %if.end519
  %72 = load i8, ptr %arrayidx6.le1046
  %73 = trunc i64 %lit.0 to i8
  %cmp7.not.i = icmp eq i8 %72, %73
  br i1 %cmp7.not.i, label %for.body.i.1, label %if.then527

for.end.i:                                        ; preds = %if.end.i.4, %for.cond.i.3
  %cmp13.not.i = icmp eq i64 %sub524, %ln.0
  br i1 %cmp13.not.i, label %if.end545, label %if.then527

if.then527:                                       ; preds = %for.end.i, %if.end.i, %if.end.i.4, %for.body.i.4, %if.end.i.3, %for.body.i.3, %if.end.i.2, %for.body.i.2, %if.end.i.1, %for.body.i.1, %if.end519
  %ei520.0.ph = phi i64 [ %sub524, %if.end519 ], [ 0, %if.end.i ], [ %sub524, %for.body.i.1 ], [ 1, %if.end.i.1 ], [ %sub524, %for.body.i.2 ], [ 2, %if.end.i.2 ], [ %sub524, %for.body.i.3 ], [ 3, %if.end.i.3 ], [ %sub524, %for.body.i.4 ], [ 4, %if.end.i.4 ], [ %ln.0, %for.end.i ]
  %add529 = add i64 %ei520.0.ph, %idxprom.lcssa
  store i64 %add529, ptr %off
  call void @od_gap_recover(ptr %c, i64 %idxprom.lcssa)
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  %74 = load i64, ptr %off
  store i64 %74, ptr %err
  br label %cleanup580

if.end545:                                        ; preds = %for.end.i, %cleanup491
  %add489.pn = phi i64 [ %add489, %cleanup491 ], [ %tag.0, %for.end.i ]
  %tokens.12 = add i64 %tokens.0.lcssa1073, 1
  %terms.12 = add i64 %add489.pn, %terms.0.lcssa1079
  %cmp546 = icmp ult i64 %ee.1, %cond
  br i1 %cmp546, label %land.rhs552, label %after_value

land.rhs552:                                      ; preds = %while.body557, %if.end545
  %q.01062 = phi i64 [ %inc558, %while.body557 ], [ %ee.1, %if.end545 ]
  %arrayidx553 = getelementptr inbounds i8, ptr %b, i64 %q.01062
  %75 = load i8, ptr %arrayidx553
  br label %NodeBlock83

NodeBlock83:                                      ; preds = %land.rhs552
  %Pivot84 = icmp slt i8 %75, 13
  br i1 %Pivot84, label %LeafBlock74, label %NodeBlock81

NodeBlock81:                                      ; preds = %NodeBlock83
  %Pivot82 = icmp slt i8 %75, 32
  br i1 %Pivot82, label %LeafBlock77, label %LeafBlock79

LeafBlock79:                                      ; preds = %NodeBlock81
  %SwitchLeaf80 = icmp eq i8 %75, 32
  br i1 %SwitchLeaf80, label %while.body557, label %if.then562

LeafBlock77:                                      ; preds = %NodeBlock81
  %SwitchLeaf78 = icmp eq i8 %75, 13
  br i1 %SwitchLeaf78, label %while.body557, label %if.then562

LeafBlock74:                                      ; preds = %NodeBlock83
  %.off75 = add i8 %75, -9
  %SwitchLeaf76 = icmp ule i8 %.off75, 1
  br i1 %SwitchLeaf76, label %while.body557, label %if.then562

while.body557:                                    ; preds = %LeafBlock79, %LeafBlock77, %LeafBlock74
  %inc558 = add i64 %q.01062, 1
  %exitcond1171.not = icmp eq i64 %inc558, %cond
  br i1 %exitcond1171.not, label %after_value, label %land.rhs552

if.then562:                                       ; preds = %LeafBlock79, %LeafBlock77, %LeafBlock74
  store i64 0, ptr %tokens_out
  store i64 0, ptr %values_out
  store i64 0, ptr %sum_out
  store i64 %q.01062, ptr %err
  br label %cleanup580

accept:                                           ; preds = %if.then357
  store i64 %tokens.8, ptr %tokens_out
  store i64 %tokens.8, ptr %values_out
  %add579 = add i64 %terms.8, %arena.10
  store i64 %add579, ptr %sum_out
  br label %cleanup580

cleanup580:                                       ; preds = %accept, %if.then562, %if.then527, %if.else510, %cleanup491.thread, %if.then428, %if.then402, %if.then372, %if.then360, %if.then321, %if.then311, %if.then297, %cleanup287.thread, %cleanup.thread, %if.then118, %if.then105, %if.then94, %if.then68, %if.then38, %if.then12, %if.then
  %retval.14 = phi i64 [ 0, %if.then ], [ 0, %if.then12 ], [ 0, %if.then68 ], [ 0, %if.then360 ], [ 1, %accept ], [ 0, %if.then372 ], [ 0, %if.then402 ], [ 0, %if.then105 ], [ 0, %if.then118 ], [ 0, %if.then297 ], [ 0, %if.then311 ], [ 0, %if.then428 ], [ 0, %if.then94 ], [ 0, %if.then38 ], [ 0, %if.then321 ], [ 0, %cleanup.thread ], [ 0, %cleanup287.thread ], [ 0, %if.then562 ], [ 0, %cleanup491.thread ], [ 0, %if.else510 ], [ 0, %if.then527 ]
  call void @llvm.lifetime.end.p0(i64 1192, ptr %c)
  call void @llvm.lifetime.end.p0(i64 24, ptr %e)
  call void @llvm.lifetime.end.p0(i64 520, ptr %stk)
  call void @llvm.lifetime.end.p0(i64 8, ptr %xj)
  ret i64 %retval.14
}

declare void @llvm.lifetime.start.p0(i64, ptr)
declare void @llvm.lifetime.end.p0(i64, ptr)
declare void @llvm.trap()
declare i32 @s2_string_body(ptr %c, ptr %p, i64 %len, ptr %dst, ptr %outn, ptr %xp, ptr %xj, i64 %nxp)
declare i32 @num_fast_el1(ptr %p, i64 %n, ptr %out, ptr %err)
declare void @od_gap_recover(ptr %c, i64 %t.0.val)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
