; The table-driven stage-2 candidate as emitted, in the fragment `LeanLLVM.Semantics` models.
; Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-dfa.sh
;
; from kernel/json/stage2_dfa.c (which includes kernel/json/stage2.c), emitted at
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names \
;         <both units with `noinline` on every helper except sd_walk>
;
; then `opt -passes=lower-switch`, then reduced to the one `define` block.
;
; The source transform is part of the derivation, not of the file: `sd_walk`
; keeps `__attribute__((always_inline))` and inlines into the wrapper, where the
; mode is the constant `S2_VAL | S2_STR | S2_EV` and the branches that mode does
; not take fold away; the helpers listed in stage2-dfa.rewrites.tsv carry
; `noinline` instead, so their bodies stay out of this text.  That boundary is
; the point: the number path's arithmetic is binary64, which this fragment has no
; operations for, and its contract is the tier composition proved in
; LeanLLVM/Refinement/JsonStage2Body.lean (`numFastEmitted_strtodSpec`).
;
; So this is the walk's text with its intra-unit helper boundaries preserved and
; the mode constant: NOT the measured object's text, which inlines the helpers.
; Measured: the fused emission of the same source is 1249 lines and
; 158 blocks and carries binary64; the body below is 564 lines and
; 92 blocks and carries none.
;
; The function's parameters are `stage2.h`'s thirteen in their ABI order,
; followed by the record's eight slots (see stage2-dfa.staging.tsv): %d.i,
; %c.i, %ctype.i, %cst.i, %t352.i, %s, %z, %e.  Six are the body's flattened
; allocas (%stk.i is %ctype.i, %tok.i is %t352.i); %d.i is staged and unused,
; %cst.i carries the 256-byte classifier at offset 0 and the 10-byte resume
; table at 256, and the 80-byte transition table at 272; the body reads them
; and never writes the slot.
; The re-indexing between the twenty-one-argument body and the thirteen-argument
; ABI is stated in LeanLLVM/Refinement/JsonStage2IR.lean, and the pin in
; LeanLLVM/Refinement/JsonStage2DfaBody.lean makes this text the body those
; theorems run.
;
; Removed before the parser sees the text, each item with its class in
; stage2-dfa.strip.tsv, and each rewrite in stage2-dfa.rewrites.tsv; the body's
; own guards (the four trap arms and the thirteen-byte record) are
; body text and are kept.
;
; The inventory of this fixture's opcodes and call targets is
; stage2-dfa.inventory. `opt -passes=verify` accepts it and `leanllvm` parses it,
; both checked by the capture.

define i64 @leanllvm_json_stage2_dfa(ptr %b, i64 %n, ptr %ep, i64 %nep, ptr %xp, i64 %nxp, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err, ptr %d.i, ptr %c.i, ptr %ctype.i, ptr %cst.i, ptr %t352.i, ptr %s, ptr %z, ptr %e) {
entry:
  %xj.i = alloca i64
  %outn.i = alloca i64
  call void @llvm.lifetime.start.p0(i64 120, ptr %s)
  call void @llvm.lifetime.start.p0(i64 64, ptr %z)
  call void @llvm.lifetime.start.p0(i64 24, ptr %e)
  %add = add i64 %n, 63
  %shr = lshr i64 %add, 6
  call void @s2_init(ptr %s, ptr %b, i64 %n, i64 %shr, ptr %ep)
  %hash1.i.i = getelementptr inbounds i8, ptr %z, i64 32
  %ar = getelementptr inbounds i8, ptr %z, i64 40
  %0 = getelementptr inbounds i8, ptr %z, i64 24
  call void @llvm.memset.p0.i64(ptr %0, i8 0, i64 16, i1 false)
  store ptr %dst, ptr %ar
  %1 = load i64, ptr %ndst
  %alen = getelementptr inbounds i8, ptr %z, i64 48
  store i64 %1, ptr %alen
  %acap = getelementptr inbounds i8, ptr %z, i64 56
  store i64 %dstcap, ptr %acap
  store ptr %ev, ptr %z
  %2 = load i64, ptr %nev
  %len = getelementptr inbounds i8, ptr %z, i64 8
  store i64 %2, ptr %len
  %cap = getelementptr inbounds i8, ptr %z, i64 16
  store i64 %evcap, ptr %cap
  store i32 1, ptr %e
  %off = getelementptr inbounds i8, ptr %e, i64 8
  store i64 0, ptr %off
  %msg = getelementptr inbounds i8, ptr %e, i64 16
  store ptr null, ptr %msg
  %3 = load ptr, ptr %s
  %n2.i = getelementptr inbounds i8, ptr %s, i64 8
  %4 = load i64, ptr %n2.i
  %ep4.i = getelementptr inbounds i8, ptr %s, i64 48
  %5 = load ptr, ptr %ep4.i
  call void @llvm.lifetime.start.p0(i64 520, ptr %ctype.i)
  call void @llvm.lifetime.start.p0(i64 8, ptr %xj.i)
  store i64 0, ptr %xj.i
  call void @llvm.lifetime.start.p0(i64 1192, ptr %c.i)
  %6 = getelementptr inbounds i8, ptr %c.i, i64 32
  call void @llvm.memset.p0.i64(ptr %6, i8 0, i64 1160, i1 false)
  store ptr %3, ptr %c.i
  %n8.i = getelementptr inbounds i8, ptr %c.i, i64 8
  store i64 %4, ptr %n8.i
  %ix.i = getelementptr inbounds i8, ptr %c.i, i64 16
  store ptr %5, ptr %ix.i
  %nix.i = getelementptr inbounds i8, ptr %c.i, i64 24
  store i64 %nep, ptr %nix.i
  %e9.i = getelementptr inbounds i8, ptr %c.i, i64 1112
  store ptr %e, ptr %e9.i
  %invariant.gep = getelementptr i8, ptr %3, i64 -1
  %cmp.i153160.not = icmp eq i64 %nep, 0
  br i1 %cmp.i153160.not, label %if.then233.i, label %while.body.i.lr.ph.lr.ph

while.body.i.lr.ph.lr.ph:                         ; preds = %entry
  %gap.i = getelementptr inbounds i8, ptr %t352.i, i64 20
  %end.i = getelementptr inbounds i8, ptr %t352.i, i64 8
  %kind174.i = getelementptr inbounds i8, ptr %t352.i, i64 16
  %k60.i = getelementptr inbounds i8, ptr %c.i, i64 32
  %h1.i.i.i26 = getelementptr inbounds i8, ptr %z, i64 24
  br label %while.body.i.lr.ph

while.body.i.lr.ph:                               ; preds = %while.cond.i.outer.backedge, %while.body.i.lr.ph.lr.ph
  %sp.0.i.ph163 = phi i32 [ 0, %while.body.i.lr.ph.lr.ph ], [ %sp.0.i.ph.be, %while.cond.i.outer.backedge ]
  %state.0.i.ph162 = phi i32 [ 0, %while.body.i.lr.ph.lr.ph ], [ %state.0.i.ph.be, %while.cond.i.outer.backedge ]
  %k.0.i.ph161 = phi i64 [ 0, %while.body.i.lr.ph.lr.ph ], [ %inc.i, %while.cond.i.outer.backedge ]
  br label %while.body.i

while.body.i:                                     ; preds = %while.cond.i.backedge, %while.body.i.lr.ph
  %state.0.i155 = phi i32 [ %state.0.i.ph162, %while.body.i.lr.ph ], [ %and.i, %while.cond.i.backedge ]
  %k.0.i154 = phi i64 [ %k.0.i.ph161, %while.body.i.lr.ph ], [ %k.0.i.be, %while.cond.i.backedge ]
  %inc.i = add i64 %k.0.i154, 1
  %arrayidx.i = getelementptr inbounds i32, ptr %5, i64 %k.0.i154
  %7 = load i32, ptr %arrayidx.i
  %idxprom.i = zext i32 %7 to i64
  %arrayidx10.i = getelementptr inbounds i8, ptr %3, i64 %idxprom.i
  %8 = load i8, ptr %arrayidx10.i
  %idxprom11.i = zext i8 %8 to i64
  %arrayidx12.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom11.i
  %9 = load i8, ptr %arrayidx12.i
  %idxprom13.i = zext i32 %state.0.i155 to i64
  %idxprom15.i = zext i8 %9 to i64
  %cst.tr = getelementptr inbounds i8, ptr %cst.i, i64 272
  %tr.off = shl i64 %idxprom13.i, 3
  %tr.row = getelementptr inbounds i8, ptr %cst.tr, i64 %tr.off
  %arrayidx16.i = getelementptr inbounds i8, ptr %tr.row, i64 %idxprom15.i
  %10 = load i8, ptr %arrayidx16.i
  %conv17.i = zext i8 %10 to i32
  %shr.i = lshr i32 %conv17.i, 4
  %and.i = and i32 %conv17.i, 15
  br label %NodeBlock7

NodeBlock7:                                       ; preds = %while.body.i
  %Pivot8 = icmp slt i32 %shr.i, 5
  br i1 %Pivot8, label %NodeBlock1, label %NodeBlock5

NodeBlock5:                                       ; preds = %NodeBlock7
  %Pivot6 = icmp slt i32 %shr.i, 6
  br i1 %Pivot6, label %sw.bb51.i, label %NodeBlock3

NodeBlock3:                                       ; preds = %NodeBlock5
  %Pivot4 = icmp slt i32 %shr.i, 7
  br i1 %Pivot4, label %sw.bb115.i, label %LeafBlock

LeafBlock:                                        ; preds = %NodeBlock3
  %SwitchLeaf = icmp eq i32 %shr.i, 7
  br i1 %SwitchLeaf, label %if.then.i, label %sw.default.i

NodeBlock1:                                       ; preds = %NodeBlock7
  %Pivot2 = icmp slt i32 %shr.i, 1
  br i1 %Pivot2, label %while.cond.i.backedge, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock1
  %Pivot = icmp slt i32 %shr.i, 3
  br i1 %Pivot, label %sw.bb.i, label %sw.bb39.i

if.then.i:                                        ; preds = %LeafBlock
  store i64 %idxprom.i, ptr %off
  br label %if.then

sw.bb.i:                                          ; preds = %NodeBlock
  %cmp22.i = icmp ugt i32 %sp.0.i.ph163, 519
  br i1 %cmp22.i, label %if.then24.i, label %if.end27.i

if.then24.i:                                      ; preds = %sw.bb.i
  store i64 %idxprom.i, ptr %off
  br label %if.then

if.end27.i:                                       ; preds = %sw.bb.i
  %tobool28.not.i = icmp eq i32 %sp.0.i.ph163, 0
  br i1 %tobool28.not.i, label %if.end34.i, label %if.then29.i

if.then29.i:                                      ; preds = %if.end27.i
  %cst.restore = getelementptr inbounds i8, ptr %cst.i, i64 256
  %arrayidx31.i = getelementptr inbounds i8, ptr %cst.restore, i64 %idxprom13.i
  %11 = load i8, ptr %arrayidx31.i
  %sub.i = add i32 %sp.0.i.ph163, -1
  %idxprom32.i = zext i32 %sub.i to i64
  %arrayidx33.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom32.i
  store i8 %11, ptr %arrayidx33.i
  br label %if.end34.i

if.end34.i:                                       ; preds = %if.then29.i, %if.end27.i
  %inc35.i = add i32 %sp.0.i.ph163, 1
  %cmp36.i = icmp eq i32 %shr.i, 1
  %conv38.i = select i1 %cmp36.i, i8 1, i8 3
  %12 = load i32, ptr %hash1.i.i
  %tobool.not.i.i = icmp eq i32 %12, 0
  br i1 %tobool.not.i.i, label %if.end.i.i, label %if.then.i.i

if.then.i.i:                                      ; preds = %if.end34.i
  %13 = load i64, ptr %h1.i.i.i26
  %conv.i.i.i = zext i8 %conv38.i to i64
  %xor.us.i.i.i = xor i64 %13, %conv.i.i.i
  %14 = mul i64 %xor.us.i.i.i, -2358710677322311239
  %mul11.i.i.i = add i64 %14, -7046029254386353131
  store i64 %mul11.i.i.i, ptr %h1.i.i.i26
  br label %while.cond.i.outer.backedge

if.end.i.i:                                       ; preds = %if.end34.i
  %o.val.i.i = load i64, ptr %len
  %o.val11.i.i = load i64, ptr %cap
  %add.i.i.i = add i64 %o.val.i.i, 1
  %cmp.not.i.i.i = icmp ugt i64 %add.i.i.i, %o.val11.i.i
  br i1 %cmp.not.i.i.i, label %if.end.i.i.i, label %out_reserve.exit.i.i

if.end.i.i.i:                                     ; preds = %if.end.i.i
  call void @llvm.trap()
  unreachable

out_reserve.exit.i.i:                             ; preds = %if.end.i.i
  %15 = load ptr, ptr %z
  %add.ptr.i.i = getelementptr inbounds i8, ptr %15, i64 %o.val.i.i
  store i8 %conv38.i, ptr %add.ptr.i.i
  store i64 %add.i.i.i, ptr %len
  br label %while.cond.i.outer.backedge

sw.bb39.i:                                        ; preds = %NodeBlock
  %dec.i = add i32 %sp.0.i.ph163, -1
  %tobool40.not.i = icmp eq i32 %dec.i, 0
  br i1 %tobool40.not.i, label %cond.end.i, label %cond.true.i

cond.true.i:                                      ; preds = %sw.bb39.i
  %sub41.i = add i32 %sp.0.i.ph163, -2
  %idxprom42.i = zext i32 %sub41.i to i64
  %arrayidx43.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom42.i
  %16 = load i8, ptr %arrayidx43.i
  %conv44.i = zext i8 %16 to i32
  br label %cond.end.i

cond.end.i:                                       ; preds = %cond.true.i, %sw.bb39.i
  %cond45.i = phi i32 [ %conv44.i, %cond.true.i ], [ 1, %sw.bb39.i ]
  %cmp47.i = icmp eq i32 %shr.i, 3
  %conv50.i = select i1 %cmp47.i, i8 2, i8 4
  %17 = load i32, ptr %hash1.i.i
  %tobool.not.i.i24 = icmp eq i32 %17, 0
  br i1 %tobool.not.i.i24, label %if.end.i.i30, label %if.then.i.i25

if.then.i.i25:                                    ; preds = %cond.end.i
  %18 = load i64, ptr %h1.i.i.i26
  %conv.i.i.i27 = zext i8 %conv50.i to i64
  %xor.us.i.i.i28 = xor i64 %18, %conv.i.i.i27
  %19 = mul i64 %xor.us.i.i.i28, -2358710677322311239
  %mul11.i.i.i29 = add i64 %19, -7046029254386353131
  store i64 %mul11.i.i.i29, ptr %h1.i.i.i26
  br label %while.cond.i.outer.backedge

if.end.i.i30:                                     ; preds = %cond.end.i
  %o.val.i.i31 = load i64, ptr %len
  %o.val11.i.i32 = load i64, ptr %cap
  %add.i.i.i33 = add i64 %o.val.i.i31, 1
  %cmp.not.i.i.i34 = icmp ugt i64 %add.i.i.i33, %o.val11.i.i32
  br i1 %cmp.not.i.i.i34, label %if.end.i.i.i39, label %out_reserve.exit.i.i35

if.end.i.i.i39:                                   ; preds = %if.end.i.i30
  call void @llvm.trap()
  unreachable

out_reserve.exit.i.i35:                           ; preds = %if.end.i.i30
  %20 = load ptr, ptr %z
  %add.ptr.i.i36 = getelementptr inbounds i8, ptr %20, i64 %o.val.i.i31
  store i8 %conv50.i, ptr %add.ptr.i.i36
  store i64 %add.i.i.i33, ptr %len
  br label %while.cond.i.outer.backedge

while.cond.i.outer.backedge:                      ; preds = %out_reserve.exit.i.i35, %if.then.i.i25, %out_reserve.exit.i.i, %if.then.i.i
  %state.0.i.ph.be = phi i32 [ %and.i, %if.then.i.i ], [ %and.i, %out_reserve.exit.i.i ], [ %cond45.i, %if.then.i.i25 ], [ %cond45.i, %out_reserve.exit.i.i35 ]
  %sp.0.i.ph.be = phi i32 [ %inc35.i, %if.then.i.i ], [ %inc35.i, %out_reserve.exit.i.i ], [ %dec.i, %if.then.i.i25 ], [ %dec.i, %out_reserve.exit.i.i35 ]
  %cmp.i153 = icmp ult i64 %inc.i, %nep
  br i1 %cmp.i153, label %while.body.i.lr.ph, label %while.end225.i

sw.bb51.i:                                        ; preds = %NodeBlock5
  %cmp52.not.i = icmp ult i64 %inc.i, %nep
  br i1 %cmp52.not.i, label %if.end57.i, label %if.then54.i

if.then54.i:                                      ; preds = %sw.bb51.i
  store i64 %idxprom.i, ptr %off
  br label %if.then

if.end57.i:                                       ; preds = %sw.bb51.i
  %inc58.i = add i64 %k.0.i154, 2
  %arrayidx59.i = getelementptr inbounds i32, ptr %5, i64 %inc.i
  %21 = load i32, ptr %arrayidx59.i
  store i64 %inc58.i, ptr %k60.i
  %conv61.i = zext i32 %21 to i64
  %cmp62.not.i = icmp ugt i64 %4, %conv61.i
  br i1 %cmp62.not.i, label %if.end67.i, label %if.then64.i

if.then64.i:                                      ; preds = %if.end57.i
  store i64 %idxprom.i, ptr %off
  br label %if.then

if.end67.i:                                       ; preds = %if.end57.i
  %22 = and i32 %state.0.i155, -2
  %23 = icmp eq i32 %22, 2
  %24 = xor i64 %idxprom.i, -1
  %sub75.i = add i64 %conv61.i, %24
  call void @llvm.lifetime.start.p0(i64 8, ptr %outn.i)
  store i64 0, ptr %outn.i
  %add.i = add i64 %sub75.i, 64
  %z.val19 = load i64, ptr %alen
  %z.val20 = load i64, ptr %acap
  %add.i41 = add i64 %add.i, %z.val19
  %cmp.not.i = icmp ugt i64 %add.i41, %z.val20
  br i1 %cmp.not.i, label %if.end.i, label %z_arena_reserve.exit

if.end.i:                                         ; preds = %if.end67.i
  call void @llvm.trap()
  unreachable

z_arena_reserve.exit:                             ; preds = %if.end67.i
  %25 = load ptr, ptr %ar
  %add.ptr.i = getelementptr inbounds i8, ptr %25, i64 %z.val19
  %add.ptr77.i = getelementptr inbounds i8, ptr %arrayidx10.i, i64 1
  %call78.i = call i32 @s2_string_body(ptr %c.i, ptr %add.ptr77.i, i64 %sub75.i, ptr %add.ptr.i, ptr %outn.i, ptr %xp, ptr %xj.i, i64 %nxp)
  br label %NodeBlock11

NodeBlock11:                                      ; preds = %z_arena_reserve.exit
  %Pivot12 = icmp slt i32 %call78.i, 1
  br i1 %Pivot12, label %cleanup.i.thread, label %LeafBlock9

LeafBlock9:                                       ; preds = %NodeBlock11
  %SwitchLeaf10 = icmp eq i32 %call78.i, 1
  br i1 %SwitchLeaf10, label %if.then84.i, label %if.else.i

cleanup.i.thread:                                 ; preds = %NodeBlock11
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn.i)
  br label %if.then

if.then84.i:                                      ; preds = %LeafBlock9
  %add86.i = add i32 %7, 1
  %conv87.i = zext i32 %add86.i to i64
  %or.i = or i64 %conv87.i, -9223372036854775808
  br label %if.end92.i

if.else.i:                                        ; preds = %LeafBlock9
  %26 = load i64, ptr %outn.i
  %add91.i = add i64 %z.val19, %26
  store i64 %add91.i, ptr %alen
  br label %if.end92.i

if.end92.i:                                       ; preds = %if.else.i, %if.then84.i
  %conv88.i.sink.in = phi i64 [ %sub75.i, %if.then84.i ], [ %26, %if.else.i ]
  %.sink = phi i64 [ %or.i, %if.then84.i ], [ %z.val19, %if.else.i ]
  %z.val = load i64, ptr %len
  %z.val18 = load i64, ptr %cap
  %add.i42 = add i64 %z.val, 13
  %cmp.not.i43 = icmp ugt i64 %add.i42, %z.val18
  br i1 %cmp.not.i43, label %if.end.i44, label %cleanup.i

if.end.i44:                                       ; preds = %if.end92.i
  call void @llvm.trap()
  unreachable

cleanup.i:                                        ; preds = %if.end92.i
  %conv88.i.sink = trunc i64 %conv88.i.sink.in to i32
  %27 = load ptr, ptr %z
  %add.ptr98.i = getelementptr inbounds i8, ptr %27, i64 %z.val
  %conv101.i = select i1 %23, i8 5, i8 6
  store i8 %conv101.i, ptr %add.ptr98.i
  %add.ptr103.i = getelementptr inbounds i8, ptr %add.ptr98.i, i64 1
  store i32 %conv88.i.sink, ptr %add.ptr103.i
  %add.ptr105.i = getelementptr inbounds i8, ptr %add.ptr98.i, i64 5
  store i64 %.sink, ptr %add.ptr105.i
  store i64 %add.i42, ptr %len
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn.i)
  br label %while.cond.i.backedge

while.cond.i.backedge:                            ; preds = %NodeBlock1, %if.end211.i, %cleanup.i
  %k.0.i.be = phi i64 [ %inc.i, %if.end211.i ], [ %inc58.i, %cleanup.i ], [ %inc.i, %NodeBlock1 ]
  %cmp.i = icmp ult i64 %k.0.i.be, %nep
  br i1 %cmp.i, label %while.body.i, label %while.end225.i

sw.bb115.i:                                       ; preds = %NodeBlock3
  %cmp116.i = icmp ult i64 %inc.i, %nep
  br i1 %cmp116.i, label %cond.true118.i, label %cond.end122.i

cond.true118.i:                                   ; preds = %sw.bb115.i
  %arrayidx119.i = getelementptr inbounds i32, ptr %5, i64 %inc.i
  %28 = load i32, ptr %arrayidx119.i
  %conv120.i = zext i32 %28 to i64
  br label %cond.end122.i

cond.end122.i:                                    ; preds = %cond.true118.i, %sw.bb115.i
  %cond123.i = phi i64 [ %conv120.i, %cond.true118.i ], [ %4, %sw.bb115.i ]
  call void @llvm.lifetime.start.p0(i64 24, ptr %t352.i)
  store i64 %idxprom.i, ptr %t352.i
  store i32 1, ptr %gap.i
  %cmp127.i = icmp ugt i64 %cond123.i, %idxprom.i
  br i1 %cmp127.i, label %land.lhs.true.i, label %if.end143.i

land.lhs.true.i:                                  ; preds = %cond.end122.i
  %gep = getelementptr i8, ptr %invariant.gep, i64 %cond123.i
  %29 = load i8, ptr %gep
  br label %NodeBlock21

NodeBlock21:                                      ; preds = %land.lhs.true.i
  %Pivot22 = icmp slt i8 %29, 13
  br i1 %Pivot22, label %LeafBlock13, label %NodeBlock19

NodeBlock19:                                      ; preds = %NodeBlock21
  %Pivot20 = icmp slt i8 %29, 32
  br i1 %Pivot20, label %LeafBlock15, label %LeafBlock17

LeafBlock17:                                      ; preds = %NodeBlock19
  %SwitchLeaf18 = icmp eq i8 %29, 32
  br i1 %SwitchLeaf18, label %land.rhs.i.preheader, label %if.end143.i

LeafBlock15:                                      ; preds = %NodeBlock19
  %SwitchLeaf16 = icmp eq i8 %29, 13
  br i1 %SwitchLeaf16, label %land.rhs.i.preheader, label %if.end143.i

LeafBlock13:                                      ; preds = %NodeBlock21
  %.off = add i8 %29, -9
  %SwitchLeaf14 = icmp ule i8 %.off, 1
  br i1 %SwitchLeaf14, label %land.rhs.i.preheader, label %if.end143.i

land.rhs.i.preheader:                             ; preds = %LeafBlock17, %LeafBlock15, %LeafBlock13
  br label %land.rhs.i

land.rhs.i:                                       ; preds = %while.body141.i, %land.rhs.i.preheader
  %ee.0.i144 = phi i64 [ %inc142.i, %while.body141.i ], [ %idxprom.i, %land.rhs.i.preheader ]
  %arrayidx138.i = getelementptr inbounds i8, ptr %3, i64 %ee.0.i144
  %30 = load i8, ptr %arrayidx138.i
  br label %NodeBlock32

NodeBlock32:                                      ; preds = %land.rhs.i
  %Pivot33 = icmp slt i8 %30, 13
  br i1 %Pivot33, label %LeafBlock23, label %NodeBlock30

NodeBlock30:                                      ; preds = %NodeBlock32
  %Pivot31 = icmp slt i8 %30, 32
  br i1 %Pivot31, label %LeafBlock26, label %LeafBlock28

LeafBlock28:                                      ; preds = %NodeBlock30
  %SwitchLeaf29 = icmp eq i8 %30, 32
  br i1 %SwitchLeaf29, label %if.end143.i, label %while.body141.i

LeafBlock26:                                      ; preds = %NodeBlock30
  %SwitchLeaf27 = icmp eq i8 %30, 13
  br i1 %SwitchLeaf27, label %if.end143.i, label %while.body141.i

LeafBlock23:                                      ; preds = %NodeBlock32
  %.off24 = add i8 %30, -9
  %SwitchLeaf25 = icmp ule i8 %.off24, 1
  br i1 %SwitchLeaf25, label %if.end143.i, label %while.body141.i

while.body141.i:                                  ; preds = %LeafBlock28, %LeafBlock26, %LeafBlock23
  %inc142.i = add i64 %ee.0.i144, 1
  %exitcond.not = icmp eq i64 %inc142.i, %cond123.i
  br i1 %exitcond.not, label %if.end143.i, label %land.rhs.i

if.end143.i:                                      ; preds = %LeafBlock28, %LeafBlock26, %LeafBlock23, %LeafBlock17, %LeafBlock15, %LeafBlock13, %while.body141.i, %cond.end122.i
  %ee.1.i = phi i64 [ %idxprom.i, %cond.end122.i ], [ %cond123.i, %while.body141.i ], [ %ee.0.i144, %LeafBlock23 ], [ %ee.0.i144, %LeafBlock26 ], [ %ee.0.i144, %LeafBlock28 ], [ %cond123.i, %LeafBlock13 ], [ %cond123.i, %LeafBlock15 ], [ %cond123.i, %LeafBlock17 ]
  store i64 %ee.1.i, ptr %end.i
  %cmp147.i = icmp eq i8 %8, 45
  %31 = add i8 %8, -48
  %or.cond.i = icmp ult i8 %31, 10
  %or.cond362.i = or i1 %cmp147.i, %or.cond.i
  br i1 %or.cond362.i, label %if.end180.i, label %if.else157.i

if.else157.i:                                     ; preds = %if.end143.i
  br label %NodeBlock42

NodeBlock42:                                      ; preds = %if.else157.i
  %Pivot43 = icmp slt i8 %8, 110
  br i1 %Pivot43, label %LeafBlock34, label %NodeBlock40

NodeBlock40:                                      ; preds = %NodeBlock42
  %Pivot41 = icmp slt i8 %8, 116
  br i1 %Pivot41, label %LeafBlock36, label %LeafBlock38

LeafBlock38:                                      ; preds = %NodeBlock40
  %SwitchLeaf39 = icmp eq i8 %8, 116
  br i1 %SwitchLeaf39, label %if.end180.i, label %if.else175.i

LeafBlock36:                                      ; preds = %NodeBlock40
  %SwitchLeaf37 = icmp eq i8 %8, 110
  br i1 %SwitchLeaf37, label %if.then173.i, label %if.else175.i

LeafBlock34:                                      ; preds = %NodeBlock42
  %SwitchLeaf35 = icmp eq i8 %8, 102
  br i1 %SwitchLeaf35, label %if.then167.i, label %if.else175.i

if.then167.i:                                     ; preds = %LeafBlock34
  br label %if.end180.i

if.then173.i:                                     ; preds = %LeafBlock36
  br label %if.end180.i

if.else175.i:                                     ; preds = %LeafBlock38, %LeafBlock36, %LeafBlock34
  br label %if.end180.i

if.end180.i:                                      ; preds = %LeafBlock38, %if.else175.i, %if.then173.i, %if.then167.i, %if.end143.i
  %.sink317 = phi i32 [ 0, %if.else175.i ], [ 10, %if.then173.i ], [ 9, %if.then167.i ], [ 7, %if.end143.i ], [ 8, %LeafBlock38 ]
  store i32 %.sink317, ptr %kind174.i
  %call182.i = call i32 @od_scalar_value(ptr %c.i, ptr %t352.i, ptr %z)
  %tobool183.not.i = icmp eq i32 %call182.i, 0
  br i1 %tobool183.not.i, label %if.then187.i, label %if.end189.i

if.then187.i:                                     ; preds = %if.end180.i
  call void @od_gap_recover(ptr %c.i, i64 %idxprom.i)
  br label %cleanup212.i

if.end189.i:                                      ; preds = %if.end180.i
  %cmp190.i = icmp ult i64 %ee.1.i, %cond123.i
  br i1 %cmp190.i, label %land.rhs196.i, label %if.end211.i

land.rhs196.i:                                    ; preds = %while.body201.i, %if.end189.i
  %q.0.i152 = phi i64 [ %inc202.i, %while.body201.i ], [ %ee.1.i, %if.end189.i ]
  %arrayidx197.i = getelementptr inbounds i8, ptr %3, i64 %q.0.i152
  %32 = load i8, ptr %arrayidx197.i
  br label %NodeBlock53

NodeBlock53:                                      ; preds = %land.rhs196.i
  %Pivot54 = icmp slt i8 %32, 13
  br i1 %Pivot54, label %LeafBlock44, label %NodeBlock51

NodeBlock51:                                      ; preds = %NodeBlock53
  %Pivot52 = icmp slt i8 %32, 32
  br i1 %Pivot52, label %LeafBlock47, label %LeafBlock49

LeafBlock49:                                      ; preds = %NodeBlock51
  %SwitchLeaf50 = icmp eq i8 %32, 32
  br i1 %SwitchLeaf50, label %while.body201.i, label %if.then206.i

LeafBlock47:                                      ; preds = %NodeBlock51
  %SwitchLeaf48 = icmp eq i8 %32, 13
  br i1 %SwitchLeaf48, label %while.body201.i, label %if.then206.i

LeafBlock44:                                      ; preds = %NodeBlock53
  %.off45 = add i8 %32, -9
  %SwitchLeaf46 = icmp ule i8 %.off45, 1
  br i1 %SwitchLeaf46, label %while.body201.i, label %if.then206.i

while.body201.i:                                  ; preds = %LeafBlock49, %LeafBlock47, %LeafBlock44
  %inc202.i = add i64 %q.0.i152, 1
  %exitcond238.not = icmp eq i64 %inc202.i, %cond123.i
  br i1 %exitcond238.not, label %if.end211.i, label %land.rhs196.i

if.then206.i:                                     ; preds = %LeafBlock49, %LeafBlock47, %LeafBlock44
  store i64 %q.0.i152, ptr %off
  br label %cleanup212.i

if.end211.i:                                      ; preds = %while.body201.i, %if.end189.i
  call void @llvm.lifetime.end.p0(i64 24, ptr %t352.i)
  br label %while.cond.i.backedge

cleanup212.i:                                     ; preds = %if.then206.i, %if.then187.i
  call void @llvm.lifetime.end.p0(i64 24, ptr %t352.i)
  br label %if.then

sw.default.i:                                     ; preds = %LeafBlock
  store i64 %idxprom.i, ptr %off
  br label %if.then

while.end225.i:                                   ; preds = %while.cond.i.backedge, %while.cond.i.outer.backedge
  %sp.0.i.ph.lcssa142 = phi i32 [ %sp.0.i.ph163, %while.cond.i.backedge ], [ %sp.0.i.ph.be, %while.cond.i.outer.backedge ]
  %state.0.i.lcssa = phi i32 [ %and.i, %while.cond.i.backedge ], [ %state.0.i.ph.be, %while.cond.i.outer.backedge ]
  %cmp226.not.i = icmp eq i32 %sp.0.i.ph.lcssa142, 0
  br i1 %cmp226.not.i, label %if.end230.i, label %if.then228.i

if.then228.i:                                     ; preds = %while.end225.i
  store i64 %4, ptr %off
  br label %if.then

if.end230.i:                                      ; preds = %while.end225.i
  %cmp231.not.i = icmp eq i32 %state.0.i.lcssa, 1
  br i1 %cmp231.not.i, label %sd_walk.exit, label %if.then233.i

if.then233.i:                                     ; preds = %if.end230.i, %entry
  store i64 %4, ptr %off
  br label %if.then

sd_walk.exit:                                     ; preds = %if.end230.i
  call void @llvm.lifetime.end.p0(i64 1192, ptr %c.i)
  call void @llvm.lifetime.end.p0(i64 8, ptr %xj.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %ctype.i)
  %33 = load i64, ptr %alen
  store i64 %33, ptr %ndst
  %34 = load i64, ptr %len
  store i64 %34, ptr %nev
  br label %if.end

if.then:                                          ; preds = %if.then233.i, %if.then228.i, %sw.default.i, %cleanup212.i, %cleanup.i.thread, %if.then64.i, %if.then54.i, %if.then24.i, %if.then.i
  call void @llvm.lifetime.end.p0(i64 1192, ptr %c.i)
  call void @llvm.lifetime.end.p0(i64 8, ptr %xj.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %ctype.i)
  %35 = load i64, ptr %alen
  store i64 %35, ptr %ndst
  %36 = load i64, ptr %len
  store i64 %36, ptr %nev
  %37 = load i64, ptr %off
  store i64 %37, ptr %err
  br label %if.end

if.end:                                           ; preds = %if.then, %sd_walk.exit
  %tobool.not66 = phi i64 [ 0, %if.then ], [ 1, %sd_walk.exit ]
  call void @llvm.lifetime.end.p0(i64 24, ptr %e)
  call void @llvm.lifetime.end.p0(i64 64, ptr %z)
  call void @llvm.lifetime.end.p0(i64 120, ptr %s)
  ret i64 %tobool.not66
}

declare void @llvm.lifetime.start.p0(i64, ptr)
declare void @s2_init(ptr %s, ptr %b, i64 %n, i64 %nb, ptr %ep)
declare void @llvm.lifetime.end.p0(i64, ptr)
declare i32 @s2_string_body(ptr %c, ptr %p, i64 %len, ptr %dst, ptr %outn, ptr %xp, ptr %xj, i64 %nxp)
declare i32 @od_scalar_value(ptr %c, ptr %t, ptr %o)
declare void @od_gap_recover(ptr %c, i64 %t.0.val)
declare void @llvm.trap()
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
