; The stage-2 walk as emitted, in the fragment `LeanLLVM.Semantics` models.
; Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names \
;         <stage2.c with `noinline` on every helper except s2_walk>
;
; then `opt -passes=lower-switch`, then reduced to the one `define` block.
;
; The source transform is part of the derivation, not of the file: `s2_walk`
; keeps `__attribute__((always_inline))` and inlines into the wrapper, where the
; mode is the constant `S2_VAL | S2_STR | S2_EV` and the branches that mode does
; not take fold away; the twelve helpers listed in stage2.rewrites.tsv carry
; `noinline` instead, so their bodies stay out of this text.  That boundary is
; the point: the number path's arithmetic is binary64, which this fragment has no
; operations for, and its contract is the tier composition proved in
; LeanLLVM/Refinement/JsonStage2Body.lean (`numFastEmitted_strtodSpec`).
;
; So this is the walk's text with its intra-unit helper boundaries preserved and
; the mode constant: NOT the measured object's text, which inlines the helpers.
; Measured: the fused emission of the same source is 1754 lines and
; 233 blocks and carries binary64; the body below is 937 lines and
; 165 blocks and carries none.
;
; The function's parameters are `stage2.h`'s thirteen in their ABI order,
; followed by the eight local objects the fragment cannot allocate (see
; stage2.staging.tsv): %d.i, %c.i, %ctype.i, %cst.i, %t352.i, %s, %z, %e.
; The re-indexing between the twenty-one-argument body and the thirteen-argument
; ABI is stated in LeanLLVM/Refinement/JsonStage2IR.lean, and the pin there is
; what makes this text the body those theorems run.
;
; Removed before the parser sees the text, each item with its class in
; stage2.strip.tsv, and each rewrite in stage2.rewrites.tsv; the walk's own
; guards (both reserves, their four trap arms, the thirteen-byte record) are
; body text and are kept.
;
; The inventory of this fixture's opcodes and call targets is
; stage2.inventory. `opt -passes=verify` accepts it and `leanllvm` parses it,
; both checked by the capture.

define i64 @leanllvm_json_stage2(ptr %b, i64 %n, ptr %ep, i64 %nep, ptr %xp, i64 %nxp, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err, ptr %d.i, ptr %c.i, ptr %ctype.i, ptr %cst.i, ptr %t352.i, ptr %s, ptr %z, ptr %e) {
entry:
  %ei.i = alloca i64
  %root_done.i = alloca i32
  %xj.i = alloca i64
  %outn.i = alloca i64
  call void @llvm.lifetime.start.p0(i64 120, ptr %s)
  call void @llvm.lifetime.start.p0(i64 64, ptr %z)
  call void @llvm.lifetime.start.p0(i64 24, ptr %e)
  %add = add i64 %n, 63
  %shr = lshr i64 %add, 6
  call void @s2_init(ptr %s, ptr %b, i64 %n, i64 %shr, ptr %ep)
  %nsp = getelementptr inbounds i8, ptr %s, i64 56
  store i64 %nep, ptr %nsp
  %xp1 = getelementptr inbounds i8, ptr %s, i64 72
  store ptr %xp, ptr %xp1
  %nxp2 = getelementptr inbounds i8, ptr %s, i64 80
  store i64 %nxp, ptr %nxp2
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
  %3 = load ptr, ptr %s
  %n2.i = getelementptr inbounds i8, ptr %s, i64 8
  %4 = load i64, ptr %n2.i
  %ep3.i = getelementptr inbounds i8, ptr %s, i64 48
  %5 = load ptr, ptr %ep3.i
  call void @llvm.lifetime.start.p0(i64 1192, ptr %c.i)
  %6 = getelementptr inbounds i8, ptr %c.i, i64 40
  call void @llvm.memset.p0.i64(ptr %6, i8 0, i64 1152, i1 false)
  store ptr %3, ptr %c.i
  %n6.i = getelementptr inbounds i8, ptr %c.i, i64 8
  store i64 %4, ptr %n6.i
  %ix.i = getelementptr inbounds i8, ptr %c.i, i64 16
  store ptr %5, ptr %ix.i
  %nix.i = getelementptr inbounds i8, ptr %c.i, i64 24
  store i64 %nep, ptr %nix.i
  %e7.i = getelementptr inbounds i8, ptr %c.i, i64 1112
  store ptr %e, ptr %e7.i
  call void @llvm.lifetime.start.p0(i64 520, ptr %ctype.i)
  call void @llvm.lifetime.start.p0(i64 520, ptr %cst.i)
  call void @llvm.lifetime.start.p0(i64 4, ptr %root_done.i)
  store i32 0, ptr %root_done.i
  call void @llvm.lifetime.start.p0(i64 8, ptr %xj.i)
  store i64 0, ptr %xj.i
  %invariant.gep = getelementptr i8, ptr %3, i64 -1
  %cmp.i247.not = icmp eq i64 %nep, 0
  br i1 %cmp.i247.not, label %if.then492.i, label %while.body.i.lr.ph

while.body.i.lr.ph:                               ; preds = %entry
  %k11.i = getelementptr inbounds i8, ptr %c.i, i64 32
  %h1.i.i.i51 = getelementptr inbounds i8, ptr %z, i64 24
  %gap.i = getelementptr inbounds i8, ptr %t352.i, i64 20
  %end.i = getelementptr inbounds i8, ptr %t352.i, i64 8
  %kind404.i = getelementptr inbounds i8, ptr %t352.i, i64 16
  br label %while.body.i

while.body.i:                                     ; preds = %cleanup478.i, %while.body.i.lr.ph
  %k.0.i249 = phi i64 [ 0, %while.body.i.lr.ph ], [ %k.2.i, %cleanup478.i ]
  %sp.i.0248 = phi i32 [ 0, %while.body.i.lr.ph ], [ %sp.i.1, %cleanup478.i ]
  %inc.i = add i64 %k.0.i249, 1
  %arrayidx.i = getelementptr inbounds i32, ptr %5, i64 %k.0.i249
  %7 = load i32, ptr %arrayidx.i
  %idxprom.i = zext i32 %7 to i64
  %arrayidx10.i = getelementptr inbounds i8, ptr %3, i64 %idxprom.i
  %8 = load i8, ptr %arrayidx10.i
  store i64 %inc.i, ptr %k11.i
  br label %NodeBlock21

NodeBlock21:                                      ; preds = %while.body.i
  %Pivot22 = icmp slt i8 %8, 91
  br i1 %Pivot22, label %NodeBlock5, label %NodeBlock19

NodeBlock19:                                      ; preds = %NodeBlock21
  %Pivot20 = icmp slt i8 %8, 123
  br i1 %Pivot20, label %NodeBlock11, label %NodeBlock17

NodeBlock17:                                      ; preds = %NodeBlock19
  %Pivot18 = icmp slt i8 %8, 125
  br i1 %Pivot18, label %LeafBlock13, label %LeafBlock15

LeafBlock15:                                      ; preds = %NodeBlock17
  %SwitchLeaf16 = icmp eq i8 %8, 125
  br i1 %SwitchLeaf16, label %if.then53.i, label %sw.default.i

LeafBlock13:                                      ; preds = %NodeBlock17
  %SwitchLeaf14 = icmp eq i8 %8, 123
  br i1 %SwitchLeaf14, label %if.then.i, label %sw.default.i

NodeBlock11:                                      ; preds = %NodeBlock19
  %Pivot12 = icmp slt i8 %8, 93
  br i1 %Pivot12, label %LeafBlock7, label %LeafBlock9

LeafBlock9:                                       ; preds = %NodeBlock11
  %SwitchLeaf10 = icmp eq i8 %8, 93
  br i1 %SwitchLeaf10, label %if.then53.i, label %sw.default.i

LeafBlock7:                                       ; preds = %NodeBlock11
  %SwitchLeaf8 = icmp eq i8 %8, 91
  br i1 %SwitchLeaf8, label %if.then.i, label %sw.default.i

NodeBlock5:                                       ; preds = %NodeBlock21
  %Pivot6 = icmp slt i8 %8, 44
  br i1 %Pivot6, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock5
  %Pivot = icmp slt i8 %8, 58
  br i1 %Pivot, label %LeafBlock1, label %LeafBlock3

LeafBlock3:                                       ; preds = %NodeBlock
  %SwitchLeaf4 = icmp eq i8 %8, 58
  br i1 %SwitchLeaf4, label %if.then173.i, label %sw.default.i

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i8 %8, 44
  br i1 %SwitchLeaf2, label %if.then127.i, label %sw.default.i

LeafBlock:                                        ; preds = %NodeBlock5
  %SwitchLeaf = icmp eq i8 %8, 34
  br i1 %SwitchLeaf, label %sw.bb202.i, label %sw.default.i

if.then.i:                                        ; preds = %LeafBlock13, %LeafBlock7
  %9 = load i32, ptr %root_done.i
  %call14.i = call i32 @s2_value_pos(i32 %sp.i.0248, i32 %9, ptr %ctype.i, ptr %cst.i)
  %tobool15.not.i = icmp eq i32 %call14.i, 0
  br i1 %tobool15.not.i, label %if.then16.i, label %if.end.i

if.then16.i:                                      ; preds = %if.then.i
  %off1.i.i = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i
  br label %if.then

if.end.i:                                         ; preds = %if.then.i
  %cmp19.i = icmp ugt i32 %sp.i.0248, 519
  br i1 %cmp19.i, label %if.then21.i, label %if.end24.i

if.then21.i:                                      ; preds = %if.end.i
  %off1.i.i38 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i38
  br label %if.then

if.end24.i:                                       ; preds = %if.end.i
  %cmp26.i = icmp eq i8 %8, 123
  %conv28.i = select i1 %cmp26.i, i8 1, i8 2
  %idxprom29.i = zext i32 %sp.i.0248 to i64
  %arrayidx30.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom29.i
  store i8 %conv28.i, ptr %arrayidx30.i
  %arrayidx32.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom29.i
  store i8 0, ptr %arrayidx32.i
  %inc33.i = add i32 %sp.i.0248, 1
  %conv42.i = select i1 %cmp26.i, i8 1, i8 3
  %10 = load i32, ptr %hash1.i.i
  %tobool.not.i.i = icmp eq i32 %10, 0
  br i1 %tobool.not.i.i, label %if.end.i.i, label %if.then.i.i

if.then.i.i:                                      ; preds = %if.end24.i
  %11 = load i64, ptr %h1.i.i.i51
  %conv.i.i.i = zext i8 %conv42.i to i64
  %xor.us.i.i.i = xor i64 %11, %conv.i.i.i
  %12 = mul i64 %xor.us.i.i.i, -2358710677322311239
  %mul11.i.i.i = add i64 %12, -7046029254386353131
  store i64 %mul11.i.i.i, ptr %h1.i.i.i51
  br label %cleanup478.i

if.end.i.i:                                       ; preds = %if.end24.i
  %o.val.i.i = load i64, ptr %len
  %o.val11.i.i = load i64, ptr %cap
  %add.i.i.i = add i64 %o.val.i.i, 1
  %cmp.not.i.i.i = icmp ugt i64 %add.i.i.i, %o.val11.i.i
  br i1 %cmp.not.i.i.i, label %if.end.i.i.i, label %out_reserve.exit.i.i

if.end.i.i.i:                                     ; preds = %if.end.i.i
  call void @llvm.trap()
  unreachable

out_reserve.exit.i.i:                             ; preds = %if.end.i.i
  %13 = load ptr, ptr %z
  %add.ptr.i.i = getelementptr inbounds i8, ptr %13, i64 %o.val.i.i
  store i8 %conv42.i, ptr %add.ptr.i.i
  store i64 %add.i.i.i, ptr %len
  br label %cleanup478.i

if.then53.i:                                      ; preds = %LeafBlock15, %LeafBlock9
  %cmp54.i = icmp eq i32 %sp.i.0248, 0
  br i1 %cmp54.i, label %if.then56.i, label %if.end59.i

if.then56.i:                                      ; preds = %if.then53.i
  %off1.i.i41 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i41
  br label %if.then

if.end59.i:                                       ; preds = %if.then53.i
  %sub.i = add i32 %sp.i.0248, -1
  %cmp61.i = icmp eq i8 %8, 125
  %conv64.i = select i1 %cmp61.i, i32 1, i32 2
  %idxprom65.i = zext i32 %sub.i to i64
  %arrayidx66.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom65.i
  %14 = load i8, ptr %arrayidx66.i
  %conv67.i = zext i8 %14 to i32
  %cmp69.not.i = icmp eq i32 %conv64.i, %conv67.i
  br i1 %cmp69.not.i, label %if.end74.i, label %if.then71.i

if.then71.i:                                      ; preds = %if.end59.i
  %off1.i.i43 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i43
  br label %if.then

if.end74.i:                                       ; preds = %if.end59.i
  %arrayidx76.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom65.i
  %15 = load i8, ptr %arrayidx76.i
  br i1 %cmp61.i, label %cond.true.i, label %cond.end.i

cond.true.i:                                      ; preds = %if.end74.i
  br label %NodeBlock27

NodeBlock27:                                      ; preds = %cond.true.i
  %Pivot28 = icmp slt i8 %15, 3
  br i1 %Pivot28, label %LeafBlock23, label %LeafBlock25

LeafBlock25:                                      ; preds = %NodeBlock27
  %SwitchLeaf26 = icmp eq i8 %15, 3
  br i1 %SwitchLeaf26, label %if.then109.i, label %cleanup104.i

LeafBlock23:                                      ; preds = %NodeBlock27
  %SwitchLeaf24 = icmp eq i8 %15, 0
  br i1 %SwitchLeaf24, label %if.then109.i, label %cleanup104.i

cond.end.i:                                       ; preds = %if.end74.i
  %16 = icmp ult i8 %15, 2
  br i1 %16, label %if.then109.i, label %cleanup104.i

cleanup104.i:                                     ; preds = %LeafBlock25, %LeafBlock23, %cond.end.i
  %off1.i.i45 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i45
  br label %if.then

if.then109.i:                                     ; preds = %LeafBlock25, %LeafBlock23, %cond.end.i
  %conv115.i = phi i8 [ 2, %LeafBlock23 ], [ 2, %LeafBlock25 ], [ 4, %cond.end.i ]
  call void @s2_after_value(i32 %sub.i, ptr %root_done.i, ptr %ctype.i, ptr %cst.i)
  %17 = load i32, ptr %hash1.i.i
  %tobool.not.i.i49 = icmp eq i32 %17, 0
  br i1 %tobool.not.i.i49, label %if.end.i.i55, label %if.then.i.i50

if.then.i.i50:                                    ; preds = %if.then109.i
  %18 = load i64, ptr %h1.i.i.i51
  %conv.i.i.i52 = zext i8 %conv115.i to i64
  %xor.us.i.i.i53 = xor i64 %18, %conv.i.i.i52
  %19 = mul i64 %xor.us.i.i.i53, -2358710677322311239
  %mul11.i.i.i54 = add i64 %19, -7046029254386353131
  store i64 %mul11.i.i.i54, ptr %h1.i.i.i51
  br label %cleanup478.i

if.end.i.i55:                                     ; preds = %if.then109.i
  %o.val.i.i56 = load i64, ptr %len
  %o.val11.i.i57 = load i64, ptr %cap
  %add.i.i.i58 = add i64 %o.val.i.i56, 1
  %cmp.not.i.i.i59 = icmp ugt i64 %add.i.i.i58, %o.val11.i.i57
  br i1 %cmp.not.i.i.i59, label %if.end.i.i.i64, label %out_reserve.exit.i.i60

if.end.i.i.i64:                                   ; preds = %if.end.i.i55
  call void @llvm.trap()
  unreachable

out_reserve.exit.i.i60:                           ; preds = %if.end.i.i55
  %20 = load ptr, ptr %z
  %add.ptr.i.i61 = getelementptr inbounds i8, ptr %20, i64 %o.val.i.i56
  store i8 %conv115.i, ptr %add.ptr.i.i61
  store i64 %add.i.i.i58, ptr %len
  br label %cleanup478.i

if.then127.i:                                     ; preds = %LeafBlock1
  %cmp128.i = icmp eq i32 %sp.i.0248, 0
  br i1 %cmp128.i, label %if.then130.i, label %if.end133.i

if.then130.i:                                     ; preds = %if.then127.i
  %off1.i.i66 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i66
  br label %if.then

if.end133.i:                                      ; preds = %if.then127.i
  %sub135.i = add i32 %sp.i.0248, -1
  %idxprom136.i = zext i32 %sub135.i to i64
  %arrayidx137.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom136.i
  %21 = load i8, ptr %arrayidx137.i
  %cmp139.i = icmp eq i8 %21, 1
  %arrayidx143.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom136.i
  %22 = load i8, ptr %arrayidx143.i
  br i1 %cmp139.i, label %if.then141.i, label %if.else153.i

if.then141.i:                                     ; preds = %if.end133.i
  %cmp145.not.i = icmp eq i8 %22, 3
  br i1 %cmp145.not.i, label %if.end150.i, label %if.then147.i

if.then147.i:                                     ; preds = %if.then141.i
  %off1.i.i68 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i68
  br label %if.then

if.end150.i:                                      ; preds = %if.then141.i
  store i8 4, ptr %arrayidx143.i
  br label %cleanup478.i

if.else153.i:                                     ; preds = %if.end133.i
  %cmp157.not.i = icmp eq i8 %22, 1
  br i1 %cmp157.not.i, label %if.end162.i, label %if.then159.i

if.then159.i:                                     ; preds = %if.else153.i
  %off1.i.i70 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i70
  br label %if.then

if.end162.i:                                      ; preds = %if.else153.i
  store i8 2, ptr %arrayidx143.i
  br label %cleanup478.i

if.then173.i:                                     ; preds = %LeafBlock3
  %cmp174.i = icmp eq i32 %sp.i.0248, 0
  br i1 %cmp174.i, label %if.then176.i, label %if.end179.i

if.then176.i:                                     ; preds = %if.then173.i
  %off1.i.i72 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i72
  br label %if.then

if.end179.i:                                      ; preds = %if.then173.i
  %sub181.i = add i32 %sp.i.0248, -1
  %idxprom182.i = zext i32 %sub181.i to i64
  %arrayidx183.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom182.i
  %23 = load i8, ptr %arrayidx183.i
  %cmp185.not.i = icmp eq i8 %23, 1
  br i1 %cmp185.not.i, label %lor.lhs.false.i, label %if.then192.i

lor.lhs.false.i:                                  ; preds = %if.end179.i
  %arrayidx188.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom182.i
  %24 = load i8, ptr %arrayidx188.i
  %cmp190.not.i = icmp eq i8 %24, 1
  br i1 %cmp190.not.i, label %if.end195.i, label %if.then192.i

if.then192.i:                                     ; preds = %lor.lhs.false.i, %if.end179.i
  %off1.i.i74 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i74
  br label %if.then

if.end195.i:                                      ; preds = %lor.lhs.false.i
  store i8 2, ptr %arrayidx188.i
  br label %cleanup478.i

sw.bb202.i:                                       ; preds = %LeafBlock
  %cmp203.not.i = icmp ult i64 %inc.i, %nep
  br i1 %cmp203.not.i, label %if.end207.i, label %if.then205.i

if.then205.i:                                     ; preds = %sw.bb202.i
  %off1.i.i76 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %4, ptr %off1.i.i76
  br label %if.then

if.end207.i:                                      ; preds = %sw.bb202.i
  %inc208.i = add i64 %k.0.i249, 2
  %arrayidx209.i = getelementptr inbounds i32, ptr %5, i64 %inc.i
  %25 = load i32, ptr %arrayidx209.i
  store i64 %inc208.i, ptr %k11.i
  %conv211.i = zext i32 %25 to i64
  %cmp212.not.i = icmp ugt i64 %4, %conv211.i
  br i1 %cmp212.not.i, label %if.then219.i, label %if.then214.i

if.then214.i:                                     ; preds = %if.end207.i
  %off1.i.i78 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %4, ptr %off1.i.i78
  br label %if.then

if.then219.i:                                     ; preds = %if.end207.i
  %26 = load i32, ptr %root_done.i
  %call222.i = call i32 @s2_value_pos(i32 %sp.i.0248, i32 %26, ptr %ctype.i, ptr %cst.i)
  %cmp223.not.i = icmp eq i32 %sp.i.0248, 0
  br i1 %cmp223.not.i, label %if.end245.i, label %land.lhs.true.i

land.lhs.true.i:                                  ; preds = %if.then219.i
  %sub225.i = add i32 %sp.i.0248, -1
  %idxprom226.i = zext i32 %sub225.i to i64
  %arrayidx227.i = getelementptr inbounds i8, ptr %ctype.i, i64 %idxprom226.i
  %27 = load i8, ptr %arrayidx227.i
  %cmp229.i = icmp eq i8 %27, 1
  br i1 %cmp229.i, label %if.then231.i, label %if.end245.i

if.then231.i:                                     ; preds = %land.lhs.true.i
  %arrayidx235.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom226.i
  %28 = load i8, ptr %arrayidx235.i
  %29 = and i8 %28, -5
  %or.cond.i = icmp eq i8 %29, 0
  br label %if.end245.i

if.end245.i:                                      ; preds = %if.then231.i, %land.lhs.true.i, %if.then219.i
  %key.1.i = phi i1 [ %or.cond.i, %if.then231.i ], [ false, %land.lhs.true.i ], [ false, %if.then219.i ]
  %tobool248.i = icmp ne i32 %call222.i, 0
  %or.cond523.i = select i1 %key.1.i, i1 true, i1 %tobool248.i
  br i1 %or.cond523.i, label %if.end256.i, label %if.then249.i

if.then249.i:                                     ; preds = %if.end245.i
  %off1.i.i80 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i80
  br label %if.then

if.end256.i:                                      ; preds = %if.end245.i
  %30 = xor i64 %idxprom.i, -1
  %sub260.i = add i64 %conv211.i, %30
  call void @llvm.lifetime.start.p0(i64 8, ptr %outn.i)
  store i64 0, ptr %outn.i
  %add.i = add i64 %sub260.i, 64
  %z.val36 = load i64, ptr %alen
  %z.val37 = load i64, ptr %acap
  %add.i82 = add i64 %add.i, %z.val36
  %cmp.not.i = icmp ugt i64 %add.i82, %z.val37
  br i1 %cmp.not.i, label %if.end.i83, label %z_arena_reserve.exit

if.end.i83:                                       ; preds = %if.end256.i
  call void @llvm.trap()
  unreachable

z_arena_reserve.exit:                             ; preds = %if.end256.i
  %31 = load ptr, ptr %ar
  %add.ptr.i = getelementptr inbounds i8, ptr %31, i64 %z.val36
  %add.ptr271.i = getelementptr inbounds i8, ptr %arrayidx10.i, i64 1
  %call272.i = call i32 @s2_string_body(ptr %c.i, ptr %add.ptr271.i, i64 %sub260.i, ptr %add.ptr.i, ptr %outn.i, ptr %xp, ptr %xj.i, i64 %nxp)
  br label %NodeBlock31

NodeBlock31:                                      ; preds = %z_arena_reserve.exit
  %Pivot32 = icmp slt i32 %call272.i, 1
  br i1 %Pivot32, label %cleanup339.critedge.i, label %LeafBlock29

LeafBlock29:                                      ; preds = %NodeBlock31
  %SwitchLeaf30 = icmp eq i32 %call272.i, 1
  br i1 %SwitchLeaf30, label %if.then281.i, label %if.else285.i

if.then281.i:                                     ; preds = %LeafBlock29
  %add283.i = add i32 %7, 1
  %conv284.i = zext i32 %add283.i to i64
  %or.i = or i64 %conv284.i, -9223372036854775808
  br label %if.end290.i

if.else285.i:                                     ; preds = %LeafBlock29
  %32 = load i64, ptr %outn.i
  %add289.i = add i64 %z.val36, %32
  store i64 %add289.i, ptr %alen
  br label %if.end290.i

if.end290.i:                                      ; preds = %if.else285.i, %if.then281.i
  %conv286.i.sink.in = phi i64 [ %sub260.i, %if.then281.i ], [ %32, %if.else285.i ]
  %.sink = phi i64 [ %or.i, %if.then281.i ], [ %z.val36, %if.else285.i ]
  %z.val = load i64, ptr %len
  %z.val33 = load i64, ptr %cap
  %add.i84 = add i64 %z.val, 13
  %cmp.not.i85 = icmp ugt i64 %add.i84, %z.val33
  br i1 %cmp.not.i85, label %if.end.i86, label %if.then328.i

if.end.i86:                                       ; preds = %if.end290.i
  call void @llvm.trap()
  unreachable

if.then328.i:                                     ; preds = %if.end290.i
  %conv286.i.sink = trunc i64 %conv286.i.sink.in to i32
  %33 = load ptr, ptr %z
  %add.ptr297.i = getelementptr inbounds i8, ptr %33, i64 %z.val
  %conv300.i = select i1 %key.1.i, i8 5, i8 6
  store i8 %conv300.i, ptr %add.ptr297.i
  %add.ptr302.i = getelementptr inbounds i8, ptr %add.ptr297.i, i64 1
  store i32 %conv286.i.sink, ptr %add.ptr302.i
  %add.ptr304.i = getelementptr inbounds i8, ptr %add.ptr297.i, i64 5
  store i64 %.sink, ptr %add.ptr304.i
  store i64 %add.i84, ptr %len
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn.i)
  br i1 %key.1.i, label %if.then330.i, label %if.else334.i

if.then330.i:                                     ; preds = %if.then328.i
  %sub331.i = add i32 %sp.i.0248, -1
  %idxprom332.i = zext i32 %sub331.i to i64
  %arrayidx333.i = getelementptr inbounds i8, ptr %cst.i, i64 %idxprom332.i
  store i8 1, ptr %arrayidx333.i
  br label %cleanup478.i

if.else334.i:                                     ; preds = %if.then328.i
  call void @s2_after_value(i32 %sp.i.0248, ptr %root_done.i, ptr %ctype.i, ptr %cst.i)
  br label %cleanup478.i

cleanup339.critedge.i:                            ; preds = %NodeBlock31
  call void @llvm.lifetime.end.p0(i64 8, ptr %outn.i)
  br label %if.then

sw.default.i:                                     ; preds = %LeafBlock15, %LeafBlock13, %LeafBlock9, %LeafBlock7, %LeafBlock3, %LeafBlock1, %LeafBlock
  %cmp343.i = icmp ult i64 %inc.i, %nep
  br i1 %cmp343.i, label %cond.true345.i, label %cond.end349.i

cond.true345.i:                                   ; preds = %sw.default.i
  %arrayidx346.i = getelementptr inbounds i32, ptr %5, i64 %inc.i
  %34 = load i32, ptr %arrayidx346.i
  %conv347.i = zext i32 %34 to i64
  br label %cond.end349.i

cond.end349.i:                                    ; preds = %cond.true345.i, %sw.default.i
  %cond350.i = phi i64 [ %conv347.i, %cond.true345.i ], [ %4, %sw.default.i ]
  call void @llvm.lifetime.start.p0(i64 24, ptr %t352.i)
  store i64 %idxprom.i, ptr %t352.i
  store i32 1, ptr %gap.i
  %cmp355.i = icmp ugt i64 %cond350.i, %idxprom.i
  br i1 %cmp355.i, label %land.lhs.true357.i, label %if.end372.i

land.lhs.true357.i:                               ; preds = %cond.end349.i
  %gep = getelementptr i8, ptr %invariant.gep, i64 %cond350.i
  %35 = load i8, ptr %gep
  br label %NodeBlock41

NodeBlock41:                                      ; preds = %land.lhs.true357.i
  %Pivot42 = icmp slt i8 %35, 13
  br i1 %Pivot42, label %LeafBlock33, label %NodeBlock39

NodeBlock39:                                      ; preds = %NodeBlock41
  %Pivot40 = icmp slt i8 %35, 32
  br i1 %Pivot40, label %LeafBlock35, label %LeafBlock37

LeafBlock37:                                      ; preds = %NodeBlock39
  %SwitchLeaf38 = icmp eq i8 %35, 32
  br i1 %SwitchLeaf38, label %land.rhs.i.preheader, label %if.end372.i

LeafBlock35:                                      ; preds = %NodeBlock39
  %SwitchLeaf36 = icmp eq i8 %35, 13
  br i1 %SwitchLeaf36, label %land.rhs.i.preheader, label %if.end372.i

LeafBlock33:                                      ; preds = %NodeBlock41
  %.off = add i8 %35, -9
  %SwitchLeaf34 = icmp ule i8 %.off, 1
  br i1 %SwitchLeaf34, label %land.rhs.i.preheader, label %if.end372.i

land.rhs.i.preheader:                             ; preds = %LeafBlock37, %LeafBlock35, %LeafBlock33
  br label %land.rhs.i

land.rhs.i:                                       ; preds = %while.body370.i, %land.rhs.i.preheader
  %ee.0.i238 = phi i64 [ %inc371.i, %while.body370.i ], [ %idxprom.i, %land.rhs.i.preheader ]
  %arrayidx367.i = getelementptr inbounds i8, ptr %3, i64 %ee.0.i238
  %36 = load i8, ptr %arrayidx367.i
  br label %NodeBlock52

NodeBlock52:                                      ; preds = %land.rhs.i
  %Pivot53 = icmp slt i8 %36, 13
  br i1 %Pivot53, label %LeafBlock43, label %NodeBlock50

NodeBlock50:                                      ; preds = %NodeBlock52
  %Pivot51 = icmp slt i8 %36, 32
  br i1 %Pivot51, label %LeafBlock46, label %LeafBlock48

LeafBlock48:                                      ; preds = %NodeBlock50
  %SwitchLeaf49 = icmp eq i8 %36, 32
  br i1 %SwitchLeaf49, label %if.end372.i, label %while.body370.i

LeafBlock46:                                      ; preds = %NodeBlock50
  %SwitchLeaf47 = icmp eq i8 %36, 13
  br i1 %SwitchLeaf47, label %if.end372.i, label %while.body370.i

LeafBlock43:                                      ; preds = %NodeBlock52
  %.off44 = add i8 %36, -9
  %SwitchLeaf45 = icmp ule i8 %.off44, 1
  br i1 %SwitchLeaf45, label %if.end372.i, label %while.body370.i

while.body370.i:                                  ; preds = %LeafBlock48, %LeafBlock46, %LeafBlock43
  %inc371.i = add i64 %ee.0.i238, 1
  %exitcond.not = icmp eq i64 %inc371.i, %cond350.i
  br i1 %exitcond.not, label %if.end372.i, label %land.rhs.i

if.end372.i:                                      ; preds = %LeafBlock48, %LeafBlock46, %LeafBlock43, %LeafBlock37, %LeafBlock35, %LeafBlock33, %while.body370.i, %cond.end349.i
  %ee.1.i = phi i64 [ %idxprom.i, %cond.end349.i ], [ %cond350.i, %while.body370.i ], [ %ee.0.i238, %LeafBlock43 ], [ %ee.0.i238, %LeafBlock46 ], [ %ee.0.i238, %LeafBlock48 ], [ %cond350.i, %LeafBlock33 ], [ %cond350.i, %LeafBlock35 ], [ %cond350.i, %LeafBlock37 ]
  store i64 %ee.1.i, ptr %end.i
  %cmp376.i = icmp eq i8 %8, 45
  %37 = add i8 %8, -48
  %or.cond524.i = icmp ult i8 %37, 10
  %or.cond677.i = or i1 %cmp376.i, %or.cond524.i
  br i1 %or.cond677.i, label %if.then413.i, label %if.else387.i

if.else387.i:                                     ; preds = %if.end372.i
  br label %NodeBlock62

NodeBlock62:                                      ; preds = %if.else387.i
  %Pivot63 = icmp slt i8 %8, 110
  br i1 %Pivot63, label %LeafBlock54, label %NodeBlock60

NodeBlock60:                                      ; preds = %NodeBlock62
  %Pivot61 = icmp slt i8 %8, 116
  br i1 %Pivot61, label %LeafBlock56, label %LeafBlock58

LeafBlock58:                                      ; preds = %NodeBlock60
  %SwitchLeaf59 = icmp eq i8 %8, 116
  br i1 %SwitchLeaf59, label %if.then413.i, label %if.else405.i

LeafBlock56:                                      ; preds = %NodeBlock60
  %SwitchLeaf57 = icmp eq i8 %8, 110
  br i1 %SwitchLeaf57, label %if.then403.i, label %if.else405.i

LeafBlock54:                                      ; preds = %NodeBlock62
  %SwitchLeaf55 = icmp eq i8 %8, 102
  br i1 %SwitchLeaf55, label %if.then397.i, label %if.else405.i

if.then397.i:                                     ; preds = %LeafBlock54
  br label %if.then413.i

if.then403.i:                                     ; preds = %LeafBlock56
  br label %if.then413.i

if.else405.i:                                     ; preds = %LeafBlock58, %LeafBlock56, %LeafBlock54
  br label %if.then413.i

if.then413.i:                                     ; preds = %LeafBlock58, %if.else405.i, %if.then403.i, %if.then397.i, %if.end372.i
  %.sink372 = phi i32 [ 0, %if.else405.i ], [ 10, %if.then403.i ], [ 9, %if.then397.i ], [ 7, %if.end372.i ], [ 8, %LeafBlock58 ]
  store i32 %.sink372, ptr %kind404.i
  %38 = load i32, ptr %root_done.i
  %call416.i = call i32 @s2_value_pos(i32 %sp.i.0248, i32 %38, ptr %ctype.i, ptr %cst.i)
  %tobool417.not.i = icmp eq i32 %call416.i, 0
  br i1 %tobool417.not.i, label %if.then418.i, label %if.then425.i

if.then418.i:                                     ; preds = %if.then413.i
  %off1.i.i91 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i.i91
  br label %cleanup474.i

if.then425.i:                                     ; preds = %if.then413.i
  %call427.i = call i32 @od_scalar_value(ptr %c.i, ptr %t352.i, ptr %z)
  %tobool428.not.i = icmp eq i32 %call427.i, 0
  br i1 %tobool428.not.i, label %if.then432.i, label %if.then447.i

if.then432.i:                                     ; preds = %if.then425.i
  br i1 %cmp343.i, label %cond.true.i106, label %cond.end.i96

cond.true.i106:                                   ; preds = %if.then432.i
  %arrayidx.i108 = getelementptr inbounds i32, ptr %5, i64 %inc.i
  %39 = load i32, ptr %arrayidx.i108
  %conv.i = zext i32 %39 to i64
  br label %cond.end.i96

cond.end.i96:                                     ; preds = %cond.true.i106, %if.then432.i
  %cond.i = phi i64 [ %conv.i, %cond.true.i106 ], [ %4, %if.then432.i ]
  %cmp310.i = icmp ugt i64 %cond.i, %idxprom.i
  br i1 %cmp310.i, label %land.rhs.i103, label %while.end.i

land.rhs.i103:                                    ; preds = %while.body.i104, %cond.end.i96
  %ee.011.i = phi i64 [ %inc.i105, %while.body.i104 ], [ %idxprom.i, %cond.end.i96 ]
  %arrayidx5.i = getelementptr inbounds i8, ptr %3, i64 %ee.011.i
  %40 = load i8, ptr %arrayidx5.i
  br label %NodeBlock73

NodeBlock73:                                      ; preds = %land.rhs.i103
  %Pivot74 = icmp slt i8 %40, 13
  br i1 %Pivot74, label %LeafBlock64, label %NodeBlock71

NodeBlock71:                                      ; preds = %NodeBlock73
  %Pivot72 = icmp slt i8 %40, 32
  br i1 %Pivot72, label %LeafBlock67, label %LeafBlock69

LeafBlock69:                                      ; preds = %NodeBlock71
  %SwitchLeaf70 = icmp eq i8 %40, 32
  br i1 %SwitchLeaf70, label %while.end.i, label %while.body.i104

LeafBlock67:                                      ; preds = %NodeBlock71
  %SwitchLeaf68 = icmp eq i8 %40, 13
  br i1 %SwitchLeaf68, label %while.end.i, label %while.body.i104

LeafBlock64:                                      ; preds = %NodeBlock73
  %.off65 = add i8 %40, -9
  %SwitchLeaf66 = icmp ule i8 %.off65, 1
  br i1 %SwitchLeaf66, label %while.end.i, label %while.body.i104

while.body.i104:                                  ; preds = %LeafBlock69, %LeafBlock67, %LeafBlock64
  %inc.i105 = add i64 %ee.011.i, 1
  %exitcond.not.i = icmp eq i64 %inc.i105, %cond.i
  br i1 %exitcond.not.i, label %cleanup474.i, label %land.rhs.i103

while.end.i:                                      ; preds = %LeafBlock69, %LeafBlock67, %LeafBlock64, %cond.end.i96
  %ee.0.lcssa.i = phi i64 [ %idxprom.i, %cond.end.i96 ], [ %ee.011.i, %LeafBlock64 ], [ %ee.011.i, %LeafBlock67 ], [ %ee.011.i, %LeafBlock69 ]
  %cmp6.i = icmp eq i64 %ee.0.lcssa.i, %cond.i
  br i1 %cmp6.i, label %cleanup474.i, label %if.end.i97

if.end.i97:                                       ; preds = %while.end.i
  %41 = load i8, ptr %arrayidx10.i
  %cmp11.i = icmp eq i8 %41, 45
  %42 = add i8 %41, -48
  %or.cond.i98 = icmp ult i8 %42, 10
  %or.cond127.i = or i1 %cmp11.i, %or.cond.i98
  br i1 %or.cond127.i, label %if.then19.i, label %if.else.i

if.then19.i:                                      ; preds = %if.end.i97
  call void @llvm.lifetime.start.p0(i64 8, ptr %d.i)
  call void @llvm.lifetime.start.p0(i64 8, ptr %ei.i)
  %sub.i99 = sub i64 %ee.0.lcssa.i, %idxprom.i
  %call23.i = call i32 @num_fast_el1(ptr %arrayidx10.i, i64 %sub.i99, ptr %d.i, ptr %ei.i)
  %tobool24.not.not.i = icmp eq i32 %call23.i, 0
  br i1 %tobool24.not.not.i, label %if.then25.i, label %if.end67.critedge.i

if.then25.i:                                      ; preds = %if.then19.i
  %43 = load i64, ptr %ei.i
  %add.i100 = add i64 %43, %idxprom.i
  %off1.i.i101 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %add.i100, ptr %off1.i.i101
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei.i)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d.i)
  br label %cleanup474.i

if.else.i:                                        ; preds = %if.end.i97
  br label %NodeBlock83

NodeBlock83:                                      ; preds = %if.else.i
  %Pivot84 = icmp slt i8 %41, 110
  br i1 %Pivot84, label %LeafBlock75, label %NodeBlock81

NodeBlock81:                                      ; preds = %NodeBlock83
  %Pivot82 = icmp slt i8 %41, 116
  br i1 %Pivot82, label %LeafBlock77, label %LeafBlock79

LeafBlock79:                                      ; preds = %NodeBlock81
  %SwitchLeaf80 = icmp eq i8 %41, 116
  br i1 %SwitchLeaf80, label %if.end48.i, label %if.else43.i

LeafBlock77:                                      ; preds = %NodeBlock81
  %SwitchLeaf78 = icmp eq i8 %41, 110
  br i1 %SwitchLeaf78, label %if.then42.i, label %if.else43.i

LeafBlock75:                                      ; preds = %NodeBlock83
  %SwitchLeaf76 = icmp eq i8 %41, 102
  br i1 %SwitchLeaf76, label %if.then37.i, label %if.else43.i

if.then37.i:                                      ; preds = %LeafBlock75
  br label %if.end48.i

if.then42.i:                                      ; preds = %LeafBlock77
  br label %if.end48.i

if.else43.i:                                      ; preds = %LeafBlock79, %LeafBlock77, %LeafBlock75
  %off1.i129.i = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %idxprom.i, ptr %off1.i129.i
  br label %cleanup474.i

if.end48.i:                                       ; preds = %LeafBlock79, %if.then42.i, %if.then37.i
  %lit.0.i = phi ptr [ null, %if.then37.i ], [ null, %if.then42.i ], [ null, %LeafBlock79 ]
  %ln.0.i = phi i64 [ 5, %if.then37.i ], [ 4, %if.then42.i ], [ 4, %LeafBlock79 ]
  %sub54.i = sub i64 %ee.0.lcssa.i, %idxprom.i
  %cond.i.i.min = icmp ult i64 %sub54.i, %ln.0.i
  %cond.i.i = select i1 %cond.i.i.min, i64 %sub54.i, i64 %ln.0.i
  %cmp3.not28.not.i.i = icmp eq i64 %ee.0.lcssa.i, %idxprom.i
  br i1 %cmp3.not28.not.i.i, label %for.end.i.i, label %for.body.i.i

for.body.i.i:                                     ; preds = %for.inc.i.i, %if.end48.i
  %i.029.i.i = phi i64 [ %inc.i.i, %for.inc.i.i ], [ 0, %if.end48.i ]
  %arrayidx.i.i = getelementptr inbounds i8, ptr %arrayidx10.i, i64 %i.029.i.i
  %44 = load i8, ptr %arrayidx.i.i
  %arrayidx6.i.i = getelementptr inbounds i8, ptr %lit.0.i, i64 %i.029.i.i
  %45 = load i8, ptr %arrayidx6.i.i
  %cmp8.not.i.i = icmp eq i8 %44, %45
  br i1 %cmp8.not.i.i, label %for.inc.i.i, label %if.then57.i

for.inc.i.i:                                      ; preds = %for.body.i.i
  %inc.i.i = add i64 %i.029.i.i, 1
  %exitcond.not.i.i = icmp eq i64 %inc.i.i, %cond.i.i
  br i1 %exitcond.not.i.i, label %for.end.i.i, label %for.body.i.i

for.end.i.i:                                      ; preds = %for.inc.i.i, %if.end48.i
  %cmp11.not.i.i = icmp eq i64 %sub54.i, %ln.0.i
  br i1 %cmp11.not.i.i, label %if.end67.i, label %if.then57.i

if.then57.i:                                      ; preds = %for.end.i.i, %for.body.i.i
  %ei49.0.ph.i = phi i64 [ %cond.i.i, %for.end.i.i ], [ %i.029.i.i, %for.body.i.i ]
  %add60.i = add i64 %ei49.0.ph.i, %idxprom.i
  %off1.i131.i = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %add60.i, ptr %off1.i131.i
  br label %cleanup474.i

if.end67.critedge.i:                              ; preds = %if.then19.i
  call void @llvm.lifetime.end.p0(i64 8, ptr %ei.i)
  call void @llvm.lifetime.end.p0(i64 8, ptr %d.i)
  br label %if.end67.i

if.end67.i:                                       ; preds = %if.end67.critedge.i, %for.end.i.i
  %cmp6919.i = icmp ult i64 %ee.0.lcssa.i, %cond.i
  br i1 %cmp6919.i, label %land.rhs71.i, label %while.end78.i

land.rhs71.i:                                     ; preds = %while.body76.i, %if.end67.i
  %s2.020.i = phi i64 [ %inc77.i, %while.body76.i ], [ %ee.0.lcssa.i, %if.end67.i ]
  %arrayidx72.i = getelementptr inbounds i8, ptr %3, i64 %s2.020.i
  %46 = load i8, ptr %arrayidx72.i
  br label %NodeBlock94

NodeBlock94:                                      ; preds = %land.rhs71.i
  %Pivot95 = icmp slt i8 %46, 13
  br i1 %Pivot95, label %LeafBlock85, label %NodeBlock92

NodeBlock92:                                      ; preds = %NodeBlock94
  %Pivot93 = icmp slt i8 %46, 32
  br i1 %Pivot93, label %LeafBlock88, label %LeafBlock90

LeafBlock90:                                      ; preds = %NodeBlock92
  %SwitchLeaf91 = icmp eq i8 %46, 32
  br i1 %SwitchLeaf91, label %while.body76.i, label %while.end78.i

LeafBlock88:                                      ; preds = %NodeBlock92
  %SwitchLeaf89 = icmp eq i8 %46, 13
  br i1 %SwitchLeaf89, label %while.body76.i, label %while.end78.i

LeafBlock85:                                      ; preds = %NodeBlock94
  %.off86 = add i8 %46, -9
  %SwitchLeaf87 = icmp ule i8 %.off86, 1
  br i1 %SwitchLeaf87, label %while.body76.i, label %while.end78.i

while.body76.i:                                   ; preds = %LeafBlock90, %LeafBlock88, %LeafBlock85
  %inc77.i = add i64 %s2.020.i, 1
  %exitcond24.not.i = icmp eq i64 %inc77.i, %cond.i
  br i1 %exitcond24.not.i, label %while.end78.i, label %land.rhs71.i

while.end78.i:                                    ; preds = %LeafBlock90, %LeafBlock88, %LeafBlock85, %while.body76.i, %if.end67.i
  %s2.0.lcssa.i = phi i64 [ %ee.0.lcssa.i, %if.end67.i ], [ %cond.i, %while.body76.i ], [ %s2.020.i, %LeafBlock85 ], [ %s2.020.i, %LeafBlock88 ], [ %s2.020.i, %LeafBlock90 ]
  %off1.i137.i = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %s2.0.lcssa.i, ptr %off1.i137.i
  br label %cleanup474.i

if.then447.i:                                     ; preds = %if.then425.i
  call void @s2_after_value(i32 %sp.i.0248, ptr %root_done.i, ptr %ctype.i, ptr %cst.i)
  %cmp451.i = icmp ult i64 %ee.1.i, %cond350.i
  br i1 %cmp451.i, label %land.rhs457.i, label %if.end473.i

land.rhs457.i:                                    ; preds = %while.body462.i, %if.then447.i
  %q.0.i246 = phi i64 [ %inc463.i, %while.body462.i ], [ %ee.1.i, %if.then447.i ]
  %arrayidx458.i = getelementptr inbounds i8, ptr %3, i64 %q.0.i246
  %47 = load i8, ptr %arrayidx458.i
  br label %NodeBlock105

NodeBlock105:                                     ; preds = %land.rhs457.i
  %Pivot106 = icmp slt i8 %47, 13
  br i1 %Pivot106, label %LeafBlock96, label %NodeBlock103

NodeBlock103:                                     ; preds = %NodeBlock105
  %Pivot104 = icmp slt i8 %47, 32
  br i1 %Pivot104, label %LeafBlock99, label %LeafBlock101

LeafBlock101:                                     ; preds = %NodeBlock103
  %SwitchLeaf102 = icmp eq i8 %47, 32
  br i1 %SwitchLeaf102, label %while.body462.i, label %if.then467.i

LeafBlock99:                                      ; preds = %NodeBlock103
  %SwitchLeaf100 = icmp eq i8 %47, 13
  br i1 %SwitchLeaf100, label %while.body462.i, label %if.then467.i

LeafBlock96:                                      ; preds = %NodeBlock105
  %.off97 = add i8 %47, -9
  %SwitchLeaf98 = icmp ule i8 %.off97, 1
  br i1 %SwitchLeaf98, label %while.body462.i, label %if.then467.i

while.body462.i:                                  ; preds = %LeafBlock101, %LeafBlock99, %LeafBlock96
  %inc463.i = add i64 %q.0.i246, 1
  %exitcond298.not = icmp eq i64 %inc463.i, %cond350.i
  br i1 %exitcond298.not, label %if.end473.i, label %land.rhs457.i

if.then467.i:                                     ; preds = %LeafBlock101, %LeafBlock99, %LeafBlock96
  %off1.i.i113 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %q.0.i246, ptr %off1.i.i113
  br label %cleanup474.i

if.end473.i:                                      ; preds = %while.body462.i, %if.then447.i
  call void @llvm.lifetime.end.p0(i64 24, ptr %t352.i)
  br label %cleanup478.i

cleanup474.i:                                     ; preds = %if.then467.i, %while.end78.i, %if.then57.i, %if.else43.i, %if.then25.i, %while.end.i, %while.body.i104, %if.then418.i
  call void @llvm.lifetime.end.p0(i64 24, ptr %t352.i)
  br label %if.then

cleanup478.i:                                     ; preds = %if.end473.i, %if.else334.i, %if.then330.i, %if.end195.i, %if.end162.i, %if.end150.i, %out_reserve.exit.i.i60, %if.then.i.i50, %out_reserve.exit.i.i, %if.then.i.i
  %sp.i.1 = phi i32 [ %sp.i.0248, %if.end473.i ], [ %sp.i.0248, %if.end150.i ], [ %sp.i.0248, %if.end162.i ], [ %sp.i.0248, %if.end195.i ], [ %sp.i.0248, %if.else334.i ], [ %sp.i.0248, %if.then330.i ], [ %inc33.i, %if.then.i.i ], [ %inc33.i, %out_reserve.exit.i.i ], [ %sub.i, %if.then.i.i50 ], [ %sub.i, %out_reserve.exit.i.i60 ]
  %k.2.i = phi i64 [ %inc.i, %if.end473.i ], [ %inc.i, %if.end150.i ], [ %inc.i, %if.end162.i ], [ %inc.i, %if.end195.i ], [ %inc208.i, %if.else334.i ], [ %inc208.i, %if.then330.i ], [ %inc.i, %if.then.i.i ], [ %inc.i, %out_reserve.exit.i.i ], [ %inc.i, %if.then.i.i50 ], [ %inc.i, %out_reserve.exit.i.i60 ]
  %cmp.i = icmp ult i64 %k.2.i, %nep
  br i1 %cmp.i, label %while.body.i, label %if.then485.i

if.then485.i:                                     ; preds = %cleanup478.i
  %48 = icmp eq i32 %sp.i.1, 0
  br i1 %48, label %if.end490.i, label %if.then488.i

if.then488.i:                                     ; preds = %if.then485.i
  %off1.i.i115 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %4, ptr %off1.i.i115
  br label %if.then

if.end490.i:                                      ; preds = %if.then485.i
  %.pr = load i32, ptr %root_done.i
  %tobool491.not.i = icmp eq i32 %.pr, 0
  br i1 %tobool491.not.i, label %if.then492.i, label %s2_walk.exit

if.then492.i:                                     ; preds = %if.end490.i, %entry
  %off1.i.i117 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %4, ptr %off1.i.i117
  br label %if.then

s2_walk.exit:                                     ; preds = %if.end490.i
  call void @llvm.lifetime.end.p0(i64 8, ptr %xj.i)
  call void @llvm.lifetime.end.p0(i64 4, ptr %root_done.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %cst.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %ctype.i)
  call void @llvm.lifetime.end.p0(i64 1192, ptr %c.i)
  %49 = load i64, ptr %alen
  store i64 %49, ptr %ndst
  %50 = load i64, ptr %len
  store i64 %50, ptr %nev
  br label %if.end

if.then:                                          ; preds = %if.then492.i, %if.then488.i, %cleanup474.i, %cleanup339.critedge.i, %if.then249.i, %if.then214.i, %if.then205.i, %if.then192.i, %if.then176.i, %if.then159.i, %if.then147.i, %if.then130.i, %cleanup104.i, %if.then71.i, %if.then56.i, %if.then21.i, %if.then16.i
  call void @llvm.lifetime.end.p0(i64 8, ptr %xj.i)
  call void @llvm.lifetime.end.p0(i64 4, ptr %root_done.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %cst.i)
  call void @llvm.lifetime.end.p0(i64 520, ptr %ctype.i)
  call void @llvm.lifetime.end.p0(i64 1192, ptr %c.i)
  %51 = load i64, ptr %alen
  store i64 %51, ptr %ndst
  %52 = load i64, ptr %len
  store i64 %52, ptr %nev
  %off = getelementptr inbounds i8, ptr %e, i64 8
  %53 = load i64, ptr %off
  store i64 %53, ptr %err
  br label %if.end

if.end:                                           ; preds = %if.then, %s2_walk.exit
  %tobool.not151 = phi i64 [ 0, %if.then ], [ 1, %s2_walk.exit ]
  call void @llvm.lifetime.end.p0(i64 24, ptr %e)
  call void @llvm.lifetime.end.p0(i64 64, ptr %z)
  call void @llvm.lifetime.end.p0(i64 120, ptr %s)
  ret i64 %tobool.not151
}

declare void @llvm.lifetime.start.p0(i64, ptr)
declare void @s2_init(ptr %s, ptr %b, i64 %n, i64 %nb, ptr %ep)
declare void @llvm.lifetime.end.p0(i64, ptr)
declare i32 @s2_value_pos(i32 %sp, i32 %root_done, ptr %ct, ptr %cs)
declare void @s2_after_value(i32 %sp.0.val, ptr %root_done, ptr %ct, ptr %cs)
declare i32 @s2_string_body(ptr %c, ptr %p, i64 %len, ptr %dst, ptr %outn, ptr %xp, ptr %xj, i64 %nxp)
declare i32 @od_scalar_value(ptr %c, ptr %t, ptr %o)
declare void @llvm.trap()
declare i32 @num_fast_el1(ptr %p, i64 %n, ptr %out, ptr %err)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
