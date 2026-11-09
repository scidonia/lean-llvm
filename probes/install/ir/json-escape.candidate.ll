; The escape unit as emitted, in the fragment the parser reads: the
; escape-position list @leanllvm_json_escape_list, the list-driven expander's
; entry point @leanllvm_json_escape_expand, the decoder @us_dec_x it calls, and
; the out-of-line batch @xl_batch the list calls — in the emission's order.
; Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-escape.sh
;
; from kernel/json/escape.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and at the measured `-D` set (`build49.sh:19-21` plus `-DUS_EMIT4=1`), then
; reduced to those four `define` blocks.  `-fno-discard-value-names` is a naming
; flag: it names values and labels the entry block, which the parser requires,
; and the capture checks that it changes no instruction by emitting the source
; with and without it and comparing the two texts with every register name
; replaced by one placeholder.  It checks the `-D` set the same way, so a
; configuration the unit does not consult is recorded as such rather than
; assumed.
;
; Every parameter of every function is the source's own name, so the capture
; renames none.  Two headers below carry one parameter more than the source's
; list: the table base the rewrite appends.
;
; The table read is rewritten, because the fragment has no module-level
; globals.  @us_dec_x's
;
;   getelementptr inbounds nuw [256 x i8], ptr @UJ_UNESC, i64 0, i64 %idxprom.i
;
; becomes
;
;   getelementptr inbounds i8, ptr %tab, i64 %idxprom.i
;
; and %tab is appended to the parameter list of the bodies that read or pass it
; — @us_dec_x, and @leanllvm_json_escape_expand, which calls it.  The emitted
; form addresses @UJ_UNESC + 0 * 256 + idx * 1 and the rewritten form
; %tab + idx * 1, so the byte offset from the base is idx on both sides and only
; the base differs, which is what the record's table hypothesis supplies.  `nuw`
; is class 4's removal and is gone before the rewrite.  Each site, including the
; call that passes the base, is recorded in json-escape.table.tsv.
;
; The hex reader's four vector constants carry `poison` lanes past the four
; digits, and nothing reads past lane 3 — the class test takes the movemask
; `& 0x0F`, and the value is lane 0 of the `pmadd.wd` result — so each poisoned
; lane is written as the defined lane 0 and every replacement is a row in
; json-escape.rewrites.tsv.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-escape.strip.tsv.  The lines removed from the module carried:
;   source_filename = "kernel/json/escape.c"
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   (the attribute groups, the five callee declarations, the table's definition
;   and the module metadata nodes are recorded in json-escape.strip.tsv, where
;   they are removed; the table is recorded in json-escape.table.tsv as well)
;
; The fixture is checked as well-formed IR, not only as a text the parser reads,
; by the invocation a reader can repeat:
;
;   opt -passes=verify -disable-output json-escape.candidate.ll
;
; The fixture's own opcodes and call targets are in json-escape.inventory.
define void @leanllvm_json_escape_list(i64 %bs, i64 %ctl, i64 %im, i64 %blk0, ptr %xp, ptr %xn, ptr %carry) {
entry:
  %arrayidx1 = getelementptr inbounds i8, ptr %carry, i64 8
  %0 = load i64, ptr %carry
  %shl.i = shl i64 %bs, 1
  %or.i = or i64 %0, %shl.i
  %not.i = xor i64 %or.i, -1
  %and.i = and i64 %bs, %not.i
  %and1.i = and i64 %bs, 1
  %and2.i = and i64 %and1.i, %0
  %tobool.not.i = icmp eq i64 %and2.i, 0
  br i1 %tobool.not.i, label %if.end.i, label %if.then.i
if.then.i:
  %1 = load i64, ptr %arrayidx1
  %tobool3.not.i = icmp eq i64 %1, 0
  %and4.i = and i64 %bs, 2
  %cond.i = select i1 %tobool3.not.i, i64 1, i64 %and4.i
  %or5.i = or i64 %cond.i, %and.i
  br label %if.end.i
if.end.i:
  %e.0.i = phi i64 [ %or5.i, %if.then.i ], [ %and.i, %entry ]
  %and7.i = and i64 %shl.i, %bs
  %shl8.i = shl i64 %e.0.i, 2
  %and9.i = and i64 %shl8.i, %and7.i
  %or10.i = or i64 %and9.i, %e.0.i
  %shl11.i = shl i64 %or10.i, 2
  %and12.i = and i64 %shl11.i, %and7.i
  %or13.i = or i64 %and12.i, %or10.i
  %shl14.i = shl i64 %or13.i, 2
  %not16.i = xor i64 %or13.i, -1
  %2 = and i64 %shl14.i, %not16.i
  %and17.i = and i64 %2, %and7.i
  %cmp.not.i = icmp eq i64 %and17.i, 0
  br i1 %cmp.not.i, label %xl_lanes.exit, label %do.body.i
do.body.i:
  %e.1.i = phi i64 [ %or23.i, %do.body.i ], [ %or13.i, %if.end.i ]
  %shl21.i = shl i64 %e.1.i, 2
  %and22.i = and i64 %shl21.i, %and7.i
  %or23.i = or i64 %and22.i, %e.1.i
  %cmp24.not.i = icmp eq i64 %or23.i, %e.1.i
  br i1 %cmp24.not.i, label %xl_lanes.exit, label %do.body.i
xl_lanes.exit:
  %e.2.i = phi i64 [ %or13.i, %if.end.i ], [ %e.1.i, %do.body.i ]
  %shr.i = lshr i64 %bs, 63
  store i64 %shr.i, ptr %carry
  %shr2757.i = and i64 %e.2.i, %bs
  %and29.i = lshr i64 %shr2757.i, 63
  store i64 %and29.i, ptr %arrayidx1
  %or30.i = or i64 %e.2.i, %ctl
  %and31.i = and i64 %or30.i, %im
  %blk0.tr = trunc i64 %blk0 to i32
  %conv = shl i32 %blk0.tr, 6
  %tobool.not.i3 = icmp eq i64 %and31.i, 0
  br i1 %tobool.not.i3, label %xl_emit.exit, label %if.end.i4
if.end.i4:
  %3 = load i64, ptr %xn
  %add.ptr.i.i = getelementptr inbounds i32, ptr %xp, i64 %3
  %or.i.i.i = or i64 %and31.i, -9223372036854775808
  %4 = tail call i64 @llvm.cttz.i64(i64 %or.i.i.i, i1 true)
  %cast.i.i.i = trunc i64 %4 to i32
  %add.i.i.i = or i32 %conv, %cast.i.i.i
  store i32 %add.i.i.i, ptr %add.ptr.i.i
  %sub.i.i.i = add i64 %or.i.i.i, -1
  %and.i.i.i = and i64 %sub.i.i.i, %or.i.i.i
  %5 = tail call i64 @llvm.cttz.i64(i64 %and.i.i.i, i1 true)
  %cast1.i.i.i = trunc i64 %5 to i32
  %add2.i.i.i = or i32 %conv, %cast1.i.i.i
  %arrayidx3.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 4
  store i32 %add2.i.i.i, ptr %arrayidx3.i.i.i
  %sub4.i.i.i = add i64 %and.i.i.i, -1
  %and5.i.i.i = and i64 %sub4.i.i.i, %and.i.i.i
  %6 = tail call i64 @llvm.cttz.i64(i64 %and5.i.i.i, i1 true)
  %cast6.i.i.i = trunc i64 %6 to i32
  %add7.i.i.i = or i32 %conv, %cast6.i.i.i
  %arrayidx8.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 8
  store i32 %add7.i.i.i, ptr %arrayidx8.i.i.i
  %sub9.i.i.i = add i64 %and5.i.i.i, -1
  %and10.i.i.i = and i64 %sub9.i.i.i, %and5.i.i.i
  %7 = tail call i64 @llvm.cttz.i64(i64 %and10.i.i.i, i1 true)
  %cast11.i.i.i = trunc i64 %7 to i32
  %add12.i.i.i = or i32 %conv, %cast11.i.i.i
  %arrayidx13.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 12
  store i32 %add12.i.i.i, ptr %arrayidx13.i.i.i
  %sub14.i.i.i = add i64 %and10.i.i.i, -1
  %and15.i.i.i = and i64 %sub14.i.i.i, %and10.i.i.i
  %8 = tail call i64 @llvm.cttz.i64(i64 %and15.i.i.i, i1 true)
  %cast16.i.i.i = trunc i64 %8 to i32
  %add17.i.i.i = or i32 %conv, %cast16.i.i.i
  %arrayidx18.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 16
  store i32 %add17.i.i.i, ptr %arrayidx18.i.i.i
  %sub19.i.i.i = add i64 %and15.i.i.i, -1
  %and20.i.i.i = and i64 %sub19.i.i.i, %and15.i.i.i
  %9 = tail call i64 @llvm.cttz.i64(i64 %and20.i.i.i, i1 true)
  %cast21.i.i.i = trunc i64 %9 to i32
  %add22.i.i.i = or i32 %conv, %cast21.i.i.i
  %arrayidx23.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 20
  store i32 %add22.i.i.i, ptr %arrayidx23.i.i.i
  %sub24.i.i.i = add i64 %and20.i.i.i, -1
  %and25.i.i.i = and i64 %sub24.i.i.i, %and20.i.i.i
  %10 = tail call i64 @llvm.cttz.i64(i64 %and25.i.i.i, i1 true)
  %cast26.i.i.i = trunc i64 %10 to i32
  %add27.i.i.i = or i32 %conv, %cast26.i.i.i
  %arrayidx28.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 24
  store i32 %add27.i.i.i, ptr %arrayidx28.i.i.i
  %sub29.i.i.i = add i64 %and25.i.i.i, -1
  %and30.i.i.i = and i64 %sub29.i.i.i, %and25.i.i.i
  %11 = tail call i64 @llvm.cttz.i64(i64 %and30.i.i.i, i1 true)
  %cast31.i.i.i = trunc i64 %11 to i32
  %add32.i.i.i = or i32 %conv, %cast31.i.i.i
  %arrayidx33.i.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 28
  store i32 %add32.i.i.i, ptr %arrayidx33.i.i.i
  %12 = tail call i64 @llvm.ctpop.i64(i64 %and31.i)
  %cast36.i.i.i = trunc i64 %12 to i32
  %cond.i.i.i = tail call i32 @llvm.umin.i32(i32 %cast36.i.i.i, i32 8)
  %conv.i.i = zext i32 %cond.i.i.i to i64
  %add.i.i = add i64 %3, %conv.i.i
  store i64 %add.i.i, ptr %xn
  %cmp.i.i = icmp samesign ugt i64 %12, 8
  br i1 %cmp.i.i, label %for.body.preheader.i.i, label %xl_emit.exit
for.body.preheader.i.i:
  %sub.i.i = add i64 %and31.i, -1
  %and.i.i = and i64 %sub.i.i, %and31.i
  %sub.1.i.i = add i64 %and.i.i, -1
  %and.1.i.i = and i64 %sub.1.i.i, %and.i.i
  %sub.2.i.i = add i64 %and.1.i.i, -1
  %and.2.i.i = and i64 %sub.2.i.i, %and.1.i.i
  %sub.3.i.i = add i64 %and.2.i.i, -1
  %and.3.i.i = and i64 %sub.3.i.i, %and.2.i.i
  %sub.4.i.i = add i64 %and.3.i.i, -1
  %and.4.i.i = and i64 %sub.4.i.i, %and.3.i.i
  %sub.5.i.i = add i64 %and.4.i.i, -1
  %and.5.i.i = and i64 %sub.5.i.i, %and.4.i.i
  %sub.6.i.i = add i64 %and.5.i.i, -1
  %and.6.i.i = and i64 %sub.6.i.i, %and.5.i.i
  %sub.7.i.i = add i64 %and.6.i.i, -1
  %and.7.i.i = and i64 %sub.7.i.i, %and.6.i.i
  %tobool6.not42.i.i = icmp eq i64 %and.7.i.i, 0
  br i1 %tobool6.not42.i.i, label %xl_emit.exit, label %while.body.preheader.i.i
while.body.preheader.i.i:
  %add.ptr5.i.i = getelementptr inbounds i8, ptr %add.ptr.i.i, i64 32
  br label %while.body.i.i
while.body.i.i:
  %o.044.i.i = phi ptr [ %add.ptr8.i.i, %while.body.i.i ], [ %add.ptr5.i.i, %while.body.preheader.i.i ]
  %c.143.i.i = phi i64 [ %and18.7.i.i, %while.body.i.i ], [ %and.7.i.i, %while.body.preheader.i.i ]
  %call7.i.i = tail call i32 @xl_batch(i64 %c.143.i.i, i32 %conv, ptr %o.044.i.i)
  %idx.ext.i.i = zext i32 %call7.i.i to i64
  %13 = load i64, ptr %xn
  %add10.i.i = add i64 %13, %idx.ext.i.i
  store i64 %add10.i.i, ptr %xn
  %sub17.i.i = add i64 %c.143.i.i, -1
  %and18.i.i = and i64 %sub17.i.i, %c.143.i.i
  %sub17.1.i.i = add i64 %and18.i.i, -1
  %and18.1.i.i = and i64 %sub17.1.i.i, %and18.i.i
  %sub17.2.i.i = add i64 %and18.1.i.i, -1
  %and18.2.i.i = and i64 %sub17.2.i.i, %and18.1.i.i
  %sub17.3.i.i = add i64 %and18.2.i.i, -1
  %and18.3.i.i = and i64 %sub17.3.i.i, %and18.2.i.i
  %sub17.4.i.i = add i64 %and18.3.i.i, -1
  %and18.4.i.i = and i64 %sub17.4.i.i, %and18.3.i.i
  %sub17.5.i.i = add i64 %and18.4.i.i, -1
  %and18.5.i.i = and i64 %sub17.5.i.i, %and18.4.i.i
  %sub17.6.i.i = add i64 %and18.5.i.i, -1
  %and18.6.i.i = and i64 %sub17.6.i.i, %and18.5.i.i
  %sub17.7.i.i = add i64 %and18.6.i.i, -1
  %and18.7.i.i = and i64 %sub17.7.i.i, %and18.6.i.i
  %add.ptr8.i.i = getelementptr inbounds i32, ptr %o.044.i.i, i64 %idx.ext.i.i
  %tobool6.not.i.i = icmp eq i64 %and18.7.i.i, 0
  br i1 %tobool6.not.i.i, label %xl_emit.exit, label %while.body.i.i
xl_emit.exit:
  ret void
}
define i64 @leanllvm_json_escape_expand(ptr %b, i64 %n, ptr %dst, ptr %err, ptr %xp, ptr %xj, i64 %nxp, i64 %pos0, ptr %tab) {
entry:
  %call = tail call i64 @us_dec_x(ptr %b, i64 %n, ptr %dst, ptr %err, ptr %xp, ptr %xj, i64 %nxp, i64 %pos0, ptr %tab)
  ret i64 %call
}
define internal fastcc i64 @us_dec_x(ptr %p, i64 %n, ptr %dst, ptr %err, ptr %xp, ptr %xj, i64 %nxp, i64 %pos0, ptr %tab) {
entry:
  %0 = load i64, ptr %xj
  %add = add i64 %pos0, %n
  %cmp286 = icmp ult i64 %0, %nxp
  br i1 %cmp286, label %land.rhs, label %while.end
land.rhs:
  %k.0287 = phi i64 [ %inc, %while.body ], [ %0, %entry ]
  %arrayidx = getelementptr inbounds i32, ptr %xp, i64 %k.0287
  %1 = load i32, ptr %arrayidx
  %conv = zext i32 %1 to i64
  %cmp1 = icmp ugt i64 %pos0, %conv
  br i1 %cmp1, label %while.body, label %while.end
while.body:
  %inc = add i64 %k.0287, 1
  %exitcond.not = icmp eq i64 %inc, %nxp
  br i1 %exitcond.not, label %while.end35, label %land.rhs
while.end:
  %k.0.lcssa = phi i64 [ %0, %entry ], [ %k.0287, %land.rhs ]
  %cmp4293 = icmp ult i64 %k.0.lcssa, %nxp
  br i1 %cmp4293, label %while.body6, label %while.end35
while.body6:
  %k.1296 = phi i64 [ %add28, %cleanup32 ], [ %k.0.lcssa, %while.end ]
  %i.0295 = phi i64 [ %add24, %cleanup32 ], [ 0, %while.end ]
  %j.0294 = phi i64 [ %j.3, %cleanup32 ], [ 0, %while.end ]
  %arrayidx7 = getelementptr inbounds i32, ptr %xp, i64 %k.1296
  %2 = load i32, ptr %arrayidx7
  %conv8 = zext i32 %2 to i64
  %cmp9.not = icmp ugt i64 %add, %conv8
  br i1 %cmp9.not, label %if.end, label %while.end35
if.end:
  %inc11 = add i64 %k.1296, 1
  %sub = sub i64 %conv8, %pos0
  %add.ptr = getelementptr inbounds i8, ptr %p, i64 %i.0295
  %add.ptr12 = getelementptr inbounds i8, ptr %dst, i64 %j.0294
  %sub13 = sub i64 %sub, %i.0295
  %cmp.i88289 = icmp ugt i64 %sub13, 64
  br i1 %cmp.i88289, label %while.body.i91, label %us_run_long.exit99
while.body.i91:
  %k.0.i86290 = phi i64 [ %add.i98, %while.body.i91 ], [ 0, %if.end ]
  %add.ptr.i92 = getelementptr inbounds i8, ptr %add.ptr12, i64 %k.0.i86290
  %add.ptr1.i93 = getelementptr inbounds i8, ptr %add.ptr, i64 %k.0.i86290
  %3 = load <4 x i64>, ptr %add.ptr1.i93
  store <4 x i64> %3, ptr %add.ptr.i92
  %add.ptr3.i95 = getelementptr inbounds i8, ptr %add.ptr.i92, i64 32
  %add.ptr5.i96 = getelementptr inbounds i8, ptr %add.ptr1.i93, i64 32
  %4 = load <4 x i64>, ptr %add.ptr5.i96
  store <4 x i64> %4, ptr %add.ptr3.i95
  %add.i98 = add i64 %k.0.i86290, 64
  %sub.i87 = sub i64 %sub13, %add.i98
  %cmp.i88 = icmp ugt i64 %sub.i87, 64
  br i1 %cmp.i88, label %while.body.i91, label %us_run_long.exit99
us_run_long.exit99:
  %k.0.i86.lcssa = phi i64 [ 0, %if.end ], [ %add.i98, %while.body.i91 ]
  %sub.i87.lcssa = phi i64 [ %sub13, %if.end ], [ %sub.i87, %while.body.i91 ]
  %add.ptr7.i89 = getelementptr inbounds i8, ptr %add.ptr, i64 %k.0.i86.lcssa
  %add.ptr8.i90 = getelementptr inbounds i8, ptr %add.ptr12, i64 %k.0.i86.lcssa
  %5 = load <4 x i64>, ptr %add.ptr7.i89
  store <4 x i64> %5, ptr %add.ptr8.i90
  %cmp.i102 = icmp samesign ugt i64 %sub.i87.lcssa, 32
  br i1 %cmp.i102, label %if.then.i104, label %us_run.exit
if.then.i104:
  %add.ptr.i105 = getelementptr inbounds i8, ptr %add.ptr8.i90, i64 32
  %add.ptr1.i106 = getelementptr inbounds i8, ptr %add.ptr7.i89, i64 32
  %6 = load <4 x i64>, ptr %add.ptr1.i106
  store <4 x i64> %6, ptr %add.ptr.i105
  br label %us_run.exit
us_run.exit:
  %add15 = add i64 %sub13, %j.0294
  %arrayidx16 = getelementptr inbounds i8, ptr %p, i64 %sub
  %7 = load i8, ptr %arrayidx16
  %cmp18 = icmp ult i8 %7, 32
  br i1 %cmp18, label %if.then20, label %if.end21
if.then20:
  store i64 %sub, ptr %err
  store i64 %inc11, ptr %xj
  br label %cleanup41
if.end21:
  %add.i100 = add i64 %sub, 1
  %cmp.not.i = icmp ult i64 %add.i100, %n
  br i1 %cmp.not.i, label %if.end.i, label %if.then22
if.end.i:
  %arrayidx.i = getelementptr inbounds i8, ptr %p, i64 %add.i100
  %8 = load i8, ptr %arrayidx.i
  %idxprom.i = zext i8 %8 to i64
  %arrayidx2.i = getelementptr inbounds i8, ptr %tab, i64 %idxprom.i
  %9 = load i8, ptr %arrayidx2.i
  %cmp4.i = icmp sgt i8 %9, -1
  br i1 %cmp4.i, label %if.then6.i, label %if.end9.i
if.then6.i:
  %arrayidx7.i = getelementptr inbounds i8, ptr %dst, i64 %add15
  store i8 %9, ptr %arrayidx7.i
  %add8.i = add i64 %add15, 1
  br label %cleanup32
if.end9.i:
  %cmp10.not.i = icmp ne i8 %8, 117
  %add.i113 = add i64 %sub, 6
  %cmp.i114 = icmp ugt i64 %add.i113, %n
  %or.cond335 = or i1 %cmp10.not.i, %cmp.i114
  br i1 %or.cond335, label %if.then22, label %if.end.i115
if.end.i115:
  %add.ptr1.i117 = getelementptr inbounds i8, ptr %arrayidx16, i64 2
  %10 = load <2 x i64>, ptr %add.ptr1.i117
  %11 = bitcast <2 x i64> %10 to <16 x i8>
  %sub.i169 = add <16 x i8> %11, splat (i8 -48)
  %12 = or <16 x i8> %11, splat (i8 32)
  %sub.i168 = add <16 x i8> %12, splat (i8 -97)
  %cmp.i192 = icmp ult <16 x i8> %sub.i169, splat (i8 10)
  %cmp.i190 = icmp ult <16 x i8> %sub.i168, splat (i8 6)
  %or.i185258259 = or <16 x i1> %cmp.i192, %cmp.i190
  %13 = bitcast <16 x i1> %or.i185258259 to i16
  %14 = and i16 %13, 15
  %cmp.not.i128 = icmp eq i16 %14, 15
  br i1 %cmp.not.i128, label %if.end3.i, label %if.then22
if.end3.i:
  %bc318 = bitcast <2 x i64> %10 to <16 x i8>
  %15 = extractelement <16 x i8> %bc318, i64 5
  %bc = bitcast <2 x i64> %10 to <16 x i8>
  %16 = extractelement <16 x i8> %bc, i64 4
  %17 = and <16 x i8> %11, <i8 15, i8 15, i8 15, i8 15, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>
  %18 = select <16 x i1> %cmp.i190, <16 x i8> <i8 9, i8 9, i8 9, i8 9, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <16 x i8> <i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>
  %add.i202 = add <16 x i8> %18, %17
  %19 = tail call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %add.i202, <16 x i8> <i8 16, i8 1, i8 16, i8 1, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>)
  %20 = tail call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %19, <8 x i16> <i16 256, i16 1, i16 0, i16 0, i16 0, i16 0, i16 0, i16 0>)
  %vecext.i207 = extractelement <4 x i32> %20, i64 0
  %and27.i = and i32 %vecext.i207, 65535
  %21 = and i32 %vecext.i207, 64512
  %cmp4.i118 = icmp eq i32 %21, 55296
  %add5.i = add i64 %sub, 12
  %cmp6.not.i = icmp ule i64 %add5.i, %n
  %or.cond.i.not336 = and i1 %cmp6.not.i, %cmp4.i118
  %cmp9.i = icmp eq i8 %16, 92
  %or.cond = and i1 %or.cond.i.not336, %cmp9.i
  %cmp15.i = icmp eq i8 %15, 117
  %or.cond334 = and i1 %or.cond, %cmp15.i
  br i1 %or.cond334, label %if.then17.i, label %if.end32.i
if.then17.i:
  %add.ptr19.i = getelementptr inbounds i8, ptr %arrayidx16, i64 8
  %22 = load <16 x i8>, ptr %add.ptr19.i
  %sub.i167 = add <16 x i8> %22, splat (i8 -48)
  %23 = or <16 x i8> %22, splat (i8 32)
  %sub.i166 = add <16 x i8> %23, splat (i8 -97)
  %cmp.i188 = icmp ult <16 x i8> %sub.i167, splat (i8 10)
  %cmp.i187 = icmp ult <16 x i8> %sub.i166, splat (i8 6)
  %or.i260261 = or <16 x i1> %cmp.i188, %cmp.i187
  %24 = bitcast <16 x i1> %or.i260261 to i16
  %25 = and i16 %24, 15
  %cmp.not.i150 = icmp eq i16 %25, 15
  br i1 %cmp.not.i150, label %land.lhs.true22.i, label %if.end32.i
land.lhs.true22.i:
  %26 = and <16 x i8> %22, <i8 15, i8 15, i8 15, i8 15, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>
  %27 = select <16 x i1> %cmp.i187, <16 x i8> <i8 9, i8 9, i8 9, i8 9, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <16 x i8> <i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>
  %add.i201 = add <16 x i8> %27, %26
  %28 = tail call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %add.i201, <16 x i8> <i8 16, i8 1, i8 16, i8 1, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>)
  %29 = tail call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %28, <8 x i16> <i16 256, i16 1, i16 0, i16 0, i16 0, i16 0, i16 0, i16 0>)
  %vecext.i = extractelement <4 x i32> %29, i64 0
  %and27.i164 = and i32 %vecext.i, 65535
  %sub23.i = add i32 %and27.i164, -56320
  %cmp24.i = icmp ult i32 %sub23.i, 1024
  br i1 %cmp24.i, label %if.then26.i, label %if.end32.i
if.then26.i:
  %sub27.i = shl i32 %and27.i, 10
  %add28.i = add i32 %sub27.i, -56557568
  %add30.i = or i32 %sub23.i, %add28.i
  br label %if.end32.i
if.end32.i:
  %cp.i.3 = phi i32 [ %and27.i, %if.end3.i ], [ %add30.i, %if.then26.i ], [ %and27.i, %land.lhs.true22.i ], [ %and27.i, %if.then17.i ]
  %adv.1.i = phi i64 [ 6, %if.end3.i ], [ 12, %if.then26.i ], [ 6, %land.lhs.true22.i ], [ 6, %if.then17.i ]
  %shr.i = lshr i32 %cp.i.3, 6
  %and.i208 = and i32 %cp.i.3, 63
  %or1.i = or i32 %and.i208, 128
  %shl.i = shl i32 %or1.i, 8
  %or.i209 = or i32 %shr.i, %shl.i
  %or2.i = or i32 %or.i209, 192
  %shr3.i = lshr i32 %cp.i.3, 12
  %and6.i = and i32 %shr.i, 63
  %or7.i = or i32 %and6.i, 128
  %shl8.i = shl i32 %or7.i, 8
  %shl12.i = shl i32 %or1.i, 16
  %30 = or i32 %shl8.i, %shl12.i
  %or9.i = or i32 %shr3.i, %30
  %or13.i = or i32 %or9.i, 224
  %shr14.i = lshr i32 %cp.i.3, 18
  %and17.i = shl i32 %shr3.i, 8
  %or18.i = and i32 %and17.i, 16128
  %shl19.i = or i32 %shr14.i, %or18.i
  %shl24.i = shl i32 %or7.i, 16
  %or20.i = or i32 %shl19.i, %shl24.i
  %shl28.i = shl i32 %or1.i, 24
  %or25.i = or i32 %or20.i, %shl28.i
  %or29.i = or i32 %or25.i, 33008
  %cmp.i210 = icmp samesign ugt i32 %cp.i.3, 127
  %cmp30.i = icmp samesign ugt i32 %cp.i.3, 2047
  %conv31.i = zext i1 %cmp30.i to i64
  %cmp32.i = icmp samesign ugt i32 %cp.i.3, 65535
  %conv33.i = zext i1 %cmp32.i to i64
  %cond.i = select i1 %cmp.i210, i32 %or2.i, i32 %cp.i.3
  %cond38.i = select i1 %cmp30.i, i32 %or13.i, i32 %cond.i
  %cond43.i = select i1 %cmp32.i, i32 %or29.i, i32 %cond38.i
  %add.i211 = select i1 %cmp.i210, i64 2, i64 1
  %add.ptr.i124 = getelementptr inbounds i8, ptr %dst, i64 %add15
  store i32 %cond43.i, ptr %add.ptr.i124
  %add44.i = add i64 %add15, %conv31.i
  %add45.i = add i64 %add44.i, %add.i211
  %add.i125 = add i64 %add45.i, %conv33.i
  br label %cleanup32
if.then22:
  store i64 %sub, ptr %err
  store i64 %inc11, ptr %xj
  br label %cleanup41
cleanup32:
  %j.3 = phi i64 [ %add8.i, %if.then6.i ], [ %add.i125, %if.end32.i ]
  %adv.2 = phi i64 [ 2, %if.then6.i ], [ %adv.1.i, %if.end32.i ]
  %add24 = add i64 %adv.2, %sub
  %cmp25 = icmp eq i64 %adv.2, 12
  %conv27 = zext i1 %cmp25 to i64
  %add28 = add i64 %inc11, %conv27
  %cmp4 = icmp ult i64 %add28, %nxp
  br i1 %cmp4, label %while.body6, label %while.end35
while.end35:
  %j.0.lcssa = phi i64 [ 0, %while.end ], [ %j.0294, %while.body6 ], [ %j.3, %cleanup32 ], [ 0, %while.body ]
  %i.0.lcssa = phi i64 [ 0, %while.end ], [ %i.0295, %while.body6 ], [ %add24, %cleanup32 ], [ 0, %while.body ]
  %k.1.lcssa = phi i64 [ %k.0.lcssa, %while.end ], [ %k.1296, %while.body6 ], [ %add28, %cleanup32 ], [ %nxp, %while.body ]
  %add.ptr36 = getelementptr inbounds i8, ptr %p, i64 %i.0.lcssa
  %add.ptr37 = getelementptr inbounds i8, ptr %dst, i64 %j.0.lcssa
  %sub38 = sub i64 %n, %i.0.lcssa
  %cmp.i303 = icmp ugt i64 %sub38, 64
  br i1 %cmp.i303, label %while.body.i, label %us_run_long.exit
while.body.i:
  %k.0.i304 = phi i64 [ %add.i, %while.body.i ], [ 0, %while.end35 ]
  %add.ptr.i = getelementptr inbounds i8, ptr %add.ptr37, i64 %k.0.i304
  %add.ptr1.i = getelementptr inbounds i8, ptr %add.ptr36, i64 %k.0.i304
  %31 = load <4 x i64>, ptr %add.ptr1.i
  store <4 x i64> %31, ptr %add.ptr.i
  %add.ptr3.i = getelementptr inbounds i8, ptr %add.ptr.i, i64 32
  %add.ptr5.i = getelementptr inbounds i8, ptr %add.ptr1.i, i64 32
  %32 = load <4 x i64>, ptr %add.ptr5.i
  store <4 x i64> %32, ptr %add.ptr3.i
  %add.i = add i64 %k.0.i304, 64
  %sub.i = sub i64 %sub38, %add.i
  %cmp.i = icmp ugt i64 %sub.i, 64
  br i1 %cmp.i, label %while.body.i, label %us_run_long.exit
us_run_long.exit:
  %k.0.i.lcssa = phi i64 [ 0, %while.end35 ], [ %add.i, %while.body.i ]
  %sub.i.lcssa = phi i64 [ %sub38, %while.end35 ], [ %sub.i, %while.body.i ]
  %add.ptr7.i = getelementptr inbounds i8, ptr %add.ptr36, i64 %k.0.i.lcssa
  %add.ptr8.i = getelementptr inbounds i8, ptr %add.ptr37, i64 %k.0.i.lcssa
  %33 = load <4 x i64>, ptr %add.ptr7.i
  store <4 x i64> %33, ptr %add.ptr8.i
  %cmp.i107 = icmp samesign ugt i64 %sub.i.lcssa, 32
  br i1 %cmp.i107, label %if.then.i109, label %us_run.exit112
if.then.i109:
  %add.ptr.i110 = getelementptr inbounds i8, ptr %add.ptr8.i, i64 32
  %add.ptr1.i111 = getelementptr inbounds i8, ptr %add.ptr7.i, i64 32
  %34 = load <4 x i64>, ptr %add.ptr1.i111
  store <4 x i64> %34, ptr %add.ptr.i110
  br label %us_run.exit112
us_run.exit112:
  store i64 %k.1.lcssa, ptr %xj
  %add40 = add i64 %sub38, %j.0.lcssa
  br label %cleanup41
cleanup41:
  %retval.4 = phi i64 [ %add40, %us_run.exit112 ], [ -1, %if.then20 ], [ -1, %if.then22 ]
  ret i64 %retval.4
}
define internal fastcc i32 @xl_batch(i64 %esc, i32 %base, ptr %o) {
entry:
  %or = or i64 %esc, -9223372036854775808
  %0 = tail call i64 @llvm.cttz.i64(i64 %or, i1 true)
  %cast = trunc i64 %0 to i32
  %add = add i32 %base, %cast
  store i32 %add, ptr %o
  %sub = add i64 %or, -1
  %and = and i64 %sub, %or
  %1 = tail call i64 @llvm.cttz.i64(i64 %and, i1 true)
  %cast1 = trunc i64 %1 to i32
  %add2 = add i32 %base, %cast1
  %arrayidx3 = getelementptr inbounds i8, ptr %o, i64 4
  store i32 %add2, ptr %arrayidx3
  %sub4 = add i64 %and, -1
  %and5 = and i64 %sub4, %and
  %2 = tail call i64 @llvm.cttz.i64(i64 %and5, i1 true)
  %cast6 = trunc i64 %2 to i32
  %add7 = add i32 %base, %cast6
  %arrayidx8 = getelementptr inbounds i8, ptr %o, i64 8
  store i32 %add7, ptr %arrayidx8
  %sub9 = add i64 %and5, -1
  %and10 = and i64 %sub9, %and5
  %3 = tail call i64 @llvm.cttz.i64(i64 %and10, i1 true)
  %cast11 = trunc i64 %3 to i32
  %add12 = add i32 %base, %cast11
  %arrayidx13 = getelementptr inbounds i8, ptr %o, i64 12
  store i32 %add12, ptr %arrayidx13
  %sub14 = add i64 %and10, -1
  %and15 = and i64 %sub14, %and10
  %4 = tail call i64 @llvm.cttz.i64(i64 %and15, i1 true)
  %cast16 = trunc i64 %4 to i32
  %add17 = add i32 %base, %cast16
  %arrayidx18 = getelementptr inbounds i8, ptr %o, i64 16
  store i32 %add17, ptr %arrayidx18
  %sub19 = add i64 %and15, -1
  %and20 = and i64 %sub19, %and15
  %5 = tail call i64 @llvm.cttz.i64(i64 %and20, i1 true)
  %cast21 = trunc i64 %5 to i32
  %add22 = add i32 %base, %cast21
  %arrayidx23 = getelementptr inbounds i8, ptr %o, i64 20
  store i32 %add22, ptr %arrayidx23
  %sub24 = add i64 %and20, -1
  %and25 = and i64 %sub24, %and20
  %6 = tail call i64 @llvm.cttz.i64(i64 %and25, i1 true)
  %cast26 = trunc i64 %6 to i32
  %add27 = add i32 %base, %cast26
  %arrayidx28 = getelementptr inbounds i8, ptr %o, i64 24
  store i32 %add27, ptr %arrayidx28
  %sub29 = add i64 %and25, -1
  %and30 = and i64 %sub29, %and25
  %7 = tail call i64 @llvm.cttz.i64(i64 %and30, i1 true)
  %cast31 = trunc i64 %7 to i32
  %add32 = add i32 %base, %cast31
  %arrayidx33 = getelementptr inbounds i8, ptr %o, i64 28
  store i32 %add32, ptr %arrayidx33
  %8 = tail call i64 @llvm.ctpop.i64(i64 %esc)
  %cast36 = trunc i64 %8 to i32
  %cond = tail call i32 @llvm.umin.i32(i32 %cast36, i32 8)
  ret i32 %cond
}
