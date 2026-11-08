; The entry unit as emitted, in the fragment the parser reads: the two position
; emitters @s1f_k_pos8 and @s1f_k_b8, in the emission's order.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-entry.sh
;
; from kernel/json/entry.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to those two `define` blocks.  `-fno-discard-value-names` is a
; naming flag: it names values and labels the entry block, which the parser
; requires, and the capture checks that it changes no instruction by emitting
; the source with and without it and comparing the two texts with every
; register name replaced by one placeholder.
;
; The emission's five parameters are the ABI's own names (%ent, %blk0, %nblk,
; %out, %k), so the capture renames none; it refuses an emission whose parameter
; count is not five.  The POS8 `define` below therefore has six: the table base
; the rewrite appends.
;
; The table read is rewritten, because the fragment has no module-level
; globals.  Each
;
;   getelementptr inbounds nuw [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 %idx
;
; becomes
;
;   getelementptr inbounds <8 x i32>, ptr %tab, i64 %idx
;
; and %tab is appended to the parameter list.  Three operand differences and one
; equation: the base becomes the caller's; the element type becomes the packed
; <8 x i32>, which is 32 bytes, the stride the emitted aggregate computes; the
; two indices become one, the aggregate row the base absorbs.  The emitted form
; addresses @xl_pos8 + 0 * (256 * 32) + idx * 32 and the rewritten form
; %tab + idx * 32, so the offset from the base is 32 * idx on both sides and
; only the base differs.  `nuw` is class 4's removal, so it is gone before the
; rewrite.  Each site is recorded in json-entry.table.tsv.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-entry.strip.tsv; rewritten rather than removed — the `poison` lanes and
; the `shufflevector` masks written as lane lists — in json-entry.rewrites.tsv.
; The lines removed from the module carried:
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   (the attribute groups, source_filename, the unit's two statics and the module
;   metadata nodes are recorded in json-entry.strip.tsv, where they are removed)
;
; The fixture's own opcodes and call targets are in json-entry.inventory.
define internal fastcc i64 @s1f_k_pos8(ptr %ent, i64 %blk0, i64 %nblk, ptr %out, i64 %k, ptr %tab) {
entry:
  %cmp9.not = icmp eq i64 %nblk, 0
  br i1 %cmp9.not, label %for.cond.cleanup, label %for.body
for.cond.cleanup:
  %k.addr.0.lcssa = phi i64 [ %k, %entry ], [ %k.addr.1, %cleanup ]
  ret i64 %k.addr.0.lcssa
for.body:
  %k.addr.011 = phi i64 [ %k.addr.1, %cleanup ], [ %k, %entry ]
  %i.010 = phi i64 [ %inc, %cleanup ], [ 0, %entry ]
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.010
  %0 = load i64, ptr %arrayidx
  %tobool.not = icmp eq i64 %0, 0
  br i1 %tobool.not, label %cleanup, label %if.end
if.end:
  %add = add i64 %i.010, %blk0
  %add.tr = trunc i64 %add to i32
  %conv = shl i32 %add.tr, 6
  %add.ptr = getelementptr inbounds i32, ptr %out, i64 %k.addr.011
  %1 = trunc i64 %0 to i32
  %conv.i = and i32 %1, 255
  %idxprom.i = and i64 %0, 255
  %arrayidx.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.i
  %2 = load <8 x i32>, ptr %arrayidx.i
  %vecinit.i.i = insertelement <8 x i32> zeroinitializer, i32 %conv, i64 0
  %vecinit7.i.i = shufflevector <8 x i32> %vecinit.i.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.i = add <8 x i32> %2, %vecinit7.i.i
  store <8 x i32> %add.i.i, ptr %add.ptr
  %3 = tail call i32 @llvm.ctpop.i32(i32 %conv.i)
  %conv4.i = zext i32 %3 to i64
  %add.ptr.i = getelementptr inbounds i32, ptr %add.ptr, i64 %conv4.i
  %shr.1.i = lshr i64 %0, 8
  %4 = trunc i64 %shr.1.i to i32
  %conv.1.i = and i32 %4, 255
  %idxprom.1.i = and i64 %shr.1.i, 255
  %arrayidx.1.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.1.i
  %5 = load <8 x i32>, ptr %arrayidx.1.i
  %add.1.i = or i32 %conv, 8
  %vecinit.i.1.i = insertelement <8 x i32> zeroinitializer, i32 %add.1.i, i64 0
  %vecinit7.i.1.i = shufflevector <8 x i32> %vecinit.i.1.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.1.i = add <8 x i32> %5, %vecinit7.i.1.i
  store <8 x i32> %add.i.1.i, ptr %add.ptr.i
  %6 = tail call i32 @llvm.ctpop.i32(i32 %conv.1.i)
  %conv4.1.i = zext i32 %6 to i64
  %add.ptr.1.i = getelementptr inbounds i32, ptr %add.ptr.i, i64 %conv4.1.i
  %shr.2.i = lshr i64 %0, 16
  %7 = trunc i64 %shr.2.i to i32
  %conv.2.i = and i32 %7, 255
  %idxprom.2.i = and i64 %shr.2.i, 255
  %arrayidx.2.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.2.i
  %8 = load <8 x i32>, ptr %arrayidx.2.i
  %add.2.i = or i32 %conv, 16
  %vecinit.i.2.i = insertelement <8 x i32> zeroinitializer, i32 %add.2.i, i64 0
  %vecinit7.i.2.i = shufflevector <8 x i32> %vecinit.i.2.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.2.i = add <8 x i32> %8, %vecinit7.i.2.i
  store <8 x i32> %add.i.2.i, ptr %add.ptr.1.i
  %9 = tail call i32 @llvm.ctpop.i32(i32 %conv.2.i)
  %conv4.2.i = zext i32 %9 to i64
  %add.ptr.2.i = getelementptr inbounds i32, ptr %add.ptr.1.i, i64 %conv4.2.i
  %shr.3.i = lshr i64 %0, 24
  %10 = trunc i64 %shr.3.i to i32
  %conv.3.i = and i32 %10, 255
  %idxprom.3.i = and i64 %shr.3.i, 255
  %arrayidx.3.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.3.i
  %11 = load <8 x i32>, ptr %arrayidx.3.i
  %add.3.i = or i32 %conv, 24
  %vecinit.i.3.i = insertelement <8 x i32> zeroinitializer, i32 %add.3.i, i64 0
  %vecinit7.i.3.i = shufflevector <8 x i32> %vecinit.i.3.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.3.i = add <8 x i32> %11, %vecinit7.i.3.i
  store <8 x i32> %add.i.3.i, ptr %add.ptr.2.i
  %12 = tail call i32 @llvm.ctpop.i32(i32 %conv.3.i)
  %conv4.3.i = zext i32 %12 to i64
  %add.ptr.3.i = getelementptr inbounds i32, ptr %add.ptr.2.i, i64 %conv4.3.i
  %shr.4.i = lshr i64 %0, 32
  %13 = trunc i64 %shr.4.i to i32
  %conv.4.i = and i32 %13, 255
  %idxprom.4.i = and i64 %shr.4.i, 255
  %arrayidx.4.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.4.i
  %14 = load <8 x i32>, ptr %arrayidx.4.i
  %add.4.i = or i32 %conv, 32
  %vecinit.i.4.i = insertelement <8 x i32> zeroinitializer, i32 %add.4.i, i64 0
  %vecinit7.i.4.i = shufflevector <8 x i32> %vecinit.i.4.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.4.i = add <8 x i32> %14, %vecinit7.i.4.i
  store <8 x i32> %add.i.4.i, ptr %add.ptr.3.i
  %15 = tail call i32 @llvm.ctpop.i32(i32 %conv.4.i)
  %conv4.4.i = zext i32 %15 to i64
  %add.ptr.4.i = getelementptr inbounds i32, ptr %add.ptr.3.i, i64 %conv4.4.i
  %shr.5.i = lshr i64 %0, 40
  %16 = trunc i64 %shr.5.i to i32
  %conv.5.i = and i32 %16, 255
  %idxprom.5.i = and i64 %shr.5.i, 255
  %arrayidx.5.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.5.i
  %17 = load <8 x i32>, ptr %arrayidx.5.i
  %add.5.i = or i32 %conv, 40
  %vecinit.i.5.i = insertelement <8 x i32> zeroinitializer, i32 %add.5.i, i64 0
  %vecinit7.i.5.i = shufflevector <8 x i32> %vecinit.i.5.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.5.i = add <8 x i32> %17, %vecinit7.i.5.i
  store <8 x i32> %add.i.5.i, ptr %add.ptr.4.i
  %18 = tail call i32 @llvm.ctpop.i32(i32 %conv.5.i)
  %conv4.5.i = zext i32 %18 to i64
  %add.ptr.5.i = getelementptr inbounds i32, ptr %add.ptr.4.i, i64 %conv4.5.i
  %shr.6.i = lshr i64 %0, 48
  %19 = trunc i64 %shr.6.i to i32
  %conv.6.i = and i32 %19, 255
  %idxprom.6.i = and i64 %shr.6.i, 255
  %arrayidx.6.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %idxprom.6.i
  %20 = load <8 x i32>, ptr %arrayidx.6.i
  %add.6.i = or i32 %conv, 48
  %vecinit.i.6.i = insertelement <8 x i32> zeroinitializer, i32 %add.6.i, i64 0
  %vecinit7.i.6.i = shufflevector <8 x i32> %vecinit.i.6.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.6.i = add <8 x i32> %20, %vecinit7.i.6.i
  store <8 x i32> %add.i.6.i, ptr %add.ptr.5.i
  %21 = tail call i32 @llvm.ctpop.i32(i32 %conv.6.i)
  %conv4.6.i = zext i32 %21 to i64
  %add.ptr.6.i = getelementptr inbounds i32, ptr %add.ptr.5.i, i64 %conv4.6.i
  %shr.7.i = lshr i64 %0, 56
  %arrayidx.7.i = getelementptr inbounds <8 x i32>, ptr %tab, i64 %shr.7.i
  %22 = load <8 x i32>, ptr %arrayidx.7.i
  %add.7.i = or i32 %conv, 56
  %vecinit.i.7.i = insertelement <8 x i32> zeroinitializer, i32 %add.7.i, i64 0
  %vecinit7.i.7.i = shufflevector <8 x i32> %vecinit.i.7.i, <8 x i32> zeroinitializer, <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0, i32 0>
  %add.i.7.i = add <8 x i32> %22, %vecinit7.i.7.i
  store <8 x i32> %add.i.7.i, ptr %add.ptr.6.i
  %23 = tail call i64 @llvm.ctpop.i64(i64 %0)
  %add1 = add i64 %23, %k.addr.011
  br label %cleanup
cleanup:
  %k.addr.1 = phi i64 [ %add1, %if.end ], [ %k.addr.011, %for.body ]
  %inc = add i64 %i.010, 1
  %exitcond.not = icmp eq i64 %inc, %nblk
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body
}
define internal fastcc i64 @s1f_k_b8(ptr %ent, i64 %blk0, i64 %nblk, ptr %out, i64 %k) {
entry:
  %cmp9.not = icmp eq i64 %nblk, 0
  br i1 %cmp9.not, label %for.cond.cleanup, label %for.body
for.cond.cleanup:
  %k.addr.0.lcssa = phi i64 [ %k, %entry ], [ %k.addr.1, %cleanup ]
  ret i64 %k.addr.0.lcssa
for.body:
  %k.addr.011 = phi i64 [ %k.addr.1, %cleanup ], [ %k, %entry ]
  %i.010 = phi i64 [ %inc, %cleanup ], [ 0, %entry ]
  %arrayidx = getelementptr inbounds i64, ptr %ent, i64 %i.010
  %0 = load i64, ptr %arrayidx
  %tobool.not = icmp eq i64 %0, 0
  br i1 %tobool.not, label %cleanup, label %if.end
if.end:
  %add = add i64 %i.010, %blk0
  %add.tr = trunc i64 %add to i32
  %conv = shl i32 %add.tr, 6
  %add.ptr = getelementptr inbounds i32, ptr %out, i64 %k.addr.011
  %1 = tail call i64 @llvm.ctpop.i64(i64 %0)
  %2 = tail call i64 @llvm.cttz.i64(i64 %0, i1 true)
  %cast1.i = trunc i64 %2 to i32
  %add.i = or i32 %conv, %cast1.i
  store i32 %add.i, ptr %add.ptr
  %sub.i = add i64 %0, -1
  %and.i = and i64 %sub.i, %0
  %3 = tail call i64 @llvm.cttz.i64(i64 %and.i, i1 true)
  %cast2.i = trunc i64 %3 to i32
  %add3.i = or i32 %conv, %cast2.i
  %arrayidx4.i = getelementptr inbounds i8, ptr %add.ptr, i64 4
  store i32 %add3.i, ptr %arrayidx4.i
  %sub5.i = add i64 %and.i, -1
  %and6.i = and i64 %sub5.i, %and.i
  %4 = tail call i64 @llvm.cttz.i64(i64 %and6.i, i1 true)
  %cast7.i = trunc i64 %4 to i32
  %add8.i = or i32 %conv, %cast7.i
  %arrayidx9.i = getelementptr inbounds i8, ptr %add.ptr, i64 8
  store i32 %add8.i, ptr %arrayidx9.i
  %sub10.i = add i64 %and6.i, -1
  %and11.i = and i64 %sub10.i, %and6.i
  %5 = tail call i64 @llvm.cttz.i64(i64 %and11.i, i1 true)
  %cast12.i = trunc i64 %5 to i32
  %add13.i = or i32 %conv, %cast12.i
  %arrayidx14.i = getelementptr inbounds i8, ptr %add.ptr, i64 12
  store i32 %add13.i, ptr %arrayidx14.i
  %sub15.i = add i64 %and11.i, -1
  %and16.i = and i64 %sub15.i, %and11.i
  %6 = tail call i64 @llvm.cttz.i64(i64 %and16.i, i1 true)
  %cast17.i = trunc i64 %6 to i32
  %add18.i = or i32 %conv, %cast17.i
  %arrayidx19.i = getelementptr inbounds i8, ptr %add.ptr, i64 16
  store i32 %add18.i, ptr %arrayidx19.i
  %sub20.i = add i64 %and16.i, -1
  %and21.i = and i64 %sub20.i, %and16.i
  %7 = tail call i64 @llvm.cttz.i64(i64 %and21.i, i1 true)
  %cast22.i = trunc i64 %7 to i32
  %add23.i = or i32 %conv, %cast22.i
  %arrayidx24.i = getelementptr inbounds i8, ptr %add.ptr, i64 20
  store i32 %add23.i, ptr %arrayidx24.i
  %sub25.i = add i64 %and21.i, -1
  %and26.i = and i64 %sub25.i, %and21.i
  %8 = tail call i64 @llvm.cttz.i64(i64 %and26.i, i1 true)
  %cast27.i = trunc i64 %8 to i32
  %add28.i = or i32 %conv, %cast27.i
  %arrayidx29.i = getelementptr inbounds i8, ptr %add.ptr, i64 24
  store i32 %add28.i, ptr %arrayidx29.i
  %sub30.i = add i64 %and26.i, -1
  %and31.i = and i64 %sub30.i, %and26.i
  %9 = tail call i64 @llvm.cttz.i64(i64 %and31.i, i1 true)
  %cast32.i = trunc i64 %9 to i32
  %add33.i = or i32 %conv, %cast32.i
  %arrayidx34.i = getelementptr inbounds i8, ptr %add.ptr, i64 28
  store i32 %add33.i, ptr %arrayidx34.i
  %cmp.i = icmp samesign ult i64 %1, 9
  br i1 %cmp.i, label %s1f_ke_b8.exit, label %if.end39.i
if.end39.i:
  %sub35.i = add i64 %and31.i, -1
  %and36.i = and i64 %sub35.i, %and31.i
  %10 = tail call i64 @llvm.ctpop.i64(i64 %and36.i)
  %11 = add i64 %10, 8
  %12 = icmp eq i64 %and36.i, 0
  br i1 %12, label %s1f_ke_b8.exit, label %while.body.preheader.i
while.body.preheader.i:
  %add.ptr.i = getelementptr inbounds i8, ptr %add.ptr, i64 32
  %xtraiter = and i64 %10, 7
  %13 = icmp samesign ult i64 %10, 8
  br i1 %13, label %s1f_ke_b8.exit.loopexit.unr-lcssa, label %while.body.preheader.i.new
while.body.preheader.i.new:
  %unroll_iter = and i64 %10, 56
  br label %while.body.i
while.body.i:
  %c.096.i = phi i64 [ %and36.i, %while.body.preheader.i.new ], [ %and44.i.7, %while.body.i ]
  %o.addr.095.i = phi ptr [ %add.ptr.i, %while.body.preheader.i.new ], [ %incdec.ptr.i.7, %while.body.i ]
  %niter = phi i64 [ 0, %while.body.preheader.i.new ], [ %niter.next.7, %while.body.i ]
  %14 = tail call i64 @llvm.cttz.i64(i64 %c.096.i, i1 true)
  %cast41.i = trunc i64 %14 to i32
  %add42.i = or i32 %conv, %cast41.i
  %incdec.ptr.i = getelementptr inbounds i8, ptr %o.addr.095.i, i64 4
  store i32 %add42.i, ptr %o.addr.095.i
  %sub43.i = add i64 %c.096.i, -1
  %and44.i = and i64 %sub43.i, %c.096.i
  %15 = tail call i64 @llvm.cttz.i64(i64 %and44.i, i1 true)
  %cast41.i.1 = trunc i64 %15 to i32
  %add42.i.1 = or i32 %conv, %cast41.i.1
  %incdec.ptr.i.1 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 8
  store i32 %add42.i.1, ptr %incdec.ptr.i
  %sub43.i.1 = add i64 %and44.i, -1
  %and44.i.1 = and i64 %sub43.i.1, %and44.i
  %16 = tail call i64 @llvm.cttz.i64(i64 %and44.i.1, i1 true)
  %cast41.i.2 = trunc i64 %16 to i32
  %add42.i.2 = or i32 %conv, %cast41.i.2
  %incdec.ptr.i.2 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 12
  store i32 %add42.i.2, ptr %incdec.ptr.i.1
  %sub43.i.2 = add i64 %and44.i.1, -1
  %and44.i.2 = and i64 %sub43.i.2, %and44.i.1
  %17 = tail call i64 @llvm.cttz.i64(i64 %and44.i.2, i1 true)
  %cast41.i.3 = trunc i64 %17 to i32
  %add42.i.3 = or i32 %conv, %cast41.i.3
  %incdec.ptr.i.3 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 16
  store i32 %add42.i.3, ptr %incdec.ptr.i.2
  %sub43.i.3 = add i64 %and44.i.2, -1
  %and44.i.3 = and i64 %sub43.i.3, %and44.i.2
  %18 = tail call i64 @llvm.cttz.i64(i64 %and44.i.3, i1 true)
  %cast41.i.4 = trunc i64 %18 to i32
  %add42.i.4 = or i32 %conv, %cast41.i.4
  %incdec.ptr.i.4 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 20
  store i32 %add42.i.4, ptr %incdec.ptr.i.3
  %sub43.i.4 = add i64 %and44.i.3, -1
  %and44.i.4 = and i64 %sub43.i.4, %and44.i.3
  %19 = tail call i64 @llvm.cttz.i64(i64 %and44.i.4, i1 true)
  %cast41.i.5 = trunc i64 %19 to i32
  %add42.i.5 = or i32 %conv, %cast41.i.5
  %incdec.ptr.i.5 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 24
  store i32 %add42.i.5, ptr %incdec.ptr.i.4
  %sub43.i.5 = add i64 %and44.i.4, -1
  %and44.i.5 = and i64 %sub43.i.5, %and44.i.4
  %20 = tail call i64 @llvm.cttz.i64(i64 %and44.i.5, i1 true)
  %cast41.i.6 = trunc i64 %20 to i32
  %add42.i.6 = or i32 %conv, %cast41.i.6
  %incdec.ptr.i.6 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 28
  store i32 %add42.i.6, ptr %incdec.ptr.i.5
  %sub43.i.6 = add i64 %and44.i.5, -1
  %and44.i.6 = and i64 %sub43.i.6, %and44.i.5
  %21 = tail call i64 @llvm.cttz.i64(i64 %and44.i.6, i1 true)
  %cast41.i.7 = trunc i64 %21 to i32
  %add42.i.7 = or i32 %conv, %cast41.i.7
  %incdec.ptr.i.7 = getelementptr inbounds i8, ptr %o.addr.095.i, i64 32
  store i32 %add42.i.7, ptr %incdec.ptr.i.6
  %sub43.i.7 = add i64 %and44.i.6, -1
  %and44.i.7 = and i64 %sub43.i.7, %and44.i.6
  %niter.next.7 = add i64 %niter, 8
  %niter.ncmp.7 = icmp eq i64 %niter.next.7, %unroll_iter
  br i1 %niter.ncmp.7, label %s1f_ke_b8.exit.loopexit.unr-lcssa, label %while.body.i
s1f_ke_b8.exit.loopexit.unr-lcssa:
  %c.096.i.unr = phi i64 [ %and36.i, %while.body.preheader.i ], [ %and44.i.7, %while.body.i ]
  %o.addr.095.i.unr = phi ptr [ %add.ptr.i, %while.body.preheader.i ], [ %incdec.ptr.i.7, %while.body.i ]
  %lcmp.mod.not = icmp eq i64 %xtraiter, 0
  br i1 %lcmp.mod.not, label %s1f_ke_b8.exit, label %while.body.i.epil
while.body.i.epil:
  %c.096.i.epil = phi i64 [ %and44.i.epil, %while.body.i.epil ], [ %c.096.i.unr, %s1f_ke_b8.exit.loopexit.unr-lcssa ]
  %o.addr.095.i.epil = phi ptr [ %incdec.ptr.i.epil, %while.body.i.epil ], [ %o.addr.095.i.unr, %s1f_ke_b8.exit.loopexit.unr-lcssa ]
  %epil.iter = phi i64 [ %epil.iter.next, %while.body.i.epil ], [ 0, %s1f_ke_b8.exit.loopexit.unr-lcssa ]
  %22 = tail call i64 @llvm.cttz.i64(i64 %c.096.i.epil, i1 true)
  %cast41.i.epil = trunc i64 %22 to i32
  %add42.i.epil = or i32 %conv, %cast41.i.epil
  %incdec.ptr.i.epil = getelementptr inbounds i8, ptr %o.addr.095.i.epil, i64 4
  store i32 %add42.i.epil, ptr %o.addr.095.i.epil
  %sub43.i.epil = add i64 %c.096.i.epil, -1
  %and44.i.epil = and i64 %sub43.i.epil, %c.096.i.epil
  %epil.iter.next = add i64 %epil.iter, 1
  %epil.iter.cmp.not = icmp eq i64 %epil.iter.next, %xtraiter
  br i1 %epil.iter.cmp.not, label %s1f_ke_b8.exit, label %while.body.i.epil
s1f_ke_b8.exit:
  %retval.0.i = phi i64 [ %1, %if.end ], [ 8, %if.end39.i ], [ %11, %while.body.i.epil ], [ %11, %s1f_ke_b8.exit.loopexit.unr-lcssa ]
  %add1 = add i64 %retval.0.i, %k.addr.011
  br label %cleanup
cleanup:
  %k.addr.1 = phi i64 [ %add1, %s1f_ke_b8.exit ], [ %k.addr.011, %for.body ]
  %inc = add i64 %i.010, 1
  %exitcond.not = icmp eq i64 %inc, %nblk
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body
}
