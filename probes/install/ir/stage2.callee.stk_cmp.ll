; The stage-2 callee `stk_cmp`, as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; `noinline` on every helper and on `stk_mul_u64`, then the same token strip
; capture-stage2.sh applies.  `stk_cmp` is the rounding loop's comparison.  The emission inlines `stk_copy`, `stk_shl` and `stk_cmp_bn` into it and unrolls the shift loop four limbs an iteration, so the body is 104 blocks and 757 instructions, with `llvm.memset` and the lifetime markers in it.  In place of `stk_copy`'s variable-length `memcpy` the compiler line's hardening emits `__memcpy_chk`, which no selection in this tree answers; `stk_mul_u64` stays out of line, as the transform marks it.  Its `StkBn` and `Stk` aggregates are the fixture's own `%struct` definitions, and the layout the parser is given is their datalayout extent.
;
define i32 @stk_cmp(ptr %v, i64 %J, i64 %eB) {
entry:
  %a = alloca %struct.StkBn
  %b = alloca %struct.StkBn
  call void @llvm.lifetime.start.p0(i64 776, ptr %a)
  call void @llvm.lifetime.start.p0(i64 776, ptr %b)
  %sticky = getelementptr inbounds i8, ptr %v, i64 1560
  %0 = load i32, ptr %sticky
  %tobool.not = icmp eq i32 %0, 0
  br i1 %tobool.not, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %n.i = getelementptr inbounds i8, ptr %v, i64 1544
  %1 = load i32, ptr %n.i
  %n1.i = getelementptr inbounds i8, ptr %b, i64 768
  store i32 %1, ptr %n1.i
  %tobool.not.i = icmp eq i32 %1, 0
  br i1 %tobool.not.i, label %stk_copy.exit, label %if.then.i

if.then.i:                                        ; preds = %if.then
  %pow = getelementptr inbounds i8, ptr %v, i64 776
  %conv.i = sext i32 %1 to i64
  %mul.i = shl i64 %conv.i, 3
  %call.i.i = call ptr @__memcpy_chk(ptr %b, ptr %pow, i64 %mul.i, i64 776)
  br label %stk_copy.exit

stk_copy.exit:                                    ; preds = %if.then.i, %if.then
  call void @stk_mul_u64(ptr %b, i64 %J)
  %S = getelementptr inbounds i8, ptr %v, i64 1552
  %2 = load i64, ptr %S
  %sub = sub i64 %eB, %2
  %conv = trunc i64 %sub to i32
  %cmp.i = icmp eq i32 %conv, 0
  %.pre = load i32, ptr %n1.i
  br i1 %cmp.i, label %stk_shl.exit, label %lor.lhs.false.i

lor.lhs.false.i:                                  ; preds = %stk_copy.exit
  %cmp1.i = icmp eq i32 %.pre, 0
  br i1 %cmp1.i, label %stk_shl.exit, label %if.end.i

if.end.i:                                         ; preds = %lor.lhs.false.i
  %div78.i = lshr i32 %conv, 6
  %rem2.i = and i32 %conv, 63
  %tobool.not.i28 = icmp ne i32 %rem2.i, 0
  %cmp579.i = icmp sgt i32 %.pre, 0
  %or.cond.i = and i1 %tobool.not.i28, %cmp579.i
  br i1 %or.cond.i, label %for.body.lr.ph.i, label %if.end18.i

for.body.lr.ph.i:                                 ; preds = %if.end.i
  %sh_prom.i = and i64 %sub, 63
  %sub.i = sub i32 64, %rem2.i
  %sh_prom9.i = zext i32 %sub.i to i64
  %wide.trip.count.i = zext i32 %.pre to i64
  %xtraiter = and i64 %wide.trip.count.i, 3
  %3 = icmp ult i32 %.pre, 4
  br i1 %3, label %for.cond.cleanup.i.unr-lcssa, label %for.body.lr.ph.i.new

for.body.lr.ph.i.new:                             ; preds = %for.body.lr.ph.i
  %unroll_iter = and i64 %wide.trip.count.i, 2147483644
  br label %for.body.i

for.cond.cleanup.i.unr-lcssa:                     ; preds = %for.body.i, %for.body.lr.ph.i
  %shr.i.lcssa.ph = phi i64 [ poison, %for.body.lr.ph.i ], [ %shr.i.3, %for.body.i ]
  %indvars.iv.i.unr = phi i64 [ 0, %for.body.lr.ph.i ], [ %indvars.iv.next.i.3, %for.body.i ]
  %carry.081.i.unr = phi i64 [ 0, %for.body.lr.ph.i ], [ %shr.i.3, %for.body.i ]
  %lcmp.mod.not = icmp eq i64 %xtraiter, 0
  br i1 %lcmp.mod.not, label %for.cond.cleanup.i, label %for.body.i.epil

for.body.i.epil:                                  ; preds = %for.body.i.epil, %for.cond.cleanup.i.unr-lcssa
  %indvars.iv.i.epil = phi i64 [ %indvars.iv.next.i.epil, %for.body.i.epil ], [ %indvars.iv.i.unr, %for.cond.cleanup.i.unr-lcssa ]
  %carry.081.i.epil = phi i64 [ %shr.i.epil, %for.body.i.epil ], [ %carry.081.i.unr, %for.cond.cleanup.i.unr-lcssa ]
  %epil.iter = phi i64 [ %epil.iter.next, %for.body.i.epil ], [ 0, %for.cond.cleanup.i.unr-lcssa ]
  %arrayidx.i.epil = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.i.epil
  %4 = load i64, ptr %arrayidx.i.epil
  %shl.i.epil = shl i64 %4, %sh_prom.i
  %or.i.epil = or i64 %shl.i.epil, %carry.081.i.epil
  store i64 %or.i.epil, ptr %arrayidx.i.epil
  %shr.i.epil = lshr i64 %4, %sh_prom9.i
  %indvars.iv.next.i.epil = add i64 %indvars.iv.i.epil, 1
  %epil.iter.next = add i64 %epil.iter, 1
  %epil.iter.cmp.not = icmp eq i64 %epil.iter.next, %xtraiter
  br i1 %epil.iter.cmp.not, label %for.cond.cleanup.i, label %for.body.i.epil

for.cond.cleanup.i:                               ; preds = %for.body.i.epil, %for.cond.cleanup.i.unr-lcssa
  %shr.i.lcssa = phi i64 [ %shr.i.lcssa.ph, %for.cond.cleanup.i.unr-lcssa ], [ %shr.i.epil, %for.body.i.epil ]
  %tobool10.not.i = icmp eq i64 %shr.i.lcssa, 0
  br i1 %tobool10.not.i, label %if.end18.i, label %if.then11.i

for.body.i:                                       ; preds = %for.body.i, %for.body.lr.ph.i.new
  %indvars.iv.i = phi i64 [ 0, %for.body.lr.ph.i.new ], [ %indvars.iv.next.i.3, %for.body.i ]
  %carry.081.i = phi i64 [ 0, %for.body.lr.ph.i.new ], [ %shr.i.3, %for.body.i ]
  %niter = phi i64 [ 0, %for.body.lr.ph.i.new ], [ %niter.next.3, %for.body.i ]
  %arrayidx.i = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.i
  %5 = load i64, ptr %arrayidx.i
  %shl.i = shl i64 %5, %sh_prom.i
  %or.i = or i64 %shl.i, %carry.081.i
  store i64 %or.i, ptr %arrayidx.i
  %shr.i = lshr i64 %5, %sh_prom9.i
  %indvars.iv.next.i = or i64 %indvars.iv.i, 1
  %arrayidx.i.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i
  %6 = load i64, ptr %arrayidx.i.1
  %shl.i.1 = shl i64 %6, %sh_prom.i
  %or.i.1 = or i64 %shl.i.1, %shr.i
  store i64 %or.i.1, ptr %arrayidx.i.1
  %shr.i.1 = lshr i64 %6, %sh_prom9.i
  %indvars.iv.next.i.1 = or i64 %indvars.iv.i, 2
  %arrayidx.i.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i.1
  %7 = load i64, ptr %arrayidx.i.2
  %shl.i.2 = shl i64 %7, %sh_prom.i
  %or.i.2 = or i64 %shl.i.2, %shr.i.1
  store i64 %or.i.2, ptr %arrayidx.i.2
  %shr.i.2 = lshr i64 %7, %sh_prom9.i
  %indvars.iv.next.i.2 = or i64 %indvars.iv.i, 3
  %arrayidx.i.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i.2
  %8 = load i64, ptr %arrayidx.i.3
  %shl.i.3 = shl i64 %8, %sh_prom.i
  %or.i.3 = or i64 %shl.i.3, %shr.i.2
  store i64 %or.i.3, ptr %arrayidx.i.3
  %shr.i.3 = lshr i64 %8, %sh_prom9.i
  %indvars.iv.next.i.3 = add i64 %indvars.iv.i, 4
  %niter.next.3 = add i64 %niter, 4
  %niter.ncmp.3 = icmp eq i64 %niter.next.3, %unroll_iter
  br i1 %niter.ncmp.3, label %for.cond.cleanup.i.unr-lcssa, label %for.body.i

if.then11.i:                                      ; preds = %for.cond.cleanup.i
  %inc14.i = add i32 %.pre, 1
  %arrayidx16.i = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %wide.trip.count.i
  store i64 %shr.i.lcssa, ptr %arrayidx16.i
  br label %if.end18.i

if.end18.i:                                       ; preds = %if.then11.i, %for.cond.cleanup.i, %if.end.i
  %9 = phi i32 [ %.pre, %for.cond.cleanup.i ], [ %inc14.i, %if.then11.i ], [ %.pre, %if.end.i ]
  %tobool19.not.i = icmp ult i32 %conv, 64
  br i1 %tobool19.not.i, label %stk_shl.exit, label %if.then20.i

if.then20.i:                                      ; preds = %if.end18.i
  %i21.082.i = add i32 %9, -1
  %cmp2583.i = icmp sgt i32 %i21.082.i, -1
  br i1 %cmp2583.i, label %iter.check, label %for.cond.cleanup39.i

iter.check:                                       ; preds = %if.then20.i
  %10 = zext i32 %i21.082.i to i64
  %11 = zext i32 %9 to i64
  %min.iters.check = icmp ult i32 %9, 4
  br i1 %min.iters.check, label %for.body27.i.preheader, label %vector.scevcheck

vector.scevcheck:                                 ; preds = %iter.check
  %12 = add i32 %9, %div78.i
  %13 = add i32 %12, -1
  %14 = icmp sgt i32 %div78.i, %13
  br i1 %14, label %for.body27.i.preheader, label %vector.memcheck

vector.memcheck:                                  ; preds = %vector.scevcheck
  %15 = add i32 %9, %div78.i
  %16 = add i32 %15, -1
  %17 = sext i32 %16 to i64
  %18 = sub i64 %10, %17
  %19 = and i64 %18, 2305843009213693936
  %diff.check = icmp eq i64 %19, 0
  br i1 %diff.check, label %for.body27.i.preheader, label %vector.main.loop.iter.check

vector.main.loop.iter.check:                      ; preds = %vector.memcheck
  %min.iters.check190 = icmp ult i32 %9, 16
  br i1 %min.iters.check190, label %vec.epilog.ph, label %vector.ph

vector.ph:                                        ; preds = %vector.main.loop.iter.check
  %n.vec = and i64 %11, 4294967280
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.ph
  %index = phi i64 [ 0, %vector.ph ], [ %index.next, %vector.body ]
  %20 = sub i64 %10, %index
  %21 = trunc i64 %index to i32
  %22 = sub i32 %i21.082.i, %21
  %23 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %20
  %24 = getelementptr inbounds i8, ptr %23, i64 -24
  %25 = getelementptr inbounds i8, ptr %23, i64 -56
  %26 = getelementptr inbounds i8, ptr %23, i64 -88
  %27 = getelementptr inbounds i8, ptr %23, i64 -120
  %wide.load = load <4 x i64>, ptr %24
  %wide.load191 = load <4 x i64>, ptr %25
  %wide.load193 = load <4 x i64>, ptr %26
  %wide.load195 = load <4 x i64>, ptr %27
  %28 = add i32 %div78.i, %22
  %29 = sext i32 %28 to i64
  %30 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %29
  %31 = getelementptr inbounds i8, ptr %30, i64 -24
  %32 = getelementptr inbounds i8, ptr %30, i64 -56
  %33 = getelementptr inbounds i8, ptr %30, i64 -88
  %34 = getelementptr inbounds i8, ptr %30, i64 -120
  store <4 x i64> %wide.load, ptr %31
  store <4 x i64> %wide.load191, ptr %32
  store <4 x i64> %wide.load193, ptr %33
  store <4 x i64> %wide.load195, ptr %34
  %index.next = add i64 %index, 16
  %35 = icmp eq i64 %index.next, %n.vec
  br i1 %35, label %middle.block, label %vector.body

middle.block:                                     ; preds = %vector.body
  %cmp.n = icmp eq i64 %n.vec, %11
  br i1 %cmp.n, label %for.cond.cleanup39.i, label %vec.epilog.iter.check

vec.epilog.iter.check:                            ; preds = %middle.block
  %ind.end = sub i64 %10, %n.vec
  %n.vec.remaining = and i64 %11, 12
  %min.epilog.iters.check = icmp eq i64 %n.vec.remaining, 0
  br i1 %min.epilog.iters.check, label %for.body27.i.preheader, label %vec.epilog.ph

vec.epilog.ph:                                    ; preds = %vec.epilog.iter.check, %vector.main.loop.iter.check
  %vec.epilog.resume.val = phi i64 [ %n.vec, %vec.epilog.iter.check ], [ 0, %vector.main.loop.iter.check ]
  %n.vec202 = and i64 %11, 4294967292
  %36 = sub i64 %10, %n.vec202
  %invariant.gep = getelementptr i8, ptr %b, i64 -24
  %invariant.gep340 = getelementptr i8, ptr %b, i64 -24
  br label %vec.epilog.vector.body

vec.epilog.vector.body:                           ; preds = %vec.epilog.vector.body, %vec.epilog.ph
  %index203 = phi i64 [ %vec.epilog.resume.val, %vec.epilog.ph ], [ %index.next208, %vec.epilog.vector.body ]
  %offset.idx = sub i64 %10, %index203
  %37 = trunc i64 %index203 to i32
  %38 = sub i32 %i21.082.i, %37
  %gep = getelementptr [96 x i64], ptr %invariant.gep, i64 0, i64 %offset.idx
  %wide.load205 = load <4 x i64>, ptr %gep
  %39 = add i32 %div78.i, %38
  %40 = sext i32 %39 to i64
  %gep341 = getelementptr [96 x i64], ptr %invariant.gep340, i64 0, i64 %40
  store <4 x i64> %wide.load205, ptr %gep341
  %index.next208 = add i64 %index203, 4
  %41 = icmp eq i64 %index.next208, %n.vec202
  br i1 %41, label %vec.epilog.middle.block, label %vec.epilog.vector.body

vec.epilog.middle.block:                          ; preds = %vec.epilog.vector.body
  %cmp.n209 = icmp eq i64 %n.vec202, %11
  br i1 %cmp.n209, label %for.cond.cleanup39.i, label %for.body27.i.preheader

for.body27.i.preheader:                           ; preds = %vec.epilog.middle.block, %vec.epilog.iter.check, %vector.memcheck, %vector.scevcheck, %iter.check
  %indvars.iv88.i.ph = phi i64 [ %10, %iter.check ], [ %10, %vector.scevcheck ], [ %10, %vector.memcheck ], [ %ind.end, %vec.epilog.iter.check ], [ %36, %vec.epilog.middle.block ]
  %42 = add i64 %indvars.iv88.i.ph, 1
  %xtraiter317 = and i64 %42, 7
  %43 = and i64 %indvars.iv88.i.ph, 7
  %lcmp.mod318.not = icmp eq i64 %43, 7
  br i1 %lcmp.mod318.not, label %for.body27.i.prol.loopexit, label %for.body27.i.prol

for.body27.i.prol:                                ; preds = %for.body27.i.prol, %for.body27.i.preheader
  %indvars.iv88.i.prol = phi i64 [ %indvars.iv.next89.i.prol, %for.body27.i.prol ], [ %indvars.iv88.i.ph, %for.body27.i.preheader ]
  %prol.iter = phi i64 [ %prol.iter.next, %for.body27.i.prol ], [ 0, %for.body27.i.preheader ]
  %arrayidx30.i.prol = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv88.i.prol
  %44 = load i64, ptr %arrayidx30.i.prol
  %45 = trunc i64 %indvars.iv88.i.prol to i32
  %46 = add i32 %div78.i, %45
  %idxprom32.i.prol = sext i32 %46 to i64
  %arrayidx33.i.prol = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.prol
  store i64 %44, ptr %arrayidx33.i.prol
  %indvars.iv.next89.i.prol = add i64 %indvars.iv88.i.prol, -1
  %prol.iter.next = add i64 %prol.iter, 1
  %prol.iter.cmp.not = icmp eq i64 %prol.iter.next, %xtraiter317
  br i1 %prol.iter.cmp.not, label %for.body27.i.prol.loopexit, label %for.body27.i.prol

for.body27.i.prol.loopexit:                       ; preds = %for.body27.i.prol, %for.body27.i.preheader
  %indvars.iv88.i.unr = phi i64 [ %indvars.iv88.i.ph, %for.body27.i.preheader ], [ %indvars.iv.next89.i.prol, %for.body27.i.prol ]
  %47 = icmp ult i64 %indvars.iv88.i.ph, 7
  br i1 %47, label %for.cond.cleanup39.i, label %for.body27.i

for.body27.i:                                     ; preds = %for.body27.i, %for.body27.i.prol.loopexit
  %indvars.iv88.i = phi i64 [ %indvars.iv.next89.i.7, %for.body27.i ], [ %indvars.iv88.i.unr, %for.body27.i.prol.loopexit ]
  %arrayidx30.i = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv88.i
  %48 = load i64, ptr %arrayidx30.i
  %49 = trunc i64 %indvars.iv88.i to i32
  %50 = add i32 %div78.i, %49
  %idxprom32.i = sext i32 %50 to i64
  %arrayidx33.i = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i
  store i64 %48, ptr %arrayidx33.i
  %indvars.iv.next89.i = add i64 %indvars.iv88.i, -1
  %arrayidx30.i.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i
  %51 = load i64, ptr %arrayidx30.i.1
  %52 = trunc i64 %indvars.iv.next89.i to i32
  %53 = add i32 %div78.i, %52
  %idxprom32.i.1 = sext i32 %53 to i64
  %arrayidx33.i.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.1
  store i64 %51, ptr %arrayidx33.i.1
  %indvars.iv.next89.i.1 = add i64 %indvars.iv88.i, -2
  %arrayidx30.i.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.1
  %54 = load i64, ptr %arrayidx30.i.2
  %55 = trunc i64 %indvars.iv.next89.i.1 to i32
  %56 = add i32 %div78.i, %55
  %idxprom32.i.2 = sext i32 %56 to i64
  %arrayidx33.i.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.2
  store i64 %54, ptr %arrayidx33.i.2
  %indvars.iv.next89.i.2 = add i64 %indvars.iv88.i, -3
  %arrayidx30.i.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.2
  %57 = load i64, ptr %arrayidx30.i.3
  %58 = trunc i64 %indvars.iv.next89.i.2 to i32
  %59 = add i32 %div78.i, %58
  %idxprom32.i.3 = sext i32 %59 to i64
  %arrayidx33.i.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.3
  store i64 %57, ptr %arrayidx33.i.3
  %indvars.iv.next89.i.3 = add i64 %indvars.iv88.i, -4
  %arrayidx30.i.4 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.3
  %60 = load i64, ptr %arrayidx30.i.4
  %61 = trunc i64 %indvars.iv.next89.i.3 to i32
  %62 = add i32 %div78.i, %61
  %idxprom32.i.4 = sext i32 %62 to i64
  %arrayidx33.i.4 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.4
  store i64 %60, ptr %arrayidx33.i.4
  %indvars.iv.next89.i.4 = add i64 %indvars.iv88.i, -5
  %arrayidx30.i.5 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.4
  %63 = load i64, ptr %arrayidx30.i.5
  %64 = trunc i64 %indvars.iv.next89.i.4 to i32
  %65 = add i32 %div78.i, %64
  %idxprom32.i.5 = sext i32 %65 to i64
  %arrayidx33.i.5 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.5
  store i64 %63, ptr %arrayidx33.i.5
  %indvars.iv.next89.i.5 = add i64 %indvars.iv88.i, -6
  %arrayidx30.i.6 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.5
  %66 = load i64, ptr %arrayidx30.i.6
  %67 = trunc i64 %indvars.iv.next89.i.5 to i32
  %68 = add i32 %div78.i, %67
  %idxprom32.i.6 = sext i32 %68 to i64
  %arrayidx33.i.6 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.6
  store i64 %66, ptr %arrayidx33.i.6
  %indvars.iv.next89.i.6 = add i64 %indvars.iv88.i, -7
  %arrayidx30.i.7 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i.6
  %69 = load i64, ptr %arrayidx30.i.7
  %70 = trunc i64 %indvars.iv.next89.i.6 to i32
  %71 = add i32 %div78.i, %70
  %idxprom32.i.7 = sext i32 %71 to i64
  %arrayidx33.i.7 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i.7
  store i64 %69, ptr %arrayidx33.i.7
  %indvars.iv.next89.i.7 = add i64 %indvars.iv88.i, -8
  %cmp25.not.i.7 = icmp eq i64 %indvars.iv.next89.i.6, 0
  br i1 %cmp25.not.i.7, label %for.cond.cleanup39.i, label %for.body27.i

for.cond.cleanup39.i:                             ; preds = %for.body27.i, %for.body27.i.prol.loopexit, %vec.epilog.middle.block, %middle.block, %if.then20.i
  %72 = lshr i64 %sub, 3
  %73 = and i64 %72, 536870904
  call void @llvm.memset.p0.i64(ptr %b, i8 0, i64 %73, i1 false)
  %add48.i = add i32 %9, %div78.i
  br label %stk_shl.exit

stk_shl.exit:                                     ; preds = %for.cond.cleanup39.i, %if.end18.i, %lor.lhs.false.i, %stk_copy.exit
  %74 = phi i32 [ %.pre, %stk_copy.exit ], [ 0, %lor.lhs.false.i ], [ %9, %if.end18.i ], [ %add48.i, %for.cond.cleanup39.i ]
  %n.i29 = getelementptr inbounds i8, ptr %v, i64 768
  %75 = load i32, ptr %n.i29
  %cmp.not.i = icmp eq i32 %75, %74
  br i1 %cmp.not.i, label %for.cond.preheader.i, label %if.then.i31

for.cond.preheader.i:                             ; preds = %stk_shl.exit
  %76 = zext i32 %74 to i64
  br label %for.cond.i

if.then.i31:                                      ; preds = %stk_shl.exit
  %cmp4.i = icmp slt i32 %75, %74
  %spec.select = select i1 %cmp4.i, i32 -1, i32 1
  br label %cleanup

for.cond.i:                                       ; preds = %for.body.i34, %for.cond.preheader.i
  %indvars.iv.i32 = phi i64 [ %76, %for.cond.preheader.i ], [ %indvars.iv.next.i33, %for.body.i34 ]
  %indvars.iv.next.i33 = add i64 %indvars.iv.i32, -1
  %77 = and i64 %indvars.iv.next.i33, 2147483648
  %cmp6.not.i = icmp eq i64 %77, 0
  br i1 %cmp6.not.i, label %for.body.i34, label %cleanup

for.body.i34:                                     ; preds = %for.cond.i
  %idxprom.i = and i64 %indvars.iv.next.i33, 2147483647
  %arrayidx.i35 = getelementptr inbounds [96 x i64], ptr %v, i64 0, i64 %idxprom.i
  %78 = load i64, ptr %arrayidx.i35
  %arrayidx9.i = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom.i
  %79 = load i64, ptr %arrayidx9.i
  %cmp10.not.i = icmp eq i64 %78, %79
  br i1 %cmp10.not.i, label %for.cond.i, label %if.then11.i36

if.then11.i36:                                    ; preds = %for.body.i34
  %cmp18.i = icmp ult i64 %78, %79
  %spec.select172 = select i1 %cmp18.i, i32 -1, i32 1
  br label %cleanup

if.end:                                           ; preds = %entry
  %n.i37 = getelementptr inbounds i8, ptr %v, i64 768
  %80 = load i32, ptr %n.i37
  %n1.i38 = getelementptr inbounds i8, ptr %a, i64 768
  store i32 %80, ptr %n1.i38
  %tobool.not.i39 = icmp eq i32 %80, 0
  br i1 %tobool.not.i39, label %stk_copy.exit45, label %if.then.i40

if.then.i40:                                      ; preds = %if.end
  %conv.i41 = sext i32 %80 to i64
  %mul.i42 = shl i64 %conv.i41, 3
  %call.i.i43 = call ptr @__memcpy_chk(ptr %a, ptr %v, i64 %mul.i42, i64 776)
  br label %stk_copy.exit45

stk_copy.exit45:                                  ; preds = %if.then.i40, %if.end
  %cmp3 = icmp slt i64 %eB, 0
  br i1 %cmp3, label %if.then5, label %if.end8

if.then5:                                         ; preds = %stk_copy.exit45
  %81 = trunc i64 %eB to i32
  %conv7 = sub i32 0, %81
  %82 = load i32, ptr %n1.i38
  %cmp1.i49 = icmp eq i32 %82, 0
  br i1 %cmp1.i49, label %if.end8, label %if.end.i50

if.end.i50:                                       ; preds = %if.then5
  %div78.i51 = lshr i32 %conv7, 6
  %rem2.i52 = and i32 %conv7, 63
  %tobool.not.i53 = icmp ne i32 %rem2.i52, 0
  %cmp579.i54 = icmp sgt i32 %82, 0
  %or.cond.i55 = and i1 %tobool.not.i53, %cmp579.i54
  br i1 %or.cond.i55, label %for.body.lr.ph.i71, label %if.end18.i56

for.body.lr.ph.i71:                               ; preds = %if.end.i50
  %sh_prom.i72 = zext i32 %rem2.i52 to i64
  %sub.i73 = sub i32 64, %rem2.i52
  %sh_prom9.i74 = zext i32 %sub.i73 to i64
  %wide.trip.count.i75 = zext i32 %82 to i64
  %xtraiter319 = and i64 %wide.trip.count.i75, 3
  %83 = icmp ult i32 %82, 4
  br i1 %83, label %for.cond.cleanup.i85.unr-lcssa, label %for.body.lr.ph.i71.new

for.body.lr.ph.i71.new:                           ; preds = %for.body.lr.ph.i71
  %unroll_iter323 = and i64 %wide.trip.count.i75, 2147483644
  br label %for.body.i76

for.cond.cleanup.i85.unr-lcssa:                   ; preds = %for.body.i76, %for.body.lr.ph.i71
  %shr.i82.lcssa.ph = phi i64 [ poison, %for.body.lr.ph.i71 ], [ %shr.i82.3, %for.body.i76 ]
  %indvars.iv.i77.unr = phi i64 [ 0, %for.body.lr.ph.i71 ], [ %indvars.iv.next.i83.3, %for.body.i76 ]
  %carry.081.i78.unr = phi i64 [ 0, %for.body.lr.ph.i71 ], [ %shr.i82.3, %for.body.i76 ]
  %lcmp.mod321.not = icmp eq i64 %xtraiter319, 0
  br i1 %lcmp.mod321.not, label %for.cond.cleanup.i85, label %for.body.i76.epil

for.body.i76.epil:                                ; preds = %for.body.i76.epil, %for.cond.cleanup.i85.unr-lcssa
  %indvars.iv.i77.epil = phi i64 [ %indvars.iv.next.i83.epil, %for.body.i76.epil ], [ %indvars.iv.i77.unr, %for.cond.cleanup.i85.unr-lcssa ]
  %carry.081.i78.epil = phi i64 [ %shr.i82.epil, %for.body.i76.epil ], [ %carry.081.i78.unr, %for.cond.cleanup.i85.unr-lcssa ]
  %epil.iter320 = phi i64 [ %epil.iter320.next, %for.body.i76.epil ], [ 0, %for.cond.cleanup.i85.unr-lcssa ]
  %arrayidx.i79.epil = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.i77.epil
  %84 = load i64, ptr %arrayidx.i79.epil
  %shl.i80.epil = shl i64 %84, %sh_prom.i72
  %or.i81.epil = or i64 %shl.i80.epil, %carry.081.i78.epil
  store i64 %or.i81.epil, ptr %arrayidx.i79.epil
  %shr.i82.epil = lshr i64 %84, %sh_prom9.i74
  %indvars.iv.next.i83.epil = add i64 %indvars.iv.i77.epil, 1
  %epil.iter320.next = add i64 %epil.iter320, 1
  %epil.iter320.cmp.not = icmp eq i64 %epil.iter320.next, %xtraiter319
  br i1 %epil.iter320.cmp.not, label %for.cond.cleanup.i85, label %for.body.i76.epil

for.cond.cleanup.i85:                             ; preds = %for.body.i76.epil, %for.cond.cleanup.i85.unr-lcssa
  %shr.i82.lcssa = phi i64 [ %shr.i82.lcssa.ph, %for.cond.cleanup.i85.unr-lcssa ], [ %shr.i82.epil, %for.body.i76.epil ]
  %tobool10.not.i86 = icmp eq i64 %shr.i82.lcssa, 0
  br i1 %tobool10.not.i86, label %if.end18.i56, label %if.then11.i87

for.body.i76:                                     ; preds = %for.body.i76, %for.body.lr.ph.i71.new
  %indvars.iv.i77 = phi i64 [ 0, %for.body.lr.ph.i71.new ], [ %indvars.iv.next.i83.3, %for.body.i76 ]
  %carry.081.i78 = phi i64 [ 0, %for.body.lr.ph.i71.new ], [ %shr.i82.3, %for.body.i76 ]
  %niter324 = phi i64 [ 0, %for.body.lr.ph.i71.new ], [ %niter324.next.3, %for.body.i76 ]
  %arrayidx.i79 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.i77
  %85 = load i64, ptr %arrayidx.i79
  %shl.i80 = shl i64 %85, %sh_prom.i72
  %or.i81 = or i64 %shl.i80, %carry.081.i78
  store i64 %or.i81, ptr %arrayidx.i79
  %shr.i82 = lshr i64 %85, %sh_prom9.i74
  %indvars.iv.next.i83 = or i64 %indvars.iv.i77, 1
  %arrayidx.i79.1 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i83
  %86 = load i64, ptr %arrayidx.i79.1
  %shl.i80.1 = shl i64 %86, %sh_prom.i72
  %or.i81.1 = or i64 %shl.i80.1, %shr.i82
  store i64 %or.i81.1, ptr %arrayidx.i79.1
  %shr.i82.1 = lshr i64 %86, %sh_prom9.i74
  %indvars.iv.next.i83.1 = or i64 %indvars.iv.i77, 2
  %arrayidx.i79.2 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i83.1
  %87 = load i64, ptr %arrayidx.i79.2
  %shl.i80.2 = shl i64 %87, %sh_prom.i72
  %or.i81.2 = or i64 %shl.i80.2, %shr.i82.1
  store i64 %or.i81.2, ptr %arrayidx.i79.2
  %shr.i82.2 = lshr i64 %87, %sh_prom9.i74
  %indvars.iv.next.i83.2 = or i64 %indvars.iv.i77, 3
  %arrayidx.i79.3 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i83.2
  %88 = load i64, ptr %arrayidx.i79.3
  %shl.i80.3 = shl i64 %88, %sh_prom.i72
  %or.i81.3 = or i64 %shl.i80.3, %shr.i82.2
  store i64 %or.i81.3, ptr %arrayidx.i79.3
  %shr.i82.3 = lshr i64 %88, %sh_prom9.i74
  %indvars.iv.next.i83.3 = add i64 %indvars.iv.i77, 4
  %niter324.next.3 = add i64 %niter324, 4
  %niter324.ncmp.3 = icmp eq i64 %niter324.next.3, %unroll_iter323
  br i1 %niter324.ncmp.3, label %for.cond.cleanup.i85.unr-lcssa, label %for.body.i76

if.then11.i87:                                    ; preds = %for.cond.cleanup.i85
  %inc14.i88 = add i32 %82, 1
  store i32 %inc14.i88, ptr %n1.i38
  %arrayidx16.i90 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %wide.trip.count.i75
  store i64 %shr.i82.lcssa, ptr %arrayidx16.i90
  br label %if.end18.i56

if.end18.i56:                                     ; preds = %if.then11.i87, %for.cond.cleanup.i85, %if.end.i50
  %89 = phi i32 [ %82, %for.cond.cleanup.i85 ], [ %inc14.i88, %if.then11.i87 ], [ %82, %if.end.i50 ]
  %tobool19.not.i57 = icmp samesign ult i32 %conv7, 64
  br i1 %tobool19.not.i57, label %if.end8, label %if.then20.i58

if.then20.i58:                                    ; preds = %if.end18.i56
  %i21.082.i59 = add i32 %89, -1
  %cmp2583.i60 = icmp sgt i32 %i21.082.i59, -1
  br i1 %cmp2583.i60, label %iter.check218, label %for.cond.cleanup39.i61

iter.check218:                                    ; preds = %if.then20.i58
  %90 = zext i32 %i21.082.i59 to i64
  %91 = zext i32 %89 to i64
  %min.iters.check216 = icmp ult i32 %89, 4
  br i1 %min.iters.check216, label %for.body27.i64.preheader, label %vector.scevcheck210

vector.scevcheck210:                              ; preds = %iter.check218
  %92 = add i32 %89, %div78.i51
  %93 = add i32 %92, -1
  %94 = icmp sgt i32 %div78.i51, %93
  br i1 %94, label %for.body27.i64.preheader, label %vector.memcheck214

vector.memcheck214:                               ; preds = %vector.scevcheck210
  %95 = add i32 %89, %div78.i51
  %96 = add i32 %95, -1
  %97 = sext i32 %96 to i64
  %98 = sub i64 %90, %97
  %99 = and i64 %98, 2305843009213693936
  %diff.check215 = icmp eq i64 %99, 0
  br i1 %diff.check215, label %for.body27.i64.preheader, label %vector.main.loop.iter.check220

vector.main.loop.iter.check220:                   ; preds = %vector.memcheck214
  %min.iters.check219 = icmp ult i32 %89, 16
  br i1 %min.iters.check219, label %vec.epilog.ph243, label %vector.ph221

vector.ph221:                                     ; preds = %vector.main.loop.iter.check220
  %n.vec223 = and i64 %91, 4294967280
  br label %vector.body224

vector.body224:                                   ; preds = %vector.body224, %vector.ph221
  %index225 = phi i64 [ 0, %vector.ph221 ], [ %index.next238, %vector.body224 ]
  %100 = sub i64 %90, %index225
  %101 = trunc i64 %index225 to i32
  %102 = sub i32 %i21.082.i59, %101
  %103 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %100
  %104 = getelementptr inbounds i8, ptr %103, i64 -24
  %105 = getelementptr inbounds i8, ptr %103, i64 -56
  %106 = getelementptr inbounds i8, ptr %103, i64 -88
  %107 = getelementptr inbounds i8, ptr %103, i64 -120
  %wide.load226 = load <4 x i64>, ptr %104
  %wide.load228 = load <4 x i64>, ptr %105
  %wide.load230 = load <4 x i64>, ptr %106
  %wide.load232 = load <4 x i64>, ptr %107
  %108 = add i32 %div78.i51, %102
  %109 = sext i32 %108 to i64
  %110 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %109
  %111 = getelementptr inbounds i8, ptr %110, i64 -24
  %112 = getelementptr inbounds i8, ptr %110, i64 -56
  %113 = getelementptr inbounds i8, ptr %110, i64 -88
  %114 = getelementptr inbounds i8, ptr %110, i64 -120
  store <4 x i64> %wide.load226, ptr %111
  store <4 x i64> %wide.load228, ptr %112
  store <4 x i64> %wide.load230, ptr %113
  store <4 x i64> %wide.load232, ptr %114
  %index.next238 = add i64 %index225, 16
  %115 = icmp eq i64 %index.next238, %n.vec223
  br i1 %115, label %middle.block239, label %vector.body224

middle.block239:                                  ; preds = %vector.body224
  %cmp.n240 = icmp eq i64 %n.vec223, %91
  br i1 %cmp.n240, label %for.cond.cleanup39.i61, label %vec.epilog.iter.check244

vec.epilog.iter.check244:                         ; preds = %middle.block239
  %ind.end260 = sub i64 %90, %n.vec223
  %n.vec.remaining245 = and i64 %91, 12
  %min.epilog.iters.check246 = icmp eq i64 %n.vec.remaining245, 0
  br i1 %min.epilog.iters.check246, label %for.body27.i64.preheader, label %vec.epilog.ph243

vec.epilog.ph243:                                 ; preds = %vec.epilog.iter.check244, %vector.main.loop.iter.check220
  %vec.epilog.resume.val241 = phi i64 [ %n.vec223, %vec.epilog.iter.check244 ], [ 0, %vector.main.loop.iter.check220 ]
  %n.vec248 = and i64 %91, 4294967292
  %116 = sub i64 %90, %n.vec248
  %invariant.gep342 = getelementptr i8, ptr %a, i64 -24
  %invariant.gep344 = getelementptr i8, ptr %a, i64 -24
  br label %vec.epilog.vector.body249

vec.epilog.vector.body249:                        ; preds = %vec.epilog.vector.body249, %vec.epilog.ph243
  %index250 = phi i64 [ %vec.epilog.resume.val241, %vec.epilog.ph243 ], [ %index.next256, %vec.epilog.vector.body249 ]
  %offset.idx251 = sub i64 %90, %index250
  %117 = trunc i64 %index250 to i32
  %118 = sub i32 %i21.082.i59, %117
  %gep343 = getelementptr [96 x i64], ptr %invariant.gep342, i64 0, i64 %offset.idx251
  %wide.load253 = load <4 x i64>, ptr %gep343
  %119 = add i32 %div78.i51, %118
  %120 = sext i32 %119 to i64
  %gep345 = getelementptr [96 x i64], ptr %invariant.gep344, i64 0, i64 %120
  store <4 x i64> %wide.load253, ptr %gep345
  %index.next256 = add i64 %index250, 4
  %121 = icmp eq i64 %index.next256, %n.vec248
  br i1 %121, label %vec.epilog.middle.block257, label %vec.epilog.vector.body249

vec.epilog.middle.block257:                       ; preds = %vec.epilog.vector.body249
  %cmp.n258 = icmp eq i64 %n.vec248, %91
  br i1 %cmp.n258, label %for.cond.cleanup39.i61, label %for.body27.i64.preheader

for.body27.i64.preheader:                         ; preds = %vec.epilog.middle.block257, %vec.epilog.iter.check244, %vector.memcheck214, %vector.scevcheck210, %iter.check218
  %indvars.iv88.i65.ph = phi i64 [ %90, %iter.check218 ], [ %90, %vector.scevcheck210 ], [ %90, %vector.memcheck214 ], [ %ind.end260, %vec.epilog.iter.check244 ], [ %116, %vec.epilog.middle.block257 ]
  %122 = add i64 %indvars.iv88.i65.ph, 1
  %xtraiter325 = and i64 %122, 7
  %123 = and i64 %indvars.iv88.i65.ph, 7
  %lcmp.mod326.not = icmp eq i64 %123, 7
  br i1 %lcmp.mod326.not, label %for.body27.i64.prol.loopexit, label %for.body27.i64.prol

for.body27.i64.prol:                              ; preds = %for.body27.i64.prol, %for.body27.i64.preheader
  %indvars.iv88.i65.prol = phi i64 [ %indvars.iv.next89.i69.prol, %for.body27.i64.prol ], [ %indvars.iv88.i65.ph, %for.body27.i64.preheader ]
  %prol.iter327 = phi i64 [ %prol.iter327.next, %for.body27.i64.prol ], [ 0, %for.body27.i64.preheader ]
  %arrayidx30.i66.prol = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv88.i65.prol
  %124 = load i64, ptr %arrayidx30.i66.prol
  %125 = trunc i64 %indvars.iv88.i65.prol to i32
  %126 = add i32 %div78.i51, %125
  %idxprom32.i67.prol = sext i32 %126 to i64
  %arrayidx33.i68.prol = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.prol
  store i64 %124, ptr %arrayidx33.i68.prol
  %indvars.iv.next89.i69.prol = add i64 %indvars.iv88.i65.prol, -1
  %prol.iter327.next = add i64 %prol.iter327, 1
  %prol.iter327.cmp.not = icmp eq i64 %prol.iter327.next, %xtraiter325
  br i1 %prol.iter327.cmp.not, label %for.body27.i64.prol.loopexit, label %for.body27.i64.prol

for.body27.i64.prol.loopexit:                     ; preds = %for.body27.i64.prol, %for.body27.i64.preheader
  %indvars.iv88.i65.unr = phi i64 [ %indvars.iv88.i65.ph, %for.body27.i64.preheader ], [ %indvars.iv.next89.i69.prol, %for.body27.i64.prol ]
  %127 = icmp ult i64 %indvars.iv88.i65.ph, 7
  br i1 %127, label %for.cond.cleanup39.i61, label %for.body27.i64

for.body27.i64:                                   ; preds = %for.body27.i64, %for.body27.i64.prol.loopexit
  %indvars.iv88.i65 = phi i64 [ %indvars.iv.next89.i69.7, %for.body27.i64 ], [ %indvars.iv88.i65.unr, %for.body27.i64.prol.loopexit ]
  %arrayidx30.i66 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv88.i65
  %128 = load i64, ptr %arrayidx30.i66
  %129 = trunc i64 %indvars.iv88.i65 to i32
  %130 = add i32 %div78.i51, %129
  %idxprom32.i67 = sext i32 %130 to i64
  %arrayidx33.i68 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67
  store i64 %128, ptr %arrayidx33.i68
  %indvars.iv.next89.i69 = add i64 %indvars.iv88.i65, -1
  %arrayidx30.i66.1 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69
  %131 = load i64, ptr %arrayidx30.i66.1
  %132 = trunc i64 %indvars.iv.next89.i69 to i32
  %133 = add i32 %div78.i51, %132
  %idxprom32.i67.1 = sext i32 %133 to i64
  %arrayidx33.i68.1 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.1
  store i64 %131, ptr %arrayidx33.i68.1
  %indvars.iv.next89.i69.1 = add i64 %indvars.iv88.i65, -2
  %arrayidx30.i66.2 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.1
  %134 = load i64, ptr %arrayidx30.i66.2
  %135 = trunc i64 %indvars.iv.next89.i69.1 to i32
  %136 = add i32 %div78.i51, %135
  %idxprom32.i67.2 = sext i32 %136 to i64
  %arrayidx33.i68.2 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.2
  store i64 %134, ptr %arrayidx33.i68.2
  %indvars.iv.next89.i69.2 = add i64 %indvars.iv88.i65, -3
  %arrayidx30.i66.3 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.2
  %137 = load i64, ptr %arrayidx30.i66.3
  %138 = trunc i64 %indvars.iv.next89.i69.2 to i32
  %139 = add i32 %div78.i51, %138
  %idxprom32.i67.3 = sext i32 %139 to i64
  %arrayidx33.i68.3 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.3
  store i64 %137, ptr %arrayidx33.i68.3
  %indvars.iv.next89.i69.3 = add i64 %indvars.iv88.i65, -4
  %arrayidx30.i66.4 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.3
  %140 = load i64, ptr %arrayidx30.i66.4
  %141 = trunc i64 %indvars.iv.next89.i69.3 to i32
  %142 = add i32 %div78.i51, %141
  %idxprom32.i67.4 = sext i32 %142 to i64
  %arrayidx33.i68.4 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.4
  store i64 %140, ptr %arrayidx33.i68.4
  %indvars.iv.next89.i69.4 = add i64 %indvars.iv88.i65, -5
  %arrayidx30.i66.5 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.4
  %143 = load i64, ptr %arrayidx30.i66.5
  %144 = trunc i64 %indvars.iv.next89.i69.4 to i32
  %145 = add i32 %div78.i51, %144
  %idxprom32.i67.5 = sext i32 %145 to i64
  %arrayidx33.i68.5 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.5
  store i64 %143, ptr %arrayidx33.i68.5
  %indvars.iv.next89.i69.5 = add i64 %indvars.iv88.i65, -6
  %arrayidx30.i66.6 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.5
  %146 = load i64, ptr %arrayidx30.i66.6
  %147 = trunc i64 %indvars.iv.next89.i69.5 to i32
  %148 = add i32 %div78.i51, %147
  %idxprom32.i67.6 = sext i32 %148 to i64
  %arrayidx33.i68.6 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.6
  store i64 %146, ptr %arrayidx33.i68.6
  %indvars.iv.next89.i69.6 = add i64 %indvars.iv88.i65, -7
  %arrayidx30.i66.7 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next89.i69.6
  %149 = load i64, ptr %arrayidx30.i66.7
  %150 = trunc i64 %indvars.iv.next89.i69.6 to i32
  %151 = add i32 %div78.i51, %150
  %idxprom32.i67.7 = sext i32 %151 to i64
  %arrayidx33.i68.7 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom32.i67.7
  store i64 %149, ptr %arrayidx33.i68.7
  %indvars.iv.next89.i69.7 = add i64 %indvars.iv88.i65, -8
  %cmp25.not.i70.7 = icmp eq i64 %indvars.iv.next89.i69.6, 0
  br i1 %cmp25.not.i70.7, label %for.cond.cleanup39.i61, label %for.body27.i64

for.cond.cleanup39.i61:                           ; preds = %for.body27.i64, %for.body27.i64.prol.loopexit, %vec.epilog.middle.block257, %middle.block239, %if.then20.i58
  %152 = lshr i32 %conv7, 3
  %153 = and i32 %152, 536870904
  %154 = zext i32 %153 to i64
  call void @llvm.memset.p0.i64(ptr %a, i8 0, i64 %154, i1 false)
  %add48.i62 = add i32 %89, %div78.i51
  store i32 %add48.i62, ptr %n1.i38
  br label %if.end8

if.end8:                                          ; preds = %for.cond.cleanup39.i61, %if.end18.i56, %if.then5, %stk_copy.exit45
  %n.i92 = getelementptr inbounds i8, ptr %v, i64 1544
  %155 = load i32, ptr %n.i92
  %n1.i93 = getelementptr inbounds i8, ptr %b, i64 768
  store i32 %155, ptr %n1.i93
  %tobool.not.i94 = icmp eq i32 %155, 0
  br i1 %tobool.not.i94, label %stk_copy.exit100, label %if.then.i95

if.then.i95:                                      ; preds = %if.end8
  %pow9 = getelementptr inbounds i8, ptr %v, i64 776
  %conv.i96 = sext i32 %155 to i64
  %mul.i97 = shl i64 %conv.i96, 3
  %call.i.i98 = call ptr @__memcpy_chk(ptr %b, ptr %pow9, i64 %mul.i97, i64 776)
  br label %stk_copy.exit100

stk_copy.exit100:                                 ; preds = %if.then.i95, %if.end8
  call void @stk_mul_u64(ptr %b, i64 %J)
  %cmp10 = icmp sgt i64 %eB, 0
  %.pre181 = load i32, ptr %n1.i93
  br i1 %cmp10, label %lor.lhs.false.i102, label %if.end14

lor.lhs.false.i102:                               ; preds = %stk_copy.exit100
  %cmp1.i104 = icmp eq i32 %.pre181, 0
  br i1 %cmp1.i104, label %if.end14, label %if.end.i105

if.end.i105:                                      ; preds = %lor.lhs.false.i102
  %conv13 = trunc i64 %eB to i32
  %div78.i106 = lshr i32 %conv13, 6
  %rem2.i107 = and i32 %conv13, 63
  %tobool.not.i108 = icmp ne i32 %rem2.i107, 0
  %cmp579.i109 = icmp sgt i32 %.pre181, 0
  %or.cond.i110 = and i1 %tobool.not.i108, %cmp579.i109
  br i1 %or.cond.i110, label %for.body.lr.ph.i126, label %if.end18.i111

for.body.lr.ph.i126:                              ; preds = %if.end.i105
  %sh_prom.i127 = and i64 %eB, 63
  %sub.i128 = sub i32 64, %rem2.i107
  %sh_prom9.i129 = zext i32 %sub.i128 to i64
  %wide.trip.count.i130 = zext i32 %.pre181 to i64
  %xtraiter328 = and i64 %wide.trip.count.i130, 3
  %156 = icmp ult i32 %.pre181, 4
  br i1 %156, label %for.cond.cleanup.i140.unr-lcssa, label %for.body.lr.ph.i126.new

for.body.lr.ph.i126.new:                          ; preds = %for.body.lr.ph.i126
  %unroll_iter332 = and i64 %wide.trip.count.i130, 2147483644
  br label %for.body.i131

for.cond.cleanup.i140.unr-lcssa:                  ; preds = %for.body.i131, %for.body.lr.ph.i126
  %shr.i137.lcssa.ph = phi i64 [ poison, %for.body.lr.ph.i126 ], [ %shr.i137.3, %for.body.i131 ]
  %indvars.iv.i132.unr = phi i64 [ 0, %for.body.lr.ph.i126 ], [ %indvars.iv.next.i138.3, %for.body.i131 ]
  %carry.081.i133.unr = phi i64 [ 0, %for.body.lr.ph.i126 ], [ %shr.i137.3, %for.body.i131 ]
  %lcmp.mod330.not = icmp eq i64 %xtraiter328, 0
  br i1 %lcmp.mod330.not, label %for.cond.cleanup.i140, label %for.body.i131.epil

for.body.i131.epil:                               ; preds = %for.body.i131.epil, %for.cond.cleanup.i140.unr-lcssa
  %indvars.iv.i132.epil = phi i64 [ %indvars.iv.next.i138.epil, %for.body.i131.epil ], [ %indvars.iv.i132.unr, %for.cond.cleanup.i140.unr-lcssa ]
  %carry.081.i133.epil = phi i64 [ %shr.i137.epil, %for.body.i131.epil ], [ %carry.081.i133.unr, %for.cond.cleanup.i140.unr-lcssa ]
  %epil.iter329 = phi i64 [ %epil.iter329.next, %for.body.i131.epil ], [ 0, %for.cond.cleanup.i140.unr-lcssa ]
  %arrayidx.i134.epil = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.i132.epil
  %157 = load i64, ptr %arrayidx.i134.epil
  %shl.i135.epil = shl i64 %157, %sh_prom.i127
  %or.i136.epil = or i64 %shl.i135.epil, %carry.081.i133.epil
  store i64 %or.i136.epil, ptr %arrayidx.i134.epil
  %shr.i137.epil = lshr i64 %157, %sh_prom9.i129
  %indvars.iv.next.i138.epil = add i64 %indvars.iv.i132.epil, 1
  %epil.iter329.next = add i64 %epil.iter329, 1
  %epil.iter329.cmp.not = icmp eq i64 %epil.iter329.next, %xtraiter328
  br i1 %epil.iter329.cmp.not, label %for.cond.cleanup.i140, label %for.body.i131.epil

for.cond.cleanup.i140:                            ; preds = %for.body.i131.epil, %for.cond.cleanup.i140.unr-lcssa
  %shr.i137.lcssa = phi i64 [ %shr.i137.lcssa.ph, %for.cond.cleanup.i140.unr-lcssa ], [ %shr.i137.epil, %for.body.i131.epil ]
  %tobool10.not.i141 = icmp eq i64 %shr.i137.lcssa, 0
  br i1 %tobool10.not.i141, label %if.end18.i111, label %if.then11.i142

for.body.i131:                                    ; preds = %for.body.i131, %for.body.lr.ph.i126.new
  %indvars.iv.i132 = phi i64 [ 0, %for.body.lr.ph.i126.new ], [ %indvars.iv.next.i138.3, %for.body.i131 ]
  %carry.081.i133 = phi i64 [ 0, %for.body.lr.ph.i126.new ], [ %shr.i137.3, %for.body.i131 ]
  %niter333 = phi i64 [ 0, %for.body.lr.ph.i126.new ], [ %niter333.next.3, %for.body.i131 ]
  %arrayidx.i134 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.i132
  %158 = load i64, ptr %arrayidx.i134
  %shl.i135 = shl i64 %158, %sh_prom.i127
  %or.i136 = or i64 %shl.i135, %carry.081.i133
  store i64 %or.i136, ptr %arrayidx.i134
  %shr.i137 = lshr i64 %158, %sh_prom9.i129
  %indvars.iv.next.i138 = or i64 %indvars.iv.i132, 1
  %arrayidx.i134.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i138
  %159 = load i64, ptr %arrayidx.i134.1
  %shl.i135.1 = shl i64 %159, %sh_prom.i127
  %or.i136.1 = or i64 %shl.i135.1, %shr.i137
  store i64 %or.i136.1, ptr %arrayidx.i134.1
  %shr.i137.1 = lshr i64 %159, %sh_prom9.i129
  %indvars.iv.next.i138.1 = or i64 %indvars.iv.i132, 2
  %arrayidx.i134.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i138.1
  %160 = load i64, ptr %arrayidx.i134.2
  %shl.i135.2 = shl i64 %160, %sh_prom.i127
  %or.i136.2 = or i64 %shl.i135.2, %shr.i137.1
  store i64 %or.i136.2, ptr %arrayidx.i134.2
  %shr.i137.2 = lshr i64 %160, %sh_prom9.i129
  %indvars.iv.next.i138.2 = or i64 %indvars.iv.i132, 3
  %arrayidx.i134.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next.i138.2
  %161 = load i64, ptr %arrayidx.i134.3
  %shl.i135.3 = shl i64 %161, %sh_prom.i127
  %or.i136.3 = or i64 %shl.i135.3, %shr.i137.2
  store i64 %or.i136.3, ptr %arrayidx.i134.3
  %shr.i137.3 = lshr i64 %161, %sh_prom9.i129
  %indvars.iv.next.i138.3 = add i64 %indvars.iv.i132, 4
  %niter333.next.3 = add i64 %niter333, 4
  %niter333.ncmp.3 = icmp eq i64 %niter333.next.3, %unroll_iter332
  br i1 %niter333.ncmp.3, label %for.cond.cleanup.i140.unr-lcssa, label %for.body.i131

if.then11.i142:                                   ; preds = %for.cond.cleanup.i140
  %inc14.i143 = add i32 %.pre181, 1
  %arrayidx16.i145 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %wide.trip.count.i130
  store i64 %shr.i137.lcssa, ptr %arrayidx16.i145
  br label %if.end18.i111

if.end18.i111:                                    ; preds = %if.then11.i142, %for.cond.cleanup.i140, %if.end.i105
  %162 = phi i32 [ %.pre181, %for.cond.cleanup.i140 ], [ %inc14.i143, %if.then11.i142 ], [ %.pre181, %if.end.i105 ]
  %tobool19.not.i112 = icmp samesign ult i64 %eB, 64
  br i1 %tobool19.not.i112, label %if.end14, label %if.then20.i113

if.then20.i113:                                   ; preds = %if.end18.i111
  %i21.082.i114 = add i32 %162, -1
  %cmp2583.i115 = icmp sgt i32 %i21.082.i114, -1
  br i1 %cmp2583.i115, label %iter.check269, label %for.cond.cleanup39.i116

iter.check269:                                    ; preds = %if.then20.i113
  %163 = zext i32 %i21.082.i114 to i64
  %164 = zext i32 %162 to i64
  %min.iters.check267 = icmp ult i32 %162, 4
  br i1 %min.iters.check267, label %for.body27.i119.preheader, label %vector.scevcheck261

vector.scevcheck261:                              ; preds = %iter.check269
  %165 = add i32 %162, %div78.i106
  %166 = add i32 %165, -1
  %167 = icmp sgt i32 %div78.i106, %166
  br i1 %167, label %for.body27.i119.preheader, label %vector.memcheck265

vector.memcheck265:                               ; preds = %vector.scevcheck261
  %168 = add i32 %162, %div78.i106
  %169 = add i32 %168, -1
  %170 = sext i32 %169 to i64
  %171 = sub i64 %163, %170
  %172 = and i64 %171, 2305843009213693936
  %diff.check266 = icmp eq i64 %172, 0
  br i1 %diff.check266, label %for.body27.i119.preheader, label %vector.main.loop.iter.check271

vector.main.loop.iter.check271:                   ; preds = %vector.memcheck265
  %min.iters.check270 = icmp ult i32 %162, 16
  br i1 %min.iters.check270, label %vec.epilog.ph294, label %vector.ph272

vector.ph272:                                     ; preds = %vector.main.loop.iter.check271
  %n.vec274 = and i64 %164, 4294967280
  br label %vector.body275

vector.body275:                                   ; preds = %vector.body275, %vector.ph272
  %index276 = phi i64 [ 0, %vector.ph272 ], [ %index.next289, %vector.body275 ]
  %173 = sub i64 %163, %index276
  %174 = trunc i64 %index276 to i32
  %175 = sub i32 %i21.082.i114, %174
  %176 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %173
  %177 = getelementptr inbounds i8, ptr %176, i64 -24
  %178 = getelementptr inbounds i8, ptr %176, i64 -56
  %179 = getelementptr inbounds i8, ptr %176, i64 -88
  %180 = getelementptr inbounds i8, ptr %176, i64 -120
  %wide.load277 = load <4 x i64>, ptr %177
  %wide.load279 = load <4 x i64>, ptr %178
  %wide.load281 = load <4 x i64>, ptr %179
  %wide.load283 = load <4 x i64>, ptr %180
  %181 = add i32 %div78.i106, %175
  %182 = sext i32 %181 to i64
  %183 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %182
  %184 = getelementptr inbounds i8, ptr %183, i64 -24
  %185 = getelementptr inbounds i8, ptr %183, i64 -56
  %186 = getelementptr inbounds i8, ptr %183, i64 -88
  %187 = getelementptr inbounds i8, ptr %183, i64 -120
  store <4 x i64> %wide.load277, ptr %184
  store <4 x i64> %wide.load279, ptr %185
  store <4 x i64> %wide.load281, ptr %186
  store <4 x i64> %wide.load283, ptr %187
  %index.next289 = add i64 %index276, 16
  %188 = icmp eq i64 %index.next289, %n.vec274
  br i1 %188, label %middle.block290, label %vector.body275

middle.block290:                                  ; preds = %vector.body275
  %cmp.n291 = icmp eq i64 %n.vec274, %164
  br i1 %cmp.n291, label %for.cond.cleanup39.i116, label %vec.epilog.iter.check295

vec.epilog.iter.check295:                         ; preds = %middle.block290
  %ind.end311 = sub i64 %163, %n.vec274
  %n.vec.remaining296 = and i64 %164, 12
  %min.epilog.iters.check297 = icmp eq i64 %n.vec.remaining296, 0
  br i1 %min.epilog.iters.check297, label %for.body27.i119.preheader, label %vec.epilog.ph294

vec.epilog.ph294:                                 ; preds = %vec.epilog.iter.check295, %vector.main.loop.iter.check271
  %vec.epilog.resume.val292 = phi i64 [ %n.vec274, %vec.epilog.iter.check295 ], [ 0, %vector.main.loop.iter.check271 ]
  %n.vec299 = and i64 %164, 4294967292
  %189 = sub i64 %163, %n.vec299
  %invariant.gep346 = getelementptr i8, ptr %b, i64 -24
  %invariant.gep348 = getelementptr i8, ptr %b, i64 -24
  br label %vec.epilog.vector.body300

vec.epilog.vector.body300:                        ; preds = %vec.epilog.vector.body300, %vec.epilog.ph294
  %index301 = phi i64 [ %vec.epilog.resume.val292, %vec.epilog.ph294 ], [ %index.next307, %vec.epilog.vector.body300 ]
  %offset.idx302 = sub i64 %163, %index301
  %190 = trunc i64 %index301 to i32
  %191 = sub i32 %i21.082.i114, %190
  %gep347 = getelementptr [96 x i64], ptr %invariant.gep346, i64 0, i64 %offset.idx302
  %wide.load304 = load <4 x i64>, ptr %gep347
  %192 = add i32 %div78.i106, %191
  %193 = sext i32 %192 to i64
  %gep349 = getelementptr [96 x i64], ptr %invariant.gep348, i64 0, i64 %193
  store <4 x i64> %wide.load304, ptr %gep349
  %index.next307 = add i64 %index301, 4
  %194 = icmp eq i64 %index.next307, %n.vec299
  br i1 %194, label %vec.epilog.middle.block308, label %vec.epilog.vector.body300

vec.epilog.middle.block308:                       ; preds = %vec.epilog.vector.body300
  %cmp.n309 = icmp eq i64 %n.vec299, %164
  br i1 %cmp.n309, label %for.cond.cleanup39.i116, label %for.body27.i119.preheader

for.body27.i119.preheader:                        ; preds = %vec.epilog.middle.block308, %vec.epilog.iter.check295, %vector.memcheck265, %vector.scevcheck261, %iter.check269
  %indvars.iv88.i120.ph = phi i64 [ %163, %iter.check269 ], [ %163, %vector.scevcheck261 ], [ %163, %vector.memcheck265 ], [ %ind.end311, %vec.epilog.iter.check295 ], [ %189, %vec.epilog.middle.block308 ]
  %195 = add i64 %indvars.iv88.i120.ph, 1
  %xtraiter334 = and i64 %195, 7
  %196 = and i64 %indvars.iv88.i120.ph, 7
  %lcmp.mod335.not = icmp eq i64 %196, 7
  br i1 %lcmp.mod335.not, label %for.body27.i119.prol.loopexit, label %for.body27.i119.prol

for.body27.i119.prol:                             ; preds = %for.body27.i119.prol, %for.body27.i119.preheader
  %indvars.iv88.i120.prol = phi i64 [ %indvars.iv.next89.i124.prol, %for.body27.i119.prol ], [ %indvars.iv88.i120.ph, %for.body27.i119.preheader ]
  %prol.iter336 = phi i64 [ %prol.iter336.next, %for.body27.i119.prol ], [ 0, %for.body27.i119.preheader ]
  %arrayidx30.i121.prol = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv88.i120.prol
  %197 = load i64, ptr %arrayidx30.i121.prol
  %198 = trunc i64 %indvars.iv88.i120.prol to i32
  %199 = add i32 %div78.i106, %198
  %idxprom32.i122.prol = sext i32 %199 to i64
  %arrayidx33.i123.prol = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.prol
  store i64 %197, ptr %arrayidx33.i123.prol
  %indvars.iv.next89.i124.prol = add i64 %indvars.iv88.i120.prol, -1
  %prol.iter336.next = add i64 %prol.iter336, 1
  %prol.iter336.cmp.not = icmp eq i64 %prol.iter336.next, %xtraiter334
  br i1 %prol.iter336.cmp.not, label %for.body27.i119.prol.loopexit, label %for.body27.i119.prol

for.body27.i119.prol.loopexit:                    ; preds = %for.body27.i119.prol, %for.body27.i119.preheader
  %indvars.iv88.i120.unr = phi i64 [ %indvars.iv88.i120.ph, %for.body27.i119.preheader ], [ %indvars.iv.next89.i124.prol, %for.body27.i119.prol ]
  %200 = icmp ult i64 %indvars.iv88.i120.ph, 7
  br i1 %200, label %for.cond.cleanup39.i116, label %for.body27.i119

for.body27.i119:                                  ; preds = %for.body27.i119, %for.body27.i119.prol.loopexit
  %indvars.iv88.i120 = phi i64 [ %indvars.iv.next89.i124.7, %for.body27.i119 ], [ %indvars.iv88.i120.unr, %for.body27.i119.prol.loopexit ]
  %arrayidx30.i121 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv88.i120
  %201 = load i64, ptr %arrayidx30.i121
  %202 = trunc i64 %indvars.iv88.i120 to i32
  %203 = add i32 %div78.i106, %202
  %idxprom32.i122 = sext i32 %203 to i64
  %arrayidx33.i123 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122
  store i64 %201, ptr %arrayidx33.i123
  %indvars.iv.next89.i124 = add i64 %indvars.iv88.i120, -1
  %arrayidx30.i121.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124
  %204 = load i64, ptr %arrayidx30.i121.1
  %205 = trunc i64 %indvars.iv.next89.i124 to i32
  %206 = add i32 %div78.i106, %205
  %idxprom32.i122.1 = sext i32 %206 to i64
  %arrayidx33.i123.1 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.1
  store i64 %204, ptr %arrayidx33.i123.1
  %indvars.iv.next89.i124.1 = add i64 %indvars.iv88.i120, -2
  %arrayidx30.i121.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.1
  %207 = load i64, ptr %arrayidx30.i121.2
  %208 = trunc i64 %indvars.iv.next89.i124.1 to i32
  %209 = add i32 %div78.i106, %208
  %idxprom32.i122.2 = sext i32 %209 to i64
  %arrayidx33.i123.2 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.2
  store i64 %207, ptr %arrayidx33.i123.2
  %indvars.iv.next89.i124.2 = add i64 %indvars.iv88.i120, -3
  %arrayidx30.i121.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.2
  %210 = load i64, ptr %arrayidx30.i121.3
  %211 = trunc i64 %indvars.iv.next89.i124.2 to i32
  %212 = add i32 %div78.i106, %211
  %idxprom32.i122.3 = sext i32 %212 to i64
  %arrayidx33.i123.3 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.3
  store i64 %210, ptr %arrayidx33.i123.3
  %indvars.iv.next89.i124.3 = add i64 %indvars.iv88.i120, -4
  %arrayidx30.i121.4 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.3
  %213 = load i64, ptr %arrayidx30.i121.4
  %214 = trunc i64 %indvars.iv.next89.i124.3 to i32
  %215 = add i32 %div78.i106, %214
  %idxprom32.i122.4 = sext i32 %215 to i64
  %arrayidx33.i123.4 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.4
  store i64 %213, ptr %arrayidx33.i123.4
  %indvars.iv.next89.i124.4 = add i64 %indvars.iv88.i120, -5
  %arrayidx30.i121.5 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.4
  %216 = load i64, ptr %arrayidx30.i121.5
  %217 = trunc i64 %indvars.iv.next89.i124.4 to i32
  %218 = add i32 %div78.i106, %217
  %idxprom32.i122.5 = sext i32 %218 to i64
  %arrayidx33.i123.5 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.5
  store i64 %216, ptr %arrayidx33.i123.5
  %indvars.iv.next89.i124.5 = add i64 %indvars.iv88.i120, -6
  %arrayidx30.i121.6 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.5
  %219 = load i64, ptr %arrayidx30.i121.6
  %220 = trunc i64 %indvars.iv.next89.i124.5 to i32
  %221 = add i32 %div78.i106, %220
  %idxprom32.i122.6 = sext i32 %221 to i64
  %arrayidx33.i123.6 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.6
  store i64 %219, ptr %arrayidx33.i123.6
  %indvars.iv.next89.i124.6 = add i64 %indvars.iv88.i120, -7
  %arrayidx30.i121.7 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %indvars.iv.next89.i124.6
  %222 = load i64, ptr %arrayidx30.i121.7
  %223 = trunc i64 %indvars.iv.next89.i124.6 to i32
  %224 = add i32 %div78.i106, %223
  %idxprom32.i122.7 = sext i32 %224 to i64
  %arrayidx33.i123.7 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom32.i122.7
  store i64 %222, ptr %arrayidx33.i123.7
  %indvars.iv.next89.i124.7 = add i64 %indvars.iv88.i120, -8
  %cmp25.not.i125.7 = icmp eq i64 %indvars.iv.next89.i124.6, 0
  br i1 %cmp25.not.i125.7, label %for.cond.cleanup39.i116, label %for.body27.i119

for.cond.cleanup39.i116:                          ; preds = %for.body27.i119, %for.body27.i119.prol.loopexit, %vec.epilog.middle.block308, %middle.block290, %if.then20.i113
  %225 = lshr i64 %eB, 3
  %226 = and i64 %225, 536870904
  call void @llvm.memset.p0.i64(ptr %b, i8 0, i64 %226, i1 false)
  %add48.i117 = add i32 %162, %div78.i106
  br label %if.end14

if.end14:                                         ; preds = %for.cond.cleanup39.i116, %if.end18.i111, %lor.lhs.false.i102, %stk_copy.exit100
  %227 = phi i32 [ %add48.i117, %for.cond.cleanup39.i116 ], [ %162, %if.end18.i111 ], [ 0, %lor.lhs.false.i102 ], [ %.pre181, %stk_copy.exit100 ]
  %228 = load i32, ptr %n1.i38
  %cmp.not.i149 = icmp eq i32 %228, %227
  br i1 %cmp.not.i149, label %for.cond.preheader.i154, label %if.then.i150

for.cond.preheader.i154:                          ; preds = %if.end14
  %229 = zext i32 %227 to i64
  br label %for.cond.i155

if.then.i150:                                     ; preds = %if.end14
  %cmp4.i151 = icmp slt i32 %228, %227
  %cond.i152 = select i1 %cmp4.i151, i32 -1, i32 1
  br label %cleanup

for.cond.i155:                                    ; preds = %for.body.i159, %for.cond.preheader.i154
  %indvars.iv.i156 = phi i64 [ %229, %for.cond.preheader.i154 ], [ %indvars.iv.next.i157, %for.body.i159 ]
  %indvars.iv.next.i157 = add i64 %indvars.iv.i156, -1
  %230 = and i64 %indvars.iv.next.i157, 2147483648
  %cmp6.not.i158 = icmp eq i64 %230, 0
  br i1 %cmp6.not.i158, label %for.body.i159, label %cleanup

for.body.i159:                                    ; preds = %for.cond.i155
  %idxprom.i160 = and i64 %indvars.iv.next.i157, 2147483647
  %arrayidx.i161 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %idxprom.i160
  %231 = load i64, ptr %arrayidx.i161
  %arrayidx9.i162 = getelementptr inbounds [96 x i64], ptr %b, i64 0, i64 %idxprom.i160
  %232 = load i64, ptr %arrayidx9.i162
  %cmp10.not.i163 = icmp eq i64 %231, %232
  br i1 %cmp10.not.i163, label %for.cond.i155, label %if.then11.i164

if.then11.i164:                                   ; preds = %for.body.i159
  %cmp18.i165 = icmp ult i64 %231, %232
  %cond19.i166 = select i1 %cmp18.i165, i32 -1, i32 1
  br label %cleanup

cleanup:                                          ; preds = %if.then11.i164, %for.cond.i155, %if.then.i150, %if.then11.i36, %for.cond.i, %if.then.i31
  %retval.0 = phi i32 [ %cond.i152, %if.then.i150 ], [ %cond19.i166, %if.then11.i164 ], [ %spec.select, %if.then.i31 ], [ %spec.select172, %if.then11.i36 ], [ 0, %for.cond.i155 ], [ 1, %for.cond.i ]
  call void @llvm.lifetime.end.p0(i64 776, ptr %b)
  call void @llvm.lifetime.end.p0(i64 776, ptr %a)
  ret i32 %retval.0
}
