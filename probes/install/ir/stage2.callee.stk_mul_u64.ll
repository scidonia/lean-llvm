; The stage-2 callee `stk_mul_u64`, as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; `noinline` on every helper and on `stk_mul_u64`, then the same token strip
; capture-stage2.sh applies.  `stk_mul_u64` calls `stk_mul_add`, which the emission inlines, so the body is the multiply with its `unsigned __int128` carry chain in the loop and the tail word the trailing `while` appends.  It calls nothing and reads no global.
;
define void @stk_mul_u64(ptr %a, i64 %m) {
entry:
  %n.i = getelementptr inbounds i8, ptr %a, i64 768
  %0 = load i32, ptr %n.i
  %cmp28.i = icmp sgt i32 %0, 0
  br i1 %cmp28.i, label %for.body.lr.ph.i, label %stk_mul_add.exit

for.body.lr.ph.i:                                 ; preds = %entry
  %conv3.i = zext i64 %m to i128
  %wide.trip.count.i = zext i32 %0 to i64
  %xtraiter = and i64 %wide.trip.count.i, 3
  %1 = icmp ult i32 %0, 4
  br i1 %1, label %while.cond.preheader.i.unr-lcssa, label %for.body.lr.ph.i.new

for.body.lr.ph.i.new:                             ; preds = %for.body.lr.ph.i
  %unroll_iter = and i64 %wide.trip.count.i, 2147483644
  br label %for.body.i

while.cond.preheader.i.unr-lcssa.loopexit:        ; preds = %for.body.i
  %extract.t6 = trunc i128 %shr.i.3 to i64
  br label %while.cond.preheader.i.unr-lcssa

while.cond.preheader.i.unr-lcssa:                 ; preds = %while.cond.preheader.i.unr-lcssa.loopexit, %for.body.lr.ph.i
  %add4.i.lcssa.ph = phi i128 [ poison, %for.body.lr.ph.i ], [ %add4.i.3, %while.cond.preheader.i.unr-lcssa.loopexit ]
  %shr.i.lcssa.ph.off0 = phi i64 [ poison, %for.body.lr.ph.i ], [ %extract.t6, %while.cond.preheader.i.unr-lcssa.loopexit ]
  %indvars.iv.i.unr = phi i64 [ 0, %for.body.lr.ph.i ], [ %indvars.iv.next.i.3, %while.cond.preheader.i.unr-lcssa.loopexit ]
  %carry.029.i.unr = phi i128 [ 0, %for.body.lr.ph.i ], [ %shr.i.3, %while.cond.preheader.i.unr-lcssa.loopexit ]
  %lcmp.mod.not = icmp eq i64 %xtraiter, 0
  br i1 %lcmp.mod.not, label %while.cond.preheader.i, label %for.body.i.epil

for.body.i.epil:                                  ; preds = %for.body.i.epil, %while.cond.preheader.i.unr-lcssa
  %indvars.iv.i.epil = phi i64 [ %indvars.iv.next.i.epil, %for.body.i.epil ], [ %indvars.iv.i.unr, %while.cond.preheader.i.unr-lcssa ]
  %carry.029.i.epil = phi i128 [ %shr.i.epil, %for.body.i.epil ], [ %carry.029.i.unr, %while.cond.preheader.i.unr-lcssa ]
  %epil.iter = phi i64 [ %epil.iter.next, %for.body.i.epil ], [ 0, %while.cond.preheader.i.unr-lcssa ]
  %arrayidx.i.epil = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.i.epil
  %2 = load i64, ptr %arrayidx.i.epil
  %conv2.i.epil = zext i64 %2 to i128
  %mul.i.epil = mul i128 %conv2.i.epil, %conv3.i
  %add4.i.epil = add i128 %mul.i.epil, %carry.029.i.epil
  %conv5.i.epil = trunc i128 %add4.i.epil to i64
  store i64 %conv5.i.epil, ptr %arrayidx.i.epil
  %shr.i.epil = lshr i128 %add4.i.epil, 64
  %indvars.iv.next.i.epil = add i64 %indvars.iv.i.epil, 1
  %epil.iter.next = add i64 %epil.iter, 1
  %epil.iter.cmp.not = icmp eq i64 %epil.iter.next, %xtraiter
  br i1 %epil.iter.cmp.not, label %while.cond.preheader.i.epilog-lcssa, label %for.body.i.epil

while.cond.preheader.i.epilog-lcssa:              ; preds = %for.body.i.epil
  %extract.t5 = trunc i128 %shr.i.epil to i64
  br label %while.cond.preheader.i

while.cond.preheader.i:                           ; preds = %while.cond.preheader.i.epilog-lcssa, %while.cond.preheader.i.unr-lcssa
  %add4.i.lcssa = phi i128 [ %add4.i.lcssa.ph, %while.cond.preheader.i.unr-lcssa ], [ %add4.i.epil, %while.cond.preheader.i.epilog-lcssa ]
  %shr.i.lcssa.off0 = phi i64 [ %shr.i.lcssa.ph.off0, %while.cond.preheader.i.unr-lcssa ], [ %extract.t5, %while.cond.preheader.i.epilog-lcssa ]
  %tobool.not31.i = icmp ult i128 %add4.i.lcssa, 18446744073709551616
  br i1 %tobool.not31.i, label %stk_mul_add.exit, label %while.body.us.i

while.body.us.i:                                  ; preds = %while.cond.preheader.i
  %inc12.us.i = add i32 %0, 1
  %arrayidx14.us.i = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %wide.trip.count.i
  store i64 %shr.i.lcssa.off0, ptr %arrayidx14.us.i
  store i32 %inc12.us.i, ptr %n.i
  br label %stk_mul_add.exit

for.body.i:                                       ; preds = %for.body.i, %for.body.lr.ph.i.new
  %indvars.iv.i = phi i64 [ 0, %for.body.lr.ph.i.new ], [ %indvars.iv.next.i.3, %for.body.i ]
  %carry.029.i = phi i128 [ 0, %for.body.lr.ph.i.new ], [ %shr.i.3, %for.body.i ]
  %niter = phi i64 [ 0, %for.body.lr.ph.i.new ], [ %niter.next.3, %for.body.i ]
  %arrayidx.i = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.i
  %3 = load i64, ptr %arrayidx.i
  %conv2.i = zext i64 %3 to i128
  %mul.i = mul i128 %conv2.i, %conv3.i
  %add4.i = add i128 %mul.i, %carry.029.i
  %conv5.i = trunc i128 %add4.i to i64
  store i64 %conv5.i, ptr %arrayidx.i
  %shr.i = lshr i128 %add4.i, 64
  %indvars.iv.next.i = or i64 %indvars.iv.i, 1
  %arrayidx.i.1 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i
  %4 = load i64, ptr %arrayidx.i.1
  %conv2.i.1 = zext i64 %4 to i128
  %mul.i.1 = mul i128 %conv2.i.1, %conv3.i
  %add4.i.1 = add i128 %mul.i.1, %shr.i
  %conv5.i.1 = trunc i128 %add4.i.1 to i64
  store i64 %conv5.i.1, ptr %arrayidx.i.1
  %shr.i.1 = lshr i128 %add4.i.1, 64
  %indvars.iv.next.i.1 = or i64 %indvars.iv.i, 2
  %arrayidx.i.2 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i.1
  %5 = load i64, ptr %arrayidx.i.2
  %conv2.i.2 = zext i64 %5 to i128
  %mul.i.2 = mul i128 %conv2.i.2, %conv3.i
  %add4.i.2 = add i128 %mul.i.2, %shr.i.1
  %conv5.i.2 = trunc i128 %add4.i.2 to i64
  store i64 %conv5.i.2, ptr %arrayidx.i.2
  %shr.i.2 = lshr i128 %add4.i.2, 64
  %indvars.iv.next.i.2 = or i64 %indvars.iv.i, 3
  %arrayidx.i.3 = getelementptr inbounds [96 x i64], ptr %a, i64 0, i64 %indvars.iv.next.i.2
  %6 = load i64, ptr %arrayidx.i.3
  %conv2.i.3 = zext i64 %6 to i128
  %mul.i.3 = mul i128 %conv2.i.3, %conv3.i
  %add4.i.3 = add i128 %mul.i.3, %shr.i.2
  %conv5.i.3 = trunc i128 %add4.i.3 to i64
  store i64 %conv5.i.3, ptr %arrayidx.i.3
  %shr.i.3 = lshr i128 %add4.i.3, 64
  %indvars.iv.next.i.3 = add i64 %indvars.iv.i, 4
  %niter.next.3 = add i64 %niter, 4
  %niter.ncmp.3 = icmp eq i64 %niter.next.3, %unroll_iter
  br i1 %niter.ncmp.3, label %while.cond.preheader.i.unr-lcssa.loopexit, label %for.body.i

stk_mul_add.exit:                                 ; preds = %while.body.us.i, %while.cond.preheader.i, %entry
  ret void
}
