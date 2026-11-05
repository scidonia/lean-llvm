define void @ci2(ptr %buf, ptr %cmask, ptr %imask, i64 %nblocks) {
entry:
  br label %loop
loop:
  %b = phi i64 [ 0, %entry ], [ %bn, %blk.end ]
  %open = phi i64 [ 0, %entry ], [ %openn, %blk.end ]
  %ppar = phi i64 [ 0, %entry ], [ %pparn, %blk.end ]
  %carry = phi i64 [ 0, %entry ], [ %carryn, %blk.end ]
  %off = shl i64 %b, 6
  ; ---- classify block (c2)
  %addrc2 = getelementptr inbounds i8, ptr %buf, i64 %off
  %addr2c2 = getelementptr inbounds i8, ptr %addrc2, i64 32
  %v0c2 = load <32 x i8>, ptr %addrc2
  %v1c2 = load <32 x i8>, ptr %addr2c2
  %qc20c = icmp eq <32 x i8> %v0c2, <i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34>
  %qc20s = bitcast <32 x i1> %qc20c to i32
  %bc20c = icmp eq <32 x i8> %v0c2, <i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92>
  %bc20s = bitcast <32 x i1> %bc20c to i32
  %sc200 = icmp eq <32 x i8> %v0c2, <i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44>
  %sc201 = icmp eq <32 x i8> %v0c2, <i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58>
  %sc20acc1 = or <32 x i1> %sc200, %sc201
  %sc202 = icmp eq <32 x i8> %v0c2, <i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123>
  %sc20acc2 = or <32 x i1> %sc20acc1, %sc202
  %sc203 = icmp eq <32 x i8> %v0c2, <i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125>
  %sc20acc3 = or <32 x i1> %sc20acc2, %sc203
  %sc204 = icmp eq <32 x i8> %v0c2, <i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91>
  %sc20acc4 = or <32 x i1> %sc20acc3, %sc204
  %sc205 = icmp eq <32 x i8> %v0c2, <i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93>
  %sc20acc5 = or <32 x i1> %sc20acc4, %sc205
  %sc20s = bitcast <32 x i1> %sc20acc5 to i32
  %qc21c = icmp eq <32 x i8> %v1c2, <i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34, i8 34>
  %qc21s = bitcast <32 x i1> %qc21c to i32
  %bc21c = icmp eq <32 x i8> %v1c2, <i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92, i8 92>
  %bc21s = bitcast <32 x i1> %bc21c to i32
  %sc210 = icmp eq <32 x i8> %v1c2, <i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44, i8 44>
  %sc211 = icmp eq <32 x i8> %v1c2, <i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58, i8 58>
  %sc21acc1 = or <32 x i1> %sc210, %sc211
  %sc212 = icmp eq <32 x i8> %v1c2, <i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123, i8 123>
  %sc21acc2 = or <32 x i1> %sc21acc1, %sc212
  %sc213 = icmp eq <32 x i8> %v1c2, <i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125, i8 125>
  %sc21acc3 = or <32 x i1> %sc21acc2, %sc213
  %sc214 = icmp eq <32 x i8> %v1c2, <i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91, i8 91>
  %sc21acc4 = or <32 x i1> %sc21acc3, %sc214
  %sc215 = icmp eq <32 x i8> %v1c2, <i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93, i8 93>
  %sc21acc5 = or <32 x i1> %sc21acc4, %sc215
  %sc21s = bitcast <32 x i1> %sc21acc5 to i32
  %qloc2 = zext i32 %qc20s to i64
  %qhi0c2 = zext i32 %qc21s to i64
  %qhic2 = shl i64 %qhi0c2, 32
  %qallc2 = or i64 %qloc2, %qhic2
  %bloc2 = zext i32 %bc20s to i64
  %bhi0c2 = zext i32 %bc21s to i64
  %bhic2 = shl i64 %bhi0c2, 32
  %ballc2 = or i64 %bloc2, %bhic2
  %sloc2 = zext i32 %sc20s to i64
  %shi0c2 = zext i32 %sc21s to i64
  %shic2 = shl i64 %shi0c2, 32
  %sallc2 = or i64 %sloc2, %shic2
  %qrawc2 = or i64 %qallc2, 0
  %ssc2 = or i64 %sallc2, 0
  %bsc2 = or i64 %ballc2, 0
  %bs1c2 = shl i64 %bsc2, 1
  %opbc2 = or i64 %bs1c2, %open
  %nstartsc2 = xor i64 %opbc2, -1
  %starts0c2 = and i64 %bsc2, %nstartsc2
  %bs0c2 = and i64 %bsc2, 1
  %fakec2 = and i64 %bs0c2, %open
  %startsc2 = or i64 %starts0c2, %fakec2
  %bsrc2 = lshr i64 %bsc2, 1
  %nlastsc2 = xor i64 %bsrc2, -1
  %lastsc2 = and i64 %bsc2, %nlastsc2
  %afterc2 = shl i64 %lastsc2, 1
  %flipc2 = and i64 %open, %ppar
  %altc2 = xor i64 6148914691236517205, %flipc2
  %sec2 = call i64 @llvm.x86.bmi.pext.64(i64 %altc2, i64 %startsc2)
  %lec2 = call i64 @llvm.x86.bmi.pext.64(i64 6148914691236517205, i64 %lastsc2)
  %ddc2 = xor i64 %sec2, %lec2
  %nrc2 = xor i64 %ddc2, -1
  %escmc2 = call i64 @llvm.x86.bmi.pdep.64(i64 %nrc2, i64 %afterc2)
  %nb0c2 = xor i64 %bs0c2, -1
  %needb0c2 = and i64 %open, %nb0c2
  %b0bitc2 = and i64 %needb0c2, %ppar
  %escc2 = or i64 %escmc2, %b0bitc2
  %topc2 = lshr i64 %bsc2, 63
  %invc2 = xor i64 %bsc2, -1
  %lzc2 = call i64 @llvm.ctlz.i64(i64 %invc2, i1 false)
  %lzpc2 = and i64 %lzc2, 1
  %allonc2 = icmp eq i64 %bsc2, -1
  %opennzc2 = icmp ne i64 %open, 0
  %keepc2 = and i1 %allonc2, %opennzc2
  %contribc2 = select i1 %keepc2, i64 %ppar, i64 0
  %ppc2 = xor i64 %contribc2, %lzpc2
  %topvc2 = or i64 %topc2, 0
  %ppnc2 = and i64 %topc2, %ppc2
  %nescc2 = xor i64 %escc2, -1
  %qmc2 = and i64 %qrawc2, %nescc2
  %qac2 = insertelement <2 x i64> zeroinitializer, i64 %qmc2, i32 0
  %px2c2 = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %qac2, <2 x i64> <i64 -1, i64 0>, i8 0)
  %pxc2 = extractelement <2 x i64> %px2c2, i32 0
  %openn = or i64 %topvc2, 0
  %pparn = or i64 %ppnc2, 0
  %m = xor i64 %pxc2, %carry
  %carryn = ashr i64 %m, 63
  %notm = xor i64 %m, -1
  %sm = and i64 %ssc2, %notm
  %cand = or i64 %sm, %qmc2
  %cp = getelementptr inbounds i64, ptr %cmask, i64 %b
  store i64 %cand, ptr %cp
  %mp = getelementptr inbounds i64, ptr %imask, i64 %b
  store i64 %m, ptr %mp
  br label %blk.end
blk.end:
  %bn = add i64 %b, 1
  %more = icmp ult i64 %bn, %nblocks
  br i1 %more, label %loop, label %exit
exit:
  ret void
}
