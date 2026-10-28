; The candidate seam as emitted, in the fragment `LeanLLVM.Semantics` models.
;
;   clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone candidate_lanes.c
;   opt -passes='function(mem2reg,simplifycfg),instnamer'
;
; candidate_lanes.c is probes/install/Candidate.lean's eight-lane fold with
; the boxed-`Nat` counter written out lane by lane; the emission of the boxed
; loop itself (candidate.raw.ll) is outside the modelled fragment.  Same
; textual stripping as baseline.ll; `simplifycfg` folded each lane's diamond
; back into the `select` the source wrote.
; LeanLLVM/Vellum/CommaMaskIR.lean proves this body returns `byteLoop x` for
; every `x`, by rewriting it to the fold in `CommaMask.byteLoop` (no
; bit-blasting).
define i64 @leanllvm_comma_mask8(i64 %arg) {
bb:
  %i = xor i64 %arg, 3182967604875373612
  %i1 = lshr i64 %i, 0
  %i2 = and i64 %i1, 255
  %i3 = icmp eq i64 %i2, 0
  %i4 = or i64 0, 128
  %i5 = select i1 %i3, i64 %i4, i64 0
  %i6 = lshr i64 %i, 8
  %i7 = and i64 %i6, 255
  %i8 = icmp eq i64 %i7, 0
  %i9 = or i64 %i5, 32768
  %i10 = select i1 %i8, i64 %i9, i64 %i5
  %i11 = lshr i64 %i, 16
  %i12 = and i64 %i11, 255
  %i13 = icmp eq i64 %i12, 0
  %i14 = or i64 %i10, 8388608
  %i15 = select i1 %i13, i64 %i14, i64 %i10
  %i16 = lshr i64 %i, 24
  %i17 = and i64 %i16, 255
  %i18 = icmp eq i64 %i17, 0
  %i19 = or i64 %i15, 2147483648
  %i20 = select i1 %i18, i64 %i19, i64 %i15
  %i21 = lshr i64 %i, 32
  %i22 = and i64 %i21, 255
  %i23 = icmp eq i64 %i22, 0
  %i24 = or i64 %i20, 549755813888
  %i25 = select i1 %i23, i64 %i24, i64 %i20
  %i26 = lshr i64 %i, 40
  %i27 = and i64 %i26, 255
  %i28 = icmp eq i64 %i27, 0
  %i29 = or i64 %i25, 140737488355328
  %i30 = select i1 %i28, i64 %i29, i64 %i25
  %i31 = lshr i64 %i, 48
  %i32 = and i64 %i31, 255
  %i33 = icmp eq i64 %i32, 0
  %i34 = or i64 %i30, 36028797018963968
  %i35 = select i1 %i33, i64 %i34, i64 %i30
  %i36 = lshr i64 %i, 56
  %i37 = and i64 %i36, 255
  %i38 = icmp eq i64 %i37, 0
  %i39 = or i64 %i35, -9223372036854775808
  %i40 = select i1 %i38, i64 %i39, i64 %i35
  ret i64 %i40
}
