; The stage-2 helper `s2_init`, as emitted, in the fragment `LeanLLVM.Semantics`
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
; symbol's address from.  The body is captured and the fragment expresses it.
;
define void @s2_init(ptr %s, ptr %b, i64 %n, i64 %nb, ptr %ep) {
entry:
  store ptr %b, ptr %s
  %n2 = getelementptr inbounds i8, ptr %s, i64 8
  store i64 %n, ptr %n2
  %nb3 = getelementptr inbounds i8, ptr %s, i64 16
  store i64 %nb, ptr %nb3
  %ix4 = getelementptr inbounds i8, ptr %s, i64 24
  %ep7 = getelementptr inbounds i8, ptr %s, i64 48
  tail call void @llvm.memset.p0.i64(ptr %ix4, i8 0, i64 24, i1 false)
  store ptr %ep, ptr %ep7
  %nsp = getelementptr inbounds i8, ptr %s, i64 56
  tail call void @llvm.memset.p0.i64(ptr %nsp, i8 0, i64 64, i1 false)
  ret void
}
