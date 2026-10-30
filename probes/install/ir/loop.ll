; The comma mask as a memory-backed loop: counter and accumulator live in
; memory, the lane bit and test are computed from the counter, and the select
; folds the accumulator.  The loop is the control-flow-different counterpart of
; the unrolled candidate in candidate.ll.
;
; Emitted from LeanLLVM.Vellum.CommaMaskLoop.loopFunction -- the AST in
; LeanLLVM/Vellum/CommaMaskLoopBody.lean that
; LeanLLVM/Vellum/CommaMaskLoop.lean parses this file back to and proves its
; correctness and framed-memory statements about -- with
;
;   nix develop -c bash -c 'lake exe leanllvm-loop-emit > probes/install/ir/loop.ll'
;
; through LeanLLVM.Function.render, the framework's own printer.
; probes/install/ir/capture.sh runs the same command as part of the fixture
; route, with the redirect inside the shell so the dev shell's startup banner
; is not written here.
;
; This is not the output of Lean's native compiler: no `lean -c` C emission and
; no clang lowering is involved.  Nothing in the text below was removed or
; rewritten after rendering.
define i64 @leanllvm_comma_mask8(i64 %arg) {
entry:
  %m = xor i64 %arg, 3182967604875373612
  %acc = alloca i64, align 8
  %i = alloca i64, align 8
  store i64 0, ptr %acc
  store i64 0, ptr %i
  br label %cond

cond:
  %i1 = load i64, ptr %i
  %c = icmp ult i64 %i1, 8
  br i1 %c, label %body, label %done

body:
  %sh = mul i64 %i1, 8
  %b = lshr i64 %m, %sh
  %b2 = and i64 %b, 255
  %z = icmp eq i64 %b2, 0
  %a0 = load i64, ptr %acc
  %bit = shl i64 128, %sh
  %a1 = or i64 %a0, %bit
  %a2 = select i1 %z, i64 %a1, i64 %a0
  store i64 %a2, ptr %acc
  %i2 = add i64 %i1, 1
  store i64 %i2, ptr %i
  br label %cond

done:
  %r = load i64, ptr %acc
  ret i64 %r
}
