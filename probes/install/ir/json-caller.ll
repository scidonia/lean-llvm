; The JSON seam's staging caller: four i64 words are staged into four locals
; from address 1, then the seam is called on the first local's address, and the
; i32 it returns is the caller's result.
;
; Emitted from LeanLLVM.Vellum.JsonSeam.scanCaller with
;
;   nix develop -c bash probes/install/lake-locked.sh exe leanllvm-json-emit > probes/install/ir/json-caller.ll
;
; through LeanLLVM.Module.render, the framework's own printer.  The module holds
; the seam's declaration and the caller's definition, because the fixture is
; checked with `opt -passes=verify` and LLVM refuses a call to an undeclared
; symbol.  LeanLLVM/Vellum/JsonSeam.lean parses this file back and pins the
; whole module, declaration included, with `#guard`.
;
; This is not the output of Lean's native compiler: no `lean -c` C emission and
; no clang lowering is involved.  Nothing in the text below was removed or
; rewritten after rendering.
declare i32 @leanllvm_json_classify32(ptr)

define i32 @leanllvm_json_scan_caller(i64 %w0, i64 %w1, i64 %w2, i64 %w3) {
entry:
  %b0 = alloca i64, align 8
  %b1 = alloca i64, align 8
  %b2 = alloca i64, align 8
  %b3 = alloca i64, align 8
  store i64 %w0, ptr %b0
  store i64 %w1, ptr %b1
  store i64 %w2, ptr %b2
  store i64 %w3, ptr %b3
  %m = call i32 @leanllvm_json_classify32(ptr %b0)
  ret i32 %m
}
