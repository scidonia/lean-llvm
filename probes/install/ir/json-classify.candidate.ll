; The JSON block classifier as emitted, in the fragment `LeanLLVM.Semantics`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-json.sh
;
; from probes/install/json/classify.candidate.c, emitted with
;
;   clang -S -emit-llvm -O2 -mavx2 probes/install/json/classify.candidate.c
;
; and passed through
;
;   opt -passes=instnamer
;
; then the verbatim `define` block of @leanllvm_json_classify32, with the
; textual syntax listed in capture-json.sh removed.  `instnamer` labels the
; entry block (the parser requires a label on every block) and names values;
; it changes no instruction.  The optimiser form is clang 21.1.8 at -O2 -mavx2
; for x86_64-unknown-linux-gnu with +avx2: instcombine folded the two
; comparisons for the tab and newline bytes into a range test, which is why
; the body contains `add <32 x i8>` and `icmp ult <32 x i8>` and why the
; splat constant is negative.  At -O0 the same source emits an `icmp eq` for
; each of the twelve bytes and neither of those two instructions.
;
; Removed before the parser sees the text, each because it does not change the
; value computed: `noundef`; `readonly`; `captures(none)`;
; `local_unnamed_addr`; `#0` and the `attributes #0 = { ... }` group
; (including `memory(argmem: read)` and the target-feature list);
; `, align 1`; `, !tbaa !6`; every `!llvm.*` and `!N = ...` line;
; `target datalayout`; `target triple`; `source_filename`.  The module
; configuration those lines carried is: x86_64-unknown-linux-gnu, little
; endian, 64-bit pointers, +avx2.
;
; The load's `align 1` is dropped because the parser's `load` has no
; alignment field.  Under LLVM's own reading an unadorned load assumes ABI
; alignment (`llvm-as` then `llvm-dis` renders this one `align 32`), which
; is stricter than the `align 1` clang emitted for the unaligned source
; load; this text is parsed by LeanLLVM's parser rather than compiled as LLVM
; IR, and the theorem claims nothing about a stricter alignment.
;
; Measured inventory of the block below (counted on this text):
;   opcodes:  load 1, icmp 11 (10 eq, 1 ult),
;             or 10, add 1, bitcast 1, ret 1
;   vector types: <32 x i8> 13, <32 x i1> 11
;   scalar types: i8 12 (in splat constants), i32 3 (header return
;                 type, bitcast target, ret), ptr 2 (parameter, load
;                 address)
;   vector constants: splat (i8 N) 12
;
; The body reads 32 bytes and writes none; it calls nothing, allocates
; nothing and contains no `getelementptr`, shuffle, select or `phi`.
define i32 @leanllvm_json_classify32(ptr %arg) {
bb:
  %i = load <32 x i8>, ptr %arg
  %i1 = icmp eq <32 x i8> %i, splat (i8 34)
  %i2 = icmp eq <32 x i8> %i, splat (i8 92)
  %i3 = or <32 x i1> %i1, %i2
  %i4 = icmp eq <32 x i8> %i, splat (i8 58)
  %i5 = or <32 x i1> %i4, %i3
  %i6 = icmp eq <32 x i8> %i, splat (i8 44)
  %i7 = or <32 x i1> %i6, %i5
  %i8 = icmp eq <32 x i8> %i, splat (i8 123)
  %i9 = or <32 x i1> %i8, %i7
  %i10 = icmp eq <32 x i8> %i, splat (i8 125)
  %i11 = or <32 x i1> %i10, %i9
  %i12 = icmp eq <32 x i8> %i, splat (i8 91)
  %i13 = or <32 x i1> %i12, %i11
  %i14 = icmp eq <32 x i8> %i, splat (i8 93)
  %i15 = or <32 x i1> %i14, %i13
  %i16 = icmp eq <32 x i8> %i, splat (i8 32)
  %i17 = or <32 x i1> %i16, %i15
  %i18 = add <32 x i8> %i, splat (i8 -9)
  %i19 = icmp ult <32 x i8> %i18, splat (i8 2)
  %i20 = or <32 x i1> %i19, %i17
  %i21 = icmp eq <32 x i8> %i, splat (i8 13)
  %i22 = or <32 x i1> %i21, %i20
  %i23 = bitcast <32 x i1> %i22 to i32
  ret i32 %i23
}
