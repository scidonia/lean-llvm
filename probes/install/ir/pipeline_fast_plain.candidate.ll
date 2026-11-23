; The split-stage-1 plain pipeline's body, as emitted: the static
; `@pf_plain_pipeline` the two exported entries call, at the certified
; pipeline's own 20-argument ABI.  Regenerate from the repository root with:
;
;   nix develop -c clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul \
;     -std=gnu11 -falign-loops=64 -falign-functions=64 \
;     -fno-discard-value-names -I kernel/json \
;     kernel/json/pipeline_fast_plain.c -o /tmp/pfp.ll
;
; and take the `@pf_plain_pipeline` `define` block plus the five unit
; `declare`s.  The exported `_pos8`/`_b8` entries are the caller of this body:
; they stage the two stage-1 slots (24 and 48 zero bytes) and pass `arm = 0`/`1`,
; and their 16-argument ABI is unchanged.
;
; The body stages exactly what `pipeline.c` stages: `%sc` (24 B), `%mk` (48 B),
; the `%entw` array, the entry stream, the cursors and `%arm`.  It has no
; `alloca`, no `memset` and no lifetime call.  Its difference from
; `pipeline.c` is only the stage-1 shape: a mask loop that collects one word per
; block into `%entw`, then one `@leanllvm_json_entry_pos8`/`_b8` call over the
; array, then the same ungated `@leanllvm_json_utf8` and the same list-free
; `@leanllvm_json_stage2`.  `arm & 1` selects the emitter; `arm & 2` (the escape
; list) is unused, so `xp`/`nxp` pass through unchanged.
;
; The one staging difference the route must carry: `%entw` is the
; `(n+63)>>6`-word array, not `pipeline.c`'s one-word scratch.  The route's
; `(entw, 8)` must widen to `8 * pipelineBlocks n` in the pre's staged bytes,
; the post's `UnchangedOutside`, and `pipelineRegions`.
;
; Normalisation (recorded): keep the one `define` block and the five unit
; `declare`s; drop the module header, attribute groups, metadata, intrinsic
; declares and comments; remove `nonnull`, `noundef`, `captures(none)`,
; `range(i64 0, 2)`, `#N`, `local_unnamed_addr`/`unnamed_addr`,
; `align N`, `dereferenceable(N)`, `writeonly`, and the trailing
; `!tbaa`/`!llvm.loop` operands; drop `tail ` and `fastcc `/`internal `.
; `inbounds`/`nuw`/`nsw` are left in place: the parser accepts and drops them.
define i64 @pf_plain_pipeline(ptr %b, i64 %n, ptr %sc, ptr %mk, ptr %ent, ptr %ep, i64 %epcap, ptr %nk, ptr %xp, i64 %xpcap, ptr %nxp, ptr %xcarry, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err, i64 %arm) {
entry:
  %add = add i64 %n, 63
  %shr = lshr i64 %add, 6
  %cmp61.not = icmp ult i64 %add, 64
  br i1 %cmp61.not, label %for.cond.cleanup, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  %delim = getelementptr i8, ptr %mk, i64 8
  %in_string = getelementptr i8, ptr %mk, i64 16
  %ws = getelementptr i8, ptr %mk, i64 24
  br label %for.body

for.cond.cleanup:                                 ; preds = %for.body, %entry
  %and19 = and i64 %arm, 1
  %tobool.not = icmp eq i64 %and19, 0
  %0 = load i64, ptr %nk
  br i1 %tobool.not, label %cond.false, label %cond.true

for.body:                                         ; preds = %for.body.lr.ph, %for.body
  %prevS.063 = phi i64 [ 0, %for.body.lr.ph ], [ %shr13, %for.body ]
  %i.062 = phi i64 [ 0, %for.body.lr.ph ], [ %inc, %for.body ]
  %shl = shl i64 %i.062, 6
  %add.ptr = getelementptr i8, ptr %b, i64 %shl
  call void @leanllvm_json_s1_masks(ptr %add.ptr, ptr %sc, ptr %mk)
  %1 = load i64, ptr %mk
  %2 = load i64, ptr %delim
  %3 = load i64, ptr %in_string
  %4 = load i64, ptr %ws
  %5 = or i64 %1, %4
  %6 = or i64 %5, %2
  %or2 = or i64 %6, %3
  %not = xor i64 %or2, -1
  %not6 = xor i64 %3, -1
  %and = and i64 %2, %not6
  %shl8 = shl i64 %not, 1
  %or9 = or i64 %shl8, %prevS.063
  %not10 = xor i64 %or9, -1
  %and11 = and i64 %not10, %not
  %7 = or i64 %and, %and11
  %or12 = or i64 %7, %1
  %shr13 = lshr i64 %not, 63
  %sub = sub i64 %n, %shl
  %cmp15 = icmp ult i64 %sub, 64
  %notmask = shl i64 -1, %sub
  %sub17 = xor i64 %notmask, -1
  %and18 = select i1 %cmp15, i64 %sub17, i64 -1
  %e.0 = and i64 %or12, %and18
  %arrayidx = getelementptr i64, ptr %ent, i64 %i.062
  store i64 %e.0, ptr %arrayidx
  %inc = add i64 %i.062, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body

cond.true:                                        ; preds = %for.cond.cleanup
  %call = call i64 @leanllvm_json_entry_b8(ptr %ent, i64 0, i64 %shr, ptr %ep, i64 %0)
  br label %cond.end

cond.false:                                       ; preds = %for.cond.cleanup
  %call20 = call i64 @leanllvm_json_entry_pos8(ptr %ent, i64 0, i64 %shr, ptr %ep, i64 %0)
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %call, %cond.true ], [ %call20, %cond.false ]
  store i64 %cond, ptr %nk
  %call21 = call i64 @leanllvm_json_utf8(ptr %b, i64 %n, i32 0)
  %cmp22.not = icmp eq i64 %call21, 0
  br i1 %cmp22.not, label %if.end24, label %if.then23

if.then23:                                        ; preds = %cond.end
  store i64 %n, ptr %err
  br label %cleanup

if.end24:                                         ; preds = %cond.end
  %8 = load i64, ptr %nxp
  %call25 = call i64 @leanllvm_json_stage2(ptr %b, i64 %n, ptr %ep, i64 %cond, ptr %xp, i64 %8, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err)
  br label %cleanup

cleanup:                                          ; preds = %if.end24, %if.then23
  %retval.0 = phi i64 [ 0, %if.then23 ], [ %call25, %if.end24 ]
  ret i64 %retval.0
}

; The five callees, in the ABI their headers declare.
declare void @leanllvm_json_s1_masks(ptr, ptr, ptr)
declare i64 @leanllvm_json_entry_b8(ptr, i64, i64, ptr, i64)
declare i64 @leanllvm_json_entry_pos8(ptr, i64, i64, ptr, i64)
declare i64 @leanllvm_json_utf8(ptr, i64, i32)
declare i64 @leanllvm_json_stage2(ptr, i64, ptr, i64, ptr, i64, ptr, i64, ptr, ptr, i64, ptr, ptr)
