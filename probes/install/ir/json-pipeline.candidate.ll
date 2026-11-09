; The assembled JSON pipeline as emitted, in the fragment the parser reads: the
; caller @leanllvm_json_pipeline and nothing else.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-pipeline.sh
;
; from kernel/json/pipeline.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to the one `define` block.  The pipeline has no unit `-D` set: it
; reaches each unit through the external ABI its header declares.
; `-fno-discard-value-names` is a naming flag: it names values and labels the
; entry block, which the parser requires, and the capture checks that it changes
; no instruction by emitting the source with and without it and comparing the
; two texts with every register name replaced by one placeholder.
;
; Every parameter is the source's own name, so the capture renames none.  The
; six callees are reached through the ABI their headers declare:
;
;   @leanllvm_json_s1_masks     the mask unit, per block
;   @leanllvm_json_entry_pos8   the first entry emitter, per block
;   @leanllvm_json_entry_b8     the second entry emitter, per block
;   @leanllvm_json_escape_list  the escape-position list, per block, on the gate
;   @leanllvm_json_utf8         the document-level validity stage
;   @leanllvm_json_stage2       the entry stream's walk
;
; Their `declare` lines are kept, with their surface (`noundef`,
; `local_unnamed_addr`, `#N`) removed so the text is the syntax the parser
; reads; the declarations are what makes the fixture well-formed IR.  The
; `call` instructions stay, so the fixture's call targets are the census.  Nothing is rewritten: this unit has no table and no
; `poison` lane, and json-pipeline.rewrites.tsv is empty and says so.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-pipeline.strip.tsv.  The lines removed from the module carried:
;   source_filename = "kernel/json/pipeline.c"
;   target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
;   target triple = "x86_64-unknown-linux-gnu"
;   (the attribute groups and the module metadata nodes are recorded in
;   json-pipeline.strip.tsv, where they are removed; the six declarations are
;   kept and their removed surface is in that file's rows too)
;
; The fixture's own opcodes and call targets are in json-pipeline.inventory.
declare void @leanllvm_json_s1_masks(ptr, ptr, ptr)
declare i64 @leanllvm_json_entry_b8(ptr, i64, i64, ptr, i64)
declare i64 @leanllvm_json_entry_pos8(ptr, i64, i64, ptr, i64)
declare void @leanllvm_json_escape_list(i64, i64, i64, i64, ptr, ptr, ptr)
declare i64 @leanllvm_json_utf8(ptr, i64, i32)
declare i64 @leanllvm_json_stage2(ptr, i64, ptr, i64, ptr, i64, ptr, i64, ptr, ptr, i64, ptr, ptr)
define i64 @leanllvm_json_pipeline(ptr %b, i64 %n, ptr %sc, ptr %mk, ptr %entw, ptr %ep, i64 %epcap, ptr %nk, ptr %xp, i64 %xpcap, ptr %nxp, ptr %xcarry, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err, i64 %arm) {
entry:
  %add = add i64 %n, 63
  %shr = lshr i64 %add, 6
  %0 = load i64, ptr %nk
  %cmp79.not = icmp ult i64 %add, 64
  br i1 %cmp79.not, label %for.cond.cleanup, label %for.body.lr.ph
for.body.lr.ph:
  %delim = getelementptr inbounds i8, ptr %mk, i64 8
  %in_string = getelementptr inbounds i8, ptr %mk, i64 16
  %ws = getelementptr inbounds i8, ptr %mk, i64 24
  %and19 = and i64 %arm, 1
  %tobool.not = icmp eq i64 %and19, 0
  %and23 = and i64 %arm, 2
  %tobool24.not = icmp eq i64 %and23, 0
  %backslash = getelementptr inbounds i8, ptr %mk, i64 32
  %ctl = getelementptr inbounds i8, ptr %mk, i64 40
  br i1 %tobool.not, label %for.body.lr.ph.split.us, label %for.body.lr.ph.split
for.body.lr.ph.split.us:
  br i1 %tobool24.not, label %for.body.us.us, label %for.body.us
for.body.us.us:
  %prevS.082.us.us = phi i64 [ %shr13.us.us, %for.body.us.us ], [ 0, %for.body.lr.ph.split.us ]
  %k.081.us.us = phi i64 [ %call21.us.us, %for.body.us.us ], [ %0, %for.body.lr.ph.split.us ]
  %i.080.us.us = phi i64 [ %inc.us.us, %for.body.us.us ], [ 0, %for.body.lr.ph.split.us ]
  %shl.us.us = shl i64 %i.080.us.us, 6
  %add.ptr.us.us = getelementptr inbounds i8, ptr %b, i64 %shl.us.us
  tail call void @leanllvm_json_s1_masks(ptr %add.ptr.us.us, ptr %sc, ptr %mk)
  %1 = load i64, ptr %mk
  %2 = load i64, ptr %delim
  %3 = load i64, ptr %in_string
  %4 = load i64, ptr %ws
  %5 = or i64 %1, %4
  %6 = or i64 %5, %2
  %or2.us.us = or i64 %6, %3
  %not.us.us = xor i64 %or2.us.us, -1
  %not6.us.us = xor i64 %3, -1
  %and.us.us = and i64 %2, %not6.us.us
  %shl8.us.us = shl i64 %not.us.us, 1
  %or9.us.us = or i64 %shl8.us.us, %prevS.082.us.us
  %not10.us.us = xor i64 %or9.us.us, -1
  %and11.us.us = and i64 %not10.us.us, %not.us.us
  %7 = or i64 %and.us.us, %and11.us.us
  %or12.us.us = or i64 %7, %1
  %shr13.us.us = lshr i64 %not.us.us, 63
  %sub.us.us = sub i64 %n, %shl.us.us
  %cmp15.us.us = icmp ult i64 %sub.us.us, 64
  %notmask.us.us = shl i64 -1, %sub.us.us
  %sub17.us.us = xor i64 %notmask.us.us, -1
  %and18.us.us = select i1 %cmp15.us.us, i64 %sub17.us.us, i64 -1
  %ent.0.us.us = and i64 %or12.us.us, %and18.us.us
  store i64 %ent.0.us.us, ptr %entw
  %call21.us.us = tail call i64 @leanllvm_json_entry_pos8(ptr %entw, i64 %i.080.us.us, i64 1, ptr %ep, i64 %k.081.us.us)
  %inc.us.us = add i64 %i.080.us.us, 1
  %exitcond116.not = icmp eq i64 %inc.us.us, %shr
  br i1 %exitcond116.not, label %for.cond.cleanup, label %for.body.us.us
for.body.us:
  %prevS.082.us = phi i64 [ %shr13.us, %for.body.us ], [ 0, %for.body.lr.ph.split.us ]
  %k.081.us = phi i64 [ %call21.us, %for.body.us ], [ %0, %for.body.lr.ph.split.us ]
  %i.080.us = phi i64 [ %inc.us, %for.body.us ], [ 0, %for.body.lr.ph.split.us ]
  %shl.us = shl i64 %i.080.us, 6
  %add.ptr.us = getelementptr inbounds i8, ptr %b, i64 %shl.us
  tail call void @leanllvm_json_s1_masks(ptr %add.ptr.us, ptr %sc, ptr %mk)
  %8 = load i64, ptr %mk
  %9 = load i64, ptr %delim
  %10 = load i64, ptr %in_string
  %11 = load i64, ptr %ws
  %12 = or i64 %8, %11
  %13 = or i64 %12, %9
  %or2.us = or i64 %13, %10
  %not.us = xor i64 %or2.us, -1
  %not6.us = xor i64 %10, -1
  %and.us = and i64 %9, %not6.us
  %shl8.us = shl i64 %not.us, 1
  %or9.us = or i64 %shl8.us, %prevS.082.us
  %not10.us = xor i64 %or9.us, -1
  %and11.us = and i64 %not10.us, %not.us
  %14 = or i64 %and.us, %and11.us
  %or12.us = or i64 %14, %8
  %shr13.us = lshr i64 %not.us, 63
  %sub.us = sub i64 %n, %shl.us
  %cmp15.us = icmp ult i64 %sub.us, 64
  %notmask.us = shl i64 -1, %sub.us
  %sub17.us = xor i64 %notmask.us, -1
  %and18.us = select i1 %cmp15.us, i64 %sub17.us, i64 -1
  %ent.0.us = and i64 %or12.us, %and18.us
  store i64 %ent.0.us, ptr %entw
  %call21.us = tail call i64 @leanllvm_json_entry_pos8(ptr %entw, i64 %i.080.us, i64 1, ptr %ep, i64 %k.081.us)
  %15 = load i64, ptr %backslash
  %16 = load i64, ptr %ctl
  %17 = load i64, ptr %in_string
  tail call void @leanllvm_json_escape_list(i64 %15, i64 %16, i64 %17, i64 %i.080.us, ptr %xp, ptr %nxp, ptr %xcarry)
  %inc.us = add i64 %i.080.us, 1
  %exitcond115.not = icmp eq i64 %inc.us, %shr
  br i1 %exitcond115.not, label %for.cond.cleanup, label %for.body.us
for.body.lr.ph.split:
  br i1 %tobool24.not, label %for.body.us83, label %for.body
for.body.us83:
  %prevS.082.us84 = phi i64 [ %shr13.us98, %for.body.us83 ], [ 0, %for.body.lr.ph.split ]
  %k.081.us85 = phi i64 [ %call.us, %for.body.us83 ], [ %0, %for.body.lr.ph.split ]
  %i.080.us86 = phi i64 [ %inc.us106, %for.body.us83 ], [ 0, %for.body.lr.ph.split ]
  %shl.us87 = shl i64 %i.080.us86, 6
  %add.ptr.us88 = getelementptr inbounds i8, ptr %b, i64 %shl.us87
  tail call void @leanllvm_json_s1_masks(ptr %add.ptr.us88, ptr %sc, ptr %mk)
  %18 = load i64, ptr %mk
  %19 = load i64, ptr %delim
  %20 = load i64, ptr %in_string
  %21 = load i64, ptr %ws
  %22 = or i64 %18, %21
  %23 = or i64 %22, %19
  %or2.us89 = or i64 %23, %20
  %not.us90 = xor i64 %or2.us89, -1
  %not6.us91 = xor i64 %20, -1
  %and.us92 = and i64 %19, %not6.us91
  %shl8.us93 = shl i64 %not.us90, 1
  %or9.us94 = or i64 %shl8.us93, %prevS.082.us84
  %not10.us95 = xor i64 %or9.us94, -1
  %and11.us96 = and i64 %not10.us95, %not.us90
  %24 = or i64 %and.us92, %and11.us96
  %or12.us97 = or i64 %24, %18
  %shr13.us98 = lshr i64 %not.us90, 63
  %sub.us99 = sub i64 %n, %shl.us87
  %cmp15.us100 = icmp ult i64 %sub.us99, 64
  %notmask.us101 = shl i64 -1, %sub.us99
  %sub17.us102 = xor i64 %notmask.us101, -1
  %and18.us103 = select i1 %cmp15.us100, i64 %sub17.us102, i64 -1
  %ent.0.us104 = and i64 %or12.us97, %and18.us103
  store i64 %ent.0.us104, ptr %entw
  %call.us = tail call i64 @leanllvm_json_entry_b8(ptr %entw, i64 %i.080.us86, i64 1, ptr %ep, i64 %k.081.us85)
  %inc.us106 = add i64 %i.080.us86, 1
  %exitcond114.not = icmp eq i64 %inc.us106, %shr
  br i1 %exitcond114.not, label %for.cond.cleanup, label %for.body.us83
for.cond.cleanup:
  %k.0.lcssa = phi i64 [ %0, %entry ], [ %call21.us.us, %for.body.us.us ], [ %call21.us, %for.body.us ], [ %call.us, %for.body.us83 ], [ %call, %for.body ]
  store i64 %k.0.lcssa, ptr %nk
  %25 = trunc i64 %arm to i32
  %26 = lshr i32 %25, 2
  %conv = and i32 %26, 1
  %call30 = tail call i64 @leanllvm_json_utf8(ptr %b, i64 %n, i32 %conv)
  %cmp31.not = icmp eq i64 %call30, 0
  br i1 %cmp31.not, label %if.end34, label %if.then33
for.body:
  %prevS.082 = phi i64 [ %shr13, %for.body ], [ 0, %for.body.lr.ph.split ]
  %k.081 = phi i64 [ %call, %for.body ], [ %0, %for.body.lr.ph.split ]
  %i.080 = phi i64 [ %inc, %for.body ], [ 0, %for.body.lr.ph.split ]
  %shl = shl i64 %i.080, 6
  %add.ptr = getelementptr inbounds i8, ptr %b, i64 %shl
  tail call void @leanllvm_json_s1_masks(ptr %add.ptr, ptr %sc, ptr %mk)
  %27 = load i64, ptr %mk
  %28 = load i64, ptr %delim
  %29 = load i64, ptr %in_string
  %30 = load i64, ptr %ws
  %31 = or i64 %27, %30
  %32 = or i64 %31, %28
  %or2 = or i64 %32, %29
  %not = xor i64 %or2, -1
  %not6 = xor i64 %29, -1
  %and = and i64 %28, %not6
  %shl8 = shl i64 %not, 1
  %or9 = or i64 %shl8, %prevS.082
  %not10 = xor i64 %or9, -1
  %and11 = and i64 %not10, %not
  %33 = or i64 %and, %and11
  %or12 = or i64 %33, %27
  %shr13 = lshr i64 %not, 63
  %sub = sub i64 %n, %shl
  %cmp15 = icmp ult i64 %sub, 64
  %notmask = shl i64 -1, %sub
  %sub17 = xor i64 %notmask, -1
  %and18 = select i1 %cmp15, i64 %sub17, i64 -1
  %ent.0 = and i64 %or12, %and18
  store i64 %ent.0, ptr %entw
  %call = tail call i64 @leanllvm_json_entry_b8(ptr %entw, i64 %i.080, i64 1, ptr %ep, i64 %k.081)
  %34 = load i64, ptr %backslash
  %35 = load i64, ptr %ctl
  %36 = load i64, ptr %in_string
  tail call void @leanllvm_json_escape_list(i64 %34, i64 %35, i64 %36, i64 %i.080, ptr %xp, ptr %nxp, ptr %xcarry)
  %inc = add i64 %i.080, 1
  %exitcond.not = icmp eq i64 %inc, %shr
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body
if.then33:
  store i64 %n, ptr %err
  br label %cleanup
if.end34:
  %37 = load i64, ptr %nxp
  %call35 = tail call i64 @leanllvm_json_stage2(ptr %b, i64 %n, ptr %ep, i64 %k.0.lcssa, ptr %xp, i64 %37, ptr %dst, i64 %dstcap, ptr %ndst, ptr %ev, i64 %evcap, ptr %nev, ptr %err)
  br label %cleanup
cleanup:
  %retval.0 = phi i64 [ 0, %if.then33 ], [ %call35, %if.end34 ]
  ret i64 %retval.0
}
