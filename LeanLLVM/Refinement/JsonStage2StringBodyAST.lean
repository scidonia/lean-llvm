import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonStage2HelperIRBodies

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The body, as the fixture parses

**The pinned body is the emitted two-arm body.**  `stage2.helper.s2_string_body.ll`
is `s2_string_body`'s text as `capture-stage2-helpers.sh` writes it from
`kernel/json/stage2.c`: `entry` tests `nxp` and the two arms follow.  With a
stage-1 list the scan walks the position list and the escaped form calls
`leanllvm_json_escape_expand`; with no list (`nxp = 0`) the body scans its own
span (`z_scan`), refuses a control byte at its own offset, copies the clean
prefix exactly once the decode has accepted (`llvm.memcpy`), and decodes the
suffix with `leanllvm_json_escape_decode`.

Two properties of the emission are what make the body's own run match the staged
model, and both are the source's, not the fixture's:

- **one slot.**  The body allocates exactly one eight-byte slot, written only on
  a path that is about to call a decoder, so the contract's `(next, 8)` region is
  the body's whole allocation and the plain and control arms write nothing there.
  `z_scan` therefore writes no state: the caller distinguishes a backslash from a
  control byte by reading `p[off]`.
- **an exact prefix.**  The prefix copy writes `off` bytes, not a rounded block,
  and only after the decode accepted, so the refusing arm writes nothing at `dst`.

The literal below is the parser's own result written out: `capture-stage2-helpers.sh
--emit-pins s2_string_body` prints it, and the `#guard` beneath it asserts that
parsing the fixture returns exactly this.  The pin is a `#guard` rather than an
`rfl` proposition because the parser runs on `String` primitives, which the kernel
does not reduce.  The control beside it is `s2StringBodySrcMutated`: the same text
with the error record's offset changed, which still parses and is not the pinned
body. -/

/-- `@s2_string_body`, as `probes/install/ir/stage2.helper.s2_string_body.ll`
parses: `entry` tests `nxp` and the two arms follow. -/
def s2StringBodyBody : Function :=
{ name := "s2_string_body",
  retTy := Ty.int 32,
  params := [("%c", Ty.ptr),
             ("%p", Ty.ptr),
             ("%len", Ty.int 64),
             ("%dst", Ty.ptr),
             ("%outn", Ty.ptr),
             ("%xp", Ty.ptr),
             ("%xj", Ty.ptr),
             ("%nxp", Ty.int 64)],
  blocks := [{ name := "entry",
               instrs := [Instr.alloca "%ei" (Ty.int 64) 0,
                          Instr.load "%0" (Ty.ptr) (Operand.reg "%c"),
                          Instr.ptrtoint "%sub.ptr.lhs.cast" (Operand.reg "%p"),
                          Instr.ptrtoint "%sub.ptr.rhs.cast" (Operand.reg "%0"),
                          Instr.binop
                            "%sub.ptr.sub"
                            (BinOp.sub)
                            64
                            (Operand.reg "%sub.ptr.lhs.cast")
                            (Operand.reg "%sub.ptr.rhs.cast"),
                          Instr.callVoid
                            "llvm.lifetime.start.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")],
                          Instr.icmp
                            "%tobool.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%nxp")
                            (Operand.imm (Const.int 64 0x0000000000000000#64))],
               term := Term.condbr (Operand.reg "%tobool.not") "if.end16"
                 "while.cond.preheader" },
             { name := "while.cond.preheader",
               instrs := [Instr.load "%xj.promoted" (Ty.int 64) (Operand.reg "%xj"),
                          Instr.icmp
                            "%cmp3"
                            (IPred.ult)
                            64
                            (Operand.reg "%xj.promoted")
                            (Operand.reg "%nxp")],
               term := Term.condbr (Operand.reg "%cmp3") "land.rhs" "if.then9" },
             { name := "land.rhs",
               instrs := [Instr.phi
                            "%inc24"
                            (Ty.int 64)
                            [("while.body", Operand.reg "%inc"),
                             ("while.cond.preheader", Operand.reg "%xj.promoted")],
                          Instr.gep
                            "%arrayidx"
                            (Ty.int 32)
                            (Operand.reg "%xp")
                            (Operand.reg "%inc24"),
                          Instr.load "%1" (Ty.int 32) (Operand.reg "%arrayidx"),
                          Instr.zext "%conv" 32 64 (Operand.reg "%1"),
                          Instr.icmp
                            "%cmp1"
                            (IPred.ugt)
                            64
                            (Operand.reg "%sub.ptr.sub")
                            (Operand.reg "%conv")],
               term := Term.condbr (Operand.reg "%cmp1") "while.body" "land.lhs.true" },
             { name := "while.body",
               instrs := [Instr.binop
                            "%inc"
                            (BinOp.add)
                            64
                            (Operand.reg "%inc24")
                            (Operand.imm (Const.int 64 0x0000000000000001#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%inc")
                            (Operand.reg "%xj"),
                          Instr.icmp
                            "%exitcond.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%inc")
                            (Operand.reg "%nxp")],
               term := Term.condbr (Operand.reg "%exitcond.not") "if.then9" "land.rhs" },
             { name := "land.lhs.true",
               instrs := [Instr.binop
                            "%add"
                            (BinOp.add)
                            64
                            (Operand.reg "%sub.ptr.sub")
                            (Operand.reg "%len"),
                          Instr.icmp
                            "%cmp7"
                            (IPred.ugt)
                            64
                            (Operand.reg "%add")
                            (Operand.reg "%conv")],
               term := Term.condbr (Operand.reg "%cmp7") "if.end" "if.then9" },
             { name := "if.then9",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%len")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup47" },
             { name := "if.end",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.imm (Const.int 64 0x0000000000000000#64))
                            (Operand.reg "%ei"),
                          Instr.call
                            "%call"
                            (Ty.int 64)
                            "leanllvm_json_escape_expand"
                            [(Ty.ptr, Operand.reg "%p"),
                             (Ty.int 64, Operand.reg "%len"),
                             (Ty.ptr, Operand.reg "%dst"),
                             (Ty.ptr, Operand.reg "%ei"),
                             (Ty.ptr, Operand.reg "%xp"),
                             (Ty.ptr, Operand.reg "%xj"),
                             (Ty.int 64, Operand.reg "%nxp"),
                             (Ty.int 64, Operand.reg "%sub.ptr.sub")],
                          Instr.icmp
                            "%cmp10"
                            (IPred.eq)
                            64
                            (Operand.reg "%call")
                            (Operand.imm (Const.int 64 0xffffffffffffffff#64))],
               term := Term.condbr (Operand.reg "%cmp10") "if.then12" "if.end15" },
             { name := "if.then12",
               instrs := [Instr.load "%2" (Ty.int 64) (Operand.reg "%ei"),
                          Instr.binop
                            "%add13"
                            (BinOp.add)
                            64
                            (Operand.reg "%2")
                            (Operand.reg "%sub.ptr.sub"),
                          Instr.gep
                            "%3"
                            (Ty.int 8)
                            (Operand.reg "%c")
                            (Operand.imm (Const.int 64 0x0000000000000458#64)),
                          Instr.load "%c.val95" (Ty.ptr) (Operand.reg "%3"),
                          Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000000#32))
                            (Operand.reg "%c.val95"),
                          Instr.gep
                            "%off1.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val95")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add13")
                            (Operand.reg "%off1.i.i"),
                          Instr.gep
                            "%msg2.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val95")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.ptr)
                            (Operand.imm (Const.null))
                            (Operand.reg "%msg2.i.i")],
               term := Term.br "cleanup47" },
             { name := "if.end15",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%call")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup47" },
             { name := "if.end16",
               instrs := [Instr.call
                            "%call17"
                            (Ty.int 64)
                            "z_scan"
                            [(Ty.ptr, Operand.reg "%p"),
                             (Ty.int 64, Operand.reg "%len")],
                          Instr.icmp
                            "%cmp18"
                            (IPred.eq)
                            64
                            (Operand.reg "%call17")
                            (Operand.imm (Const.int 64 0xffffffffffffffff#64))],
               term := Term.condbr (Operand.reg "%cmp18") "if.then20" "if.end21" },
             { name := "if.then20",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%len")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup47" },
             { name := "if.end21",
               instrs := [Instr.gep
                            "%arrayidx22"
                            (Ty.int 8)
                            (Operand.reg "%p")
                            (Operand.reg "%call17"),
                          Instr.load "%4" (Ty.int 8) (Operand.reg "%arrayidx22"),
                          Instr.icmp
                            "%cmp24.not"
                            (IPred.eq)
                            8
                            (Operand.reg "%4")
                            (Operand.imm (Const.int 8 0x5c#8))],
               term := Term.condbr (Operand.reg "%cmp24.not") "if.end29" "if.then26" },
             { name := "if.then26",
               instrs := [Instr.binop
                            "%add27"
                            (BinOp.add)
                            64
                            (Operand.reg "%call17")
                            (Operand.reg "%sub.ptr.sub"),
                          Instr.gep
                            "%5"
                            (Ty.int 8)
                            (Operand.reg "%c")
                            (Operand.imm (Const.int 64 0x0000000000000458#64)),
                          Instr.load "%c.val94" (Ty.ptr) (Operand.reg "%5"),
                          Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000000#32))
                            (Operand.reg "%c.val94"),
                          Instr.gep
                            "%off1.i.i96"
                            (Ty.int 8)
                            (Operand.reg "%c.val94")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add27")
                            (Operand.reg "%off1.i.i96"),
                          Instr.gep
                            "%msg2.i.i97"
                            (Ty.int 8)
                            (Operand.reg "%c.val94")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.ptr)
                            (Operand.imm (Const.null))
                            (Operand.reg "%msg2.i.i97")],
               term := Term.br "cleanup47" },
             { name := "if.end29",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.imm (Const.int 64 0x0000000000000000#64))
                            (Operand.reg "%ei"),
                          Instr.binop
                            "%sub"
                            (BinOp.sub)
                            64
                            (Operand.reg "%len")
                            (Operand.reg "%call17"),
                          Instr.gep
                            "%add.ptr31"
                            (Ty.int 8)
                            (Operand.reg "%dst")
                            (Operand.reg "%call17"),
                          Instr.call
                            "%call32"
                            (Ty.int 64)
                            "leanllvm_json_escape_decode"
                            [(Ty.ptr, Operand.reg "%arrayidx22"),
                             (Ty.int 64, Operand.reg "%sub"),
                             (Ty.ptr, Operand.reg "%add.ptr31"),
                             (Ty.ptr, Operand.reg "%ei")],
                          Instr.icmp
                            "%cmp33"
                            (IPred.eq)
                            64
                            (Operand.reg "%call32")
                            (Operand.imm (Const.int 64 0xffffffffffffffff#64))],
               term := Term.condbr (Operand.reg "%cmp33") "if.then35" "if.end39" },
             { name := "if.then35",
               instrs := [Instr.binop
                            "%add36"
                            (BinOp.add)
                            64
                            (Operand.reg "%call17")
                            (Operand.reg "%sub.ptr.sub"),
                          Instr.load "%6" (Ty.int 64) (Operand.reg "%ei"),
                          Instr.binop
                            "%add37"
                            (BinOp.add)
                            64
                            (Operand.reg "%add36")
                            (Operand.reg "%6"),
                          Instr.gep
                            "%7"
                            (Ty.int 8)
                            (Operand.reg "%c")
                            (Operand.imm (Const.int 64 0x0000000000000458#64)),
                          Instr.load "%c.val" (Ty.ptr) (Operand.reg "%7"),
                          Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000000#32))
                            (Operand.reg "%c.val"),
                          Instr.gep
                            "%off1.i.i98"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add37")
                            (Operand.reg "%off1.i.i98"),
                          Instr.gep
                            "%msg2.i.i99"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.ptr)
                            (Operand.imm (Const.null))
                            (Operand.reg "%msg2.i.i99")],
               term := Term.br "cleanup47" },
             { name := "if.end39",
               instrs := [Instr.icmp
                            "%tobool40.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%call17")
                            (Operand.imm (Const.int 64 0x0000000000000000#64))],
               term := Term.condbr (Operand.reg "%tobool40.not") "if.end43" "if.then41" },
             { name := "if.then41",
               instrs := [Instr.callVoid
                            "llvm.memcpy.p0.p0.i64"
                            [(Ty.ptr, Operand.reg "%dst"),
                             (Ty.ptr, Operand.reg "%p"),
                             (Ty.int 64, Operand.reg "%call17"),
                             (Ty.int 1, Operand.imm (Const.int 1 0x0#1))]],
               term := Term.br "if.end43" },
             { name := "if.end43",
               instrs := [Instr.binop
                            "%add44"
                            (BinOp.add)
                            64
                            (Operand.reg "%call32")
                            (Operand.reg "%call17"),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add44")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup47" },
             { name := "cleanup47",
               instrs := [Instr.phi
                            "%retval.3"
                            (Ty.int 32)
                            [("if.then9", Operand.imm (Const.int 32 0x0000000000000001#32)),
                             ("if.then12", Operand.imm (Const.int 32 0x0000000000000000#32)),
                             ("if.end15", Operand.imm (Const.int 32 0x0000000000000002#32)),
                             ("if.then20", Operand.imm (Const.int 32 0x0000000000000001#32)),
                             ("if.then26", Operand.imm (Const.int 32 0x0000000000000000#32)),
                             ("if.then35", Operand.imm (Const.int 32 0x0000000000000000#32)),
                             ("if.end43", Operand.imm (Const.int 32 0x0000000000000002#32))],
                          Instr.callVoid
                            "llvm.lifetime.end.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")]],
               term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.3")) }] }

-- Parsing `stage2.helper.s2_string_body.ll` returns `s2StringBodyBody`.
#guard decide (firstFunction s2StringBodySrc = some s2StringBodyBody)

/-- The pin's control: the same fixture with the error-record offset moved from
`1112` to `1116`.  It parses, and it is not the pinned body, so the equality
above is about the text rather than about a search that would accept either. -/
def s2StringBodySrcMutated : String := s2StringBodySrc.replace "i64 1112" "i64 1116"

#guard parses s2StringBodySrcMutated
#guard decide (firstFunction s2StringBodySrcMutated ≠ some s2StringBodyBody)

/-! ### The escape expander, at this call's eight arguments

`if.end` calls `leanllvm_json_escape_expand` with eight arguments: the body's
document pointer and extent, the destination, the offset slot, the position
list and its count, the cursor, and the body's document offset.  The ninth
argument the expander's own record takes (`Γ_escape_expand`'s table base) is not
passed here: the emitted callee has that table compiled in, which is the same
reason the capture's other bodies take a `null` message.

So this is not a restatement of that record.  What is stated is the expander's
own rule *at these eight arguments*: the cursor is scanned forward over the
list to the body's first position (`j1`), the suffix inside the body's window is
decoded by `escapeDecodeGo`, and the three writes are the ones the emitted
callee performs — the decoded prefix at the destination, the advanced cursor at
`xj`, and its own word at the offset slot.  The returned word is the decoded
length on the accepting arm and all-ones on the refusing one, which is the
comparison `if.then11` makes.

The escape unit's own correspondence is what the decode term rests on: the
expander's record is proved of the emitted expander body
(`escape_expand_satisfies_unconditional`, `JsonEscapeExpandAssembly`), and its
post's decode clause is `escapeDecodeGo` at the caller's cursor.  What this
clause adds is the eight-argument reading of that rule, which no statement in
that file makes, because its calls carry the table.

**This is a boundary, not a queued proof.**  The record's ninth argument and its
`readBytes mem tab 256 = some unescapeTable` conjunct are what the emitted call
cannot supply: the call passes eight arguments, its callee has the table compiled
in, and `Calls` — `String → List Value → Mem → Nat → Option CallOutcome` — carries
no module-level global.  That is the same boundary the refusal message's symbol
operand runs into on this capture (`stage2.helpers.tsv` records the rewrite to
`null`, and the extracted body takes the table as an appended `%tab` parameter,
which is the fragment's stand-in for a global).  So the clause is the reading in
use, not a promise: identifying it with the record would take a staging that
carries the table's address and its 256 bytes and an adapter between the eight-
and nine-argument calls, and neither is in the tree.  What the body proof rests
on is therefore the decoder's rule at this call's arguments — `escapeDecodeGo`,
which is the proved record's post's decode clause — and not the expander's own
call. -/
def escapeExpand8 : Calls
  | "leanllvm_json_escape_expand",
    [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
     .int 64 pos0], mem, next =>
      match stage2ReadWord mem xj 8, readLanes32 mem xp nxp.toNat,
            readBytes mem p len.toNat with
      | some j0, some ps, some body =>
          let j1 := j0 + ((ps.drop j0).takeWhile (fun q => q < pos0.toNat)).length
          let inBody := (ps.drop j1).takeWhile (fun q => q < pos0.toNat + len.toNat)
          match escapeDecodeGo body 0 0 (inBody.map (fun q => q - pos0.toNat)) [] with
          | .decoded out k =>
              some { ret := .int 64 (BitVec.ofNat 64 out.length),
                     mem := writeBytes
                       (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
                       ei (wordBytes 8 out.length),
                     next := next }
          | .refused off k =>
              some { ret := .int 64 0xffffffffffffffff#64,
                     mem := writeBytes (writeBytes mem ei (wordBytes 8 off))
                       xj (wordBytes 8 (j1 + k)),
                     next := next }
      | _, _, _ => none
  | _, _, _, _ => none

/-! ### The list-free arm's two callees and the exact prefix copy

`z_scan` writes no state and returns the first control byte or backslash of the
body's own span; `leanllvm_json_escape_decode` is the escape unit's list-free
decoder, whose accepting answer writes the decoded span at `dst` and whose refusal
writes the body-relative offset into the slot; `llvm.memcpy.p0.p0.i64` writes the
`n` bytes it reads.  All three are clauses of the body's environment, so every
call the emitted text makes is one this fragment describes. -/

/-- `z_scan`: the first control byte or backslash of the span, all-ones when it
has none.  The scan writes no state, which is why the body has one slot. -/
def zScan8 : Calls
  | "z_scan", [.ptr p, .int 64 len], mem, next =>
      match readBytes mem p len.toNat with
      | some body =>
          some { ret := .int 64 (match firstSpanSpecial? body 0 with
                                 | none => 0xffffffffffffffff#64
                                 | some (off, _) => BitVec.ofNat 64 off),
                 mem := mem, next := next }
      | none => none
  | _, _, _, _ => none

/-- `leanllvm_json_escape_decode` at its emitted four arguments: the decoded span
at `dst`, or the span-relative refusal offset in the slot. -/
def escapeDecode4 : Calls
  | "leanllvm_json_escape_decode", [.ptr p, .int 64 len, .ptr dst, .ptr ei], mem, next =>
      match readBytes mem p len.toNat with
      | some body =>
          match escapeDecodeSpan body with
          | .decoded out _ => some { ret := .int 64 (BitVec.ofNat 64 out.length),
                                     mem := writeBytes mem dst out, next := next }
          | .refused rel _ => some { ret := .int 64 0xffffffffffffffff#64,
                                     mem := writeBytes mem ei (wordBytes 8 rel), next := next }
      | none => none
  | _, _, _, _ => none

/-- `llvm.memcpy.p0.p0.i64`: the bytes it reads, written exactly at the
destination, and nothing else. -/
def memcpy4 : Calls
  | "llvm.memcpy.p0.p0.i64", [.ptr dst, .ptr src, .int 64 n, .int 1 _], mem, next =>
      match readBytes mem src n.toNat with
      | some bs => some { ret := .int 1 0, mem := writeBytes mem dst bs, next := next }
      | none => none
  | _, _, _, _ => none

/-- The body's out-of-line callees: the expander on the list arm, and the scan,
the list-free decoder and the exact copy on the no-list arm. -/
def s2StringBodySub : Calls := fun callee args mem next =>
  match callee with
  | "z_scan" => zScan8 callee args mem next
  | "leanllvm_json_escape_decode" => escapeDecode4 callee args mem next
  | "llvm.memcpy.p0.p0.i64" => memcpy4 callee args mem next
  | _ => escapeExpand8 callee args mem next

/-- **The body's call environment**: the two lifetime markers and `memset` from
the walk's own intrinsic selection, and the four clauses above.  A body this
environment does not describe fails rather than being read as something it is
not. -/
def s2StringBodyCalls : Calls := JsonStage2IR.stage2Calls s2StringBodySub

/-- The walk's intrinsic selection sends this callee to the clause below. -/
theorem s2StringBodyCalls_expand_eq (args : List Value) (mem : Mem) (next : Nat) :
    s2StringBodyCalls "leanllvm_json_escape_expand" args mem next =
      escapeExpand8 "leanllvm_json_escape_expand" args mem next := rfl

theorem s2StringBodyCalls_zscan_eq (args : List Value) (mem : Mem) (next : Nat) :
    s2StringBodyCalls "z_scan" args mem next = zScan8 "z_scan" args mem next := rfl

theorem s2StringBodyCalls_decode_eq (args : List Value) (mem : Mem) (next : Nat) :
    s2StringBodyCalls "leanllvm_json_escape_decode" args mem next =
      escapeDecode4 "leanllvm_json_escape_decode" args mem next := rfl

theorem s2StringBodyCalls_memcpy_eq (args : List Value) (mem : Mem) (next : Nat) :
    s2StringBodyCalls "llvm.memcpy.p0.p0.i64" args mem next =
      memcpy4 "llvm.memcpy.p0.p0.i64" args mem next := rfl

/-- **The expander's accepting answer at this call's eight arguments**: the
decoded prefix at the destination, the advanced cursor at `xj`, the decoded
length at the offset slot, and the length as the returned word. -/
theorem escapeExpand8_decoded (p len dst ei xp xj nxp pos0 : Nat) (mem : Mem)
    (next : Nat) {j0 : Nat} {ps : List Nat} {body out : List UInt8} {k : Nat}
    (hj : stage2ReadWord mem xj 8 = some j0)
    (hp : readLanes32 mem xp nxp = some ps)
    (hb : readBytes mem p len = some body)
    (hlen : len < 2 ^ 64) (hnxp : nxp < 2 ^ 64) (hpos0 : pos0 < 2 ^ 64)
    (hd : escapeDecodeGo body 0 0
      (((ps.drop (j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length)).takeWhile
        (fun q => q < pos0 + len)).map (fun q => q - pos0)) [] = .decoded out k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 (BitVec.ofNat 64 len), .ptr dst, .ptr ei, .ptr xp, .ptr xj,
       .int 64 (BitVec.ofNat 64 nxp), .int 64 (BitVec.ofNat 64 pos0)] mem next =
    some { ret := .int 64 (BitVec.ofNat 64 out.length),
           mem := writeBytes (writeBytes (writeBytes mem dst out) xj
             (wordBytes 8 (j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length + k)))
             ei (wordBytes 8 out.length),
           next := next } := by
  rw [s2StringBodyCalls_expand_eq]
  unfold escapeExpand8
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hnxp,
    Nat.mod_eq_of_lt hpos0, hj, hp, hb, hd]

/-- **The expander's refusing answer at this call's eight arguments**: the
body-relative offset at the offset slot, the advanced cursor, and all-ones as
the returned word. -/
theorem escapeExpand8_refused (p len dst ei xp xj nxp pos0 : Nat) (mem : Mem)
    (next : Nat) {j0 : Nat} {ps : List Nat} {body : List UInt8} {off k : Nat}
    (hj : stage2ReadWord mem xj 8 = some j0)
    (hp : readLanes32 mem xp nxp = some ps)
    (hb : readBytes mem p len = some body)
    (hlen : len < 2 ^ 64) (hnxp : nxp < 2 ^ 64) (hpos0 : pos0 < 2 ^ 64)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop (j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length)).takeWhile
        (fun q => q < pos0 + len)).map (fun q => q - pos0)) [] = .refused off k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 (BitVec.ofNat 64 len), .ptr dst, .ptr ei, .ptr xp, .ptr xj,
       .int 64 (BitVec.ofNat 64 nxp), .int 64 (BitVec.ofNat 64 pos0)] mem next =
    some { ret := .int 64 0xffffffffffffffff#64,
           mem := writeBytes (writeBytes mem ei (wordBytes 8 off)) xj
             (wordBytes 8 (j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length + k)),
           next := next } := by
  rw [s2StringBodyCalls_expand_eq]
  unfold escapeExpand8
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hnxp,
    Nat.mod_eq_of_lt hpos0, hj, hp, hb, hr]

/-- **`z_scan` at this call's two arguments**: the first special byte's offset, or
all-ones for a plain span. -/
theorem zScan8_at (p len : Nat) (mem : Mem) (next : Nat) {body : List UInt8}
    (hb : readBytes mem p len = some body) (hlen : len < 2 ^ 64) :
    s2StringBodyCalls "z_scan" [.ptr p, .int 64 (BitVec.ofNat 64 len)] mem next =
      some { ret := .int 64 (match firstSpanSpecial? body 0 with
                             | none => 0xffffffffffffffff#64
                             | some (off, _) => BitVec.ofNat 64 off),
             mem := mem, next := next } := by
  rw [s2StringBodyCalls_zscan_eq]
  unfold zScan8
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, hb]

/-- **The list-free decoder's accepting answer at this call's four arguments**:
the decoded span at `dst` and the decoded length as the returned word. -/
theorem escapeDecode4_decoded (p len dst ei : Nat) (mem : Mem) (next : Nat)
    {body out : List UInt8} {k : Nat}
    (hb : readBytes mem p len = some body) (hlen : len < 2 ^ 64)
    (hd : escapeDecodeSpan body = .decoded out k) :
    s2StringBodyCalls "leanllvm_json_escape_decode"
      [.ptr p, .int 64 (BitVec.ofNat 64 len), .ptr dst, .ptr ei] mem next =
    some { ret := .int 64 (BitVec.ofNat 64 out.length),
           mem := writeBytes mem dst out, next := next } := by
  rw [s2StringBodyCalls_decode_eq]
  unfold escapeDecode4
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, hb, hd]

/-- **The list-free decoder's refusing answer at this call's four arguments**: the
span-relative offset in the slot and all-ones as the returned word. -/
theorem escapeDecode4_refused (p len dst ei : Nat) (mem : Mem) (next : Nat)
    {body : List UInt8} {rel k : Nat}
    (hb : readBytes mem p len = some body) (hlen : len < 2 ^ 64)
    (hr : escapeDecodeSpan body = .refused rel k) :
    s2StringBodyCalls "leanllvm_json_escape_decode"
      [.ptr p, .int 64 (BitVec.ofNat 64 len), .ptr dst, .ptr ei] mem next =
    some { ret := .int 64 0xffffffffffffffff#64,
           mem := writeBytes mem ei (wordBytes 8 rel), next := next } := by
  rw [s2StringBodyCalls_decode_eq]
  unfold escapeDecode4
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, hb, hr]

/-- **`llvm.memcpy.p0.p0.i64` at this call's four arguments**: the read bytes
written at the destination. -/
theorem memcpy4_at (dst src n : Nat) (volatile : BitVec 1) (mem : Mem) (next : Nat)
    {bs : List UInt8} (hb : readBytes mem src n = some bs) (hn : n < 2 ^ 64) :
    s2StringBodyCalls "llvm.memcpy.p0.p0.i64"
      [.ptr dst, .ptr src, .int 64 (BitVec.ofNat 64 n), .int 1 volatile] mem next =
    some { ret := .int 1 0, mem := writeBytes mem dst bs, next := next } := by
  rw [s2StringBodyCalls_memcpy_eq]
  unfold memcpy4
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hb]

/-! ### One instruction, one step

The shapes this body has that `BlockEval`'s vocabulary does not: the address
conversion, an `i32` `getelementptr`, the `i32` lane load, an `i64` store of a
literal, a `ptr` store of `null`, the `alloca`, and the two call forms.  Each is
the `evalInstr` equation at the environment builder, in the shape its chain step
consumes. -/

theorem sb_step_alloca (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (al : Nat) :
    evalInstr calls (stateAt env s) (.alloca d ty al) =
      some (stateAt ((d, .ptr s.next) :: env) { s with next := s.next + ty.sizeBytes }) := by
  rfl

theorem sb_step_loadPtr (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat} (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (wordBytes 8 q)) (hq : q < 2 ^ 64) :
    evalInstr calls (stateAt env s) (.load d (Ty.ptr) (.reg p)) =
      some (stateAt ((d, .ptr q) :: env) s) := by
  have hbs : bytesToNat (wordBytes 8 q) = q := by
    rw [wordBytes, natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
      Nat.mod_eq_of_lt hq]
  have hv' : loadValue s.mem (.ptr) a = some (.ptr q) := by
    simp only [loadValue, hv, hbs]
  simp only [evalInstr, evalOperand, stateAt, hp, hv', State.bind]

/-- **Write order is not free when a region is absent from memory.**  The closing
must align the body's write order with the model's, and the obvious lemma — that
two writes over separated regions commute — is *false* as an equality of
memories.  `writeByte` replaces a present cell in place and appends an absent
one, so two absent regions are ordered by the write sequence: here the same two
bytes at the same two addresses, written in the two orders, are two different
lists.  A commutation that holds is pointwise (`readByte` equality outside the
two regions), or is an equality of lists at a staging where at least one region is
already present (`readBytes m a bs.length = some bs` makes that write a no-op, and
the other write then meets the same addresses in the same order on both sides).
The witness is the both-absent case, so a crossing needs one present region rather
than two: `writeBytes_comm_of_present_left` and `writeBytes_comm_of_present_right`
are the two choices of which one it spends. -/
theorem writeBytes_absent_comm_witness :
    writeBytes (writeBytes [] 0 [1]) 1 [2] ≠
      writeBytes (writeBytes [] 1 [2]) 0 [1] := by decide

/-- **Reads do not determine the memory.**  A memory with a duplicated address
answers every read exactly as the memory without the duplicate: `readByte` returns
the *first* cell there.  So the two are different lists with the same byte at every
address, which is why region extensionality cannot be stated from reads alone.

This is the shape wall the absorption runs into, and it is the same kind of record
as `writeBytes_absent_comm_witness`: a false form stated so that the true one's
hypothesis is visible.  The hypothesis it points at is **duplicate-freedom** — a
`Nodup` on the address sequence — which nothing in this cone supplies, and which the
staging would have to state for the closing to compare memories as lists. -/
theorem readByte_not_determined_by_reads :
    (∀ a : Nat, readByte [(0, 1)] a = readByte [(0, 1), (0, 2)] a) ∧
      ([(0, 1)] : Mem) ≠ [(0, 1), (0, 2)] := by
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | zero => rfl
    | succ n => simp [readByte]
  · intro h
    exact absurd h (by simp)

/-- **The canonical form is not `writeByte`.**  `writeByte` replaces the *first* cell
at an address; a map over the memory replaces *every* cell there.  With a duplicated
address the two disagree, so `writeByte A a c = A.map (…)` — and therefore the
`memUpd` equivalence the section proposes — needs duplicate-freedom as well as
presence.

This closes the canonical route in this setting: duplicate-freedom is exactly the
staging clause the join is not allowed to add.  The absorption itself survives,
because both of its sides replace the *same* first occurrences; what does not
survive is the map that was meant to make it cheap. -/
theorem writeByte_not_map_of_duplicate :
    writeByte [(0, 1), (0, 2)] 0 5
      ≠ [(0, 1), (0, 2)].map (fun p => if p.1 = 0 then (p.1, 5) else p) := by
  decide

/-- **The nineteen blocks, in the order the body runs them.**  `findBlock` is a
search over this list, so the names and their order are what every block's step
lemma resolves against; the control beneath it is a name the body does not carry.
The per-block literal pins live in `JsonStage2StringBodyBlocks`, where the runs
consume them, together with the control that two blocks resolve to different
literals. -/
theorem s2StringBodyBody_blockNames :
    (s2StringBodyBody.blocks.map (·.name)) =
      ["entry", "while.cond.preheader", "land.rhs", "while.body", "land.lhs.true",
       "if.then9", "if.end", "if.then12", "if.end15", "if.end16", "if.then20",
       "if.end21", "if.then26", "if.end29", "if.then35", "if.end39", "if.then41",
       "if.end43", "cleanup47"] := by decide

-- The control: a block the body does not have is not found.
theorem s2StringBodyBody_findBlock_absent :
    s2StringBodyBody.findBlock "land.rhs.not" = none := by decide

/-! ### The entry block's environment, named

The block builds six cells over the caller's environment, and the run's statement
names them as definitions rather than as nested cons terms — the spelling
`JsonStage2WalkRun`'s `walkEntry_denote` uses, and the reason its chain matches:
a step's conclusion is `stateAt ((d, v) :: env) s'`, and a named definition is
*that* term, so the closer's `dsimp only [s2StringBodyEnv1, …]` reconciles the two
without either side having to guess a wildcard.  The allocator moves once, at the
slot's `alloca`, the lifetime marker writes no cell, and every definition below is
parameterised by the value its instruction read. -/
def s2StringBodyEnv1 (env : Env) (ei : Nat) : Env := ("%ei", .ptr ei) :: env

def s2StringBodyEnv2 (env : Env) (base : Nat) : Env := ("%0", .ptr base) :: env

def s2StringBodyEnv3 (env : Env) (p : Nat) : Env :=
  ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: env

def s2StringBodyEnv4 (env : Env) (base : Nat) : Env :=
  ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) :: env

def s2StringBodyEnv5 (env : Env) (p base : Nat) : Env :=
  ("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) :: env

def s2StringBodyEnv6 (env : Env) (nxp : BitVec 64) : Env :=
  ("%tobool.not", .int 1 (evalICmp .eq nxp (BitVec.ofNat 64 0))) :: env

/-- The seven instructions the entry block runs, in order: the slot's
allocation, the two address conversions and their subtraction, the slot's
lifetime marker, and the `nxp = 0` test. -/
def s2StringBodyEntryInstrs : List Instr :=
  [Instr.alloca "%ei" (Ty.int 64) 0,
   Instr.load "%0" (Ty.ptr) (Operand.reg "%c"),
   Instr.ptrtoint "%sub.ptr.lhs.cast" (Operand.reg "%p"),
   Instr.ptrtoint "%sub.ptr.rhs.cast" (Operand.reg "%0"),
   Instr.binop "%sub.ptr.sub" (BinOp.sub) 64 (Operand.reg "%sub.ptr.lhs.cast")
     (Operand.reg "%sub.ptr.rhs.cast"),
   Instr.callVoid "llvm.lifetime.start.p0"
     [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
      (Ty.ptr, Operand.reg "%ei")],
   Instr.icmp "%tobool.not" (IPred.eq) 64 (Operand.reg "%nxp")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

-- The instruction list is the block the pin resolves to: the run is the block's
-- own body, not a reading of it.
theorem s2StringBodyEntryInstrs_eq :
    (s2StringBodyBody.findBlock "entry").map (·.instrs) =
      some s2StringBodyEntryInstrs := by decide

/- **A write of the bytes already there leaves the memory alone** — the form the
closing needs for a region the body rewrites with its own value (the cursor word
when the scan does not run, the slot on the arm that writes nothing):
`readBytes m a bs.length = some bs → writeBytes m a bs = m`.  The proof is
`writeByte`'s in-place branch at the head byte and the induction at the next
address: `rw [List.length_cons, Nat.add_one] at h` before `simp only [readBytes]`
(so the read unfolds at the sum), then the head's `readByte` and the tail's
`readBytes` named by `cases`, then the head byte substituted — after which the
self-write lemma is applied at `b`, not at the `cases`-bound name — and the
induction hypothesis at `a + 1`.  It is stated here as the next obligation rather
than proved. -/

theorem sb_step_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {bs : List UInt8} (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some bs) :
    evalInstr calls (stateAt env s) (.load d (Ty.int 32) (.reg p)) =
      some (stateAt ((d, .int 32 (BitVec.ofNat 32 (bytesToNat bs))) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s p (.ptr a) hp
  have hv' : loadValue (stateAt env s).mem (.int 32) a =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs))) := by
    change loadValue s.mem (.int 32) a =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs)))
    simp only [loadValue, hv, show (32 + 7) / 8 = 4 from rfl]
    rw [ite_eq_right (by decide : ¬ ((32 : Nat) = 0))]
  unfold evalInstr
  dsimp only
  rw [h1]
  dsimp only
  rw [hv']
  rfl

theorem sb_step_ptrtoint (calls : Calls) (env : Env) (s : State) (d v : String)
    {a : Nat} (hv : lookupName env v = some (.ptr a)) (ha : a < 2 ^ 64) :
    evalInstr calls (stateAt env s) (.ptrtoint d (.reg v)) =
      some (stateAt ((d, .int 64 (BitVec.ofNat 64 a)) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s v (.ptr a) hv
  unfold evalInstr
  dsimp only
  rw [h1]
  dsimp only
  rw [if_pos ha]
  rfl

theorem sb_step_gep32 (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (Ty.int 32) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 4)) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s base (.ptr a) hb
  have h2 := BlockEval.evalOperand_reg_of env s off (.int 64 idx) ho
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  dsimp only
  rw [if_pos hpos]
  simp [State.bind, stateAt, Ty.sizeBytes, BitVec.signExtend_eq]

theorem sb_step_gep8_lit (calls : Calls) (env : Env) (s : State) (d base : String)
    (n : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a)) (hpos : n.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (Ty.int 8) (.reg base) (.imm (.int 64 n))) =
      some (stateAt ((d, .ptr (a + n.toNat)) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s base (.ptr a) hb
  have h2 : evalOperand (stateAt env s) (.imm (.int 64 n)) = some (.int 64 n) := rfl
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  dsimp only
  rw [if_pos (by simpa using hpos)]
  simp [State.bind, stateAt, Ty.sizeBytes, BitVec.signExtend_eq]

theorem sb_step_icmp_rr (calls : Calls) (env : Env) (s : State) (d a b : String)
    (pr : IPred) {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.icmp d pr 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmpNat pr 64 x.toNat y.toNat)) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s a (.int 64 x) ha
  have h2 := BlockEval.evalOperand_reg_of env s b (.int 64 y) hb
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, Value.intToNat]

theorem sb_step_store64_imm (calls : Calls) (env : Env) (s : State) (p : String)
    {x : BitVec 64} {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.int 64) (.imm (.int 64 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have h1 : evalOperand (stateAt env s) (.imm (.int 64 x)) = some (.int 64 x) := rfl
  have h2 := BlockEval.evalOperand_reg_of env s p (.ptr a) hp
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, storeValue]

theorem sb_step_storePtr_null (calls : Calls) (env : Env) (s : State) (p : String)
    {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.ptr) (.imm (.null)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes 0 8) }) := by
  simp [evalInstr, evalOperand, stateAt, hp, storeValue, State.bind, Const.toValue]

end LeanLLVM.Refinement
