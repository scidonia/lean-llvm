/-
`s2_string_body`'s emitted body: the AST it parses to, and the body proved of its
contract.

`JsonStage2HelperIR` pins `s2_string_body`'s text only as far as its parse.  This
module takes the rest of the step the sibling rows' bodies took: the ten blocks
are transcribed, `#guard`ed against the fixture, and then run at the staging
`s2StringBodyPre` states, with the outcome shown to satisfy `s2StringBodyPost` and
`s2StringBodyFoot`'s frame.

**The file's order is the dependency's**: the fixtures and the pinned AST, then
the block pins (`findBlock`, instruction lists), then the one-instruction steps,
then the runs — a run placed before a step it calls reads as an unknown
identifier.  **The chain's four facts**, each of which cost a revert to find: a
step is applied at the **cons** environment the previous step built (the named
`Env` definitions are the statement's spelling, reconciled at the end); the
allocator cell is `(Ty.int 64).sizeBytes`, not the numeral it reduces to; a
one-cell-deep lookup is `(by s2_lk)`; and `denoteCode_load64`'s implicit value
must be named (`(v := …)`) or its metavariable survives into the closing goal.

**And the fourth**: a statement whose environment or memory nests more than three
deep gets a `def` — there the parser's layout, not the prover, decides whether the
lemma exists at all.

**And the fifth**: every term a chain matches on is the *unreduced* form the
emitting step produces, so the statement's `def` and the chain's patterns must be
written from the produced term and not from the source text.  Three parts, each
measured on `if.then11`: a `getelementptr`'s address is `a + n.toNat` with the
literal's `toNat` unreduced (`c + (1112#64).toNat`, not `c + 1112`); a stored
value likewise (`natToBytes (0#32).toNat 4`, not `natToBytes 0 4`); and an
arithmetic cell is `x + c` in the immediate's own `BitVec` form.  The two sides of
a failed reconciliation are printed by the compiler, which is where the produced
term should be copied from — and **two margins**: the final reconciliation must
rewrite *both* `denoteCode []` occurrences (`simp only [denoteCode_nil, …]`, not a
single `rw`), and a step's `_` slot can hide a **bound** as easily as a value, so
when the two sides print identically and the goal will not close, the residual is
a side condition of a step rather than a mismatch of terms.

**The body.**  `entry` converts the two addresses and reads the cursor word;
`land.rhs`/`while.body` scan the position list forward to the body's first
position; `land.lhs.true` tests whether that position is inside the body;
`if.then` is the body-itself form; `if.end` calls the expander; `if.then11` writes
the refusal record and `if.end14` the decoded length; `cleanup` and `cleanup16`
select the returned form.  `%ei` is the body's own eight-byte slot for the
expander's offset, which is why the block opens with an `alloca`: it is one of the
four body-allocated objects no caller stages.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonStage2HelperIRBodies

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The body, as the fixture parses

The literal below is the parser's own result written out: `capture-stage2-helpers.sh`
produced the text, and the `#guard` beneath it asserts that parsing the fixture
returns exactly this.  The pin is a `#guard` rather than an `rfl` proposition
because the parser runs on `String` primitives, which the kernel does not reduce.
The control beside it is `s2StringBodySrcMutated`: the same text with the error
record's offset changed, which still parses and is not the pinned body. -/

/-- `@s2_string_body`, as `probes/install/ir/stage2.helper.s2_string_body.ll`
parses. -/
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
                          Instr.load "%xj.promoted" (Ty.int 64) (Operand.reg "%xj"),
                          Instr.icmp
                            "%cmp3"
                            (IPred.ult)
                            64
                            (Operand.reg "%xj.promoted")
                            (Operand.reg "%nxp")],
               term := Term.condbr (Operand.reg "%cmp3") "land.rhs" "if.then" },
             { name := "land.rhs",
               instrs := [Instr.phi
                            "%inc24"
                            (Ty.int 64)
                            [("while.body", Operand.reg "%inc"),
                             ("entry", Operand.reg "%xj.promoted")],
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
               term := Term.condbr (Operand.reg "%exitcond.not") "if.then" "land.rhs" },
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
               term := Term.condbr (Operand.reg "%cmp7") "if.end" "if.then" },
             { name := "if.then",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%len")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup16" },
             { name := "if.end",
               instrs := [Instr.callVoid
                            "llvm.lifetime.start.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")],
                          Instr.store
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
                            "%cmp9"
                            (IPred.eq)
                            64
                            (Operand.reg "%call")
                            (Operand.imm (Const.int 64 0xffffffffffffffff#64))],
               term := Term.condbr (Operand.reg "%cmp9") "if.then11" "if.end14" },
             { name := "if.then11",
               instrs := [Instr.load "%2" (Ty.int 64) (Operand.reg "%ei"),
                          Instr.binop
                            "%add12"
                            (BinOp.add)
                            64
                            (Operand.reg "%2")
                            (Operand.reg "%sub.ptr.sub"),
                          Instr.gep
                            "%3"
                            (Ty.int 8)
                            (Operand.reg "%c")
                            (Operand.imm (Const.int 64 0x0000000000000458#64)),
                          Instr.load "%c.val" (Ty.ptr) (Operand.reg "%3"),
                          Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000000#32))
                            (Operand.reg "%c.val"),
                          Instr.gep
                            "%off1.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add12")
                            (Operand.reg "%off1.i.i"),
                          Instr.gep
                            "%msg2.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.ptr)
                            (Operand.imm (Const.null))
                            (Operand.reg "%msg2.i.i")],
               term := Term.br "cleanup" },
             { name := "if.end14",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%call")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup" },
             { name := "cleanup",
               instrs := [Instr.phi
                            "%retval.0"
                            (Ty.int 32)
                            [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
                             ("if.end14", Operand.imm (Const.int 32 0x00000002#32))],
                          Instr.callVoid
                            "llvm.lifetime.end.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")]],
               term := Term.br "cleanup16" },
             { name := "cleanup16",
               instrs := [Instr.phi
                            "%retval.1"
                            (Ty.int 32)
                            [("cleanup", Operand.reg "%retval.0"),
                             ("if.then", Operand.imm (Const.int 32 0x0000000000000001#32))]],
               term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.1")) }] }

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
that file makes, because its calls carry the table. -/
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

/-- **The body's call environment**: the two lifetime markers and `memset` from
the walk's own intrinsic selection, and the expander at the clause above.  A body
this environment does not describe fails rather than being read as something it
is not. -/
def s2StringBodyCalls : Calls := JsonStage2IR.stage2Calls escapeExpand8

/-- The walk's intrinsic selection sends this callee to the clause below. -/
theorem s2StringBodyCalls_expand_eq (args : List Value) (mem : Mem) (next : Nat) :
    s2StringBodyCalls "leanllvm_json_escape_expand" args mem next =
      escapeExpand8 "leanllvm_json_escape_expand" args mem next := rfl

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
two regions), or is an equality of lists at a staging where both regions are
already present (`readBytes m a bs.length = some bs` makes the write a no-op).
The witness is why the closing's regions must be stated present, not merely
separated. -/
theorem writeBytes_absent_comm_witness :
    writeBytes (writeBytes [] 0 [1]) 1 [2] ≠
      writeBytes (writeBytes [] 1 [2]) 0 [1] := by decide

/-- **The ten blocks, in the order the body runs them.**  `findBlock` is a
search over this list, so the names and their order are what every block's step
lemma resolves against; the control beneath it is a name the body does not carry. -/
theorem s2StringBodyBody_blockNames :
    (s2StringBodyBody.blocks.map (·.name)) =
      ["entry", "land.rhs", "while.body", "land.lhs.true", "if.then", "if.end",
       "if.then11", "if.end14", "cleanup", "cleanup16"] := by decide

-- The control: a block the body does not have is not found.
theorem s2StringBodyBody_findBlock_absent :
    s2StringBodyBody.findBlock "land.rhs.not" = none := by decide

/-- **The entry block.**  Seven instructions: the slot's `alloca`, the two
address conversions, the subtraction, the cursor read and the two tests. -/
theorem s2StringBody_findBlock_entry :
    s2StringBodyBody.findBlock "entry" =
      some ⟨"entry",
        [Instr.alloca "%ei" (Ty.int 64) 0,
         Instr.load "%0" (Ty.ptr) (Operand.reg "%c"),
         Instr.ptrtoint "%sub.ptr.lhs.cast" (Operand.reg "%p"),
         Instr.ptrtoint "%sub.ptr.rhs.cast" (Operand.reg "%0"),
         Instr.binop "%sub.ptr.sub" (BinOp.sub) 64 (Operand.reg "%sub.ptr.lhs.cast")
           (Operand.reg "%sub.ptr.rhs.cast"),
         Instr.load "%xj.promoted" (Ty.int 64) (Operand.reg "%xj"),
         Instr.icmp "%cmp3" (IPred.ult) 64 (Operand.reg "%xj.promoted")
           (Operand.reg "%nxp")],
        Term.condbr (Operand.reg "%cmp3") "land.rhs" "if.then"⟩ := by decide

-- The nine blocks beside `entry`, each the literal `findBlock` resolves to.  The
-- search is over the list pinned above, so these nine and the entry's statement
-- are what every block's step lemma rewrites with; the two controls beneath them
-- are that a name the body does not carry is `none`, and that two different
-- blocks do not resolve to the same literal — a step applied at the wrong block
-- fails here rather than in the run that follows it.
theorem s2StringBody_findBlock_land_rhs :
    s2StringBodyBody.findBlock "land.rhs" =
      some { name := "land.rhs",
               instrs := [Instr.phi
                            "%inc24"
                            (Ty.int 64)
                            [("while.body", Operand.reg "%inc"),
                             ("entry", Operand.reg "%xj.promoted")],
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
               term := Term.condbr (Operand.reg "%cmp1") "while.body" "land.lhs.true" } := by decide

theorem s2StringBody_findBlock_while_body :
    s2StringBodyBody.findBlock "while.body" =
      some { name := "while.body",
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
               term := Term.condbr (Operand.reg "%exitcond.not") "if.then" "land.rhs" } := by decide

theorem s2StringBody_findBlock_land_lhs_true :
    s2StringBodyBody.findBlock "land.lhs.true" =
      some { name := "land.lhs.true",
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
               term := Term.condbr (Operand.reg "%cmp7") "if.end" "if.then" } := by decide

theorem s2StringBody_findBlock_if_then :
    s2StringBodyBody.findBlock "if.then" =
      some { name := "if.then",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%len")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup16" } := by decide

theorem s2StringBody_findBlock_if_end :
    s2StringBodyBody.findBlock "if.end" =
      some { name := "if.end",
               instrs := [Instr.callVoid
                            "llvm.lifetime.start.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")],
                          Instr.store
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
                            "%cmp9"
                            (IPred.eq)
                            64
                            (Operand.reg "%call")
                            (Operand.imm (Const.int 64 0xffffffffffffffff#64))],
               term := Term.condbr (Operand.reg "%cmp9") "if.then11" "if.end14" } := by decide

theorem s2StringBody_findBlock_if_then11 :
    s2StringBodyBody.findBlock "if.then11" =
      some { name := "if.then11",
               instrs := [Instr.load "%2" (Ty.int 64) (Operand.reg "%ei"),
                          Instr.binop
                            "%add12"
                            (BinOp.add)
                            64
                            (Operand.reg "%2")
                            (Operand.reg "%sub.ptr.sub"),
                          Instr.gep
                            "%3"
                            (Ty.int 8)
                            (Operand.reg "%c")
                            (Operand.imm (Const.int 64 0x0000000000000458#64)),
                          Instr.load "%c.val" (Ty.ptr) (Operand.reg "%3"),
                          Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000000#32))
                            (Operand.reg "%c.val"),
                          Instr.gep
                            "%off1.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%add12")
                            (Operand.reg "%off1.i.i"),
                          Instr.gep
                            "%msg2.i.i"
                            (Ty.int 8)
                            (Operand.reg "%c.val")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.ptr)
                            (Operand.imm (Const.null))
                            (Operand.reg "%msg2.i.i")],
               term := Term.br "cleanup" } := by decide

theorem s2StringBody_findBlock_if_end14 :
    s2StringBodyBody.findBlock "if.end14" =
      some { name := "if.end14",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%call")
                            (Operand.reg "%outn")],
               term := Term.br "cleanup" } := by decide

theorem s2StringBody_findBlock_cleanup :
    s2StringBodyBody.findBlock "cleanup" =
      some { name := "cleanup",
               instrs := [Instr.phi
                            "%retval.0"
                            (Ty.int 32)
                            [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
                             ("if.end14", Operand.imm (Const.int 32 0x00000002#32))],
                          Instr.callVoid
                            "llvm.lifetime.end.p0"
                            [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
                             (Ty.ptr, Operand.reg "%ei")]],
               term := Term.br "cleanup16" } := by decide

theorem s2StringBody_findBlock_cleanup16 :
    s2StringBodyBody.findBlock "cleanup16" =
      some { name := "cleanup16",
               instrs := [Instr.phi
                            "%retval.1"
                            (Ty.int 32)
                            [("cleanup", Operand.reg "%retval.0"),
                             ("if.then", Operand.imm (Const.int 32 0x00000001#32))]],
               term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.1")) } := by decide
-- The control: two different blocks are two different literals.
theorem s2StringBody_findBlock_entry_ne_ifEnd :
    s2StringBodyBody.findBlock "entry" ≠ s2StringBodyBody.findBlock "if.end" := by decide

/-! ### The entry block's environment, named

The block builds seven cells over the caller's environment, and the run's
statement names them as definitions rather than as nested cons terms — the
spelling `JsonStage2WalkRun`'s `walkEntry_denote` uses, and the reason its chain
matches: a step's conclusion is `stateAt ((d, v) :: env) s'`, and a named
definition is *that* term, so the closer's `dsimp only [s2StringBodyEnv1, …]`
reconciles the two without either side having to guess a wildcard.  The
allocator moves once, at the slot's `alloca`, and every definition below is
parameterised by the value its instruction read. -/
def s2StringBodyEnv1 (env : Env) (ei : Nat) : Env := ("%ei", .ptr ei) :: env

def s2StringBodyEnv2 (env : Env) (base : Nat) : Env := ("%0", .ptr base) :: env

def s2StringBodyEnv3 (env : Env) (p : Nat) : Env :=
  ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: env

def s2StringBodyEnv4 (env : Env) (base : Nat) : Env :=
  ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) :: env

def s2StringBodyEnv5 (env : Env) (p base : Nat) : Env :=
  ("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) :: env

def s2StringBodyEnv6 (env : Env) (j0 : Nat) : Env :=
  ("%xj.promoted", .int 64 (BitVec.ofNat 64 j0)) :: env

def s2StringBodyEnv7 (env : Env) (j0 : Nat) (nxp : BitVec 64) : Env :=
  ("%cmp3", .int 1 (evalICmp .ult (BitVec.ofNat 64 j0) nxp)) :: env

/-- The seven instructions the entry block runs, in order: the slot's
allocation, the two address conversions and their subtraction, the cursor read
and the test. -/
def s2StringBodyEntryInstrs : List Instr :=
  [Instr.alloca "%ei" (Ty.int 64) 0,
   Instr.load "%0" (Ty.ptr) (Operand.reg "%c"),
   Instr.ptrtoint "%sub.ptr.lhs.cast" (Operand.reg "%p"),
   Instr.ptrtoint "%sub.ptr.rhs.cast" (Operand.reg "%0"),
   Instr.binop "%sub.ptr.sub" (BinOp.sub) 64 (Operand.reg "%sub.ptr.lhs.cast")
     (Operand.reg "%sub.ptr.rhs.cast"),
   Instr.load "%xj.promoted" (Ty.int 64) (Operand.reg "%xj"),
   Instr.icmp "%cmp3" (IPred.ult) 64 (Operand.reg "%xj.promoted")
     (Operand.reg "%nxp")]

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
  have h1 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) := hp
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
  have h1 : evalOperand (stateAt env s) (.reg v) = some (.ptr a) := hv
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
  have h1 : evalOperand (stateAt env s) (.reg base) = some (.ptr a) := hb
  have h2 : evalOperand (stateAt env s) (.reg off) = some (.int 64 idx) := ho
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
  have h1 : evalOperand (stateAt env s) (.reg base) = some (.ptr a) := hb
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
  have h1 : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) := ha
  have h2 : evalOperand (stateAt env s) (.reg b) = some (.int 64 y) := hb
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, Value.intToNat]

theorem sb_step_store64_imm (calls : Calls) (env : Env) (s : State) (p : String)
    {x : BitVec 64} {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.int 64) (.imm (.int 64 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have h1 : evalOperand (stateAt env s) (.imm (.int 64 x)) = some (.int 64 x) := rfl
  have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) := hp
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, storeValue]

theorem sb_step_storePtr_null (calls : Calls) (env : Env) (s : State) (p : String)
    {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.ptr) (.imm (.null)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes 0 8) }) := by
  simp [evalInstr, evalOperand, stateAt, hp, storeValue, State.bind, Const.toValue]


/-! ### Axiom footprints

The clause and the two arm lemmas print their footprints with `#guard_msgs`, so
the build checks them rather than printing them.  The instrument's
discriminating control is the one §7.6 records: a throwaway declaration proved
with `sorry` prints `sorryAx` under the same command.  No `sorry` is in this
module. -/
/-- info: 'LeanLLVM.Refinement.escapeExpand8_decoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand8_decoded

/-- info: 'LeanLLVM.Refinement.escapeExpand8_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand8_refused

/-- info: 'LeanLLVM.Refinement.s2StringBodyCalls_expand_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s2StringBodyCalls_expand_eq

/-- `store i32 <c>, ptr %p`: the refusal record's first field. -/
theorem sb_step_store32_imm (calls : Calls) (env : Env) (s : State) (p : String)
    {x : BitVec 32} {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.int 32) (.imm (.int 32 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have h1 : evalOperand (stateAt env s) (.imm (.int 32 x)) = some (.int 32 x) := rfl
  have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) := hp
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, storeValue]

/-- A void call at two arguments: the lifetime marker's emitted form. -/
theorem sb_step_callVoid2 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.int 64, o1), (Ty.ptr, o2)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, o1), (Ty.ptr, o2)] = some [v1, v2] := by
    simp only [evalOperands, h1, h2]
  have hc' : calls callee [v1, v2] (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- A call at eight arguments binding its `i64` result: the expander's emitted
form.  Its outcome is the clause's (`escapeExpand8_decoded`/`_refused`). -/
theorem sb_step_call8 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 o3 o4 o5 o6 o7 o8 : Operand)
    {v1 v2 v3 v4 v5 v6 v7 v8 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (h6 : evalOperand (stateAt env s) o6 = some v6)
    (h7 : evalOperand (stateAt env s) o7 = some v7)
    (h8 : evalOperand (stateAt env s) o8 = some v8)
    (hc : calls callee [v1, v2, v3, v4, v5, v6, v7, v8] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.call d (Ty.int 64) callee
        [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4), (Ty.ptr, o5),
         (Ty.ptr, o6), (Ty.int 64, o7), (Ty.int 64, o8)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4), (Ty.ptr, o5),
       (Ty.ptr, o6), (Ty.int 64, o7), (Ty.int 64, o8)] =
      some [v1, v2, v3, v4, v5, v6, v7, v8] := by
    simp only [evalOperands, h1, h2, h3, h4, h5, h6, h7, h8]
  have hc' : calls callee [v1, v2, v3, v4, v5, v6, v7, v8]
      (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- **The entry block's run.**  The seven instructions, each applied at the
**cons** environment the previous step built — the named `Env` definitions are
the statement's spelling and are reconciled at the end — with the allocator cell
carried as `(Ty.int 64).sizeBytes` and each one-cell-deep lookup peeled by
`s2_lk`.  The two address cells are the instructions' own values, `ptrtoint` and
`sub` at `i64`, which is what the model's `Nat` arithmetic is bridged to at the
closing rather than here. -/
theorem s2StringBody_entry_denote {calls : Calls} {env : Env} {s : State}
    {c p xj base j0 : Nat} {nxp : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64) :
    denoteCode calls s2StringBodyEntryInstrs (stateAt env s) =
      denoteCode calls []
        (stateAt (s2StringBodyEnv7 (s2StringBodyEnv6 (s2StringBodyEnv5
          (s2StringBodyEnv4 (s2StringBodyEnv3 (s2StringBodyEnv2
            (s2StringBodyEnv1 env s.next) base) p) base) p base) j0) j0 nxp)
          { s with next := s.next + (Ty.int 64).sizeBytes }) := by
  dsimp only [s2StringBodyEntryInstrs]
  rw [denoteCode_cons_of _ _ _ _ _ (sb_step_alloca calls env s "%ei" (Ty.int 64) 0)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr calls (("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%0" "%c" (by s2_lk) hbase hb64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_ptrtoint calls (("%0", .ptr base) :: ("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%sub.ptr.lhs.cast" "%p" (by s2_lk) hp64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_ptrtoint calls
      (("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
        ("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%sub.ptr.rhs.cast" "%0" (by s2_lk) hb64)]
  rw [denoteCode_sub_reg calls
    (("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
      ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
      ("%ei", .ptr s.next) :: env) { s with next := s.next + (Ty.int 64).sizeBytes }
    "%sub.ptr.sub" "%sub.ptr.lhs.cast" "%sub.ptr.rhs.cast" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_load64 (v := BitVec.ofNat 64 j0) calls
    (("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) ::
      ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
      ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
      ("%ei", .ptr s.next) :: env) { s with next := s.next + (Ty.int 64).sizeBytes }
    "%xj.promoted" "%xj" (by s2_lk)
    (by rw [hj0]; simp only [wordBytes]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64]) _]
  rw [denoteCode_icmp_ult_reg calls
    (("%xj.promoted", .int 64 (BitVec.ofNat 64 j0)) ::
      ("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) ::
      ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
      ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
      ("%ei", .ptr s.next) :: env) { s with next := s.next + (Ty.int 64).sizeBytes }
    "%cmp3" "%xj.promoted" "%nxp" (by s2_lk) (by s2_lk) []]
  rw [denoteCode_nil, denoteCode_nil]
  simp only [s2StringBodyEnv1, s2StringBodyEnv2, s2StringBodyEnv3, s2StringBodyEnv4,
    s2StringBodyEnv5, s2StringBodyEnv6, s2StringBodyEnv7]

/-- The `if.then` arm's one instruction: the body-itself form's length word. -/
theorem s2StringBodyIfThenInstrs_eq :
    (s2StringBodyBody.findBlock "if.then").map (·.instrs) =
      some [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")] := by
  decide

/-- **The `if.then` arm's run**: `outn` takes the body's extent, and the memory is
the caller's everywhere else. -/
theorem s2StringBody_ifThen_denote {calls : Calls} {env : Env} {s : State}
    {len : BitVec 64} {outn : Nat}
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")]
        (stateAt env s) =
      denoteCode calls []
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) }) := by
  rw [denoteCode_store64 calls env s "%len" "%outn" hlen houtn []]

/-- The `if.end14` arm's one instruction: the decoded length at `outn`. -/
theorem s2StringBodyIfEnd14Instrs_eq :
    (s2StringBodyBody.findBlock "if.end14").map (·.instrs) =
      some [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")] := by
  decide

/-- **The `if.end14` arm's run**: the expander's returned word at `outn`, which is
the decoded length on the accepting arm. -/
theorem s2StringBody_ifEnd14_denote {calls : Calls} {env : Env} {s : State}
    {call : BitVec 64} {outn : Nat}
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls
        [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")]
        (stateAt env s) =
      denoteCode calls []
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8) }) := by
  rw [denoteCode_store64 calls env s "%call" "%outn" hcall houtn []]

/-- The `while.body` block's instruction list. -/
def s2StringBodyWhileBodyInstrs : List Instr :=
  [Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%inc24")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.store (Ty.int 64) (Operand.reg "%inc") (Operand.reg "%xj"),
   Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc")
     (Operand.reg "%nxp")]

/-- The `while.body` block's three instructions: the counter's increment, its
write-back to the cursor word, and the exit test. -/
theorem s2StringBodyWhileBodyInstrs_eq :
    (s2StringBodyBody.findBlock "while.body").map (·.instrs) =
      some [Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%inc24")
              (Operand.imm (Const.int 64 0x0000000000000001#64)),
            Instr.store (Ty.int 64) (Operand.reg "%inc") (Operand.reg "%xj"),
            Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc")
              (Operand.reg "%nxp")] := by
  decide

/-- The `if.then11` block's environment and memory, named: the record's pointer,
its three fields, and the offset word the expander returned. -/
def s2StringBodyIfThen11Env (env : Env) (off sub : BitVec 64) (c e : Nat) : Env :=
  ("%msg2.i.i", .ptr (e + (16#64).toNat)) ::
    ("%off1.i.i", .ptr (e + (8#64).toNat)) ::
    ("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
    ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env

def s2StringBodyIfThen11Mem (mem : Mem) (e : Nat) (off sub : BitVec 64) : Mem :=
  writeBytes
    (writeBytes (writeBytes mem e (natToBytes (0#32).toNat 4))
      (e + (8#64).toNat) (natToBytes (off + sub).toNat 8))
    (e + (16#64).toNat) (natToBytes 0 8)

/-- The `if.then11` block's instruction list: the expander's offset word, the
record's pointer, and the record's three fields. -/
def s2StringBodyIfThen11Instrs : List Instr :=
  [Instr.load "%2" (Ty.int 64) (Operand.reg "%ei"),
   Instr.binop "%add12" (BinOp.add) 64 (Operand.reg "%2") (Operand.reg "%sub.ptr.sub"),
   Instr.gep "%3" (Ty.int 8) (Operand.reg "%c")
     (Operand.imm (Const.int 64 0x0000000000000458#64)),
   Instr.load "%c.val" (Ty.ptr) (Operand.reg "%3"),
   Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x0000000000000000#32))
     (Operand.reg "%c.val"),
   Instr.gep "%off1.i.i" (Ty.int 8) (Operand.reg "%c.val")
     (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.store (Ty.int 64) (Operand.reg "%add12") (Operand.reg "%off1.i.i"),
   Instr.gep "%msg2.i.i" (Ty.int 8) (Operand.reg "%c.val")
     (Operand.imm (Const.int 64 0x0000000000000010#64)),
   Instr.store (Ty.ptr) (Operand.imm (Const.null)) (Operand.reg "%msg2.i.i")]

theorem s2StringBodyIfThen11Instrs_eq :
    (s2StringBodyBody.findBlock "if.then11").map (·.instrs) =
      some s2StringBodyIfThen11Instrs := by decide

theorem s2StringBody_ifThen11_denote {calls : Calls} {env : Env} {s : State}
    {c ei e : Nat} {off sub : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    denoteCode calls s2StringBodyIfThen11Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt (s2StringBodyIfThen11Env env off sub c e)
          { s with mem := s2StringBodyIfThen11Mem s.mem e off sub }) := by
  dsimp only [s2StringBodyIfThen11Instrs]
  rw [denoteCode_load64 (v := off) calls env s "%2" "%ei"
    (by simpa [lookupName] using hei) hoff _]
  rw [denoteCode_add_reg calls (("%2", .int 64 off) :: env) s "%add12" "%2"
    "%sub.ptr.sub" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s "%3" "%c"
      (1112#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr calls
      (("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s
      "%c.val" "%3" (by s2_lk) hcval he64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store32_imm calls
      (("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s
      "%c.val" (by s2_lk))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
      "%off1.i.i" "%c.val" (8#64) (by s2_lk) (by decide))]
  rw [denoteCode_store64 calls
    (("%off1.i.i", .ptr (e + (8#64).toNat)) ::
      ("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
      ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
    { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
    "%add12" "%off1.i.i" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%off1.i.i", .ptr (e + (8#64).toNat)) ::
        ("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i" "%c.val" (16#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_storePtr_null calls
      (("%msg2.i.i", .ptr (e + (16#64).toNat)) ::
        ("%off1.i.i", .ptr (e + (8#64).toNat)) ::
        ("%c.val", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add12", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i" (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyIfThen11Env, s2StringBodyIfThen11Mem]

/-- **The `while.body` block's run**: the counter advances by one, the cursor
word takes it, and the exit test compares it with the count.  This is the scan's
per-iteration effect, the write the `BoundLoop`'s invariant carries. -/
theorem s2StringBody_whileBody_denote {calls : Calls} {env : Env} {s : State}
    {inc24 nxp : BitVec 64} {xj : Nat}
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode calls s2StringBodyWhileBodyInstrs (stateAt env s) =
      denoteCode calls []
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) :: env)
          { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) }) := by
  dsimp only [s2StringBodyWhileBodyInstrs]
  rw [denoteCode_add_imm calls env s "%inc" "%inc24" hinc24 _]
  rw [denoteCode_store64 calls (("%inc", .int 64 (inc24 + 1#64)) :: env) s "%inc" "%xj"
    (by s2_lk) (by s2_lk) _]
  rw [denoteCode_icmp_eq_reg calls (("%inc", .int 64 (inc24 + 1#64)) :: env)
    { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) }
    "%exitcond.not" "%inc" "%nxp" (by s2_lk) (by s2_lk) []]

/-! ### The `if.end` block: the expander's call, and the test of its answer

The block marks `%ei` live, clears the offset word, calls the expander at eight
arguments, and compares the returned word with all-ones.  Its two call shapes are
the model's: the lifetime marker is an identity (`stage2Calls` selects it by the
callee's name — no value read, no byte written, no allocation), and the expander
is `s2StringBodyCalls`'s own clause.

**The marker's step is stated, not rewritten through `sb_step_callVoid2`.**  That
step takes the argument values and the outcome as parameters, so a chain that
supplies only the operands leaves `v2`, `r`, and the `r.mem`/`r.next` in the goal
as metavariables.  The side goal the compiler then reports is

    ⊢ s2StringBodyCalls callee [v1, ?v2] s.mem s.next = some ?r

— a goal *about* the call, whose visible form names its operands, not the
marker's answer — and a chain that keeps answering it by rewriting the argument
alone leaves it unchanged, because the missing piece is `hc`, not `h1`/`h2`.  At
this environment the answer is not a parameter: `stage2Calls` selects it by the
callee's name, so the marker writes nothing and allocates nothing, and the step's
conclusion is the state unchanged.  The form to write from is the produced one. -/
theorem sb_step_lifetime (env : Env) (s : State) (ei : Nat) (callee : String)
    (hname : callee = "llvm.lifetime.start.p0" ∨ callee = "llvm.lifetime.end.p0")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    evalInstr s2StringBodyCalls (stateAt env s)
        (.callVoid callee [(Ty.int 64, .imm (.int 64 (8#64))), (Ty.ptr, .reg "%ei")]) =
      some (stateAt env s) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, .imm (.int 64 (8#64))), (Ty.ptr, .reg "%ei")] =
      some [.int 64 (8#64), .ptr ei] := by
    simp only [evalOperands, evalOperand, Const.toValue, stateAt, hei]
  rcases hname with rfl | rfl <;>
    simp only [evalInstr, hargs, s2StringBodyCalls, JsonStage2IR.stage2Calls]

/-- The `if.end` block's environment: the expander's returned word and the
branch test over it. -/
def s2StringBodyIfEndEnv (env : Env) (call : BitVec 64) : Env :=
  ("%cmp9", .int 1 (evalICmp .eq call 0xffffffffffffffff#64)) ::
    ("%call", .int 64 call) :: env

/-- The `if.end` block's instruction list: the marker, the cleared offset word,
the expander at eight arguments, and the test of its answer. -/
def s2StringBodyIfEndInstrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0"
     [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
      (Ty.ptr, Operand.reg "%ei")],
   Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64))
     (Operand.reg "%ei"),
   Instr.call "%call" (Ty.int 64) "leanllvm_json_escape_expand"
     [(Ty.ptr, Operand.reg "%p"), (Ty.int 64, Operand.reg "%len"),
      (Ty.ptr, Operand.reg "%dst"), (Ty.ptr, Operand.reg "%ei"),
      (Ty.ptr, Operand.reg "%xp"), (Ty.ptr, Operand.reg "%xj"),
      (Ty.int 64, Operand.reg "%nxp"), (Ty.int 64, Operand.reg "%sub.ptr.sub")],
   Instr.icmp "%cmp9" (IPred.eq) 64 (Operand.reg "%call")
     (Operand.imm (Const.int 64 0xffffffffffffffff#64))]

-- The list is the block the pin resolves to: the run is the block's own body.
theorem s2StringBodyIfEndInstrs_eq :
    (s2StringBodyBody.findBlock "if.end").map (·.instrs) =
      some s2StringBodyIfEndInstrs := by decide

/-- **The `if.end` block's run**: the marker, the cleared offset word, the
expander at the eight registers the entry block left, and the test of the
returned word against all-ones.  The callee's answer is the arm's own literal —
its returned word, its memory and its cursor — so the chain's state is named
rather than existentially bound: no step of it leaves a metavariable in the
conclusion. -/
theorem s2StringBody_ifEnd_denote {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hc : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := m, next := nx }) :
    denoteCode s2StringBodyCalls s2StringBodyIfEndInstrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx }) := by
  dsimp only [s2StringBodyIfEndInstrs]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_lifetime env s ei "llvm.lifetime.start.p0" (Or.inl rfl) hei)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store64_imm s2StringBodyCalls env s "%ei" (x := 0#64) hei)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_call8 s2StringBodyCalls env _ "%call" "leanllvm_json_escape_expand"
      (.reg "%p") (.reg "%len") (.reg "%dst") (.reg "%ei") (.reg "%xp")
      (.reg "%xj") (.reg "%nxp") (.reg "%sub.ptr.sub")
      hp hlen hdst hei hxp hxj hnxp hsub hc)]
  rw [denoteCode_icmp_eq_imm s2StringBodyCalls _ _ "%cmp9" "%call" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyIfEndEnv]

/-! ### The scan's head, its inside test, and the two cleanup blocks

`land.rhs` is the scan's head: a `phi` naming the counter, the lane's address,
the lane, its zero-extension and the test against the body's extent.
`land.lhs.true` adds the extent to the base offset and tests the lane against it.
`cleanup` and `cleanup16` select the returned form — a `phi` each, and the
marker's identity step on the way out.

**The `phi` steps are the leading run, as one step.**  `denoteCode_phi` reads the
edge's label out of `s.pre` and selects the operand that label names, at the
state the edge delivered; that is why each of these runs carries the predecessor
as a hypothesis, and why the two blocks that name a `phi` have no other way to
state the step: `evalInstr`'s own `phi` arm binds through `s.bind`, while
`denoteCode`'s run installs every member at one snapshot (`denoteCode_phiRun`). -/

/-- The `land.rhs` block's instruction list. -/
def s2StringBodyLandRhsInstrs : List Instr :=
  [Instr.phi "%inc24" (Ty.int 64)
     [("while.body", Operand.reg "%inc"), ("entry", Operand.reg "%xj.promoted")],
   Instr.gep "%arrayidx" (Ty.int 32) (Operand.reg "%xp") (Operand.reg "%inc24"),
   Instr.load "%1" (Ty.int 32) (Operand.reg "%arrayidx"),
   Instr.zext "%conv" 32 64 (Operand.reg "%1"),
   Instr.icmp "%cmp1" (IPred.ugt) 64 (Operand.reg "%sub.ptr.sub")
     (Operand.reg "%conv")]

theorem s2StringBodyLandRhsInstrs_eq :
    (s2StringBodyBody.findBlock "land.rhs").map (·.instrs) =
      some s2StringBodyLandRhsInstrs := by decide

/-- The `land.rhs` block's environment: the counter, the lane's address, the lane
and its zero-extension, and the test over the body's extent — each in the form
its step produced. -/
def s2StringBodyLandRhsEnv (env : Env) (inc24 : BitVec 64) (xp : Nat)
    (bs : List UInt8) (sub : BitVec 64) : Env :=
  ("%cmp1", .int 1 (evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat)) ::
    ("%conv", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) ::
    ("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
    ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
    ("%inc24", .int 64 inc24) :: env

/-- **The `land.rhs` block's run**, at the predecessor the edge delivered: the
counter's `phi`, the lane at the position, its zero-extension and the test. -/
theorem s2StringBody_landRhs_denote {calls : Calls} {env : Env} {s : State}
    {p : String} {op : Operand} {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8}
    {sub : BitVec 64}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs) :
    denoteCode calls s2StringBodyLandRhsInstrs (stateAt env s) =
      denoteCode calls [] (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s) := by
  dsimp only [s2StringBodyLandRhsInstrs]
  rw [denoteCode_phi calls env s "%inc24" (Ty.int 64) _ hpre hinc hop _ (by decide)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep32 calls (("%inc24", .int 64 inc24) :: env) s "%arrayidx" "%xp"
      "%inc24" (by s2_lk) (by s2_lk) hpos)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_load32 calls
      (("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
        ("%inc24", .int 64 inc24) :: env) s "%1" "%arrayidx" (by s2_lk) hlane)]
  rw [denoteCode_zext calls
    (("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
      ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
      ("%inc24", .int 64 inc24) :: env) s "%conv" "%1" 32 64 (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_icmp_rr calls
      (("%conv", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) ::
        ("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
        ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
        ("%inc24", .int 64 inc24) :: env) s "%cmp1" "%sub.ptr.sub" "%conv" .ugt
      (by s2_lk) (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyLandRhsEnv]

/-- The `land.lhs.true` block's instruction list: the extent's end and the test
of the lane against it. -/
def s2StringBodyLandLhsTrueInstrs : List Instr :=
  [Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%sub.ptr.sub")
     (Operand.reg "%len"),
   Instr.icmp "%cmp7" (IPred.ugt) 64 (Operand.reg "%add") (Operand.reg "%conv")]

theorem s2StringBodyLandLhsTrueInstrs_eq :
    (s2StringBodyBody.findBlock "land.lhs.true").map (·.instrs) =
      some s2StringBodyLandLhsTrueInstrs := by decide

/-- **The `land.lhs.true` block's run**: the body's extent as an end address, and
the lane tested against it. -/
theorem s2StringBody_landLhsTrue_denote {calls : Calls} {env : Env} {s : State}
    {sub len conv : BitVec 64}
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv)) :
    denoteCode calls s2StringBodyLandLhsTrueInstrs (stateAt env s) =
      denoteCode calls []
        (stateAt
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) s) := by
  dsimp only [s2StringBodyLandLhsTrueInstrs]
  rw [denoteCode_add_reg calls env s "%add" "%sub.ptr.sub" "%len" hsub hlen _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_icmp_rr calls (("%add", .int 64 (sub + len)) :: env) s "%cmp7"
      "%add" "%conv" .ugt (by s2_lk) hconv)]

/-- The `cleanup` block's instruction list: the returned form's `phi` and the
slot's end marker. -/
def s2StringBodyCleanupInstrs : List Instr :=
  [Instr.phi "%retval.0" (Ty.int 32)
     [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
      ("if.end14", Operand.imm (Const.int 32 0x00000002#32))],
   Instr.callVoid "llvm.lifetime.end.p0"
     [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
      (Ty.ptr, Operand.reg "%ei")]]

theorem s2StringBodyCleanupInstrs_eq :
    (s2StringBodyBody.findBlock "cleanup").map (·.instrs) =
      some s2StringBodyCleanupInstrs := by decide

/-- **The `cleanup` block's run**: the form's `phi`, and the marker — an identity
step at this environment, so the block's memory and cursor are the edge's. -/
theorem s2StringBody_cleanup_denote {env : Env} {s : State}
    {p : String} {op : Operand} {form : BitVec 32} {ei : Nat}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
      ("if.end14", Operand.imm (Const.int 32 0x00000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    denoteCode s2StringBodyCalls s2StringBodyCleanupInstrs (stateAt env s) =
      denoteCode s2StringBodyCalls [] (stateAt (("%retval.0", .int 32 form) :: env) s) := by
  dsimp only [s2StringBodyCleanupInstrs]
  rw [denoteCode_phi s2StringBodyCalls env s "%retval.0" (Ty.int 32) _ hpre hinc hop _
    (by decide)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_lifetime (("%retval.0", .int 32 form) :: env) s ei
      "llvm.lifetime.end.p0" (Or.inr rfl) (by s2_lk))]

/-- The `cleanup16` block's instruction list: the returned form's second `phi`,
which reads the first's cell on one edge and the body's own constant on the
other. -/
def s2StringBodyCleanup16Instrs : List Instr :=
  [Instr.phi "%retval.1" (Ty.int 32)
     [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))]]

theorem s2StringBodyCleanup16Instrs_eq :
    (s2StringBodyBody.findBlock "cleanup16").map (·.instrs) =
      some s2StringBodyCleanup16Instrs := by decide

/-- **The `cleanup16` block's run**: the second `phi`, and nothing else. -/
theorem s2StringBody_cleanup16_denote {calls : Calls} {env : Env} {s : State}
    {p : String} {op : Operand} {form : BitVec 32}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form)) :
    denoteCode calls s2StringBodyCleanup16Instrs (stateAt env s) =
      denoteCode calls [] (stateAt (("%retval.1", .int 32 form) :: env) s) := by
  dsimp only [s2StringBodyCleanup16Instrs]
  rw [denoteCode_phi calls env s "%retval.1" (Ty.int 32) _ hpre hinc hop _ (by decide)]

/-! ### Writing a region twice

The closing must match the body's memory to the model's, and the scan's own
invariant must update the cursor word once per iteration.  Both need the same
fact, and it is not the one the list encoding makes obvious: `writeByte` replaces
a cell in place when the address is present and **appends** it otherwise, so two
writes over separated regions are *not* interchangeable as lists — the write order
survives in the appended cells (`writeBytes_absent_comm_witness` is the witness).
What does hold is the weaker, sufficient form proved here: writing a region twice
is the second write, when the second write is at least as long.  The first write's
cells inside the region are then all replaced in place, and the cells the two
writes append are the same cells in the same order — so the appended tail, which
is what the order would have distinguished, is identical.

This ordering rule is the one the scan needs at `(xj, 8)` every iteration and the
one the closing needs wherever the body rewrites a region the model writes once. -/

/-- Writing one address twice is the second write: the first leaves a cell there,
in place or appended, and the second replaces that cell. -/
theorem writeByte_writeByte_same (m : Mem) (a : Nat) (b₁ b : UInt8) :
    writeByte (writeByte m a b₁) a b = writeByte m a b := by
  induction m with
  | nil => simp [writeByte]
  | cons cell rest ih =>
      obtain ⟨a', b'⟩ := cell
      by_cases h : a' = a
      · subst h; simp [writeByte]
      · simp only [writeByte, ite_eq_right h]
        rw [ih]

/-- Writes at two different addresses commute as lists when the second address is
occupied: an absent cell is appended, so its *position* is what makes the two
orders differ, and an occupied one is replaced where it stands. -/
theorem writeByte_swap_of_readByte (m : Mem) (a : Nat) (b : UInt8) :
    ∀ (a' : Nat) (b' : UInt8), a ≠ a' → readByte m a ≠ none →
      writeByte (writeByte m a b) a' b' = writeByte (writeByte m a' b') a b := by
  induction m with
  | nil => intro a' b' _ hp; exact absurd rfl hp
  | cons cell rest ih =>
      obtain ⟨x, c⟩ := cell
      intro a' b' hne hp
      by_cases h1 : x = a
      · have hxa' : x ≠ a' := by rw [h1]; exact hne
        simp only [writeByte, ite_eq_left h1, ite_eq_right hxa']
      · by_cases h2 : x = a'
        · simp only [writeByte, ite_eq_right h1, ite_eq_left h2]
        · have hp' : readByte rest a ≠ none := by
            intro hc
            apply hp
            simp only [readByte, ite_eq_right h1, hc]
          simp only [writeByte, ite_eq_right h1, ite_eq_right h2]
          rw [ih a' b' hne hp']

/-- A cell outside a written range keeps its place: the write sequence conses
nothing at that address and appends nothing before it. -/
theorem writeBytes_cons_outside (a' : Nat) (b' : UInt8) :
    ∀ (a : Nat) (bs : List UInt8), a' < a ∨ a + bs.length ≤ a' →
      ∀ rest : Mem,
        writeBytes ((a', b') :: rest) a bs = (a', b') :: writeBytes rest a bs
  | _, [], _, _ => rfl
  | a, b :: bs, h, rest => by
      have hne : a' ≠ a := by
        intro heq
        subst heq
        rcases h with h | h
        · exact absurd h (Nat.lt_irrefl a')
        · simp only [List.length_cons] at h; omega
      show writeBytes (writeByte ((a', b') :: rest) a b) (a + 1) bs
        = (a', b') :: writeBytes rest a (b :: bs)
      rw [show writeByte ((a', b') :: rest) a b = (a', b') :: writeByte rest a b from by
        simp only [writeByte, ite_eq_right hne]]
      exact writeBytes_cons_outside a' b' (a + 1) bs (by
        rcases h with h | h
        · exact Or.inl (by omega)
        · simp only [List.length_cons] at h; omega) (writeByte rest a b)

/-- A single write below a sequence's range commutes with the whole sequence, when
the address it writes is occupied. -/
theorem writeByte_writeBytes_above (m : Mem) (a : Nat) (b : UInt8) :
    ∀ (a' : Nat) (bs : List UInt8), a < a' → readByte m a ≠ none →
      writeByte (writeBytes m a' bs) a b = writeBytes (writeByte m a b) a' bs
  | _, [], _, _ => rfl
  | a', b' :: bs, hlt, hp => by
      show writeByte (writeBytes (writeByte m a' b') (a' + 1) bs) a b
        = writeBytes (writeByte (writeByte m a b) a' b') (a' + 1) bs
      have hpres : readByte (writeByte m a' b') a ≠ none := by
        rw [readByte_writeByte_other m b' (by omega)]; exact hp
      rw [writeByte_writeBytes_above (writeByte m a' b') a b (a' + 1) bs (by omega) hpres]
      rw [writeByte_swap_of_readByte m a b a' b' (by omega) hp]

/-- A write at the head of a sequence is the sequence with its head replaced: the
rest of the sequence pushes the cell out of the way, so the write lands on the
head's own cell wherever the sequence appended it. -/
theorem writeByte_writeBytes_head (m : Mem) (a : Nat) :
    ∀ (b₁ : UInt8) (bs : List UInt8) (b : UInt8),
      writeByte (writeBytes m a (b₁ :: bs)) a b
        = writeBytes (writeByte m a b) (a + 1) bs
  | b₁, bs, b => by
      show writeByte (writeBytes (writeByte m a b₁) (a + 1) bs) a b = _
      rw [writeByte_writeBytes_above (writeByte m a b₁) a b (a + 1) bs (by omega)
        (by rw [readByte_writeByte_same]; exact Option.some_ne_none b₁)]
      rw [writeByte_writeByte_same]

/-- **Writing a region twice is the second write**, when the second write is at
least as long: the first write's cells inside the region are replaced in place,
and the two writes append the same cells in the same order.  This is the form the
scan's invariant and the closing's memory term both consume. -/
theorem writeBytes_writeBytes_same (m : Mem) (a : Nat) :
    ∀ (bs₁ bs₂ : List UInt8), bs₁.length ≤ bs₂.length →
      writeBytes (writeBytes m a bs₁) a bs₂ = writeBytes m a bs₂
  | [], _, _ => rfl
  | _ :: _, [], h => by
      simp only [List.length_cons, List.length_nil] at h; omega
  | b₁ :: bs₁, b :: bs, h => by
      show writeBytes (writeByte (writeBytes m a (b₁ :: bs₁)) a b) (a + 1) bs
        = writeBytes (writeByte m a b) (a + 1) bs
      rw [writeByte_writeBytes_head m a b₁ bs₁ b]
      exact writeBytes_writeBytes_same (writeByte m a b) (a + 1) bs₁ bs
        (by simp only [List.length_cons] at h; omega)

/-! ### The scan's bound

The scan is the body's only loop: `land.rhs` reads the lane at the counter, and
`while.body` advances the counter and writes it back.  It leaves in two ways —
`land.rhs` for `land.lhs.true` when the lane is already inside the body, and
`while.body` for `if.then` when the counter reaches the count — so the exit is a
predicate and the head's test is the disjunction of both.

**The cost is two control steps.**  One iteration is `land.rhs`'s step —
`getelementptr`, the lane load, the zero-extension and the test — then
`while.body`'s — the counter's increment, its write-back and the exit test — and
the back edge is the second one's jump, so every instantiation passes `cost = 2`;
the exit is `land.rhs`'s own jump to `land.lhs.true`, one step, inside that bound.
The field is a parameter here for the reason the decoder's instance makes it one:
the arms are the body's facts, and the bound's arithmetic is `BoundLoop`'s.

**The measure is the counter's distance to the count.**  `while.body` writes
`c + 1` to the cursor word it was given, so at the head the cursor word holds the
counter; `Inv r s c` says exactly that, together with `c + r = N`.  Both ways out
are then `atBound`'s two disjuncts: the first is the count reached, the second is
the lane already at or past the body's first position.  Neither is a decrease of
the lane's index — it is the *distance* that falls — which is why the bound is
`N` and not the position list's length. -/

/-- The scan's invariant at the head: the state is at `land.rhs`, its cursor word
holds the counter `c`, and `c + r` is the count.  `mem0` is the memory the scan
started from, and `xj` the cursor word's address: the loop's only memory effect is
that word's write, one per iteration. -/
def s2StringBodyScanInv (mem0 : Mem) (xj N : Nat) (r : Nat) (s : State)
    (c : Nat) : Prop :=
  s.pc = "land.rhs" ∧ s.mem = writeBytes mem0 xj (wordBytes 8 c) ∧ c + r = N

/-- The head's test: the next index reaches the count, or the lane at this index is
already inside the body.  The `match` is the second disjunct in a decidable form —
an unbounded `∃` over `Nat` is not a decision — and
`s2StringBodyScanAtBound_eq` states the disjunction it stands for. -/
def s2StringBodyScanAtBound (ps : List Nat) (pos0 N : Nat) : State → Nat → Bool :=
  fun _ c =>
    decide (N ≤ c + 1) ||
      match ps[c]? with
      | some q => decide (pos0 ≤ q)
      | none => false

/-- The head's test, as the two ways out. -/
theorem s2StringBodyScanAtBound_eq (ps : List Nat) (pos0 N : Nat) (s : State)
    (c : Nat) :
    s2StringBodyScanAtBound ps pos0 N s c = true ↔
      (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) := by
  unfold s2StringBodyScanAtBound
  rw [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · split at h
      · rename_i q hq
        exact Or.inr ⟨q, hq, of_decide_eq_true h⟩
      · cases h
  · rintro (h | ⟨q, hq, hle⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [hq]; exact decide_eq_true hle)

/-- **The invariant's entry**: the head carrying the entry's counter `j0`, with the
count as the whole budget. -/
theorem s2StringBodyScanInv_entry (mem0 : Mem) (xj N j0 : Nat) (s : State)
    (hpc : s.pc = "land.rhs") (hmem : s.mem = writeBytes mem0 xj (wordBytes 8 j0))
    (hj0 : j0 ≤ N) :
    s2StringBodyScanInv mem0 xj N (N - j0) s j0 :=
  ⟨hpc, hmem, by omega⟩

/-- **The scan is a `BoundLoop`.**  The bound, the head's test, the invariant and
the budget are fixed here; the two arms are the body's — the exit step and one
iteration's return to the head — stated as the shape's per-iteration facts, as the
decoder's and the copy loops' instances state theirs.  The two exits share one
induction: `Exit` is the disjunction of the blocks they leave for. -/
def s2StringBodyScanBoundLoop (mem0 : Mem) (xj N pos0 : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      s2StringBodyScanInv mem0 xj N r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      s2StringBodyScanInv mem0 xj N (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj N r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e) :
    BoundLoop s2StringBodyCalls s2StringBodyBody where
  head := "land.rhs"
  exitBlock := "land.lhs.true"
  N := N
  cost := cost
  Inv := s2StringBodyScanInv mem0 xj N
  atBound := s2StringBodyScanAtBound ps pos0 N
  Exit := Exit
  ExitWord := ExitWord
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    obtain ⟨_hpc, _hmem, hsum⟩ := h
    rw [s2StringBodyScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨_hpc, _hmem, hsum⟩ := h
    omega

/-- **The scan's fuel is a term of the arguments.**  With the body's two arms, the
head reaches an exit within `(N + 1) * cost` control steps, and a completed exit
continuation lifts to the whole loop.  The induction is `BoundLoop.run_at`'s;
nothing here is specific to the scan beyond its invariant. -/
theorem s2StringBodyScan_run_at (mem0 : Mem) (xj N pos0 : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      s2StringBodyScanInv mem0 xj N r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      s2StringBodyScanInv mem0 xj N (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj N r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (s : State) (c : Nat) (k : Nat) (hinv : s2StringBodyScanInv mem0 xj N N s c)
    {o : Outcome}
    (hcont : ∀ (e : State), Exit e → ExitWord e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * cost + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanBoundLoop mem0 xj N pos0 ps cost Exit ExitWord step_exit
    step_loop).run_at s c hinv k hcont

/-! ### The blocks as control steps

`step` reads a block at `s.pc`, denotes its instruction list, and executes its
terminator; the runs above are the same `denoteCode` at the same block.  The two
are one step (`step_at_block`), and what each step still needs is its terminator's
branch value — the bit the block's own test wrote, which the run's conclusion
names as the environment's cell.  Stating the bit as a hypothesis (rather than
case-splitting inside each step) is what keeps the step at the shape `runFuel`'s
recursion consumes: `runFuel_jump_prefix` turns a `.jump` into one control step,
and `BoundLoop`'s arms are two of these composed.

**The nine pin theorems are the block labels the `_at` shapes resolve to.**  Each
is `decide`, so a block whose instruction list moved fails here rather than inside
a step's proof. -/

/-- One control step from a block's run: `step` at a state whose program counter
finds `b`, whose instruction list denotes to `s'`, and whose terminator is `c`. -/
theorem step_at_block {calls : Calls} {f : Function} {s s' : State} {b : Block}
    {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) :
    step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

theorem s2StringBody_findBlock_entry_at :
    s2StringBodyBody.findBlock "entry" =
      some ⟨"entry", s2StringBodyEntryInstrs,
        Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩ := by decide

theorem s2StringBody_findBlock_land_rhs_at :
    s2StringBodyBody.findBlock "land.rhs" =
      some ⟨"land.rhs", s2StringBodyLandRhsInstrs,
        Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩ := by decide

theorem s2StringBody_findBlock_while_body_at :
    s2StringBodyBody.findBlock "while.body" =
      some ⟨"while.body", s2StringBodyWhileBodyInstrs,
        Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩ := by decide

theorem s2StringBody_findBlock_land_lhs_true_at :
    s2StringBodyBody.findBlock "land.lhs.true" =
      some ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
        Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩ := by decide

theorem s2StringBody_findBlock_if_then_at :
    s2StringBodyBody.findBlock "if.then" =
      some ⟨"if.then",
        [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")],
        Term.br "cleanup16"⟩ := by decide

theorem s2StringBody_findBlock_if_end_at :
    s2StringBodyBody.findBlock "if.end" =
      some ⟨"if.end", s2StringBodyIfEndInstrs,
        Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩ := by decide

theorem s2StringBody_findBlock_if_then11_at :
    s2StringBodyBody.findBlock "if.then11" =
      some ⟨"if.then11", s2StringBodyIfThen11Instrs, Term.br "cleanup"⟩ := by decide

theorem s2StringBody_findBlock_if_end14_at :
    s2StringBodyBody.findBlock "if.end14" =
      some ⟨"if.end14",
        [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")],
        Term.br "cleanup"⟩ := by decide

theorem s2StringBody_findBlock_cleanup_at :
    s2StringBodyBody.findBlock "cleanup" =
      some ⟨"cleanup", s2StringBodyCleanupInstrs, Term.br "cleanup16"⟩ := by decide

theorem s2StringBody_findBlock_cleanup16_at :
    s2StringBodyBody.findBlock "cleanup16" =
      some ⟨"cleanup16", s2StringBodyCleanup16Instrs,
        Term.ret (Ty.int 32) (some (Operand.reg "%retval.1"))⟩ := by decide

/-- The entry block's environment after its seven instructions, named: the
allocator's first cell and the six the block builds over it. -/
def s2StringBodyEntryOut (env : Env) (next : Nat) (base p j0 : Nat)
    (nxp : BitVec 64) : Env :=
  s2StringBodyEnv7 (s2StringBodyEnv6 (s2StringBodyEnv5 (s2StringBodyEnv4
    (s2StringBodyEnv3 (s2StringBodyEnv2 (s2StringBodyEnv1 env next) base) p) base)
    p base) j0) j0 nxp

/-- The entry block's step, to the scan's head: the test holds. -/
theorem step_entry_landRhs {env : Env} {s : State} {c p xj base j0 : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hxj hnxp hbase hb64 hp64 hj0 hj64
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The entry block's step, to the body-itself arm: the test fails. -/
theorem step_entry_ifThen {env : Env} {s : State} {c p xj base j0 : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hxj hnxp hbase hb64 hp64 hj0 hj64
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's head, while the lane is still below the body: one control step to
`while.body`. -/
theorem step_landRhs_while {env : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub)
        { s with pc := "while.body", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s)
    (b := ⟨"land.rhs", s2StringBodyLandRhsInstrs,
      Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_rhs_at
  · simpa only [denoteCode_nil] using
      s2StringBody_landRhs_denote hpre hinc hop hxp hsub hpos hlane
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The scan's head, the lane inside the body: one control step to
`land.lhs.true`, the loop's first exit. -/
theorem step_landRhs_exit {env : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub)
        { s with pc := "land.lhs.true", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s)
    (b := ⟨"land.rhs", s2StringBodyLandRhsInstrs,
      Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_rhs_at
  · simpa only [denoteCode_nil] using
      s2StringBody_landRhs_denote hpre hinc hop hxp hsub hpos hlane
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's body: the counter's advance written back, one control step to the
scan's head (`cost`'s second step). -/
theorem step_whileBody_back {env : Env} {s : State} {inc24 nxp : BitVec 64}
    {xj : Nat}
    (hpc : s.pc = "while.body")
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbit : evalICmp .eq (inc24 + 1#64) nxp = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
          ("%inc", .int 64 (inc24 + 1#64)) :: env)
        ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
        ("%inc", .int 64 (inc24 + 1#64)) :: env)
      { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) })
    (b := ⟨"while.body", s2StringBodyWhileBodyInstrs,
      Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_body_at
  · simpa only [denoteCode_nil] using s2StringBody_whileBody_denote hinc24 hxj hnxp
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's body, the counter at the count: one control step to `if.then`, the
loop's second exit. -/
theorem step_whileBody_exit {env : Env} {s : State} {inc24 nxp : BitVec 64}
    {xj : Nat}
    (hpc : s.pc = "while.body")
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbit : evalICmp .eq (inc24 + 1#64) nxp = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
          ("%inc", .int 64 (inc24 + 1#64)) :: env)
        ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
        ("%inc", .int 64 (inc24 + 1#64)) :: env)
      { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) })
    (b := ⟨"while.body", s2StringBodyWhileBodyInstrs,
      Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_body_at
  · simpa only [denoteCode_nil] using s2StringBody_whileBody_denote hinc24 hxj hnxp
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The inside test, the lane past the body's end: one control step to `if.end`. -/
theorem step_landLhsTrue_ifEnd {env : Env} {s : State} {sub len conv : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) s)
    (b := ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
      Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The inside test, the lane inside the body: one control step to `if.then`. -/
theorem step_landLhsTrue_ifThen {env : Env} {s : State} {sub len conv : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) s)
    (b := ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
      Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The body-itself arm's step: the extent's word at `outn`, then `cleanup16`. -/
theorem step_ifThen_cleanup16 {env : Env} {s : State} {len : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.then")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) })
    (b := ⟨"if.then",
      [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")],
      Term.br "cleanup16"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then_at
  · simpa only [denoteCode_nil] using s2StringBody_ifThen_denote hlen houtn
  · rfl

/-- The expander's step, its answer all-ones: one control step to the refusal
record. -/
theorem step_ifEnd_ifThen11 {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hc : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := m, next := nx })
    (hbit : evalICmp .eq call 0xffffffffffffffff#64 = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEndEnv env call)
        ({ s with mem := m, next := nx, pc := "if.then11", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The expander's step, an answer that is not all-ones: one control step to the
decoded length's write. -/
theorem step_ifEnd_ifEnd14 {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hc : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := m, next := nx })
    (hbit : evalICmp .eq call 0xffffffffffffffff#64 = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEndEnv env call)
        ({ s with mem := m, next := nx, pc := "if.end14", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

set_option maxHeartbeats 1000000 in
/-- The refusal record's step: the three fields written, then `cleanup`. -/
theorem step_ifThen11_cleanup {env : Env} {s : State} {c ei e : Nat} {off sub : BitVec 64}
    (hpc : s.pc = "if.then11")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfThen11Env env off sub c e)
        ({ s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfThen11Env env off sub c e)
      { s with mem := s2StringBodyIfThen11Mem s.mem e off sub })
    (b := ⟨"if.then11", s2StringBodyIfThen11Instrs, Term.br "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then11_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifThen11_denote hc hei hsub hoff hcval he64
  · rfl

/-- The decoded length's step at `outn`, then `cleanup`. -/
theorem step_ifEnd14_cleanup {env : Env} {s : State} {call : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.end14")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8) })
    (b := ⟨"if.end14",
      [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")],
      Term.br "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end14_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd14_denote hcall houtn
  · rfl

/-- The first cleanup block's step: the form's `phi`, then `cleanup16`. -/
theorem step_cleanup_cleanup16 {env : Env} {s : State} {p : String} {op : Operand}
    {form : BitVec 32} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
      ("if.end14", Operand.imm (Const.int 32 0x00000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (("%retval.0", .int 32 form) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (("%retval.0", .int 32 form) :: env) s)
    (b := ⟨"cleanup", s2StringBodyCleanupInstrs, Term.br "cleanup16"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_cleanup_at
  · simpa only [denoteCode_nil] using s2StringBody_cleanup_denote hpre hinc hop hei
  · rfl

/-- The second cleanup block's step: the returned form, and the function's
answer.  The `i32` the `phi` selects is what `execTerm` reads, so the terminator is
a `ret` of that word, not of the register. -/
theorem step_cleanup16_ret {env : Env} {s : State} {p : String} {op : Operand}
    {form : BitVec 32}
    (hpc : s.pc = "cleanup16") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.ret (some (.int 32 form)) (stateAt (("%retval.1", .int 32 form) :: env) s) := by
  refine step_at_block
    (s' := stateAt (("%retval.1", .int 32 form) :: env) s)
    (b := ⟨"cleanup16", s2StringBodyCleanup16Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.1"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_cleanup16_at
  · simpa only [denoteCode_nil] using s2StringBody_cleanup16_denote hpre hinc hop
  · have hv : evalOperand (stateAt (("%retval.1", .int 32 form) :: env) s)
        (.reg "%retval.1") = some (.int 32 form) := by s2_lk
    simp only [execTerm, hv]


/-- The scan's cursor word after one iteration: the word written where the cursor's
own word stands replaces it in place, so the head's memory is the caller's with the
cursor at the new counter.  This is `writeBytes_writeBytes_same` at `(xj, 8)`, and
`hc64` is what makes the counter's increment not wrap. -/
theorem s2StringBodyScan_advance (mem0 : Mem) (xj c : Nat) (s : State)
    (hmem : s.mem = writeBytes mem0 xj (wordBytes 8 c))
    (hc64 : c + 1 < 2 ^ 64) :
    writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8) =
      writeBytes mem0 xj (wordBytes 8 (c + 1)) := by
  rw [hmem]
  have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [htoNat]
  exact writeBytes_writeBytes_same mem0 xj (wordBytes 8 c) (wordBytes 8 (c + 1))
    (by simp [wordBytes, natToBytes_length])

/-- **The scan's iteration**: two control steps from the head back to the head, the
counter's word written where it stands.  The two steps are the block steps composed
through `runFuel_jump_prefix`, so the cost this loop's instance names is `2` and the
state it returns is the next head, at `(r, c + 1)` in the invariant's terms. -/
theorem s2StringBodyScanIterate {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 nxp : BitVec 64} {xp xj : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hxj : lookupName envH "%xj" = some (.ptr xj))
    (hnxp : lookupName envH "%nxp" = some (.int 64 nxp))
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt envH s) op = some (.int 64 inc24))
    (hxp : lookupName envH "%xp" = some (.ptr xp))
    (hsub : lookupName envH "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit1 : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1)
    (hbit2 : evalICmp .eq (inc24 + 1#64) nxp = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) ::
            s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })) := by
  intro k
  have h1 := step_landRhs_while (env := envH) (s := s) (p := p) (op := op)
    hpc hpre hinc hop hxp hsub hpos hlane hbit1
  have h2 := step_whileBody_back
    (env := s2StringBodyLandRhsEnv envH inc24 xp bs sub)
    (s := { s with pc := "while.body", pre := some s.pc })
    (inc24 := inc24) (nxp := nxp) (xj := xj)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hbit2
  calc runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s)
      = runFuel s2StringBodyCalls (1 + (1 + k)) s2StringBodyBody (stateAt envH s) := by
        rw [show 2 + k = 1 + (1 + k) from by omega]
    _ = runFuel s2StringBodyCalls (1 + k) s2StringBodyBody
          (stateAt (s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            { s with pc := "while.body", pre := some s.pc }) :=
        runFuel_jump_prefix h1 (1 + k)
    _ = runFuel s2StringBodyCalls k s2StringBodyBody
          (stateAt
            (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
              ("%inc", .int 64 (inc24 + 1#64)) ::
              s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })) :=
        runFuel_jump_prefix h2 k

/-- **The scan's first exit**: one control step to `land.lhs.true`, the lane already
inside the body, the memory as the head left it. -/
theorem s2StringBodyScanExit {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt envH s) op = some (.int 64 inc24))
    (hxp : lookupName envH "%xp" = some (.ptr xp))
    (hsub : lookupName envH "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          { s with pc := "land.lhs.true", pre := some s.pc }) := by
  intro k
  exact runFuel_jump_prefix
    (step_landRhs_exit hpc hpre hinc hop hxp hsub hpos hlane hbit) k

/-! ### Axiom footprints

The runs and the loop's shape print their footprints with `#guard_msgs`, so the
build checks them rather than printing them.  `Classical.choice` appears exactly
where a `getelementptr`'s sign-extension enters (`s2StringBody_landRhs_denote`, and
the loop that composes it), which is the `gep` step's core lemma and not a choice
any proof here makes; the blocks with no `getelementptr` carry the frame lemmas'
`[propext, Quot.sound]`. -/
/-- info: 'LeanLLVM.Refinement.sb_step_lifetime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sb_step_lifetime

/-- info: 'LeanLLVM.Refinement.s2StringBody_ifEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBody_ifEnd_denote

/-- info: 'LeanLLVM.Refinement.s2StringBody_landRhs_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBody_landRhs_denote

/-- info: 'LeanLLVM.Refinement.s2StringBodyScanAtBound_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s2StringBodyScanAtBound_eq

/-- info: 'LeanLLVM.Refinement.s2StringBodyScanBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBodyScanBoundLoop

/-- info: 'LeanLLVM.Refinement.s2StringBodyScan_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBodyScan_run_at

end LeanLLVM.Refinement
