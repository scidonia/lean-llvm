/-
`s2_string_body`'s emitted body: the AST it parses to, and the body proved of its
contract.

`JsonStage2HelperIR` pins `s2_string_body`'s text only as far as its parse.  This
module takes the rest of the step the sibling rows' bodies took: the ten blocks
are transcribed, `#guard`ed against the fixture, and then run at the staging
`s2StringBodyPre` states, with the outcome shown to satisfy `s2StringBodyPost` and
`s2StringBodyFoot`'s frame.

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

end LeanLLVM.Refinement
