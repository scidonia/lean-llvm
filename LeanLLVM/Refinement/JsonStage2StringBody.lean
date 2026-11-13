/-
`s2_string_body`'s emitted body: the AST it parses to, its ten blocks pinned and
run, and the expander's clause at the call's own arguments.  **The contract is not
yet proved of it.**

`JsonStage2HelperIR` pins `s2_string_body`'s text only as far as its parse.  This
module takes the same step the sibling rows' bodies took, and has taken it this
far: the ten blocks are transcribed and `#guard`ed against the fixture; each block
is a `denoteCode` run and a control step, with its branch bit named; the scan is a
`BoundLoop` value at `cost = 2` whose invariant is seated at the head the entry
leaves; and every path -- the body-itself arm, the decoded length, the refusal
record, through `land.lhs.true`'s inside test or straight out of the scan -- has
its terminal run proved.  The memory primitives the closing rests on are proved
too: writing a region twice is the second write, a region the memory holds is
written back in place, and two in-place writes over disjoint regions commute once
the commutation lemma's two swaps are in.

What is **owed** is exactly the contract: the memory term's two callee arms (the
commutation lemma and its instantiations, where the body's write order meets the
model's) and the assembly that composes seat, run and memory into
`s2StringBodyPost` and `s2StringBodyFoot`'s frame -- `s2StringBodyBody_contract`,
which does not exist yet.  Individual block runs are useful progress, but they do
not establish the whole helper's totality or postcondition, and nothing in this
module claims they do: no row moves on their strength.

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

**A fact two sections share belongs before both.**  The order above (fixtures,
steps, runs) is a dependency order and says nothing about a lemma that one
section states and another consumes; `readBytes_length_some` was written in the
bits section and read by the memory section, and had to move.  Stating such a fact
ahead of both is the rule, not an afterthought.

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

**And the two vocabulary gaps this module had to fill.**  `Lexis`-level facts the
cone does not carry: `Memory` proves the *below* case for a sequence read
(`readBytes_writeBytes_below`) and only the single-byte case above it, so
`s2StringBodyReadBytes_above` is proved here — a four-byte lane read past a write
needs it.  And there is no `getElem?_isSome`: `ps[c]? = some q` yields `c <
ps.length` through `List.getElem?_eq_none` and `cases` on the resulting absurdity.
`readLanes32_nth` states what `readLanes32_lane` states here and lives in the
walk's cone, out of this module's imports; the two names differ deliberately, so a
consumer importing both has one of each rather than an ambiguity.

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

/-- Reads above a single written cell are unchanged, so a sequence's presence
survives a write below it. -/
theorem readBytes_writeByte_below (m : Mem) {x : Nat} {v : UInt8} :
    ∀ (n a : Nat), x < a → readBytes (writeByte m x v) a n = readBytes m a n
  | 0, _, _ => by simp only [readBytes]
  | n + 1, a, h => by
      have hb : readByte (writeByte m x v) a = readByte m a :=
        readByte_writeByte_other m v (by omega)
      simp only [readBytes, hb]
      cases hr : readByte m a with
      | none => rfl
      | some b =>
          rw [readBytes_writeByte_below m n (a + 1) (by omega)]

/-- Reads at or above a written range are unchanged (`Memory` states the below
case; this is its dual, in the form a four-byte lane read needs). -/
theorem s2StringBodyReadBytes_above (m : Mem) :
    ∀ (bs : List UInt8) (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | _, 0, _, _, _ => by simp only [readBytes]
  | bs, n + 1, addr, start, h => by
      have hb : readByte (writeBytes m start bs) addr = readByte m addr :=
        readByte_writeBytes_above m bs h
      simp only [readBytes, hb]
      cases hr : readByte m addr with
      | none => simp only [hr]
      | some b =>
          simp only [hr]
          rw [s2StringBodyReadBytes_above m bs n (addr + 1) start (by omega)]

/-- Reads entirely below a single written cell are unchanged — the dual of
`readBytes_writeByte_below`, and the other half of what a presence fact needs: a
write on either side of a region leaves it alone. -/
theorem readBytes_writeByte_above (m : Mem) {x : Nat} {v : UInt8} :
    ∀ (n a : Nat), a + n ≤ x → readBytes (writeByte m x v) a n = readBytes m a n
  | 0, _, _ => by simp only [readBytes]
  | n + 1, a, h => by
      have hb : readByte (writeByte m x v) a = readByte m a :=
        readByte_writeByte_other m v (by omega)
      simp only [readBytes, hb]
      cases hr : readByte m a with
      | none => rfl
      | some b => rw [readBytes_writeByte_above m n (a + 1) (by omega)]

/-- **The swap with the presence on the other address.**  The equality is symmetric
in its two writes, so this is `writeByte_swap_of_readByte` with the addresses
exchanged — the variant the commutation's upper case needs, where the region, not
the odd byte, is the address the memory is known to hold. -/
theorem writeByte_swap_of_present_second (m : Mem) (a : Nat) (b : UInt8)
    (a' : Nat) (b' : UInt8) (h : a ≠ a') (hp : readByte m a' ≠ none) :
    writeByte (writeByte m a b) a' b' = writeByte (writeByte m a' b') a b :=
  (writeByte_swap_of_readByte m a' b' a b (Ne.symm h) hp).symm


/-- **A single byte at `b` commutes with a sequence at `a`**, given that the memory
holds a sequence of the same length at `a` and that the two ranges are disjoint.
The induction peels the presence one cell at a time (each peel is the `readBytes`
recursion), which is why presence is stated existentially — the *written* bytes and
the *present* bytes are different lists of the same length. -/
theorem writeByte_writeBytes_comm (m : Mem) (b : Nat) (y : UInt8) :
    ∀ (a : Nat) (X : List UInt8), (∃ X₀, readBytes m a X.length = some X₀) →
      (b < a ∨ a + X.length ≤ b) →
      writeByte (writeBytes m a X) b y = writeBytes (writeByte m b y) a X
  | _, [], _, _ => rfl
  | a, c :: cs, hpres, hdisj => by
      obtain ⟨X₀, hX₀⟩ := hpres
      simp only [List.length_cons] at hX₀ hdisj
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, readByte m a = some c₀ := by
        cases h : readByte m a with
        | none =>
            rw [show readBytes m a (cs.length + 1) = none from by
              simp only [readBytes, h]] at hX₀
            cases hX₀
        | some c₀ => exact ⟨c₀, rfl⟩
      obtain ⟨cs₀, hcs₀⟩ : ∃ cs₀, readBytes m (a + 1) cs.length = some cs₀ := by
        rw [show readBytes m a (cs.length + 1) = (match readByte m a with
          | none => none
          | some c₀ => match readBytes m (a + 1) cs.length with
            | none => none
            | some bs => some (c₀ :: bs))
          from rfl, hc₀] at hX₀
        cases h : readBytes m (a + 1) cs.length with
        | none => rw [h] at hX₀; cases hX₀
        | some cs₀ => exact ⟨cs₀, rfl⟩
      have htail : ∃ cs₀, readBytes (writeByte m a c) (a + 1) cs.length = some cs₀ :=
        ⟨cs₀, by
          rw [readBytes_writeByte_below m cs.length (a + 1) (by omega)]
          exact hcs₀⟩
      have hdisj' : b < a + 1 ∨ (a + 1) + cs.length ≤ b := by
        rcases hdisj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hne : a ≠ b := by
        intro heq
        rw [heq] at hdisj
        rcases hdisj with h | h <;> omega
      show writeByte (writeBytes (writeByte m a c) (a + 1) cs) b y
        = writeBytes (writeByte m b y) a (c :: cs)
      rw [writeByte_writeBytes_comm (writeByte m a c) b y (a + 1) cs htail hdisj']
      rw [show writeBytes (writeByte m b y) a (c :: cs)
        = writeBytes (writeByte (writeByte m b y) a c) (a + 1) cs from rfl]
      rw [writeByte_swap_of_readByte m a c b y hne (by rw [hc₀]; exact Option.some_ne_none c₀)]

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

/-- A successful read of `n` bytes has `n` of them. -/
theorem readBytes_length_some {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : readBytes m addr n = some bs) : bs.length = n := by
  induction n generalizing addr bs with
  | zero => simp only [readBytes, Option.some.injEq] at h; subst h; rfl
  | succ n ih =>
      simp only [readBytes] at h
      cases hb : readByte m addr with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (addr + 1) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons, ih hr]

/-- A byte read back at an address is the byte that is there, so writing it back
changes nothing: the cell is replaced where it stands. -/
theorem writeByte_readByte_self (m : Mem) (a : Nat) (b : UInt8)
    (h : readByte m a = some b) : writeByte m a b = m := by
  induction m with
  | nil => simp only [readByte] at h; cases h
  | cons cell rest ih =>
      obtain ⟨a', b'⟩ := cell
      by_cases ha : a' = a
      · subst ha
        simp only [readByte] at h
        rw [ite_eq_left trivial] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [writeByte]
        rw [ite_eq_left trivial]
      · simp only [readByte, ite_eq_right ha] at h
        simp only [writeByte, ite_eq_right ha]
        rw [ih h]

/-- **A region the memory already holds is written back with no effect.**  This is
the presence fact the scan's invariant and the closing's memory term both need:
the bytes a `readBytes` returned are exactly the bytes a `writeBytes` of them
leaves, because every cell is replaced in place. -/
theorem writeBytes_of_readBytes_self (m : Mem) :
    ∀ (n a : Nat) {bs : List UInt8}, readBytes m a n = some bs →
      bs.length = n → writeBytes m a bs = m
  | 0, _, _, h, _ => by
      simp only [readBytes, Option.some.injEq] at h
      subst h
      rfl
  | n + 1, a, bs, h, hlen => by
      simp only [readBytes] at h
      cases hb : readByte m a with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (a + 1) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons] at hlen
              show writeBytes (writeByte m a b) (a + 1) tl = m
              rw [writeByte_readByte_self m a b hb]
              exact writeBytes_of_readBytes_self m n (a + 1) hr (by omega)

/-- **The cursor word's presence, at the model's own vocabulary.**  A word the
staging reads at `xj` is already the memory's there, so the scan's first write of
it is a no-op — which is the seating's first clause, and the same fact the closing
needs for every region the body rewrites. -/
theorem stage2ReadWord_writeBytes_self (mem : Mem) (xj w j : Nat)
    (h : stage2ReadWord mem xj w = some j) :
    writeBytes mem xj (wordBytes w j) = mem := by
  unfold stage2ReadWord at h
  cases hr : readBytes mem xj w with
  | none => rw [hr] at h; cases h
  | some bs =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hlen : bs.length = w := readBytes_length_some hr
      have hbs0 : List.take bs.length (natToBytes (bytesToNat bs) w) = bs :=
        natToBytes_bytesToNat bs w (by omega)
      have htake : List.take bs.length (natToBytes (bytesToNat bs) w)
          = natToBytes (bytesToNat bs) w :=
        List.take_of_length_le (by rw [natToBytes_length]; omega)
      have hbs : natToBytes (bytesToNat bs) w = bs := by rw [← htake]; exact hbs0
      simp only [wordBytes]
      rw [hbs]
      exact writeBytes_of_readBytes_self mem w xj hr hlen


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

/-- **Two writes over disjoint present regions commute.**  Both regions are present,
so both writes are replacements in place and the append order — the one thing that
distinguishes the two sides as lists — never enters.  This is
`writeBytes_absent_comm_witness`'s statement with the hypothesis the absent case
cannot meet. -/
theorem writeBytes_comm_of_present (A : Mem) :
    ∀ (a : Nat) (X : List UInt8) (b : Nat) (Y : List UInt8),
      (∃ X₀, readBytes A a X.length = some X₀) →
      (∃ Y₀, readBytes A b Y.length = some Y₀) →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X
  | a, X, b, [], _, _, _ => rfl
  | a, X, b, y :: Ys, hX, hY, hdisj => by
      obtain ⟨Y₀, hY₀⟩ := hY
      simp only [List.length_cons] at hY₀ hdisj
      obtain ⟨y₀, hy₀⟩ : ∃ y₀, readByte A b = some y₀ := by
        cases h : readByte A b with
        | none =>
            rw [show readBytes A b (Ys.length + 1) = none from by
              simp only [readBytes, h]] at hY₀
            cases hY₀
        | some y₀ => exact ⟨y₀, rfl⟩
      obtain ⟨Ys₀, hYs₀⟩ : ∃ Ys₀, readBytes A (b + 1) Ys.length = some Ys₀ := by
        rw [show readBytes A b (Ys.length + 1) = (match readByte A b with
          | none => none
          | some y₀ => match readBytes A (b + 1) Ys.length with
            | none => none
            | some bs => some (y₀ :: bs))
          from rfl, hy₀] at hY₀
        cases h : readBytes A (b + 1) Ys.length with
        | none => rw [h] at hY₀; cases hY₀
        | some Ys₀ => exact ⟨Ys₀, rfl⟩
      -- the single byte at `b` lifts past the whole of `X`
      have hlift : writeByte (writeBytes A a X) b y = writeBytes (writeByte A b y) a X := by
        refine writeByte_writeBytes_comm (m := A) (b := b) (y := y) a X hX ?_
        rcases hdisj with h | h
        · exact Or.inr h
        · exact Or.inl (by omega)
      -- the region's presence in the memory the byte write leaves: the write is on
      -- one side of it or the other
      have hX' : ∃ X₀, readBytes (writeByte A b y) a X.length = some X₀ := by
        obtain ⟨X₀, hX₀⟩ := hX
        refine ⟨X₀, ?_⟩
        rcases hdisj with h | h
        · rw [readBytes_writeByte_above A X.length a (by omega)]
          exact hX₀
        · rw [readBytes_writeByte_below A X.length a (by omega)]
          exact hX₀
      have hY' : ∃ Y₀, readBytes (writeByte A b y) (b + 1) Ys.length = some Y₀ :=
        ⟨Ys₀, by
          rw [readBytes_writeByte_below A Ys.length (b + 1) (by omega)]
          exact hYs₀⟩
      have hdisj' : a + X.length ≤ b + 1 ∨ (b + 1) + Ys.length ≤ a := by
        rcases hdisj with h | h
        · exact Or.inl (Nat.le_trans h (Nat.le_succ b))
        · refine Or.inr ?_
          have heq : b + (Ys.length + 1) = (b + 1) + Ys.length := by omega
          rwa [heq] at h
      show writeBytes (writeByte (writeBytes A a X) b y) (b + 1) Ys
        = writeBytes (writeBytes A b (y :: Ys)) a X
      rw [hlift]
      rw [show writeBytes (writeBytes A b (y :: Ys)) a X
        = writeBytes (writeBytes (writeByte A b y) (b + 1) Ys) a X from rfl]
      exact writeBytes_comm_of_present (writeByte A b y) a X (b + 1) Ys hX' hY' hdisj'

/-- Presence as an existential, from the `≠ none` form the section states. -/
theorem exists_readBytes_of_ne {A : Mem} {a n : Nat} (h : readBytes A a n ≠ none) :
    ∃ bs, readBytes A a n = some bs := by
  cases hb : readBytes A a n with
  | none => exact absurd hb h
  | some bs => exact ⟨bs, rfl⟩

/-- **The absorption**: an earlier write to a region, crossed by two writes disjoint
from it, is erased by a later write to that same region.  Three presences, and they
are exactly the regions the proof crosses; the crossing itself is two commutations
and then `writeBytes_writeBytes_same`, because the two writes to the erased region
end up adjacent. -/
theorem writeBytes_absorb_one (B : Mem) {ei dst xj : Nat} {X out Wj Z : List UInt8}
    (hei : readBytes B ei X.length ≠ none)
    (hdst : readBytes B dst out.length ≠ none)
    (hxj : readBytes B xj Wj.length ≠ none)
    (hlen : X.length ≤ Z.length)
    (hd_ei : ei + X.length ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + X.length ≤ xj ∨ xj + Wj.length ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + Wj.length ≤ dst) :
    writeBytes (writeBytes (writeBytes (writeBytes B ei X) dst out) xj Wj) ei Z
      = writeBytes (writeBytes (writeBytes B dst out) xj Wj) ei Z := by
  obtain ⟨X₀, hX₀⟩ := exists_readBytes_of_ne hei
  obtain ⟨O₀, hO₀⟩ := exists_readBytes_of_ne hdst
  obtain ⟨W₀, hW₀⟩ := exists_readBytes_of_ne hxj
  -- 1. the clear crosses `dst`
  rw [writeBytes_comm_of_present B ei X dst out ⟨X₀, hX₀⟩ ⟨O₀, hO₀⟩ hd_ei]
  -- 2. and then `xj`: the `ei` region is still present after `dst`'s write
  have hei' : readBytes (writeBytes B dst out) ei X.length ≠ none := by
    rcases hd_ei with h | h
    · rw [readBytes_writeBytes_below B out X.length ei dst h]
      exact hei
    · rw [s2StringBodyReadBytes_above B out X.length ei dst h]
      exact hei
  have hxj' : readBytes (writeBytes B dst out) xj Wj.length ≠ none := by
    rcases hd_xj with h | h
    · rw [s2StringBodyReadBytes_above B out Wj.length xj dst h]
      exact hxj
    · rw [readBytes_writeBytes_below B out Wj.length xj dst h]
      exact hxj
  obtain ⟨X₁, hX₁⟩ := exists_readBytes_of_ne hei'
  obtain ⟨W₁, hW₁⟩ := exists_readBytes_of_ne hxj'
  rw [writeBytes_comm_of_present (writeBytes B dst out) ei X xj Wj ⟨X₁, hX₁⟩ ⟨W₁, hW₁⟩ hx_ei]
  -- 3. the two writes to `ei` are adjacent, and the second one is the memory
  exact writeBytes_writeBytes_same (writeBytes (writeBytes B dst out) xj Wj) ei X Z hlen

/-- **A counter whose every position below it satisfies the predicate, and whose own
position does not (or is past the list), is the `takeWhile` length.**  Induction on
the counter, with the head peeled by `takeWhile_cons_of_pos`/`_of_neg`. -/
theorem takeWhile_length_of_counter {l : List Nat} {pos0 : Nat} :
    ∀ (n : Nat), (∀ k, k < n → ∃ q, l[k]? = some q ∧ q < pos0) →
      (l[n]? = none ∨ ∃ q, l[n]? = some q ∧ pos0 ≤ q) →
      (l.takeWhile (fun q => decide (q < pos0))).length = n
  | 0, _, hstop => by
      cases l with
      | nil => rfl
      | cons a t =>
          have hneg : ¬ decide (a < pos0) = true := by
            rcases hstop with h | ⟨q, hq, hle⟩
            · simp only [List.getElem?_cons_zero, Option.some_ne_none] at h
            · simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
              subst hq
              simp only [decide_eq_true_eq]
              omega
          rw [List.takeWhile_cons_of_neg (p := fun q => decide (q < pos0)) hneg]
          rfl
  | n + 1, hstep, hstop => by
      cases l with
      | nil =>
          obtain ⟨q, hq, _⟩ := hstep 0 (by omega)
          simp only [List.getElem?_nil] at hq
          cases hq
      | cons a t =>
          obtain ⟨q, hq, hlt⟩ := hstep 0 (by omega)
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          subst hq
          rw [List.takeWhile_cons_of_pos (p := fun q => decide (q < pos0))
            (by simpa using hlt)]
          simp only [List.length_cons]
          rw [takeWhile_length_of_counter n ?_ ?_]
          · intro k hk
            obtain ⟨q', hq', hlt'⟩ := hstep (k + 1) (by omega)
            exact ⟨q', by simpa using hq', hlt'⟩
          · rcases hstop with h | ⟨q', hq', hle⟩
            · exact Or.inl (by simpa using h)
            · exact Or.inr ⟨q', by simpa using hq', hle⟩

/-- **The scan's counter is the model's `j1`.**  From the invariant's counter `c`
at the exit — every position between `j0` and `c` below the body's first position,
and `c` itself past it or past the list — the model's
`j0 + ((ps.drop j0).takeWhile (fun q => decide (q < pos0))).length` is `c`. -/
theorem scanCounter_eq_takeWhile (ps : List Nat) (pos0 : Nat) (j0 c : Nat)
    (hjc : j0 ≤ c)
    (hstep : ∀ k, j0 ≤ k → k < c → ∃ q, ps[k]? = some q ∧ q < pos0)
    (hstop : ps[c]? = none ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) :
    c = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < pos0))).length := by
  have h := takeWhile_length_of_counter (l := ps.drop j0) (pos0 := pos0) (n := c - j0)
    (by
      intro k hk
      obtain ⟨q, hq, hlt⟩ := hstep (j0 + k) (by omega) (by omega)
      exact ⟨q, by rw [List.getElem?_drop]; simpa using hq, hlt⟩)
    (by
      rcases hstop with h' | ⟨q, hq, hle⟩
      · refine Or.inl ?_
        rw [List.getElem?_drop, Nat.add_sub_cancel' hjc]
        exact h'
      · exact Or.inr ⟨q, by
          rw [List.getElem?_drop, Nat.add_sub_cancel' hjc]
          exact hq, hle⟩)
  omega

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

/-- The scan's invariant at the head.  It carries what one iteration needs to run
and to be re-established: the state is at `land.rhs`; its cursor word holds the
counter and the counter plus the budget is the count; the predecessor names a
`phi` whose selected operand already reads the counter (so the `phi` and its edge
are part of the invariant, not of the arm's hypotheses); the four registers the
head reads are the model's arguments widened to `i64`; and the lane at the counter
is the model's `ps` entry there — its bytes and their value, together.  The lane
clause is what forces `c < N`, because `ps[c]?` has no entry at `c = N`.

`mem0` is the memory the scan started from and `xj` the cursor word's address: the
loop's only memory effect is that word's write, one per iteration. -/
def s2StringBodyScanInv (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "land.rhs" ∧ s.mem = writeBytes mem0 xj (wordBytes 8 c) ∧ c + r = N ∧
  (∃ p op, s.pre = some p ∧
    phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op ∧
    evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 c))) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%xj" = some (.ptr xj) ∧
  lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 N)) ∧
  (∃ q bs, ps[c]? = some q ∧ bs.length = 4 ∧ bytesToNat bs = q ∧
    readBytes s.mem (xp + 4 * c) 4 = some bs)

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

/-! ### The head's bits, from the head's test

The steps take the branch bits as hypotheses; the loop's arms must produce them,
and producing them is this section: the comparison's two outcomes as `BitVec 1`
values, the lane read's value as the model's `ps` entry, and then the head's test
in both of its forms.  Nothing here is about a state's history — the bits are
functions of the counter, the lane and the two bounds — which is why the arms can
be proved once rather than at each iteration. -/

/-- Sign-extending an `i64` value to `i64` is the value. -/
theorem signExtend_ofNat (c : Nat) (hc : c < 2 ^ 64) :
    ((BitVec.ofNat 64 c).signExtend 64).toNat = c := by
  rw [BitVec.toNat_signExtend]
  have hset : (BitVec.setWidth 64 (BitVec.ofNat 64 c)).toNat = c := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hc]
  rw [hset]
  split <;> omega

/-- The counter's increment at the model's width. -/
theorem ofNat_add_one (c : Nat) :
    (BitVec.ofNat 64 c) + 1#64 = BitVec.ofNat 64 (c + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The unsigned-greater test is `1` exactly when the second operand is below the
first, both below `2 ^ 64` (the width the model reads them at). -/
theorem evalICmpNat_ugt_one {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : y < x) : evalICmpNat .ugt 64 x y = 1#1 := by
  simp only [evalICmpNat, evalICmp, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, h, BitVec.ofBool]
  rfl

/-- The same test as `0` when the first operand is at or below the second. -/
theorem evalICmpNat_ugt_zero {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : x ≤ y) : evalICmpNat .ugt 64 x y = 0#1 := by
  have hlt : ¬ y < x := by omega
  simp only [evalICmpNat, evalICmp, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, hlt, BitVec.ofBool]
  rfl

/-- Equality as a one-bit value. -/
theorem evalICmp_eq_one {x y : BitVec 64} (h : x = y) : evalICmp .eq x y = 1#1 := by
  subst h
  simp only [evalICmp, BitVec.ofBool]
  rfl

/-- Inequality as a one-bit value. -/
theorem evalICmp_eq_zero {x y : BitVec 64} (h : x ≠ y) : evalICmp .eq x y = 0#1 := by
  simp only [evalICmp, BitVec.ofBool, h]
  rfl

/-- A four-byte lane is below `2 ^ 32`, so a lane's value is its own widening to
`i64`. -/
theorem bytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have := bytesToNat_lt bs
  rw [h] at this
  calc bytesToNat bs < 256 ^ 4 := this
    _ = 2 ^ 32 := by decide

/-- **The lane the model names.**  A successful lane read gives, at every index
inside it, the list's entry there and the four bytes it was read from — with the
entry being exactly the bytes' value.  This is what lets the head's read at
`xp + c * 4` be the model's `ps[c]`. -/
theorem readLanes32_lane {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧
          bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := readLanes32_lane (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

/-- The head's test, in its false form: the scan has not reached the count and the
lane at the counter is below the body's first position. -/
theorem s2StringBodyScanAtBound_false (ps : List Nat) (pos0 N : Nat) (s : State)
    (c : Nat) :
    s2StringBodyScanAtBound ps pos0 N s c = false ↔
      ¬ (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) := by
  by_cases h : s2StringBodyScanAtBound ps pos0 N s c = true
  · have hp : N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q :=
      (s2StringBodyScanAtBound_eq ps pos0 N s c).mp h
    exact ⟨fun hf => absurd (hf.symm.trans h) (by decide), fun hn => absurd hp hn⟩
  · have hf : s2StringBodyScanAtBound ps pos0 N s c = false := by
      cases hb : s2StringBodyScanAtBound ps pos0 N s c with
      | false => rfl
      | true => exact absurd hb h
    exact ⟨fun _ hp => h ((s2StringBodyScanAtBound_eq ps pos0 N s c).mpr hp),
      fun _ => hf⟩

/-- The head's lane test when the lane is already inside the body: `0`, so the scan
leaves at the head in one step (`s2StringBodyScanExit`'s bit). -/
theorem evalICmpNat_ugt_of_ge {pos0 q : Nat} (hpos0 : pos0 < 2 ^ 64)
    (hq64 : q < 2 ^ 64) (hge : pos0 ≤ q) :
    evalICmpNat .ugt 64 pos0 q = 0#1 :=
  evalICmpNat_ugt_zero hpos0 hq64 hge

/-- The exit test when the counter has reached the count: `1`, so `while.body`
leaves for `if.then` (`s2StringBodyScanIterate`'s second bit in its exit form). -/
theorem evalICmp_eq_of_eq {c N : Nat} (hN : N < 2 ^ 64) (heq : N = c + 1) :
    evalICmp .eq ((BitVec.ofNat 64 c) + 1#64) (BitVec.ofNat 64 N) = 1#1 := by
  have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hbit : (BitVec.ofNat 64 c) + 1#64 = BitVec.ofNat 64 N := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, heq]
  exact evalICmp_eq_one hbit

/-- **The head's two bits, from the head's test being false**: the lane is the
model's `ps` entry at the counter, `sub` is the body's first position, and the
counter is the index — under which the lane test holds (the scan advances) and the
exit test does not (the counter has not reached the count).  These are exactly the
two hypotheses `s2StringBodyScanIterate` consumes. -/
theorem s2StringBodyScan_bits_of_not_atBound
    {ps : List Nat} {pos0 N c q : Nat} {bs : List UInt8} {s : State}
    {sub inc24 nxp : BitVec 64}
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = false)
    (hq : ps[c]? = some q) (hval : bytesToNat bs = q) (hblen : bs.length = 4)
    (hsub : sub = BitVec.ofNat 64 pos0) (hpos0 : pos0 < 2 ^ 64)
    (hinc24 : inc24 = BitVec.ofNat 64 c) (hnxp : nxp = BitVec.ofNat 64 N)
    (hN : N < 2 ^ 64) :
    evalICmpNat .ugt 64 sub.toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1 ∧
      evalICmp .eq (inc24 + 1#64) nxp = 0#1 := by
  rw [s2StringBodyScanAtBound_false] at hbound
  have hnot : ¬ (N ≤ c + 1 ∨ ∃ q', ps[c]? = some q' ∧ pos0 ≤ q') := hbound
  have hlt : c + 1 < N := by
    by_contra h; exact hnot (Or.inl (by omega))
  have hqlt : q < pos0 := by
    by_contra h; exact hnot (Or.inr ⟨q, hq, by omega⟩)
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = q := by
    have h32 := bytesToNat_lt_32 hblen
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega), hval]
  constructor
  · rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
    exact evalICmpNat_ugt_one hpos0 (by have := bytesToNat_lt_32 hblen; omega) hqlt
  · have hne : (BitVec.ofNat 64 c) + 1#64 ≠ BitVec.ofNat 64 N := by
      intro heq
      have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      have := congrArg BitVec.toNat heq
      rw [htoNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at this
      omega
    rw [hinc24, hnxp]
    exact evalICmp_eq_zero hne

/-- **The invariant's entry**: the head carrying the entry's counter `j0`, with the
count as the whole budget.  The clauses are the staging's facts read at the head —
the predecessor (`entry`, through the `phi`), the four registers, and the lane at
`j0` — which is why this is the only place the pre's content is consumed. -/
theorem s2StringBodyScanInv_entry (mem0 : Mem) (xj pos0 xp N j0 : Nat)
    (ps : List Nat) (s : State)
    (hpc : s.pc = "land.rhs") (hmem : s.mem = writeBytes mem0 xj (wordBytes 8 j0))
    (hj0 : j0 ≤ N)
    (hphi : ∃ p op, s.pre = some p ∧
      phiIncoming p [("while.body", Operand.reg "%inc"),
        ("entry", Operand.reg "%xj.promoted")] = some op ∧
      evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 j0)))
    (hxp : lookupName s.env "%xp" = some (.ptr xp))
    (hsub : lookupName s.env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hxj : lookupName s.env "%xj" = some (.ptr xj))
    (hnxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 N)))
    (hlane : ∃ q bs, ps[j0]? = some q ∧ bs.length = 4 ∧ bytesToNat bs = q ∧
      readBytes s.mem (xp + 4 * j0) 4 = some bs) :
    s2StringBodyScanInv mem0 xj pos0 xp N ps (N - j0) s j0 :=
  ⟨hpc, hmem, by omega, hphi, hxp, hsub, hxj, hnxp, hlane⟩

/-- **The scan is a `BoundLoop`.**  The bound, the head's test, the invariant and
the budget are fixed here; the two arms are the body's — the exit step and one
iteration's return to the head — stated as the shape's per-iteration facts, as the
decoder's and the copy loops' instances state theirs.  The two exits share one
induction: `Exit` is the disjunction of the blocks they leave for. -/
def s2StringBodyScanBoundLoop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e) :
    BoundLoop s2StringBodyCalls s2StringBodyBody where
  head := "land.rhs"
  exitBlock := "land.lhs.true"
  N := N
  cost := cost
  Inv := s2StringBodyScanInv mem0 xj pos0 xp N ps
  atBound := s2StringBodyScanAtBound ps pos0 N
  Exit := Exit
  ExitWord := ExitWord
  step_exit := fun r s c => step_exit r c s
  step_loop := fun r s c => step_loop r c s
  exit_at_zero := by
    intro s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    rw [s2StringBodyScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    omega

/-- **The scan's fuel is a term of the arguments.**  With the body's two arms, the
head reaches an exit within `(N + 1) * cost` control steps, and a completed exit
continuation lifts to the whole loop.  The induction is `BoundLoop.run_at`'s;
nothing here is specific to the scan beyond its invariant. -/
theorem s2StringBodyScan_run_at (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (s : State) (c : Nat) (k : Nat) (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps N s c)
    {o : Outcome}
    (hcont : ∀ (e : State), Exit e → ExitWord e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * cost + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanBoundLoop mem0 xj pos0 xp N ps cost Exit ExitWord step_exit
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

/-- **The scan's back edge.**  One iteration is two control steps (`cost = 2`):
the head's step advances, `while.body` writes the counter and returns to the head.
Every clause of the invariant is re-established — the `phi`'s edge is `while.body`
and its operand `%inc` now reads `c + 1`, the four registers are still the outer
cells, the cursor word is the new counter (`s2StringBodyScan_advance`, which is
where the write order matters), and the lane at `c + 1` is the model's entry there
(`readLanes32_lane`), read past the cursor's write by the region's disjointness. -/
theorem s2StringBodyScan_step_loop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = "land.rhs" ∧ c < c' ∧
      s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hb : s2StringBodyScanAtBound ps pos0 N s c = false := hbound
  rw [s2StringBodyScanAtBound_false] at hbound
  have hcN : c + 1 < N := by
    by_contra h; exact hbound (Or.inl (by omega))
  have hc : c < N := by omega
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  obtain ⟨hbit1, hbit2⟩ :=
    s2StringBodyScan_bits_of_not_atBound hb hq hval hblen rfl hpos0 rfl rfl hN64
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]
    omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]
    exact hlane
  have hrun := s2StringBodyScanIterate (envH := s.env) (s := s) (p := p) (op := op)
    hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
  obtain ⟨laneQ, laneBs, hq', hlaneM, hval'⟩ :=
    (readLanes32_lane hps).2 (c + 1) hcN
  have hblen' : laneBs.length = 4 := readBytes_length_some hlaneM
  have hframe : readBytes (writeBytes mem0 xj (wordBytes 8 (c + 1))) (xp + 4 * (c + 1)) 4
      = some laneBs := by
    rcases hdisj (c + 1) hcN with h | h
    · rw [readBytes_writeBytes_below mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by omega)]
      exact hlaneM
    · rw [s2StringBodyReadBytes_above mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by simp [wordBytes, natToBytes_length]; omega)]
      exact hlaneM
  let e : State := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
          (BitVec.ofNat 64 N))) ::
        ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
        s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
      ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })
  refine ⟨e, c + 1, 2, le_rfl, rfl, by omega, ?_, ?_⟩
  · refine ⟨rfl, ?_, by omega,
      ⟨"while.body", Operand.reg "%inc", rfl, by simp [phiIncoming], ?_⟩,
      ?_, ?_, ?_, ?_, ⟨laneQ, laneBs, hq', hblen', hval', ?_⟩⟩
    · exact s2StringBodyScan_advance mem0 xj c s hmem (by omega)
    · simp [e, stateAt, evalOperand, lookupName, s2StringBodyLandRhsEnv, ofNat_add_one]
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxp
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hsub
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxj
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hnxp
    · simp only [e]
      rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
          = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
        s2StringBodyScan_advance mem0 xj c s hmem (by omega)]
      exact hframe
  · exact hrun


/-- **The scan's iteration, leaving.**  The same two control steps as
`s2StringBodyScanIterate`, but the counter has reached the count, so `while.body`'s
test holds and the scan leaves for `if.then`. -/
theorem s2StringBodyScanIterateExit {envH : Env} {s : State} {p : String} {op : Operand}
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
    (hbit2 : evalICmp .eq (inc24 + 1#64) nxp = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) ::
            s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })) := by
  intro k
  have h1 := step_landRhs_while (env := envH) (s := s) (p := p) (op := op)
    hpc hpre hinc hop hxp hsub hpos hlane hbit1
  have h2 := step_whileBody_exit
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
            ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })) :=
        runFuel_jump_prefix h2 k

/-- The blocks the scan may leave for. -/
def s2StringBodyScanExited (e : State) : Prop :=
  e.pc = "land.lhs.true" ∨ e.pc = "if.then"

/-- What the scan leaves behind: the cursor word at the counter it stopped at, and
that counter being the count or the first lane inside the body. -/
def s2StringBodyScanExitWord (mem0 : Mem) (xj : Nat) (ps : List Nat) (pos0 N : Nat)
    (e : State) : Prop :=
  ∃ c, e.mem = writeBytes mem0 xj (wordBytes 8 c) ∧
    (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q)

theorem s2StringBodyScan_step_exit (mem0 : Mem) (xj pos0 xp N : Nat)
    (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps r s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧ s2StringBodyScanExited e ∧
      s2StringBodyScanExitWord mem0 xj ps pos0 N e ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hcN : c < N := by
    have : c < ps.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hq
      cases hq
    omega
  have hb : s2StringBodyScanAtBound ps pos0 N s c = true := hbound
  rw [s2StringBodyScanAtBound_eq] at hbound
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]; exact hlane
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = q := by
    have h32 := bytesToNat_lt_32 hblen
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega), hval]
  by_cases hge : pos0 ≤ q
  · -- the lane is already inside the body: the head's exit, one step
    have hbit : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_of_ge hpos0 (by have := bytesToNat_lt_32 hblen; omega) hge
    have hrun := s2StringBodyScanExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hinc hop hxp hsub hpos hlane' hbit
    let e : State := stateAt (s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0)) { s with pc := "land.lhs.true", pre := some s.pc }
    refine ⟨e, 1, by decide, Or.inl rfl, ?_, hrun⟩
    exact ⟨c, by simp only [e, stateAt]; exact hmem, Or.inr ⟨q, hq, hge⟩⟩
  · -- the lane is below the body's start, so only the count can have stopped it
    have hlt : q < pos0 := by omega
    have hNle : N ≤ c + 1 := by
      rcases hbound with h | ⟨q', hq', hge'⟩
      · exact h
      · rw [hq] at hq'; cases Option.some.inj hq'; exact absurd hge' hge
    have heqc : c + 1 = N := by omega
    have hbit1 : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_one hpos0 (by have := bytesToNat_lt_32 hblen; omega) hlt
    have hbit2 : evalICmp .eq ((BitVec.ofNat 64 c) + 1#64) (BitVec.ofNat 64 N) = 1#1 :=
      evalICmp_eq_of_eq hN64 heqc.symm
    have hrun := s2StringBodyScanIterateExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
    let e : State := stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
            (BitVec.ofNat 64 N))) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
          s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
        ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })
    refine ⟨e, 2, le_rfl, Or.inr rfl, ?_, hrun⟩
    refine ⟨c + 1, ?_, Or.inl (by omega)⟩
    simp only [e, stateAt]
    rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
        = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
      s2StringBodyScan_advance mem0 xj c s hmem (by omega)]


/-- **The scan, as a `BoundLoop`.**  The two arms are proved, so the value carries no
hypothesis beyond the staging's: the lane list, the region disjointness the frame
needs, and the two bounds.  The exits are `land.lhs.true` and `if.then`, and the
exit word is the cursor at the counter the scan stopped at. -/
def s2StringBodyScanLoop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64) :
    BoundLoop s2StringBodyCalls s2StringBodyBody :=
  s2StringBodyScanBoundLoop mem0 xj pos0 xp N ps 2
    s2StringBodyScanExited (s2StringBodyScanExitWord mem0 xj ps pos0 N)
    (s2StringBodyScan_step_exit mem0 xj pos0 xp N ps hps hdisj hN hpos0)
    (s2StringBodyScan_step_loop mem0 xj pos0 xp N ps hps hdisj hN hpos0)

/-- **The scan's fuel, read off its instance**: `(N + 1) * 2` control steps from the
head, and the exit's continuation at its own fuel. -/
theorem s2StringBodyScan_run (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (s : State) (c : Nat) (k : Nat)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps N s c) {o : Outcome}
    (hcont : ∀ (e : State), s2StringBodyScanExited e →
      s2StringBodyScanExitWord mem0 xj ps pos0 N e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * 2 + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanLoop mem0 xj pos0 xp N ps hps hdisj hN hpos0).run_at s c hinv k hcont


/-! ### The entry's prefix

The body's run starts here: the entry block's step, stated as the `runFuel` prefix
the closing composes with (`s2StringBodyScan_run` for the scan, and the exit
continuations for the rest).  The *seating* — reading `s2StringBodyScanInv` off the
staging at the head the entry leaves — is not stated here, and its first clause is
why: the invariant wants `s.mem = writeBytes s.mem xj (wordBytes 8 j0)`, which is
the self-write form of a region already present.  That is the presence clause
`s2StringBodyPre` still owes (obligation 3), so the seating belongs with it rather
than ahead of it. -/

/-- `ofNat` at `i64` is a homomorphism for subtraction when the operands do not
borrow: `(p - base)` as the model's `Nat` is the bit-vector difference. -/
theorem ofNat_sub (p base : Nat) (hb : base ≤ p) (hp : p < 2 ^ 64) :
    (BitVec.ofNat 64 p) - (BitVec.ofNat 64 base) = BitVec.ofNat 64 (p - base) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **The entry's step to the scan's head, as a prefix**: one control step, and the
run continues from the head at `land.rhs`. -/
theorem s2StringBodyEntry_prefix_landRhs {env : Env} {s : State}
    {c p xj base j0 : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_landRhs hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit) k

/-- **The entry's step to the body-itself arm, as a prefix.** -/
theorem s2StringBodyEntry_prefix_ifThen {env : Env} {s : State}
    {c p xj base j0 : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_ifThen hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit) k



/-- **Seating the scan's invariant at the head the entry left.**  Every clause is
read off the staging: the entry writes nothing, so its memory is the caller's and
the cursor word's presence (`stage2ReadWord_writeBytes_self`) is the invariant's
memory clause; the `phi`'s edge is `entry` selecting `%xj.promoted`, which the entry
has just bound to `j0`; `%xp`, `%xj` and `%nxp` are the caller's registers, falling
through the entry's seven cells; `%sub.ptr.sub` is `p - base` (`ofNat_sub`); and the
lane at `j0` is the model's, because the head's memory is the caller's. -/
theorem s2StringBodyScanInv_seat (env : Env) (s : State) (base p xj xp j0 : Nat)
    (ps : List Nat) (nxp : BitVec 64)
    (hpc : s.pc = "entry")
    (hbase : base ≤ p) (hp64 : p < 2 ^ 64)
    (hword : stage2ReadWord s.mem xj 8 = some j0)
    (hps : readLanes32 s.mem xp nxp.toNat = some ps)
    (hj0 : j0 < nxp.toNat)
    (hxpc : lookupName env "%xp" = some (.ptr xp))
    (hxjc : lookupName env "%xj" = some (.ptr xj))
    (hnxpc : lookupName env "%nxp" = some (.int 64 nxp)) :
    s2StringBodyScanInv s.mem xj (p - base) xp nxp.toNat ps (nxp.toNat - j0)
      (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc })
      j0 := by
  obtain ⟨q, bs, hq, hlaneM, hval⟩ := (readLanes32_lane hps).2 j0 hj0
  have hblen : bs.length = 4 := readBytes_length_some hlaneM
  have hpres := stage2ReadWord_writeBytes_self s.mem xj 8 j0 hword
  have hnxp : BitVec.ofNat 64 nxp.toNat = nxp := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nxp.isLt]
  refine ⟨rfl, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ⟨q, bs, hq, hblen, hval, ?_⟩⟩
  · simpa only [stateAt] using hpres.symm
  · refine ⟨"entry", Operand.reg "%xj.promoted", ?_, by simp [phiIncoming], ?_⟩
    · simp only [stateAt, hpc]
    · simp [stateAt, evalOperand, lookupName, s2StringBodyEntryOut,
        s2StringBodyEnv7, s2StringBodyEnv6]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxpc]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, ofNat_sub p base hbase hp64]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxjc]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hnxp, hnxpc]
  · simp only [stateAt]
    exact hlaneM


/-! ### The end of the run

Two blocks finish the body — `cleanup16` returns the form, and `if.then` writes the
extent's word before it — and both are `ret`s rather than jumps, so the run ends at
them (`runFuel` maps a `ret` step to the outcome, dropping the state).  These are
the continuations' last link: every path reaches `cleanup16` at some form, and the
form is the `phi`'s answer from whichever cleanup block preceded it. -/

/-- A `ret` step completes the run: the outcome carries the returned word and the
memory the block left. -/
theorem runFuel_ret_mem {calls : Calls} {f : Function} {s s' : State} {v : Value}
    (h : step calls f s = .ret (some v) s') (k : Nat) :
    runFuel calls (1 + k) f s = some (.ret (some v) s'.mem) := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-- **`cleanup16` finishes the body**: the returned form's `phi` and the function's
answer at that word, one control step. -/
theorem s2StringBodyCleanup16_finishes {env : Env} {s : State} {p : String}
    {op : Operand} {form : BitVec 32}
    (hpc : s.pc = "cleanup16") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form)) :
    runFuel s2StringBodyCalls 1 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 form))
        (stateAt (("%retval.1", .int 32 form) :: env) s).mem) :=
  runFuel_ret_mem (step_cleanup16_ret hpc hpre hinc hop) 0

/-- **The body-itself arm's end**: `if.then` writes the extent's word at `outn`,
`cleanup16` returns `1`, and the run is over in two control steps. -/
theorem s2StringBodyIfThen_finishes {env : Env} {s : State} {len : BitVec 64}
    {outn : Nat}
    (hpc : s.pc = "if.then")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have h1 := step_ifThen_cleanup16 hpc hlen houtn
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) =
      .ret (some (.int 32 0x00000001#32))
        (stateAt (("%retval.1", .int 32 0x00000001#32) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) := by
    refine step_cleanup16_ret (p := "if.then")
      (op := .imm (Const.int 32 0x00000001#32)) rfl ?_ ?_ rfl
    · rw [hpc]
    · simp [phiIncoming]
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hcont : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (stateAt (("%retval.1", .int 32 0x00000001#32) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }).mem) :=
    runFuel_ret_mem h2 0
  simpa only [stateAt] using runFuel_prefix_some hpre hcont


/-- **`cleanup` finishes, having come from the refusal**: its `phi` selects `0`,
`cleanup16` returns `%retval.0`, and the run is over in two control steps. -/
theorem s2StringBodyCleanup_fromRefused_finishes {env : Env} {s : State} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some "if.then11")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32)) s.mem) := by
  have hstep : step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      .jump (stateAt (("%retval.0", .int 32 0x00000000#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) :=
    step_cleanup_cleanup16 (env := env) (s := s) (p := "if.then11")
      (op := .imm (Const.int 32 0x00000000#32)) hpc hpre (by simp [phiIncoming]) rfl hei
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (("%retval.0", .int 32 0x00000000#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32)) s.mem) := by
    have h := s2StringBodyCleanup16_finishes (env := ("%retval.0", .int 32 0x00000000#32) :: env)
      (s := { s with pc := "cleanup16", pre := some s.pc }) (p := "cleanup")
      (op := .reg "%retval.0") (form := 0x00000000#32) rfl (by rw [hpc])
      (by simp [phiIncoming]) (by s2_lk)
    simpa only [stateAt] using h
  exact runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin

/-- **`cleanup` finishes, having come from the decoded arm**: its `phi` selects `2`. -/
theorem s2StringBodyCleanup_fromDecoded_finishes {env : Env} {s : State} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some "if.end14")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32)) s.mem) := by
  have hstep : step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      .jump (stateAt (("%retval.0", .int 32 0x00000002#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) :=
    step_cleanup_cleanup16 (env := env) (s := s) (p := "if.end14")
      (op := .imm (Const.int 32 0x00000002#32)) hpc hpre (by simp [phiIncoming]) rfl hei
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (("%retval.0", .int 32 0x00000002#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32)) s.mem) := by
    have h := s2StringBodyCleanup16_finishes (env := ("%retval.0", .int 32 0x00000002#32) :: env)
      (s := { s with pc := "cleanup16", pre := some s.pc }) (p := "cleanup")
      (op := .reg "%retval.0") (form := 0x00000002#32) rfl (by rw [hpc])
      (by simp [phiIncoming]) (by s2_lk)
    simpa only [stateAt] using h
  exact runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin


/-- **The decoded length's path finishes**: the word at `outn`, `cleanup`'s decoded
form, and the run is over in three control steps. -/
theorem s2StringBodyIfEnd14_finishes {env : Env} {s : State} {call : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.end14")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) := by
  have hstep := step_ifEnd14_cleanup hpc hcall houtn
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) :=
    s2StringBodyCleanup_fromDecoded_finishes (env := env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc })
      rfl (by rw [hpc]) hei
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this

/-- **The inside test finishing at the body-itself arm**: one step to `if.then`,
then the arm's two — three control steps, form `1`. -/
theorem s2StringBodyLandLhsTrue_toIfThen_finishes {env : Env} {s : State}
    {sub len conv : BitVec 64} {outn : Nat}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have hstep := step_landLhsTrue_ifThen hpc hsub hlen hconv hbit
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyIfThen_finishes (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.then", pre := some s.pc }) rfl (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this


/-- The refusal record's output state, named: the record's three fields written over
the caller's memory, at `cleanup`.  Rule four's failure mode is why this exists:
stated inline, the nine-cell environment is a `whnf` liability the elaborator pays
at every unification, and the proof dies in `whnf` — *not* in logic — at the
default budget and again at a million heartbeats.  Naming the state is necessary
but was measured **not** sufficient for the refusal path: the cost that remains is
the instantiation of a completion lemma at this environment, so a path stated here
still wants its completion proved over a state variable (no `s2StringBodyIfThen11Mem`
in the type) rather than at this term. -/
def s2StringBodyIfThen11Out (env : Env) (s : State) (off sub : BitVec 64) (c e : Nat) :
    State :=
  stateAt (s2StringBodyIfThen11Env env off sub c e)
    { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc }

set_option maxHeartbeats 4000000 in
/-- **The refusal record's path finishes**, with the record's facts and the slot
lookup supplied by the caller: the heavy environment appears once, in the
composition's state, and the completion is the generic one.

**The budget is scoped to this theorem, and it is a cost exception, not a proof
trick.**  The composition's elaboration exceeds the default 200 000 heartbeats —
measured again after naming the state and after taking the slot lookup from the
caller, so neither of those is the cause — and completes at 4 000 000 in about a
minute.  The cause is inherent to a nine-cell record state crossing a lemma whose
conclusion mentions the state's memory; the general fix is a completion whose
outcome carries the memory as a *variable*, which is a change to the closing's
shape rather than to this path. -/
theorem s2StringBodyIfThen11_finishes {env : Env} {s : State} {c ei e : Nat}
    {off sub : BitVec 64}
    (hpc : s.pc = "if.then11")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64)
    (hslot : lookupName (s2StringBodyIfThen11Env env off sub c e) "%ei"
      = some (.ptr ei)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem s.mem e off sub)) := by
  have hstep := step_ifThen11_cleanup hpc hc hei hsub hoff hcval he64
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (s2StringBodyIfThen11Env env off sub c e)
        { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem s.mem e off sub)) :=
    s2StringBodyCleanup_fromRefused_finishes
      (env := s2StringBodyIfThen11Env env off sub c e)
      (s := { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc })
      rfl (by rw [hpc]) hslot
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this


/-- **The inside test's refusal path, end to end**: `land.lhs.true`, `if.end`, the
record's three fields, `cleanup`'s refusal form — five control steps, answer `0`.

Stated as one theorem because its terminal state spells the caller's values (the
callee's memory `extra` and cursor `nx`, its returned word `call`, and the record's
`c`, `ei`, `e`, `off`): the prefix split works only where a terminal's input state
is describable by the prefix's own hypotheses, and here it is not.  It needs **no
budget** — a lemma's proof is not re-elaborated at its call site — which is the
composition-side half of the cost model: the price is paid where the terminal is
proved, not where it is used. -/
theorem s2StringBodyLandLhsTrue_refused_finishes {env : Env} {s : State}
    {sub len conv off : BitVec 64} {p dst ei xp xj c e : Nat} {nxp : BitVec 64}
    {extra : Mem} {nx : Nat} {call : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hc : lookupName env "%c" = some (.ptr c))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName env "%p" = some (.ptr p))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 1#1)
    (hoff : readBytes extra ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes extra (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem extra e off sub)) := by
  have h1 := step_landLhsTrue_ifEnd hpc hsub hlen hconv hbit7
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) =
      .jump (stateAt (s2StringBodyIfEndEnv
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env) call)
        { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" }) := by
    refine step_ifEnd_ifThen11 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit9
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfThen11_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" })
    (c := c) (ei := ei) (e := e) (off := off) (sub := sub)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) (by simpa only [stateAt] using hoff)
    (by simpa only [stateAt] using hcval) he64 (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this


/-- **The inside test's decoded path, end to end**: `land.lhs.true`, `if.end`, the
decoded length's word at `outn` — five control steps, answer `2`.  The terminal
spells no caller value, so this composition is the cheapest of the four. -/
theorem s2StringBodyLandLhsTrue_decoded_finishes {env : Env} {s : State}
    {sub len conv : BitVec 64} {p dst ei outn xp xj : Nat} {nxp : BitVec 64}
    {extra : Mem} {nx : Nat} {call : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName env "%p" = some (.ptr p))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes extra outn (natToBytes call.toNat 8))) := by
  have h1 := step_landLhsTrue_ifEnd hpc hsub hlen hconv hbit7
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) =
      .jump (stateAt (s2StringBodyIfEndEnv
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env) call)
        { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" }) := by
    refine step_ifEnd_ifEnd14 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit9
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfEnd14_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" })
    (call := call) (outn := outn)
    rfl (by s2_lk) (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this


/-! ### The split on `Exited`

The scan leaves either at `if.then` (its second exit) or at `land.lhs.true` (its
first), and the second's two branches are the lane test's bit.  Each wrapper below
reads the composed path at the exit state the scan's instance returns, so `hcont`
in `s2StringBodyScan_run` is one `rcases` away:

* `if.then` — the body-itself arm, answer `1`;
* `land.lhs.true` with the inside test false — the body-itself arm through
  `if.then`, answer `1`;
* `land.lhs.true` with the inside test true and the expander's answer all-ones —
  the refusal, answer `0`;
* `land.lhs.true` with the inside test true and any other answer — the decoded
  length, answer `2`.

`ExitWord` is not consumed here: the outcome's memory is the exit state's own, and
the counter's `∃ c` is what the closing uses to name that memory as the model's. -/

/-- The second exit finishes the body-itself arm. -/
theorem s2StringBodyExit_ifThen {e : State} {len : BitVec 64} {outn : Nat}
    (hpc : e.pc = "if.then")
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes e.mem outn (natToBytes len.toNat 8))) :=
  s2StringBodyIfThen_finishes (env := e.env) (s := e) hpc hlen houtn

/-- The first exit, the lane inside the body: the body-itself arm through
`if.then`. -/
theorem s2StringBodyExit_landLhsTrue_toIfThen {e : State} {sub len conv : BitVec 64}
    {outn : Nat}
    (hpc : e.pc = "land.lhs.true")
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1)
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes e.mem outn (natToBytes len.toNat 8))) :=
  s2StringBodyLandLhsTrue_toIfThen_finishes (env := e.env) (s := e)
    hpc hsub hlen hconv hbit houtn

/-- The first exit, the expander refusing: the record's path, answer `0`. -/
theorem s2StringBodyExit_refused {e : State} {sub len conv off : BitVec 64}
    {p dst ei xp xj c j : Nat} {nxp : BitVec 64} {extra : Mem} {nx : Nat}
    {call : BitVec 64}
    (hpc : e.pc = "land.lhs.true")
    (hc : lookupName e.env "%c" = some (.ptr c))
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName e.env "%p" = some (.ptr p))
    (hdst : lookupName e.env "%dst" = some (.ptr dst))
    (hei : lookupName e.env "%ei" = some (.ptr ei))
    (hxp : lookupName e.env "%xp" = some (.ptr xp))
    (hxj : lookupName e.env "%xj" = some (.ptr xj))
    (hnxp : lookupName e.env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 1#1)
    (hoff : readBytes extra ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes extra (c + (1112#64).toNat) 8 = some (wordBytes 8 j))
    (hj64 : j < 2 ^ 64) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem extra j off sub)) :=
  s2StringBodyLandLhsTrue_refused_finishes (env := e.env) (s := e)
    hpc hc hsub hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp hbit9 hoff hcval hj64

/-- The first exit, the expander decoding: the decoded length's word, answer `2`. -/
theorem s2StringBodyExit_decoded {e : State} {sub len conv : BitVec 64}
    {p dst ei outn xp xj : Nat} {nxp : BitVec 64} {extra : Mem} {nx : Nat}
    {call : BitVec 64}
    (hpc : e.pc = "land.lhs.true")
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName e.env "%p" = some (.ptr p))
    (hdst : lookupName e.env "%dst" = some (.ptr dst))
    (hei : lookupName e.env "%ei" = some (.ptr ei))
    (hxp : lookupName e.env "%xp" = some (.ptr xp))
    (hxj : lookupName e.env "%xj" = some (.ptr xj))
    (hnxp : lookupName e.env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes extra outn (natToBytes call.toNat 8))) :=
  s2StringBodyLandLhsTrue_decoded_finishes (env := e.env) (s := e)
    hpc hsub hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp hbit9 houtn


/-! ### The memory term

The post's memory is `r.mem = writeBytes m next slot`, with `m` the model's memory and
`slot` the bytes at the body's own `alloca`.  Reading it per arm shows the three
cases are not alike at all:

* **the body-itself arm writes no slot** — the model's `slot` is `[]` there, so
  `writeBytes m next [] = m` and the term is the identity on the model's memory;
* **the body-itself arm's memory is the model's by definition** — the arm writes
  `natToBytes len 8` at `outn` and the model writes `wordBytes 8 len`, and
  `wordBytes` *is* `natToBytes`, so the two memories are the same term;
* **the two callee arms are not** — the callee writes `dst`, `xj` and the slot `ei`
  in its own order, the model writes `dst`/`xj`/`outn` over `mem` and then the slot
  at `next`; joining those is where the write-order primitives are spent
  (`writeBytes_writeBytes_same` for a region written twice,
  `writeBytes_of_readBytes_self` for one already present), and it is the last
  substantial obligation of the row.

So this section states the two facts that make the first two bullets true and names
the third's shape.  Neither is a `rfl`-convenience: the first says the model's slot
parameter must be a *variable* (it is `[]` on one arm and eight bytes on the others,
and a consumer reading `writeBytes m next slot` must not assume it is populated), and
the second says the arm's memory needs no rewriting at all. -/

/-- The body-itself arm writes no slot: the model's slot is empty, so its slot write
is the identity on the memory.  This is why `slot` has to be a parameter of the
memory term and not a fixed eight-byte region. -/
theorem s2StringBodySlot_of_bodyItself (m : Mem) (next : Nat) :
    writeBytes m next ([] : List UInt8) = m := rfl

/-- The body-itself arm's memory **is** the model's, as one term: the arm writes the
extent's bytes at `outn` and the model writes `wordBytes 8 len`, which is those
bytes. -/
theorem s2StringBodyMemory_of_bodyItself (mem : Mem) (xj outn j1 len : Nat) :
    writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn (natToBytes len 8) =
      writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn (wordBytes 8 len) := rfl

/-- **The decoded arm's memory join**: the body's memory is the model's plus the slot
at the call's allocator.  Two moves — the arm's clear is absorbed, then the slot's
write crosses `outn`'s — each spending the presence and disjointness of the region it
crosses. -/
theorem s2StringBodyMemory_decoded (mem : Mem) {ei dst xj outn j1 k : Nat}
    {out : List UInt8}
    (hei : readBytes mem ei 8 ≠ none)
    (hdst : readBytes mem dst out.length ≠ none)
    (hxj : readBytes mem xj 8 ≠ none)
    (houtn : readBytes mem outn 8 ≠ none)
    (hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst)
    (ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei)
    (ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn)
    (ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn) :
    writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst out)
            xj (wordBytes 8 (j1 + k)))
          ei (wordBytes 8 out.length))
        outn (natToBytes out.length 8)
      = writeBytes
          (writeBytes
            (writeBytes
              (writeBytes mem dst out)
              xj (wordBytes 8 (j1 + k)))
            outn (wordBytes 8 out.length))
          ei (wordBytes 8 out.length) := by
  -- name the arm's word in the model's spelling, so the two sides' only difference
  -- is the clear's presence
  show writeBytes (writeBytes (writeBytes (writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst out)
      xj (wordBytes 8 (j1 + k))) ei (wordBytes 8 out.length)) outn (wordBytes 8 out.length)
    = writeBytes (writeBytes (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
        outn (wordBytes 8 out.length)) ei (wordBytes 8 out.length)
  -- 1. the arm's clear is absorbed
  rw [writeBytes_absorb_one mem hei hdst hxj
    (by simp [wordBytes, natToBytes_length]) hd_ei hx_ei hd_xj]
  -- 2. the slot's write crosses `outn`, which needs both regions present in the
  --    memory the crossed writes leave
  have hmid_ei : readBytes (writeBytes mem dst out) ei 8 ≠ none := by
    rcases hd_ei with h | h
    · rw [readBytes_writeBytes_below mem out 8 ei dst h]; exact hei
    · rw [s2StringBodyReadBytes_above mem out 8 ei dst h]; exact hei
  have hmid_outn : readBytes (writeBytes mem dst out) outn 8 ≠ none := by
    rcases ho_d with h | h
    · rw [readBytes_writeBytes_below mem out 8 outn dst h]; exact houtn
    · rw [s2StringBodyReadBytes_above mem out 8 outn dst h]; exact houtn
  have hei' : readBytes (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
      ei 8 ≠ none := by
    rcases hx_ei with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 ei xj h]
      exact hmid_ei
    · rw [s2StringBodyReadBytes_above (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 ei xj (by simpa [wordBytes, natToBytes_length] using h)]
      exact hmid_ei
  have houtn' : readBytes (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
      outn 8 ≠ none := by
    rcases ho_x with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 outn xj h]
      exact hmid_outn
    · rw [s2StringBodyReadBytes_above (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 outn xj (by simpa [wordBytes, natToBytes_length] using h)]
      exact hmid_outn
  obtain ⟨X₁, hX₁⟩ := exists_readBytes_of_ne hei'
  obtain ⟨O₁, hO₁⟩ := exists_readBytes_of_ne houtn'
  have ho_ei' : ei + (wordBytes 8 out.length).length ≤ outn ∨
      outn + (wordBytes 8 out.length).length ≤ ei := by
    simpa [wordBytes, natToBytes_length] using ho_ei
  rw [writeBytes_comm_of_present (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
    ei (wordBytes 8 out.length) outn (wordBytes 8 out.length)
    ⟨X₁, hX₁⟩ ⟨O₁, hO₁⟩ ho_ei']

/-- **The refusal record's fields are the model's.**  The body writes the record's
three words at `e`, `e + 8`, `e + 16`; the model writes
`writeBytes (writeBytes (writeBytes mem e (wordBytes 4 0)) (e + 8) (wordBytes 8 off))
(e + 16) (wordBytes 8 msg)` with `off = pos0 + off` and `msg = 0`.  The three writes
agree word for word, and the offset's reconciliation is the only arithmetic: the
body's `off + sub` is `off.toNat + pos0` because `sub` is `pos0` at `i64` and the sum
does not wrap. -/
theorem s2StringBodyErrRecord_reconciles (mem : Mem) (e : Nat) (off : BitVec 64)
    (sub : BitVec 64) (pos0 : Nat)
    (hsub : sub = BitVec.ofNat 64 pos0) (hpos0 : pos0 < 2 ^ 64)
    (hsum : off.toNat + pos0 < 2 ^ 64) :
    writeBytes
        (writeBytes
          (writeBytes mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8))
        (e + (16#64).toNat) (natToBytes (0#64).toNat 8)
      = stage2ErrSetMsg mem e (pos0 + off.toNat) 0 := by
  have htoNat : (off + sub).toNat = off.toNat + pos0 := by
    rw [hsub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h0_32 : (0#32).toNat = 0 := by decide
  have h0_64 : (0#64).toNat = 0 := by decide
  have h8 : (8#64).toNat = 8 := by decide
  have h16 : (16#64).toNat = 16 := by decide
  simp only [stage2ErrSetMsg, stage2ErrSet, wordBytes, htoNat, h0_32, h0_64, h8, h16,
    Nat.add_comm]

/-- **The refused arm's memory join.**  The clear is absorbed by the callee's own
`ei` write (adjacent: for the refusal the slot's content *is* that word), then
`scan(xj)` moves right past the record's three words and the `ei` write follows it —
seven crossings over five present, pairwise disjoint regions. -/
theorem s2StringBodyMemory_refused (mem : Mem) {ei xj e : Nat}
    {Wj R0 R1 R2 Woff : List UInt8}
    (hWoff : Woff.length = 8)
    (hei : readBytes mem ei Woff.length ≠ none)
    (hxj : readBytes mem xj Wj.length ≠ none)
    (he0 : readBytes mem e R0.length ≠ none)
    (he1 : readBytes mem (e + (8#64).toNat) R1.length ≠ none)
    (he2 : readBytes mem (e + (16#64).toNat) R2.length ≠ none)
    (h1 : ei + Woff.length ≤ xj ∨ xj + Wj.length ≤ ei)
    (h2 : ei + Woff.length ≤ e ∨ e + R0.length ≤ ei)
    (h3 : ei + Woff.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ ei)
    (h4 : ei + Woff.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ ei)
    (h5 : xj + Wj.length ≤ e ∨ e + R0.length ≤ xj)
    (h6 : xj + Wj.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ xj)
    (h7 : xj + Wj.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ xj)
    (h8 : e + R0.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ e)
    (h9 : e + R0.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ e)
    (h10 : e + (8#64).toNat + R1.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ e + (8#64).toNat) :
    writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes mem ei (natToBytes (0#64).toNat 8)) ei Woff)
              xj Wj)
            e R0)
          (e + (8#64).toNat) R1)
        (e + (16#64).toNat) R2
      = writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes mem e R0)
                (e + (8#64).toNat) R1)
              (e + (16#64).toNat) R2)
            xj Wj)
          ei Woff := by
  rw [show writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) ei Woff
      = writeBytes mem ei Woff from
    writeBytes_writeBytes_same mem ei (natToBytes (0#64).toNat 8) Woff
      (by simp [natToBytes_length, hWoff])]
  -- the presences, one per region per hop
  have hei_xj : readBytes (writeBytes mem xj Wj) ei Woff.length ≠ none := by
    rcases h1 with h | h
    · rw [readBytes_writeBytes_below mem Wj Woff.length ei xj (by omega)]; exact hei
    · rw [s2StringBodyReadBytes_above mem Wj Woff.length ei xj (by omega)]; exact hei
  have he0_xj : readBytes (writeBytes mem xj Wj) e R0.length ≠ none := by
    rcases h5 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R0.length e xj (by omega)]; exact he0
    · rw [readBytes_writeBytes_below mem Wj R0.length e xj (by omega)]; exact he0
  have hei_xj0 : readBytes (writeBytes (writeBytes mem xj Wj) e R0) ei Woff.length ≠ none := by
    rcases h2 with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem xj Wj) R0 Woff.length ei e (by omega)]
      exact hei_xj
    · rw [s2StringBodyReadBytes_above (writeBytes mem xj Wj) R0 Woff.length ei e (by omega)]
      exact hei_xj
  have hei_xj01 : readBytes (writeBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1) ei Woff.length ≠ none := by
    rcases h3 with h | h
    · rw [readBytes_writeBytes_below (writeBytes (writeBytes mem xj Wj) e R0) R1
        Woff.length ei (e + (8#64).toNat) (by omega)]
      exact hei_xj0
    · rw [s2StringBodyReadBytes_above (writeBytes (writeBytes mem xj Wj) e R0) R1
        Woff.length ei (e + (8#64).toNat) (by omega)]
      exact hei_xj0
  have he1_xj : readBytes (writeBytes mem xj Wj) (e + (8#64).toNat) R1.length ≠ none := by
    rcases h6 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R1.length (e + (8#64).toNat) xj (by omega)]
      exact he1
    · rw [readBytes_writeBytes_below mem Wj R1.length (e + (8#64).toNat) xj (by omega)]
      exact he1
  have he1_xj0 : readBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1.length ≠ none := by
    rcases h8 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem xj Wj) R0 R1.length
        (e + (8#64).toNat) e h]
      exact he1_xj
    · rw [readBytes_writeBytes_below (writeBytes mem xj Wj) R0 R1.length
        (e + (8#64).toNat) e h]
      exact he1_xj
  have he2_xj : readBytes (writeBytes mem xj Wj) (e + (16#64).toNat) R2.length ≠ none := by
    rcases h7 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R2.length (e + (16#64).toNat) xj (by omega)]
      exact he2
    · rw [readBytes_writeBytes_below mem Wj R2.length (e + (16#64).toNat) xj (by omega)]
      exact he2
  have he2_xj0 : readBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (16#64).toNat) R2.length ≠ none := by
    rcases h9 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem xj Wj) R0 R2.length
        (e + (16#64).toNat) e h]
      exact he2_xj
    · rw [readBytes_writeBytes_below (writeBytes mem xj Wj) R0 R2.length
        (e + (16#64).toNat) e h]
      exact he2_xj
  have he2_e0 : readBytes (writeBytes mem e R0) (e + (16#64).toNat) R2.length ≠ none := by
    rcases h9 with h | h
    · rw [s2StringBodyReadBytes_above mem R0 R2.length (e + (16#64).toNat) e h]; exact he2
    · rw [readBytes_writeBytes_below mem R0 R2.length (e + (16#64).toNat) e h]; exact he2
  have he2_xj01 : readBytes (writeBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1) (e + (16#64).toNat) R2.length ≠ none := by
    rcases h10 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes (writeBytes mem xj Wj) e R0) R1
        R2.length (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_xj0
    · rw [readBytes_writeBytes_below (writeBytes (writeBytes mem xj Wj) e R0) R1
        R2.length (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_xj0
  -- 1. `ei`'s write crosses `xj`
  rw [writeBytes_comm_of_present mem ei Woff xj Wj
    (exists_readBytes_of_ne hei) (exists_readBytes_of_ne hxj) h1]
  -- 2-3. and the record's first two words
  rw [writeBytes_comm_of_present (writeBytes mem xj Wj) ei Woff e R0
    (exists_readBytes_of_ne hei_xj) (exists_readBytes_of_ne he0_xj) h2]
  rw [writeBytes_comm_of_present (writeBytes (writeBytes mem xj Wj) e R0) ei Woff
    (e + (8#64).toNat) R1 (exists_readBytes_of_ne hei_xj0)
    (exists_readBytes_of_ne he1_xj0) h3]
  rw [writeBytes_comm_of_present (writeBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1) ei Woff (e + (16#64).toNat) R2
    (exists_readBytes_of_ne hei_xj01)
    (exists_readBytes_of_ne he2_xj01) h4]
  -- 4. `xj` past the record's first word
  rw [writeBytes_comm_of_present mem xj Wj e R0
    (exists_readBytes_of_ne hxj) (exists_readBytes_of_ne he0) h5]
  -- 5-6. and past the next two, which needs `xj`'s and their presence in what the
  -- earlier crossings left
  have hxj_e0 : readBytes (writeBytes mem e R0) xj Wj.length ≠ none := by
    rcases h5 with h | h
    · rw [readBytes_writeBytes_below mem R0 Wj.length xj e h]; exact hxj
    · rw [s2StringBodyReadBytes_above mem R0 Wj.length xj e h]; exact hxj
  have he1_e0 : readBytes (writeBytes mem e R0) (e + (8#64).toNat) R1.length ≠ none := by
    rcases h8 with h | h
    · rw [s2StringBodyReadBytes_above mem R0 R1.length (e + (8#64).toNat) e h]; exact he1
    · rw [readBytes_writeBytes_below mem R0 R1.length (e + (8#64).toNat) e h]; exact he1
  have he1_e0xj : readBytes (writeBytes (writeBytes mem e R0) xj Wj)
      (e + (8#64).toNat) R1.length ≠ none := by
    rcases h6 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem e R0) Wj R1.length
        (e + (8#64).toNat) xj h]
      exact he1_e0
    · rw [readBytes_writeBytes_below (writeBytes mem e R0) Wj R1.length
        (e + (8#64).toNat) xj h]
      exact he1_e0
  rw [writeBytes_comm_of_present (writeBytes mem e R0) xj Wj (e + (8#64).toNat) R1
    (exists_readBytes_of_ne hxj_e0) (exists_readBytes_of_ne he1_e0) h6]
  have hxj_e01 : readBytes (writeBytes (writeBytes mem e R0) (e + (8#64).toNat) R1)
      xj Wj.length ≠ none := by
    rcases h6 with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem e R0) R1 Wj.length xj
        (e + (8#64).toNat) h]
      exact hxj_e0
    · rw [s2StringBodyReadBytes_above (writeBytes mem e R0) R1 Wj.length xj
        (e + (8#64).toNat) h]
      exact hxj_e0
  have he2_e01 : readBytes (writeBytes (writeBytes mem e R0) (e + (8#64).toNat) R1)
      (e + (16#64).toNat) R2.length ≠ none := by
    rcases h10 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem e R0) R1 R2.length
        (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_e0
    · rw [readBytes_writeBytes_below (writeBytes mem e R0) R1 R2.length
        (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_e0
  rw [writeBytes_comm_of_present (writeBytes (writeBytes mem e R0) (e + (8#64).toNat) R1)
    xj Wj (e + (16#64).toNat) R2 (exists_readBytes_of_ne hxj_e01)
    (exists_readBytes_of_ne he2_e01) h7]

/-- **`%cmp3`'s bit.**  The entry's test is `j0` against the count at `i64`; both
sides are below `2 ^ 63`, so the unsigned comparison is the model's `Nat` one. -/
theorem s2StringBodyBit_cmp3_one {j0 : Nat} {nxp : BitVec 64}
    (hx : j0 < 2 ^ 63) (hy : nxp.toNat < 2 ^ 63) (h : j0 < nxp.toNat) :
    evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1 := by
  have h64 : j0 < 2 ^ 64 := by omega
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, h, BitVec.ofBool]
  rfl

/-- The same test as `0`: the entry leaves for the body-itself arm. -/
theorem s2StringBodyBit_cmp3_zero {j0 : Nat} {nxp : BitVec 64}
    (hx : j0 < 2 ^ 63) (hy : nxp.toNat < 2 ^ 63) (h : nxp.toNat ≤ j0) :
    evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1 := by
  have h64 : j0 < 2 ^ 64 := by omega
  have hlt : ¬ j0 < nxp.toNat := by omega
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, hlt,
    BitVec.ofBool]
  rfl

/-- **`takeWhile` is empty exactly when the list is empty or its head fails the
predicate.**  The `true` direction is structural — `takeWhile`'s two equations and the
induction — and the `false` direction is the head's value; that asymmetry is why
stating the `iff` this way needs no arithmetic. -/
theorem takeWhile_isEmpty_iff {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.takeWhile p).isEmpty = true ↔
      (l = [] ∨ ∃ a t, l = a :: t ∧ ¬ p a = true)
  | [] => by simp
  | a :: t => by
      by_cases h : p a = true
      · rw [List.takeWhile_cons_of_pos (p := p) h]
        simp only [List.isEmpty_cons, Bool.false_eq_true, false_iff]
        rintro (h' | ⟨a', t', heq, hneg⟩)
        · exact absurd h' (by simp)
        · simp only [List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact absurd h hneg
      · rw [List.takeWhile_cons_of_neg (p := p) h]
        exact ⟨fun _ => Or.inr ⟨a, t, rfl, h⟩, fun _ => rfl⟩

set_option maxHeartbeats 1000000 in
/- **The inside test's shape**: the model's window is empty exactly when the lane at
`j1` is past it, or there is none — which is what the body's `%cmp7` reads, its lane's
value being the model's entry at that index. -/
theorem s2StringBodyInBody_empty_iff (ps : List Nat) (j1 pos0 len : Nat) :
    ((ps.drop j1).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true ↔
      (ps.drop j1 = [] ∨ ∃ a t, ps.drop j1 = a :: t ∧ pos0 + len ≤ a) := by
  rw [takeWhile_isEmpty_iff]
  constructor
  · rintro (h | ⟨a, t, heq, hneg⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a, t, heq, ?_⟩
      have : ¬ a < pos0 + len := by simpa using hneg
      omega
  · rintro (h | ⟨a, t, heq, hle⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a, t, heq, ?_⟩
      have : ¬ a < pos0 + len := by omega
      simpa using this

/-- A lane the list holds at `c` starts the drop at `c`. -/
theorem drop_eq_cons_of_getElem? {ps : List Nat} {c lane : Nat}
    (h : ps[c]? = some lane) : ps.drop c = lane :: ps.drop (c + 1) := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  rw [← heq]
  exact List.drop_eq_getElem_cons hlt

/-- **`%cmp7`'s case**: a lane at or past the window's end makes the model's window
empty, which is the body-itself arm.  The lane is the one `readLanes32_lane` gives at
the scan's exit counter, and the comparison is the body's `%cmp7`. -/
theorem s2StringBodyWindow_empty_of_lane {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane) (hle : pos0 + len ≤ lane) :
    ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true := by
  rw [s2StringBodyInBody_empty_iff]
  exact Or.inr ⟨lane, ps.drop (c + 1), drop_eq_cons_of_getElem? hlane, hle⟩

/-- **The expander arm's switch**: a lane below the window's end keeps the window
non-empty, which is the decoded/refused fork.  The dual of
`s2StringBodyWindow_empty_of_lane`, with `false`/`<` in place of `true`/`≤`. -/
theorem s2StringBodyWindow_cons_of_lane {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane) (hlt : lane < pos0 + len) :
    ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = false := by
  rw [drop_eq_cons_of_getElem? hlane]
  rw [List.takeWhile_cons_of_pos (p := fun q => decide (q < pos0 + len)) (by simpa using hlt)]
  rfl

/-- The body's own slot is eight bytes, so the run's cursor moves by exactly the
post's `next + 8` — and nothing else in the body moves it: the callee keeps `next`,
and the other blocks allocate nothing. -/
theorem s2StringBodySlot_sizeBytes : (Ty.int 64).sizeBytes = 8 := by decide

/- **The assembly's remaining content, and it is the control flow, not the memory.**
The memory is done: both arms' joins, the record reconciliation, the `takeWhile`
bridge.  What the contract still needs is the correspondence between the model's
three-way split and the body's four branch bits, each derived from the model's own
data:

* `%cmp3` (entry) is `j0 < nxp.toNat` — the pre's `j0 < 2^63` and the model's
  `readLanes32` give it;
* `%cmp1` (the head) is `pos0 ≤ ps[c]` read backwards: the lane's value is the model's
  entry (`readLanes32_lane`) and `sub` is `pos0` at `i64` (`ofNat_sub`);
* `%cmp7` (the inside test) is `pos0 + len` against that lane — which is where the
  model's `inBody.isEmpty` decides the body-itself arm, and the `takeWhile` bridge
  supplies the `j1` the arm's memory names;
* `%cmp9` (the call's answer) is the expander's own word, which the clause gives
  (`escapeExpand8_decoded`/`_refused`).

So the assembly is **four bit derivations and a composition**, and the composition is
the part the module already has: entry prefix, seat, `s2StringBodyScan_run`, the
`Exited` split, and the arm-correct join.  It is the control flow's correspondence
that is new, and it is the same kind of work as the bridge: a semantic link between
the model's `Nat` data and the body's `i1` tests. -/

/- **The contract's prerequisite, now proved.**  The planning estimate was that
`s2StringBodyBody_contract` would assemble seat, run, split and joins — "no crossings,
so the smallest unit" — and a check of this cone said otherwise: the scan's
characterization was missing.  The model's `j1` is
`j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length`, while the loop's exit word
gives a counter `c` with `s2StringBodyScanAtBound`'s disjunction at it.  That bridge is
`scanCounter_eq_takeWhile` below, from `takeWhile_length_of_counter`: **a counter whose
every position below it satisfies the predicate, and whose own position does not (or is
past the list), is the `takeWhile` length.**  It is a three-lemma development, not an
assembly step — which is why "no crossings" was the wrong dimension to count, and the
mistake was mine. -/

/-- The cursor word the scan leaves is the model's `j1`: the exit word's counter,
written at the caller's cursor, is the memory the model's `j1` names.  This is where
`ExitWord`'s `∃ c` is consumed — at the memory term, not at the exits. -/
theorem s2StringBodyMemory_cursor {mem0 : Mem} {xj c : Nat} {e : State}
    (h : e.mem = writeBytes mem0 xj (wordBytes 8 c)) :
    writeBytes mem0 xj (wordBytes 8 c) = e.mem := h.symm


/-! ### The callee arms' join

Both callee arms end with two eight-byte writes whose *order* differs from the
model's, and the join needs exactly two facts:

* **the slot write absorbs the arm's clear** — proved below
  (`s2StringBodySlot_absorb`): the body stores `0` at its slot before the call and
  the callee stores the arm's word there, so the second write is the memory;
* **two in-place writes over disjoint regions commute** — proved below as
  `writeBytes_comm_of_present`, at the shape the join uses:

      readBytes A a X.length ≠ none → readBytes A b Y.length ≠ none →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X

  It is not `writeBytes_absent_comm_witness`'s claim (that one is false, and the
  witness is why): both regions must be **present**, which is what makes each write
  a replacement in place, and only then is the append order irrelevant.  Presence is
  stated existentially — the bytes *written* and the bytes *present* are different
  lists of the same length — and it survives the inductive step's byte write by
  `readBytes_writeByte_above`/`_below`, one for each side of the region.  **That
  two-sidedness is the cluster's whole content**: the commutation splits on which
  side the odd address lies, and so does the preservation it needs.  The remaining
  obligation is the two instantiations, whose presence facts are the staging's.

**A write-order join's cost is the distance between the model's write position and
the body's, measured in intervening regions — every unit of distance is one
commutation.**  The body writes the slot early (the callee does it, before `outn`'s
word), the model writes it last, so the decoded arm is three moves (absorb the
arm's clear, then commute the slot past `outn` and `outn` past `xj`/`dst`) and the
refused arm is one more.  A reader who knows the distance will not expect one move.
The first of those moves needs a lemma this section does not yet have —
`writeBytes_absorb_one`: a write to a region that is **present**, followed by
intervening writes disjoint from it, is absorbed by a later write to that region.
Its proof is an induction over the memory showing that an in-place write changes no
cell's *position*, which is what the two preservations above supply one byte at a
time.

**The absorption is an artefact of the direction, and moving the *clear* rightwards
is what makes it cheap.**  Two directions reach the adjacency, and they do not cost
the same, because the target's slot write comes **last**:

* moving the **clear** rightwards to meet the slot costs **four** moves — past
  `dst`, past `xj`, the absorption itself, then the slot past `outn`;
* moving the **slot** leftwards towards the clear costs **seven** — the same three
  crossings to reach it, the absorption, and then three back, because the model's
  memory has the slot last and it has to return.

**The absorption's route, and the canonical form that does not work.**  The first
idea was to make the shape definitional — a map `memUpd A a n bs` re-valuing the
region's cells, with `writeBytes A a bs = memUpd A a bs.length bs` proved once.  It
fails, and the witness is `writeByte_not_map_of_duplicate`: **`writeByte` replaces the
*first* cell at an address, and a map replaces every cell there**, so with a
duplicated address the two disagree.  The equivalence therefore needs
duplicate-freedom *as well as* presence, and duplicate-freedom is exactly the staging
clause the join may not add — so the canonical route is closed here, and it is closed
by the same wall `readByte_not_determined_by_reads` shows: the memory's list order
carries information its bytes do not.

**The absorption itself survives duplicates**, because both of its sides replace the
*same* first occurrences — which is why the direct induction over the memory is the
route, not a map lemma.  But it needs presence of **every** region it names, not only
the one it erases: an absent region is *appended*, and the two sides append in
different orders (`clear, dst, xj` against `dst, xj, slot`), so a single absent
region makes the lists differ while every read agrees.  That is the same wall for the
third time, now quantitative — presence is what makes each write in place, and the
absorption needs it on all three regions it crosses.  The join has it: `dst` and `xj`
are staged (the writing caller's buffers) and `ei` is the caller's own stack slot, so
none of the three is appended by these writes.

The lemma is proved above (`writeBytes_absorb_one`), and **it is not a walk**: the
earlier clear crosses `dst`, then `xj`, and the two writes to the erased region end
up adjacent, where `writeBytes_writeBytes_same` erases the first.  Two commutations
and one absorption — which is the four-move count, vindicated: the retraction two
rounds ago (that commutations cannot remove a write) was wrong because adjacency plus
`writeBytes_writeBytes_same` *is* the removal.

Its hypotheses are six, and instrument eleven counts them exactly: **three presences**
(the erased region and both regions it crosses) and **three pairwise disjointnesses**
(one per pair).  Each crossing spends its presence and its disjointness, which is why
the conclusion's one region needed six facts in the statement.

**The refused arm's chain, written out.**  Its body writes six times:
`clear(ei)`, the callee's `offset(ei)`, `scan(xj)`, then the record's three words at
`e`, `e + 8`, `e + 16`.  The model writes five: the record's three, `scan(xj)`, then
the slot at `ei`.  So the join is

* the clear absorbed by the callee's own `ei` write — they are **adjacent**, so
  `writeBytes_writeBytes_same` does it (`s2StringBodySlot_absorb` outside a type
  argument);
* `scan(xj)` moved right past the record's three words — 3 crossings;
* the `ei` write moved right to the end — 4 crossings;

**seven commutations, and ten pairwise disjointnesses** (five regions: `ei`, `xj`,
`e`, `e + 8`, `e + 16`), the last three pairs being the record's own words, which are
disjoint from each other (`4`, `8`, `8` bytes at `e`, `e + 8`, `e + 16`).  The
decoded arm's three crossings are the same two moves at a shorter distance: **the
model's write order charges for the record's three words, and the decoded arm never
writes a record at all.**  That is the two arms' difference, measured.

**Neither count is reachable with commutations alone, and the typecheck says why.**
The statement typechecks with its conclusion as a hypothesis (the produced-form
check: if `example (…) (h : <the equality>) : <the equality> := h` elaborates, the
terms are the ones the callee produces), and the same check shows the gap: the
source order is
`clear, dst, xj, slot, outn` and the target is `dst, xj, outn, slot`.  Commuting a
write never *removes* one, so the `clear` must be **erased**, not moved — and the
only eraser is a write to the same region, which the target's `slot` is, but only
after `outn`, i.e. not adjacent to the `clear` in any order the commutations can
produce while keeping the target's order.  So the absorption is necessary after all,
and it is `writeBytes_absorb_one` — the lemma this section previously concluded was
an artefact.  **Two counts and one retraction are recorded here on purpose**: the
leftward count (three) reached the adjacency but not the target; the rightward
count (four) reached neither without erasing; and the erasure is the induction.

What the typecheck *did* establish is worth keeping: the source term is the body's
own, the target term is the model's plus the slot at `next = ei`, and the two differ
exactly by the clear's erasure — which is the whole of what the induction must show.

For the record, the two facts that direction would have needed:

* **position preservation** — a write over a *present* region changes values only,
  so every cell keeps its position and the memory's *shape* is unchanged.  That is
  what rules out `b`'s append moving when the `a`-region is rewritten first, the
  hypothesis the commutation route could not supply;
* **region extensionality** — two memories that agree at every address outside a
  region, and each hold that region present, agree after being rewritten there with
  the same bytes.  That is what lets a final in-place write erase an earlier one
  whose values differ — **but it is false as stated**, and
  `readByte_not_determined_by_reads` is the witness: a duplicated address answers
  every read as the memory without it does, so two different lists have the same
  byte everywhere.  The true statement needs **duplicate-freedom** on the memory's
  address sequence, which no module in this cone supplies; so the absorption is
  either proved by a direct induction over the memory with two region cursors (no
  extensionality), or the staging gains a `Nodup` clause.  That choice is the
  closing's, not the lemma's, and it is the last shape question the row has.

With both, `writeBytes_absorb_one` is an induction whose region extent is
*constant* (both `ei` writes are eight bytes, so no length negotiation enters) and
whose outside-agreement is carried by `readBytes_writeByte_above`/`_below`.

**And the method, three times over**: a lemma written for one purpose has twice
become the next lemma's prerequisite — `readBytes_writeByte_below` was written for
the commutation, `_above` as its dual, and the absorption needs both, as the
instrument that carries a presence past a write on either side.  That is what a
vocabulary converging on the right side conditions looks like, and the practical
reason to state a fact at the weakest side condition its *use* needs rather than at
the strongest its proof can reach.  -/

/-- **The slot write absorbs the arm's clear.**  The body writes `0` at the slot
before the call and the callee writes the arm's word there; the second write is the
memory, because the first one made the region present and both are eight bytes. -/
theorem s2StringBodySlot_absorb (a : Mem) (ei : Nat) (w : BitVec 64) :
    writeBytes (writeBytes a ei (natToBytes (0#64).toNat 8)) ei
        (natToBytes w.toNat 8) =
      writeBytes a ei (natToBytes w.toNat 8) :=
  writeBytes_writeBytes_same a ei (natToBytes (0#64).toNat 8) (natToBytes w.toNat 8)
    (by simp [natToBytes_length])


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
