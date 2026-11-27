/-
`num_el_el1`'s emitted body, pinned, and the deferred Eisel-Lemire test it computes.

`JsonNumFastAssumed` states the conversion's callee half as one value,
`NumFastCalleesAnswered`: the walk's `Calls` selection answers `num_d8_el1`,
`num_el_el1` and `stk_mul_u64` with their measured model, and the content that
the compiled bodies behave as that model is the trust statement the value names.
`JsonStage2NumFastCalls` supplies the model — `numElEl1` for this kernel, with the
`EPOW` table as a parameter — and `JsonStage2NumFastCalleeD8` pins the first of
the three bodies.  This module is the second.

**What the fixture needed.**  `probes/install/ir/capture-stage2-callees.sh`
writes the body from `kernel/json/stage2.c` at the measured compiler line, and
until now the capture recorded this one as unreadable: its `EPOW` index is
`getelementptr [91 x %struct.EPow]`, a *named struct* as an array element, and
the parser had no reader for one.  Two changes close that.

* `Parser.expectArrayTy` and the `getelementptr` branch now resolve
  `%struct.<name>` through the declared `Layout` (`Parser.resolveStruct`), and
  `Ty.gepElemAdmitted` admits a resolved struct: its declared extent is both its
  allocated and its stored size, so the step scales by exactly the number LLVM
  steps by.  The two-index form `[91 x %struct.EPow], ptr @EPOW, i64 0, i64 %sub`
  reduces to the one-index struct step the model carries — `Instr.gep "%arrayidx"
  (Ty.struct "EPow" 24) (Operand.global "@EPOW") (Operand.reg "%sub")` — and the
  printer's reduced form re-parses to that same AST.  The extent 24 is
  `numElLayout` below: `uint64_t hi, lo; int32_t e` is twenty bytes padded to the
  struct's eight-byte alignment, and `numEl_arrayExtent` checks it against the
  array's own lane count and the exponent's byte offset.
* The body's one `llvm.ctlz.i64` call is emitted with the flag `i1 true`, which
  the parser refuses by name (it promises poison at the zero word, and the model
  has no poison).  The capture therefore *weakens* the flag to `i1 false`, one
  row in `stage2.callees.rewrites.tsv`; § "The ctlz flag" states the structural
  fact that makes it sound — the entry's `%w == 0` return keeps the zero word off
  the only path to the call, and the two flags agree on a nonzero operand.

**What this module establishes.**  The pin — `numElSrc` is the fixture,
`firstFunctionWith numElLayout` of it is `numElBody`, block by block and
instruction by instruction, with mutated-text, no-layout and wrong-layout
controls so the equality is about the file — and the body's test, in the model's
vocabulary:

* `numEl_rowAddr`, `numEl_rowAddr_i64`, `numEl_eAddr` — the emitted
  `getelementptr`s are `EPOW + 24 * (q + 45)` and `row + 16`, read through the
  semantics' own `gep` rule;
* `numEl_mask`, `numEl_slice`, `numEl_shift`, `numEl_half` — the guard slice, the
  significand and the two window words the emitted `and`/`or`/`lshr`/`shl`
  sequence computes, as the model's `hp`, `m`, `hh` and `up`;
* `numEl_window` — the emitted wrapped `(hp - hh) + 2 < 3` test is the guard's
  own `inWindow` at those words (`ElGuardRefine`), so the branch the body takes
  is the branch `numElEl1` takes;
* `NumElRow`, `NumElRow.row`, `numEl_load_hi`, `numEl_load_e` — the staging the
  body reads its row from: the two loads at the `EPOW` address and sixteen bytes
  into it are the row's `hi` and `e` words, and the four field reads compose to
  the 24-byte record the out-of-line `el_exact` receives;
* `numEl_entry_test`, `numEl_entry_cond_false`, `numEl_end4_only_from_entry`,
  `numEl_flag_domain` — the ctlz flag's poison is unobserved.

**What it is not.**  It is not the agreement theorem, and it is not a run of the
body: `numElEl1`'s answer at the entry state — the refusal arms, the window's
`el_exact` call and the fast path's `el_pack` call — is not stated here.  What is
here is the branch condition and the arguments those calls pass, each proved of
the pinned text.  The two out-of-line callees are not modelled either: `el_exact`
and `el_pack` are `Calls`-resolved in the body, their own emitted bodies are not
captured under `probes/`, and this fixture is a `define` block, so it carries no
`@EPOW` or `@g_el_window` declaration — the table's rows and the counter's word
are the staging's data (`NumElRow`, `numElGlobals`), not text the fixture states.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonStage2StringBodyMemory
import LeanLLVM.ElGuardRefine
import LeanLLVM.Refinement.BitLanes

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The fixture, its layout and the body -/

/-- The captured body, as `capture-stage2-callees.sh` writes it. -/
def numElSrc : String :=
  include_str "../../probes/install/ir/stage2.callee.num_el_el1.ll"

/-- **The declared layout the fixture needs.**  The capture takes one `define`
block, so the module's `%struct.EPow = type` line is not in the text, and the
parser takes a struct's extent from its `Layout` argument.  `kernel/json/stage2.c`
declares `typedef struct { uint64_t hi, lo; int32_t e; } EPow;`: sixteen bytes of
limbs and four of exponent, padded to the struct's eight-byte alignment, so the
extent is 24.  `numEl_arrayExtent` and `numEl_eOffset` hold it to the two numbers
the body states itself: the array's 91 lanes and the exponent's byte offset of 16
(`if.end19`'s own `getelementptr i8 … i64 16`). -/
def numElLayout : Layout := [("EPow", 24)]

/-- The entry block. -/
def numElEntryInstrs : List Instr :=
  [
    Instr.icmp "%cmp2" (IPred.eq) 64 (Operand.reg "%w") (Operand.imm (Const.int 64 0x0000000000000000#64))]

/-- The zero-mantissa arm: `*out = 0.0`. -/
def numElIfThen3Instrs : List Instr :=
  [
    Instr.store Ty.double (Operand.imm (Const.float 0x0000000000000000#64)) (Operand.reg "%out")]

/-- The guard computation: the table index, the normalised product's high word,
the guard slice and the window test. -/
def numElIfEnd4Instrs : List Instr :=
  [
    Instr.binop "%sub" (BinOp.add) 64 (Operand.reg "%q") (Operand.imm (Const.int 64 0x000000000000002d#64)),
    Instr.gep "%arrayidx" (Ty.struct "EPow" 24) (Operand.global "@EPOW") (Operand.reg "%sub"),
    Instr.call "%0" (Ty.int 64) "llvm.ctlz.i64" [((Ty.int 64), (Operand.reg "%w")),
                             ((Ty.int 1), (Operand.imm (Const.int 1 0x0#1)))],
    Instr.trunc "%cast" 64 32 (Operand.reg "%0"),
    Instr.binop "%shl" (BinOp.shl) 64 (Operand.reg "%w") (Operand.reg "%0"),
    Instr.zext "%conv" 64 128 (Operand.reg "%shl"),
    Instr.load "%1" (Ty.int 64) (Operand.reg "%arrayidx"),
    Instr.zext "%conv5" 64 128 (Operand.reg "%1"),
    Instr.binop "%mul" (BinOp.mul) 128 (Operand.reg "%conv5") (Operand.reg "%conv"),
    Instr.binop "%shr" (BinOp.lshr) 128 (Operand.reg "%mul") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.trunc "%conv6" 128 64 (Operand.reg "%shr"),
    Instr.binop "%shr7" (BinOp.lshr) 64 (Operand.reg "%conv6") (Operand.imm (Const.int 64 0x000000000000003f#64)),
    Instr.trunc "%conv8" 64 32 (Operand.reg "%shr7"),
    Instr.binop "%shl9" (BinOp.shl) 64 (Operand.reg "%shr7") (Operand.imm (Const.int 64 0x000000000000000a#64)),
    Instr.binop "%or" (BinOp.or) 64 (Operand.reg "%shl9") (Operand.imm (Const.int 64 0x00000000000003ff#64)),
    Instr.binop "%and" (BinOp.and) 64 (Operand.reg "%or") (Operand.reg "%conv6"),
    Instr.binop "%shl11" (BinOp.shl) 32 (Operand.imm (Const.int 32 0x00000200#32)) (Operand.reg "%conv8"),
    Instr.zext "%conv12" 32 64 (Operand.reg "%shl11"),
    Instr.binop "%reass.sub" (BinOp.sub) 64 (Operand.reg "%and") (Operand.reg "%conv12"),
    Instr.binop "%sub14" (BinOp.add) 64 (Operand.reg "%reass.sub") (Operand.imm (Const.int 64 0x0000000000000002#64)),
    Instr.icmp "%cmp15" (IPred.ult) 64 (Operand.reg "%sub14") (Operand.imm (Const.int 64 0x0000000000000003#64))]

/-- The exact arm: the window is hit, the counter moves and `el_exact` decides. -/
def numElIfThen18Instrs : List Instr :=
  [
    Instr.load "%2" (Ty.int 64) (Operand.global "@g_el_window"),
    Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%2") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.store (Ty.int 64) (Operand.reg "%inc") (Operand.global "@g_el_window"),
    Instr.call "%call" (Ty.int 32) "el_exact" [((Ty.int 64), (Operand.reg "%shl")),
                             ((Ty.int 32), (Operand.reg "%cast")),
                             (Ty.ptr, (Operand.reg "%arrayidx")),
                             ((Ty.int 64), (Operand.reg "%q")),
                             (Ty.ptr, (Operand.reg "%out"))]]

/-- The fast arm: the significand and the exponent's word go to `el_pack`. -/
def numElIfEnd19Instrs : List Instr :=
  [
    Instr.binop "%add" (BinOp.or) 64 (Operand.reg "%shr7") (Operand.imm (Const.int 64 0x000000000000000a#64)),
    Instr.binop "%shr21" (BinOp.lshr) 64 (Operand.reg "%conv6") (Operand.reg "%add"),
    Instr.icmp "%cmp22" (IPred.ugt) 64 (Operand.reg "%and") (Operand.reg "%conv12"),
    Instr.zext "%conv23" 1 32 (Operand.reg "%cmp22"),
    Instr.gep "%3" (Ty.int 8) (Operand.reg "%arrayidx") (Operand.imm (Const.int 64 0x0000000000000010#64)),
    Instr.load "%arrayidx.val" (Ty.int 32) (Operand.reg "%3"),
    Instr.call "%call24" (Ty.int 32) "el_pack" [((Ty.int 64), (Operand.reg "%shr21")),
                             ((Ty.int 32), (Operand.reg "%conv23")),
                             ((Ty.int 32), (Operand.reg "%conv8")),
                             ((Ty.int 32), (Operand.reg "%arrayidx.val")),
                             ((Ty.int 32), (Operand.reg "%cast")),
                             (Ty.ptr, (Operand.reg "%out"))]]

/-- The return: the three arms' results. -/
def numElReturnInstrs : List Instr :=
  [
    Instr.phi "%retval.1" (Ty.int 32) [("if.then3", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.then18", (Operand.reg "%call")),
                                       ("if.end19", (Operand.reg "%call24"))]]

/-- `@num_el_el1`, as `probes/install/ir/stage2.callee.num_el_el1.ll` parses under
`numElLayout`. -/
def numElBody : Function :=
  { name := "num_el_el1",
    retTy := (Ty.int 32),
    params := [("%w", (Ty.int 64)),
               ("%q", (Ty.int 64)),
               ("%out", Ty.ptr)],
    blocks := [
      { name := "entry", instrs := numElEntryInstrs,
        term := Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4" },
      { name := "if.then3", instrs := numElIfThen3Instrs, term := Term.br "return" },
      { name := "if.end4", instrs := numElIfEnd4Instrs,
        term := Term.condbr (Operand.reg "%cmp15") "if.then18" "if.end19" },
      { name := "if.then18", instrs := numElIfThen18Instrs, term := Term.br "return" },
      { name := "if.end19", instrs := numElIfEnd19Instrs, term := Term.br "return" },
      { name := "return", instrs := numElReturnInstrs,
        term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.1")) }] }

/- The pin: the fixture parses to the literal above, under the declared layout. -/
#guard decide (firstFunctionWith numElLayout numElSrc = some numElBody)

/- The controls.  The same fixture with the fast path's mask constant changed
parses, and it is not the pinned body, so the equality above is about the text
rather than about a search that would accept anything. -/
def numElSrcMutated : String := numElSrc.replace ", 1023" ", 1022"

#guard decide (firstFunctionWith numElLayout numElSrcMutated ≠ some numElBody)

/- The layout is load-bearing in both directions: without an `EPow` entry the
fixture is refused — the struct's extent is not in the text — and with a wrong
extent it parses to a different body. -/
#guard decide (firstFunction numElSrc = none)

#guard decide (firstFunctionWith [("EPow", 32)] numElSrc ≠ some numElBody)

/- The shape, in the inventory's own vocabulary: `stage2.callees.tsv` counts
instruction *lines*; the pin's count is the parsed instructions. -/
#guard decide
  ((numElBody.name, numElBody.blocks.length,
      (numElBody.blocks.flatMap (·.instrs)).length, numElBody.params.length) =
    ("num_el_el1", 6, 35, 3))

/- The rewritten flag is the fixture's call's, and the emitted call is not: the
banner names `i1 true` in prose, so the check is on the call's spelling. -/
#guard hasSubstr numElSrc "@llvm.ctlz.i64(i64 %w, i1 false)"
#guard !hasSubstr numElSrc "@llvm.ctlz.i64(i64 %w, i1 true)"

/-! ### The block pins

Each block's run, read from the literal rather than from a re-reading of the
fixture's text: the six equations are what the pieces below consume. -/

theorem numEl_findBlock_entry :
    numElBody.findBlock "entry" =
      some ⟨"entry", numElEntryInstrs,
        Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4"⟩ := by decide

theorem numEl_findBlock_ifThen3 :
    numElBody.findBlock "if.then3" =
      some ⟨"if.then3", numElIfThen3Instrs, Term.br "return"⟩ := by decide

theorem numEl_findBlock_ifEnd4 :
    numElBody.findBlock "if.end4" =
      some ⟨"if.end4", numElIfEnd4Instrs,
        Term.condbr (Operand.reg "%cmp15") "if.then18" "if.end19"⟩ := by decide

theorem numEl_findBlock_ifThen18 :
    numElBody.findBlock "if.then18" =
      some ⟨"if.then18", numElIfThen18Instrs, Term.br "return"⟩ := by decide

theorem numEl_findBlock_ifEnd19 :
    numElBody.findBlock "if.end19" =
      some ⟨"if.end19", numElIfEnd19Instrs, Term.br "return"⟩ := by decide

theorem numEl_findBlock_return :
    numElBody.findBlock "return" =
      some ⟨"return", numElReturnInstrs,
        Term.ret (Ty.int 32) (some (Operand.reg "%retval.1"))⟩ := by decide

/-! ### The declared extent, against the text's own

The struct's extent is the one number the parser does not read from the body, so
it is checked against the places the body states it: the array's lane count is
91, and the exponent's byte offset is 16. -/

/-- The extent the layout declares is the size of the struct's four slots. -/
theorem numEl_structExtent : Ty.sizeBytes (.struct "EPow" 24) = 24 := by decide

/-- A resolved struct needs no further condition to scale a step. -/
theorem numEl_structAdmitted : Ty.gepElemAdmitted (.struct "EPow" 24) = true := by
  decide

/-- The array the emission indexes is 91 rows of 24 bytes. -/
theorem numEl_arrayExtent :
    Ty.sizeBytes (.array 91 (.struct "EPow" 24)) = 2184 := by decide

/-- The step the pinned `Instr.gep` makes at an index: `24 * i` bytes in. -/
theorem numEl_rowStride (i : Nat) :
    i * Ty.sizeBytes (.struct "EPow" 24) = 24 * i := by
  rw [numEl_structExtent, Nat.mul_comm]

/-- **The exponent's byte offset, against the text.**  The struct's first two
slots are eight bytes each, and the body's `if.end19` reads the exponent with a
byte `getelementptr` at exactly that offset: the constant the instruction carries
is the sum of the two limbs' `sizeBytes`. -/
theorem numEl_eOffset :
    Ty.sizeBytes (.int 64) + Ty.sizeBytes (.int 64) = 16 ∧
      Instr.gep "%3" (.int 8) (Operand.reg "%arrayidx") (Operand.imm (Const.int 64 16))
        ∈ numElIfEnd19Instrs := by
  refine ⟨by decide, by decide⟩

/-! ### The address

`%arrayidx = getelementptr inbounds [91 x %struct.EPow], ptr @EPOW, i64 0, i64 %sub`
reduces to the one-index struct step (the pinned `Instr.gep` above), and the
semantics' rule scales it by the declared extent. -/

/-- The row's address, as the model's `gep` computes it: the base plus `24` per
row, for an index whose sign-extended value is below `2 ^ 63`. -/
theorem numEl_rowAddr {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a w : Nat} {n : BitVec w}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d (.struct "EPow" 24) base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat * 24))) := by
  rw [evalInstr_gep hb ho hpos, numEl_structExtent]

/-- The same at an `i64` index, where the sign extension is the identity: the
index the emission passes is the row, and the address is `EPOW + 24 * %sub`. -/
theorem numEl_rowAddr_i64 {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a : Nat} {n : BitVec 64}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int 64 n)) (hpos : n.toNat < 2 ^ 63) :
    evalInstr calls s (.gep d (.struct "EPow" 24) base off) =
      some (s.bind d (.ptr (a + n.toNat * 24))) := by
  rw [numEl_rowAddr hb ho (by simpa using hpos)]
  simp

/-- The second `getelementptr` is a byte step: `16` bytes into the row. -/
theorem numEl_eAddr {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a : Nat} {n : BitVec 64}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int 64 n)) (hpos : n.toNat < 2 ^ 63) :
    evalInstr calls s (.gep d (.int 8) base off) =
      some (s.bind d (.ptr (a + n.toNat))) := by
  rw [evalInstr_gep_i8 hb ho (by simpa using hpos)]
  simp

/-! ### The guard slice

The body's `ub`, `hp`, `m` and `hh` are the model's, by the instructions that
compute them: `%shr7 = %conv6 >>> 63` is the top bit of the high word, `%or` is
the mask `2 ^ (10 + ub) - 1`, `%and` the slice below it, `%shr21` the quotient
above it and `%shl11` half the slice.  Each is stated as the natural its name
denotes, so the model's `Ahi / 2 ^ ub`, `Ahi % 2 ^ (10 + ub)` and `2 ^ (9 + ub)`
are the emitted values. -/

/-- `Ahi / 2 ^ 63` is at most one: the top bit's value. -/
theorem numEl_ub_le (Ahi : Nat) (h : Ahi < 2 ^ 64) : Ahi / 2 ^ 63 ≤ 1 := by
  have h2 : Ahi / 2 ^ 63 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)]
    have : (2 : Nat) * 2 ^ 63 = 2 ^ 64 := by decide
    omega
  omega

/-- `%or = (%shr7 << 10) | 1023` is `2 ^ (10 + ub) - 1` at a `ub` that is a bit. -/
theorem numEl_mask (ub : Nat) (h : ub ≤ 1) :
    (((BitVec.ofNat 64 ub) <<< 10) ||| (1023 : BitVec 64)).toNat = 2 ^ (10 + ub) - 1 := by
  have h01 : ub = 0 ∨ ub = 1 := by omega
  rcases h01 with rfl | rfl <;> decide

/-- A mask of `k` low bits is the remainder modulo `2 ^ k`. -/
theorem land_two_pow_sub_one (n k : Nat) : n &&& (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- `%and = %or &&& %conv6` keeps the low `10 + ub` bits: the guard slice `hp`. -/
theorem numEl_slice (Ahi : BitVec 64) (h : Ahi.toNat / 2 ^ 63 ≤ 1) :
    (Ahi &&& (((BitVec.ofNat 64 (Ahi.toNat / 2 ^ 63)) <<< 10) ||| (1023 : BitVec 64))).toNat
      = Ahi.toNat % 2 ^ (10 + Ahi.toNat / 2 ^ 63) := by
  rw [BitVec.toNat_and, numEl_mask (Ahi.toNat / 2 ^ 63) h, land_two_pow_sub_one]

/-- `%shr21 = %conv6 >>> (ub | 10)` is the quotient above the slice: on a bit
`ub`, `ub ||| 10` is `10 + ub`. -/
theorem numEl_shift (ub : Nat) (h : ub ≤ 1) : (10 ||| ub) = 10 + ub := by
  have h01 : ub = 0 ∨ ub = 1 := by omega
  rcases h01 with rfl | rfl <;> decide

/-- `%shl11 = 512 << ub` is half the slice. -/
theorem numEl_half (ub : Nat) (h : ub ≤ 1) :
    (((512 : BitVec 32) <<< ub)).toNat = 2 ^ (9 + ub) := by
  have h01 : ub = 0 ∨ ub = 1 := by omega
  rcases h01 with rfl | rfl <;> decide

/-! ### The window test

The emitted test wraps twice: `%reass.sub = %and - %conv12` is an `i64`
subtraction whose true difference may be negative, and `%sub14 = %reass.sub + 2`
adds two back before the unsigned comparison.  At a slice below `2 * hh` the
wrapped value is at most two exactly in the three-value window, which is
`ElGuardRefine.inWindow` — the model's `hh ≤ hp + 2 ∧ hp ≤ hh`. -/

/-- The emitted wrapped test is the guard's `inWindow` at the same two words. -/
theorem numEl_window (hp hh : Nat) (hh2 : 2 ≤ hh) (hhle : hh ≤ 2 ^ 11)
    (hlt : hp < 2 ^ 64) :
    ((((hp + 2 ^ 64 - hh) % 2 ^ 64 + 2) % 2 ^ 64) ≤ 2)
      ↔ LeanLLVM.ElGuardRefine.inWindow hp hh = true := by
  have hX : hp + 2 ^ 64 - hh + 2 = hp + 2 ^ 64 - (hh - 2) := by omega
  have hstep : ((hp + 2 ^ 64 - hh) % 2 ^ 64 + 2) % 2 ^ 64
      = (hp + 2 ^ 64 - hh + 2) % 2 ^ 64 := by
    rw [Nat.add_mod (hp + 2 ^ 64 - hh) 2 (2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 2 < 2 ^ 64)]
  rw [hstep, hX, LeanLLVM.ElGuardRefine.inWindow, decide_eq_true_eq]

/-! ### The ctlz flag

Three facts make the capture's one rewrite sound, and they are the body's own
structure rather than an assumption about it. -/

/-- The nonzero word's test is clear. -/
theorem numEl_test_nonzero {w : BitVec 64} (h : w ≠ 0) :
    evalICmp .eq w (0 : BitVec 64) = (0 : BitVec 1) := by
  have hb : decide (w = (0 : BitVec 64)) = false := by
    rw [decide_eq_false_iff_not]
    exact h
  simp only [evalICmp, hb, BitVec.ofBool_false]

/-- The zero word's test is set. -/
theorem numEl_test_zero : evalICmp .eq (0 : BitVec 64) (0 : BitVec 64) = (1 : BitVec 1) := by
  decide

/-- The entry's test: `%cmp2 = icmp eq i64 %w, 0` is set exactly at the zero
word, so its clear value is "`%w` is nonzero". -/
theorem numEl_entry_test (w : BitVec 64) :
    (evalICmp .eq w (0 : BitVec 64) = (1 : BitVec 1) ↔ w = 0) := by
  by_cases hw : w = 0
  · subst hw
    rw [numEl_test_zero]
    simp
  · rw [numEl_test_nonzero hw]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h hw⟩

/-- The entry terminator takes its false edge exactly at a clear condition. -/
theorem numEl_entry_cond_false (s : State)
    (h : evalOperand s (Operand.reg "%cmp2") = some (.int 1 (0 : BitVec 1))) :
    execTerm s (Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4") =
      .jump { s with pc := "if.end4", pre := some s.pc } := by
  have hstep : execTerm s (Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4") =
      (match evalOperand s (Operand.reg "%cmp2") with
       | some (.int 1 bit) =>
           if bit = (1 : BitVec 1) then .jump { s with pc := "if.then3", pre := some s.pc }
           else if bit = (0 : BitVec 1) then .jump { s with pc := "if.end4", pre := some s.pc }
           else .ub
       | _ => .ub) := rfl
  rw [hstep, h]
  simp

/-- `if.end4` is entered from `entry` and nowhere else: the pinned body's terms
name it once, as the entry's false target. -/
theorem numEl_end4_only_from_entry :
    (numElBody.blocks.map fun b =>
      (b.name, match b.term with
        | .br l => l == "if.end4"
        | .condbr _ t f => t == "if.end4" || f == "if.end4"
        | _ => false)).filter (fun p => p.2) = [("entry", true)] := by
  decide

/-- **The flag's poison is unobserved.**  A state at `entry` whose `%cmp2` is the
entry test's result can reach `if.end4` only through the terminator above, whose
premise is a clear condition — `%w ≠ 0` — so the emitted `i1 true` and the
fixture's `i1 false` agree at every call the body makes. -/
theorem numEl_flag_domain (s : State) (w : BitVec 64)
    (hcmp : evalOperand s (Operand.reg "%cmp2") = some (.int 1 (evalICmp .eq w 0)))
    (hclear : evalICmp .eq w 0 = (0 : BitVec 1)) :
    w ≠ 0 ∧ execTerm s (Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4") =
      .jump { s with pc := "if.end4", pre := some s.pc } := by
  refine ⟨fun hw => ?_, numEl_entry_cond_false s (by rw [hcmp, hclear])⟩
  subst hw
  rw [numEl_test_zero] at hclear
  exact absurd hclear (by decide)

/-! ### The staging: the table's row and the counter's word

The fixture names `@EPOW` and `@g_el_window` and declares neither: the `define`
extraction has no globals, and the `Calls` boundary has no table.  Their
addresses are the run's staging (`Globals`), and the bytes behind `@EPOW` are the
row's — the record `epow_table.h` holds, little-endian as the loads read it. -/

/-- The `int32_t` slot's 32-bit word: the low four bytes of the two's-complement
value, so a negative exponent's `0xFFFF_FFxx` is the word the slot holds. -/
def epowEWord (e : Int) : Nat := (e % (2 ^ 32 : Int)).toNat

/-- The exponent's slot is a 32-bit word. -/
theorem epowEWord_lt (e : Int) : epowEWord e < 2 ^ 32 := by
  unfold epowEWord
  have hpos : (0 : Int) < (2 ^ 32 : Int) := by decide
  have hlt := Int.emod_lt_of_pos e hpos
  have hge := Int.emod_nonneg e (by decide : (2 ^ 32 : Int) ≠ 0)
  omega

/-- One `EPOW` row's 24 bytes: the two limbs, the exponent's word and the four
padding bytes the emission's slot leaves zero. -/
def epowRowBytes (t : EPow) : List UInt8 :=
  natToBytes t.hi 8 ++ natToBytes t.lo 8 ++ natToBytes (epowEWord t.e) 4 ++ [0, 0, 0, 0]

/-- The row as the body reads it: the `i64` at the row's address, the `i64` at
its eighth byte, the `i32` at its sixteenth and the four padding bytes.  This is
the staging, stated at the four reads the body and its callee make. -/
structure NumElRow (mem : Mem) (a : Nat) (t : EPow) : Prop where
  /-- `t->hi`, the `load i64` the deferred kernel makes at the row. -/
  hi : readBytes mem a 8 = some (natToBytes t.hi 8)
  /-- `t->lo`, which `el_exact` reads at the row's eighth byte. -/
  lo : readBytes mem (a + 8) 8 = some (natToBytes t.lo 8)
  /-- `t->e`, the `load i32` at the byte `getelementptr i8 … 16` names. -/
  e : readBytes mem (a + 16) 4 = some (natToBytes (epowEWord t.e) 4)
  /-- The slot's padding, zero as the emission's table leaves it. -/
  pad : readBytes mem (a + 20) 4 = some [0, 0, 0, 0]

/-- The four reads are the 24-byte record: `el_exact`'s third argument is a
pointer to the row, and the row's bytes are what the staging holds behind it. -/
theorem NumElRow.row {mem : Mem} {a : Nat} {t : EPow} (h : NumElRow mem a t) :
    readBytes mem a 24 = some (epowRowBytes t) := by
  have he : readBytes mem (a + 8 + 8) 4 = some (natToBytes (epowEWord t.e) 4) := by
    rw [show a + 8 + 8 = a + 16 from by omega]
    exact h.e
  have hpad : readBytes mem ((a + 8) + (8 + 4)) 4 = some [0, 0, 0, 0] := by
    rw [show (a + 8) + (8 + 4) = a + 20 from by omega]
    exact h.pad
  have h16 : readBytes mem (a + 8) 16 =
      some (natToBytes t.lo 8 ++ (natToBytes (epowEWord t.e) 4 ++ [0, 0, 0, 0])) := by
    have h1 : readBytes mem (a + 8) (8 + 4) =
        some (natToBytes t.lo 8 ++ natToBytes (epowEWord t.e) 4) :=
      JsonEntrySteps.readBytes_append mem 8 (a + 8) _ 4 _ h.lo he
    have h2 : readBytes mem (a + 8) (8 + 4 + 4) =
        some ((natToBytes t.lo 8 ++ natToBytes (epowEWord t.e) 4) ++ [0, 0, 0, 0]) :=
      JsonEntrySteps.readBytes_append mem (8 + 4) (a + 8) _ 4 _ h1 hpad
    rw [show (8 + 4 + 4 : Nat) = 16 from rfl] at h2
    simpa [List.append_assoc] using h2
  have h24 : readBytes mem a (8 + 16) =
      some (natToBytes t.hi 8 ++
        (natToBytes t.lo 8 ++ (natToBytes (epowEWord t.e) 4 ++ [0, 0, 0, 0]))) :=
    JsonEntrySteps.readBytes_append mem 8 a (natToBytes t.hi 8) 16
      (natToBytes t.lo 8 ++ (natToBytes (epowEWord t.e) 4 ++ [0, 0, 0, 0])) h.hi h16
  rw [show (8 + 16 : Nat) = 24 from rfl] at h24
  simpa [epowRowBytes] using h24

/-- The `load i64` at the row is the row's `hi` word. -/
theorem numEl_load_hi {mem : Mem} {a : Nat} {t : EPow} (h : NumElRow mem a t)
    (hhi : t.hi < 2 ^ 64) :
    loadValue mem (.int 64) a = some (.int 64 (BitVec.ofNat 64 t.hi)) := by
  have hlt : t.hi < 256 ^ 8 := by
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
    exact hhi
  have h64 : (64 = 0) = False := by decide
  simp only [loadValue, h.hi, h64, ite_false]
  rw [bytesToNat_natToBytes hlt]

/-- The `load i32` sixteen bytes into the row is the row's exponent word. -/
theorem numEl_load_e {mem : Mem} {a : Nat} {t : EPow} (h : NumElRow mem a t) :
    loadValue mem (.int 32) (a + 16) = some (.int 32 (BitVec.ofNat 32 (epowEWord t.e))) := by
  have hlt : epowEWord t.e < 256 ^ 4 := by
    rw [show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]
    exact epowEWord_lt t.e
  have h32 : (32 = 0) = False := by decide
  simp only [loadValue, h.e, h32, ite_false]
  rw [bytesToNat_natToBytes hlt]

/-- The run's global staging: the table's address and the window counter's.  The
addresses are the staging's choice; they lie outside `null` and outside the
allocator's range, at a distance of more than the table's 2184 bytes, as
`Globals` requires. -/
def numElGlobals : Globals := [("@EPOW", 0x100000), ("@g_el_window", 0x200000)]

/-- The staging binds the table's symbol. -/
theorem numEl_globals_EPOW : lookupName numElGlobals "@EPOW" = some 0x100000 := rfl

/-- The staging binds the counter's symbol. -/
theorem numEl_globals_window : lookupName numElGlobals "@g_el_window" = some 0x200000 := rfl

/-- The two staged regions do not overlap. -/
theorem numEl_globals_disjoint : 0x100000 + 2184 ≤ 0x200000 := by decide

/-! ### Axiom footprints

Pinned with `#guard_msgs` so the build checks the footprints rather than printing
them.  The instrument is `#print axioms`; a declaration proved with `sorry` prints
`sorryAx` under the same command, which is the control the tree records. -/

/-- info: 'LeanLLVM.Refinement.numEl_structExtent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numEl_structExtent

/-- info: 'LeanLLVM.Refinement.numEl_rowAddr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numEl_rowAddr

/-- info: 'LeanLLVM.Refinement.land_two_pow_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms land_two_pow_sub_one

/-- info: 'LeanLLVM.Refinement.numEl_entry_test' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numEl_entry_test

/-- info: 'LeanLLVM.Refinement.numEl_load_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numEl_load_hi

/-- info: 'LeanLLVM.Refinement.NumElRow.row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NumElRow.row

end LeanLLVM.Refinement
