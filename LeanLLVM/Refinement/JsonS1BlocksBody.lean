/-
The block unit's loop body, at the emitted body's own registers.

`JsonS1BlocksIR` pins the nine-block body; `JsonS1BlocksRun` proves the traces of
the blocks that are not the classifier's vector arithmetic.  This module is the
rest: the loop body and the peeled tail, their value identities against
`JsonScanSpec`'s words, and the composition of the two escape arms.

The body's classifier arithmetic is the mask unit's, at registers the block unit
renames: `%or.i99` is `JsonS1MasksSteps.qrawW`'s raw quote word, `%or14.i` is its
backslash word, `%xor.i` its in-string word, and the escape arithmetic is the same
register chain.  The one word the block unit computes that the mask unit does not
is the *neither* word: the body never forms the whitespace mask, and instead joins
the two table words, compares the join with zero, and calls the result `%or23.i`.
`neitherW` names it.  Its identification with `~~~(or5W ||| orWsW)` is owed: the
word's identity is not stated here yet.

`bodyInstrs` is the body's instruction list at constructor spelling and is pinned
to `bodyBlock.instrs` by `rfl`, so a trace below is a proof about the literal
list; the AST's own link to the fixture is `JsonS1BlocksIR`'s `#guard`, which
parses the committed text and decides it equals the AST.  A change to the fixture
without the AST fails the `#guard`; a change to the AST without this list fails
the `rfl`.  The six leading `phi`s are traced (`phi_denote`), and the cell steps
of the quote/backslash prefix and the rest of the body are present
(`b_quote` … `b_andQuote`, `b_neither` onwards); what is owed is their
composition into the body's `denoteCode` run.

## The reuse boundary

The mask unit's step lemmas are stated at `s1Calls` and `withEnv`, while the block
unit runs `s1BlocksCalls` at `stateAt`.  `evalInstr`'s only arms that consult the
call environment are the two call forms, so an instruction that mentions no call
evaluates identically at any pair of environments: `evalInstr_calls_irrelevance`,
with `callsInstr` deciding the premise, and `evalInstr_blocks_of_masks` composing
it with the environment bridge.  One lemma therefore covers every reused step,
which is why the wrappers are not written: a wrapper per reused instruction would
duplicate a proof whose only varying part is the environment argument, and a new
step would need a new wrapper before it could be used.
-/
import LeanLLVM.Refinement.JsonS1BlocksRun
import LeanLLVM.Refinement.JsonEntSpec

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.Pclmul (clmul)
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### The reuse boundary

The mask unit's steps are stated at its own call environment; these two lemmas
move one to this unit's without restating it. -/

/-- Whether evaluating an instruction consults the call environment.  Only the two
call forms do; every other arm of `evalInstr` computes from the state alone. -/
def callsInstr : Instr → Bool
  | .call _ _ _ _ => true
  | .callVoid _ _ => true
  | _ => false

/-- **Evaluation ignores the call environment** for an instruction that makes no
call: the two environments differ only in the `calls` argument, which no other
arm of `evalInstr` reads. -/
theorem evalInstr_calls_irrelevance (c₁ c₂ : Calls) (s : State) (i : Instr)
    (h : callsInstr i = false) : evalInstr c₁ s i = evalInstr c₂ s i := by
  cases i <;> simp_all [evalInstr, callsInstr]

/-- The two environment constructors are one: `withEnv` and `stateAt` both replace
the state's environment and carry every other field through. -/
theorem withEnv_eq_stateAt (env : Env) (s : State) : withEnv env s = stateAt env s := rfl

/-- **A mask-unit step at this unit's environment.**  An instruction that mentions
no call evaluates the same at `s1BlocksCalls`/`stateAt` as at
`s1Calls`/`withEnv`, so a step lemma stated at the mask unit's environment is this
unit's step. -/
theorem evalInstr_blocks_of_masks (env : Env) (s : State) (i : Instr)
    (h : callsInstr i = false) :
    evalInstr s1BlocksCalls (stateAt env s) i = evalInstr s1Calls (withEnv env s) i := by
  rw [← withEnv_eq_stateAt]
  exact evalInstr_calls_irrelevance _ _ _ _ h

/-- The same bridge with `withEnv` on both sides: a run that a mask-unit step has
already left in `withEnv` form continues at `s1BlocksCalls` the same way. -/
theorem evalInstr_blocks_of_masks_w (env : Env) (s : State) (i : Instr)
    (h : callsInstr i = false) :
    evalInstr s1BlocksCalls (withEnv env s) i = evalInstr s1Calls (withEnv env s) i := by
  rw [withEnv_eq_stateAt]
  exact evalInstr_blocks_of_masks env s i h

/-! ### Instruction spelling -/

/-- A 64-bit literal. -/
def lit64 (v : Int) : Operand := .imm (.int 64 (BitVec.ofInt 64 v))

/-- A 32-bit literal. -/
def lit32 (v : Int) : Operand := .imm (.int 32 (BitVec.ofInt 32 v))

/-- A splat of `i8`s. -/
def splat8 (n : Nat) (v : Int) : Operand := .imm (.splat n 8 (BitVec.ofInt 8 v))

/-- A splat of `i16`s. -/
def splat16 (v : Int) : Operand := .imm (.splat 16 16 (BitVec.ofInt 16 v))

/-- A splat of `i64`s. -/
def splat64 (n : Nat) (v : Int) : Operand := .imm (.splat n 64 (BitVec.ofInt 64 v))

/-- A lane list of `i64`s. -/
def lanes64 (vs : List Int) : Operand := .imm (.vector 64 (vs.map (BitVec.ofInt 64)))

/-- The four-lane tables the shuffled quote and control words are read at. -/
def shuffle8 (dst : String) : Instr :=
  .shuffleVec dst 4 64 (reg "%0") (reg "%1") [0, 1, 2, 3, 4, 5, 6, 7]

/-- A `pshuf.b` lookup at a table the emission spells as a literal. -/
def pshufbBlock (dst : String) (tab : List Int) (v : Operand) : Instr :=
  .call dst (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b"
    [(.vec 32 (.int 8), .imm (.vector 8 (tab.map (BitVec.ofInt 8)))),
     (.vec 32 (.int 8), v)]

/-! ### The body's list -/

/-- `for.body` at constructor spelling. -/
def bodyInstrs : List Instr := [
  .phi "%prevS.0180" (.int 64)
    [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr16")],
  .phi "%ascii.0179" (.vec 4 (.int 64))
    [("for.body.lr.ph", splat64 4 0), ("if.end", reg "%or.i97")],
  .phi "%i.0178" (.int 64)
    [("for.body.lr.ph", lit64 0), ("if.end", reg "%inc")],
  .phi "%st.sroa.0.0177" (.int 64)
    [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr.i.i")],
  .phi "%st.sroa.7.0176" (.int 64)
    [("for.body.lr.ph", lit64 0), ("if.end", reg "%conv13.i.i")],
  .phi "%st.sroa.11.0175" (.int 64)
    [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr.i")],
  .binop "%shl" .shl 64 (reg "%i.0178") (lit64 6),
  .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
  .load "%0" (.vec 4 (.int 64)) (reg "%add.ptr"),
  .gep "%add.ptr2" (.int 8) (reg "%add.ptr") (lit64 32),
  .load "%1" (.vec 4 (.int 64)) (reg "%add.ptr2"),
  .binopVec "%or.i98" .or 4 64 (reg "%0") (reg "%ascii.0179"),
  .binopVec "%or.i97" .or 4 64 (reg "%or.i98") (reg "%1"),
  .vecBitcast "%2" 4 64 32 8 (reg "%0"),
  .vecBitcast "%3" 4 64 32 8 (reg "%1"),
  shuffle8 "%4",
  .vecBitcast "%5" 8 64 64 8 (reg "%4"),
  .icmpVec "%6" .eq 64 8 (reg "%5") (splat8 64 34),
  .bitcastMask "%or.i99" 64 (reg "%6"),
  .icmpVec "%cmp.i39.i" .eq 32 8 (reg "%2") (splat8 32 92),
  .bitcastMask "%7" 32 (reg "%cmp.i39.i"),
  .zext "%conv9.i" 32 64 (reg "%7"),
  .icmpVec "%cmp.i.i" .eq 32 8 (reg "%3") (splat8 32 92),
  .bitcastMask "%8" 32 (reg "%cmp.i.i"),
  .zext "%conv12.i" 32 64 (reg "%8"),
  .binop "%shl13.i" .shl 64 (reg "%conv12.i") (lit64 32),
  .binop "%or14.i" .or 64 (reg "%shl13.i") (reg "%conv9.i"),
  .binop "%and.i.i" .and 64 (reg "%st.sroa.0.0177") (reg "%st.sroa.7.0176"),
  .binop "%shl.i.i" .shl 64 (reg "%or14.i") (lit64 1),
  .binop "%not.i.i" .xor 64 (reg "%shl.i.i") (lit64 (-1)),
  .binop "%and1.i.i" .and 64 (reg "%or14.i") (reg "%not.i.i"),
  .binop "%xor.i.i" .xor 64 (reg "%and.i.i") (lit64 0x5555555555555555),
  .binop "%and2.i.i" .and 64 (reg "%and1.i.i") (reg "%xor.i.i"),
  .binop "%xor3.i.i" .xor 64 (reg "%and2.i.i") (reg "%and1.i.i"),
  .binop "%not4.i.i" .xor 64 (reg "%or14.i") (lit64 (-1)),
  .binop "%add.i.i" .add 64 (reg "%and2.i.i") (reg "%or14.i"),
  .binop "%add5.i.i" .add 64 (reg "%xor3.i.i") (reg "%or14.i"),
  .binop "%and6.i.i" .and 64 (reg "%not4.i.i") (lit64 (-6148914691236517206)),
  .binop "%and7.i.i" .and 64 (reg "%and6.i.i") (reg "%add.i.i"),
  .binop "%and8.i.i" .and 64 (reg "%not4.i.i") (lit64 6148914691236517205),
  .binop "%and9.i.i" .and 64 (reg "%and8.i.i") (reg "%add5.i.i"),
  .binop "%and11.i.i" .and 64 (reg "%and.i.i") (reg "%not4.i.i"),
  .binop "%or.i.i" .or 64 (reg "%and7.i.i") (reg "%and11.i.i"),
  .binop "%or12.i.i" .or 64 (reg "%or.i.i") (reg "%and9.i.i"),
  .icmp "%cmp.i45.i" .ult 64 (reg "%add5.i.i") (reg "%or14.i"),
  .zext "%conv13.i.i" 1 64 (reg "%cmp.i45.i"),
  .binop "%shr.i.i" .lshr 64 (reg "%conv12.i") (lit64 31),
  .binop "%not.i" .xor 64 (reg "%or12.i.i") (lit64 (-1)),
  .binop "%and.i" .and 64 (reg "%or.i99") (reg "%not.i"),
  .vecBitcast "%9" 4 64 16 16 (reg "%0"),
  .binopVec "%10" .lshr 16 16 (reg "%9") (splat16 4),
  .binopVec "%11" .and 32 8 (reg "%2") (splat8 32 15),
  pshufbBlock "%12" JsonS1BlocksIR.loTab (reg "%11"),
  .vecBitcast "%13" 16 16 32 8 (reg "%10"),
  .binopVec "%14" .and 32 8 (reg "%13") (splat8 32 15),
  pshufbBlock "%15" JsonS1BlocksIR.hiTab (reg "%14"),
  .binopVec "%and.i2326.i.i" .and 32 8 (reg "%15") (reg "%12"),
  .binopVec "%16" .and 32 8 (reg "%and.i2326.i.i") (splat8 32 63),
  .icmpVec "%cmp.i21.i.i" .eq 32 8 (reg "%16") (splat8 32 0),
  .bitcastMask "%17" 32 (reg "%cmp.i21.i.i"),
  .binop "%not.i46.i" .xor 32 (reg "%17") (lit32 (-1)),
  .vecBitcast "%18" 4 64 16 16 (reg "%1"),
  .binopVec "%19" .lshr 16 16 (reg "%18") (splat16 4),
  .binopVec "%20" .and 32 8 (reg "%3") (splat8 32 15),
  pshufbBlock "%21" JsonS1BlocksIR.loTab (reg "%20"),
  .vecBitcast "%22" 16 16 32 8 (reg "%19"),
  .binopVec "%23" .and 32 8 (reg "%22") (splat8 32 15),
  pshufbBlock "%24" JsonS1BlocksIR.hiTab (reg "%23"),
  .binopVec "%and.i2326.i47.i" .and 32 8 (reg "%24") (reg "%21"),
  .binopVec "%25" .and 32 8 (reg "%and.i2326.i47.i") (splat8 32 63),
  .icmpVec "%cmp.i21.i48.i" .eq 32 8 (reg "%25") (splat8 32 0),
  .bitcastMask "%26" 32 (reg "%cmp.i21.i48.i"),
  .binop "%not.i49.i" .xor 32 (reg "%26") (lit32 (-1)),
  .zext "%conv16.i" 32 64 (reg "%not.i46.i"),
  .zext "%conv17.i" 32 64 (reg "%not.i49.i"),
  .binop "%shl18.i" .shl 64 (reg "%conv17.i") (lit64 32),
  .binop "%or19.i" .or 64 (reg "%shl18.i") (reg "%conv16.i"),
  .shuffleVec "%27" 32 8 (reg "%and.i2326.i.i") (reg "%and.i2326.i47.i")
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
     16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
     32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
     48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
  .icmpVec "%28" .eq 64 8 (reg "%27") (splat8 64 0),
  .bitcastMask "%or23.i" 64 (reg "%28"),
  .insertelement "%vecinit1.i.i.i" 2 64 (.imm (.splat 2 64 (BitVec.ofNat 64 0)))
    (reg "%and.i") (lit64 0),
  .call "%29" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
    [(.vec 2 (.int 64), reg "%vecinit1.i.i.i"),
     (.vec 2 (.int 64), lanes64 [-1, 0]), (.int 8, .imm (.int 8 (BitVec.ofInt 8 0)))],
  .extractelement "%vecext.i.i.i" 2 64 (reg "%29") (lit64 0),
  .binop "%xor.i" .xor 64 (reg "%vecext.i.i.i") (reg "%st.sroa.11.0175"),
  .binop "%shr.i" .ashr 64 (reg "%xor.i") (lit64 63),
  .binop "%not7" .xor 64 (reg "%xor.i") (lit64 (-1)),
  .binop "%30" .or 64 (reg "%and.i") (reg "%xor.i"),
  .binop "%31" .xor 64 (reg "%30") (lit64 (-1)),
  .binop "%and8" .and 64 (reg "%or23.i") (reg "%31"),
  .binop "%and10" .and 64 (reg "%or19.i") (reg "%not7"),
  .binop "%shl11" .shl 64 (reg "%and8") (lit64 1),
  .binop "%or12" .or 64 (reg "%shl11") (reg "%prevS.0180"),
  .binop "%not13" .xor 64 (reg "%or12") (lit64 (-1)),
  .binop "%and14" .and 64 (reg "%and8") (reg "%not13"),
  .binop "%32" .or 64 (reg "%and10") (reg "%and14"),
  .binop "%or15" .or 64 (reg "%32") (reg "%and.i"),
  .binop "%shr16" .lshr 64 (reg "%and8") (lit64 63),
  .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.0178"),
  .store (.int 64) (reg "%or15") (reg "%arrayidx")]

theorem bodyInstrs_eq : bodyInstrs = bodyBlock.instrs := rfl

/-! ### The body's values

The classifier words are `JsonS1MasksSteps`'s, at the block unit's registers.  The
words unique to this body are the neither word, the folded escape chain that omits
the mask unit's `%and10`, and the entry word. -/

/-- The block index shifted by six: the block's byte offset. -/
def shl6W (i : BitVec 64) : BitVec 64 := i <<< 6

/-- The loop body's first load address. -/
def ptrB (b : Nat) (i : BitVec 64) : Nat := b + (shl6W i).toNat

/-- One lane-wise OR of two `<4 x i64>` values. -/
def orLanes (a b : List (BitVec 64)) : List (BitVec 64) :=
  (a.zip b).map fun p => p.1 ||| p.2

/-- `%or.i98`: the low half folded into the accumulator. -/
def ascii1Lanes (k : Ctx) (a : List (BitVec 64)) : List (BitVec 64) :=
  orLanes (unpackLanes 64 4 (loWord k)) a

/-- `%or.i97`: the high half folded into the accumulator. -/
def ascii2Lanes (k : Ctx) (a : List (BitVec 64)) : List (BitVec 64) :=
  orLanes (ascii1Lanes k a) (unpackLanes 64 4 (hiWord k))

/-- `%28`'s lanes: zero exactly where the byte carries neither a structural nor a
whitespace bit. -/
def neitherLanes (k : Ctx) : List (BitVec 1) :=
  ((andWordLanes k ++ andWordLanesHi k).zip
    (List.replicate 64 (BitVec.ofInt 8 0))).map fun p => evalICmp .eq p.1 p.2

/-- `%or23.i`: the neither word. -/
def neitherW (k : Ctx) : BitVec 64 := BitVec.ofNat 64 (lanesToNat (neitherLanes k))

/-- `%and11.i.i`: the emitted chain's shortcut, `and00 & ~backslash`. -/
def blkAnd11W (k : Ctx) : BitVec 64 := bv (escAnd00W k &&& escNotBsW k)

/-- `%or.i.i`: the emitted chain's `s1f_escaped` join. -/
def blkOr62W (k : Ctx) : BitVec 64 := bv (escAnd7W k ||| blkAnd11W k)

/-- `%or12.i.i`: the escape word the emitted chain leaves. -/
def blkEscapedW (k : Ctx) : BitVec 64 := bv (blkOr62W k ||| escAnd9W k)

/-- `%not.i`: the escape word's complement. -/
def blkNotEscW (k : Ctx) : BitVec 64 := bv (blkEscapedW k ^^^ BitVec.allOnes 64)

/-- `%and.i`: the unescaped quote word. -/
def blkAndQuoteW (k : Ctx) : BitVec 64 := bv (qrawW k &&& blkNotEscW k)

/-- `%vecinit1.i.i.i`. -/
def blkVecInitLanes (k : Ctx) : List (BitVec 64) := [blkAndQuoteW k, 0]

/-- `%29`. -/
def blkPclmulLanes (k : Ctx) : List (BitVec 64) :=
  [clmul (blkAndQuoteW k) (BitVec.allOnes 64), 0]

/-- `%vecext.i.i.i`. -/
def blkVecextW (k : Ctx) : BitVec 64 := clmul (blkAndQuoteW k) (BitVec.allOnes 64)

/-- `%not7`. -/
def notXorW (k : Ctx) : BitVec 64 := bv (inStringWord k ^^^ BitVec.allOnes 64)

/-- `%30`. -/
def orQImW (k : Ctx) : BitVec 64 := bv (andQuoteW k ||| inStringWord k)

/-- `%31`. -/
def notQImW (k : Ctx) : BitVec 64 := bv (orQImW k ^^^ BitVec.allOnes 64)

/-- The scalar word `S`, the lanes neither structural, quote nor in a string, in
the mask unit's words.  That these are the body's `%and8` is an owed value
identity, not this definition: the body computes it from `neitherW`, and the
definition states the word, not the register. -/
def scalarW (k : Ctx) : BitVec 64 := bv (neitherW k &&& notQImW k)

/-- `%and10`: the delimiter outside a string. -/
def delimNotImW (k : Ctx) : BitVec 64 := bv (or5W k &&& notXorW k)

/-- `%shl11`. -/
def shlScalarW (k : Ctx) : BitVec 64 := bv (scalarW k <<< 1)

/-- `%or12`. -/
def orPrevW (k : Ctx) (p : BitVec 64) : BitVec 64 := bv (shlScalarW k ||| p)

/-- `%not13`. -/
def notOrPrevW (k : Ctx) (p : BitVec 64) : BitVec 64 :=
  bv (orPrevW k p ^^^ BitVec.allOnes 64)

/-- `%and14`. -/
def andScalarW (k : Ctx) (p : BitVec 64) : BitVec 64 :=
  bv (scalarW k &&& notOrPrevW k p)

/-- `%32`. -/
def or32W (k : Ctx) (p : BitVec 64) : BitVec 64 :=
  bv (delimNotImW k ||| andScalarW k p)

/-- `%or15`: the entry word the body stores. -/
def entryW (k : Ctx) (p : BitVec 64) : BitVec 64 :=
  bv (or32W k p ||| andQuoteW k)

/-- `%shr16`: the block's top scalar lane, the next block's `prevS`. -/
def prevOutW (k : Ctx) : BitVec 64 := bv (scalarW k >>> 63)

/-- The `ent` slot the body stores at. -/
def entAddr (ent : Nat) (i : BitVec 64) : Nat := ent + i.toNat * 8

/-! ### Integer and conversion steps -/

theorem step_binop_v (calls : Calls) (env : Env) (s : State) (d : String)
    (bop : BinOp) (a b : String) (x y r : BitVec 64)
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y))
    (hr : evalBinopNat bop 64 x.toNat y.toNat = some r.toNat) :
    evalInstr calls (stateAt env s) (.binop d bop 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 r) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := x) (y := y) (r := r.toNat)
    (ha := by simp only [stateAt, evalOperand, ha])
    (hb := by simp only [stateAt, evalOperand, hb]) hr]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem step_binop_imm (calls : Calls) (env : Env) (s : State) (d : String)
    (bop : BinOp) (a : String) (ci x r : BitVec 64)
    (ha : lookupName env a = some (.int 64 x))
    (hr : evalBinopNat bop 64 x.toNat ci.toNat = some r.toNat) :
    evalInstr calls (stateAt env s) (.binop d bop 64 (.reg a) (.imm (.int 64 ci))) =
      some (stateAt ((d, .int 64 r) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := x) (y := ci) (r := r.toNat)
    (ha := by simp only [stateAt, evalOperand, ha])
    (hb := by simp only [stateAt, evalOperand, Const.toValue]) hr]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem step_icmp_v (calls : Calls) (env : Env) (s : State) (d : String)
    (pred : IPred) (a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.icmp d pred 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp pred x y)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmp (x := x) (y := y)
    (ha := by simp only [stateAt, evalOperand, ha])
    (hb := by simp only [stateAt, evalOperand, hb])]
  simp only [stateAt, State.bind]

theorem step_zext32 (calls : Calls) (env : Env) (s : State) (d a : String)
    (x : BitVec 32) (ha : lookupName env a = some (.int 32 x)) :
    evalInstr calls (stateAt env s) (.zext d 32 64 (.reg a)) =
      some (stateAt ((d, .int 64 (zext64W x)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_zext (x := x) (hv := by simp only [stateAt, evalOperand, ha])]
  simp only [stateAt, State.bind, zext64W]

theorem step_zext1 (calls : Calls) (env : Env) (s : State) (d a : String)
    (x : BitVec 1) (ha : lookupName env a = some (.int 1 x)) :
    evalInstr calls (stateAt env s) (.zext d 1 64 (.reg a)) =
      some (stateAt ((d, .int 64 (BitVec.ofNat 64 x.toNat)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_zext (x := x) (hv := by simp only [stateAt, evalOperand, ha])]
  simp only [stateAt, State.bind]

theorem step_gep8_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {o : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 o)) (h : o.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + o.toNat)) :: env) s) := by
  have h2 : o.toNat < 9223372036854775808 := by
    rw [show (9223372036854775808 : Nat) = 2 ^ 63 from by decide]; exact h
  simp [stateAt, State.bind, evalInstr, evalOperand, hb, ho, h2, Ty.sizeBytes]

theorem step_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat} (hb : lookupName env base = some (.ptr a))
    (h : c.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a + c.toNat)) :: env) s) := by
  have h2 : c.toNat < 9223372036854775808 := by
    rw [show (9223372036854775808 : Nat) = 2 ^ 63 from by decide]; exact h
  simp [stateAt, State.bind, evalInstr, evalOperand, Const.toValue, hb, h2, Ty.sizeBytes]

theorem step_gep64_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {o : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 o)) (h : o.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 64) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + o.toNat * 8)) :: env) s) := by
  have h2 : o.toNat < 9223372036854775808 := by
    rw [show (9223372036854775808 : Nat) = 2 ^ 63 from by decide]; exact h
  simp [stateAt, State.bind, evalInstr, evalOperand, hb, ho, h2, Ty.sizeBytes]

theorem step_load_vec4 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {bs : List UInt8} (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some bs) :
    evalInstr calls (stateAt env s) (.load d (.vec 4 (.int 64)) (.reg p)) =
      some (stateAt ((d, .vec 4 64 (unpackLanes 64 4 (bytesToNat bs))) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_load (p := .reg p) (a := a)
    (hp := by simp only [stateAt, evalOperand, hp])
    (loadValue_vec_int (by decide) (by decide) hr)]
  rfl

theorem step_store64 (calls : Calls) (env : Env) (s : State) (r p : String)
    (x : BitVec 64) {a : Nat} (hv : lookupName env r = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 64) (.reg r) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [JsonS1MasksIR.evalInstr_store (vv := .int 64 x) (a := a)
    (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
    (hv := by simp only [stateAt, evalOperand, hv])
    (hp := by simp only [stateAt, evalOperand, hp])
    (hs := by simp [storeValue, stateAt])]

/-! ### Lane-wise steps -/

theorem binopLanes_or (a b : List (BitVec 64)) :
    binopLanes .or a b = some (orLanes a b) := by
  simpa only [binopLanes, orLanes, evalBinop] using
    mapM_some_map (a.zip b) (fun p : BitVec 64 × BitVec 64 => p.1 ||| p.2)

theorem mapM_congr_opt {α β : Type} (l : List α) {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]

theorem shuffleLanes_pick64 {w : Nat} {a b : List (BitVec w)} (ha : a.length = 32)
    (hb : b.length = 32) :
    shuffleLanes 32 a b (List.range 64) = some (a ++ b) := by
  rw [shuffleLanes]
  have hlen : (a ++ b).length = 64 := by simp [ha, hb]
  have hfun : ∀ k ∈ List.range 64,
      (if k < 32 then a[k]? else b[k - 32]?) = some ((a ++ b).getD k 0) := by
    intro k hk
    have hk64 : k < 64 := List.mem_range.mp hk
    by_cases h32 : k < 32
    · have haa : a[k]? = some (a.getD k 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
      have hgd : (a ++ b).getD k 0 = a.getD k 0 := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hlen]; omega), Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
          Option.getD_some, List.getElem_append_left (by omega)]
      rw [if_pos h32, hgd, haa]
    · have hbb : b[k - 32]? = some (b.getD (k - 32) 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
      have hopt : (a ++ b)[k]? = b[k - 32]? := by
        rw [List.getElem?_append_right (by omega),
          show k - a.length = k - 32 from by omega]
      have hgd : (a ++ b).getD k 0 = b.getD (k - 32) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hopt]
      rw [if_neg h32, hgd, hbb]
  rw [mapM_congr_opt _ hfun]
  have hpure : (fun x : Nat => some ((a ++ b).getD x 0))
      = (fun x => pure ((a ++ b).getD x 0)) := rfl
  rw [hpure, List.mapM_pure]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlen]; omega), Option.getD_some]

theorem step_binopVec_or64 (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : List (BitVec 64)} (hx : x.length = 4) (hy : y.length = 4)
    (ha : lookupName env a = some (.vec 4 64 x))
    (hb : lookupName env b = some (.vec 4 64 y)) :
    evalInstr calls (stateAt env s) (.binopVec d .or 4 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .vec 4 64 (orLanes x y)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binopVec (l1 := x) (l2 := y) (ls := orLanes x y)
    (h1 := hx) (h2 := hy)
    (ha := by simp only [stateAt, evalOperand, ha])
    (hb := by simp only [stateAt, evalOperand, hb])
    (hm := by
      show binopLanes .or x y = some (orLanes x y)
      exact binopLanes_or x y)]
  rfl

theorem step_shuffle27 (env : Env) (s : State) (k : Ctx)
    (ha : lookupName env "%and.i2326.i.i" = some (.vec 32 8 (andWordLanes k)))
    (hb : lookupName env "%and.i2326.i47.i" = some (.vec 32 8 (andWordLanesHi k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.shuffleVec "%27" 32 8 (.reg "%and.i2326.i.i") (.reg "%and.i2326.i47.i")
          (List.range 64)) =
      some (stateAt (("%27", .vec 64 8 (andWordLanes k ++ andWordLanesHi k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_shuffleVec
    (ha := by simp only [stateAt, evalOperand, ha])
    (hb := by simp only [stateAt, evalOperand, hb])
    (h1 := vecLanes_self (andWordLanes_length k))
    (h2 := vecLanes_self (andWordLanesHi_length k))
    (hm := shuffleLanes_pick64 (andWordLanes_length k) (andWordLanesHi_length k))]
  rfl

/-- A zero comparison over `n` lanes, at the verdict list the step binds. -/
def eqZeroLanes (n : Nat) (l : List (BitVec 8)) : List (BitVec 1) :=
  (l.zip (List.replicate n (BitVec.ofInt 8 0))).map fun p => evalICmp .eq p.1 p.2

theorem step_icmp_lanes_eq0 (env : Env) (s : State) (d : String) (r : String)
    (n : Nat) (l : List (BitVec 8)) (hl : l.length = n)
    (h : lookupName env r = some (.vec n 8 l)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.icmpVec d .eq n 8 (.reg r) (.imm (.splat n 8 (BitVec.ofInt 8 0)))) =
      some (stateAt ((d, .vec n 1 (eqZeroLanes n l)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmpVec
    (ha := by simp only [stateAt, evalOperand, h])
    (vb := .vec n 8 (List.replicate n (BitVec.ofInt 8 0)))
    (hb := by simp only [stateAt, evalOperand, Const.toValue, List.length_replicate])
    (h1 := vecLanes_self hl)
    (h2 := vecLanes_self (List.length_replicate))]
  rfl

/-! ### The body's cell steps -/

theorem b_quote (env : Env) (s : State) (k : Ctx)
    (h6 : lookupName env "%6" = some (.vec 64 1 (quoteLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s) (.bitcastMask "%or.i99" 64 (.reg "%6")) =
      some (stateAt (("%or.i99", .int 64 (qrawW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_bitcastMask (hv := by simp only [stateAt, evalOperand, h6])
    (quoteLanes_length k)]
  rfl

theorem b_backLoCmp (env : Env) (s : State) (k : Ctx)
    (h2 : lookupName env "%2" = some (.vec 32 8 (loLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.icmpVec "%cmp.i39.i" .eq 32 8 (.reg "%2") (.imm (.splat 32 8 (BitVec.ofInt 8 92)))) =
      some (stateAt (("%cmp.i39.i", .vec 32 1 (backLo k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmpVec
    (ha := by simp only [stateAt, evalOperand, h2])
    (vb := .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 92)))
    (hb := by simp only [stateAt, evalOperand, Const.toValue, List.length_replicate])
    (h1 := vecLanes_self (loLanes_length k))
    (h2 := vecLanes_self (List.length_replicate))]
  rfl

theorem b_backLoMask (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i39.i" = some (.vec 32 1 (backLo k))) :
    evalInstr s1BlocksCalls (stateAt env s) (.bitcastMask "%7" 32 (.reg "%cmp.i39.i")) =
      some (stateAt (("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_bitcastMask (hv := by simp only [stateAt, evalOperand, h])
    (backLo_length k)]
  rfl

theorem b_backHiCmp (env : Env) (s : State) (k : Ctx)
    (h3 : lookupName env "%3" = some (.vec 32 8 (hiLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.icmpVec "%cmp.i.i" .eq 32 8 (.reg "%3") (.imm (.splat 32 8 (BitVec.ofInt 8 92)))) =
      some (stateAt (("%cmp.i.i", .vec 32 1 (backHi k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmpVec
    (ha := by simp only [stateAt, evalOperand, h3])
    (vb := .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 92)))
    (hb := by simp only [stateAt, evalOperand, Const.toValue, List.length_replicate])
    (h1 := vecLanes_self (hiLanes_length k))
    (h2 := vecLanes_self (List.length_replicate))]
  rfl

theorem b_backHiMask (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i.i" = some (.vec 32 1 (backHi k))) :
    evalInstr s1BlocksCalls (stateAt env s) (.bitcastMask "%8" 32 (.reg "%cmp.i.i")) =
      some (stateAt (("%8", .int 32 (BitVec.ofNat 32 (lanesToNat (backHi k)))) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_bitcastMask (hv := by simp only [stateAt, evalOperand, h])
    (backHi_length k)]
  rfl

theorem b_shl (env : Env) (s : State) {i : BitVec 64}
    (hi : lookupName env "%i.0178" = some (.int 64 i)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shl" .shl 64 (.reg "%i.0178") (.imm (.int 64 (BitVec.ofInt 64 6)))) =
      some (stateAt (("%shl", .int 64 (shl6W i)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := i) (y := BitVec.ofInt 64 6)
    (ha := by simp only [stateAt, evalOperand, hi])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (shl6W i).toNat) (hr := by
      rw [show BitVec.ofInt 64 6 = (6 : BitVec 64) from by decide,
        show (6 : BitVec 64).toNat = 6 from by decide]
      simp [evalBinopNat, evalBinop, shl6W])]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_load0 (env : Env) (s : State) (k : Ctx) {b : Nat} {i : BitVec 64}
    (hp : lookupName env "%add.ptr" = some (.ptr (ptrB b i)))
    (hr : readBytes s.mem (ptrB b i) 32 = some (List.ofFn k.lo)) :
    evalInstr s1BlocksCalls (stateAt env s) (.load "%0" (.vec 4 (.int 64)) (.reg "%add.ptr")) =
      some (stateAt (("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s) := by
  rw [step_load_vec4 s1BlocksCalls env s "%0" "%add.ptr" hp hr]
  rfl

theorem b_load1 (env : Env) (s : State) (k : Ctx) {b : Nat} {i : BitVec 64}
    (hp : lookupName env "%add.ptr2" = some (.ptr (ptrB b i + 32)))
    (hr : readBytes s.mem (ptrB b i + 32) 32 = some (List.ofFn k.hi)) :
    evalInstr s1BlocksCalls (stateAt env s) (.load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr2")) =
      some (stateAt (("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: env) s) := by
  rw [step_load_vec4 s1BlocksCalls env s "%1" "%add.ptr2" hp hr]
  rfl

theorem b_orAscii1 (env : Env) (s : State) (k : Ctx) {a : List (BitVec 64)}
    (ha : a.length = 4)
    (h0 : lookupName env "%0" = some (.vec 4 64 (unpackLanes 64 4 (loWord k))))
    (hascii : lookupName env "%ascii.0179" = some (.vec 4 64 a)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binopVec "%or.i98" .or 4 64 (.reg "%0") (.reg "%ascii.0179")) =
      some (stateAt (("%or.i98", .vec 4 64 (ascii1Lanes k a)) :: env) s) := by
  rw [step_binopVec_or64 s1BlocksCalls env s "%or.i98" "%0" "%ascii.0179"
    (unpackLanes_length 64 4 (loWord k)) ha h0 hascii]
  rfl

theorem b_orAscii2 (env : Env) (s : State) (k : Ctx) {a : List (BitVec 64)}
    (ha : a.length = 4)
    (h1 : lookupName env "%or.i98" = some (.vec 4 64 (ascii1Lanes k a)))
    (h2 : lookupName env "%1" = some (.vec 4 64 (unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binopVec "%or.i97" .or 4 64 (.reg "%or.i98") (.reg "%1")) =
      some (stateAt (("%or.i97", .vec 4 64 (ascii2Lanes k a)) :: env) s) := by
  rw [step_binopVec_or64 s1BlocksCalls env s "%or.i97" "%or.i98" "%1"
    (by simp [ascii1Lanes, orLanes, unpackLanes_length, ha])
    (unpackLanes_length 64 4 (hiWord k)) h1 h2]
  rfl

/-! ### The escape chain, at the body's shortcut -/

theorem b_and00 (env : Env) (s : State) (k : Ctx)
    (h1 : lookupName env "%st.sroa.0.0177" = some (.int 64 (openW k)))
    (h2 : lookupName env "%st.sroa.7.0176" = some (.int 64 (pparW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and.i.i" .and 64 (.reg "%st.sroa.0.0177") (.reg "%st.sroa.7.0176")) =
      some (stateAt (("%and.i.i", .int 64 (escAnd00W k)) :: env) s) :=
  step_binop_v _ _ _ "%and.i.i" .and "%st.sroa.0.0177" "%st.sroa.7.0176"
    (openW k) (pparW k) (escAnd00W k) h1 h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat,
        escAnd00W, BitVec.and_comm])

theorem b_escShl (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shl.i.i" .shl 64 (.reg "%or14.i") (.imm (.int 64 (BitVec.ofInt 64 1)))) =
      some (stateAt (("%shl.i.i", .int 64 (escShlW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := bsW k) (y := BitVec.ofInt 64 1)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (escShlW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, ofNat_toNat]
      rw [show (BitVec.ofInt 64 1).toNat = 1 from by decide]
      simp only [escShlW, bv_toNat, ofNat_toNat, BitVec.shiftLeft_eq])]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_escNot (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%shl.i.i" = some (.int 64 (escShlW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%not.i.i" .xor 64 (.reg "%shl.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1))))) =
      some (stateAt (("%not.i.i", .int 64 (escNotW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := escShlW k) (y := BitVec.ofInt 64 (-1))
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (escNotW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNotW,
        show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from by decide])]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_escStarts (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k)))
    (h2 : lookupName env "%not.i.i" = some (.int 64 (escNotW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and1.i.i" .and 64 (.reg "%or14.i") (.reg "%not.i.i")) =
      some (stateAt (("%and1.i.i", .int 64 (escStartsW k)) :: env) s) :=
  step_binop_v _ _ _ "%and1.i.i" .and "%or14.i" "%not.i.i" (bsW k) (escNotW k)
    (escStartsW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escStartsW])

theorem b_escEvenAlt (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and.i.i" = some (.int 64 (escAnd00W k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%xor.i.i" .xor 64 (.reg "%and.i.i")
          (.imm (.int 64 (BitVec.ofInt 64 0x5555555555555555)))) =
      some (stateAt (("%xor.i.i", .int 64 (escEvenAltW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := escAnd00W k)
    (y := BitVec.ofInt 64 0x5555555555555555)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (escEvenAltW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escEvenAltW,
        evenC])]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_escEvenClass (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and1.i.i" = some (.int 64 (escStartsW k)))
    (h2 : lookupName env "%xor.i.i" = some (.int 64 (escEvenAltW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and2.i.i" .and 64 (.reg "%and1.i.i") (.reg "%xor.i.i")) =
      some (stateAt (("%and2.i.i", .int 64 (escEvenClassW k)) :: env) s) :=
  step_binop_v _ _ _ "%and2.i.i" .and "%and1.i.i" "%xor.i.i" (escStartsW k)
    (escEvenAltW k) (escEvenClassW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escEvenClassW,
        BitVec.and_comm])

theorem b_escOddClass (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and2.i.i" = some (.int 64 (escEvenClassW k)))
    (h2 : lookupName env "%and1.i.i" = some (.int 64 (escStartsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%xor3.i.i" .xor 64 (.reg "%and2.i.i") (.reg "%and1.i.i")) =
      some (stateAt (("%xor3.i.i", .int 64 (escOddClassW k)) :: env) s) :=
  step_binop_v _ _ _ "%xor3.i.i" .xor "%and2.i.i" "%and1.i.i" (escEvenClassW k)
    (escStartsW k) (escOddClassW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escOddClassW])

theorem b_escNotBs (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%not4.i.i" .xor 64 (.reg "%or14.i") (.imm (.int 64 (BitVec.ofInt 64 (-1))))) =
      some (stateAt (("%not4.i.i", .int 64 (escNotBsW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := bsW k) (y := BitVec.ofInt 64 (-1))
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (escNotBsW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNotBsW,
        show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from by decide])]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_escSumEven (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and2.i.i" = some (.int 64 (escEvenClassW k)))
    (h2 : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%add.i.i" .add 64 (.reg "%and2.i.i") (.reg "%or14.i")) =
      some (stateAt (("%add.i.i", .int 64 (escSumEvenW k)) :: env) s) :=
  step_binop_v _ _ _ "%add.i.i" .add "%and2.i.i" "%or14.i" (escEvenClassW k) (bsW k)
    (escSumEvenW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escSumEvenW])

theorem b_escSumOdd (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor3.i.i" = some (.int 64 (escOddClassW k)))
    (h2 : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%add5.i.i" .add 64 (.reg "%xor3.i.i") (.reg "%or14.i")) =
      some (stateAt (("%add5.i.i", .int 64 (escSumOddW k)) :: env) s) :=
  step_binop_v _ _ _ "%add5.i.i" .add "%xor3.i.i" "%or14.i" (escOddClassW k) (bsW k)
    (escSumOddW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escSumOddW])

theorem b_escAnd6 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%not4.i.i" = some (.int 64 (escNotBsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and6.i.i" .and 64 (.reg "%not4.i.i") (.imm (.int 64 evenNotC))) =
      some (stateAt (("%and6.i.i", .int 64 (escAnd6W k)) :: env) s) :=
  step_binop_imm _ _ _ "%and6.i.i" .and "%not4.i.i" evenNotC (escNotBsW k) (escAnd6W k) h (by
    simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd6W])

theorem b_escAnd7 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and6.i.i" = some (.int 64 (escAnd6W k)))
    (h2 : lookupName env "%add.i.i" = some (.int 64 (escSumEvenW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and7.i.i" .and 64 (.reg "%and6.i.i") (.reg "%add.i.i")) =
      some (stateAt (("%and7.i.i", .int 64 (escAnd7W k)) :: env) s) :=
  step_binop_v _ _ _ "%and7.i.i" .and "%and6.i.i" "%add.i.i" (escAnd6W k) (escSumEvenW k)
    (escAnd7W k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd7W])

theorem b_escAnd8 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%not4.i.i" = some (.int 64 (escNotBsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and8.i.i" .and 64 (.reg "%not4.i.i") (.imm (.int 64 evenC))) =
      some (stateAt (("%and8.i.i", .int 64 (escAnd8W k)) :: env) s) :=
  step_binop_imm _ _ _ "%and8.i.i" .and "%not4.i.i" evenC (escNotBsW k) (escAnd8W k) h (by
    simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd8W])

theorem b_escAnd9 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and8.i.i" = some (.int 64 (escAnd8W k)))
    (h2 : lookupName env "%add5.i.i" = some (.int 64 (escSumOddW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and9.i.i" .and 64 (.reg "%and8.i.i") (.reg "%add5.i.i")) =
      some (stateAt (("%and9.i.i", .int 64 (escAnd9W k)) :: env) s) :=
  step_binop_v _ _ _ "%and9.i.i" .and "%and8.i.i" "%add5.i.i" (escAnd8W k) (escSumOddW k)
    (escAnd9W k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd9W])

theorem b_escAnd11 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and.i.i" = some (.int 64 (escAnd00W k)))
    (h2 : lookupName env "%not4.i.i" = some (.int 64 (escNotBsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and11.i.i" .and 64 (.reg "%and.i.i") (.reg "%not4.i.i")) =
      some (stateAt (("%and11.i.i", .int 64 (blkAnd11W k)) :: env) s) :=
  step_binop_v _ _ _ "%and11.i.i" .and "%and.i.i" "%not4.i.i" (escAnd00W k) (escNotBsW k)
    (blkAnd11W k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, blkAnd11W])

theorem b_escOr (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and7.i.i" = some (.int 64 (escAnd7W k)))
    (h2 : lookupName env "%and11.i.i" = some (.int 64 (blkAnd11W k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%or.i.i" .or 64 (.reg "%and7.i.i") (.reg "%and11.i.i")) =
      some (stateAt (("%or.i.i", .int 64 (blkOr62W k)) :: env) s) :=
  step_binop_v _ _ _ "%or.i.i" .or "%and7.i.i" "%and11.i.i" (escAnd7W k) (blkAnd11W k)
    (blkOr62W k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, blkOr62W])

theorem b_escOr12 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or.i.i" = some (.int 64 (blkOr62W k)))
    (h2 : lookupName env "%and9.i.i" = some (.int 64 (escAnd9W k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%or12.i.i" .or 64 (.reg "%or.i.i") (.reg "%and9.i.i")) =
      some (stateAt (("%or12.i.i", .int 64 (blkEscapedW k)) :: env) s) :=
  step_binop_v _ _ _ "%or12.i.i" .or "%or.i.i" "%and9.i.i" (blkOr62W k) (escAnd9W k)
    (blkEscapedW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, blkEscapedW])

theorem b_escCmp (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%add5.i.i" = some (.int 64 (escSumOddW k)))
    (h2 : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.icmp "%cmp.i45.i" .ult 64 (.reg "%add5.i.i") (.reg "%or14.i")) =
      some (stateAt (("%cmp.i45.i", .int 1 (escCmp63L k)) :: env) s) :=
  step_icmp_v _ _ _ "%cmp.i45.i" .ult "%add5.i.i" "%or14.i" (escSumOddW k) (bsW k) h h2

theorem b_escConv13 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i45.i" = some (.int 1 (escCmp63L k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.zext "%conv13.i.i" 1 64 (.reg "%cmp.i45.i")) =
      some (stateAt (("%conv13.i.i", .int 64 (escConv13W k)) :: env) s) := by
  rw [step_zext1 s1BlocksCalls env s "%conv13.i.i" "%cmp.i45.i" (escCmp63L k) h]
  rfl

theorem b_escShr16 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%conv12.i" = some (.int 64 (conv12W k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shr.i.i" .lshr 64 (.reg "%conv12.i") (.imm (.int 64 (BitVec.ofInt 64 31)))) =
      some (stateAt (("%shr.i.i", .int 64 (escShr16W k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := conv12W k) (y := BitVec.ofInt 64 31)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, Const.toValue])
    (r := (escShr16W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, ofNat_toNat]
      rw [show (BitVec.ofInt 64 31).toNat = 31 from by decide]
      simp only [escShr16W, bv_toNat, ofNat_toNat]
      rfl)]
  simp only [stateAt, State.bind, ofNat_toNat]

theorem b_notEsc (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or12.i.i" = some (.int 64 (blkEscapedW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%not.i" .xor 64 (.reg "%or12.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1))))) =
      some (stateAt (("%not.i", .int 64 (blkNotEscW k)) :: env) s) :=
  step_binop_imm _ _ _ "%not.i" .xor "%or12.i.i" (BitVec.ofInt 64 (-1)) (blkEscapedW k)
    (blkNotEscW k) h (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, blkNotEscW,
        show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from by decide])

theorem b_andQuote (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or.i99" = some (.int 64 (qrawW k)))
    (h2 : lookupName env "%not.i" = some (.int 64 (blkNotEscW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and.i" .and 64 (.reg "%or.i99") (.reg "%not.i")) =
      some (stateAt (("%and.i", .int 64 (blkAndQuoteW k)) :: env) s) :=
  step_binop_v _ _ _ "%and.i" .and "%or.i99" "%not.i" (qrawW k) (blkNotEscW k)
    (blkAndQuoteW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, blkAndQuoteW])

/-! ### The leading `phi` run -/

def phiInstrs : List Instr :=
  [ .phi "%prevS.0180" (.int 64) [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr16")],
    .phi "%ascii.0179" (.vec 4 (.int 64)) [("for.body.lr.ph", splat64 4 0), ("if.end", reg "%or.i97")],
    .phi "%i.0178" (.int 64) [("for.body.lr.ph", lit64 0), ("if.end", reg "%inc")],
    .phi "%st.sroa.0.0177" (.int 64) [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr.i.i")],
    .phi "%st.sroa.7.0176" (.int 64) [("for.body.lr.ph", lit64 0), ("if.end", reg "%conv13.i.i")],
    .phi "%st.sroa.11.0175" (.int 64) [("for.body.lr.ph", lit64 0), ("if.end", reg "%shr.i")]]

theorem phiInstrs_eq : phiInstrs = bodyInstrs.take 6 := rfl

/-- The six leading `phi`s, resolved at the loop's back edge: the carried values
are the latch's own cells. -/
theorem phi_denote (env : Env) (s : State) (i prevS st0 st7 st11 : BitVec 64)
    (ascii : List (BitVec 64))
    (hpre : s.pre = some "if.end")
    (hprev : lookupName env "%shr16" = some (.int 64 prevS))
    (hascii : lookupName env "%or.i97" = some (.vec 4 64 ascii))
    (hinc : lookupName env "%inc" = some (.int 64 i))
    (h0 : lookupName env "%shr.i.i" = some (.int 64 st0))
    (h7 : lookupName env "%conv13.i.i" = some (.int 64 st7))
    (h11 : lookupName env "%shr.i" = some (.int 64 st11)) :
    denoteCode s1BlocksCalls phiInstrs (stateAt env s) =
      some (stateAt (
        ("%st.sroa.11.0175", .int 64 st11) ::
        ("%st.sroa.7.0176", .int 64 st7) ::
        ("%st.sroa.0.0177", .int 64 st0) ::
        ("%i.0178", .int 64 i) ::
        ("%ascii.0179", .vec 4 64 ascii) ::
        ("%prevS.0180", .int 64 prevS) :: env) s) := by
  rw [phiInstrs_eq]
  simp only [bodyInstrs, List.take, JsonS1BlocksIR.reg, lit64, splat64]
  block_phi_run
  · simp only [runCells]
    rfl
  · exact hpre
  · decide
  all_goals (try (first
    | rfl
    | (simp [phiIncoming])
    | exact evalOperand_reg_of _ _ _ _ (by assumption)
    | (simp only [evalOperand, Const.toValue])))

/-- The six leading `phi`s, resolved at the loop's entry edge: every carried
value is the loop's seed, so the index, the two carry words and the incoming
in-string word are zero and the accumulator is the zero vector. -/
theorem phi_denote_entry (env : Env) (s : State)
    (hpre : s.pre = some "for.body.lr.ph") :
    denoteCode s1BlocksCalls phiInstrs (stateAt env s) =
      some (stateAt (
        ("%st.sroa.11.0175", .int 64 0) ::
        ("%st.sroa.7.0176", .int 64 0) ::
        ("%st.sroa.0.0177", .int 64 0) ::
        ("%i.0178", .int 64 0) ::
        ("%ascii.0179", .vec 4 64 (List.replicate 4 0)) ::
        ("%prevS.0180", .int 64 0) :: env) s) := by
  rw [phiInstrs_eq]
  simp only [bodyInstrs, List.take, JsonS1BlocksIR.reg, lit64, splat64]
  block_phi_run
  · simp only [runCells]
    rfl
  · exact hpre
  · decide
  all_goals (try (first
    | rfl
    | (simp [phiIncoming])
    | exact evalOperand_reg_of _ _ _ _ (by assumption)
    | (simp only [evalOperand, Const.toValue])))

end LeanLLVM.Refinement.JsonS1BlocksSteps
