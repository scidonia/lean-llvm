/-
The emitter's entry block, `if.end.i4`, and the memory it writes.

`if.end.i4` is the sixty-three-instruction block between the lanes loop's exit and
the eight-at-a-time writer.  It does four things: it loads the caller's count, it
writes the **first** batch inline, it advances the count by `min (ctpop esc) 8`, and
it branches to the writer loop only when there are positions left.

**The inlined batch is not `batchMem`.**  Every store here writes `%conv ||| %cast`,
where `@xl_batch` writes `%base + %cast`; the two agree exactly on the lanes the
batch *claims* — a claimed lane is below sixty-four and the base is a multiple of
sixty-four, so `|||` and `+` coincide there — and they diverge on the eight-entry
reserve, where an exhausted chain's cast is `64` and `base ||| 64` differs from
`base + 64` whenever bit six of the base is set.  The record's post stops at
`4 * length` and says nothing about the reserve (C119), so the divergence is inside
the region the record is silent about and no clause distinguishes the two forms.
The memory is therefore stated as its own expression, `lstIfEnd4Mem`, with its own
per-index entry law and its own thirty-two-byte frame; the *claimed* entries are
then shown equal to `batchBytes`'s, which is what the record reads.

The count law is the block's own: `%add.i.i = %3 + zext (umin (ctpop esc) 8)`, and
`%3` is the caller's count read back as a 64-bit word.  The branch is
`icmp ugt (ctpop esc) 8`, so the writer loop is entered exactly when the inline
batch did not drain the word.

**What is here for the writer loop.**  Its call site is resolved
(`b_call_batch`, `xl_batch_call_next`: the record's count, the batch's memory, and
an unchanged allocator).  The bridge its invariant needs is proved too:
`ListLoopInv` states the residual word by *lane membership* while the store's
conjunct is about the *list* `position.drop used`, so a step that advances `used`
needs `setLanes w = position.drop used`; `setLanes_eq_of_lane_mem` gives it, from
`filter_range_mem_eq_self` (a range filtered by membership in an increasing list,
all of whose entries lie below the word, *is* that list) and
`filter_lt_append_not`.  `BitLanes` has only the inverse, `setLanes_getElem?_rank`,
which reads the list out of the word.  And `lstIfEnd4_cursor_eq` ties the loop's
entry cursor to the inline batch: the branch that enters the loop has
`ctpop esc > 8`, so the inline claim is exactly eight and the preheader's `+32` is
`4 * used`.

**What is not here.**  The writer block's own instruction trace and its
remaining-block induction: twenty-five instructions at `while.body.i.i`, whose
state must carry `ListLoopInv`'s three conjuncts, the cursor `xp + 4 * xn0 + 4 *
used` (by `lstIfEnd4_cursor_eq` at entry) and the residual word advanced by
`clearLow`, and whose exit test compares the residual with zero rather than with
its next iterate — so `CarriedLoop` is not its shape and it needs the
remaining-block idiom restricted to a memory-carrying state.  The pieces above are
what that trace consumes; nothing in it is a statement the body falsifies.
-/
import LeanLLVM.Vellum.JsonEscapeListMemo
import LeanLLVM.Vellum.JsonEscapeBatchEntries

set_option maxRecDepth 8000
set_option maxHeartbeats 800000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonB8Steps

/-! ### Two instruction shapes the block uses

`@xl_batch` adds; the inlined batch masks its base with the truncated lane, so the
`or` at 32 bits is the one shape the batch module does not carry. -/

/-- `%d = or i32 %a, %b`. -/
theorem b_or32 (env : Env) (s : State) (d a b : String) (x y : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) (hb : lookupName env b = some (.int 32 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .or 32 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 32 (x ||| y)) :: env) s) := by
  rw [evalInstr_binop (r := (x ||| y).toNat)
    (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_reg_of env s b (.int 32 y) hb)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]

/-- `%d = icmp ugt i64 %a, <c>`. -/
theorem b_icmp_ugt64_imm (env : Env) (s : State) (d a : String) (x c : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .ugt 64 (.reg a) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 1 (evalICmp .ugt x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 c)]
  simp only [withEnv, State.bind]

/-! ### The block, from the pinned AST -/

theorem lstIfEnd4_instrs :
    lstIfEnd4.instrs =
      [ .load "%3" (.int 64) (.reg "%xn"),
        .gep "%add.ptr.i.i" (.int 32) (.reg "%xp") (.reg "%3"),
        .binop "%or.i.i.i" .or 64 (.reg "%and31.i")
          (.imm (.int 64 (BitVec.ofInt 64 (-9223372036854775808)))),
        .call "%4" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%or.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast.i.i.i" 64 32 (.reg "%4"),
        .binop "%add.i.i.i" .or 32 (.reg "%conv") (.reg "%cast.i.i.i"),
        .store (.int 32) (.reg "%add.i.i.i") (.reg "%add.ptr.i.i"),
        .binop "%sub.i.i.i" .add 64 (.reg "%or.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.i.i.i" .and 64 (.reg "%sub.i.i.i") (.reg "%or.i.i.i"),
        .call "%5" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast1.i.i.i" 64 32 (.reg "%5"),
        .binop "%add2.i.i.i" .or 32 (.reg "%conv") (.reg "%cast1.i.i.i"),
        .gep "%arrayidx3.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 4))),
        .store (.int 32) (.reg "%add2.i.i.i") (.reg "%arrayidx3.i.i.i"),
        .binop "%sub4.i.i.i" .add 64 (.reg "%and.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and5.i.i.i" .and 64 (.reg "%sub4.i.i.i") (.reg "%and.i.i.i"),
        .call "%6" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and5.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast6.i.i.i" 64 32 (.reg "%6"),
        .binop "%add7.i.i.i" .or 32 (.reg "%conv") (.reg "%cast6.i.i.i"),
        .gep "%arrayidx8.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 8))),
        .store (.int 32) (.reg "%add7.i.i.i") (.reg "%arrayidx8.i.i.i"),
        .binop "%sub9.i.i.i" .add 64 (.reg "%and5.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and10.i.i.i" .and 64 (.reg "%sub9.i.i.i") (.reg "%and5.i.i.i"),
        .call "%7" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and10.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast11.i.i.i" 64 32 (.reg "%7"),
        .binop "%add12.i.i.i" .or 32 (.reg "%conv") (.reg "%cast11.i.i.i"),
        .gep "%arrayidx13.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 12))),
        .store (.int 32) (.reg "%add12.i.i.i") (.reg "%arrayidx13.i.i.i"),
        .binop "%sub14.i.i.i" .add 64 (.reg "%and10.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and15.i.i.i" .and 64 (.reg "%sub14.i.i.i") (.reg "%and10.i.i.i"),
        .call "%8" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and15.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast16.i.i.i" 64 32 (.reg "%8"),
        .binop "%add17.i.i.i" .or 32 (.reg "%conv") (.reg "%cast16.i.i.i"),
        .gep "%arrayidx18.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 16))),
        .store (.int 32) (.reg "%add17.i.i.i") (.reg "%arrayidx18.i.i.i"),
        .binop "%sub19.i.i.i" .add 64 (.reg "%and15.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and20.i.i.i" .and 64 (.reg "%sub19.i.i.i") (.reg "%and15.i.i.i"),
        .call "%9" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and20.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast21.i.i.i" 64 32 (.reg "%9"),
        .binop "%add22.i.i.i" .or 32 (.reg "%conv") (.reg "%cast21.i.i.i"),
        .gep "%arrayidx23.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 20))),
        .store (.int 32) (.reg "%add22.i.i.i") (.reg "%arrayidx23.i.i.i"),
        .binop "%sub24.i.i.i" .add 64 (.reg "%and20.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and25.i.i.i" .and 64 (.reg "%sub24.i.i.i") (.reg "%and20.i.i.i"),
        .call "%10" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and25.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast26.i.i.i" 64 32 (.reg "%10"),
        .binop "%add27.i.i.i" .or 32 (.reg "%conv") (.reg "%cast26.i.i.i"),
        .gep "%arrayidx28.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 24))),
        .store (.int 32) (.reg "%add27.i.i.i") (.reg "%arrayidx28.i.i.i"),
        .binop "%sub29.i.i.i" .add 64 (.reg "%and25.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and30.i.i.i" .and 64 (.reg "%sub29.i.i.i") (.reg "%and25.i.i.i"),
        .call "%11" (.int 64) "llvm.cttz.i64"
          [(.int 64, .reg "%and30.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
        .trunc "%cast31.i.i.i" 64 32 (.reg "%11"),
        .binop "%add32.i.i.i" .or 32 (.reg "%conv") (.reg "%cast31.i.i.i"),
        .gep "%arrayidx33.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 28))),
        .store (.int 32) (.reg "%add32.i.i.i") (.reg "%arrayidx33.i.i.i"),
        .call "%12" (.int 64) "llvm.ctpop.i64" [(.int 64, .reg "%and31.i")],
        .trunc "%cast36.i.i.i" 64 32 (.reg "%12"),
        .call "%cond.i.i.i" (.int 32) "llvm.umin.i32"
          [(.int 32, .reg "%cast36.i.i.i"), (.int 32, .imm (.int 32 (BitVec.ofInt 32 8)))],
        .zext "%conv.i.i" 32 64 (.reg "%cond.i.i.i"),
        .binop "%add.i.i" .add 64 (.reg "%3") (.reg "%conv.i.i"),
        .store (.int 64) (.reg "%add.i.i") (.reg "%xn"),
        .icmp "%cmp.i.i" .ugt 64 (.reg "%12") (.imm (.int 64 (BitVec.ofInt 64 8))) ] := by
  decide

theorem lstIfEnd4_term :
    lstIfEnd4.term =
      .condbr (.reg "%cmp.i.i") "for.body.preheader.i.i" "xl_emit.exit" := by
  decide

/-! ### The block's memory expression

The eight inline stores write `%conv ||| %cast`; the count's store follows them.
`inlWrites` is the same eight writes read from the inside out, so the entry at
offset `4 * i` is the `i`-th `writeBytes` and the peeling induction has an index to
follow. -/

/-- The four bytes the inlined batch stores at step `i`: the base masked with the
truncated trailing lane, rather than added to it. -/
def inlBytes (base : BitVec 32) (esc : BitVec 64) (i : Nat) : List UInt8 :=
  natToBytes (BitVec.ofNat 32 (base.toNat ||| (batchCast esc i).toNat)).toNat 4

/-- The inlined batch's writes in increasing offset: `n` entries at `o, o + 4, …`. -/
def inlWrites (base : BitVec 32) (esc : BitVec 64) (o : Nat) : Nat → Mem → Mem
  | 0, mem => mem
  | n + 1, mem =>
      writeBytes (inlWrites base esc o n mem) (o + 4 * n) (inlBytes base esc n)

/-- The block's memory: the eight inline entries at `o`, then the count's eight
bytes at `xn`. -/
def lstIfEnd4Mem (base : BitVec 32) (esc : BitVec 64) (o xn count : Nat) (mem : Mem) : Mem :=
  writeBytes (inlWrites base esc o 8 mem) xn (natToBytes count 8)

/-- The count the block stores: the caller's count plus the number of entries the
inline batch claimed. -/
def lstIfEnd4Count (xn0 : Nat) (esc : BitVec 64) : Nat := xn0 + min (ctpop esc) 8

/-- The cell `%add.i.i`, as the block computes it. -/
def lstIfEnd4CountWord (xn0 : Nat) (esc : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 xn0 + BitVec.ofNat 64 (min (ctpop esc) 8)

/-- The branch the block takes: the writer loop iff the inline batch left positions
behind. -/
def lstIfEnd4Next (esc : BitVec 64) : String :=
  if ctpop esc > 8 then "for.body.preheader.i.i" else "xl_emit.exit"

/-! ### The count's word

The truncation, the `umin` and the `zext` compose to the count the record names.
`JsonEscapeBatch`'s `batchCount_eq` is the same three steps at `@xl_batch`'s return,
and it is reused rather than restated. -/

/-! ### The byte arithmetic the count and the entries need -/

/-- A truncation of a 64-bit numeral is the same numeral at 32 bits. -/
theorem ofNat32_ofNat64 (m : Nat) :
    BitVec.ofNat 32 ((BitVec.ofNat 64 m).toNat % 2 ^ 32) = BitVec.ofNat 32 m := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- A zero extension of a 32-bit numeral is the same numeral at 64 bits, at a value
that does not truncate. -/
theorem ofNat64_ofNat32 (m : Nat) (hm : m < 2 ^ 32) :
    BitVec.ofNat 64 ((BitVec.ofNat 32 m).toNat) = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  have hL : (BitVec.ofNat 64 ((BitVec.ofNat 32 m).toNat)).toNat = m := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
      Nat.mod_eq_of_lt (by omega : m < 2 ^ 64)]
  have hR : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64)]
  rw [hL, hR]

/-- The `umin` against eight, at a count that fits: the smaller of the two. -/
theorem umin_ofNat_eight (m : Nat) (hm : m < 2 ^ 32) :
    umin (BitVec.ofNat 32 m) (BitVec.ofInt 32 8) = BitVec.ofNat 32 (min m 8) := by
  have h8 : (BitVec.ofInt 32 8 : BitVec 32) = BitVec.ofNat 32 8 := by decide
  have hm' : (BitVec.ofNat 32 m).toNat = m := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  have h8' : (BitVec.ofNat 32 8).toNat = 8 := by simp [BitVec.toNat_ofNat]
  unfold umin
  rw [h8, hm', h8']
  by_cases h : m ≤ 8
  · rw [ite_eq_left h, Nat.min_eq_left h]
  · rw [ite_eq_right h, Nat.min_eq_right (by omega)]

/-- Two 64-bit numerals add to their sum's numeral. -/
theorem ofNat64_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- **`natToBytes` sees only the low bytes a width keeps.**  Writing a value and
writing its residue at a power of two are the same bytes. -/
theorem natToBytes_mod_pow (v k n : Nat) (hn : k ≤ n) :
    natToBytes (v % 256 ^ n) k = natToBytes v k := by
  induction k generalizing v n with
  | zero => rfl
  | succ k ih =>
      have hn1 : 1 ≤ n := by omega
      have hpow : (256 : Nat) ^ n = 256 * 256 ^ (n - 1) := by
        have h1 : (256 : Nat) * 256 ^ (n - 1) = 256 ^ (n - 1) * 256 := Nat.mul_comm _ _
        rw [h1, ← Nat.pow_succ, show (n - 1).succ = n from by omega]
      rw [natToBytes, natToBytes]
      have hmod : (v % 256 ^ n) % 256 = v % 256 := by
        rw [hpow, Nat.mod_mul_right_mod]
      have hdiv : (v % 256 ^ n) / 256 = (v / 256) % 256 ^ (n - 1) := by
        rw [hpow, Nat.mod_mul_right_div_self]
      rw [hmod, hdiv, ih (v / 256) (n - 1) (by omega)]

/-- Eight bytes of a 64-bit word are the same eight bytes of its residue. -/
theorem natToBytes_mod_two_pow (v : Nat) :
    natToBytes (v % 2 ^ 64) 8 = natToBytes v 8 := by
  have h : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  rw [h]
  exact natToBytes_mod_pow v 8 8 (Nat.le_refl 8)

/-- The count's cell, as the block computes it: the caller's count plus the
inline batch's eight-at-most claim, at sixty-four bits. -/
theorem lstIfEnd4_count_compose (xn0 : Nat) (esc : BitVec 64) :
    BitVec.ofNat 64 xn0 +
        BitVec.ofNat 64
          ((umin (BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32))
            (BitVec.ofInt 32 8)).toNat) =
      lstIfEnd4CountWord xn0 esc := by
  unfold lstIfEnd4CountWord
  rw [ofNat32_ofNat64]
  have hle : ctpop esc < 2 ^ 32 := by
    have := ctpop_eq_setLanes_length esc
    have hlen : (setLanes esc).length ≤ 64 := setLanes_length_le esc
    omega
  rw [umin_ofNat_eight (ctpop esc) hle,
    ofNat64_ofNat32 (min (ctpop esc) 8) (by omega), ofNat64_add]

/-- The stored bytes of the count read back as the record's word. -/
theorem lstIfEnd4_count_bytes (xn0 : Nat) (esc : BitVec 64) :
    natToBytes (lstIfEnd4CountWord xn0 esc).toNat 8 =
      wordBytes 8 (lstIfEnd4Count xn0 esc) := by
  unfold lstIfEnd4CountWord wordBytes lstIfEnd4Count
  rw [ofNat64_add, BitVec.toNat_ofNat]
  exact natToBytes_mod_two_pow _


/-! ### The block's run

The sixty-three instruction lines, in order.  Each step's operands are resolved from
the environment the previous step bound; the eight inline stores build
`inlWrites` from the inside out, and the count's store is the last memory write. -/

/-- The cells `if.end.i4` does not write and the writer reads: the body's
arguments, the count's slot, the two carry cells, and the two seed cells the
writer's preheaders use. -/
structure lstWriterKeeps (env0 env : Env) : Prop where
  bsReg : lookupName env "%bs" = lookupName env0 "%bs"
  ctlReg : lookupName env "%ctl" = lookupName env0 "%ctl"
  imReg : lookupName env "%im" = lookupName env0 "%im"
  blk0Reg : lookupName env "%blk0" = lookupName env0 "%blk0"
  xpReg : lookupName env "%xp" = lookupName env0 "%xp"
  xnReg : lookupName env "%xn" = lookupName env0 "%xn"
  carryReg : lookupName env "%carry" = lookupName env0 "%carry"
  arrReg : lookupName env "%arrayidx1" = lookupName env0 "%arrayidx1"
  andiReg : lookupName env "%and31.i" = lookupName env0 "%and31.i"
  convReg : lookupName env "%conv" = lookupName env0 "%conv"

/-- The `umin` the count's `zext` reads. -/
def lstUmin8 (esc : BitVec 64) : BitVec 32 :=
  umin (BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32)) (BitVec.ofInt 32 8)

/-- The count's cell as the block computes it: the caller's count plus the inline
claim, in the `zext`'s own form. -/
def lstIfEnd4CellCount (c0 : Nat) (esc : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 c0 + BitVec.ofNat 64 (lstUmin8 esc).toNat

/-- A cell of the environment the block leaves: the walk passes every cons the
block wrote before it and stops at the one that names the cell, or at the
incoming environment for a name the block does not write.  The walk alone closes
the second case (the two sides coincide), and `<;>` keeps that from being an
error when it does. -/
macro "ie4_lk" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)] <;>
   (first | rw [lookupName_cons_self] | rfl)))

/-- The same walk at the count's cell, whose value the record states folded. -/
macro "ie4_lk_count" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)] <;>
   (first
    | (rw [lookupName_cons_self]; simp only [lstIfEnd4CellCount, lstUmin8])
    | rfl)))

/-! ### The block's run

The sixty-three instruction lines, in order.  Each step's operands are resolved
from the environment the previous step bound; the eight inline stores build
`inlWrites` from the inside out, and the count's store is the last memory write.
The conclusion states the memory and the cells a successor reads, so the writer's
trace names what it uses rather than restating the block. -/

theorem lstIfEnd4_run (env : Env) (s : State) (esc : BitVec 64) (base : BitVec 32)
    (xp xn c0 : Nat)
    (hes : lookupName env "%and31.i" = some (.int 64 esc))
    (hconv : lookupName env "%conv" = some (.int 32 base))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hc0 : c0 < 2 ^ 63)
    (hld : readBytes s.mem xn 8 = some (natToBytes c0 8)) :
    Option.map State.mem (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)) =
        some (lstIfEnd4Mem base esc (xp + c0 * 4) xn (lstIfEnd4Count c0 esc) s.mem) ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%bs") = lookupName env "%bs" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%ctl") = lookupName env "%ctl" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%im") = lookupName env "%im" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%blk0") = lookupName env "%blk0" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%xp") = lookupName env "%xp" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%xn") = lookupName env "%xn" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%carry") = lookupName env "%carry" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%arrayidx1") = lookupName env "%arrayidx1" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%and31.i") = lookupName env "%and31.i" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%conv") = lookupName env "%conv" ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.ptr.i.i") = some (.ptr (xp + c0 * 4)) ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i.i") =
          some (.int 64 (lstIfEnd4CellCount c0 esc)) ∧
      (denoteCode escapeCalls lstIfEnd4.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.i.i") =
          some (.int 1
            (evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8))) := by
  rw [lstIfEnd4_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load64_nat env s "%3" "%xn" xn c0 hxn hld)]
  have hk : (BitVec.signExtend 64 (BitVec.ofNat 64 c0)).toNat = c0 := by
    rw [show BitVec.signExtend 64 (BitVec.ofNat 64 c0) = BitVec.ofNat 64 c0 from by simp,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c0 < 2 ^ 64)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep4_reg64 _ _ "%add.ptr.i.i" "%xp" "%3" xp
    (BitVec.ofNat 64 c0) c0 (by b_lk hxp) (by b_lk lookupName_cons_self) hk (by omega))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or_imm64 _ _ "%or.i.i.i" "%and31.i" esc
    (BitVec.ofInt 64 (-9223372036854775808)) (by b_lk hes))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%4" "%or.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast.i.i.i" "%4" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add.i.i.i" "%conv" "%cast.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add.i.i.i" "%add.ptr.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub.i.i.i" "%or.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and.i.i.i" "%sub.i.i.i" "%or.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%5" "%and.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast1.i.i.i" "%5" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add2.i.i.i" "%conv" "%cast1.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx3.i.i.i" "%add.ptr.i.i" _
    4 (BitVec.ofInt 64 4) (by b_lk (lookupName_cons_ne _ _ (by decide))) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add2.i.i.i" "%arrayidx3.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub4.i.i.i" "%and.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and5.i.i.i" "%sub4.i.i.i" "%and.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%6" "%and5.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast6.i.i.i" "%6" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add7.i.i.i" "%conv" "%cast6.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx8.i.i.i" "%add.ptr.i.i" _
    8 (BitVec.ofInt 64 8) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add7.i.i.i" "%arrayidx8.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub9.i.i.i" "%and5.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and10.i.i.i" "%sub9.i.i.i" "%and5.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%7" "%and10.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast11.i.i.i" "%7" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add12.i.i.i" "%conv" "%cast11.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx13.i.i.i" "%add.ptr.i.i" _
    12 (BitVec.ofInt 64 12) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add12.i.i.i" "%arrayidx13.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub14.i.i.i" "%and10.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and15.i.i.i" "%sub14.i.i.i" "%and10.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%8" "%and15.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast16.i.i.i" "%8" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add17.i.i.i" "%conv" "%cast16.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx18.i.i.i" "%add.ptr.i.i" _
    16 (BitVec.ofInt 64 16) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add17.i.i.i" "%arrayidx18.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub19.i.i.i" "%and15.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and20.i.i.i" "%sub19.i.i.i" "%and15.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%9" "%and20.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast21.i.i.i" "%9" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add22.i.i.i" "%conv" "%cast21.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx23.i.i.i" "%add.ptr.i.i" _
    20 (BitVec.ofInt 64 20) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add22.i.i.i" "%arrayidx23.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub24.i.i.i" "%and20.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and25.i.i.i" "%sub24.i.i.i" "%and20.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%10" "%and25.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast26.i.i.i" "%10" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add27.i.i.i" "%conv" "%cast26.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx28.i.i.i" "%add.ptr.i.i" _
    24 (BitVec.ofInt 64 24) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add27.i.i.i" "%arrayidx28.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub29.i.i.i" "%and25.i.i.i" _
    (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and30.i.i.i" "%sub29.i.i.i" "%and25.i.i.i" _
    _ (by b_lk lookupName_cons_self) (by b_lk (lookupName_cons_ne _ _ (by decide))))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%11" "%and30.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast31.i.i.i" "%11" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or32 _ _ "%add32.i.i.i" "%conv" "%cast31.i.i.i" base _
    (by b_lk hconv) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx33.i.i.i" "%add.ptr.i.i" _
    28 (BitVec.ofInt 64 28) (by b_lk (by b_lk lookupName_cons_self)) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add32.i.i.i" "%arrayidx33.i.i.i" _ _
    (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_ctpop _ _ "%12" "%and31.i" esc (by b_lk hes))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast36.i.i.i" "%12" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_umin _ _ "%cond.i.i.i" "%cast36.i.i.i" _
    (BitVec.ofInt 32 8) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_zext32_64 _ _ "%conv.i.i" "%cond.i.i.i" _
    (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add.i.i" "%3" "%conv.i.i" _
    _ (by b_lk (by b_lk (lookupName_cons_ne _ _ (by decide)))) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64_mem _ _ _ "%add.i.i" "%xn" _
    xn (by b_lk lookupName_cons_self) (by b_lk hxn))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ _ "%cmp.i.i" "%12" _
    (BitVec.ofInt 64 8) (by b_lk (by b_lk (lookupName_cons_ne _ _ (by decide)))))]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [denoteCode, Option.map_some, withEnv]
    rw [lstIfEnd4_count_compose, lstIfEnd4_count_bytes]
    simp [lstIfEnd4Mem, wordBytes, inlWrites, inlBytes, batchCast, batchChain]
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk
  · simp only [denoteCode, Option.bind_some, withEnv]
    ie4_lk_count
  · simp only [denoteCode, Option.bind_some, withEnv]
    rw [lookupName_cons_self] <;> rfl


/-! ### The inline batch's memory laws

The eight writes read back one entry at a time and leave every byte outside their
thirty-two untouched.  The proofs mirror `JsonEscapeBatchEntries`'s laws for
`batchWrites`, because the bodies are the same eight stores with a different
arithmetic on the value. -/

/-- Entry `i` reads back as the bytes the block stored there. -/
theorem inlWrites_readBytes_entry (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    ∀ n i, i < n → ∀ mem : Mem,
      readBytes (inlWrites base esc o n mem) (o + 4 * i) 4 = some (inlBytes base esc i) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      intro i hi mem
      rw [inlWrites]
      rcases Nat.lt_or_ge i n with hlt | hge
      · rw [readBytes_writeBytes_below (inlWrites base esc o n mem) (inlBytes base esc n)
          4 (o + 4 * i) (o + 4 * n) (by omega)]
        exact ih i hlt mem
      · have hie : i = n := by omega
        rw [hie]
        simpa [inlBytes, natToBytes_length] using readBytes_writeBytes_same
          (inlWrites base esc o n mem) (inlBytes base esc n)

/-- A byte outside the inline batch's writes is the byte it was. -/
theorem inlWrites_frame (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    ∀ n a, (a < o ∨ o + 4 * n ≤ a) → ∀ mem : Mem,
      readByte (inlWrites base esc o n mem) a = readByte mem a := by
  intro n
  induction n with
  | zero =>
      intro a _ mem
      rfl
  | succ n ih =>
      intro a h mem
      rw [inlWrites]
      rw [readByte_writeBytes_outside (inlWrites base esc o n mem) (inlBytes base esc n) (by
        have hl : (inlBytes base esc n).length = 4 := by
          simp [inlBytes, natToBytes_length]
        rw [hl]
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))]
      exact ih a (by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)) mem

/-- A read entirely above a write is unaffected by it. -/
theorem readBytes_writeBytes_above (m : Mem) :
    ∀ (bs : List UInt8) (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | _, 0, _, _, _ => by simp only [readBytes]
  | bs, n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs (by omega)]
      rw [readBytes_writeBytes_above m bs n (addr + 1) start (by omega)]

/-- **The claimed entries of the inline batch are the batch's.**  On a lane the
batch claims, the truncated trailing count is below sixty-four and the base is a
multiple of sixty-four, so the inlined `or` and the out-of-line `add` write the
same four bytes.  On the reserve they need not, which is why the memory is not
`batchMem`. -/
theorem inlBytes_eq_batchBytes (blk0 : BitVec 64) (esc : BitVec 64) {i : Nat}
    (hi : i < min (ctpop esc) 8) (hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32) :
    inlBytes (lxBase blk0) esc i = batchBytes (lxBase blk0) esc i := by
  have hi' : i < ctpop esc := (Nat.lt_min.mp hi).1
  have hX : (setLanes esc).getD i 0 < 64 := setLanes_getD_lt esc i
  have hc : (batchCast esc i).toNat = (setLanes esc).getD i 0 := by
    rw [batchCast_toNat, cttz_batchChain esc hi']
  have h : (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32) <<< 6).toNat ||| (batchCast esc i).toNat =
      (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32) <<< 6).toNat + (setLanes esc).getD i 0 := by
    rw [← BitVec.toNat_or]
    exact bv32_or_lane_toNat (z := BitVec.ofNat 32 (blk0.toNat % 2 ^ 32))
      (c := batchCast esc i) (lane := (setLanes esc).getD i 0) hc hX
  have hcap' : (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32) <<< 6).toNat + 64 ≤ 2 ^ 32 := hcap
  rw [batchBytes_eq (lxBase blk0) esc hi hcap]
  unfold inlBytes lxBase
  rw [BitVec.toNat_ofNat, h, Nat.mod_eq_of_lt (by omega)]

/-- **The inline batch's claimed entries, at the block's own memory.** -/
theorem lstIfEnd4Mem_entry (blk0 : BitVec 64) (esc : BitVec 64) (o xn count : Nat)
    (mem : Mem) {i : Nat} (hi : i < min (ctpop esc) 8)
    (hcap : (lxBase blk0).toNat + 64 ≤ 2 ^ 32)
    (hdisj : xn + 8 ≤ o ∨ o + 32 ≤ xn) :
    readBytes (lstIfEnd4Mem (lxBase blk0) esc o xn count mem) (o + 4 * i) 4 =
      some (natToBytes ((lxBase blk0).toNat + (setLanes esc).getD i 0) 4) := by
  have hi8 : i < 8 := (Nat.lt_min.mp hi).2
  unfold lstIfEnd4Mem
  rcases hdisj with hd | hd
  · rw [readBytes_writeBytes_above _ _ 4 (o + 4 * i) xn (by rw [natToBytes_length]; omega)]
    rw [inlWrites_readBytes_entry _ _ _ 8 i hi8 mem, inlBytes_eq_batchBytes blk0 esc hi hcap,
      batchBytes_eq (lxBase blk0) esc hi hcap]
  · rw [readBytes_writeBytes_below _ _ 4 (o + 4 * i) xn (by omega)]
    rw [inlWrites_readBytes_entry _ _ _ 8 i hi8 mem, inlBytes_eq_batchBytes blk0 esc hi hcap,
      batchBytes_eq (lxBase blk0) esc hi hcap]

/-- **The frame**: a byte outside the inline batch's thirty-two and outside the
count's eight is the byte it was. -/
theorem lstIfEnd4Mem_unchanged (base : BitVec 32) (esc : BitVec 64) (o xn count : Nat)
    (mem : Mem) {a : Nat} (h : a < o ∨ o + 32 ≤ a) (h2 : a < xn ∨ xn + 8 ≤ a) :
    readByte (lstIfEnd4Mem base esc o xn count mem) a = readByte mem a := by
  unfold lstIfEnd4Mem
  rw [readByte_writeBytes_outside _ _ h2]
  exact inlWrites_frame base esc o 8 a (by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)) mem


/-! ### The block's one control step -/

/-- **`if.end.i4`'s one control step.**  The block leaves the inline batch and the
advanced count, and branches to the writer's first preheader exactly when the
inline batch left positions behind. -/
theorem lstIfEnd4_step (env : Env) (s : State) (esc : BitVec 64) (base : BitVec 32)
    (xp xn c0 : Nat)
    (hpc : (withEnv env s).pc = "if.end.i4")
    (hes : lookupName env "%and31.i" = some (.int 64 esc))
    (hconv : lookupName env "%conv" = some (.int 32 base))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxn : lookupName env "%xn" = some (.ptr xn))
    (hc0 : c0 < 2 ^ 63)
    (hld : readBytes s.mem xn 8 = some (natToBytes c0 8)) :
    ∃ (e : State), step escapeCalls escapeListFunction (withEnv env s) = .jump e ∧
      e.pc = lstIfEnd4Next esc ∧
      e.mem = lstIfEnd4Mem base esc (xp + c0 * 4) xn (lstIfEnd4Count c0 esc) s.mem ∧
      lstWriterKeeps env e.env ∧
      lookupName e.env "%add.ptr.i.i" = some (.ptr (xp + c0 * 4)) ∧
      lookupName e.env "%add.i.i" = some (.int 64 (lstIfEnd4CellCount c0 esc)) ∧
      lookupName e.env "%cmp.i.i" = some (.int 1
        (evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8))) := by
  obtain ⟨hmem, hbs, hctl, him, hblk, hxp', hxn', hcarry, harr, handi, hconv', haddr,
    hcount, hcmp⟩ := lstIfEnd4_run env s esc base xp xn c0 hes hconv hxp hxn hc0 hld
  obtain ⟨st, hst, _⟩ := Option.bind_eq_some_iff.mp haddr
  have hstmem : st.mem =
      lstIfEnd4Mem base esc (xp + c0 * 4) xn (lstIfEnd4Count c0 esc) s.mem := by
    obtain ⟨st', hst', hEq⟩ := Option.map_eq_some_iff.mp hmem
    have hss : st = st' := Option.some.inj (hst.symm.trans hst')
    rw [hss]; exact hEq
  have hstep : step escapeCalls escapeListFunction (withEnv env s) = execTerm st lstIfEnd4.term :=
    step_of (withEnv env s) "if.end.i4" lstIfEnd4 st hpc findBlock_ifEnd4 hst
  rw [hstep, lstIfEnd4_term]
  have hval : evalOperand st (.reg "%cmp.i.i") =
      some (.int 1 (evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8))) := by
    show lookupName st.env "%cmp.i.i" = _
    simpa only [hst, Option.bind_some] using hcmp
  have h8 : (BitVec.ofInt 64 8 : BitVec 64).toNat = 8 := by decide
  have hct : (BitVec.ofNat 64 (ctpop esc)).toNat = ctpop esc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have h1 := ctpop_eq_setLanes_length esc
    have h2 := setLanes_length_le esc
    omega
  by_cases hgt : ctpop esc > 8
  · have hone : evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8) = (1 : BitVec 1) := by
      rw [evalICmp_ugt_one_iff_toNat, h8, hct]; omega
    have hnext : lstIfEnd4Next esc = "for.body.preheader.i.i" := by
      unfold lstIfEnd4Next; rw [ite_eq_left hgt]
    rw [execTerm_condbr_one _ _ _ _ _ hval hone]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnext]
    · exact hstmem
    · exact ⟨by simpa only [hst, Option.bind_some] using hbs, by simpa only [hst, Option.bind_some] using hctl, by simpa only [hst, Option.bind_some] using him, by simpa only [hst, Option.bind_some] using hblk, by simpa only [hst, Option.bind_some] using hxp',
        by simpa only [hst, Option.bind_some] using hxn', by simpa only [hst, Option.bind_some] using hcarry, by simpa only [hst, Option.bind_some] using harr, by simpa only [hst, Option.bind_some] using handi, by simpa only [hst, Option.bind_some] using hconv'⟩
    · simpa only [hst, Option.bind_some] using haddr
    · simpa only [hst, Option.bind_some] using hcount
    · simpa only [hst, Option.bind_some] using hcmp
  · have hzero : evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8) = (0 : BitVec 1) := by
      rcases bitVec_one_eq_zero_or_one
        (evalICmp .ugt (BitVec.ofNat 64 (ctpop esc)) (BitVec.ofInt 64 8)) with h0 | h1
      · exact h0
      · exfalso
        have := (evalICmp_ugt_one_iff_toNat _ _).mp h1
        rw [h8, hct] at this
        omega
    have hnext : lstIfEnd4Next esc = "xl_emit.exit" := by
      unfold lstIfEnd4Next; rw [ite_eq_right hgt]
    rw [execTerm_condbr_zero _ _ _ _ _ hval hzero]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnext]
    · exact hstmem
    · exact ⟨by simpa only [hst, Option.bind_some] using hbs, by simpa only [hst, Option.bind_some] using hctl, by simpa only [hst, Option.bind_some] using him, by simpa only [hst, Option.bind_some] using hblk, by simpa only [hst, Option.bind_some] using hxp',
        by simpa only [hst, Option.bind_some] using hxn', by simpa only [hst, Option.bind_some] using hcarry, by simpa only [hst, Option.bind_some] using harr, by simpa only [hst, Option.bind_some] using handi, by simpa only [hst, Option.bind_some] using hconv'⟩
    · simpa only [hst, Option.bind_some] using haddr
    · simpa only [hst, Option.bind_some] using hcount
    · simpa only [hst, Option.bind_some] using hcmp


/-- The count's stored bytes are the record's word: the caller's count plus the
inline claim. -/
theorem lstIfEnd4_cellCount_bytes (c0 : Nat) (esc : BitVec 64) :
    natToBytes (lstIfEnd4CellCount c0 esc).toNat 8 =
      wordBytes 8 (lstIfEnd4Count c0 esc) := by
  simp only [lstIfEnd4CellCount, lstUmin8]
  rw [lstIfEnd4_count_compose]
  exact lstIfEnd4_count_bytes c0 esc

/-! ### Axiom footprints

Two of these carry `Classical.choice`.  Its carrier is
`Nat.mod_mul_right_div_self`, the division lemma `natToBytes_mod_pow` uses to see
that `natToBytes` reads only the low bytes a width keeps; the repository already
names it at the same place in the masks' module.  Nothing else in this module
opens a choice. -/

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_run

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_step

/-- info: 'LeanLLVM.Vellum.inlBytes_eq_batchBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inlBytes_eq_batchBytes

/-- info: 'LeanLLVM.Vellum.lstIfEnd4Mem_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4Mem_entry

/-- info: 'LeanLLVM.Vellum.lstIfEnd4Mem_unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4Mem_unchanged

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_cellCount_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_cellCount_bytes

/-- info: 'LeanLLVM.Vellum.natToBytes_mod_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natToBytes_mod_pow

/-- info: 'LeanLLVM.Vellum.b_or32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_or32


/-! ### The out-of-line batch, as an instruction

The writer loop's third instruction calls `@xl_batch`; the list's call environment
resolves that symbol at the batch's own record (`JsonEscapeIR`), and the record's
run gives the count and the memory (`JsonEscapeListInvariant`).  The two lemmas
below are the call-site form: the instruction's value is the record's count, its
memory the batch's, and the allocator base unchanged — `envForUnit` advances
`next` by zero, which is what makes a loop iteration allocate nothing. -/

/-- A call to `@xl_batch` in the list's environment does not move the allocator. -/
theorem xl_batch_call_next (esc : BitVec 64) (base : BitVec 32) (o : Nat) (mem : Mem)
    (next : Nat) :
    ∀ r, escapeListCalls Γ_xl_batch "xl_batch" [.int 64 esc, .int 32 base, .ptr o]
        mem next = some r → r.next = next := by
  intro r h
  rw [escapeListCalls_xlBatch] at h
  simp only [envForUnit, ↓reduceIte] at h
  split at h
  all_goals (first
    | (injection h with h'; subst h'; simp)
    | (cases h))

/-- `%d = call i32 @xl_batch(i64 %c, i32 %conv, ptr %o)`. -/
theorem b_call_batch (env : Env) (s : State) (d c o : String) (esc : BitVec 64)
    (base : BitVec 32) (n : Nat)
    (hesc : lookupName env c = some (.int 64 esc))
    (hbase : lookupName env "%conv" = some (.int 32 base))
    (ho : lookupName env o = some (.ptr n)) :
    evalInstr (escapeListCalls Γ_xl_batch) (withEnv env s)
        (.call d (.int 32) "xl_batch"
          [(.int 64, .reg c), (.int 32, .reg "%conv"), (.ptr, .reg o)]) =
      some (withEnv
        ((d, .int 32 (umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8))) :: env)
        { s with mem := batchMem base esc n s.mem }) := by
  obtain ⟨r, hcall, hret, hmem⟩ := xl_batch_call_eq esc base n s.mem s.next
  have hnext : r.next = s.next := xl_batch_call_next esc base n s.mem s.next r hcall
  rw [evalInstr_call
    (ha := evalOperands_cons (evalOperand_reg_of env s c (.int 64 esc) hesc)
      (evalOperands_cons (evalOperand_reg_of env s "%conv" (.int 32 base) hbase)
        (evalOperands_cons (evalOperand_reg_of env s o (.ptr n) ho) (by rfl))))
    (hc := hcall)]
  rw [hret, hmem, hnext]
  simp only [withEnv]

/-- info: 'LeanLLVM.Vellum.xl_batch_call_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xl_batch_call_next

/-- info: 'LeanLLVM.Vellum.b_call_batch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_batch

/-- info: 'LeanLLVM.Vellum.ofNat32_ofNat64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofNat32_ofNat64

/-- info: 'LeanLLVM.Vellum.ofNat64_ofNat32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofNat64_ofNat32

/-- info: 'LeanLLVM.Vellum.umin_ofNat_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms umin_ofNat_eight

/-- info: 'LeanLLVM.Vellum.ofNat64_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofNat64_add

/-- info: 'LeanLLVM.Vellum.natToBytes_mod_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natToBytes_mod_two_pow

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_count_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_count_compose

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_count_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_count_bytes

/-- info: 'LeanLLVM.Vellum.inlWrites_readBytes_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inlWrites_readBytes_entry

/-- info: 'LeanLLVM.Vellum.inlWrites_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inlWrites_frame

/-- info: 'LeanLLVM.Vellum.readBytes_writeBytes_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_above


/-! ### The bridge between the lane predicate and the position list

`ListLoopInv` states its first conjunct as a *lane membership* — the residual
word's set lanes are the positions not yet emitted — while its second conjunct is
about the *list* `position.drop used`.  A step that advances `used` has to pass
from one to the other, and that passes through one list fact: a strictly
increasing list of lanes, all below the word, is exactly the range filtered by
membership in it.  The three lemmas prove that fact and apply it. -/

/-- A list with no members is empty.  Stated here rather than through
`List.eq_nil_iff_forall_not_mem`, whose proof carries `Classical.choice`. -/
theorem eq_nil_of_forall_not_mem {l : List Nat} (h : ∀ a, a ∉ l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t => exact absurd (List.mem_cons_self ..) (h a)

/-- An increasing list splits at a lane into the entries below it and the rest. -/
theorem filter_lt_append_not (l : List Nat) (n : Nat) (hs : l.Pairwise (· < ·)) :
    l.filter (fun k => decide (k < n)) ++ l.filter (fun k => decide (¬ k < n)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨halt, hst⟩ := hs
      by_cases ha : a < n
      · rw [List.filter_cons, ite_eq_left (by simp [ha]), List.filter_cons,
            ite_eq_right (by simp [ha])]
        rw [List.cons_append, ih hst]
      · rw [List.filter_cons, ite_eq_right (by simp [ha]), List.filter_cons,
            ite_eq_left (by simp [ha])]
        have hnil : t.filter (fun k => decide (k < n)) = [] :=
          filter_eq_nil_of_all_false (fun k hk => by
            have hlt := halt k hk
            show decide (k < n) = false
            rw [decide_eq_false (by omega)])
        rw [hnil, List.nil_append] at ih
        rw [ih hst, hnil, List.nil_append]

/-- **The range filtered by membership is the list**, for a strictly increasing
list whose entries lie below the range.  This is the direction `BitLanes` does not
state: its `setLanes_getElem?_rank` reads the list out of the word, and here the
word is what we are trying to read. -/
theorem filter_range_mem_eq_self (l : List Nat) (n : Nat) :
    l.Pairwise (· < ·) → (∀ k ∈ l, k < n) →
      (List.range n).filter (fun k => decide (k ∈ l)) = l := by
  revert l
  induction n with
  | zero =>
      intro l hs hlt
      have hl : l = [] := eq_nil_of_forall_not_mem (fun k hk => by
        have := hlt k hk
        omega)
      rw [hl]
      simp
  | succ n ih =>
      intro l hs hlt
      rw [List.range_succ, List.filter_append]
      have hlt₁ : ∀ k ∈ l.filter (fun k => decide (k < n)), k < n := by
        intro k hk
        rw [List.mem_filter] at hk
        exact of_decide_eq_true hk.2
      have hf₁ : (List.range n).filter (fun k => decide (k ∈ l))
          = l.filter (fun k => decide (k < n)) := by
        have hcongr : (List.range n).filter (fun k => decide (k ∈ l))
            = (List.range n).filter
                (fun k => decide (k ∈ l.filter (fun k => decide (k < n)))) := by
          apply List.filter_congr
          intro k hk
          have hkn : k < n := List.mem_range.mp hk
          have hiff : k ∈ l ↔ k ∈ l.filter (fun k => decide (k < n)) := by
            rw [List.mem_filter]
            exact ⟨fun h => ⟨h, decide_eq_true hkn⟩, fun h => h.1⟩
          by_cases h : k ∈ l
          · rw [decide_eq_true h, decide_eq_true (hiff.mp h)]
          · rw [decide_eq_false h, decide_eq_false (fun hc => h (hiff.mpr hc))]
        rw [hcongr]
        exact ih (l.filter (fun k => decide (k < n))) (List.Pairwise.filter _ hs) hlt₁
      have hall₂ : ∀ x ∈ l.filter (fun k => decide (¬ k < n)), x = n := by
        intro x hx
        rw [List.mem_filter] at hx
        have hxn : ¬ x < n := of_decide_eq_true hx.2
        have hxlt : x < n + 1 := hlt x hx.1
        omega
      have hmem₂ : n ∈ l ↔ n ∈ l.filter (fun k => decide (¬ k < n)) := by
        constructor
        · intro h
          rw [List.mem_filter]
          exact ⟨h, decide_eq_true (by omega)⟩
        · intro h
          rw [List.mem_filter] at h
          exact h.1
      have hl₂ : l.filter (fun k => decide (¬ k < n)) = if n ∈ l then [n] else [] := by
        have hlr : l.filter (fun k => decide (¬ k < n)) = []
            ∨ l.filter (fun k => decide (¬ k < n)) = [n] := by
          rcases hl : l.filter (fun k => decide (¬ k < n)) with _ | ⟨a, rest⟩
          · exact Or.inl rfl
          · cases rest with
            | nil =>
                right
                have ha : a = n := hall₂ a (by rw [hl]; simp)
                rw [ha]
            | cons b rest =>
                exfalso
                have hs₂ := List.Pairwise.filter (fun k => decide (¬ k < n)) hs
                rw [hl, List.pairwise_cons, List.pairwise_cons] at hs₂
                have ha : a = n := hall₂ a (by rw [hl]; simp)
                have hb : b = n := hall₂ b (by rw [hl]; simp)
                have := hs₂.1 b (by simp)
                omega
        rcases hlr with h | h
        · rw [h, ite_eq_right]
          intro hn
          have hn₂ := hmem₂.mp hn
          rw [h] at hn₂
          simp at hn₂
        · rw [h, ite_eq_left]
          exact hmem₂.mpr (by rw [h]; simp)
      have hf₃ : ([n] : List Nat).filter (fun k => decide (k ∈ l))
          = if n ∈ l then [n] else [] := by
        by_cases hn : n ∈ l
        · rw [List.filter_cons, ite_eq_left (by simp [hn]), List.filter_nil, ite_eq_left hn]
        · rw [List.filter_cons, ite_eq_right (by simp [hn]), List.filter_nil, ite_eq_right hn]
      rw [hf₁, hf₃, ← hl₂]
      exact filter_lt_append_not l n hs

/-- **The bridge.**  A residual word whose lanes are exactly an increasing list's
members *is* that list's mask: `ListLoopInv`'s lane predicate becomes the store's
list equality. -/
theorem setLanes_eq_of_lane_mem {w : BitVec 64} {l : List Nat}
    (hs : l.Pairwise (· < ·)) (hlt : ∀ k ∈ l, k < 64)
    (h : ∀ k, k < 64 → w.getLsbD k = decide (k ∈ l)) :
    setLanes w = l := by
  rw [setLanes]
  rw [show (List.range 64).filter (fun i => w.getLsbD i)
      = (List.range 64).filter (fun i => decide (i ∈ l)) from
    List.filter_congr (fun k hk => h k (List.mem_range.mp hk))]
  exact filter_range_mem_eq_self l 64 hs hlt

/-- info: 'LeanLLVM.Vellum.setLanes_eq_of_lane_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms setLanes_eq_of_lane_mem

/-- info: 'LeanLLVM.Vellum.filter_range_mem_eq_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_range_mem_eq_self

/-- **The cursor the writer starts from is the store's end.**  The preheader puts
`%add.ptr5.i.i` at `%add.ptr.i.i + 32`, and the branch that enters the loop has
`ctpop esc > 8`, so the inline batch claimed exactly eight entries — the cursor is
`xp + 4 * (xn0 + used)` at loop entry, which is what ties the loop invariant's
count to its cursor. -/
theorem lstIfEnd4_cursor_eq (xp c0 : Nat) (esc : BitVec 64) (h : ctpop esc > 8) :
    xp + 4 * c0 + 32 = xp + 4 * lstIfEnd4Count c0 esc := by
  unfold lstIfEnd4Count
  rw [Nat.min_eq_right (by omega)]
  omega

/-- info: 'LeanLLVM.Vellum.eq_nil_of_forall_not_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms eq_nil_of_forall_not_mem

/-- info: 'LeanLLVM.Vellum.filter_lt_append_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms filter_lt_append_not

/-- info: 'LeanLLVM.Vellum.lstIfEnd4_cursor_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstIfEnd4_cursor_eq

end LeanLLVM.Vellum
