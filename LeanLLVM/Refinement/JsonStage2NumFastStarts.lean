/-
`num_fast_el1`'s scan dispatch: the runs' starts, fixed from the sign, the `.`,
the `e` and its sign.

`JsonStage2NumFastDigitRuns` states each of the body's three digit runs as a
`BoundLoop` and proves the instance, but at the run's own start `i0` and `d0`:
the integer run from `i0` with `d0` digits already counted, the fraction run
from its `i0` with `d0 = 0`, and the exponent run from its `i0` with an empty
accumulator.  The counters are therefore offsets from an arbitrary head entry,
and what fixes them is the straight-line dispatch before the loop:

    entry → land.lhs.true → if.end → if.end6 → if.else → if.then22 → while.end
          → land.lhs.true41.preheader → land.lhs.true41

and the same shape after the integer run (`if.end68` … `land.lhs.true119`), and
after the fraction run (`if.end144` … `land.lhs.true195`).  This module is that
dispatch, block by block, and its composition into each run's initial invariant.

**What it fixes.**  For the integer run, the head's entry edge carries
`%i.1558`, `%idig.0560` and `%ip.0562`; the dispatch proves they are the index
after the `int` part's leading digit, the count `1` (that digit), and its
value.  The run invariant's `d0` is therefore `1` and its `i0` the index after
the lead.  A lexeme whose `int` part is `0` alone does not enter the run at all:
`if.end6`'s `'0'` test goes to `if.then11`, which jumps straight to `if.end68`
with `%i.5 = i0 + 1`, `%idig.4 = 1`, `%ip.5 = 0` — the `0`-alone rule.

For the fraction run the start is the byte after the `.` with `d0 = 0` and an
empty accumulator; for the exponent run the start is the byte after the `e`/`E`
and its optional sign, with an empty accumulator.  Each is reached only when the
dispatch's tests hold — a digit where the grammar requires one — so a lexeme the
emitted tests refuse is a refusal path rather than a run (`if.else66` for a
non-digit `int` lead, `if.then89` for a `.` with no digit after it, `cleanup223`
for an `e` with no digit after it).

**The two fast paths, which are not this module's.**  Both the integer and the
fraction part have an eight-digit `num_d8_el1` fast path (`while.body`/`cleanup`
at `if.then22`, `while.body100`/`cleanup112` at `while.cond91.preheader`).  That
path is a second loop, with an out-of-line call whose answer is a `Calls`
entry's; the dispatch below is proved for the branch on which its guard is
refused (`%add563 > %n`, `%add92582 > %n`), and behind that guard the registers
this module fixes are the loop's own.  The fast path leaves `%i.1558 = i0 + 8k + 1`
and `%idig.0560 = 1 + 8k`, which is the run's start after the groups; deriving
that is the fast path's loop, and the statements here name it as the boundary.

Each block is one `step` read from its own `findBlock` pin — never a re-reading
of `numFastBody`'s block list — and every `denoteCode` is the block's literal
instruction list.  The dispatch has no calls on the paths proved, so each
theorem is at an arbitrary `Calls`, and instantiates at both `s2HelperCalls` and
`stage2NumFastCalls` without a choice.
-/
import LeanLLVM.Refinement.JsonStage2NumFastDigitRuns
import LeanLLVM.Refinement.JsonScanLane

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

/- The dispatch's own vocabulary.  Namespaced because the escape bodies carry
blocks named `if.end`/`if.then22` too, and their lemmas are already in
`LeanLLVM.Refinement`. -/
namespace NumFastStarts

/-! ### Reading a comparison's bit

`evalICmp` is `BitVec.ofBool` of the predicate, so a comparison's bit is one
exactly when the predicate holds; `JsonEscapeListBody` and
`JsonEscapeDecodeRun` carry the two readings this module needs, and the third
below is the `0` direction the refusals read. -/

theorem ofBool_bool {b : Bool} : BitVec.ofBool b = 1 ↔ b = true := by
  cases b <;> decide

theorem ofBool_prop {p : Prop} [Decidable p] : BitVec.ofBool p = 1 ↔ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

/-- The unsigned test at one. -/
theorem ult_iff_one {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (1 : BitVec 1) ↔ x.toNat < y.toNat := by
  rw [show evalICmp .ult x y = BitVec.ofBool (x.ult y) from rfl, ofBool_bool]
  exact BitVec.ult_iff_toNat_lt

/-- The unsigned test at zero. -/
theorem ult_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (0 : BitVec 1) ↔ ¬ x.toNat < y.toNat := by
  constructor
  · intro h hh
    have h1 : evalICmp .ult x y = 1 := (ult_iff_one x y).mpr hh
    rw [h1] at h
    exact absurd h (by decide)
  · intro h
    rcases bitVec1_eq_zero_or_one (evalICmp .ult x y) with hu | hu
    · exact hu
    · exact absurd ((ult_iff_one x y).mp hu) h

/-- The equality test at one. -/
theorem eq_iff_one {w : Nat} (x y : BitVec w) :
    evalICmp .eq x y = (1 : BitVec 1) ↔ x = y := by
  rw [show evalICmp .eq x y = BitVec.ofBool (decide (x = y)) from rfl]
  exact ofBool_prop

/-- The equality test at zero. -/
theorem eq_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .eq x y = (0 : BitVec 1) ↔ x ≠ y := by
  constructor
  · intro h hh
    rw [← eq_iff_one x y] at hh
    rw [hh] at h
    exact absurd h (by decide)
  · intro h
    rcases bitVec1_eq_zero_or_one (evalICmp .eq x y) with hu | hu
    · exact hu
    · exact absurd ((eq_iff_one x y).mp hu) h

/-- Two bytes are the same byte exactly when their 8-bit readings are. -/
theorem vByte_inj {b b' : UInt8} (h : JsonScanLane.vByte b = JsonScanLane.vByte b') :
    b = b' := by
  have h2 := congrArg BitVec.toNat h
  simp only [JsonScanLane.vByte, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt b.toNat_lt, Nat.mod_eq_of_lt b'.toNat_lt] at h2
  exact UInt8.toNat_inj.mp h2

theorem vByte_eq_iff {b b' : UInt8} :
    JsonScanLane.vByte b = JsonScanLane.vByte b' ↔ b = b' :=
  ⟨vByte_inj, fun h => by rw [h]⟩

/-- The sign byte's index: `1` for a leading `minus`, `0` without one.  This is
`if.end`'s `%i.0` at a `land.lhs.true` predecessor. -/
def negIndex (b : UInt8) : Nat := if b = 0x2D then 1 else 0

/-- `%cmp1 = (%0 != 0x2d)`: the sign test, as a bit. -/
theorem evalICmp_ne_minus (b : UInt8) :
    evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 = (if b = 0x2D then 0 else 1) := by
  unfold evalICmp
  by_cases h : b = 0x2D
  · subst h; simp [JsonScanLane.vByte]
  · have hne : JsonScanLane.vByte b ≠ 0x2d#8 := fun hh => h (vByte_inj hh)
    simp [h, hne]

/-- The sign test's complement: `%not.cmp1`, one exactly at a leading `minus`. -/
theorem xor_one_sign (x : BitVec 1) :
    x ^^^ 0x1#1 = (if x = 0 then 1 else 0) := by
  rcases bitVec1_eq_zero_or_one x with h | h <;> subst h <;> decide

/-- `%spec.select439`, the sign's `zext`, as the sign's index. -/
theorem specSel_negIndex (b : UInt8) :
    BitVec.ofNat 64 ((evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)).toNat
      = BitVec.ofNat 64 (negIndex b) := by
  by_cases h : b = 0x2D
  · have h1 : evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 = 0 := by
      rw [evalICmp_ne_minus b, if_pos h]
    rw [h1, negIndex, if_pos h]
    decide
  · have h1 : evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 = 1 := by
      rw [evalICmp_ne_minus b, if_neg h]
    rw [h1, negIndex, if_neg h]
    decide

/-! ### The three digit windows

The dispatch tests a byte against `'0' … '9'` in three spellings: the `int`
head's `(b + 0xd0) <u 10`, the fraction and exponent heads' identical test, and
the lead rule `(b + 0xcf) <u 9` at `if.else` (which excludes `'0'`, handled
before it).  The refusal tests are `(b + 0xc6) <u 0xf6` at `lor.lhs.false` and
`lor.lhs.false180`, which hold exactly off the digit window.  Each is stated at
the byte's `Nat` reading, the form the dispatch's case analysis closes with. -/

theorem isDigitB_iff_interval (b : UInt8) :
    IsDigitB b = true ↔ (0x30 ≤ b ∧ b ≤ 0x39) := by
  simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq]

theorem isDigitB_toNat_iff (b : UInt8) :
    IsDigitB b = true ↔ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [isDigitB_iff_interval, UInt8.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  simp

theorem isDigitB_false_toNat (b : UInt8) :
    IsDigitB b = false ↔ ¬ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [← isDigitB_toNat_iff]
  constructor
  · intro h hh
    rw [hh] at h; exact absurd h (by decide)
  · intro h
    cases hb : IsDigitB b <;> simp_all

/-- The lead window `'1' … '9'`, as `%or.cond = ((b + 0xcf) <u 9)`. -/
theorem ult_leadDigit_toNat (b : UInt8) :
    (JsonScanLane.vByte b + 0xcf#8).ult (0x09#8) = true ↔
      (49 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [BitVec.ult_iff_toNat_lt, bv_add_toNat, vByte_toNat,
    show (0xcf#8 : BitVec 8).toNat = 207 from rfl,
    show (0x09#8 : BitVec 8).toNat = 9 from rfl]
  have hb := b.toNat_lt
  constructor
  · intro h
    by_cases h1 : b.toNat < 49
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    · refine ⟨by omega, ?_⟩
      by_contra h2
      rw [show b.toNat + 207 = (b.toNat - 49) + 256 from by omega, Nat.add_mod,
        show (256 : Nat) % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro ⟨h1, h2⟩
    rw [show b.toNat + 207 = (b.toNat - 49) + 256 from by omega, Nat.add_mod,
      show (256 : Nat) % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The lead window at the `Nat` reading, the form the dispatch's arithmetic
closes with. -/
theorem ult_leadDigit_lt (b : UInt8) :
    (JsonScanLane.vByte b + 0xcf#8).toNat < (0x09#8).toNat ↔
      (49 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [← BitVec.ult_iff_toNat_lt, ult_leadDigit_toNat]

/-- The digit window `'0' … '9'` as the heads' `(b + 0xd0) <u 10`, at the
byte's `Nat` reading. -/
theorem ult_digit_toNat (b : UInt8) :
    (JsonScanLane.vByte b + 0xd0#8).ult (0x0a#8) = true ↔
      (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [isDigitB_iff_ult, isDigitB_toNat_iff]

/-- The refusal test `%or.cond441`, at the byte's `Nat` reading: outside the
digit window. -/
theorem ult_nondigit_toNat (b : UInt8) :
    (JsonScanLane.vByte b + 0xc6#8).ult (0xf6#8) = true ↔
      ¬ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [BitVec.ult_iff_toNat_lt, bv_add_toNat, vByte_toNat,
    show (0xc6#8 : BitVec 8).toNat = 198 from rfl,
    show (0xf6#8 : BitVec 8).toNat = 246 from rfl]
  have hb := b.toNat_lt
  constructor
  · intro h
    by_cases hlt : b.toNat < 48
    · omega
    · refine fun hc => ?_
      rw [show b.toNat + 198 = b.toNat + 198 from rfl,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro h
    by_cases hlt : b.toNat < 48
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have hgt : 57 < b.toNat := by
        by_contra hh
        exact h ⟨by omega, by omega⟩
      rw [show b.toNat + 198 = (b.toNat - 58) + 256 from by omega, Nat.add_mod,
        show (256 : Nat) % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega)]
      omega

/-- The refusal test at the `Nat` reading. -/
theorem ult_nondigit_lt (b : UInt8) :
    (JsonScanLane.vByte b + 0xc6#8).toNat < (0xf6#8).toNat ↔
      ¬ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by
  rw [← BitVec.ult_iff_toNat_lt, ult_nondigit_toNat]

/-! ### `land.lhs.true`: the sign check

`%0` is the first byte, `%cmp1` is `%0 != '-'`, `%not.cmp1` its complement and
`%spec.select439` the `zext` of that complement to `i64` — the value `if.end`'s
`%i.0` phi takes. -/

theorem sign_denote {calls : Calls} {env : Env} {s : State} {a : Nat} {b : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hread : readByte s.mem a = some b) :
    denoteCode calls numFastLandLhsTrueInstrs (stateAt env s) =
      some (stateAt
        (("%spec.select439", .int 64 (BitVec.ofNat 64
            ((evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)).toNat)) ::
         ("%not.cmp1", .int 1
            (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)) ::
         ("%cmp1", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) ::
         ("%0", .int 8 (JsonScanLane.vByte b)) :: env) s) := by
  unfold numFastLandLhsTrueInstrs
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%0" "%p" hp
    (readBytes_one_some.mpr hread) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp1" "%0" .ne
    (lookupName_cons_self ..) _]
  rw [JsonScanLane.denoteCode_xor_imm_w _ _ _ "%not.cmp1" "%cmp1" 1
    (lookupName_cons_self ..) _]
  rw [denoteCode_zext _ _ _ "%spec.select439" "%not.cmp1" 1 64
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt]

theorem sign_step {calls : Calls} {env : Env} {s : State} {a : Nat} {b : UInt8}
    (hpc : s.pc = "land.lhs.true")
    (hp : lookupName env "%p" = some (.ptr a))
    (hread : readByte s.mem a = some b) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt
        (("%spec.select439", .int 64 (BitVec.ofNat 64
            ((evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)).toNat)) ::
         ("%not.cmp1", .int 1
            (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)) ::
         ("%cmp1", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) ::
         ("%0", .int 8 (JsonScanLane.vByte b)) :: env)
        { s with pc := "if.end", pre := some "land.lhs.true" }) := by
  refine numFast_step_at (s' := stateAt
      (("%spec.select439", .int 64 (BitVec.ofNat 64
          ((evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)).toNat)) ::
       ("%not.cmp1", .int 1
          (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)) ::
       ("%cmp1", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) ::
       ("%0", .int 8 (JsonScanLane.vByte b)) :: env) s)
    (b := ⟨"land.lhs.true", numFastLandLhsTrueInstrs, Term.br "if.end"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrueInstrs]
      using numFast_findBlock_land_lhs_true
  · simpa only [denoteCode_nil] using sign_denote (calls := calls) hp hread
  · simp only [execTerm, stateAt, hpc]

/-! ### The sign's index, bounded

`negIndex` is `0` or `1`, so every index the dispatch forms from it stays below
the word's modulus without a hypothesis. -/

theorem negIndex_le_one (b : UInt8) : negIndex b ≤ 1 := by
  unfold negIndex; split <;> omega

/-- A 64-bit word plus a small constant, as the blocks' `add` writes it. -/
theorem ofNat64_add_const {j k : Nat} (hk : j + k < 2 ^ 64) :
    BitVec.ofNat 64 j + BitVec.ofNat 64 k = BitVec.ofNat 64 (j + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hj : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hk' : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [hj, hk']

/-- The unsigned-greater test at one. -/
theorem ugt_iff_one {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (1 : BitVec 1) ↔ y.toNat < x.toNat := by
  rw [show evalICmp .ugt x y = BitVec.ofBool (BitVec.ult y x) from rfl, ofBool_bool,
    BitVec.ult_iff_toNat_lt]

/-- `land.lhs.true`'s environment: `%0`, `%cmp1`, `%not.cmp1` and the sign's
`zext`.  `sign_denote`'s statement is this builder's body. -/
def signEnv (env : Env) (b : UInt8) : Env :=
  ("%spec.select439", .int 64 (BitVec.ofNat 64
      ((evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)).toNat)) ::
  ("%not.cmp1", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 ^^^ 0x1#1)) ::
  ("%cmp1", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) ::
  ("%0", .int 8 (JsonScanLane.vByte b)) :: env

theorem signEnv_cmp1 (env : Env) (b : UInt8) :
    lookupName (signEnv env b) "%cmp1"
      = some (.int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) := by
  simp only [signEnv,
    lookupName_cons_ne (k := "%spec.select439") (n := "%cmp1") _ _ (by decide),
    lookupName_cons_ne (k := "%not.cmp1") (n := "%cmp1") _ _ (by decide),
    lookupName_cons_self]

theorem signEnv_spec (env : Env) (b : UInt8) :
    lookupName (signEnv env b) "%spec.select439"
      = some (.int 64 (BitVec.ofNat 64 (negIndex b))) := by
  simp only [signEnv, lookupName_cons_self, specSel_negIndex]

/-- `if.end`'s two `phi`s: the sign's bit and the sign's index. -/
def ifEndPhiEnv (env : Env) (b : UInt8) : Env :=
  ("%i.0", .int 64 (BitVec.ofNat 64 (negIndex b))) ::
  ("%tobool274.not", .int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)) :: env

def ifEndEnv (env : Env) (b : UInt8) (n : Nat) : Env :=
  ("%cmp3.not", .int 1
      (evalICmp .ult (BitVec.ofNat 64 (negIndex b)) (BitVec.ofNat 64 n))) ::
  ifEndPhiEnv env b

/-- **`if.end`'s reading.**  The two `phi`s take the sign's bit and index from
`land.lhs.true`, and `%cmp3.not` tests the index against the length. -/
theorem ifEnd_denote {calls : Calls} {env : Env} {s : State} {b : UInt8} {n : Nat}
    (hpre : s.pre = some "land.lhs.true")
    (hc : lookupName env "%cmp1"
      = some (.int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)))
    (hs : lookupName env "%spec.select439"
      = some (.int 64 (BitVec.ofNat 64 (negIndex b))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    denoteCode calls numFastIfEndInstrs (stateAt env s) =
      some (stateAt (ifEndEnv env b n) s) := by
  unfold numFastIfEndInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%cmp1" _ hc
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%spec.select439" _ hs
  · simp only [runCells, ifEndPhiEnv]
    rw [JsonScanLane.denoteCode_icmp_reg_w (x := BitVec.ofNat 64 (negIndex b))
      (y := BitVec.ofNat 64 n) _ _ _ "%cmp3.not" "%i.0" "%n" .ult 64
      (lookupName_cons_self ..) (by block_lk) _]
    simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifEndEnv, ifEndPhiEnv]

theorem ifEnd_step {calls : Calls} {env : Env} {s : State} {b : UInt8} {n : Nat}
    (hpc : s.pc = "if.end") (hpre : s.pre = some "land.lhs.true")
    (hc : lookupName env "%cmp1"
      = some (.int 1 (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8)))
    (hs : lookupName env "%spec.select439"
      = some (.int 64 (BitVec.ofNat 64 (negIndex b))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbit : evalICmp .ult (BitVec.ofNat 64 (negIndex b)) (BitVec.ofNat 64 n) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEndEnv env b n) { s with pc := "if.end6", pre := some "if.end" }) := by
  refine numFast_step_at (s' := stateAt (ifEndEnv env b n) s)
    (b := ⟨"if.end", numFastIfEndInstrs,
      Term.condbr (Operand.reg "%cmp3.not") "if.end6" "if.then5"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEndInstrs] using numFast_findBlock_if_end
  · simpa only [denoteCode_nil] using ifEnd_denote (calls := calls) hpre hc hs hn
  · have hlk : lookupName (ifEndEnv env b n) "%cmp3.not"
        = some (.int 1 (evalICmp .ult (BitVec.ofNat 64 (negIndex b)) (BitVec.ofNat 64 n))) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp3.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.end6`: the `int` part's first byte

The byte at `%i.0` — the index the sign left — is loaded and tested against
`'0'`.  A `'0'` takes `if.then11` (the zero-alone arm); anything else is tested
by `if.else` for the lead window. -/

def ifEnd6Env (env : Env) (a i0 : Nat) (b0 : UInt8) : Env :=
  ("%cmp9", .int 1 (evalICmp .eq (JsonScanLane.vByte b0) 0x30#8)) ::
  ("%1", .int 8 (JsonScanLane.vByte b0)) ::
  ("%arrayidx7", .ptr (a + i0)) :: env

theorem ifEnd6_denote {calls : Calls} {env : Env} {s : State} {a i0 : Nat} {b0 : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hj : i0 < 2 ^ 63)
    (hread : readByte s.mem (a + i0) = some b0) :
    denoteCode calls numFastIfEnd6Instrs (stateAt env s) =
      some (stateAt (ifEnd6Env env a i0 b0) s) := by
  unfold numFastIfEnd6Instrs
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx7" "%p" "%i.0" hp hi
    (by rw [sExt_ofNat64 hj]; exact hj) _]
  rw [sExt_ofNat64 hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%1" "%arrayidx7" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp9" "%1" .eq
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifEnd6Env]

theorem ifEnd6_step {calls : Calls} {env : Env} {s : State} {a i0 : Nat} {b0 : UInt8}
    (hpc : s.pc = "if.end6")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hj : i0 < 2 ^ 63)
    (hread : readByte s.mem (a + i0) = some b0)
    (hbit : evalICmp .eq (JsonScanLane.vByte b0) 0x30#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd6Env env a i0 b0)
        { s with pc := "if.else", pre := some "if.end6" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd6Env env a i0 b0) s)
    (b := ⟨"if.end6", numFastIfEnd6Instrs,
      Term.condbr (Operand.reg "%cmp9") "if.then11" "if.else"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd6Instrs] using numFast_findBlock_if_end6
  · simpa only [denoteCode_nil] using ifEnd6_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (ifEnd6Env env a i0 b0) "%cmp9"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b0) 0x30#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp9" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem ifEnd6_step_zero {calls : Calls} {env : Env} {s : State} {a i0 : Nat} {b0 : UInt8}
    (hpc : s.pc = "if.end6")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hj : i0 < 2 ^ 63)
    (hread : readByte s.mem (a + i0) = some b0)
    (hbit : evalICmp .eq (JsonScanLane.vByte b0) 0x30#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd6Env env a i0 b0)
        { s with pc := "if.then11", pre := some "if.end6" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd6Env env a i0 b0) s)
    (b := ⟨"if.end6", numFastIfEnd6Instrs,
      Term.condbr (Operand.reg "%cmp9") "if.then11" "if.else"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd6Instrs] using numFast_findBlock_if_end6
  · simpa only [denoteCode_nil] using ifEnd6_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (ifEnd6Env env a i0 b0) "%cmp9"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b0) 0x30#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp9" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.else`: the lead window

`%2 = %1 + 0xcf` and `%or.cond = %2 <u 9` — the `'1' … '9'` window, since `'0'`
has already left by `if.then11`.  A lead takes `if.then22`; anything else is
`if.else66`, the refusal that stores `%i.0` at `%err`. -/

def ifElseEnv (env : Env) (b0 : UInt8) : Env :=
  ("%or.cond", .int 1 (evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8)) ::
  ("%2", .int 8 (JsonScanLane.vByte b0 + 0xcf#8)) :: env

theorem ifElse_denote {calls : Calls} {env : Env} {s : State} {b0 : UInt8}
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0))) :
    denoteCode calls numFastIfElseInstrs (stateAt env s) =
      some (stateAt (ifElseEnv env b0) s) := by
  unfold numFastIfElseInstrs
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%2" "%1" 8 h1 _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond" "%2" .ult
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifElseEnv]

theorem ifElse_step {calls : Calls} {env : Env} {s : State} {b0 : UInt8}
    (hpc : s.pc = "if.else")
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hbit : evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifElseEnv env b0)
        { s with pc := "if.then22", pre := some "if.else" }) := by
  refine numFast_step_at (s' := stateAt (ifElseEnv env b0) s)
    (b := ⟨"if.else", numFastIfElseInstrs,
      Term.condbr (Operand.reg "%or.cond") "if.then22" "if.else66"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfElseInstrs] using numFast_findBlock_if_else
  · simpa only [denoteCode_nil] using ifElse_denote (calls := calls) h1
  · have hlk : lookupName (ifElseEnv env b0) "%or.cond"
        = some (.int 1 (evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%or.cond" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem ifElse_step_refused {calls : Calls} {env : Env} {s : State} {b0 : UInt8}
    (hpc : s.pc = "if.else")
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hbit : evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifElseEnv env b0)
        { s with pc := "if.else66", pre := some "if.else" }) := by
  refine numFast_step_at (s' := stateAt (ifElseEnv env b0) s)
    (b := ⟨"if.else", numFastIfElseInstrs,
      Term.condbr (Operand.reg "%or.cond") "if.then22" "if.else66"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfElseInstrs] using numFast_findBlock_if_else
  · simpa only [denoteCode_nil] using ifElse_denote (calls := calls) h1
  · have hlk : lookupName (ifElseEnv env b0) "%or.cond"
        = some (.int 1 (evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%or.cond" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.then22`: the first digit's value, and the fast path's guard

`%3` is the lead's low nibble — the digit's value — `%conv25` its `zext`,
`%inc26 = %i.0 + 1` the index after the lead, `%add563 = %i.0 + 9`, and
`%cmp27564.not` the guard `%add563 > %n` that refuses the eight-digit fast path.
On the refusal the block jumps straight to `while.end`, which is the integer
run's start: the lead counted, the index after it, the accumulator its value. -/

def ifThen22Env (env : Env) (i0 : Nat) (b0 : UInt8) (n : Nat) : Env :=
  ("%cmp27564.not", .int 1
      (evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n))) ::
  ("%add563", .int 64 (BitVec.ofNat 64 i0 + 0x9#64)) ::
  ("%inc26", .int 64 (BitVec.ofNat 64 i0 + 0x1#64)) ::
  ("%conv25", .int 64 (BitVec.ofNat 64
      (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) ::
  ("%3", .int 8 (JsonScanLane.vByte b0 &&& 0x0f#8)) :: env

theorem ifThen22_denote {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {b0 : UInt8} {n : Nat}
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    denoteCode calls
        [Instr.binop "%3" (BinOp.and) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x0f#8)),
         Instr.zext "%conv25" 8 64 (Operand.reg "%3"),
         Instr.binop "%inc26" (BinOp.add) 64 (Operand.reg "%i.0")
           (Operand.imm (Const.int 64 0x0000000000000001#64)),
         Instr.binop "%add563" (BinOp.add) 64 (Operand.reg "%i.0")
           (Operand.imm (Const.int 64 0x0000000000000009#64)),
         Instr.icmp "%cmp27564.not" (IPred.ugt) 64 (Operand.reg "%add563")
           (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (ifThen22Env env i0 b0 n) s) := by
  rw [JsonScanLane.denoteCode_and_imm_w _ _ _ "%3" "%1" h1 _]
  rw [denoteCode_zext _ _ _ "%conv25" "%3" 8 64 (lookupName_cons_self ..) _]
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%inc26" "%i.0" 64 (by block_lk) _]
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%add563" "%i.0" 64 (by block_lk) _]
  rw [JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp27564.not" "%add563" "%n" .ugt 64
    (lookupName_cons_self ..) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifThen22Env]

theorem ifThen22_step {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {b0 : UInt8} {n : Nat}
    (hpc : s.pc = "if.then22")
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifThen22Env env i0 b0 n)
        { s with pc := "while.end", pre := some "if.then22" }) := by
  refine numFast_step_at (s' := stateAt (ifThen22Env env i0 b0 n) s)
    (b := ⟨"if.then22",
      [Instr.binop "%3" (BinOp.and) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x0f#8)),
       Instr.zext "%conv25" 8 64 (Operand.reg "%3"),
       Instr.binop "%inc26" (BinOp.add) 64 (Operand.reg "%i.0")
         (Operand.imm (Const.int 64 0x0000000000000001#64)),
       Instr.binop "%add563" (BinOp.add) 64 (Operand.reg "%i.0")
         (Operand.imm (Const.int 64 0x0000000000000009#64)),
       Instr.icmp "%cmp27564.not" (IPred.ugt) 64 (Operand.reg "%add563")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp27564.not") "while.end" "while.body.preheader"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then22
  · simpa only [denoteCode_nil] using ifThen22_denote (calls := calls) h1 hi hn
  · have hlk : lookupName (ifThen22Env env i0 b0 n) "%cmp27564.not"
        = some (.int 1
          (evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n))) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp27564.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `while.end`: the integer run's start

The `phi` run's `if.then22` edge takes `%conv25` into `%ip.0562`, the immediate
`1` into `%idig.0560` and `%inc26` into `%i.1558`; `%cmp39572` then tests
`%i.1558` against the length, and a true sends the run to its preheader. -/

def whileEndEnv (env : Env) (i0 : Nat) (b0 : UInt8) (n : Nat) : Env :=
  ("%cmp39572", .int 1
      (evalICmp .ult (BitVec.ofNat 64 i0 + 0x1#64) (BitVec.ofNat 64 n))) ::
  ("%i.1558", .int 64 (BitVec.ofNat 64 i0 + 0x1#64)) ::
  ("%idig.0560", .int 64 (0x1#64)) ::
  ("%ip.0562", .int 64 (BitVec.ofNat 64
      (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) :: env

theorem whileEnd_denote {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {b0 : UInt8} {n : Nat}
    (hpre : s.pre = some "if.then22")
    (hb : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64
      (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)))
    (hi : lookupName env "%inc26" = some (.int 64 (BitVec.ofNat 64 i0 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    denoteCode calls
        [Instr.phi "%ip.0562" (Ty.int 64)
           [("cleanup.thread", (Operand.reg "%ip.0565.lcssa")),
            ("if.then22", (Operand.reg "%conv25")),
            ("cleanup", (Operand.reg "%add35"))],
         Instr.phi "%idig.0560" (Ty.int 64)
           [("cleanup.thread", (Operand.reg "%idig.0566.lcssa")),
            ("if.then22", (Operand.imm (Const.int 64 0x0000000000000001#64))),
            ("cleanup", (Operand.reg "%add29569933"))],
         Instr.phi "%i.1558" (Ty.int 64)
           [("cleanup.thread", (Operand.reg "%i.1567.lcssa")),
            ("if.then22", (Operand.reg "%inc26")),
            ("cleanup", (Operand.reg "%add568934"))],
         Instr.icmp "%cmp39572" (IPred.ult) 64 (Operand.reg "%i.1558")
           (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (whileEndEnv env i0 b0 n) s) := by
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%conv25" _ hb
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ _ _
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%inc26" _ hi
  · simp only [runCells]
    rw [JsonScanLane.denoteCode_icmp_reg_w (x := BitVec.ofNat 64 i0 + 0x1#64)
      (y := BitVec.ofNat 64 n) _ _ _ "%cmp39572" "%i.1558" "%n" .ult 64
      (lookupName_cons_self ..) (by block_lk) _]
    simp only [denoteCode, denoteRun, State.bindAll, stateAt, whileEndEnv]

theorem whileEnd_step {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {b0 : UInt8} {n : Nat}
    (hpc : s.pc = "while.end")
    (hpre : s.pre = some "if.then22")
    (hb : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64
      (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)))
    (hi : lookupName env "%inc26" = some (.int 64 (BitVec.ofNat 64 i0 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbit : evalICmp .ult (BitVec.ofNat 64 i0 + 0x1#64) (BitVec.ofNat 64 n) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (whileEndEnv env i0 b0 n)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) := by
  refine numFast_step_at (s' := stateAt (whileEndEnv env i0 b0 n) s)
    (b := ⟨"while.end",
      [Instr.phi "%ip.0562" (Ty.int 64)
         [("cleanup.thread", (Operand.reg "%ip.0565.lcssa")),
          ("if.then22", (Operand.reg "%conv25")),
          ("cleanup", (Operand.reg "%add35"))],
       Instr.phi "%idig.0560" (Ty.int 64)
         [("cleanup.thread", (Operand.reg "%idig.0566.lcssa")),
          ("if.then22", (Operand.imm (Const.int 64 0x0000000000000001#64))),
          ("cleanup", (Operand.reg "%add29569933"))],
       Instr.phi "%i.1558" (Ty.int 64)
         [("cleanup.thread", (Operand.reg "%i.1567.lcssa")),
          ("if.then22", (Operand.reg "%inc26")),
          ("cleanup", (Operand.reg "%add568934"))],
       Instr.icmp "%cmp39572" (IPred.ult) 64 (Operand.reg "%i.1558")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_end
  · simpa only [denoteCode_nil] using whileEnd_denote (calls := calls) hpre hb hi hn
  · have hlk : lookupName (whileEndEnv env i0 b0 n) "%cmp39572"
        = some (.int 1
          (evalICmp .ult (BitVec.ofNat 64 i0 + 0x1#64) (BitVec.ofNat 64 n))) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp39572" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The run's preheader

`land.lhs.true41.preheader` computes `%idig.0560 + %n` and `%i.1558` from it —
the two words `BoundLoop`'s `N` is read from — and jumps to the head.  The
values are kept as the block's own words, because the invariant reads the head's
`phi` sources, not the preheader's arithmetic. -/

def intPreheaderEnv (env : Env) (nv iv dv : BitVec 64) : Env :=
  ("%7", .int 64 ((dv + nv) - iv)) ::
  ("%6", .int 64 (dv + nv)) :: env

theorem intPreheader_denote {calls : Calls} {env : Env} {s : State}
    {nv iv dv : BitVec 64}
    (hd : lookupName env "%idig.0560" = some (.int 64 dv))
    (hi : lookupName env "%i.1558" = some (.int 64 iv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.binop "%6" (BinOp.add) 64 (Operand.reg "%idig.0560") (Operand.reg "%n"),
         Instr.binop "%7" (BinOp.sub) 64 (Operand.reg "%6") (Operand.reg "%i.1558")]
        (stateAt env s) =
      some (stateAt (intPreheaderEnv env nv iv dv) s) := by
  rw [denoteCode_add_reg _ _ _ "%6" "%idig.0560" "%n" hd hn _]
  rw [denoteCode_sub_reg _ _ _ "%7" "%6" "%i.1558" (lookupName_cons_self ..) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, intPreheaderEnv]

theorem intPreheader_step {calls : Calls} {env : Env} {s : State}
    {nv iv dv : BitVec 64}
    (hpc : s.pc = "land.lhs.true41.preheader")
    (hd : lookupName env "%idig.0560" = some (.int 64 dv))
    (hi : lookupName env "%i.1558" = some (.int 64 iv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intPreheaderEnv env nv iv dv)
        { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }) := by
  refine numFast_step_at (s' := stateAt (intPreheaderEnv env nv iv dv) s)
    (b := ⟨"land.lhs.true41.preheader",
      [Instr.binop "%6" (BinOp.add) 64 (Operand.reg "%idig.0560") (Operand.reg "%n"),
       Instr.binop "%7" (BinOp.sub) 64 (Operand.reg "%6") (Operand.reg "%i.1558")],
      Term.br "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true41_preheader
  · simpa only [denoteCode_nil] using intPreheader_denote (calls := calls) hd hi hn
  · simp only [execTerm, stateAt, hpc]

/-- **The invariant at the head's entry edge.**  A head state the preheader
reached, with the carried counters the dispatch fixed, is `intRunInv` at its
first iteration: the budget is the whole distance to the lexeme's end and the
counter is zero.  The preheader's `%7` is the carried fact the end-of-lexeme exit
reads. -/
theorem intRunInv_entry {mem : Mem} {p n i0 d0 : Nat} {bs : List UInt8} {s : State}
    (hpc : s.pc = "land.lhs.true41")
    (hpre : s.pre = some "land.lhs.true41.preheader")
    (hmem : s.mem = mem) (hltn : i0 < n) (hnlt : n < 2 ^ 63) (hd0 : d0 ≤ i0)
    (hp : lookupName s.env "%p" = some (.ptr p))
    (hn : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes mem p n = some bs)
    (h7 : lookupName s.env "%7"
      = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)))
    (hi : lookupName s.env "%i.1558" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hid : lookupName s.env "%idig.0560" = some (.int 64 (BitVec.ofNat 64 d0)))
    (hip : lookupName s.env "%ip.0562"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19))))) :
    intRunInv mem p n i0 d0 bs (n - i0) s 0 := by
  refine ⟨hpc, hmem, by omega, by omega, hnlt, hd0, hp, hn, hread, h7,
    Or.inl ⟨hpre, ?_, ?_, ?_⟩⟩
  · simpa using hi
  · simpa using hid
  · simpa only [Nat.add_zero] using hip

/-! ### The dispatch's environment, and the ties between the block builders

`intStartEnv` is the environment the seven dispatch steps leave: the preheader's
two cells over the head's three `phi` sources over the truncation's cells over
the sign's.  The `lookupName` facts below are the same environment's readings,
peeled once each. -/

def intStartEnv (env : Env) (b b0 : UInt8) (a n : Nat) : Env :=
  intPreheaderEnv
    (whileEndEnv
      (ifThen22Env
        (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0) b0)
        (negIndex b) b0 n)
      (negIndex b) b0 n)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 (negIndex b) + 0x1#64) (0x1#64)

/-- A 64-bit word plus a small constant, read as a `Nat`. -/
theorem toNat_add_const {j k : Nat} (hk : j + k < 2 ^ 64) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 k).toNat = j + k := by
  rw [ofNat64_add_const hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- Every `lookupName` the dispatch's composition reads: peel the builders'
cells and take the base environment's fact.  The values are the builders' own,
so the only facts needed are the ones each step's hypotheses already name. -/
macro "lk_all" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only
       [signEnv, ifEndEnv, ifEndPhiEnv, ifEnd6Env, ifElseEnv, ifThen22Env, whileEndEnv,
        intPreheaderEnv, intStartEnv]
      block_lk)))

/-- **The integer run's start.**  From `land.lhs.true` — the sign check — with
the lexeme's bytes readable, the first byte the sign's own, the `int` part's
lead a `'1' … '9'`, the length past it and the eight-digit fast path's guard
refused, the seven dispatch steps reach `land.lhs.true41` with the run's
invariant at `i0 = negIndex b + 1` and `d0 = 1`: the index after the lead and
the one digit counted. -/
theorem intRun_start {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {b b0 : UInt8}
    (hpc : s.pc = "land.lhs.true") (hpre : s.pre = some "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hltn : negIndex b < n) (hnext : negIndex b + 1 < n)
    (hfast : n < negIndex b + 9) (hnlt : n < 2 ^ 63) :
    ∃ e : State,
      intRunInv s.mem a n (negIndex b + 1) 1 bs (n - (negIndex b + 1)) e 0 ∧
      ∀ k, runFuel calls (7 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hng1 : negIndex b ≤ 1 := negIndex_le_one b
  have hng63 : negIndex b < 2 ^ 63 := by omega
  have hb_toNat : 49 ≤ b0.toNat ∧ b0.toNat ≤ 57 :=
    ⟨UInt8.le_iff_toNat_le.mp hlead.1, UInt8.le_iff_toNat_le.mp hlead.2⟩
  have hb_ne30 : b0 ≠ 0x30 := by
    intro h; rw [h] at hb_toNat; exact absurd hb_toNat.1 (by decide)
  have hcmp9 : evalICmp .eq (JsonScanLane.vByte b0) 0x30#8 = 0 := by
    rw [eq_zero_iff]
    intro hh; exact hb_ne30 (vByte_inj hh)
  have hor : evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8 = 1 := by
    rw [ult_iff_one, ult_leadDigit_lt]; exact hb_toNat
  have hcmp3 : evalICmp .ult (BitVec.ofNat 64 (negIndex b)) (BitVec.ofNat 64 n) = 1 := by
    rw [ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hltn
  have hguard : evalICmp .ugt (BitVec.ofNat 64 (negIndex b) + 0x9#64)
      (BitVec.ofNat 64 n) = 1 := by
    rw [ugt_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      toNat_add_const (by omega)]
    exact hfast
  have hend : evalICmp .ult (BitVec.ofNat 64 (negIndex b) + 0x1#64)
      (BitVec.ofNat 64 n) = 1 := by
    rw [ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      toNat_add_const (by omega)]
    exact hnext
  have hb : lookupName (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
      a (negIndex b) b0) b0) (negIndex b) b0 n) "%conv25"
      = some (.int 64 (BitVec.ofNat 64
        (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) := by lk_all
  have hi6 : lookupName (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
      a (negIndex b) b0) b0) (negIndex b) b0 n) "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (negIndex b) + 0x1#64)) := by lk_all
  have h1s : step calls numFastBody (stateAt env s) =
      .jump (stateAt (signEnv env b)
        { s with pc := "if.end", pre := some "land.lhs.true" }) :=
    sign_step (calls := calls) hpc hp hsign
  have h2s : step calls numFastBody
      (stateAt (signEnv env b) { s with pc := "if.end", pre := some "land.lhs.true" }) =
      .jump (stateAt (ifEndEnv (signEnv env b) b n)
        { s with pc := "if.end6", pre := some "if.end" }) :=
    ifEnd_step (calls := calls) rfl rfl
      (signEnv_cmp1 env b) (signEnv_spec env b)
      (by lk_all) hcmp3
  have h3s : step calls numFastBody
      (stateAt (ifEndEnv (signEnv env b) b n)
        { s with pc := "if.end6", pre := some "if.end" }) =
      .jump (stateAt (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0)
        { s with pc := "if.else", pre := some "if.end6" }) :=
    ifEnd6_step (calls := calls) rfl (by lk_all) (by lk_all) hng63 hbyte hcmp9
  have h4s : step calls numFastBody
      (stateAt (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0)
        { s with pc := "if.else", pre := some "if.end6" }) =
      .jump (stateAt (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0) b0)
        { s with pc := "if.then22", pre := some "if.else" }) :=
    ifElse_step (calls := calls) rfl (by lk_all) hor
  have h5s : step calls numFastBody
      (stateAt (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0) b0)
        { s with pc := "if.then22", pre := some "if.else" }) =
      .jump (stateAt (ifThen22Env
          (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0) b0)
          (negIndex b) b0 n)
        { s with pc := "while.end", pre := some "if.then22" }) :=
    ifThen22_step (calls := calls) rfl (by lk_all) (by lk_all) (by lk_all) hguard
  have h6s : step calls numFastBody
      (stateAt (ifThen22Env
          (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n) a (negIndex b) b0) b0)
          (negIndex b) b0 n)
        { s with pc := "while.end", pre := some "if.then22" }) =
      .jump (stateAt (whileEndEnv
          (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
            a (negIndex b) b0) b0) (negIndex b) b0 n) (negIndex b) b0 n)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) :=
    whileEnd_step (calls := calls) rfl rfl hb hi6 (by lk_all) hend
  have hd6 : lookupName (whileEndEnv
      (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
        a (negIndex b) b0) b0) (negIndex b) b0 n) (negIndex b) b0 n) "%idig.0560"
      = some (.int 64 (BitVec.ofNat 64 1)) := by lk_all
  have hi6' : lookupName (whileEndEnv
      (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
        a (negIndex b) b0) b0) (negIndex b) b0 n) (negIndex b) b0 n) "%i.1558"
      = some (.int 64 (BitVec.ofNat 64 (negIndex b) + 0x1#64)) := by lk_all
  have h7s : step calls numFastBody
      (stateAt (whileEndEnv
          (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
            a (negIndex b) b0) b0) (negIndex b) b0 n) (negIndex b) b0 n)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) =
      .jump (stateAt (intPreheaderEnv (whileEndEnv
          (ifThen22Env (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv env b) b n)
            a (negIndex b) b0) b0) (negIndex b) b0 n) (negIndex b) b0 n)
          (BitVec.ofNat 64 n) (BitVec.ofNat 64 (negIndex b) + 0x1#64) (0x1#64))
        { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }) :=
    intPreheader_step (calls := calls) rfl hd6 hi6' (by lk_all)
  refine ⟨stateAt (intStartEnv env b b0 a n)
    { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }, ?_, ?_⟩
  · refine intRunInv_entry rfl rfl rfl (by omega) hnlt (by omega) ?_ ?_ hread
      ?_ ?_ ?_ ?_
    · lk_all
    · lk_all
    · have h1 : BitVec.ofNat 64 (negIndex b + 1)
          = BitVec.ofNat 64 (negIndex b) + 0x1#64 :=
        (ofNat64_add_one (by omega)).symm
      rw [h1]; lk_all
    · have h1 : BitVec.ofNat 64 (negIndex b + 1)
          = BitVec.ofNat 64 (negIndex b) + 0x1#64 :=
        (ofNat64_add_one (by omega)).symm
      rw [h1]; lk_all
    · lk_all
    · have hdig : IsDigitB b0 = true := by
        unfold IsDigitB
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true (UInt8.le_iff_toNat_le.mpr (by
            show (0x30 : UInt8).toNat ≤ b0.toNat
            rw [show (0x30 : UInt8).toNat = 48 from by decide]
            omega)),
          decide_eq_true (UInt8.le_iff_toNat_le.mpr (by
            show b0.toNat ≤ (0x39 : UInt8).toNat
            rw [show (0x39 : UInt8).toNat = 57 from by decide]
            omega))⟩
      have hblen : bs.length = n := JsonEntrySteps.readBytes_length s.mem a n hread
      have hget : bs.getD (negIndex b) 0 = b0 :=
        getD_of_readBytes hread hltn hbyte
      have hfold : digitFold bs (negIndex b) 1 = b0.toNat - 0x30 := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
          digitFold_succ (by omega),
          Nat.add_zero, digitFold_zero, Nat.zero_mul, Nat.zero_add, hget]
      have hconv : lookupName (intStartEnv env b b0 a n) "%ip.0562"
          = some (.int 64 (BitVec.ofNat 64
            (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) := by lk_all
      have hval : BitVec.ofNat 64 (JsonScanLane.vByte b0 &&& 0x0f#8).toNat
          = BitVec.ofNat 64 (digitFold bs (negIndex b + 1 - 1) (min 1 19)) := by
        rw [show negIndex b + 1 - 1 = negIndex b from by omega,
          show min 1 19 = 1 from by decide, hfold,
          digit_and_toNat hdig]
      rw [hval] at hconv
      exact hconv
  · intro k
    rw [show 7 + k = 1 + (1 + (1 + (1 + (1 + (1 + (1 + k)))))) from by omega,
      runFuel_jump_prefix h1s, runFuel_jump_prefix h2s, runFuel_jump_prefix h3s,
      runFuel_jump_prefix h4s, runFuel_jump_prefix h5s, runFuel_jump_prefix h6s,
      runFuel_jump_prefix h7s]
    rfl

/-! ### `if.then11`: the `0`-alone arm

The `int` part `0` alone: `%inc12` is the index after it, and the block jumps
straight to `if.end68` with `%ip.5 = 0`, `%idig.4 = 1` and `%i.5 = %inc12`.
There is no integer run. -/

def ifThen11Env (env : Env) (i0 : Nat) : Env :=
  ("%inc12", .int 64 (BitVec.ofNat 64 i0 + 0x1#64)) :: env

theorem ifThen11_denote {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0))) :
    denoteCode calls
        [Instr.binop "%inc12" (BinOp.add) 64 (Operand.reg "%i.0")
          (Operand.imm (Const.int 64 0x0000000000000001#64))]
        (stateAt env s) =
      some (stateAt (ifThen11Env env i0) s) := by
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%inc12" "%i.0" 64 hi _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifThen11Env]

theorem ifThen11_step {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    (hpc : s.pc = "if.then11")
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifThen11Env env i0)
        { s with pc := "if.end68", pre := some "if.then11" }) := by
  refine numFast_step_at (s' := stateAt (ifThen11Env env i0) s)
    (b := ⟨"if.then11",
      [Instr.binop "%inc12" (BinOp.add) 64 (Operand.reg "%i.0")
        (Operand.imm (Const.int 64 0x0000000000000001#64))],
      Term.br "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then11
  · simpa only [denoteCode_nil] using ifThen11_denote (calls := calls) hi
  · simp only [execTerm, stateAt, hpc]

/-! ### `if.end68`: the integer part's exit

The three `phi`s merge the zero arm's `(0, 1, inc12)`, the integer run's
`(ip.0562, idig.0560, i.1558)` and the head's own non-digit reach; `%cmp69` tests
the merged index against the length. -/

def ifEnd68PhiEnv (env : Env) (i5 ip5 idig5 : BitVec 64) : Env :=
  ("%i.5", .int 64 i5) :: ("%idig.4", .int 64 idig5) :: ("%ip.5", .int 64 ip5) :: env

def ifEnd68Env (env : Env) (i5 ip5 idig5 nv : BitVec 64) : Env :=
  ("%cmp69", .int 1 (evalICmp .ult i5 nv)) :: ifEnd68PhiEnv env i5 ip5 idig5

theorem ifEnd68_denote_zero {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {nv : BitVec 64}
    (hpre : s.pre = some "if.then11")
    (hi : lookupName env "%inc12"
      = some (.int 64 (BitVec.ofNat 64 i0 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd68Instrs (stateAt env s) =
      some (stateAt (ifEnd68Env env (BitVec.ofNat 64 i0 + 0x1#64) 0x0#64 0x1#64 nv) s) := by
  unfold numFastIfEnd68Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ _ _
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ _ _
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%inc12" _ hi
  · simp only [runCells]
    rw [JsonScanLane.denoteCode_icmp_reg_w (x := BitVec.ofNat 64 i0 + 0x1#64) (y := nv)
      _ _ _ "%cmp69" "%i.5" "%n" .ult 64 (lookupName_cons_self ..) (by block_lk) _]
    simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifEnd68Env, ifEnd68PhiEnv]

theorem ifEnd68_denote_loop {calls : Calls} {env : Env} {s : State}
    {ip5 idig5 i5 : BitVec 64} {nv : BitVec 64}
    (hpre : s.pre = some "while.end")
    (hp5 : lookupName env "%ip.0562" = some (.int 64 ip5))
    (hd5 : lookupName env "%idig.0560" = some (.int 64 idig5))
    (hi5 : lookupName env "%i.1558" = some (.int 64 i5))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd68Instrs (stateAt env s) =
      some (stateAt (ifEnd68Env env i5 ip5 idig5 nv) s) := by
  unfold numFastIfEnd68Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%ip.0562" _ hp5
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%idig.0560" _ hd5
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%i.1558" _ hi5
  · simp only [runCells]
    rw [JsonScanLane.denoteCode_icmp_reg_w (x := i5) (y := nv)
      _ _ _ "%cmp69" "%i.5" "%n" .ult 64 (lookupName_cons_self ..) (by block_lk) _]
    simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifEnd68Env, ifEnd68PhiEnv]

theorem ifEnd68_step {calls : Calls} {env : Env} {s : State}
    {i5 ip5 idig5 nv : BitVec 64}
    (hpc : s.pc = "if.end68")
    (hden : denoteCode calls numFastIfEnd68Instrs (stateAt env s) =
      some (stateAt (ifEnd68Env env i5 ip5 idig5 nv) s))
    (hbit : evalICmp .ult i5 nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd68Env env i5 ip5 idig5 nv)
        { s with pc := "land.lhs.true71", pre := some "if.end68" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd68Env env i5 ip5 idig5 nv) s)
    (b := ⟨"if.end68", numFastIfEnd68Instrs,
      Term.condbr (Operand.reg "%cmp69") "land.lhs.true71" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd68Instrs] using numFast_findBlock_if_end68
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd68Env env i5 ip5 idig5 nv) "%cmp69"
        = some (.int 1 (evalICmp .ult i5 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp69" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem ifEnd68_step_nondigit {calls : Calls} {env : Env} {s : State}
    {i5 ip5 idig5 nv : BitVec 64}
    (hpc : s.pc = "if.end68")
    (hden : denoteCode calls numFastIfEnd68Instrs (stateAt env s) =
      some (stateAt (ifEnd68Env env i5 ip5 idig5 nv) s))
    (hbit : evalICmp .ult i5 nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd68Env env i5 ip5 idig5 nv)
        { s with pc := "if.end144", pre := some "if.end68" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd68Env env i5 ip5 idig5 nv) s)
    (b := ⟨"if.end68", numFastIfEnd68Instrs,
      Term.condbr (Operand.reg "%cmp69") "land.lhs.true71" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd68Instrs] using numFast_findBlock_if_end68
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd68Env env i5 ip5 idig5 nv) "%cmp69"
        = some (.int 1 (evalICmp .ult i5 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp69" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `land.lhs.true71`: the `.` test

The byte after the `int` part, tested against `'.'`. -/

def landLhsTrue71Env (env : Env) (a i5 : Nat) (bd : UInt8) : Env :=
  ("%cmp74", .int 1 (evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8)) ::
  ("%11", .int 8 (JsonScanLane.vByte bd)) ::
  ("%arrayidx72", .ptr (a + i5)) :: env

theorem landLhsTrue71_denote {calls : Calls} {env : Env} {s : State}
    {a i5 : Nat} {bd : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hj : i5 < 2 ^ 63)
    (hread : readByte s.mem (a + i5) = some bd) :
    denoteCode calls
        [Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5"),
         Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx72"),
         Instr.icmp "%cmp74" (IPred.eq) 8 (Operand.reg "%11")
           (Operand.imm (Const.int 8 0x2e#8))]
        (stateAt env s) =
      some (stateAt (landLhsTrue71Env env a i5 bd) s) := by
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx72" "%p" "%i.5" hp hi
    (by rw [sExt_ofNat64 hj]; exact hj) _]
  rw [sExt_ofNat64 hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%11" "%arrayidx72" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp74" "%11" .eq
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, landLhsTrue71Env]

theorem landLhsTrue71_step {calls : Calls} {env : Env} {s : State}
    {a i5 : Nat} {bd : UInt8}
    (hpc : s.pc = "land.lhs.true71")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hj : i5 < 2 ^ 63)
    (hread : readByte s.mem (a + i5) = some bd)
    (hbit : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (landLhsTrue71Env env a i5 bd)
        { s with pc := "if.then76", pre := some "land.lhs.true71" }) := by
  refine numFast_step_at (s' := stateAt (landLhsTrue71Env env a i5 bd) s)
    (b := ⟨"land.lhs.true71",
      [Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5"),
       Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx72"),
       Instr.icmp "%cmp74" (IPred.eq) 8 (Operand.reg "%11")
         (Operand.imm (Const.int 8 0x2e#8))],
      Term.condbr (Operand.reg "%cmp74") "if.then76" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true71
  · simpa only [denoteCode_nil] using landLhsTrue71_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (landLhsTrue71Env env a i5 bd) "%cmp74"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp74" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem landLhsTrue71_step_nodot {calls : Calls} {env : Env} {s : State}
    {a i5 : Nat} {bd : UInt8}
    (hpc : s.pc = "land.lhs.true71")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hj : i5 < 2 ^ 63)
    (hread : readByte s.mem (a + i5) = some bd)
    (hbit : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (landLhsTrue71Env env a i5 bd)
        { s with pc := "if.end144", pre := some "land.lhs.true71" }) := by
  refine numFast_step_at (s' := stateAt (landLhsTrue71Env env a i5 bd) s)
    (b := ⟨"land.lhs.true71",
      [Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5"),
       Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx72"),
       Instr.icmp "%cmp74" (IPred.eq) 8 (Operand.reg "%11")
         (Operand.imm (Const.int 8 0x2e#8))],
      Term.condbr (Operand.reg "%cmp74") "if.then76" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true71
  · simpa only [denoteCode_nil] using landLhsTrue71_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (landLhsTrue71Env env a i5 bd) "%cmp74"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp74" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.then76`: the index after the `.`

`%inc77 = %i.5 + 1` and `%cmp78.not = %inc77 <u %n`: the fraction needs a byte
after the `.`. -/

def ifThen76Env (env : Env) (i5 : Nat) (nv : BitVec 64) : Env :=
  ("%cmp78.not", .int 1 (evalICmp .ult (BitVec.ofNat 64 i5 + 0x1#64) nv)) ::
  ("%inc77", .int 64 (BitVec.ofNat 64 i5 + 0x1#64)) :: env

theorem ifThen76_denote {calls : Calls} {env : Env} {s : State} {i5 : Nat}
    {nv : BitVec 64}
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%i.5")
          (Operand.imm (Const.int 64 0x0000000000000001#64)),
         Instr.icmp "%cmp78.not" (IPred.ult) 64 (Operand.reg "%inc77") (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (ifThen76Env env i5 nv) s) := by
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%inc77" "%i.5" 64 hi _]
  rw [JsonScanLane.denoteCode_icmp_reg_w (x := BitVec.ofNat 64 i5 + 0x1#64) (y := nv)
    _ _ _ "%cmp78.not" "%inc77" "%n" .ult 64 (lookupName_cons_self ..) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, ifThen76Env]

theorem ifThen76_step {calls : Calls} {env : Env} {s : State} {i5 : Nat}
    {nv : BitVec 64}
    (hpc : s.pc = "if.then76")
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult (BitVec.ofNat 64 i5 + 0x1#64) nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifThen76Env env i5 nv)
        { s with pc := "lor.lhs.false", pre := some "if.then76" }) := by
  refine numFast_step_at (s' := stateAt (ifThen76Env env i5 nv) s)
    (b := ⟨"if.then76",
      [Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%i.5")
        (Operand.imm (Const.int 64 0x0000000000000001#64)),
       Instr.icmp "%cmp78.not" (IPred.ult) 64 (Operand.reg "%inc77") (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp78.not") "lor.lhs.false" "if.then89"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then76
  · simpa only [denoteCode_nil] using ifThen76_denote (calls := calls) hi hn
  · have hlk : lookupName (ifThen76Env env i5 nv) "%cmp78.not"
        = some (.int 1 (evalICmp .ult (BitVec.ofNat 64 i5 + 0x1#64) nv)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp78.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `lor.lhs.false`: the fraction must start with a digit

The byte at `%inc77`, tested against the digit window: `%or.cond441` is one
exactly off it, and the block then takes `if.then89`, the refusal that stores
`%inc77`.  A digit goes on to `while.cond91.preheader`. -/

def lorLhsFalseEnv (env : Env) (a inc77 : Nat) (bd : UInt8) : Env :=
  ("%or.cond441", .int 1 (evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8)) ::
  ("%13", .int 8 (JsonScanLane.vByte bd + 0xc6#8)) ::
  ("%12", .int 8 (JsonScanLane.vByte bd)) ::
  ("%arrayidx80", .ptr (a + inc77)) :: env

theorem lorLhsFalse_denote {calls : Calls} {env : Env} {s : State}
    {a inc77 : Nat} {bd : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 inc77)))
    (hj : inc77 < 2 ^ 63)
    (hread : readByte s.mem (a + inc77) = some bd) :
    denoteCode calls
        [Instr.gep "%arrayidx80" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
         Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx80"),
         Instr.binop "%13" (BinOp.add) 8 (Operand.reg "%12") (Operand.imm (Const.int 8 0xc6#8)),
         Instr.icmp "%or.cond441" (IPred.ult) 8 (Operand.reg "%13")
           (Operand.imm (Const.int 8 0xf6#8))]
        (stateAt env s) =
      some (stateAt (lorLhsFalseEnv env a inc77 bd) s) := by
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx80" "%p" "%inc77" hp hi
    (by rw [sExt_ofNat64 hj]; exact hj) _]
  rw [sExt_ofNat64 hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%12" "%arrayidx80" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%13" "%12" 8 (lookupName_cons_self ..) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond441" "%13" .ult
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, lorLhsFalseEnv]

theorem lorLhsFalse_step_digit {calls : Calls} {env : Env} {s : State}
    {a inc77 : Nat} {bd : UInt8}
    (hpc : s.pc = "lor.lhs.false")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 inc77)))
    (hj : inc77 < 2 ^ 63)
    (hread : readByte s.mem (a + inc77) = some bd)
    (hbit : evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lorLhsFalseEnv env a inc77 bd)
        { s with pc := "while.cond91.preheader", pre := some "lor.lhs.false" }) := by
  refine numFast_step_at (s' := stateAt (lorLhsFalseEnv env a inc77 bd) s)
    (b := ⟨"lor.lhs.false",
      [Instr.gep "%arrayidx80" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
       Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx80"),
       Instr.binop "%13" (BinOp.add) 8 (Operand.reg "%12") (Operand.imm (Const.int 8 0xc6#8)),
       Instr.icmp "%or.cond441" (IPred.ult) 8 (Operand.reg "%13")
         (Operand.imm (Const.int 8 0xf6#8))],
      Term.condbr (Operand.reg "%or.cond441") "if.then89" "while.cond91.preheader"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_lor_lhs_false
  · simpa only [denoteCode_nil] using lorLhsFalse_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (lorLhsFalseEnv env a inc77 bd) "%or.cond441"
        = some (.int 1 (evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%or.cond441" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `while.cond91.preheader`: the fraction's fast path's guard

`%add92582 = %i.5 + 9` and `%cmp93583.not = %add92582 > %n`: refused takes
`while.end115` with `fr = fdig = 0` and the index at `%inc77`. -/

def whileCond91PreheaderEnv (env : Env) (i5 : Nat) (nv : BitVec 64) : Env :=
  ("%cmp93583.not", .int 1
      (evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) nv)) ::
  ("%add92582", .int 64 (BitVec.ofNat 64 i5 + 0x9#64)) :: env

theorem whileCond91Preheader_denote {calls : Calls} {env : Env} {s : State}
    {i5 : Nat} {nv : BitVec 64}
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.binop "%add92582" (BinOp.add) 64 (Operand.reg "%i.5")
          (Operand.imm (Const.int 64 0x0000000000000009#64)),
         Instr.icmp "%cmp93583.not" (IPred.ugt) 64 (Operand.reg "%add92582")
           (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (whileCond91PreheaderEnv env i5 nv) s) := by
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%add92582" "%i.5" 64 hi _]
  rw [JsonScanLane.denoteCode_icmp_reg_w (x := BitVec.ofNat 64 i5 + 0x9#64) (y := nv)
    _ _ _ "%cmp93583.not" "%add92582" "%n" .ugt 64 (lookupName_cons_self ..) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, whileCond91PreheaderEnv]

theorem whileCond91Preheader_step {calls : Calls} {env : Env} {s : State}
    {i5 : Nat} {nv : BitVec 64}
    (hpc : s.pc = "while.cond91.preheader")
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (whileCond91PreheaderEnv env i5 nv)
        { s with pc := "while.end115", pre := some "while.cond91.preheader" }) := by
  refine numFast_step_at (s' := stateAt (whileCond91PreheaderEnv env i5 nv) s)
    (b := ⟨"while.cond91.preheader",
      [Instr.binop "%add92582" (BinOp.add) 64 (Operand.reg "%i.5")
        (Operand.imm (Const.int 64 0x0000000000000009#64)),
       Instr.icmp "%cmp93583.not" (IPred.ugt) 64 (Operand.reg "%add92582")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp93583.not") "while.end115" "while.body100.preheader"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_cond91_preheader
  · simpa only [denoteCode_nil] using whileCond91Preheader_denote (calls := calls) hi hn
  · have hlk : lookupName (whileCond91PreheaderEnv env i5 nv) "%cmp93583.not"
        = some (.int 1 (evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) nv)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp93583.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `while.end115`: the fraction run's start

The `phi` run's `while.cond91.preheader` edge takes `0` into `%fr.0556` and
`%fdig.0554` and `%inc77` into `%i.6552`; `%cmp117592` tests the index against
the length. -/

def whileEnd115Env (env : Env) (inc77 nv : BitVec 64) : Env :=
  ("%cmp117592", .int 1 (evalICmp .ult inc77 nv)) ::
  ("%i.6552", .int 64 inc77) ::
  ("%fdig.0554", .int 64 (0x0#64)) ::
  ("%fr.0556", .int 64 (0x0#64)) :: env

theorem whileEnd115_denote {calls : Calls} {env : Env} {s : State}
    {inc77 nv : BitVec 64}
    (hpre : s.pre = some "while.cond91.preheader")
    (hi : lookupName env "%inc77" = some (.int 64 inc77))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.phi "%fr.0556" (Ty.int 64)
           [("cleanup112.thread", (Operand.reg "%fr.0584.lcssa")),
            ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
            ("cleanup112", (Operand.reg "%add109"))],
         Instr.phi "%fdig.0554" (Ty.int 64)
           [("cleanup112.thread", (Operand.reg "%fdig.0585.lcssa")),
            ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
            ("cleanup112", (Operand.reg "%add96588941"))],
         Instr.phi "%i.6552" (Ty.int 64)
           [("cleanup112.thread", (Operand.reg "%i.6586.lcssa")),
            ("while.cond91.preheader", (Operand.reg "%inc77")),
            ("cleanup112", (Operand.reg "%add92587942"))],
         Instr.icmp "%cmp117592" (IPred.ult) 64 (Operand.reg "%i.6552")
           (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (whileEnd115Env env inc77 nv) s) := by
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ _ _
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ _ _
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_reg_of env s "%inc77" _ hi
  · simp only [runCells]
    rw [JsonScanLane.denoteCode_icmp_reg_w (x := inc77) (y := nv)
      _ _ _ "%cmp117592" "%i.6552" "%n" .ult 64 (lookupName_cons_self ..) (by block_lk) _]
    simp only [denoteCode, denoteRun, State.bindAll, stateAt, whileEnd115Env]

theorem whileEnd115_step {calls : Calls} {env : Env} {s : State}
    {inc77 nv : BitVec 64}
    (hpc : s.pc = "while.end115")
    (hpre : s.pre = some "while.cond91.preheader")
    (hi : lookupName env "%inc77" = some (.int 64 inc77))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult inc77 nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (whileEnd115Env env inc77 nv)
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) := by
  refine numFast_step_at (s' := stateAt (whileEnd115Env env inc77 nv) s)
    (b := ⟨"while.end115",
      [Instr.phi "%fr.0556" (Ty.int 64)
         [("cleanup112.thread", (Operand.reg "%fr.0584.lcssa")),
          ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
          ("cleanup112", (Operand.reg "%add109"))],
       Instr.phi "%fdig.0554" (Ty.int 64)
         [("cleanup112.thread", (Operand.reg "%fdig.0585.lcssa")),
          ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
          ("cleanup112", (Operand.reg "%add96588941"))],
       Instr.phi "%i.6552" (Ty.int 64)
         [("cleanup112.thread", (Operand.reg "%i.6586.lcssa")),
          ("while.cond91.preheader", (Operand.reg "%inc77")),
          ("cleanup112", (Operand.reg "%add92587942"))],
       Instr.icmp "%cmp117592" (IPred.ult) 64 (Operand.reg "%i.6552")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_end115
  · simpa only [denoteCode_nil] using whileEnd115_denote (calls := calls) hpre hi hn
  · have hlk : lookupName (whileEnd115Env env inc77 nv) "%cmp117592"
        = some (.int 1 (evalICmp .ult inc77 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp117592" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The fraction run's preheader and invariant -/

def fracPreheaderEnv (env : Env) (nv iv dv : BitVec 64) : Env :=
  ("%17", .int 64 ((dv + nv) - iv)) ::
  ("%16", .int 64 (dv + nv)) :: env

theorem fracPreheader_denote {calls : Calls} {env : Env} {s : State}
    {nv iv dv : BitVec 64}
    (hd : lookupName env "%fdig.0554" = some (.int 64 dv))
    (hi : lookupName env "%i.6552" = some (.int 64 iv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.binop "%16" (BinOp.add) 64 (Operand.reg "%fdig.0554") (Operand.reg "%n"),
         Instr.binop "%17" (BinOp.sub) 64 (Operand.reg "%16") (Operand.reg "%i.6552")]
        (stateAt env s) =
      some (stateAt (fracPreheaderEnv env nv iv dv) s) := by
  rw [denoteCode_add_reg _ _ _ "%16" "%fdig.0554" "%n" hd hn _]
  rw [denoteCode_sub_reg _ _ _ "%17" "%16" "%i.6552" (lookupName_cons_self ..) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fracPreheaderEnv]

theorem fracPreheader_step {calls : Calls} {env : Env} {s : State}
    {nv iv dv : BitVec 64}
    (hpc : s.pc = "land.lhs.true119.preheader")
    (hd : lookupName env "%fdig.0554" = some (.int 64 dv))
    (hi : lookupName env "%i.6552" = some (.int 64 iv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracPreheaderEnv env nv iv dv)
        { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }) := by
  refine numFast_step_at (s' := stateAt (fracPreheaderEnv env nv iv dv) s)
    (b := ⟨"land.lhs.true119.preheader",
      [Instr.binop "%16" (BinOp.add) 64 (Operand.reg "%fdig.0554") (Operand.reg "%n"),
       Instr.binop "%17" (BinOp.sub) 64 (Operand.reg "%16") (Operand.reg "%i.6552")],
      Term.br "land.lhs.true119"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true119_preheader
  · simpa only [denoteCode_nil] using fracPreheader_denote (calls := calls) hd hi hn
  · simp only [execTerm, stateAt, hpc]

theorem fracRunInv_entry {mem : Mem} {p n i0 d0 : Nat} {bs : List UInt8} {s : State}
    (hpc : s.pc = "land.lhs.true119")
    (hpre : s.pre = some "land.lhs.true119.preheader")
    (hmem : s.mem = mem) (hltn : i0 < n) (hnlt : n < 2 ^ 63) (hd0 : d0 ≤ i0)
    (hp : lookupName s.env "%p" = some (.ptr p))
    (hn : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes mem p n = some bs)
    (h17 : lookupName s.env "%17"
      = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)))
    (hparts : fracPartCells s.env)
    (hi : lookupName s.env "%i.6552" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hid : lookupName s.env "%fdig.0554" = some (.int 64 (BitVec.ofNat 64 d0)))
    (hf : lookupName s.env "%fr.0556"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19))))) :
    fracRunInv mem p n i0 d0 bs (n - i0) s 0 := by
  refine ⟨hpc, hmem, by omega, by omega, hnlt, hd0, hp, hn, hread, h17, hparts,
    Or.inl ⟨hpre, ?_, ?_, ?_⟩⟩
  · simpa using hi
  · simpa using hid
  · simpa only [Nat.add_zero] using hf

/-- Every `lookupName` the fraction dispatch's composition reads.  The
fraction builders are declared above the integer composition's tactic, so this
one lists them. -/
macro "lk_frac" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only
       [stateAt, signEnv, ifEndEnv, ifEndPhiEnv, ifEnd6Env, ifElseEnv, ifThen22Env, whileEndEnv,
        intPreheaderEnv, intStartEnv, ifThen11Env, ifEnd68Env, ifEnd68PhiEnv,
        landLhsTrue71Env, ifThen76Env, lorLhsFalseEnv, whileCond91PreheaderEnv,
        whileEnd115Env, fracPreheaderEnv]
      block_lk)))

/-- **The fraction run's start.**  From `land.lhs.true71` — the `.` test, taken
— with the byte after the `.` a digit, the length past it and the eight-digit
fast path's guard refused, the six dispatch steps reach `land.lhs.true119` with
the run's invariant at `i0 = i5 + 1` and `d0 = 0`: the index after the `.`, no
fraction digits counted yet. -/
theorem fracRun_start {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {i5 : Nat} {bd bd2 : UInt8}
    (hpc : s.pc = "land.lhs.true71")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hparts : fracPartCells env)
    (hdot : readByte s.mem (a + i5) = some bd) (hdoteq : bd = 0x2E)
    (hd2 : readByte s.mem (a + (i5 + 1)) = some bd2)
    (hd2digit : IsDigitB bd2 = true)
    (hltn : i5 + 1 < n) (hfast : n < i5 + 9) (hnlt : n < 2 ^ 63) :
    ∃ e : State,
      fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
      ∀ k, runFuel calls (6 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hi63 : i5 < 2 ^ 63 := by omega
  have hbit : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 1 := by
    rw [eq_iff_one, hdoteq]; rfl
  have hinc64 : evalICmp .ult (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n) = 1 := by
    rw [ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      toNat_add_const (by omega)]
    exact hltn
  have hnd : evalICmp .ult (JsonScanLane.vByte bd2 + 0xc6#8) 0xf6#8 = 0 := by
    rw [ult_zero_iff]
    intro hh
    have hr : 48 ≤ bd2.toNat ∧ bd2.toNat ≤ 57 := (isDigitB_toNat_iff bd2).mp hd2digit
    have h2 : (JsonScanLane.vByte bd2 + 0xc6#8).toNat < (0xf6#8).toNat := by
      simpa using hh
    exact (ult_nondigit_lt bd2).mp h2 hr
  have hfastb : evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) (BitVec.ofNat 64 n) = 1 := by
    rw [ugt_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      toNat_add_const (by omega)]
    exact hfast
  have hdot' : readByte s.mem (a + i5) = some bd := hdot
  have hinc_lk : BitVec.ofNat 64 (i5 + 1) = BitVec.ofNat 64 i5 + 0x1#64 :=
    (ofNat64_add_one (by omega)).symm
  have hinc_d : lookupName (ifThen76Env (landLhsTrue71Env env a i5 bd) i5
      (BitVec.ofNat 64 n)) "%inc77"
      = some (.int 64 (BitVec.ofNat 64 (i5 + 1))) := by
    rw [hinc_lk]; lk_frac
  have h1s : step calls numFastBody (stateAt env s) =
      .jump (stateAt (landLhsTrue71Env env a i5 bd)
        { s with pc := "if.then76", pre := some "land.lhs.true71" }) :=
    landLhsTrue71_step (calls := calls) hpc hp hi5 hi63 hdot' hbit
  have h2s : step calls numFastBody
      (stateAt (landLhsTrue71Env env a i5 bd)
        { s with pc := "if.then76", pre := some "land.lhs.true71" }) =
      .jump (stateAt (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n))
        { s with pc := "lor.lhs.false", pre := some "if.then76" }) :=
    ifThen76_step (calls := calls) rfl (by lk_frac) (by lk_frac) hinc64
  have h3s : step calls numFastBody
      (stateAt (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n))
        { s with pc := "lor.lhs.false", pre := some "if.then76" }) =
      .jump (stateAt (lorLhsFalseEnv (ifThen76Env (landLhsTrue71Env env a i5 bd) i5
          (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
        { s with pc := "while.cond91.preheader", pre := some "lor.lhs.false" }) :=
    lorLhsFalse_step_digit (calls := calls) rfl (by lk_frac)
      hinc_d (by omega) hd2 hnd
  have h4s : step calls numFastBody
      (stateAt (lorLhsFalseEnv (ifThen76Env (landLhsTrue71Env env a i5 bd) i5
          (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
        { s with pc := "while.cond91.preheader", pre := some "lor.lhs.false" }) =
      .jump (stateAt (whileCond91PreheaderEnv (lorLhsFalseEnv (ifThen76Env
          (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
          i5 (BitVec.ofNat 64 n))
        { s with pc := "while.end115", pre := some "while.cond91.preheader" }) :=
    whileCond91Preheader_step (calls := calls) rfl (by lk_frac) (by lk_frac) hfastb
  have hinc' : lookupName (whileCond91PreheaderEnv (lorLhsFalseEnv (ifThen76Env
      (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
      i5 (BitVec.ofNat 64 n)) "%inc77"
      = some (.int 64 (BitVec.ofNat 64 i5 + 0x1#64)) := by lk_frac
  have h5s : step calls numFastBody
      (stateAt (whileCond91PreheaderEnv (lorLhsFalseEnv (ifThen76Env
          (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
          i5 (BitVec.ofNat 64 n))
        { s with pc := "while.end115", pre := some "while.cond91.preheader" }) =
      .jump (stateAt (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
          (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
          i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) :=
    whileEnd115_step (calls := calls) rfl rfl hinc' (by lk_frac) hinc64
  have hd6 : lookupName (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
      (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
      i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
      "%fdig.0554" = some (.int 64 (0x0#64)) := by lk_frac
  have hd6i : lookupName (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
      (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
      i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
      "%i.6552" = some (.int 64 (BitVec.ofNat 64 i5 + 0x1#64)) := by lk_frac
  have h6s : step calls numFastBody
      (stateAt (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
          (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
          i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) =
      .jump (stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
          (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
          i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
          (BitVec.ofNat 64 n) (BitVec.ofNat 64 i5 + 0x1#64) (0x0#64))
        { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }) :=
    fracPreheader_step (calls := calls) rfl hd6 hd6i (by lk_frac)
  exact ⟨stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv (lorLhsFalseEnv
      (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2)
      i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n))
      (BitVec.ofNat 64 n) (BitVec.ofNat 64 i5 + 0x1#64) (0x0#64))
    { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" },
    fracRunInv_entry rfl rfl rfl (by omega) hnlt (by omega) (by lk_frac) (by lk_frac)
      hread (by rw [hinc_lk]; lk_frac)
      (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
          exact ⟨idigv, ipv, by lk_frac, by lk_frac⟩)
      (by rw [hinc_lk]; lk_frac) (by lk_frac)
      (by
        rw [show min 0 19 = 0 from by decide, digitFold_zero]
        lk_frac),
    fun k => by
      rw [show 6 + k = 1 + (1 + (1 + (1 + (1 + (1 + k))))) from by omega,
        runFuel_jump_prefix h1s, runFuel_jump_prefix h2s, runFuel_jump_prefix h3s,
        runFuel_jump_prefix h4s, runFuel_jump_prefix h5s, runFuel_jump_prefix h6s]⟩

/-! ### `lor.lhs.false180`: the exponent must start with a digit

The byte at `%i.11` — the index the marker and its optional sign left — tested
against the digit window.  A digit goes on to `land.lhs.true195`, which is the
exponent run's head and takes `%i.11` and the accumulator's `0` as its `phi`
sources; off the window the block takes `cleanup223`, the refusal that stores
`%i.11`. -/

def lorLhsFalse180Env (env : Env) (a i11 : Nat) (bd : UInt8) : Env :=
  ("%or.cond444", .int 1 (evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8)) ::
  ("%24", .int 8 (JsonScanLane.vByte bd + 0xc6#8)) ::
  ("%23", .int 8 (JsonScanLane.vByte bd)) ::
  ("%arrayidx181", .ptr (a + i11)) :: env

theorem lorLhsFalse180_denote {calls : Calls} {env : Env} {s : State}
    {a i11 : Nat} {bd : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.11" = some (.int 64 (BitVec.ofNat 64 i11)))
    (hj : i11 < 2 ^ 63)
    (hread : readByte s.mem (a + i11) = some bd) :
    denoteCode calls
        [Instr.gep "%arrayidx181" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.11"),
         Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx181"),
         Instr.binop "%24" (BinOp.add) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0xc6#8)),
         Instr.icmp "%or.cond444" (IPred.ult) 8 (Operand.reg "%24")
           (Operand.imm (Const.int 8 0xf6#8))]
        (stateAt env s) =
      some (stateAt (lorLhsFalse180Env env a i11 bd) s) := by
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx181" "%p" "%i.11" hp hi
    (by rw [sExt_ofNat64 hj]; exact hj) _]
  rw [sExt_ofNat64 hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%23" "%arrayidx181" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%24" "%23" 8 (lookupName_cons_self ..) _]
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond444" "%24" .ult
    (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, lorLhsFalse180Env]

theorem lorLhsFalse180_step_digit {calls : Calls} {env : Env} {s : State}
    {a i11 : Nat} {bd : UInt8}
    (hpc : s.pc = "lor.lhs.false180")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.11" = some (.int 64 (BitVec.ofNat 64 i11)))
    (hj : i11 < 2 ^ 63)
    (hread : readByte s.mem (a + i11) = some bd)
    (hbit : evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lorLhsFalse180Env env a i11 bd)
        { s with pc := "land.lhs.true195", pre := some "lor.lhs.false180" }) := by
  refine numFast_step_at (s' := stateAt (lorLhsFalse180Env env a i11 bd) s)
    (b := ⟨"lor.lhs.false180",
      [Instr.gep "%arrayidx181" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.11"),
       Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx181"),
       Instr.binop "%24" (BinOp.add) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0xc6#8)),
       Instr.icmp "%or.cond444" (IPred.ult) 8 (Operand.reg "%24")
         (Operand.imm (Const.int 8 0xf6#8))],
      Term.condbr (Operand.reg "%or.cond444") "cleanup223" "land.lhs.true195"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_lor_lhs_false180
  · simpa only [denoteCode_nil] using lorLhsFalse180_denote (calls := calls) hp hi hj hread
  · have hlk : lookupName (lorLhsFalse180Env env a i11 bd) "%or.cond444"
        = some (.int 1 (evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%or.cond444" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem expRunInv_entry {mem : Mem} {p n i0 : Nat} {bs : List UInt8} {s : State}
    (hpc : s.pc = "land.lhs.true195")
    (hpre : s.pre = some "lor.lhs.false180")
    (hmem : s.mem = mem) (hltn : i0 < n) (hnlt : n < 2 ^ 63)
    (hp : lookupName s.env "%p" = some (.ptr p))
    (hn : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes mem p n = some bs)
    (hi : lookupName s.env "%i.11" = some (.int 64 (BitVec.ofNat 64 i0))) :
    expRunInv mem p n i0 bs (n - i0) s 0 :=
  ⟨hpc, hmem, by omega, by omega, hnlt, hp, hn, hread, Or.inl ⟨hpre, by simpa using hi⟩⟩

macro "lk_exp" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only
       [stateAt, lorLhsFalse180Env]
      block_lk)))

/-- **The exponent run's start.**  From `lor.lhs.false180` — the marker and its
optional sign already consumed, so `%i.11` is the index of the exponent's first
digit — with that byte a digit, one dispatch step reaches `land.lhs.true195` with
the run's invariant at `i0 = i11` and an empty accumulator.  The index `%i.11`
is the block's carried register: this theorem fixes the run's start *at* it,
and the paragraph below names the nest that fixes it from the `e`/`E` and its
sign. -/
theorem expRun_start {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {i11 : Nat} {bd : UInt8}
    (hpc : s.pc = "lor.lhs.false180")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hi11 : lookupName env "%i.11" = some (.int 64 (BitVec.ofNat 64 i11)))
    (hd : readByte s.mem (a + i11) = some bd)
    (hdigit : IsDigitB bd = true)
    (hltn : i11 < n) (hnlt : n < 2 ^ 63) :
    ∃ e : State,
      expRunInv s.mem a n i11 bs (n - i11) e 0 ∧
      ∀ k, runFuel calls (1 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hi63 : i11 < 2 ^ 63 := by omega
  have hbit : evalICmp .ult (JsonScanLane.vByte bd + 0xc6#8) 0xf6#8 = 0 := by
    rw [ult_zero_iff]
    intro h2
    have hr : 48 ≤ bd.toNat ∧ bd.toNat ≤ 57 := (isDigitB_toNat_iff bd).mp hdigit
    exact (ult_nondigit_lt bd).mp h2 hr
  have h1s : step calls numFastBody (stateAt env s) =
      .jump (stateAt (lorLhsFalse180Env env a i11 bd)
        { s with pc := "land.lhs.true195", pre := some "lor.lhs.false180" }) :=
    lorLhsFalse180_step_digit (calls := calls) hpc hp hi11 hi63 hd hbit
  exact ⟨stateAt (lorLhsFalse180Env env a i11 bd)
      { s with pc := "land.lhs.true195", pre := some "lor.lhs.false180" },
    expRunInv_entry rfl rfl rfl (by omega) hnlt (by lk_exp) (by lk_exp) hread (by lk_exp),
    fun k => by
      rw [runFuel_jump_prefix h1s k]⟩

/-! ### Where the exponent's index comes from

The register `expRun_start` takes — `%i.11` — is written by the marker nest
between `if.end144` and `lor.lhs.false180`, which is not in this module:

* `land.lhs.true147` loads the byte at `%i.10` and `NodeBlock` pivots on it with
  a *signed* compare against `0x65`, so `LeafBlock` tests `0x45` and
  `LeafBlock1` tests `0x65`; either leaf's equality takes `if.then157` and
  anything else `if.end226` (no exponent at all);
* `if.then157` forms `%inc158 = %i.10 + 1` and tests it against the length, and
  `land.lhs.true161`/`NodeBlock7`/`LeafBlock5`/`LeafBlock3` read the optional
  sign byte at `%inc158` against `0x2d` and `0x2b`;
* `if.then171` sets `%i.11 = %i.10 + 2` and `%esign.0 = (%22 != 0x2d)`, while
  `if.end177`'s other three edges set `%i.11 = %inc158` and `%esign.0 = 1`.

Those ten blocks are straight-line and their pins are
`numFast_findBlock_land_lhs_true147`, `_NodeBlock`, `_LeafBlock`, `_LeafBlock1`,
`_if_then157`, `_land_lhs_true161`, `_NodeBlock7`, `_LeafBlock3`, `_LeafBlock5`,
`_if_then171` and `_if_end177`; the marker's case and the sign's presence are
the four path shapes.  What this module fixes is the run's start *conditioned
on* the index that nest produces, and `expRun_start` is that statement. -/

end NumFastStarts

/-! ### Axiom footprints

The dispatch's own facts are pinned: a change that introduces an axiom into a
block's step or into a run's start is visible in the build log.  The three
start theorems carry `Classical.choice` through the digit-window lemmas'
`by_contra` (`ult_digit_toNat`, `ult_nondigit_toNat`); nothing about the lexeme,
the byte or the counter rests on it.  The block steps and the invariant
builders are at `[propext, Quot.sound]`. -/

/-- info: 'LeanLLVM.Refinement.NumFastStarts.intRun_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.intRun_start

/-- info: 'LeanLLVM.Refinement.NumFastStarts.fracRun_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.fracRun_start

/-- info: 'LeanLLVM.Refinement.NumFastStarts.expRun_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.expRun_start

/-- info: 'LeanLLVM.Refinement.NumFastStarts.intRunInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.intRunInv_entry

/-- info: 'LeanLLVM.Refinement.NumFastStarts.fracRunInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.fracRunInv_entry

/-- info: 'LeanLLVM.Refinement.NumFastStarts.expRunInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.expRunInv_entry

/-- info: 'LeanLLVM.Refinement.NumFastStarts.sign_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.sign_step

/-- info: 'LeanLLVM.Refinement.NumFastStarts.ifEnd68_denote_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.NumFastStarts.ifEnd68_denote_zero




