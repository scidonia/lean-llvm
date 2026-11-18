/-
The guard's `if`: both of the scan's runs in one statement.

`num_fast_el1`'s integer part has one branch point that decides which run
consumes the digits: `if.then22`'s `%cmp27564.not = (%i.0 + 9 ugt %n)`.
Refused, `while.end` merges the lead digit and the run starts at
`land.lhs.true41` with one digit counted; taken, `while.body.preheader` reads the
next eight bytes and the run starts with one, nine or seventeen digits counted.
`JsonStage2NumFastScanRun.intScan_run` states the scan behind the refusal, so a
scan from `entry` needs the guard's other answer as well.

This module is that statement.  Both answers reach `intRunInv` — the same
predicate at the same head — so the run's own bounded-loop instance continues
either way, and which one it is is the two `Nat` readings of `%add563` and `%n`.
The refusal is three control steps from `if.then22` (`while.end`, the digit head's
preheader, the head); the taken answer is
`JsonStage2NumFastTaken.fpIfThen22_entry`'s four shapes.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTaken

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastStarts

namespace NumFastJoin

/-! ### The guard's two readings

`%add563 ugt %n` is the `condbr`'s zero exactly when the length reaches the guard
sum, and its one exactly when the length falls short of it. -/

/-- `%add563 ugt %n` at zero is the length past the guard's sum. -/
theorem ugt_zero_ofNat_le {i0 n : Nat} (h : i0 + 9 ≤ n) (h64 : i0 + 9 < 2 ^ 64)
    (hn64 : n < 2 ^ 64) :
    evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n) = 0 := by
  refine (NumFastStarts.ult_zero_iff (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 i0 + 0x9#64)).mpr ?_
  intro hlt
  have h1 : (BitVec.ofNat 64 i0 + 0x9#64).toNat = i0 + 9 :=
    NumFastStarts.toNat_add_const (j := i0) (k := 9) h64
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  rw [h1, h2] at hlt
  omega

/-- `%add563 ugt %n` at one is the guard's sum past the length. -/
theorem ugt_one_ofNat_lt {i0 n : Nat} (h : n < i0 + 9) (h64 : i0 + 9 < 2 ^ 64)
    (hn64 : n < 2 ^ 64) :
    evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n) = 1 := by
  refine (NumFastStarts.ugt_iff_one (BitVec.ofNat 64 i0 + 0x9#64)
    (BitVec.ofNat 64 n)).mpr ?_
  have h1 : (BitVec.ofNat 64 i0 + 0x9#64).toNat = i0 + 9 :=
    NumFastStarts.toNat_add_const (j := i0) (k := 9) h64
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  rw [h2, h1]
  exact h

/-! ### The refused answer's run

The block's one leaves for `while.end`, whose `phi`s take the lead digit's value,
the count one and the index after the lead; the digit head's preheader adds the
length, and three control steps reach the run's invariant. -/

/-- **`if.then22`'s refused edge is the run's ordinary start.**  Three control
steps reach `intRunInv` at `(start + 1, 1)` with the walk's memory: the
`while.end` merge, the digit head's preheader, and the head. -/
theorem ifThen22_refused_run {epow : Int → Option EPow} {env : Env} {s : State}
    {a n start : Nat} {b0 : UInt8} {bs : List UInt8}
    (hpc : s.pc = "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 start)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hbyte : readByte s.mem (a + start) = some b0)
    (hdig : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hltn : start < n) (hnext : start + 1 < n) (hnlt : n < 2 ^ 63)
    (hbit : evalICmp .ugt (BitVec.ofNat 64 start + 0x9#64) (BitVec.ofNat 64 n) = 1) :
    ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length s.mem a n hread
  have hdigB : IsDigitB b0 = true := by
    unfold IsDigitB
    rw [Bool.and_eq_true]
    have h30 : (0x30 : UInt8) ≤ b0 := by
      have h49 : (0x31 : UInt8).toNat ≤ b0.toNat := UInt8.le_iff_toNat_le.mp hdig.1
      rw [show (0x31 : UInt8).toNat = 49 from by decide] at h49
      exact UInt8.le_iff_toNat_le.mpr (by
        rw [show (0x30 : UInt8).toNat = 48 from by decide]
        omega)
    exact ⟨decide_eq_true h30, decide_eq_true hdig.2⟩
  have hget : bs.getD start 0 = b0 := getD_of_readBytes hread hltn hbyte
  have hfold : digitFold bs start 1 = (JsonScanLane.vByte b0 &&& 0x0f#8).toNat := by
    rw [NumFastSeams.digitFold_one (by omega) hget, digit_and_toNat hdigB]
  have h1s : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.ifThen22Env env start b0 n)
        { s with pc := "while.end", pre := some "if.then22" }) :=
    NumFastStarts.ifThen22_step (calls := stage2NumFastCalls epow) hpc h1 hi hn hbit
  have hb : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%conv25"
      = some (.int 64 (BitVec.ofNat 64
        (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) := by
    lk_all
  have hi26 : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%inc26"
      = some (.int 64 (BitVec.ofNat 64 start + 0x1#64)) := by
    lk_all
  have hbit2 : evalICmp .ult (BitVec.ofNat 64 start + 0x1#64) (BitVec.ofNat 64 n) = 1 := by
    rw [NumFastStarts.ult_iff_one, NumFastStarts.toNat_add_const (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hnext
  have h2s : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastStarts.ifThen22Env env start b0 n)
        { s with pc := "while.end", pre := some "if.then22" }) =
      .jump (stateAt (NumFastStarts.whileEndEnv (NumFastStarts.ifThen22Env env start b0 n)
          start b0 n)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) :=
    NumFastStarts.whileEnd_step (calls := stage2NumFastCalls epow) rfl rfl hb hi26
      (by lk_all) hbit2
  have hd6 : lookupName (NumFastStarts.whileEndEnv
      (NumFastStarts.ifThen22Env env start b0 n) start b0 n) "%idig.0560"
      = some (.int 64 (0x1#64)) := by lk_all
  have hi6' : lookupName (NumFastStarts.whileEndEnv
      (NumFastStarts.ifThen22Env env start b0 n) start b0 n) "%i.1558"
      = some (.int 64 (BitVec.ofNat 64 start + 0x1#64)) := by lk_all
  have hn' : lookupName (NumFastStarts.whileEndEnv
      (NumFastStarts.ifThen22Env env start b0 n) start b0 n) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by lk_all
  have h3s : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastStarts.whileEndEnv
        (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) =
      .jump (stateAt (NumFastStarts.intPreheaderEnv (NumFastStarts.whileEndEnv
          (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
          (BitVec.ofNat 64 n) (BitVec.ofNat 64 start + 0x1#64) (0x1#64))
        { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }) :=
    NumFastStarts.intPreheader_step (calls := stage2NumFastCalls epow) rfl hd6 hi6' hn'
  refine ⟨stateAt (NumFastStarts.intPreheaderEnv (NumFastStarts.whileEndEnv
      (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
      (BitVec.ofNat 64 n) (BitVec.ofNat 64 start + 0x1#64) (0x1#64))
      { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" },
    ?_, ?_⟩
  refine NumFastStarts.intRunInv_entry (mem := s.mem) (p := a) (n := n)
      (i0 := start + 1) (d0 := 1) (bs := bs) rfl rfl rfl hnext hnlt (by omega)
      ?_ ?_ hread ?_ ?_ ?_ ?_
  · lk_all
  · lk_all
  · rw [show BitVec.ofNat 64 (start + 1) = BitVec.ofNat 64 start + 0x1#64
        from (ofNat64_add_one (by omega)).symm]
    simp only [stateAt, NumFastStarts.intPreheaderEnv]
    block_lk
  · simp only [stateAt]
    have hcell : lookupName (NumFastStarts.intPreheaderEnv (NumFastStarts.whileEndEnv
        (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 start + 0x1#64) (0x1#64)) "%i.1558"
        = some (.int 64 (BitVec.ofNat 64 start + 0x1#64)) := by lk_all
    rw [hcell, ofNat64_add_one (by omega)]
  · simp only [stateAt]
    have hcell : lookupName (NumFastStarts.intPreheaderEnv (NumFastStarts.whileEndEnv
        (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 start + 0x1#64) (0x1#64)) "%idig.0560"
        = some (.int 64 (0x1#64)) := by lk_all
    rw [hcell]
  · simp only [stateAt]
    have hcell : lookupName (NumFastStarts.intPreheaderEnv (NumFastStarts.whileEndEnv
        (NumFastStarts.ifThen22Env env start b0 n) start b0 n)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 start + 0x1#64) (0x1#64)) "%ip.0562"
        = some (.int 64 (BitVec.ofNat 64
          (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)) := by lk_all
    rw [hcell]
    rw [show start + 1 - 1 = start from by omega, show min 1 19 = 1 from by decide]
    rw [← hfold]
  · intro k
    rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
      runFuel_jump_prefix h1s, runFuel_jump_prefix h2s, runFuel_jump_prefix h3s]

/-! ### The guard's two answers, one statement

`if.then22`'s `condbr` decides which run: the refusal is the ordinary start above
and the taken answer is `fpIfThen22_entry`'s four shapes.  The predicate below is
that pair of answers as one proposition, and `guard_join` proves it from the
block's own cells. -/

/-- The scan's answer at `if.then22`: whichever answer the guard gave, the head's
invariant at the count the run began with — the refusal at `(start + 1, 1)` in
three steps, the taken answer in the reader's four shapes at five and seven. -/
def guardOutcome (epow : Int → Option EPow) (env : Env) (s : State)
    (a v8a start n : Nat) (bs : List UInt8) : Prop :=
  (start + 9 ≤ n →
      (d8Value ((bs.drop (start + 1)).take 8) = none →
          ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
            ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
              = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
          NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
            (BitVec.ofNat 64 n) = 0 →
          start + 9 < n →
          ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
            (n - (start + 9)) e 0 ∧
            ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
              = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8 = some ((bs.drop (start + 9)).take 8) →
          (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
          ∀ (w : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
          NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
            (BitVec.ofNat 64 n) = 1 →
          start + 9 < n → d8Value ((bs.drop (start + 9)).take 8) = none →
          ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
            (n - (start + 9)) e 0 ∧
            ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
              = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8 = some ((bs.drop (start + 9)).take 8) →
          (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
          ∀ (w w2 : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
          NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
            (BitVec.ofNat 64 n) = 1 →
          start + 17 < n → d8Value ((bs.drop (start + 9)).take 8) = some w2 →
          w2 < 2 ^ 32 →
          ∃ e : State, intRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
            (natToBytes w2 4)) a n (start + 17) 17 bs (n - (start + 17)) e 0 ∧
            ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
              = runFuel (stage2NumFastCalls epow) k numFastBody e))
  ∧ (n < start + 9 →
      ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
        ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody (stateAt env s)
          = runFuel (stage2NumFastCalls epow) k numFastBody e)

/-- **The guard's two answers, one statement.**  The block's `condbr` splits on
two `Nat` readings — `start + 9 ≤ n` takes the eight-digit reader and
`n < start + 9` refuses it — and both answers reach `intRunInv`. -/
theorem guard_join {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n : Nat} {b0 : UInt8} {bs : List UInt8}
    (hpc : s.pc = "if.then22")
    (hpre : s.pre = some "if.else")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 start)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hltn : start < n)
    (hnext : start + 1 < n)
    (hbyte : readByte s.mem (a + start) = some b0)
    (hdig : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hnlt : n < 2 ^ 63) :
    guardOutcome epow env s a v8a start n bs := by
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · exact NumFastTaken.fpIfThen22_entry (epow := epow)
      (lead := (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)
      hpc hpre hp hv8 h1 hi hn hread hltn hbyte rfl hdig hsep hnlt
      (ugt_zero_ofNat_le (i0 := start) hge (by omega) (by omega))
  · exact ifThen22_refused_run (epow := epow) hpc hp h1 hi hn hread hbyte hdig hltn hnext hnlt
      (ugt_one_ofNat_lt (i0 := start) hlt (by omega) (by omega))

/-! ### Axiom footprints

The two readings are `ult_iff_one`'s two-valued branch; the refused run adds the
head's `ofNat64_add_one`; the taken answer is `fpIfThen22_entry`'s. -/

/-- info: 'LeanLLVM.Refinement.NumFastJoin.ugt_zero_ofNat_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ugt_zero_ofNat_le

/-- info: 'LeanLLVM.Refinement.NumFastJoin.ugt_one_ofNat_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ugt_one_ofNat_lt

/-- info: 'LeanLLVM.Refinement.NumFastJoin.ifThen22_refused_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ifThen22_refused_run

/-- info: 'LeanLLVM.Refinement.NumFastJoin.guard_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guard_join

end NumFastJoin

end LeanLLVM.Refinement
