/-
The two eight-digit fast paths, composed from their dispatch's edges.

`JsonStage2NumFastTaken` states each fast path at its guard's own block — the
guard's zero at `if.then22` for the integer part and at `while.cond91.preheader`
for the fraction — and `JsonStage2NumFastJoin.guard_join` states the integer
guard's *two* answers at one predicate.  A scan composition does not arrive at
those blocks: it arrives at `entry`, where the sign byte is read at position
`0`, and at `land.lhs.true71`, where the decimal point is read at `%i.5`.  This
module carries the same statements back to those edges, so the fast path is a
statement about the state the dispatch hands it rather than about a state a
caller must reconstruct.

* `intScan_fastTaken`: from `entry`, five steps — the emptiness test, the sign
  read, `if.end`, `if.end6`, `if.else` — reach `if.then22` with the block's own
  cells, and the taken guard's four reader answers reach `intRunInv` in ten
  (one-group) or twelve (two-group) control steps in all, at
  `(negIndex b + 1, 1)`, `(negIndex b + 9, 9)` or `(negIndex b + 17, 17)`.
  The guard's `Nat` reading is `negIndex b + 9 ≤ n`, and the `%v8` local the
  reader writes is `entry`'s own allocation at `s.next + 768 + 1568`.
* `whileCond91_refused_run` and `fracGuard_join`: the fraction guard's other
  answer, at the same predicate the fraction run's head reads: three steps to
  `fracRunInv` at `(i5 + 1, 0)`, with the guard's one and the guard's zero as
  the two `Nat` readings of `%add92582` and `%n`.
* `fracScan_fastTaken`: from `land.lhs.true71` — the `.` read at `%i.5` — three
  steps reach the fraction's guard, and the guard's zero's four answers reach
  `fracRunInv` in eight or ten steps in all, at `(i5 + 1, 0)`,
  `(i5 + 9, 8)` or `(i5 + 17, 16)`.

**What the composition is stated at.**  Every step is at
`stage2NumFastCalls epow`, the selection that answers the reader the fast path
calls; the statements therefore carry `epow`.  The runs these shapes enter are
stated at `s2HelperCalls` (`JsonStage2NumFastDigitRuns.intRun_end_run`,
`fracRun_end_run`), because the run's blocks call nothing.  Appending a run to
these shapes is therefore a change of `Calls` at a seam where both sides are
call-free but their *lemmas* are not yet parameterised: the fast path's reader is
answered only at `stage2NumFastCalls`, and the run's `BoundLoop` instance is
instantiated at `s2HelperCalls`.  That seam is named rather than assumed, and it
is what the arm's composition still owes — not the arithmetic, which is at the
runs' exits.
-/
import LeanLLVM.Refinement.JsonStage2NumFastJoin
import LeanLLVM.Refinement.JsonStage2NumFastScanRun

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastStarts
open LeanLLVM.Refinement.NumFastScanRun

namespace NumFastScanFast

/-! ### The dispatch's cells, one peel at a time

The environment a step reads is a `cells` builder over the one before it, so a
cell a block did not write is found by peeling the blocks that came after it.
The list below is the dispatch's builders on both routes — `entry`'s own
allocations, the sign's cells, the lead window's, the integer guard's, and the
fraction's test chain.  The names are qualified where the escape bodies carry a
same-named lemma (`LeanLLVM.Refinement.ifEnd_step`), so each step below is the
dispatch's own. -/
macro "ff_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only
       [stateAt, cells, numFastEntryEnv, signEnv, ifEndEnv, ifEndPhiEnv, ifEnd6Env,
        ifElseEnv, ifThen22Env, whileEndEnv, intPreheaderEnv, ifThen11Env, ifEnd68Env,
        ifEnd68PhiEnv, landLhsTrue71Env, ifThen76Env, lorLhsFalseEnv,
        whileCond91PreheaderEnv, whileEnd115Env, fracPreheaderEnv]
      block_lk)))

/-- `entry`'s `%v8`: the reader's four-byte local, the block's own allocation
after the digit array and the accumulator struct. -/
theorem entry_v8 {env : Env} {nxt : Nat} {cmp : BitVec 1} :
    lookupName (numFastEntryEnv env nxt cmp) "%v8"
      = some (.ptr (nxt + 768 + 1568)) := by
  simp only [numFastEntryEnv]
  block_lk

/-! ### The integer fast path from `entry`

The five dispatch steps are `JsonStage2NumFastStarts`' own — the same steps
`intRun_start` composes behind the guard's *refusal* — and the guard's taken
answer is `JsonStage2NumFastTaken.fpIfThen22_entry`'s four shapes.  The proof
here is that pair: the steps are composed as `runFuel` prefixes and the shapes
are the four implications the reader's `Option` answer admits. -/

/-- **The integer fast path, from `entry` to the run's invariant.**  At a
non-empty lexeme whose sign is at `0` and whose lead digit is at `negIndex b`,
with the eight-digit guard taken (`negIndex b + 9 ≤ n`), the body reaches
`intRunInv` in ten control steps for the one-group shapes and twelve for the
two-group ones, carrying the reader's answer's counters. -/
theorem intScan_fastTaken {epow : Int → Option EPow} {env : Env} {s : State}
    {a n : Nat} {bs : List UInt8} {b b0 : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : negIndex b < n)
    (hfast : negIndex b + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hsep : s.next + 768 + 1568 + 4 ≤ a ∨ a + n ≤ s.next + 768 + 1568) :
    (d8Value ((bs.drop (negIndex b + 1)).take 8) = none →
        ∃ e : State, intRunInv s.mem a n (negIndex b + 1) 1 bs
          (n - (negIndex b + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (10 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value ((bs.drop (negIndex b + 1)).take 8) = some w →
        w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (negIndex b + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 0 →
        negIndex b + 9 < n →
        ∃ e : State, intRunInv
          (writeBytes s.mem (s.next + 768 + 1568) (natToBytes w 4)) a n
          (negIndex b + 9) 9 bs (n - (negIndex b + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (10 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (negIndex b + 9)) 8
          = some ((bs.drop (negIndex b + 9)).take 8) →
        (s.next + 768 + 1568 + 4 ≤ a + (negIndex b + 9) ∨
          a + (negIndex b + 9) + 8 ≤ s.next + 768 + 1568) →
        ∀ (w : Nat), d8Value ((bs.drop (negIndex b + 1)).take 8) = some w →
        w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (negIndex b + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        negIndex b + 9 < n → d8Value ((bs.drop (negIndex b + 9)).take 8) = none →
        ∃ e : State, intRunInv
          (writeBytes s.mem (s.next + 768 + 1568) (natToBytes w 4)) a n
          (negIndex b + 9) 9 bs (n - (negIndex b + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (12 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (negIndex b + 9)) 8
          = some ((bs.drop (negIndex b + 9)).take 8) →
        (s.next + 768 + 1568 + 4 ≤ a + (negIndex b + 9) ∨
          a + (negIndex b + 9) + 8 ≤ s.next + 768 + 1568) →
        ∀ (w w2 : Nat), d8Value ((bs.drop (negIndex b + 1)).take 8) = some w →
        w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (negIndex b + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        negIndex b + 17 < n → d8Value ((bs.drop (negIndex b + 9)).take 8) = some w2 →
        w2 < 2 ^ 32 →
        ∃ e : State, intRunInv
          (writeBytes (writeBytes s.mem (s.next + 768 + 1568) (natToBytes w 4))
            (s.next + 768 + 1568) (natToBytes w2 4)) a n (negIndex b + 17) 17 bs
          (n - (negIndex b + 17)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (12 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 n ≠ 0x0000000000000000#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at h2
    simp at h2
    omega
  let cmp : BitVec 1 := evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64
  have hbit0 : cmp = 0 := NumFastStarts.eq_zero_iff _ _ |>.mpr hne
  have hb_toNat : 49 ≤ b0.toNat ∧ b0.toNat ≤ 57 :=
    ⟨UInt8.le_iff_toNat_le.mp hlead.1, UInt8.le_iff_toNat_le.mp hlead.2⟩
  have hb_ne30 : b0 ≠ 0x30 := by
    intro h
    rw [h] at hb_toNat
    exact absurd hb_toNat.1 (by decide)
  have hcmp9 : evalICmp .eq (JsonScanLane.vByte b0) 0x30#8 = 0 := by
    rw [NumFastStarts.eq_zero_iff]
    intro hh
    exact hb_ne30 (NumFastStarts.vByte_inj hh)
  have hor : evalICmp .ult (JsonScanLane.vByte b0 + 0xcf#8) 0x09#8 = 1 := by
    rw [NumFastStarts.ult_iff_one, NumFastStarts.ult_leadDigit_lt]
    exact hb_toNat
  have hcmp3 : evalICmp .ult (BitVec.ofNat 64 (negIndex b)) (BitVec.ofNat 64 n) = 1 := by
    rw [NumFastStarts.ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hltn
  have hlt63 : negIndex b < 2 ^ 63 := by omega
  have hguard : evalICmp .ugt (BitVec.ofNat 64 (negIndex b) + 0x9#64)
      (BitVec.ofNat 64 n) = 0 :=
    NumFastJoin.ugt_zero_ofNat_le hfast (by omega) (by omega)
  have h1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump (stateAt (numFastEntryEnv env s.next cmp) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "land.lhs.true", pre := some "entry" }) :=
    entry_step_land (calls := stage2NumFastCalls epow) hpc hn hbit0
  have h2 : step (stage2NumFastCalls epow) numFastBody (stateAt (numFastEntryEnv env s.next cmp) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "land.lhs.true", pre := some "entry" }) = .jump (stateAt (signEnv (numFastEntryEnv env s.next cmp) b) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.end", pre := some "land.lhs.true" }) :=
    NumFastStarts.sign_step (calls := stage2NumFastCalls epow) rfl (entry_env_lookup_p hp) hsign
  have h3 : step (stage2NumFastCalls epow) numFastBody (stateAt (signEnv (numFastEntryEnv env s.next cmp) b) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.end", pre := some "land.lhs.true" }) = .jump (stateAt (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.end6", pre := some "if.end" }) :=
    NumFastStarts.ifEnd_step (calls := stage2NumFastCalls epow) rfl rfl (signEnv_cmp1 _ b) (signEnv_spec _ b) (by ff_lk) hcmp3
  have h4 : step (stage2NumFastCalls epow) numFastBody (stateAt (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.end6", pre := some "if.end" }) = .jump (stateAt (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.else", pre := some "if.end6" }) :=
    NumFastStarts.ifEnd6_step (calls := stage2NumFastCalls epow) rfl (by ff_lk) (by ff_lk) hlt63 hbyte hcmp9
  have h5 : step (stage2NumFastCalls epow) numFastBody (stateAt (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.else", pre := some "if.end6" }) = .jump (stateAt (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.then22", pre := some "if.else" }) :=
    NumFastStarts.ifElse_step (calls := stage2NumFastCalls epow) rfl (by ff_lk) hor
  have hguardEnv : lookupName (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) "%p" = some (.ptr a) ∧ lookupName (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) "%v8" = some (.ptr (s.next + 768 + 1568)) ∧ lookupName (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) "%1" = some (.int 8 (JsonScanLane.vByte b0)) ∧ lookupName (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) "%i.0" = some (.int 64 (BitVec.ofNat 64 (negIndex b))) ∧ lookupName (ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    ⟨by ff_lk, by ff_lk, by ff_lk, by ff_lk, by ff_lk⟩
  obtain ⟨hp', hv8', h1', hi', hn'⟩ := hguardEnv
  obtain ⟨s1, s2, s3, s4⟩ :=
    NumFastTaken.fpIfThen22_entry (epow := epow) (env := ifElseEnv (ifEnd6Env (ifEndEnv (signEnv (numFastEntryEnv env s.next cmp) b) b n) a (negIndex b) b0) b0) (s := { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "if.then22", pre := some "if.else" }) (a := a) (v8a := s.next + 768 + 1568) (start := negIndex b) (n := n) (lead := (JsonScanLane.vByte b0 &&& 0x0f#8).toNat) (b0 := b0) (bs := bs) rfl rfl hp' hv8' h1' hi' hn' hread hltn hbyte rfl hlead hsep hnlt hguard
  refine ⟨fun hnone => ?_, fun w hsome hw hguard1 hmore => ?_,
    fun hsb hsep2 w hsome hw hguard1 hmore hnone => ?_,
    fun hsb hsep2 w w2 hsome hw hguard1 hmore hsome2 hw2 => ?_⟩
  · obtain ⟨e, hinv, hcont⟩ := s1 hnone
    exact ⟨e, hinv, fun k => by
      rw [show 10 + k = 1 + (1 + (1 + (1 + (1 + (5 + k))))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s2 w hsome hw hguard1 hmore
    exact ⟨e, hinv, fun k => by
      rw [show 10 + k = 1 + (1 + (1 + (1 + (1 + (5 + k))))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s3 hsb hsep2 w hsome hw hguard1 hmore hnone
    exact ⟨e, hinv, fun k => by
      rw [show 12 + k = 1 + (1 + (1 + (1 + (1 + (7 + k))))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s4 hsb hsep2 w w2 hsome hw hguard1 hmore hsome2 hw2
    exact ⟨e, hinv, fun k => by
      rw [show 12 + k = 1 + (1 + (1 + (1 + (1 + (7 + k))))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5]
      exact hcont k⟩

/-! ### The fraction guard's refused answer

The fraction's guard at `while.cond91.preheader` tests `%add92582 = %i.5 + 9`
against `%n`.  Refused, the block leaves for `while.end115`, whose three `phi`s
take the guard's own cells — the index `%inc77`, the count zero, the accumulator
zero — and the digit head's preheader adds the length.  Three steps reach
`fracRunInv` at `(i5 + 1, 0)`: the index after the `.` and no fraction digits
counted. -/
theorem whileCond91_refused_run {epow : Int → Option EPow} {env : Env} {s : State}
    {a i5 n : Nat} {bs : List UInt8}
    (hpc : s.pc = "while.cond91.preheader")
    (hparts : fracPartCells env)
    (hp : lookupName env "%p" = some (.ptr a))
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hnext : i5 + 1 < n) (hnlt : n < 2 ^ 63) (hfast : n < i5 + 9) :
    ∃ e : State, fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody (stateAt env s) =
        runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hbit : evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) (BitVec.ofNat 64 n) = 1 :=
    NumFastJoin.ugt_one_ofNat_lt hfast (by omega) (by omega)
  have hult : evalICmp .ult (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n) = 1 := by
    rw [NumFastStarts.ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hnext
  have h1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump (stateAt (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) { s with pc := "while.end115", pre := some "while.cond91.preheader" }) :=
    NumFastStarts.whileCond91Preheader_step (calls := stage2NumFastCalls epow) hpc hi5 hn hbit
  have h2 : step (stage2NumFastCalls epow) numFastBody (stateAt (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) { s with pc := "while.end115", pre := some "while.cond91.preheader" }) = .jump (stateAt (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) :=
    NumFastStarts.whileEnd115_step (calls := stage2NumFastCalls epow) rfl rfl (by ff_lk) (by ff_lk) hult
  have hd5 : lookupName (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) "%fdig.0554" = some (.int 64 (0x0#64)) := by ff_lk
  have hi5' : lookupName (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) "%i.6552" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))) := by ff_lk
  have h3 : step (stage2NumFastCalls epow) numFastBody (stateAt (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) = .jump (stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n) (BitVec.ofNat 64 (i5 + 1)) (0x0#64)) { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }) :=
    NumFastStarts.fracPreheader_step (calls := stage2NumFastCalls epow) rfl hd5 hi5' (by ff_lk)
  refine ⟨stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n) (BitVec.ofNat 64 (i5 + 1)) (0x0#64)) { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }, ?_, ?_⟩
  · obtain ⟨idig5, ip5, hidig5, hip5⟩ := hparts
    have hpm : lookupName (stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n) (BitVec.ofNat 64 (i5 + 1)) (0x0#64)) { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }).env "%p" = some (.ptr a) := by ff_lk
    refine NumFastStarts.fracRunInv_entry (s := stateAt (fracPreheaderEnv (whileEnd115Env (whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 (i5 + 1)) (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n) (BitVec.ofNat 64 (i5 + 1)) (0x0#64)) { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }) (mem := s.mem) (p := a) (n := n) (i0 := i5 + 1) (d0 := 0) (bs := bs) rfl rfl rfl hnext hnlt (by omega) hpm (by ff_lk) hread (by ff_lk) ⟨idig5, ip5, by ff_lk, by ff_lk⟩ (by ff_lk) (by ff_lk) (by
        rw [Nat.sub_zero, show min 0 19 = 0 from by decide, digitFold_zero]
        ff_lk)
  · intro k
    rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
      runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]

/-! ### The fraction guard's two answers

`while.cond91.preheader`'s `condbr` decodes to the same pair of `Nat` readings
the integer guard's does: `%add92582 ugt %n` at zero is `i5 + 9 ≤ n`, and at one
is `n < i5 + 9`.  Taken, the four reader answers are
`fracWhileCond91_entry`'s; refused, the run starts at `(i5 + 1, 0)`. -/
theorem fracGuard_join {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a i5 n : Nat} {bs : List UInt8}
    (hpc : s.pc = "while.cond91.preheader")
    (hparts : fracPartCells env)
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hnext : i5 + 1 < n) (hnlt : n < 2 ^ 63)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) :
    (i5 + 9 ≤ n →
        (d8Value ((bs.drop (i5 + 1)).take 8) = none →
            ∃ e : State, fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
              ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody
                (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
        ∧ (∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
            NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
              (BitVec.ofNat 64 n) = 0 →
            i5 + 1 + 8 < n →
            ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n
              (i5 + 1 + 8) 8 bs (n - (i5 + 1 + 8)) e 0 ∧
              ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody
                (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
        ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8
              = some ((bs.drop (i5 + 1 + 8)).take 8) →
            (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
            ∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
            NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
              (BitVec.ofNat 64 n) = 1 →
            i5 + 1 + 8 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = none →
            ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n
              (i5 + 1 + 8) 8 bs (n - (i5 + 1 + 8)) e 0 ∧
              ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody
                (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
        ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8
              = some ((bs.drop (i5 + 1 + 8)).take 8) →
            (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
            ∀ (w w2 : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
            NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
              (BitVec.ofNat 64 n) = 1 →
            i5 + 1 + 16 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = some w2 →
            w2 < 2 ^ 32 →
            ∃ e : State, fracRunInv
              (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a (natToBytes w2 4))
              a n (i5 + 1 + 16) 16 bs (n - (i5 + 1 + 16)) e 0 ∧
              ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody
                (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e))
    ∧ (n < i5 + 9 →
        ∃ e : State, fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · exact NumFastTaken.fracWhileCond91_entry (epow := epow) hpc hparts hp hv8 hi5 hinc hn
      hread hge hnlt hsep hsep2
      (NumFastJoin.ugt_zero_ofNat_le (i0 := i5) hge (by omega) (by omega))
  · exact whileCond91_refused_run hpc hparts hp hi5 hinc hn hread hnext hnlt hlt

/-! ### The fraction fast path from the `.`

`land.lhs.true71` loads the byte at `%i.5` and tests it against `0x2e`; taken,
`if.then76` bounds the index after the `.`, `lor.lhs.false` requires a digit
there, and `while.cond91.preheader` is the guard.  The four dispatch steps are
`fracRun_start`'s, and the guard's zero's four answers are
`fracWhileCond91_entry`'s. -/
theorem fracScan_fastTaken {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a i5 n : Nat} {bs : List UInt8} {bd bd2 : UInt8}
    (hpc : s.pc = "land.lhs.true71")
    (hparts : fracPartCells env)
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hdot : readByte s.mem (a + i5) = some bd) (hdoteq : bd = 0x2E)
    (hd2 : readByte s.mem (a + (i5 + 1)) = some bd2)
    (hd2digit : IsDigitB bd2 = true)
    (hltn : i5 + 1 < n) (hfast : i5 + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) :
    (d8Value ((bs.drop (i5 + 1)).take 8) = none →
        ∃ e : State, fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (8 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 0 →
        i5 + 1 + 8 < n →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n
          (i5 + 1 + 8) 8 bs (n - (i5 + 1 + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (8 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8
          = some ((bs.drop (i5 + 1 + 8)).take 8) →
        (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
        ∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        i5 + 1 + 8 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = none →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n
          (i5 + 1 + 8) 8 bs (n - (i5 + 1 + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (10 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8
          = some ((bs.drop (i5 + 1 + 8)).take 8) →
        (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
        ∀ (w w2 : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        i5 + 1 + 16 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = some w2 →
        w2 < 2 ^ 32 →
        ∃ e : State, fracRunInv
          (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a (natToBytes w2 4))
          a n (i5 + 1 + 16) 16 bs (n - (i5 + 1 + 16)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (10 + k) numFastBody
            (stateAt env s) = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  have hi63 : i5 < 2 ^ 63 := by omega
  have hbit : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 1 := by
    rw [NumFastStarts.eq_iff_one, hdoteq]; rfl
  have hinc64 : evalICmp .ult (BitVec.ofNat 64 i5 + 0x1#64) (BitVec.ofNat 64 n) = 1 := by
    rw [NumFastStarts.ult_iff_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      NumFastStarts.toNat_add_const (by omega)]
    exact hltn
  have hnd : evalICmp .ult (JsonScanLane.vByte bd2 + 0xc6#8) 0xf6#8 = 0 := by
    rw [NumFastStarts.ult_zero_iff]
    intro hh
    have hr : 48 ≤ bd2.toNat ∧ bd2.toNat ≤ 57 :=
      (NumFastStarts.isDigitB_toNat_iff bd2).mp hd2digit
    have h2 : (JsonScanLane.vByte bd2 + 0xc6#8).toNat < (0xf6#8).toNat := by
      simpa using hh
    exact (NumFastStarts.ult_nondigit_lt bd2).mp h2 hr
  have hinc_lk : BitVec.ofNat 64 (i5 + 1) = BitVec.ofNat 64 i5 + 0x1#64 :=
    (ofNat64_add_one (by omega)).symm
  have h1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump (stateAt (landLhsTrue71Env env a i5 bd) { s with pc := "if.then76", pre := some "land.lhs.true71" }) :=
    NumFastStarts.landLhsTrue71_step (calls := stage2NumFastCalls epow) hpc hp hi5 hi63 hdot hbit
  have h2 : step (stage2NumFastCalls epow) numFastBody (stateAt (landLhsTrue71Env env a i5 bd) { s with pc := "if.then76", pre := some "land.lhs.true71" }) = .jump (stateAt (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) { s with pc := "lor.lhs.false", pre := some "if.then76" }) :=
    NumFastStarts.ifThen76_step (calls := stage2NumFastCalls epow) rfl (by ff_lk) (by ff_lk) hinc64
  have hinc_d : lookupName (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))) := by
    rw [hinc_lk]; ff_lk
  have h3 : step (stage2NumFastCalls epow) numFastBody (stateAt (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) { s with pc := "lor.lhs.false", pre := some "if.then76" }) = .jump (stateAt (lorLhsFalseEnv (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2) { s with pc := "while.cond91.preheader", pre := some "lor.lhs.false" }) :=
    NumFastStarts.lorLhsFalse_step_digit (calls := stage2NumFastCalls epow) rfl (by ff_lk) hinc_d (by omega) hd2 hnd
  have hguardEnv : lookupName (lorLhsFalseEnv (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2) "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))) := by
    rw [hinc_lk]; ff_lk
  obtain ⟨s1, s2, s3, s4⟩ :=
    NumFastTaken.fracWhileCond91_entry (epow := epow) (env := lorLhsFalseEnv (ifThen76Env (landLhsTrue71Env env a i5 bd) i5 (BitVec.ofNat 64 n)) a (i5 + 1) bd2) (s := { s with pc := "while.cond91.preheader", pre := some "lor.lhs.false" }) (a := a) (v8a := v8a) (i5 := i5) (n := n) (bs := bs) rfl (by
      obtain ⟨idig5, ip5, hidig5, hip5⟩ := hparts
      exact ⟨idig5, ip5, by ff_lk, by ff_lk⟩) (by ff_lk) (by ff_lk) (by ff_lk) hguardEnv (by ff_lk) hread hfast hnlt hsep hsep2 (NumFastJoin.ugt_zero_ofNat_le (i0 := i5) hfast (by omega) (by omega))
  refine ⟨fun hnone => ?_, fun w hsome hw hguard1 hmore => ?_,
    fun hsb hsep3 w hsome hw hguard1 hmore hnone => ?_,
    fun hsb hsep3 w w2 hsome hw hguard1 hmore hsome2 hw2 => ?_⟩
  · obtain ⟨e, hinv, hcont⟩ := s1 hnone
    exact ⟨e, hinv, fun k => by
      rw [show 8 + k = 1 + (1 + (1 + (5 + k))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s2 w hsome hw hguard1 hmore
    exact ⟨e, hinv, fun k => by
      rw [show 8 + k = 1 + (1 + (1 + (5 + k))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s3 hsb hsep3 w hsome hw hguard1 hmore hnone
    exact ⟨e, hinv, fun k => by
      rw [show 10 + k = 1 + (1 + (1 + (7 + k))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]
      exact hcont k⟩
  · obtain ⟨e, hinv, hcont⟩ := s4 hsb hsep3 w w2 hsome hw hguard1 hmore hsome2 hw2
    exact ⟨e, hinv, fun k => by
      rw [show 10 + k = 1 + (1 + (1 + (7 + k))) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]
      exact hcont k⟩

/-! ### Axiom footprints

`#print axioms` on the four statements, pinned with `#guard_msgs` so the build
checks the footprint rather than printing it: the two compositions carry
`Classical.choice` through `fpIfThen22_entry`/`fracWhileCond91_entry`'s digit
windows, and the refused run is `[propext, Quot.sound]`. -/

/-- info: 'LeanLLVM.Refinement.NumFastScanFast.intScan_fastTaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_fastTaken

/-- info: 'LeanLLVM.Refinement.NumFastScanFast.whileCond91_refused_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whileCond91_refused_run

/-- info: 'LeanLLVM.Refinement.NumFastScanFast.fracGuard_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracGuard_join

/-- info: 'LeanLLVM.Refinement.NumFastScanFast.fracScan_fastTaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracScan_fastTaken

end NumFastScanFast

end LeanLLVM.Refinement
