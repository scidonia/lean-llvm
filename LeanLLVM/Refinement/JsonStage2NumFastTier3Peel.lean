/-
Tier 3's region past the poison edge: the peel epilogue's induction, and its
composition with the traversal's trip count.

`JsonStage2NumFastTier3.t3_traversal_counts_1_3` takes the peeled nest's entry at
a count `0 < k < 4` to `for.body.i.i566.i.i.epil` — the block that consumes the
peel's residue, one group per visit, with the two `phi`s the `poison` edge bound
and the residue counter at zero.  That block is the region's first loop: its own
terminator is `%epil.iter1084.cmp.not` (`%epil.iter1084.next = %xtraiter1083`),
so it visits exactly `%xtraiter1083` times and then leaves for
`while.cond.preheader.i.i577.i.i.epilog-lcssa`.

**The visit.**  One visit is the block's own `step`: `t3_epil_denote` at the
entry edge (the `unr` `phi` sources) and `t3_epil_denote_self` at the back edge
(the previous visit's `%indvars.iv.next.i.i575.i.i.epil`,
`%shr.i.i574.i.i.epil` and `%epil.iter1084.next`), then
`t3_epil_step_lcssa`/`t3_epil_step_self`.  The self edge's `denoteCode` is
stated here because the block's phis read a second pair of incoming operands and
`JsonStage2NumFastTier3`'s chain is the entry edge's.

**The invariant.**  `T3PeelInv addr N xt` carries the residue counter and its
distance to the peel's `%xtraiter1083`, the row of the table each remaining visit
reads — one eight-byte word per visit, from the visit's index upwards — and the
digit staging the copy's later blocks read.  A visit overwrites its own row (the
`i128` sum's low word), never a later one, so the staging that remains is the
staging at the next index; that is the whole of the memory the loop writes, and
`readBytes_writeBytes_above'` is the read that keeps it.

**The composition.**  `t3_traversal_peel_run` is the traversal's two steps
followed by the loop at its whole bound, so the region past the poison edge is
one `runFuel` chain from the peel's entry to the epilogue's exit, at the trip
count the peel's residue supplies.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopyLoop

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier3

namespace NumFastTier3Peel

/-- A sequence read above a written range is the read of the memory underneath.
`JsonStage2NumFastTaken`'s lemma is the same fact, but that module sits above this
one in the import graph, so the two-line lifting of `readByte_writeBytes_above` is
stated here. -/
theorem readBytes_writeBytes_above' (m : Mem) (bs : List UInt8) :
    ∀ (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | 0, addr, start, _ => rfl
  | n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs h]
      cases hr : readByte m addr with
      | none => rfl
      | some b =>
          rw [readBytes_writeBytes_above' m bs n (addr + 1) start (by omega)]

/-! ### The epilogue's environment

`t3_epil_denote` leaves `t3EpilEnv`'s cells, and the back edge's visit reads the
three the previous visit wrote.  The lookups below are that builder's own cells
and the ones it carries from the caller's environment. -/

theorem t3EpilEnv_iv (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%indvars.iv.i.i567.i.i.epil"
      = some (.int 64 iv) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_carry (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%carry.029.i.i568.i.i.epil"
      = some (.int 128 carry) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_iter (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%epil.iter1084"
      = some (.int 64 iter) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_next (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%indvars.iv.next.i.i575.i.i.epil"
      = some (.int 64 (iv + 0x1#64)) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_shrNext (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%shr.i.i574.i.i.epil"
      = some (.int 128 (t3EpilSum w carry >>> (0x00000000000000000000000000000040#128).toNat)) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_iterNext (env : Env) (addr : Nat) (w iv : BitVec 64) (carry : BitVec 128)
    (iter xt : BitVec 64) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%epil.iter1084.next"
      = some (.int 64 (iter + 0x1#64)) := by
  simp only [t3EpilEnv]; block_lk

theorem t3EpilEnv_pow {env : Env} {addr' : Nat} (addr : Nat) (w iv : BitVec 64)
    (carry : BitVec 128) (iter xt : BitVec 64)
    (h : lookupName env "%pow.i.i" = some (.ptr addr')) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%pow.i.i" = some (.ptr addr') := by
  simp only [t3EpilEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem t3EpilEnv_xt {env : Env} {xt' : BitVec 64} (addr : Nat) (w iv : BitVec 64)
    (carry : BitVec 128) (iter xt : BitVec 64)
    (h : lookupName env "%xtraiter1083" = some (.int 64 xt')) :
    lookupName (t3EpilEnv env addr w iv carry iter xt) "%xtraiter1083"
      = some (.int 64 xt') := by
  simp only [t3EpilEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The block at its back edge

The three `phi`s take the previous visit's cells: `%indvars.iv.next.i.i575.i.i.epil`,
`%shr.i.i574.i.i.epil` and `%epil.iter1084.next`.  The rest of the chain is the
entry edge's, which is why the statement below ends at the same `t3EpilState`. -/
theorem t3_epil_denote_self {calls : Calls} {env : Env} {s : State}
    {addr : Nat} {w : BitVec 64} {iv : BitVec 64} {carry : BitVec 128}
    {iter xt : BitVec 64}
    (hpre : s.pre = some "for.body.i.i566.i.i.epil")
    (hp : lookupName env "%pow.i.i" = some (.ptr addr))
    (hiv : lookupName env "%indvars.iv.next.i.i575.i.i.epil" = some (.int 64 iv))
    (hcarry : lookupName env "%shr.i.i574.i.i.epil" = some (.int 128 carry))
    (hiter : lookupName env "%epil.iter1084.next" = some (.int 64 iter))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 xt))
    (hpos : (iv.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (addr + (iv.signExtend 64).toNat * 8) 8
      = some (natToBytes w.toNat 8)) :
    denoteCode calls t3EpilInstrs (stateAt env s) =
      some (t3EpilState env addr w iv carry iter xt s) := by
  unfold t3EpilInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%indvars.iv.next.i.i575.i.i.epil" _ hiv
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%shr.i.i574.i.i.epil" _ hcarry
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%epil.iter1084.next" _ hiter
  rw [NumFastTier1.denoteCode_gep64_reg calls _ _ "%arrayidx.i.i569.i.i.epil" "%pow.i.i"
    "%indvars.iv.i.i567.i.i.epil" (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_load64 calls _ _ "%102" "%arrayidx.i.i569.i.i.epil"
    (by block_lk) hread _]
  rw [denoteCode_zext calls _ _ "%conv2.i.i570.i.i.epil" "%102" 64 128
    (by block_lk) _]
  rw [denoteCode_mul_imm_w calls _ _ "%mul.i.i571.i.i.epil"
    "%conv2.i.i570.i.i.epil" 128 (by block_lk) _]
  rw [denoteCode_add_reg_w calls _ _ "%add4.i.i572.i.i.epil" "%mul.i.i571.i.i.epil"
    "%carry.029.i.i568.i.i.epil" 128 (by block_lk) (by block_lk) _]
  rw [denoteCode_trunc calls _ _ "%conv5.i.i573.i.i.epil" "%add4.i.i572.i.i.epil"
    128 64 (by block_lk) _]
  rw [denoteCode_store64 calls _ _ "%conv5.i.i573.i.i.epil" "%arrayidx.i.i569.i.i.epil"
    (by block_lk) (by block_lk) _]
  rw [denoteCode_lshr_imm_w calls _ _ "%shr.i.i574.i.i.epil" "%add4.i.i572.i.i.epil"
    128 (by block_lk) _]
  rw [JsonScanLane.denoteCode_add_imm_w calls _ _ "%indvars.iv.next.i.i575.i.i.epil"
    "%indvars.iv.i.i567.i.i.epil" 64 (by block_lk) _]
  rw [JsonScanLane.denoteCode_add_imm_w calls _ _ "%epil.iter1084.next" "%epil.iter1084"
    64 (by block_lk) _]
  rw [BlockEval.denoteCode_icmp_eq_reg calls _ _ "%epil.iter1084.cmp.not"
    "%epil.iter1084.next" "%xtraiter1083" (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, runCells, t3EpilState, t3EpilEnv, t3EpilProd,
    t3EpilSum, t3PowConst]

/-! ### The visit's invariant

`r` visits remain, the residue counter is `c`, and the counter's distance to the
peel's `%xtraiter1083` is `r`.  A visit is one control step, so the loop's cost is
one; the exit test is `%xtraiter1083 ≤ c + 1`, which is the emitted
`%epil.iter1084.next = %xtraiter1083`.  The rows the remaining visits read are
carried as a function of the row's index: a visit writes its own row and no later
one, which is the only memory the loop touches. -/
def T3PeelInv (addr N xt : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "for.body.i.i566.i.i.epil" ∧
  lookupName s.env "%pow.i.i" = some (.ptr addr) ∧
  lookupName s.env "%xtraiter1083" = some (.int 64 (BitVec.ofNat 64 xt)) ∧
  N < 2 ^ 63 ∧
  xt < 2 ^ 63 ∧
  (∃ (iv : Nat) (carryB : BitVec 128) (row : Nat → BitVec 64),
    iv + r ≤ N ∧
    (∀ j, j < r →
      readBytes s.mem (addr + (iv + j) * 8) 8 = some (natToBytes (row (iv + j)).toNat 8)) ∧
    ((s.pre = some "while.cond.preheader.i.i577.i.i.unr-lcssa" ∧ c = 0 ∧
        lookupName s.env "%indvars.iv.i.i567.i.i.unr"
          = some (.int 64 (BitVec.ofNat 64 iv)) ∧
        lookupName s.env "%carry.029.i.i568.i.i.unr" = some (.int 128 carryB))
      ∨ (s.pre = some "for.body.i.i566.i.i.epil" ∧
        lookupName s.env "%indvars.iv.next.i.i575.i.i.epil"
          = some (.int 64 (BitVec.ofNat 64 iv)) ∧
        lookupName s.env "%shr.i.i574.i.i.epil" = some (.int 128 carryB) ∧
        lookupName s.env "%epil.iter1084.next"
          = some (.int 64 (BitVec.ofNat 64 c))))) ∧
  c + r = xt ∧ 1 ≤ r

/-- The visit's exit test: the residue counter's next value reached the peel's
`%xtraiter1083`. -/
def t3PeelAtBound (xt : Nat) : State → Nat → Bool := fun _ c => decide (xt ≤ c + 1)

/-- The block the epilogue leaves for, once the residue is spent. -/
def t3PeelExit : State → Prop := fun e =>
  e.pc = "while.cond.preheader.i.i577.i.i.epilog-lcssa"

/-- What the exit state carries: the table's base, the residue the loop spent,
and the shifted `i128` sum the truncation block reads. -/
def t3PeelExitWord (addr xt : Nat) : State → Prop := fun e =>
  lookupName e.env "%pow.i.i" = some (.ptr addr) ∧
  lookupName e.env "%xtraiter1083" = some (.int 64 (BitVec.ofNat 64 xt)) ∧
  ∃ carryB : BitVec 128, lookupName e.env "%shr.i.i574.i.i.epil" = some (.int 128 carryB)

/-- A visit's write is below the rows the later visits read, so the staging that
remains is the staging at the next index. -/
theorem row_shift {m : Mem} {addr : Nat} {bs : List UInt8} {iv j : Nat}
    {row : Nat → BitVec 64} (hlen : bs.length = 8)
    (h : readBytes m (addr + (iv + (j + 1)) * 8) 8
      = some (natToBytes (row (iv + (j + 1))).toNat 8)) :
    readBytes (writeBytes m (addr + iv * 8) bs) (addr + ((iv + 1) + j) * 8) 8
      = some (natToBytes (row ((iv + 1) + j)).toNat 8) := by
  have hidx : (iv + 1) + j = iv + (j + 1) := by omega
  rw [hidx, readBytes_writeBytes_above' m bs 8 _ _ (by rw [hlen]; omega)]
  exact h

/-! ### The visit's two arms

The back edge spends one step and advances the counter, the index and the carried
sum; the exit arm spends one step and leaves the three cells the truncation block
reads.  Each arm builds the successor invariant field by field, so a mismatch
names the cell it is about. -/
theorem t3_peel_step_loop (addr N xt : Nat) :
    ∀ (r : Nat) (s : State) (c : Nat), T3PeelInv addr N xt (r + 1) s c →
      t3PeelAtBound xt s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 1 ∧
        e.pc = "for.body.i.i566.i.i.epil" ∧ c < c' ∧
        T3PeelInv addr N xt r e c' ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e := by
  intro r s c hinv hb
  obtain ⟨hpc, hp, hxt, hN, hxt63, ⟨iv, carryB, row, hivN, hrow, hpre⟩, hsum, hr1⟩ := hinv
  unfold t3PeelAtBound at hb
  have hlt : ¬ (xt ≤ c + 1) := of_decide_eq_false hb
  have hc64 : c + 1 < 2 ^ 64 := by omega
  have hxt64 : xt < 2 ^ 64 := by omega
  have hivlt : iv < 2 ^ 63 := by omega
  have hposShift : ((BitVec.ofNat 64 iv).signExtend 64).toNat = iv := sExt_ofNat64 hivlt
  have hpos : ((BitVec.ofNat 64 iv).signExtend 64).toNat < 2 ^ 63 := by
    rw [hposShift]; exact hivlt
  have hrow0 : readBytes s.mem (addr + (iv + 0) * 8) 8
      = some (natToBytes (row (iv + 0)).toNat 8) := hrow 0 (by omega)
  have hread : readBytes s.mem (addr + ((BitVec.ofNat 64 iv).signExtend 64).toNat * 8) 8
      = some (natToBytes (row (iv + 0)).toNat 8) := by
    rw [hposShift]; exact hrow0
  have hneq : evalICmp .eq (BitVec.ofNat 64 c + 0x1#64) (BitVec.ofNat 64 xt)
      = (0 : BitVec 1) := by
    refine evalICmp_eq_ne ?_
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [ofNat64_add_one hc64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxt64] at h2
    omega
  have hlen : (natToBytes
      (BitVec.ofNat 64 ((t3EpilSum (row (iv + 0)) carryB).toNat % 2 ^ 64)).toNat 8).length
      = 8 := natToBytes_length _ _
  rcases hpre with hent | hback
  · obtain ⟨hpre0, hc0, hivCell, hcarryCell⟩ := hent
    subst hc0
    have hden := t3_epil_denote (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv)
      (carry := carryB) (xt := BitVec.ofNat 64 xt) hpre0 hp hivCell hcarryCell hxt hpos hread
    have hstep := t3_epil_step_self (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv) (carry := carryB)
      (iter := (0x0#64)) (xt := BitVec.ofNat 64 xt) hpc hden hneq
    have hpow' : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%pow.i.i" = some (.ptr addr) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_pow addr _ _ _ _ _ hp
    have hxt' : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%xtraiter1083" = some (.int 64 (BitVec.ofNat 64 xt)) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_xt addr _ _ _ _ _ hxt
    have hivN' : iv + 1 + r ≤ N := by omega
    have hrows' : ∀ j, j < r → readBytes (t3EpilState s.env addr (row (iv + 0))
        (BitVec.ofNat 64 iv) carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "for.body.i.i566.i.i.epil" }).mem
        (addr + ((iv + 1) + j) * 8) 8
        = some (natToBytes (row ((iv + 1) + j)).toNat 8) := by
      intro j hj
      have hmem : (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv) carryB
          (0x0#64) (BitVec.ofNat 64 xt)
          { s with pc := "for.body.i.i566.i.i.epil",
                   pre := some "for.body.i.i566.i.i.epil" }).mem
          = writeBytes s.mem (addr + iv * 8)
              (natToBytes (BitVec.ofNat 64 ((t3EpilSum (row (iv + 0)) carryB).toNat % 2 ^ 64)).toNat 8) := by
        simp only [t3EpilState, hposShift]
      rw [hmem]
      exact row_shift hlen (hrow (j + 1) (by omega))
    have hivNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%indvars.iv.next.i.i575.i.i.epil" = some (.int 64 (BitVec.ofNat 64 (iv + 1))) := by
      simp only [t3EpilState, t3EpilEnv, stateAt]
      block_lk
      rw [ofNat64_add_one (by omega)]
    have hcarryNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%shr.i.i574.i.i.epil"
        = some (.int 128 (t3EpilSum (row (iv + 0)) carryB >>> (0x00000000000000000000000000000040#128).toNat)) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_shrNext _ _ _ _ _ _ _
    have hiterNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (0x0#64) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%epil.iter1084.next" = some (.int 64 (BitVec.ofNat 64 (0 + 1))) := by
      simp only [t3EpilState, t3EpilEnv, stateAt]
      block_lk
      exact congrArg (fun x : BitVec 64 => some (Value.int 64 x))
        (ofNat64_add_one (j := 0) (by omega))
    refine ⟨_, 1, 1, le_rfl, rfl, by omega,
      ⟨rfl, hpow', hxt', hN, hxt63,
        ⟨iv + 1, t3EpilSum (row (iv + 0)) carryB >>> (0x00000000000000000000000000000040#128).toNat,
          row, hivN', hrows', Or.inr ⟨rfl, hivNext, hcarryNext, hiterNext⟩⟩,
        by omega, by omega⟩, ?_⟩
    · intro k; exact runFuel_jump_prefix hstep k
  · obtain ⟨hpre0, hivCell, hcarryCell, hiterCell⟩ := hback
    have hden := t3_epil_denote_self (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv)
      (carry := carryB) (iter := BitVec.ofNat 64 c) (xt := BitVec.ofNat 64 xt)
      hpre0 hp hivCell hcarryCell hiterCell hxt hpos hread
    have hstep := t3_epil_step_self (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv) (carry := carryB)
      (iter := BitVec.ofNat 64 c) (xt := BitVec.ofNat 64 xt) hpc hden hneq
    have hpow' : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%pow.i.i" = some (.ptr addr) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_pow addr _ _ _ _ _ hp
    have hxt' : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%xtraiter1083" = some (.int 64 (BitVec.ofNat 64 xt)) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_xt addr _ _ _ _ _ hxt
    have hivN' : iv + 1 + r ≤ N := by omega
    have hrows' : ∀ j, j < r → readBytes (t3EpilState s.env addr (row (iv + 0))
        (BitVec.ofNat 64 iv) carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "for.body.i.i566.i.i.epil" }).mem
        (addr + ((iv + 1) + j) * 8) 8
        = some (natToBytes (row ((iv + 1) + j)).toNat 8) := by
      intro j hj
      have hmem : (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv) carryB
          (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
          { s with pc := "for.body.i.i566.i.i.epil",
                   pre := some "for.body.i.i566.i.i.epil" }).mem
          = writeBytes s.mem (addr + iv * 8)
              (natToBytes (BitVec.ofNat 64 ((t3EpilSum (row (iv + 0)) carryB).toNat % 2 ^ 64)).toNat 8) := by
        simp only [t3EpilState, hposShift]
      rw [hmem]
      exact row_shift hlen (hrow (j + 1) (by omega))
    have hivNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%indvars.iv.next.i.i575.i.i.epil" = some (.int 64 (BitVec.ofNat 64 (iv + 1))) := by
      simp only [t3EpilState, t3EpilEnv, stateAt]
      block_lk
      rw [ofNat64_add_one (by omega)]
    have hcarryNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%shr.i.i574.i.i.epil"
        = some (.int 128 (t3EpilSum (row (iv + 0)) carryB >>> (0x00000000000000000000000000000040#128).toNat)) := by
      simp only [t3EpilState, stateAt]; exact t3EpilEnv_shrNext _ _ _ _ _ _ _
    have hiterNext : lookupName (t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv)
        carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt)
        { s with pc := "for.body.i.i566.i.i.epil", pre := some "for.body.i.i566.i.i.epil" }).env
        "%epil.iter1084.next" = some (.int 64 (BitVec.ofNat 64 (c + 1))) := by
      simp only [t3EpilState, t3EpilEnv, stateAt]
      block_lk
      exact congrArg (fun x : BitVec 64 => some (Value.int 64 x))
        (ofNat64_add_one (j := c) hc64)
    refine ⟨_, c + 1, 1, le_rfl, rfl, by omega,
      ⟨rfl, hpow', hxt', hN, hxt63,
        ⟨iv + 1, t3EpilSum (row (iv + 0)) carryB >>> (0x00000000000000000000000000000040#128).toNat,
          row, hivN', hrows', Or.inr ⟨rfl, hivNext, hcarryNext, hiterNext⟩⟩,
        by omega, by omega⟩, ?_⟩
    · intro k; exact runFuel_jump_prefix hstep k

theorem t3_peel_step_exit (addr N xt : Nat) :
    ∀ (r : Nat) (s : State) (c : Nat), T3PeelInv addr N xt r s c →
      t3PeelAtBound xt s c = true →
      ∃ (e : State) (j : Nat), j ≤ 1 ∧ t3PeelExit e ∧ t3PeelExitWord addr xt e ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e := by
  intro r s c hinv hb
  obtain ⟨hpc, hp, hxt, hN, hxt63, ⟨iv, carryB, row, hivN, hrow, hpre⟩, hsum, hr1⟩ := hinv
  unfold t3PeelAtBound at hb
  have hge : xt ≤ c + 1 := of_decide_eq_true hb
  have hcxt : c + 1 = xt := by omega
  have hivlt : iv < 2 ^ 63 := by omega
  have hposShift : ((BitVec.ofNat 64 iv).signExtend 64).toNat = iv := sExt_ofNat64 hivlt
  have hpos : ((BitVec.ofNat 64 iv).signExtend 64).toNat < 2 ^ 63 := by
    rw [hposShift]; exact hivlt
  have hrow0 : readBytes s.mem (addr + (iv + 0) * 8) 8
      = some (natToBytes (row (iv + 0)).toNat 8) := hrow 0 (by omega)
  have hread : readBytes s.mem (addr + ((BitVec.ofNat 64 iv).signExtend 64).toNat * 8) 8
      = some (natToBytes (row (iv + 0)).toNat 8) := by
    rw [hposShift]; exact hrow0
  have hbit : evalICmp .eq (BitVec.ofNat 64 c + 0x1#64) (BitVec.ofNat 64 xt)
      = (1 : BitVec 1) := by
    have h1 : BitVec.ofNat 64 c + 0x1#64 = BitVec.ofNat 64 xt := by
      rw [ofNat64_add_one (by omega), hcxt]
    rw [h1, evalICmp_eq_refl]
  rcases hpre with hent | hback
  · obtain ⟨hpre0, hc0, hivCell, hcarryCell⟩ := hent
    subst hc0
    have hden := t3_epil_denote (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv)
      (carry := carryB) (xt := BitVec.ofNat 64 xt) hpre0 hp hivCell hcarryCell hxt hpos hread
    have hstep := t3_epil_step_lcssa (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv) (carry := carryB)
      (iter := (0x0#64)) (xt := BitVec.ofNat 64 xt) hpc hden hbit
    refine ⟨t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv) carryB (0x0#64) (BitVec.ofNat 64 xt) { s with pc := "while.cond.preheader.i.i577.i.i.epilog-lcssa", pre := some "for.body.i.i566.i.i.epil" }, 1, le_rfl, rfl, ?_, ?_⟩
    · exact ⟨by simp only [t3EpilState, stateAt]; exact t3EpilEnv_pow addr _ _ _ _ _ hp,
        by simp only [t3EpilState, stateAt]; exact t3EpilEnv_xt addr _ _ _ _ _ hxt,
        by simp only [t3EpilState, stateAt]
           exact ⟨_, t3EpilEnv_shrNext _ _ _ _ _ _ _⟩⟩
    · intro k; exact runFuel_jump_prefix hstep k
  · obtain ⟨hpre0, hivCell, hcarryCell, hiterCell⟩ := hback
    have hden := t3_epil_denote_self (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv)
      (carry := carryB) (iter := BitVec.ofNat 64 c) (xt := BitVec.ofNat 64 xt)
      hpre0 hp hivCell hcarryCell hiterCell hxt hpos hread
    have hstep := t3_epil_step_lcssa (calls := s2HelperCalls) (env := s.env) (s := s)
      (addr := addr) (w := row (iv + 0)) (iv := BitVec.ofNat 64 iv) (carry := carryB)
      (iter := BitVec.ofNat 64 c) (xt := BitVec.ofNat 64 xt) hpc hden hbit
    refine ⟨t3EpilState s.env addr (row (iv + 0)) (BitVec.ofNat 64 iv) carryB (BitVec.ofNat 64 c) (BitVec.ofNat 64 xt) { s with pc := "while.cond.preheader.i.i577.i.i.epilog-lcssa", pre := some "for.body.i.i566.i.i.epil" }, 1, le_rfl, rfl, ?_, ?_⟩
    · exact ⟨by simp only [t3EpilState, stateAt]; exact t3EpilEnv_pow addr _ _ _ _ _ hp,
        by simp only [t3EpilState, stateAt]; exact t3EpilEnv_xt addr _ _ _ _ _ hxt,
        by simp only [t3EpilState, stateAt]
           exact ⟨_, t3EpilEnv_shrNext _ _ _ _ _ _ _⟩⟩
    · intro k; exact runFuel_jump_prefix hstep k

/-! ### The epilogue's loop

One visit per unit of the bound, at the emitted blocks: the head is the peel's
epilogue, the exit is the truncation block's predecessor, and the bound is the
residue the traversal's count supplies. -/
def t3PeelLoop (addr N xt : Nat) : BoundLoop s2HelperCalls numFastBody where
  head := "for.body.i.i566.i.i.epil"
  exitBlock := "while.cond.preheader.i.i577.i.i.epilog-lcssa"
  N := xt
  cost := 1
  Inv := T3PeelInv addr N xt
  atBound := t3PeelAtBound xt
  Exit := t3PeelExit
  ExitWord := t3PeelExitWord addr xt
  step_exit := by
    intro r s c hinv hb
    obtain ⟨e, j, hj, hexit, hword, hrun⟩ := t3_peel_step_exit addr N xt r s c hinv hb
    exact ⟨e, j, hj, hexit, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    exact t3_peel_step_loop addr N xt r s c hinv hb
  exit_at_zero := by
    intro s c h
    obtain ⟨-, -, -, -, -, -, -, hr1⟩ := h
    exact absurd hr1 (by omega)
  budget := by
    intro r s c h
    obtain ⟨-, -, -, -, -, -, hsum, -⟩ := h
    omega

/-- **The epilogue reaches the truncation block.**  At the whole residue as its
budget the loop leaves `while.cond.preheader.i.i577.i.i.epilog-lcssa` within
`(xt + 1) * 1` control steps, carrying the table's base, the residue and the
shifted sum. -/
theorem t3PeelLoop_run (addr N xt : Nat) (s : State) (k : Nat)
    (h : T3PeelInv addr N xt xt s 0) :
    ∃ (e : State) (j : Nat), j ≤ (xt + 1) * 1 ∧ t3PeelExit e ∧
      t3PeelExitWord addr xt e ∧
      runFuel s2HelperCalls (j + k) numFastBody s =
        runFuel s2HelperCalls k numFastBody e := by
  have h' : (t3PeelLoop addr N xt).Inv (t3PeelLoop addr N xt).N s 0 := by
    simpa only [t3PeelLoop] using h
  simpa only [t3PeelLoop] using (t3PeelLoop addr N xt).run s 0 h' k

/-- `%xtraiter1083` at a peeled count below four is the count itself: the residue
`%wide.trip.count & 3` does not mask a value the width already holds. -/
theorem and_three_ofNat {m : Nat} (hm : m < 4) :
    BitVec.ofNat 64 m &&& 0x3#64 = BitVec.ofNat 64 m := by
  match m, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | _ + 4, h => omega

/-- **The region past the poison edge, at the trip count.**  From the peel's
entry at a count `0 < k < 4`, the traversal's two steps reach the epilogue and
the epilogue's own induction spends the residue: the body leaves
`while.cond.preheader.i.i577.i.i.epilog-lcssa` within `2 + (k + 1) * 1` control
steps, carrying the shifted sum the truncation reads.  The residual edge zeroes
the epilogue's two carried words, so the first visit reads the table's row `0`
and the staging carries the rows from there. -/
theorem t3_traversal_peel_run {env : Env} {s : State} {c : BitVec 32} {addr N : Nat}
    {row : Nat → BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (h0 : 0 < c.toNat) (h4 : c.toNat < 4)
    (hN : N < 2 ^ 63) (hNc : c.toNat ≤ N)
    (hpow : lookupName env "%pow.i.i" = some (.ptr addr))
    (hrow : ∀ j, j < c.toNat →
      readBytes s.mem (addr + j * 8) 8 = some (natToBytes (row j).toNat 8))
    (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 2 + (c.toNat + 1) * 1 ∧ t3PeelExit e ∧
      t3PeelExitWord addr c.toNat e ∧
      runFuel s2HelperCalls (j + k) numFastBody (stateAt env s) =
        runFuel s2HelperCalls k numFastBody e := by
  have htraverse := t3_traversal_counts_1_3 (calls := s2HelperCalls) (env := env) (s := s)
    (c := c) hpc hc h0 h4
  have hinv : T3PeelInv addr N c.toNat c.toNat
      (stateAt (t3ResidualEnv (t3EntryEnv env c) (BitVec.ofNat 64 c.toNat))
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) 0 := by
    refine ⟨rfl, ?_, ?_, hN, by omega, ⟨0, 0, row, by omega, ?_,
      Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩, by omega, by omega⟩
    · simp only [t3ResidualEnv, t3EntryEnv, stateAt]; block_lk
    · simp only [t3ResidualEnv, t3EntryEnv, stateAt]
      rw [and_three_ofNat h4]
      block_lk
    · intro j hj
      have hshift : addr + (0 + j) * 8 = addr + j * 8 := by omega
      rw [hshift, show 0 + j = j from by omega]
      exact hrow j hj
    · simp only [t3ResidualEnv, t3EntryEnv, stateAt]
      rfl
    · simp only [t3ResidualEnv, t3EntryEnv, stateAt]
      rfl
  obtain ⟨e, j, hj, hexit, hword, hrun⟩ := t3PeelLoop_run addr N c.toNat _ k hinv
  refine ⟨e, 2 + j, by omega, hexit, hword, ?_⟩
  rw [show 2 + j + k = (j + k) + 2 from by omega, htraverse (j + k)]
  exact hrun

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.readBytes_writeBytes_above'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_above'

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.t3_epil_denote_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms t3_epil_denote_self

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.t3_peel_step_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_peel_step_loop

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.t3_peel_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_peel_step_exit

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.t3PeelLoop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3PeelLoop_run

/-- info: 'LeanLLVM.Refinement.NumFastTier3Peel.t3_traversal_peel_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_traversal_peel_run

end NumFastTier3Peel

end LeanLLVM.Refinement
