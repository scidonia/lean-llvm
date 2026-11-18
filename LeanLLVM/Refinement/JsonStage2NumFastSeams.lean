/-
`num_fast_el1`'s scan: the block seams the composed runs stop at, the two
eight-digit fast paths, and the register transport at the merge.

`JsonStage2NumFastScanRun` composes the integer run, the fraction dispatch and
the fraction run, the exponent's marker nest and the two merge steps, and names
four regions it does not cover.  This module is three of them.

**The one-block seams.**  `intScan_run` ends at the integer run's own exit
predicate, and `fracScan_run` starts at `land.lhs.true71`.  Between them there are
two blocks.  `if.end68` re-reads the run's three `phi` sources on its
`land.lhs.true41` edge — the edge the run leaves by when it stops on a non-digit,
which is the edge `ifEnd68_denote_loop` does not cover (that one is `while.end`'s)
— and `land.lhs.true71` tests the byte at the stop index against `'.'`.  The
second seam is the other side of the `.`: a byte that is not one leaves
`land.lhs.true71` for `if.end144`, whose three `phi`s read the dispatch's zeroes
and the stop index, and whose own test then takes the marker's block or the
no-exponent merge.  `intExit_dispatch_dot` and `nodot_seam` are those two
compositions, each two control steps.

**The register transport at the merge.**  `if.end62` is the digit run's back
edge: it merges `if.then55`'s folded accumulator with the guard's own, increments
the count and the index, and tests the index against the length.  `ifEnd62_denote`
and its two steps are that block, and they are what the tree was missing: every
`if.end62`-preceded statement in the tree (`ifEnd230_denote_end62`,
`intHead_denote_back`) takes the block's own registers as hypotheses instead.
The end-of-lexeme edge then carries two registers into the merge, `%ip.4` into
`if.end230`'s `%ip.5708717729` and `%7` into its `%idig.4709716730`;
`seven_tie` is `%7`'s reading.  `%7 = %idig.0560 + %n - %i.1558` is computed once,
at `land.lhs.true41.preheader`, from the run's *entry* registers; at the
end-of-lexeme edge the index has been incremented to `%n`, so `%7` is the digit
count `d0 + (%n - %i0)` — the count the merge's phis read — and
`intExit_gate` is the one-step composition that says so, with the
accumulated word's tie (`intRunExit_end230`) as the other half.

**The two eight-digit fast paths.**  `if.then22`'s taken edge leads to
`while.body.preheader`, whose `@num_d8_el1` call reads eight digits into the
local `%v8`; `cleanup` folds that word into the accumulator, advances the index by
eight, and re-enters while the byte after the group is inside the length and the
count is below twelve.  `cleanup112` is the fraction's copy of the same loop from
`while.body100.preheader`.  The two taken edges are `fpPreheader_step` (the
reader answered, the word written into `%v8`'s local, the path at `cleanup`) and
`fpPreheader_step_refuse` (the answer zero, the path at `cleanup.thread`); the
count guard's arithmetic is `fastGuard_two_groups`, so the loop admits at most
two groups.

The loop's blocks are chained.  `fpCleanupInstrs` is `cleanup`'s twelve-
instruction chain (`fpCleanup_denote_pre` from the first group,
`fpCleanup_denote_body` from the second) and its two exits are
`fpCleanup_step_body`/`fpCleanup_step_end`; `fpBodyInstrs` is the second group's
reader call (`fpBody_denote_ok`/`_denote_refuse`, `fpBody_step_ok`/`_step_refuse`);
`fpWhileEnd_denote_cleanup` reads `while.end`'s three `phi`s off the folded
cells.  `fpCleanup112Instrs`, `fpBody100Instrs` and `fpWhileEnd115Instrs` are the
fraction's copies, with `fpWhileEnd115_denote_cleanup`/`_denote_thread` the two
edges a fraction byte can leave by.  The loop's own `runFuel` composition is
supplied: `fpFastSecond_run` is the first fold, the second group and the
refused count guard as three steps to `while.end` (`fpFastSecond_run_refuse`
is the second reader's failed call instead), and the accumulator is the digits'
fold (`fpFirstFold`, `fpSecondFold`, `d8Value_slice`).  What the fast path still
owes is the taken guard's entry into `intRunInv`: the exit's three cells and
their ties are named, and the `while.end` block's own two steps to the head are
what remains of that composition.

**The reader's agreement.**  `num_d8_el1`'s answer against the eight bytes at its
pointer is `numD8Answer_read`'s model read at `readBytes`: `d8Value_eq_fold` says
the model's `d8Value` is the fold base ten the digit runs carry, and
`numD8Answer_writes` says the word it writes is the word the caller's `i32` load
reads back. -/
import LeanLLVM.Refinement.JsonStage2NumFastScanRun
import LeanLLVM.Refinement.JsonStage2NumFastCalls

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

namespace NumFastSeams

/-! ### The unsigned tests at `Nat` indices

The dispatch's tests compare `BitVec.ofNat 64` readings of `Nat` counters, so the
`Nat` ordering is what a seam's hypothesis has to be translated from and to. -/

/-- `i < n` at the 64-bit readings, when both fit. -/
theorem ult_ofNat_one {i n : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    evalICmp .ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 n) = 1 := by
  rw [NumFastStarts.ult_iff_one, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn]
  exact hi

/-- `¬ i < n` at the 64-bit readings. -/
theorem ult_ofNat_zero {i n : Nat} (hi : ¬ i < n) (hi64 : i < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    evalICmp .ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 n) = 0 := by
  rw [NumFastStarts.ult_zero_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hn]
  exact hi

/-! ### Seam one: `if.end68` from the integer run's non-digit exit

`if.end68`'s three `phi`s take the accumulator, the count and the index from the
edge the run leaves by.  The run's own exit is `land.lhs.true41`'s non-digit
branch, so the cells it reads are that head's `%ip.3573`, `%idig.3574` and
`%i.4575` — not the `while.end` cells `ifEnd68_denote_loop` reads. -/

/-- `if.end68` from `land.lhs.true41`: the run's three registers merge and the
index is tested against the length. -/
theorem ifEnd68_denote_head {calls : Calls} {env : Env} {s : State}
    {ip5 idig5 i5 nv : BitVec 64}
    (hpre : s.pre = some "land.lhs.true41")
    (hp5 : lookupName env "%ip.3573" = some (.int 64 ip5))
    (hd5 : lookupName env "%idig.3574" = some (.int 64 idig5))
    (hi5 : lookupName env "%i.4575" = some (.int 64 i5))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd68Instrs (stateAt env s) =
      some (stateAt (NumFastStarts.ifEnd68Env env i5 ip5 idig5 nv) s) := by
  unfold numFastIfEnd68Instrs
  block_eval

/-- **The integer run's exit registers.**  At `if.end68` the run has stopped on
the non-digit head, so the cells are `land.lhs.true41`'s, at the index the run
stopped at. -/
theorem intRunExit_end68 {bs : List UInt8} {i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end68") (he : intRunExit bs i0 d0 e) :
    ∃ i1, lookupName e.env "%i.4575" = some (.int 64 (BitVec.ofNat 64 i1)) ∧
      lookupName e.env "%idig.3574"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0)))) ∧
      lookupName e.env "%ip.3573" = some (.int 64
        (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (i1 - i0)) 19)))) := by
  rcases he with ⟨_, i1, hi1, hid, hip⟩ | ⟨h230, _⟩
  · exact ⟨i1, hi1, hid, hip⟩
  · rw [h230] at hpc; exact absurd hpc (by decide)

/-- **Seam one, the `.` taken.**  From the integer run's non-digit exit, the
dispatch's test and the `.` test take two control steps to `if.then76`, carrying
the stop index, the length and the base pointer. -/
theorem intExit_dispatch_dot {calls : Calls} {env : Env} {s : State}
    {a n i1 : Nat} {bd : UInt8} {ipv idigv : BitVec 64}
    (hpc : s.pc = "if.end68")
    (hpre : s.pre = some "land.lhs.true41")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hip : lookupName env "%ip.3573" = some (.int 64 ipv))
    (hid : lookupName env "%idig.3574" = some (.int 64 idigv))
    (hi : lookupName env "%i.4575" = some (.int 64 (BitVec.ofNat 64 i1)))
    (hi1 : i1 < n) (hnlt : n < 2 ^ 63)
    (hread : readByte s.mem (a + i1) = some bd) (hdot : bd = 0x2E) :
    ∃ e : State, e.pc = "if.then76" ∧ e.pre = some "land.lhs.true71" ∧
      e.mem = s.mem ∧
      lookupName e.env "%i.5" = some (.int 64 (BitVec.ofNat 64 i1)) ∧
      lookupName e.env "%p" = some (.ptr a) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      ∀ k, runFuel calls (2 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hi1' : i1 < 2 ^ 63 := by omega
  have hbit69 : evalICmp .ult (BitVec.ofNat 64 i1) (BitVec.ofNat 64 n) = 1 :=
    ult_ofNat_one hi1 (by omega)
  have hden := ifEnd68_denote_head (calls := calls) (s := s) hpre hip hid hi hn
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.ifEnd68Env env (BitVec.ofNat 64 i1) ipv idigv
          (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true71", pre := some "if.end68" }) :=
    NumFastStarts.ifEnd68_step (calls := calls) hpc hden hbit69
  have hp' : lookupName (NumFastStarts.ifEnd68Env env (BitVec.ofNat 64 i1) ipv idigv
      (BitVec.ofNat 64 n)) "%p" = some (.ptr a) := by
    simp only [NumFastStarts.ifEnd68Env, NumFastStarts.ifEnd68PhiEnv]
    block_lk
  have hi' : lookupName (NumFastStarts.ifEnd68Env env (BitVec.ofNat 64 i1) ipv idigv
      (BitVec.ofNat 64 n)) "%i.5" = some (.int 64 (BitVec.ofNat 64 i1)) := by
    simp only [NumFastStarts.ifEnd68Env, NumFastStarts.ifEnd68PhiEnv]
    block_lk
  have hbit74 : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 1 := by
    rw [NumFastStarts.eq_iff_one, hdot]; decide
  have h2 : step calls numFastBody
      (stateAt (NumFastStarts.ifEnd68Env env (BitVec.ofNat 64 i1) ipv idigv
        (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true71", pre := some "if.end68" }) =
      .jump (stateAt
        (NumFastStarts.landLhsTrue71Env (NumFastStarts.ifEnd68Env env
          (BitVec.ofNat 64 i1) ipv idigv (BitVec.ofNat 64 n)) a i1 bd)
        { s with pc := "if.then76", pre := some "land.lhs.true71" }) :=
    NumFastStarts.landLhsTrue71_step (calls := calls) rfl hp' hi' hi1' hread hbit74
  refine ⟨stateAt
    (NumFastStarts.landLhsTrue71Env (NumFastStarts.ifEnd68Env env
      (BitVec.ofNat 64 i1) ipv idigv (BitVec.ofNat 64 n)) a i1 bd)
    { s with pc := "if.then76", pre := some "land.lhs.true71" },
    rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, NumFastStarts.landLhsTrue71Env, NumFastStarts.ifEnd68Env,
      NumFastStarts.ifEnd68PhiEnv]
    block_lk
  · simp only [stateAt, NumFastStarts.landLhsTrue71Env, NumFastStarts.ifEnd68Env,
      NumFastStarts.ifEnd68PhiEnv]
    block_lk
  · simp only [stateAt, NumFastStarts.landLhsTrue71Env, NumFastStarts.ifEnd68Env,
      NumFastStarts.ifEnd68PhiEnv]
    block_lk
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1, runFuel_jump_prefix h2]

/-! ### Seam two: `land.lhs.true71`'s no-`.` edge to the merge's own test

`land.lhs.true71` is where the fraction dispatch begins and where a lexeme
without a fraction leaves.  Its no-`.` edge lands at `if.end144`, whose three
`phi`s read `land.lhs.true71`'s cells: the dispatch's two zeroes and `%i.5`.  The
block's own test then takes the marker's block when the index is still inside the
lexeme. -/

/-- The `if.end144` state the marker's block reads: the fraction's zeroes and the
stop index. -/
def nodotEnv (env : Env) (a i5 n : Nat) (bd : UInt8) : Env :=
  NumFastScanRun.ifEnd144Env (NumFastStarts.landLhsTrue71Env env a i5 bd) 0 0
    (BitVec.ofNat 64 i5) (BitVec.ofNat 64 n)

/-- **Seam two, the marker's block.**  A byte that is not `.` at an index inside
the lexeme leaves `land.lhs.true71` for `if.end144`, and that block's test takes
`land.lhs.true147` with `%i.10` at the stop index, the fraction's zeroes and the
length. -/
theorem nodot_seam {calls : Calls} {env : Env} {s : State} {a i5 n : Nat} {bd : UInt8}
    (hpc : s.pc = "land.lhs.true71")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hj : i5 < 2 ^ 63) (hlt : i5 < n) (hnlt : n < 2 ^ 63)
    (hread : readByte s.mem (a + i5) = some bd) (hne : bd ≠ 0x2E) :
    ∃ e : State, e.pc = "land.lhs.true147" ∧ e.pre = some "if.end144" ∧
      e.mem = s.mem ∧
      lookupName e.env "%i.10" = some (.int 64 (BitVec.ofNat 64 i5)) ∧
      lookupName e.env "%p" = some (.ptr a) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%fr.5" = some (.int 64 0) ∧
      lookupName e.env "%fdig.4" = some (.int 64 0) ∧
      ∀ k, runFuel calls (2 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hbit74 : evalICmp .eq (JsonScanLane.vByte bd) 0x2e#8 = 0 := by
    rw [NumFastStarts.eq_zero_iff]
    intro h
    exact hne (NumFastStarts.vByte_inj h)
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.landLhsTrue71Env env a i5 bd)
        { s with pc := "if.end144", pre := some "land.lhs.true71" }) :=
    NumFastStarts.landLhsTrue71_step_nodot (calls := calls) hpc hp hi5 hj hread hbit74
  have hi5' : lookupName (NumFastStarts.landLhsTrue71Env env a i5 bd) "%i.5"
      = some (.int 64 (BitVec.ofNat 64 i5)) := by
    simp only [NumFastStarts.landLhsTrue71Env]; block_lk
  have hn' : lookupName (NumFastStarts.landLhsTrue71Env env a i5 bd) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastStarts.landLhsTrue71Env]; block_lk
  have hden := NumFastScanRun.ifEnd144_denote_dot (calls := calls)
    (s := { s with pc := "if.end144", pre := some "land.lhs.true71" }) rfl hi5' hn'
  have hbit145 : evalICmp .ult (BitVec.ofNat 64 i5) (BitVec.ofNat 64 n) = 1 :=
    ult_ofNat_one hlt (by omega)
  have h2 : step calls numFastBody
      (stateAt (NumFastStarts.landLhsTrue71Env env a i5 bd)
        { s with pc := "if.end144", pre := some "land.lhs.true71" }) =
      .jump (stateAt (nodotEnv env a i5 n bd)
        { s with pc := "land.lhs.true147", pre := some "if.end144" }) :=
    NumFastScanRun.ifEnd144_step (calls := calls) rfl hden hbit145
  refine ⟨stateAt (nodotEnv env a i5 n bd)
    { s with pc := "land.lhs.true147", pre := some "if.end144" },
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, nodotEnv, NumFastScanRun.ifEnd144Env,
      NumFastScanRun.ifEnd144PhiEnv, NumFastStarts.landLhsTrue71Env]
    block_lk
  · simp only [stateAt, nodotEnv, NumFastScanRun.ifEnd144Env,
      NumFastScanRun.ifEnd144PhiEnv, NumFastStarts.landLhsTrue71Env]
    block_lk
  · simp only [stateAt, nodotEnv, NumFastScanRun.ifEnd144Env,
      NumFastScanRun.ifEnd144PhiEnv, NumFastStarts.landLhsTrue71Env]
    block_lk
  · simp only [stateAt, nodotEnv, NumFastScanRun.ifEnd144Env,
      NumFastScanRun.ifEnd144PhiEnv, NumFastStarts.landLhsTrue71Env]
    block_lk
  · simp only [stateAt, nodotEnv, NumFastScanRun.ifEnd144Env,
      NumFastScanRun.ifEnd144PhiEnv, NumFastStarts.landLhsTrue71Env]
    block_lk
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1, runFuel_jump_prefix h2]

/-! ### The register transport at the merge

Three blocks carry the digit run's accumulator to the merge's phis.
`land.lhs.true41.preheader` forms `%7` once, from the run's entry registers;
`if.end62` merges the accumulator on the digit head's two edges, increments the
count and the index, and tests the index against the length; and `if.end230`'s six
`phi`s read `if.end62`'s `%7` and `%ip.4`.  The three are the transport. -/

/-- `land.lhs.true41.preheader`, from its `findBlock` pin. -/
def preheaderInstrs : List Instr :=
  [Instr.binop "%6" (BinOp.add) 64 (Operand.reg "%idig.0560") (Operand.reg "%n"),
   Instr.binop "%7" (BinOp.sub) 64 (Operand.reg "%6") (Operand.reg "%i.1558")]

theorem findBlock_preheader : numFastBody.findBlock "land.lhs.true41.preheader" =
    some ⟨"land.lhs.true41.preheader", preheaderInstrs, Term.br "land.lhs.true41"⟩ := by
  simpa only [preheaderInstrs] using numFast_findBlock_land_lhs_true41_preheader

/-- The preheader's environment: the entry count plus the length, and the digit
count the pair difference names. -/
def preheaderEnv (env : Env) (idig i nv : BitVec 64) : Env :=
  ("%7", .int 64 ((idig + nv) - i)) :: ("%6", .int 64 (idig + nv)) :: env

/-- `land.lhs.true41.preheader`'s two instructions: `%6 = %idig.0560 + %n` and
`%7 = %6 - %i.1558`. -/
theorem preheader_denote {calls : Calls} {env : Env} {s : State}
    {idig i nv : BitVec 64}
    (hid : lookupName env "%idig.0560" = some (.int 64 idig))
    (hi : lookupName env "%i.1558" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls preheaderInstrs (stateAt env s) =
      some (stateAt (preheaderEnv env idig i nv) s) := by
  unfold preheaderInstrs
  block_eval

/-- The preheader's step: an unconditional branch to the digit head. -/
theorem preheader_step {calls : Calls} {env : Env} {s : State}
    {idig i nv : BitVec 64}
    (hpc : s.pc = "land.lhs.true41.preheader")
    (hid : lookupName env "%idig.0560" = some (.int 64 idig))
    (hi : lookupName env "%i.1558" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (preheaderEnv env idig i nv)
        { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }) := by
  refine numFast_step_at (s' := stateAt (preheaderEnv env idig i nv) s)
    (b := ⟨"land.lhs.true41.preheader", preheaderInstrs, Term.br "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, preheaderInstrs] using findBlock_preheader
  · simpa only [denoteCode_nil] using preheader_denote (calls := calls) hid hi hn
  · simp only [execTerm, stateAt, hpc]

/-- `%7`'s reading: the entry count plus the bytes from the entry index to the
length is the digit count, at the `Nat` readings and with the sum inside the
word. -/
theorem seven_tie {d0 i0 n : Nat} (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64) :
    BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0
      = BitVec.ofNat 64 (d0 + (n - i0)) := by
  rw [NumFastStarts.ofNat64_add_const hbn, BitVec.sub_eq_iff_eq_add, ← BitVec.ofNat_add]
  congr 1
  omega

/-- `if.end62`'s environment: the merged accumulator, the incremented count and
index, and the end-of-lexeme test. -/
def ifEnd62Env (env : Env) (ip idig i nv : BitVec 64) : Env :=
  ("%exitcond.not", .int 1 (evalICmp .eq (i + 0x1#64) nv)) ::
  ("%inc64", .int 64 (i + 0x1#64)) :: ("%inc63", .int 64 (idig + 0x1#64)) ::
  ("%ip.4", .int 64 ip) :: env

/-- `if.end62` from `while.body52`: the guard refused the fold, so the
accumulator is the head's own. -/
theorem ifEnd62_denote_back {calls : Calls} {env : Env} {s : State}
    {ip idig i nv : BitVec 64}
    (hpre : s.pre = some "while.body52")
    (hip : lookupName env "%ip.3573" = some (.int 64 ip))
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hi : lookupName env "%i.4575" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd62Instrs (stateAt env s) =
      some (stateAt (ifEnd62Env env ip idig i nv) s) := by
  unfold numFastIfEnd62Instrs
  block_eval

/-- `if.end62` from `if.then55`: the guard took the fold, so the accumulator is
`%add61`'s. -/
theorem ifEnd62_denote_then {calls : Calls} {env : Env} {s : State}
    {ip idig i nv : BitVec 64}
    (hpre : s.pre = some "if.then55")
    (hip : lookupName env "%add61" = some (.int 64 ip))
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hi : lookupName env "%i.4575" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd62Instrs (stateAt env s) =
      some (stateAt (ifEnd62Env env ip idig i nv) s) := by
  unfold numFastIfEnd62Instrs
  block_eval

/-- `if.end62`'s end-of-lexeme step: the incremented index is the length, so the
run leaves for the merge with the count and the accumulator. -/
theorem ifEnd62_step_end {calls : Calls} {env : Env} {s : State}
    {ip idig i nv : BitVec 64}
    (hpc : s.pc = "if.end62")
    (hden : denoteCode calls numFastIfEnd62Instrs (stateAt env s) =
      some (stateAt (ifEnd62Env env ip idig i nv) s))
    (hbit : evalICmp .eq (i + 0x1#64) nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd62Env env ip idig i nv)
        { s with pc := "if.end230", pre := some "if.end62" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd62Env env ip idig i nv) s)
    (b := ⟨"if.end62", numFastIfEnd62Instrs,
      Term.condbr (Operand.reg "%exitcond.not") "if.end230" "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd62Instrs] using numFast_findBlock_if_end62
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd62Env env ip idig i nv) "%exitcond.not"
        = some (.int 1 (evalICmp .eq (i + 0x1#64) nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%exitcond.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `if.end62`'s back edge: the incremented index is inside the length, so the
run re-enters the digit head carrying the incremented count and accumulator. -/
theorem ifEnd62_step_loop {calls : Calls} {env : Env} {s : State}
    {ip idig i nv : BitVec 64}
    (hpc : s.pc = "if.end62")
    (hden : denoteCode calls numFastIfEnd62Instrs (stateAt env s) =
      some (stateAt (ifEnd62Env env ip idig i nv) s))
    (hbit : evalICmp .eq (i + 0x1#64) nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd62Env env ip idig i nv)
        { s with pc := "land.lhs.true41", pre := some "if.end62" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd62Env env ip idig i nv) s)
    (b := ⟨"if.end62", numFastIfEnd62Instrs,
      Term.condbr (Operand.reg "%exitcond.not") "if.end230" "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd62Instrs] using numFast_findBlock_if_end62
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd62Env env ip idig i nv) "%exitcond.not"
        = some (.int 1 (evalICmp .eq (i + 0x1#64) nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%exitcond.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The transport, composed at the gate

`if.end230`'s six `phi`s read `if.end62`'s cells, and the gate's two tests are
what admits a lexeme inside the tier-1 window.  `intExit_gate` is that pair of
steps at the run's own exit registers, and `intRunExit_gate` reads the accumulator
off the exit predicate. -/

/-- **The transport at the merge.**  From the run's end-of-lexeme exit, the two
steps through `if.end230` hand `%ip.4` to `%ip.5708717729`, `%7` to
`%idig.4709716730`, and the dispatch's zeroes to the fraction's two cells; the
gate's tests admit a lexeme whose digit count is inside `20`. -/
theorem intExit_gate {calls : Calls} {env : Env} {s : State}
    {n i0 d0 : Nat} {ipv : BitVec 64}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end62")
    (h7 : lookupName env "%7" = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))))
    (hip : lookupName env "%ip.4" = some (.int 64 ipv))
    (hdig : d0 + (n - i0) < 20) :
    ∃ e : State, e.pc = "if.then241" ∧ e.pre = some "if.end230" ∧ e.mem = s.mem ∧
      lookupName e.env "%ip.5708717729" = some (.int 64 ipv) ∧
      lookupName e.env "%idig.4709716730"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
      lookupName e.env "%fr.5718728" = some (.int 64 0) ∧
      lookupName e.env "%fdig.4719727" = some (.int 64 0) ∧
      lookupName e.env "%exp10.4731" = some (.int 64 0) ∧
      ∀ k, runFuel calls (1 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hgate1 : evalICmp .ult (0 + BitVec.ofNat 64 (d0 + (n - i0))) (20#64) = 1 := by
    simpa using ult_ofNat_one (i := d0 + (n - i0)) (n := 20) hdig (by decide)
  have hgate2 : evalICmp .ult ((0 : BitVec 64) - 0 + (45#64)) (91#64) = 1 := by
    decide
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastTier1.t1GateEnv env 0
          (BitVec.ofNat 64 (d0 + (n - i0))) ipv 0 0)
        { s with pc := "if.then241", pre := some "if.end230" }) :=
    NumFastScanRun.ifEnd230_step_end62 (calls := calls) hpc hpre h7 hip ⟨hgate1, hgate2⟩
  refine ⟨stateAt (NumFastTier1.t1GateEnv env 0
    (BitVec.ofNat 64 (d0 + (n - i0))) ipv 0 0)
    { s with pc := "if.then241", pre := some "if.end230" },
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, NumFastTier1.t1GateEnv]; block_lk
  · simp only [stateAt, NumFastTier1.t1GateEnv]; block_lk
  · simp only [stateAt, NumFastTier1.t1GateEnv]; block_lk
  · simp only [stateAt, NumFastTier1.t1GateEnv]; block_lk
  · simp only [stateAt, NumFastTier1.t1GateEnv]; block_lk
  · intro k
    rw [runFuel_jump_prefix h1]

/-- **The run's own exit at the gate.**  The integer run's end-of-lexeme exit
carries `%inc64` and `%n` at the same value, so the merge's `%ip.5708717729` is
the run's folded accumulator and its `%idig.4709716730` is `%7`'s digit count —
the length's index, `d0 + (i1 - i0)`, whose `i1` the exit's own cell fixes as the
lexeme's end.  The two register ties are therefore one statement: the
accumulator the run carried through `if.end62` and the count `%7` computed at
`land.lhs.true41.preheader`. -/
theorem intRunExit_gate {bs : List UInt8} {i0 d0 n : Nat} {e : State}
    (hpc : e.pc = "if.end230") (hpre : e.pre = some "if.end62")
    (he : intRunExit bs i0 d0 e)
    (hn : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (h7 : lookupName e.env "%7"
      = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)))
    (hdig : d0 + (n - i0) < 20) :
    ∃ o : State, o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧ o.mem = e.mem ∧
      lookupName o.env "%ip.5708717729" = some (.int 64
        (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))) ∧
      lookupName o.env "%idig.4709716730"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
      lookupName o.env "%fr.5718728" = some (.int 64 0) ∧
      lookupName o.env "%fdig.4719727" = some (.int 64 0) ∧
      lookupName o.env "%exp10.4731" = some (.int 64 0) ∧
      ∀ k, runFuel s2HelperCalls (1 + k) numFastBody (stateAt e.env e) =
        runFuel s2HelperCalls k numFastBody o := by
  have hn64 : n < 2 ^ 64 := by omega
  rcases he with ⟨h68, _⟩ | ⟨h230, i1, hi1lt, hi1, hin, hid, hip⟩
  · rw [h68] at hpc; exact absurd hpc (by decide)
  -- the exit's own index is the length's
  have hi1n : i1 = n := by
    have h1 : (Value.int 64 (BitVec.ofNat 64 i1) : Value)
        = .int 64 (BitVec.ofNat 64 n) := by
      rw [hin] at hn
      exact Option.some.inj hn
    have h2 : BitVec.ofNat 64 i1 = BitVec.ofNat 64 n :=
      eq_of_heq (Value.int.inj h1).2
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi1lt,
      Nat.mod_eq_of_lt hn64] at h3
    exact h3
  have h7i : lookupName e.env "%7"
      = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0)))) := by
    have h := h7
    rw [seven_tie hi0 hbn] at h
    rw [← hi1n] at h
    exact h
  have hdigi : d0 + (i1 - i0) < 20 := by
    have h := hdig
    rw [← hi1n] at h
    exact h
  obtain ⟨o, hpc', hpre', hmem', hip', hid', hfr, hfd, hexp, hrun⟩ :=
    intExit_gate (calls := s2HelperCalls) (env := e.env) (s := e) (n := i1) (i0 := i0)
      (d0 := d0) hpc hpre h7i hip hdigi
  refine ⟨o, hpc', hpre', hmem', ?_, ?_, hfr, hfd, hexp, hrun⟩
  · rw [← hi1n]
    exact hip'
  · rw [← hi1n]
    exact hid'

/-! ### `num_d8_el1`'s agreement with the bytes at its pointer

The reader's model folds the eight bytes it is given; the digit runs fold the
lexeme.  `foldl_digits_add` is the fold's Hom property, `d8Value_eq_fold` reads
the model's right-fold as that left fold, and `numD8Answer_writes` is the answer
at the caller's local: one, and the word its load reads back. -/

/-- The digit fold is affine in its starting accumulator. -/
theorem foldl_digits_add (bs : List UInt8) (x : Nat) :
    bs.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) x =
      x * 10 ^ bs.length +
        bs.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 := by
  induction bs generalizing x with
  | nil => simp
  | cons b rest ih =>
      have hR : (b :: rest).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0
          = (b.toNat - 0x30) * 10 ^ rest.length +
            rest.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 := by
        rw [List.foldl_cons, Nat.zero_mul, Nat.zero_add, ih]
      have hL : (b :: rest).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) x
          = (x * 10 + (b.toNat - 0x30)) * 10 ^ rest.length +
            rest.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 := by
        rw [List.foldl_cons, ih]
      rw [hL, hR, List.length_cons, Nat.pow_succ, Nat.add_mul]
      rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ rest.length), Nat.add_assoc]

/-- A successful reading of one byte is the byte's difference from `'0'`. -/
theorem asciiDigit_some {b : UInt8} {d : Nat} (h : asciiDigit b = some d) :
    d = b.toNat - 0x30 := by
  unfold asciiDigit at h
  split at h
  · simp only [Option.some.injEq] at h
    omega
  · cases h

/-- **The reader's word is the digit runs' fold.**  A successful `d8Value` reads
the eight bytes as the fold base ten, which is the expression the runs carry. -/
theorem d8Value_eq_fold : ∀ (bs : List UInt8) {w : Nat}, d8Value bs = some w →
    w = bs.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0
  | [], w, h => by
      simp only [d8Value, Option.some.injEq] at h
      subst h
      rfl
  | b :: rest, w, h => by
      cases hb : asciiDigit b with
      | none => simp only [d8Value, hb] at h; cases h
      | some d =>
          cases hr : d8Value rest with
          | none => simp only [d8Value, hb, hr] at h; cases h
          | some v =>
              simp only [d8Value, hb, hr, Option.some.injEq] at h
              subst h
              rw [List.foldl_cons, Nat.zero_mul, Nat.zero_add, ← asciiDigit_some hb,
                foldl_digits_add rest d, d8Value_eq_fold rest hr]

/-- **The reader's answer at the caller's local.**  The success answer's memory is
the word written at `v`, read back at `v`; the `i32` load of that local is the
word the reader computed. -/
theorem numD8Answer_writes {p v w : Nat} {bs : List UInt8} {mem : Mem} {next : Nat}
    (hread : readBytes mem p 8 = some bs) (hval : d8Value bs = some w)
    (hw : w < 2 ^ 32) :
    numD8Answer [.ptr p, .ptr v] mem next =
      some { ret := .int 32 1, mem := writeBytes mem v (natToBytes w 4), next := next } ∧
    readBytes (writeBytes mem v (natToBytes w 4)) v 4 = some (natToBytes w 4) ∧
    loadValue (writeBytes mem v (natToBytes w 4)) (Ty.int 32) v
      = some (.int 32 (BitVec.ofNat 32 w)) := by
  have hback : readBytes (writeBytes mem v (natToBytes w 4)) v 4
      = some (natToBytes w 4) := by
    have h := readBytes_writeBytes_same mem (bs := natToBytes w 4) (addr := v)
    rw [natToBytes_length] at h
    exact h
  refine ⟨numD8Answer_read hread hval, hback, ?_⟩
  simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
    show (32 = 0) = False from by decide, ite_false, hback, natToBytes_toNat,
    Nat.mod_eq_of_lt (by simpa using hw)]

/-! ### The eight-digit fast path: the taken guard's entry

`if.then22`'s guard is `%cmp27564.not = (%add563 ugt %n)` with
`%add563 = %i.0 + 9`: refused it leaves for `while.end` with one digit consumed,
taken it enters `while.body.preheader`, whose `@num_d8_el1` call reads the eight
bytes after the lead digit into the local `%v8`.  Every composition in the tree
is on the refused branch; the two steps below are the taken one, at the
environment that answers the reader (`stage2NumFastCalls`).

The reader's answer decides the pair's own branches.  A success writes the word
and returns one, so `%tobool.not932 = 0` and the path continues at `cleanup`,
which folds the word; a refusal returns zero and continues at `cleanup.thread`,
which carries the preheader's cells to `while.end` with one digit consumed.  The
two lemmas are the preheader's own block, and `readBytes` at the pointer plus
`d8Value`'s fold are what the reader is given. -/

/-- The preheader's environment: the reader's return, its own test, and the
pointer the call was given. -/
def fpPreEnv (env : Env) (a : Nat) (idx : BitVec 64) (v8a : Nat)
    (call : BitVec 32) : Env :=
  ("%tobool.not932", .int 1 (evalICmp .eq call 0x0#32)) ::
  ("%call931", .int 32 call) ::
  ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env

/-- `while.body.preheader`'s chain at a successful reader: the marker, the
pointer arithmetic, the call's answer and its test. -/
theorem fpPreheader_denote_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    denoteCode (stage2NumFastCalls epow) numFastWhileBodyPreheaderInstrs (stateAt env s) =
      some (stateAt (fpPreEnv env a idx v8a 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }) := by
  unfold numFastWhileBodyPreheaderInstrs
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) hv8) (stage2NumFastCalls_lifetime epow _ _ _) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow) env _ "%add.ptr930" "%p" "%inc26"
    hp hi hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call931" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 1, mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%add.ptr930"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%v8"
          = some (.ptr v8a) :=
        lookupName_cons_tail (k := "%add.ptr930")
          (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_read hread hval)]
  rw [JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call931", .int 32 1) :: ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat))
      :: env)
    { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    "%tobool.not932" "%call931" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fpPreEnv]

/-- `while.body.preheader`'s chain at a refused reader: the answer is zero and
the memory is the walk's. -/
theorem fpPreheader_denote_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    denoteCode (stage2NumFastCalls epow) numFastWhileBodyPreheaderInstrs (stateAt env s) =
      some (stateAt (fpPreEnv env a idx v8a 0)
        { s with mem := s.mem, next := s.next }) := by
  unfold numFastWhileBodyPreheaderInstrs
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) hv8) (stage2NumFastCalls_lifetime epow _ _ _) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow) env _ "%add.ptr930" "%p" "%inc26"
    hp hi hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call931" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 0, mem := s.mem, next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%add.ptr930"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%v8"
          = some (.ptr v8a) :=
        lookupName_cons_tail (k := "%add.ptr930")
          (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_refuse hread hval)]
  rw [JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call931", .int 32 0) :: ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat))
      :: env)
    { s with mem := s.mem, next := s.next }
    "%tobool.not932" "%call931" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fpPreEnv]

/-- The preheader's step, taken: a success leaves for `cleanup` with the word
written into `%v8`'s local. -/
theorem fpPreheader_step {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPreEnv env a idx v8a 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next,
                 pc := "cleanup", pre := some "while.body.preheader" }) := by
  have hbit : evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32) = 0 := by decide
  refine numFast_step_at (s' := stateAt (fpPreEnv env a idx v8a 1)
      { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next })
    (b := ⟨"while.body.preheader", numFastWhileBodyPreheaderInstrs,
      Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBodyPreheaderInstrs] using
      numFast_findBlock_while_body_preheader_named
  · simpa only [denoteCode_nil] using
      fpPreheader_denote_ok (epow := epow) hp hi hv8 hpos hread hval hw
  · have hlk : lookupName (fpPreEnv env a idx v8a 1) "%tobool.not932"
        = some (.int 1 (evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_zero _ "%tobool.not932" "cleanup.thread" "cleanup" hlk rfl]
    simp only [stateAt, hpc]

/-- The preheader's step, refused: the reader's zero leaves for
`cleanup.thread` with the walk's memory. -/
theorem fpPreheader_step_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPreEnv env a idx v8a 0)
        { s with pc := "cleanup.thread", pre := some "while.body.preheader" }) := by
  have hbit : evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32) = 1 := by decide
  refine numFast_step_at (s' := stateAt (fpPreEnv env a idx v8a 0)
      { s with mem := s.mem, next := s.next })
    (b := ⟨"while.body.preheader", numFastWhileBodyPreheaderInstrs,
      Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBodyPreheaderInstrs] using
      numFast_findBlock_while_body_preheader_named
  · simpa only [denoteCode_nil] using
      fpPreheader_denote_refuse (epow := epow) hp hi hv8 hpos hread hval
  · have hlk : lookupName (fpPreEnv env a idx v8a 0) "%tobool.not932"
        = some (.int 1 (evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_one _ "%tobool.not932" "cleanup.thread" "cleanup" hlk rfl]
    simp only [stateAt, hpc]

/-- The fast path's count guard allows one group: `%idig.0560` enters at `1` and
grows by eight, so the loop's own `%idig < 12` admits a second group only at
`1 + 8 = 9`, and the third would be `17`. -/
theorem fastGuard_two_groups {k : Nat} (hk : 1 + 8 * k < 12) : k ≤ 1 := by omega

/-! ### The fast path's other two blocks on the refusal way

A refused reader leaves `while.body.preheader` for `cleanup.thread`, which moves
the preheader's own cells — the incremented index, the count `1` and the lead
digit's value — to `while.end`; `while.end` merges them and tests the index
against the length.  Those three blocks are the whole of the taken guard when the
reader refuses, and they end where the refused guard's own path ends: at the
digit head with one digit consumed and the index at `%i.0 + 1`.  Each block's
step is proved (`fpCleanupThread_step`, `fpWhileEnd_step_head`,
`fpWhileEnd_step_merge`); the three-step `runFuel` thread through them is the
`jump`-prefix composition `intExit_gate` demonstrates, not a separate statement
here. -/

/-- `cleanup.thread`'s three carried cells, in the order the `phi` run installs
them: the last `phi` first. -/
def fpCleanupThreadEnv (env : Env) (i idig ip : BitVec 64) : Env :=
  ("%ip.0565.lcssa", .int 64 ip) :: ("%idig.0566.lcssa", .int 64 idig) ::
  ("%i.1567.lcssa", .int 64 i) :: env

/-- The block from its `findBlock` pin. -/
def fpCleanupThreadInstrs : List Instr :=
  [Instr.phi "%i.1567.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%inc26")),
                                       ("while.body", (Operand.reg "%add568934"))],
   Instr.phi "%idig.0566.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("while.body", (Operand.reg "%add29569933"))],
   Instr.phi "%ip.0565.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%conv25")),
                                       ("while.body", (Operand.reg "%add35"))],
   Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))]]

theorem findBlock_fpCleanupThread :
    numFastBody.findBlock "cleanup.thread" =
      some ⟨"cleanup.thread", fpCleanupThreadInstrs, Term.br "while.end"⟩ := by
  simpa only [fpCleanupThreadInstrs] using numFast_findBlock_cleanup_thread

/-- The closing marker is answered too: `stage2Calls` reads both lifetime symbols
the same way. -/
theorem stage2NumFastCalls_lifetime_end (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "llvm.lifetime.end.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "num_d8_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "num_el_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "stk_mul_u64")),
    s2HelperCalls, JsonStage2IR.stage2Calls]

/-- `cleanup.thread` from the preheader: the index is the dispatch's, the count
is one, and the accumulator is the lead digit's value. -/
theorem fpCleanupThread_denote_pre {epow : Int → Option EPow} {env : Env} {s : State}
    {idx : BitVec 64} {ip : BitVec 64} {v8a : Nat}
    (hpre : s.pre = some "while.body.preheader")
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hip : lookupName env "%conv25" = some (.int 64 ip))
    (hv8 : lookupName env "%v8" = some (.ptr v8a)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupThreadInstrs (stateAt env s) =
      some (stateAt (fpCleanupThreadEnv env idx 1 ip) s) := by
  unfold fpCleanupThreadInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%inc26" _ hi
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 (1 : BitVec 64)
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%conv25" _ hip
  have hv8' : lookupName
      (runCells [("%i.1567.lcssa", .int 64 idx),
        ("%idig.0566.lcssa", .int 64 (1 : BitVec 64)),
        ("%ip.0565.lcssa", .int 64 ip)] env) "%v8" = some (.ptr v8a) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide : ("%ip.0565.lcssa" : String) ≠ "%v8"),
      lookupName_cons_ne _ _ (by decide : ("%idig.0566.lcssa" : String) ≠ "%v8"),
      lookupName_cons_ne _ _ (by decide : ("%i.1567.lcssa" : String) ≠ "%v8")]
    exact hv8
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
      (runCells [("%i.1567.lcssa", .int 64 idx), ("%idig.0566.lcssa", .int 64 (1 : BitVec 64)),
        ("%ip.0565.lcssa", .int 64 ip)] env) s
      "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8") hv8')
      (stage2NumFastCalls_lifetime_end epow _ _ _) []]
  simp only [denoteCode_nil, stateAt, fpCleanupThreadEnv, runCells]

/-- `cleanup.thread`'s step: an unconditional branch to `while.end`. -/
theorem fpCleanupThread_step {epow : Int → Option EPow} {env : Env} {s : State}
    {idx ip : BitVec 64} {v8a : Nat}
    (hpc : s.pc = "cleanup.thread")
    (hpre : s.pre = some "while.body.preheader")
    (hi : lookupName env "%inc26" = some (.int 64 idx))
    (hip : lookupName env "%conv25" = some (.int 64 ip))
    (hv8 : lookupName env "%v8" = some (.ptr v8a)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupThreadEnv env idx 1 ip)
        { s with pc := "while.end", pre := some "cleanup.thread" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupThreadEnv env idx 1 ip) s)
    (b := ⟨"cleanup.thread", fpCleanupThreadInstrs, Term.br "while.end"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupThreadInstrs] using findBlock_fpCleanupThread
  · simpa only [denoteCode_nil] using
      fpCleanupThread_denote_pre (epow := epow) hpre hi hip hv8
  · simp only [execTerm, stateAt, hpc]

/-- `while.end`'s environment: the run's three cells and the index's test. -/
def fpWhileEndEnv (env : Env) (i idig ip nv : BitVec 64) : Env :=
  ("%cmp39572", .int 1 (evalICmp .ult i nv)) ::
  ("%i.1558", .int 64 i) :: ("%idig.0560", .int 64 idig) ::
  ("%ip.0562", .int 64 ip) :: env

/-- `while.end`'s three `phi`s and its test, from the block's pin. -/
def fpWhileEndInstrs : List Instr :=
  [Instr.phi "%ip.0562" (Ty.int 64) [("cleanup.thread", (Operand.reg "%ip.0565.lcssa")),
                                       ("if.then22", (Operand.reg "%conv25")),
                                       ("cleanup", (Operand.reg "%add35"))],
   Instr.phi "%idig.0560" (Ty.int 64) [("cleanup.thread", (Operand.reg "%idig.0566.lcssa")),
                                       ("if.then22", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("cleanup", (Operand.reg "%add29569933"))],
   Instr.phi "%i.1558" (Ty.int 64) [("cleanup.thread", (Operand.reg "%i.1567.lcssa")),
                                       ("if.then22", (Operand.reg "%inc26")),
                                       ("cleanup", (Operand.reg "%add568934"))],
   Instr.icmp "%cmp39572" (IPred.ult) 64 (Operand.reg "%i.1558") (Operand.reg "%n")]

theorem findBlock_fpWhileEnd :
    numFastBody.findBlock "while.end" =
      some ⟨"while.end", fpWhileEndInstrs,
        Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68"⟩ := by
  simpa only [fpWhileEndInstrs] using numFast_findBlock_while_end

/-- `while.end` from `cleanup.thread`. -/
theorem fpWhileEnd_denote_thread {epow : Int → Option EPow} {env : Env} {s : State}
    {i idig ip nv : BitVec 64}
    (hpre : s.pre = some "cleanup.thread")
    (hi : lookupName env "%i.1567.lcssa" = some (.int 64 i))
    (hid : lookupName env "%idig.0566.lcssa" = some (.int 64 idig))
    (hip : lookupName env "%ip.0565.lcssa" = some (.int 64 ip))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpWhileEndInstrs (stateAt env s) =
      some (stateAt (fpWhileEndEnv env i idig ip nv) s) := by
  unfold fpWhileEndInstrs
  block_eval

/-- `while.end`'s step to the digit head: the index is inside the lexeme. -/
theorem fpWhileEnd_step_head {epow : Int → Option EPow} {env : Env} {s : State}
    {i idig ip nv : BitVec 64}
    (hpc : s.pc = "while.end")
    (hden : denoteCode (stage2NumFastCalls epow) fpWhileEndInstrs (stateAt env s) =
      some (stateAt (fpWhileEndEnv env i idig ip nv) s))
    (hbit : evalICmp .ult i nv = 1) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpWhileEndEnv env i idig ip nv)
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) := by
  refine numFast_step_at (s' := stateAt (fpWhileEndEnv env i idig ip nv) s)
    (b := ⟨"while.end", fpWhileEndInstrs,
      Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpWhileEndInstrs] using findBlock_fpWhileEnd
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpWhileEndEnv env i idig ip nv) "%cmp39572"
        = some (.int 1 (evalICmp .ult i nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp39572" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `while.end`'s step to the run's merge: the index has reached the length, so
there is no digit run. -/
theorem fpWhileEnd_step_merge {epow : Int → Option EPow} {env : Env} {s : State}
    {i idig ip nv : BitVec 64}
    (hpc : s.pc = "while.end")
    (hden : denoteCode (stage2NumFastCalls epow) fpWhileEndInstrs (stateAt env s) =
      some (stateAt (fpWhileEndEnv env i idig ip nv) s))
    (hbit : evalICmp .ult i nv = 0) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpWhileEndEnv env i idig ip nv)
        { s with pc := "if.end68", pre := some "while.end" }) := by
  refine numFast_step_at (s' := stateAt (fpWhileEndEnv env i idig ip nv) s)
    (b := ⟨"while.end", fpWhileEndInstrs,
      Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpWhileEndInstrs] using findBlock_fpWhileEnd
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpWhileEndEnv env i idig ip nv) "%cmp39572"
        = some (.int 1 (evalICmp .ult i nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp39572" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The fast path's fold: `cleanup` and the second group

The refusal way's blocks are above.  The taken way's are the loop: `cleanup`
folds the reader's word into the accumulator (`%mul = %ip * 10 ^ 8`, the `i32`
load of the local, the zero-extend, the sum), ends the marker, advances the index
by eight and tests the two guards; `while.body` is the second group's reader
call; and `while.end` reads whichever of `cleanup`, `cleanup.thread` and
`if.then22` left.

The guard's count test is immediate: `%idig.0560` enters at one and grows by
eight, so `%idig < 12` admits `1` and `9` and refuses `17`
(`fastGuard_two_groups`), which is why the loop is at most two groups.  The
reader's answer is the model's at the local: a success writes the word and
returns one, so `%4` reads back the word the reader computed
(`numD8Answer_writes`); a refusal returns zero and leaves for `cleanup.thread`
with the walk's memory. -/

/-- The lifetime marker's closing form at a named local: `llvm.lifetime.end`
leaves the state, since its answer is the identity. -/
theorem denoteCode_lifetimeEnd_fp (epow : Int → Option EPow) {env : Env} {s : State}
    {ptr : String} {v8a : Nat}
    (hv8 : lookupName env ptr = some (.ptr v8a)) (is : List Instr) :
    denoteCode (stage2NumFastCalls epow)
      (Instr.callVoid "llvm.lifetime.end.p0"
        [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
         (Ty.ptr, (Operand.reg ptr))] :: is) (stateAt env s) =
      denoteCode (stage2NumFastCalls epow) is (stateAt env s) := by
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg ptr))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := ptr) hv8)
      (stage2NumFastCalls_lifetime_end epow _ _ _) is]

/-- `cleanup`, from its `findBlock` pin. -/
def fpCleanupInstrs : List Instr :=
  [Instr.phi "%ip.0565935" (Ty.int 64) [("while.body", (Operand.reg "%add35")),
                                       ("while.body.preheader", (Operand.reg "%conv25"))],
   Instr.phi "%add568934" (Ty.int 64) [("while.body", (Operand.reg "%add")),
                                       ("while.body.preheader", (Operand.reg "%add563"))],
   Instr.phi "%add29569933" (Ty.int 64) [("while.body", (Operand.reg "%add29")),
                                       ("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000009#64)))],
   Instr.binop "%mul" (BinOp.mul) 64 (Operand.reg "%ip.0565935") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
   Instr.load "%4" (Ty.int 32) (Operand.reg "%v8"),
   Instr.zext "%conv34" 32 64 (Operand.reg "%4"),
   Instr.binop "%add35" (BinOp.add) 64 (Operand.reg "%mul") (Operand.reg "%conv34"),
   Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                        (Ty.ptr, (Operand.reg "%v8"))],
   Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%add568934") (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.icmp "%cmp27" (IPred.ule) 64 (Operand.reg "%add") (Operand.reg "%n"),
   Instr.icmp "%cmp30" (IPred.ult) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x000000000000000c#64)),
   Instr.select "%5" (Ty.int 1) (Operand.reg "%cmp27") (Operand.reg "%cmp30") (Operand.imm (Const.int 1 0x0#1))]

theorem findBlock_fpCleanup :
    numFastBody.findBlock "cleanup" =
      some ⟨"cleanup", fpCleanupInstrs,
        Term.condbr (Operand.reg "%5") "while.body" "while.end"⟩ := by
  simpa only [fpCleanupInstrs] using numFast_findBlock_cleanup

/-- The fold's guard: the two tests on the advanced index and the count, as
`%5`'s `select` binds them. -/
def fpGuard (add cnt nv : BitVec 64) : BitVec 1 :=
  if evalICmp .ule add nv = 1 then evalICmp .ult cnt (0xc#64) else (0x0#1)

/-- `cleanup`'s environment: the folded word, the advanced index, the two guards
and the three `phi` cells. -/
def fpCleanupEnv (env : Env) (ip add568 add295 nv : BitVec 64) (w : BitVec 32) : Env :=
  ("%5", .int 1 (fpGuard (add568 + 0x8#64) add295 nv)) ::
  ("%cmp30", .int 1 (evalICmp .ult add295 (0xc#64))) ::
  ("%cmp27", .int 1 (evalICmp .ule (add568 + 0x8#64) nv)) ::
  ("%add", .int 64 (add568 + 0x8#64)) ::
  ("%add35", .int 64 (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) ::
  ("%conv34", .int 64 (BitVec.ofNat 64 w.toNat)) ::
  ("%4", .int 32 w) ::
  ("%mul", .int 64 (ip * (0x5f5e100#64))) ::
  ("%add29569933", .int 64 add295) ::
  ("%add568934", .int 64 add568) ::
  ("%ip.0565935", .int 64 ip) :: env

/-- `cleanup` from the first group: the preheader's lead digit and index, the
reader's word, and the advanced count `9`. -/
theorem fpCleanup_denote_pre {epow : Int → Option EPow} {env : Env} {s : State}
    {ip add568 nv : BitVec 64} {v8a : Nat} {w : BitVec 32}
    (hpre : s.pre = some "while.body.preheader")
    (hip : lookupName env "%conv25" = some (.int 64 ip))
    (h568 : lookupName env "%add563" = some (.int 64 add568))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hread : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpCleanupEnv env ip add568 (0x0000000000000009#64) nv w) s) := by
  unfold fpCleanupInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%conv25" _ hip
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add563" _ h568
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 (0x0000000000000009#64)
  rw [denoteCode_mul_imm _ _ _ "%mul" "%ip.0565935" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 _ _ _ "%4" "%v8"
    (by block_lk) hread _]
  rw [denoteCode_zext _ _ _ "%conv34" "%4" 32 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add35" "%mul" "%conv34" (by block_lk) (by block_lk) _]
  rw [denoteCode_lifetimeEnd_fp epow (ptr := "%v8") (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%add" "%add568934" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp27" "%add" "%n"
    .ule 64 (by block_lk) (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp30"
    "%add29569933" .ult (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_select_bit_reg_imm_w _ _ _ "%5"
    "%cmp27" "%cmp30" 1 (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, fpCleanupEnv, fpGuard, runCells]

/-- `cleanup` from the second group: `while.body`'s cells on the same shape. -/
theorem fpCleanup_denote_body {epow : Int → Option EPow} {env : Env} {s : State}
    {ip add568 add295 nv : BitVec 64} {v8a : Nat} {w : BitVec 32}
    (hpre : s.pre = some "while.body")
    (hip : lookupName env "%add35" = some (.int 64 ip))
    (h568 : lookupName env "%add" = some (.int 64 add568))
    (h295 : lookupName env "%add29" = some (.int 64 add295))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hread : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpCleanupEnv env ip add568 add295 nv w) s) := by
  unfold fpCleanupInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add35" _ hip
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add" _ h568
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add29" _ h295
  rw [denoteCode_mul_imm _ _ _ "%mul" "%ip.0565935" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 _ _ _ "%4" "%v8"
    (by block_lk) hread _]
  rw [denoteCode_zext _ _ _ "%conv34" "%4" 32 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add35" "%mul" "%conv34" (by block_lk) (by block_lk) _]
  rw [denoteCode_lifetimeEnd_fp epow (ptr := "%v8") (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%add" "%add568934" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp27" "%add" "%n"
    .ule 64 (by block_lk) (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp30"
    "%add29569933" .ult (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_select_bit_reg_imm_w _ _ _ "%5"
    "%cmp27" "%cmp30" 1 (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, fpCleanupEnv, fpGuard, runCells]

/-- `cleanup`'s step into the second group: both guards passed. -/
theorem fpCleanup_step_body {epow : Int → Option EPow} {env : Env} {s : State}
    {ip add568 add295 nv : BitVec 64} {w : BitVec 32}
    (hpc : s.pc = "cleanup")
    (hden : denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpCleanupEnv env ip add568 add295 nv w) s))
    (hbit : fpGuard (add568 + 0x8#64) add295 nv = 1) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupEnv env ip add568 add295 nv w)
        { s with pc := "while.body", pre := some "cleanup" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupEnv env ip add568 add295 nv w) s)
    (b := ⟨"cleanup", fpCleanupInstrs,
      Term.condbr (Operand.reg "%5") "while.body" "while.end"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupInstrs] using findBlock_fpCleanup
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpCleanupEnv env ip add568 add295 nv w) "%5"
        = some (.int 1 (fpGuard (add568 + 0x8#64) add295 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%5" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `cleanup`'s step out of the loop: one guard failed. -/
theorem fpCleanup_step_end {epow : Int → Option EPow} {env : Env} {s : State}
    {ip add568 add295 nv : BitVec 64} {w : BitVec 32}
    (hpc : s.pc = "cleanup")
    (hden : denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpCleanupEnv env ip add568 add295 nv w) s))
    (hbit : fpGuard (add568 + 0x8#64) add295 nv = 0) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupEnv env ip add568 add295 nv w)
        { s with pc := "while.end", pre := some "cleanup" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupEnv env ip add568 add295 nv w) s)
    (b := ⟨"cleanup", fpCleanupInstrs,
      Term.condbr (Operand.reg "%5") "while.body" "while.end"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupInstrs] using findBlock_fpCleanup
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpCleanupEnv env ip add568 add295 nv w) "%5"
        = some (.int 1 (fpGuard (add568 + 0x8#64) add295 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%5" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `while.end` from `cleanup`: the folded accumulator, the advanced count and
the advanced index. -/
theorem fpWhileEnd_denote_cleanup {epow : Int → Option EPow} {env : Env} {s : State}
    {ipr idigr ir nv : BitVec 64}
    (hpre : s.pre = some "cleanup")
    (hip : lookupName env "%add35" = some (.int 64 ipr))
    (hid : lookupName env "%add29569933" = some (.int 64 idigr))
    (hi : lookupName env "%add568934" = some (.int 64 ir))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpWhileEndInstrs (stateAt env s) =
      some (stateAt (fpWhileEndEnv env ir idigr ipr nv) s) := by
  unfold fpWhileEndInstrs
  block_eval

/-- `while.body`'s instructions, from its pin: the second group's `%add29`, the
marker's opening, the pointer and the reader call. -/
def fpBodyInstrs : List Instr :=
  [Instr.binop "%add29" (BinOp.add) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                        (Ty.ptr, (Operand.reg "%v8"))],
   Instr.gep "%add.ptr" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add568934"),
   Instr.call "%call" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr")),
                        (Ty.ptr, (Operand.reg "%v8"))],
   Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%call") (Operand.imm (Const.int 32 0x00000000#32))]

theorem findBlock_fpBody :
    numFastBody.findBlock "while.body" =
      some ⟨"while.body", fpBodyInstrs,
        Term.condbr (Operand.reg "%tobool.not") "cleanup.thread" "cleanup"⟩ := by
  simpa only [fpBodyInstrs] using numFast_findBlock_while_body

/-- `while.body`'s environment: the advanced count, the pointer, the reader's
answer and its test. -/
def fpBodyEnv (env : Env) (a v8a : Nat) (idx add295 : BitVec 64)
    (call : BitVec 32) : Env :=
  ("%tobool.not", .int 1 (evalICmp .eq call (0x0#32))) ::
  ("%call", .int 32 call) ::
  ("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
  ("%add29", .int 64 (add295 + 0x8#64)) :: env

/-- `while.body` at a successful reader: the count advances, the pointer is the
index's, the word lands in `%v8`'s local and the test is zero. -/
theorem fpBody_denote_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx add295 : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add568934" = some (.int 64 idx))
    (hcnt : lookupName env "%add29569933" = some (.int 64 add295))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    denoteCode (stage2NumFastCalls epow) fpBodyInstrs (stateAt env s) =
      some (stateAt (fpBodyEnv env a v8a idx add295 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }) := by
  unfold fpBodyInstrs
  rw [denoteCode_add_imm (stage2NumFastCalls epow) env s "%add29" "%add29569933"
    (by block_lk) _]
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
    (("%add29", .int 64 (add295 + 0x8#64)) :: env) s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8") (by block_lk))
    (stage2NumFastCalls_lifetime_end epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow)
    (("%add29", .int 64 (add295 + 0x8#64)) :: env) _ "%add.ptr" "%p" "%add568934"
    (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add29", .int 64 (add295 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr")), (Ty.ptr, (Operand.reg "%v8"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 1, mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add29", .int 64 (add295 + 0x8#64)) :: env) "%add.ptr"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add29", .int 64 (add295 + 0x8#64)) :: env) "%v8"
          = some (.ptr v8a) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_read hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call", .int 32 1) :: ("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add29", .int 64 (add295 + 0x8#64)) :: env)
    { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    "%tobool.not" "%call" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode_nil, stateAt, fpBodyEnv]

/-- `while.body` at a refused reader: the count advances and the memory is the
walk's. -/
theorem fpBody_denote_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx add295 : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add568934" = some (.int 64 idx))
    (hcnt : lookupName env "%add29569933" = some (.int 64 add295))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    denoteCode (stage2NumFastCalls epow) fpBodyInstrs (stateAt env s) =
      some (stateAt (fpBodyEnv env a v8a idx add295 0)
        { s with mem := s.mem, next := s.next }) := by
  unfold fpBodyInstrs
  rw [denoteCode_add_imm (stage2NumFastCalls epow) env s "%add29" "%add29569933"
    (by block_lk) _]
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
    (("%add29", .int 64 (add295 + 0x8#64)) :: env) s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8") (by block_lk))
    (stage2NumFastCalls_lifetime_end epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow)
    (("%add29", .int 64 (add295 + 0x8#64)) :: env) _ "%add.ptr" "%p" "%add568934"
    (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add29", .int 64 (add295 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr")), (Ty.ptr, (Operand.reg "%v8"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 0, mem := s.mem, next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add29", .int 64 (add295 + 0x8#64)) :: env) "%add.ptr"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add29", .int 64 (add295 + 0x8#64)) :: env) "%v8"
          = some (.ptr v8a) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_refuse hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call", .int 32 0) :: ("%add.ptr", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add29", .int 64 (add295 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%tobool.not" "%call" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode_nil, stateAt, fpBodyEnv]

/-- `while.body`'s step at a successful reader: the fold's block. -/
theorem fpBody_step_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx add295 : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body")
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add568934" = some (.int 64 idx))
    (hcnt : lookupName env "%add29569933" = some (.int 64 add295))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpBodyEnv env a v8a idx add295 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next,
                 pc := "cleanup", pre := some "while.body" }) := by
  have hbit : evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32) = 0 := by decide
  refine numFast_step_at (s' := stateAt (fpBodyEnv env a v8a idx add295 1)
      { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next })
    (b := ⟨"while.body", fpBodyInstrs,
      Term.condbr (Operand.reg "%tobool.not") "cleanup.thread" "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBodyInstrs] using findBlock_fpBody
  · simpa only [denoteCode_nil] using
      fpBody_denote_ok (epow := epow) hp hidx hcnt hv8 hpos hread hval hw
  · have hlk : lookupName (fpBodyEnv env a v8a idx add295 1) "%tobool.not"
        = some (.int 1 (evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_zero _ "%tobool.not" "cleanup.thread" "cleanup" hlk rfl]
    simp only [stateAt, hpc]

/-- `while.body`'s step at a refused reader: `cleanup.thread`. -/
theorem fpBody_step_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx add295 : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body")
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add568934" = some (.int 64 idx))
    (hcnt : lookupName env "%add29569933" = some (.int 64 add295))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpBodyEnv env a v8a idx add295 0)
        { s with pc := "cleanup.thread", pre := some "while.body" }) := by
  have hbit : evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32) = 1 := by decide
  refine numFast_step_at (s' := stateAt (fpBodyEnv env a v8a idx add295 0)
      { s with mem := s.mem, next := s.next })
    (b := ⟨"while.body", fpBodyInstrs,
      Term.condbr (Operand.reg "%tobool.not") "cleanup.thread" "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBodyInstrs] using findBlock_fpBody
  · simpa only [denoteCode_nil] using
      fpBody_denote_refuse (epow := epow) hp hidx hcnt hv8 hpos hread hval
  · have hlk : lookupName (fpBodyEnv env a v8a idx add295 0) "%tobool.not"
        = some (.int 1 (evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_one _ "%tobool.not" "cleanup.thread" "cleanup" hlk rfl]
    simp only [stateAt, hpc]

/-! ### The fast path's accumulator at the loop's exit

`d8Value_eq_fold` reads the reader's word as its eight bytes' fold.  The fast
path consumes the integer part's lead digit and then one or two groups, so the
accumulator `while.end` merges is `digitFold` over the digits from the lead:
`%add35 = %ip * 10 ^ 8 + %4` per group, and the splitting lemma composes the
lead with a group.  The two ties below are that composition at the window's
nine and seventeen digits, and `fpSecondFold` is the second group's own
accumulation of the nine the first took.

The refusal way's last block is the second group's: `while.body`'s failed read
leaves `cleanup.thread`, whose phis take `while.body`'s own cells — the
incremented index, the count nine and the first group's folded word, none of
which the failed read touched.  `fpCleanupThread_denote_body` and
`fpCleanupThread_step_body` are that edge. -/

/-- The digit fold splits at a prefix: the first `k` digits, then the next `m`. -/
theorem digitFold_split {bs : List UInt8} {start k m : Nat}
    (hlen : start + k + m ≤ bs.length) :
    digitFold bs start (k + m)
      = digitFold bs start k * 10 ^ m + digitFold bs (start + k) m := by
  unfold digitFold
  rw [List.take_add, List.drop_drop, List.foldl_append, foldl_digits_add]
  have hlen' : ((bs.drop (start + k)).take m).length = m := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  rw [hlen']

/-- A prefix read at the same address is the longer read's prefix: the memory is
a function of the address. -/
theorem readBytes_take_le {m : Mem} {a n k : Nat} {bs bs' : List UInt8}
    (hk : k ≤ n) (h : readBytes m a k = some bs) (h' : readBytes m a n = some bs') :
    bs'.take k = bs := by
  obtain ⟨i, rfl⟩ := Nat.le.dest hk
  obtain ⟨h1, -⟩ := readBytes_split m a k i h'
  rw [h1] at h
  exact Option.some.inj h

/-- **The reader's word is the lexeme's fold.**  A successful `d8Value` of the
eight bytes at `a + start` is `digitFold bs start 8` at the lexeme `bs` the walk
reads from `a`. -/
theorem d8Value_slice {m : Mem} {a n start : Nat} {bs bs8 : List UInt8} {w : Nat}
    (hread : readBytes m a n = some bs)
    (hslice : readBytes m (a + start) 8 = some bs8)
    (hstart : start + 8 ≤ n) (hval : d8Value bs8 = some w) :
    w = digitFold bs start 8 := by
  have hk : start ≤ n := by omega
  obtain ⟨-, hdrop⟩ := readBytes_split m a start (n - start) (by
    rw [Nat.add_sub_cancel' hk]; exact hread)
  obtain ⟨h8, -⟩ := readBytes_split m (a + start) 8 ((n - start) - 8) (by
    rw [show 8 + ((n - start) - 8) = n - start from by omega]; exact hdrop)
  have htake : (bs.drop start).take 8 = bs8 := by
    rw [h8] at hslice
    exact Option.some.inj hslice
  rw [digitFold, htake, ← d8Value_eq_fold bs8 hval]

/-- A one-digit fold is the byte's difference from `'0'`. -/
theorem digitFold_one {bs : List UInt8} {start : Nat} {b : UInt8}
    (hlen : start < bs.length) (hb : bs.getD start 0 = b) :
    digitFold bs start 1 = b.toNat - 0x30 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, digitFold_succ hlen, Nat.add_zero,
    digitFold_zero, Nat.zero_mul, Nat.zero_add, hb]

/-- **The first group's accumulator.**  The lead digit's value and the reader's
eight bytes are the nine digits from `start`. -/
theorem fpFirstFold {bs bs8 : List UInt8} {m : Mem} {a start n lead w : Nat}
    (hread : readBytes m a n = some bs)
    (hlead : lead = digitFold bs start 1)
    (hslice : readBytes m (a + (start + 1)) 8 = some bs8)
    (hstart : start + 9 ≤ n) (hval : d8Value bs8 = some w) :
    BitVec.ofNat 64 lead * 0x5f5e100#64 + BitVec.ofNat 64 w
      = BitVec.ofNat 64 (digitFold bs start 9) := by
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length m a n hread
  have hw : w = digitFold bs (start + 1) 8 :=
    d8Value_slice hread hslice (by omega) hval
  have hsplit : digitFold bs start 9
      = digitFold bs start 1 * 10 ^ 8 + digitFold bs (start + 1) 8 := by
    have := digitFold_split (bs := bs) (start := start) (k := 1) (m := 8) (by omega)
    simpa only [show (1 : Nat) + 8 = 9 from rfl] using this
  rw [hsplit, hlead, hw,
    show (0x5f5e100#64) = BitVec.ofNat 64 (10 ^ 8) from by decide,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]

/-- **The second group's accumulator.**  The nine digits the first group took and
the second reader's eight bytes are the seventeen digits from `start`. -/
theorem fpSecondFold {bs bs8 : List UInt8} {m : Mem} {a start n w2 : Nat}
    (hread : readBytes m a n = some bs)
    (hslice : readBytes m (a + (start + 9)) 8 = some bs8)
    (hstart : start + 17 ≤ n) (hval : d8Value bs8 = some w2) :
    BitVec.ofNat 64 (digitFold bs start 9) * 0x5f5e100#64 + BitVec.ofNat 64 w2
      = BitVec.ofNat 64 (digitFold bs start 17) := by
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length m a n hread
  have hw : w2 = digitFold bs (start + 9) 8 :=
    d8Value_slice hread hslice (by omega) hval
  have hsplit : digitFold bs start 17
      = digitFold bs start 9 * 10 ^ 8 + digitFold bs (start + 9) 8 := by
    have := digitFold_split (bs := bs) (start := start) (k := 9) (m := 8) (by omega)
    simpa only [show (9 : Nat) + 8 = 17 from rfl] using this
  rw [hsplit, hw,
    show (0x5f5e100#64) = BitVec.ofNat 64 (10 ^ 8) from by decide,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]

/-- The loop's count guard at its second group: `%idig.0560` has reached
`9 + 8`, so `%idig < 12` is refused and the guard is zero whatever the index
test is. -/
theorem fpGuard_second_group (add nv : BitVec 64) :
    fpGuard add (0x9#64 + 0x8#64) nv = 0 := by
  unfold fpGuard
  rw [show evalICmp .ult (0x9#64 + 0x8#64) (0xc#64) = 0 from by decide]
  split <;> rfl

/-- `cleanup.thread` from the second group's refusal: the index, the count and
the accumulator are `while.body`'s cells, unchanged by the failed read. -/
theorem fpCleanupThread_denote_body {epow : Int → Option EPow} {env : Env} {s : State}
    {i d ip : BitVec 64} {v8a : Nat}
    (hpre : s.pre = some "while.body")
    (hi : lookupName env "%add568934" = some (.int 64 i))
    (hd : lookupName env "%add29569933" = some (.int 64 d))
    (hip : lookupName env "%add35" = some (.int 64 ip))
    (hv8 : lookupName env "%v8" = some (.ptr v8a)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupThreadInstrs (stateAt env s) =
      some (stateAt (fpCleanupThreadEnv env i d ip) s) := by
  unfold fpCleanupThreadInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add568934" _ hi
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add29569933" _ hd
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add35" _ hip
  have hv8' : lookupName
      (runCells [("%i.1567.lcssa", .int 64 i), ("%idig.0566.lcssa", .int 64 d),
        ("%ip.0565.lcssa", .int 64 ip)] env) "%v8" = some (.ptr v8a) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide : ("%ip.0565.lcssa" : String) ≠ "%v8"),
      lookupName_cons_ne _ _ (by decide : ("%idig.0566.lcssa" : String) ≠ "%v8"),
      lookupName_cons_ne _ _ (by decide : ("%i.1567.lcssa" : String) ≠ "%v8")]
    exact hv8
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
      (runCells [("%i.1567.lcssa", .int 64 i), ("%idig.0566.lcssa", .int 64 d),
        ("%ip.0565.lcssa", .int 64 ip)] env) s
      "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8") hv8')
      (stage2NumFastCalls_lifetime_end epow _ _ _) []]
  simp only [denoteCode_nil, stateAt, fpCleanupThreadEnv, runCells]

/-- `cleanup.thread`'s step from the second group: an unconditional branch to
`while.end`. -/
theorem fpCleanupThread_step_body {epow : Int → Option EPow} {env : Env} {s : State}
    {i d ip : BitVec 64} {v8a : Nat}
    (hpc : s.pc = "cleanup.thread")
    (hpre : s.pre = some "while.body")
    (hi : lookupName env "%add568934" = some (.int 64 i))
    (hd : lookupName env "%add29569933" = some (.int 64 d))
    (hip : lookupName env "%add35" = some (.int 64 ip))
    (hv8 : lookupName env "%v8" = some (.ptr v8a)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupThreadEnv env i d ip)
        { s with pc := "while.end", pre := some "cleanup.thread" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupThreadEnv env i d ip) s)
    (b := ⟨"cleanup.thread", fpCleanupThreadInstrs, Term.br "while.end"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupThreadInstrs] using findBlock_fpCleanupThread
  · simpa only [denoteCode_nil] using
      fpCleanupThread_denote_body (epow := epow) hpre hi hd hip hv8
  · simp only [execTerm, stateAt, hpc]

/-! ### The fast path's run: the first fold, the second group, and `while.end`

The loop's blocks are chained above; this is their composition.  From the first
`cleanup` at a taken count guard, `while.body` reads the next eight digits and
the second `cleanup` folds them; its own count guard is then refused
(`fpGuard_second_group`, since `%idig` has reached `9 + 8`), so `while.end`
merges the second fold with the count seventeen and the advanced index.  On the
other reader answer the second group's failed call leaves for `cleanup.thread`,
whose three carried cells are the first fold's, and `while.end` merges those with
the count nine.  The two `runFuel` threads below are the loop's last two groups;
they are what the taken guard's entry into `intRunInv` composes. -/

/-- The first fold's environment: `cleanup`'s cells over the preheader's. -/
def fpFirstEnv (env : Env) (ip add568 nv : BitVec 64) (w : BitVec 32) : Env :=
  fpCleanupEnv env ip add568 (0x9#64) nv w

/-- The second reader's environment: `while.body`'s cells over the first fold's. -/
def fpBodyEnv2 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64) (w : BitVec 32) : Env :=
  fpBodyEnv (fpFirstEnv env ip add568 nv w) a v8a add568 (0x9#64) 1

/-- The second reader's refusal environment. -/
def fpBodyEnv2r (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64) (w : BitVec 32) : Env :=
  fpBodyEnv (fpFirstEnv env ip add568 nv w) a v8a add568 (0x9#64) 0

/-- The second fold's environment: the loop's exit on the success way. -/
def fpSecondEnv (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64) (w : BitVec 32)
    (w2 : Nat) : Env :=
  fpCleanupEnv (fpBodyEnv2 env a v8a ip add568 nv w)
    (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat) (add568 + 0x8#64)
    ((0x9#64) + 0x8#64) nv (BitVec.ofNat 32 w2)

/-- The refusal's `cleanup.thread` environment: the loop's exit on the failed
second read. -/
def fpSecondThreadEnv (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) : Env :=
  fpCleanupThreadEnv (fpBodyEnv2r env a v8a ip add568 nv w) add568 (0x9#64)
    (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)

/-! ### The nested environments' cells

The two folds stack three builders, so a cell read through the stack is a chain
of `lookupName` peels.  The readings are hoisted here, one per cell and one per
carried name, so each block step's hypotheses are small terms and the loop's
composition does not carry the whole stack in its proof term. -/

theorem fpFirstEnv_p {env : Env} {ip add568 nv : BitVec 64} {w : BitVec 32} {a : Nat}
    (h : lookupName env "%p" = some (.ptr a)) :
    lookupName (fpFirstEnv env ip add568 nv w) "%p" = some (.ptr a) := by
  simp only [fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpFirstEnv_add568934 (env : Env) (ip add568 nv : BitVec 64) (w : BitVec 32) :
    lookupName (fpFirstEnv env ip add568 nv w) "%add568934"
      = some (.int 64 add568) := by
  simp only [fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpFirstEnv_add29569933 (env : Env) (ip add568 nv : BitVec 64) (w : BitVec 32) :
    lookupName (fpFirstEnv env ip add568 nv w) "%add29569933"
      = some (.int 64 (0x9#64)) := by
  simp only [fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpFirstEnv_v8 {env : Env} {ip add568 nv : BitVec 64} {w : BitVec 32} {v8a : Nat}
    (h : lookupName env "%v8" = some (.ptr v8a)) :
    lookupName (fpFirstEnv env ip add568 nv w) "%v8" = some (.ptr v8a) := by
  simp only [fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2_add35 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add35"
      = some (.int 64 (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) := by
  simp only [fpBodyEnv2, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2_add (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add"
      = some (.int 64 (add568 + 0x8#64)) := by
  simp only [fpBodyEnv2, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2_add29 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add29"
      = some (.int 64 ((0x9#64) + 0x8#64)) := by
  simp only [fpBodyEnv2, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2_v8 {env : Env} {a v8a : Nat} {ip add568 nv : BitVec 64}
    {w : BitVec 32}
    (h : lookupName env "%v8" = some (.ptr v8a)) :
    lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%v8" = some (.ptr v8a) := by
  simp only [fpBodyEnv2, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2_n {env : Env} {a v8a : Nat} {ip add568 nv : BitVec 64}
    {w : BitVec 32}
    (h : lookupName env "%n" = some (.int 64 nv)) :
    lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%n" = some (.int 64 nv) := by
  simp only [fpBodyEnv2, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2r_add35 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add35"
      = some (.int 64 (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) := by
  simp only [fpBodyEnv2r, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2r_add568934 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add568934"
      = some (.int 64 add568) := by
  simp only [fpBodyEnv2r, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2r_add29569933 (env : Env) (a v8a : Nat) (ip add568 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add29569933"
      = some (.int 64 (0x9#64)) := by
  simp only [fpBodyEnv2r, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

theorem fpBodyEnv2r_v8 {env : Env} {a v8a : Nat} {ip add568 nv : BitVec 64}
    {w : BitVec 32}
    (h : lookupName env "%v8" = some (.ptr v8a)) :
    lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%v8" = some (.ptr v8a) := by
  simp only [fpBodyEnv2r, fpBodyEnv, fpFirstEnv, fpCleanupEnv]; block_lk

/-- **The second group folds into the loop's exit.**  From the first `cleanup`
at a taken count guard, three control steps: the second group's reader call, its
fold at the second `cleanup`, and that cleanup's refused count guard.  The exit
is `while.end` with `%add35` the seventeen digits' fold, `%add29569933` the count
seventeen and `%add568934` the index advanced by sixteen. -/
theorem fpFastSecond_run {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {ip add568 nv : BitVec 64} {w : BitVec 32} {w2 : Nat}
    {bs8 : List UInt8}
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hip : lookupName env "%conv25" = some (.int 64 ip))
    (h568 : lookupName env "%add563" = some (.int 64 add568))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hread1 : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hbit1 : fpGuard (add568 + 0x8#64) (0x9#64) nv = 1)
    (hpos : (add568.signExtend 64).toNat < 2 ^ 63)
    (hread2 : readBytes s.mem (a + (add568.signExtend 64).toNat) 8 = some bs8)
    (hval2 : d8Value bs8 = some w2) (hw2 : w2 < 2 ^ 32) :
    ∃ e : State, e.pc = "while.end" ∧ e.pre = some "cleanup" ∧
      e.mem = writeBytes s.mem v8a (natToBytes w2 4) ∧
      e.env = fpSecondEnv env a v8a ip add568 nv w w2 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hden1 : denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpFirstEnv env ip add568 nv w) s) :=
    fpCleanup_denote_pre (epow := epow) hpre hip h568 hv8 hread1 hn
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpFirstEnv env ip add568 nv w)
        { s with pc := "while.body", pre := some "cleanup" }) :=
    fpCleanup_step_body (epow := epow) hpc hden1 hbit1
  have hp1 : lookupName (fpFirstEnv env ip add568 nv w) "%p"
      = some (.ptr a) := fpFirstEnv_p hp
  have h568_1 : lookupName (fpFirstEnv env ip add568 nv w) "%add568934"
      = some (.int 64 add568) := fpFirstEnv_add568934 env ip add568 nv w
  have h295_1 : lookupName (fpFirstEnv env ip add568 nv w) "%add29569933"
      = some (.int 64 (0x9#64)) := fpFirstEnv_add29569933 env ip add568 nv w
  have hv8_1 : lookupName (fpFirstEnv env ip add568 nv w) "%v8"
      = some (.ptr v8a) := fpFirstEnv_v8 hv8
  have hread2' : readBytes (stateAt (fpFirstEnv env ip add568 nv w)
      { s with pc := "while.body", pre := some "cleanup" }).mem
      (a + (add568.signExtend 64).toNat) 8 = some bs8 := by
    simpa only [fpFirstEnv, fpCleanupEnv, stateAt] using hread2
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpFirstEnv env ip add568 nv w)
        { s with pc := "while.body", pre := some "cleanup" }) =
      .jump (stateAt (fpBodyEnv2 env a v8a ip add568 nv w)
        { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
                 pc := "cleanup", pre := some "while.body" }) :=
    fpBody_step_ok (epow := epow) (env := fpFirstEnv env ip add568 nv w)
      (s := { s with pc := "while.body", pre := some "cleanup" })
      rfl hp1 h568_1 h295_1 hv8_1 hpos hread2' hval2 hw2
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w2 4)) v8a 4
      = some (natToBytes w2 4) :=
    (numD8Answer_writes (p := a + (add568.signExtend 64).toNat) (v := v8a)
      (w := w2) (bs := bs8) (mem := s.mem) (next := s.next)
      hread2 hval2 hw2).2.1
  have h35_2 : lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add35"
      = some (.int 64 (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) :=
    fpBodyEnv2_add35 env a v8a ip add568 nv w
  have hadd_2 : lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add"
      = some (.int 64 (add568 + 0x8#64)) :=
    fpBodyEnv2_add env a v8a ip add568 nv w
  have h29_2 : lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%add29"
      = some (.int 64 ((0x9#64) + 0x8#64)) :=
    fpBodyEnv2_add29 env a v8a ip add568 nv w
  have hv8_2 : lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%v8"
      = some (.ptr v8a) := fpBodyEnv2_v8 hv8
  have hn_2 : lookupName (fpBodyEnv2 env a v8a ip add568 nv w) "%n"
      = some (.int 64 nv) := fpBodyEnv2_n hn
  have hwx : (BitVec.ofNat 32 w2).toNat = w2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  have hread3 : readBytes (stateAt (fpBodyEnv2 env a v8a ip add568 nv w)
      { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
               pc := "cleanup", pre := some "while.body" }).mem v8a 4
      = some (natToBytes (BitVec.ofNat 32 w2).toNat 4) := by
    rw [hwx]
    simpa only [fpBodyEnv2, stateAt] using hback
  have hden3 := fpCleanup_denote_body (epow := epow)
    (env := fpBodyEnv2 env a v8a ip add568 nv w)
    (s := { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
                    pc := "cleanup", pre := some "while.body" })
    (w := BitVec.ofNat 32 w2)
    rfl h35_2 hadd_2 h29_2 hv8_2 hread3 hn_2
  have hbit2 : fpGuard ((add568 + 0x8#64) + 0x8#64) ((0x9#64) + 0x8#64) nv = 0 :=
    fpGuard_second_group ((add568 + 0x8#64) + 0x8#64) nv
  have hstep3 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpBodyEnv2 env a v8a ip add568 nv w)
        { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
                 pc := "cleanup", pre := some "while.body" }) =
      .jump (stateAt (fpSecondEnv env a v8a ip add568 nv w w2)
        { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
                 pc := "while.end", pre := some "cleanup" }) :=
    fpCleanup_step_end (epow := epow) rfl hden3 hbit2
  refine ⟨stateAt (fpSecondEnv env a v8a ip add568 nv w w2)
    { s with mem := writeBytes s.mem v8a (natToBytes w2 4), next := s.next,
             pc := "while.end", pre := some "cleanup" }, rfl, rfl, rfl, rfl, ?_⟩
  intro k
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2,
    runFuel_jump_prefix hstep3]

/-- **The second group's failed read.**  From the first `cleanup` at a taken
count guard, the second reader's refusal leaves the first fold's cells
untouched: `while.body` jumps to `cleanup.thread`, whose phis carry the index,
the count nine and the first fold to `while.end`. -/
theorem fpFastSecond_run_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {ip add568 nv : BitVec 64} {w : BitVec 32} {bs8 : List UInt8}
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hip : lookupName env "%conv25" = some (.int 64 ip))
    (h568 : lookupName env "%add563" = some (.int 64 add568))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hread1 : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hbit1 : fpGuard (add568 + 0x8#64) (0x9#64) nv = 1)
    (hpos : (add568.signExtend 64).toNat < 2 ^ 63)
    (hread2 : readBytes s.mem (a + (add568.signExtend 64).toNat) 8 = some bs8)
    (hval2 : d8Value bs8 = none) :
    ∃ e : State, e.pc = "while.end" ∧ e.pre = some "cleanup.thread" ∧
      e.mem = s.mem ∧
      e.env = fpSecondThreadEnv env a v8a ip add568 nv w ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (3 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hden1 : denoteCode (stage2NumFastCalls epow) fpCleanupInstrs (stateAt env s) =
      some (stateAt (fpFirstEnv env ip add568 nv w) s) :=
    fpCleanup_denote_pre (epow := epow) hpre hip h568 hv8 hread1 hn
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpFirstEnv env ip add568 nv w)
        { s with pc := "while.body", pre := some "cleanup" }) :=
    fpCleanup_step_body (epow := epow) hpc hden1 hbit1
  have hp1 : lookupName (fpFirstEnv env ip add568 nv w) "%p"
      = some (.ptr a) := fpFirstEnv_p hp
  have h568_1 : lookupName (fpFirstEnv env ip add568 nv w) "%add568934"
      = some (.int 64 add568) := fpFirstEnv_add568934 env ip add568 nv w
  have h295_1 : lookupName (fpFirstEnv env ip add568 nv w) "%add29569933"
      = some (.int 64 (0x9#64)) := fpFirstEnv_add29569933 env ip add568 nv w
  have hv8_1 : lookupName (fpFirstEnv env ip add568 nv w) "%v8"
      = some (.ptr v8a) := fpFirstEnv_v8 hv8
  have hread2' : readBytes (stateAt (fpFirstEnv env ip add568 nv w)
      { s with pc := "while.body", pre := some "cleanup" }).mem
      (a + (add568.signExtend 64).toNat) 8 = some bs8 := by
    simpa only [fpFirstEnv, fpCleanupEnv, stateAt] using hread2
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpFirstEnv env ip add568 nv w)
        { s with pc := "while.body", pre := some "cleanup" }) =
      .jump (stateAt (fpBodyEnv2r env a v8a ip add568 nv w)
        { s with pc := "cleanup.thread", pre := some "while.body" }) :=
    fpBody_step_refuse (epow := epow) (env := fpFirstEnv env ip add568 nv w)
      (s := { s with pc := "while.body", pre := some "cleanup" })
      rfl hp1 h568_1 h295_1 hv8_1 hpos hread2' hval2
  have h35_2 : lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add35"
      = some (.int 64 (ip * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) :=
    fpBodyEnv2r_add35 env a v8a ip add568 nv w
  have h568_2 : lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add568934"
      = some (.int 64 add568) := fpBodyEnv2r_add568934 env a v8a ip add568 nv w
  have h295_2 : lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%add29569933"
      = some (.int 64 (0x9#64)) := fpBodyEnv2r_add29569933 env a v8a ip add568 nv w
  have hv8_2 : lookupName (fpBodyEnv2r env a v8a ip add568 nv w) "%v8"
      = some (.ptr v8a) := fpBodyEnv2r_v8 hv8
  have hden3 := fpCleanupThread_denote_body (epow := epow)
    (env := fpBodyEnv2r env a v8a ip add568 nv w)
    (s := { s with pc := "cleanup.thread", pre := some "while.body" })
    rfl h568_2 h295_2 h35_2 hv8_2
  have hstep3 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpBodyEnv2r env a v8a ip add568 nv w)
        { s with pc := "cleanup.thread", pre := some "while.body" }) =
      .jump (stateAt (fpSecondThreadEnv env a v8a ip add568 nv w)
        { s with pc := "while.end", pre := some "cleanup.thread" }) :=
    fpCleanupThread_step_body (epow := epow)
      (s := { s with pc := "cleanup.thread", pre := some "while.body" })
      rfl rfl h568_2 h295_2 h35_2 hv8_2
  refine ⟨stateAt (fpSecondThreadEnv env a v8a ip add568 nv w)
    { s with pc := "while.end", pre := some "cleanup.thread" }, rfl, rfl, rfl, rfl, ?_⟩
  intro k
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2,
    runFuel_jump_prefix hstep3]

/-! ### The fraction's copy of the fold

`cleanup112` and `while.body100` are the same three shapes on the fraction's
copy: `%fr.0584943` replaces `%ip.0565935`, `%add92587942` the index,
`%add96588941` the count, and `%v8101` the local.  `while.end115` is the merge,
whose `%fr.0556`, `%fdig.0554` and `%i.6552` read whichever of `cleanup112`,
`cleanup112.thread` and `while.cond91.preheader` left. -/

/-- `cleanup112`, from its `findBlock` pin. -/
def fpCleanup112Instrs : List Instr :=
  [Instr.phi "%fr.0584943" (Ty.int 64) [("while.body100", (Operand.reg "%add109")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
   Instr.phi "%add92587942" (Ty.int 64) [("while.body100", (Operand.reg "%add92")),
                                       ("while.body100.preheader", (Operand.reg "%add92582"))],
   Instr.phi "%add96588941" (Ty.int 64) [("while.body100", (Operand.reg "%add96")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000008#64)))],
   Instr.binop "%mul107" (BinOp.mul) 64 (Operand.reg "%fr.0584943") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
   Instr.load "%14" (Ty.int 32) (Operand.reg "%v8101"),
   Instr.zext "%conv108" 32 64 (Operand.reg "%14"),
   Instr.binop "%add109" (BinOp.add) 64 (Operand.reg "%mul107") (Operand.reg "%conv108"),
   Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                        (Ty.ptr, (Operand.reg "%v8101"))],
   Instr.binop "%add92" (BinOp.add) 64 (Operand.reg "%add92587942") (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.icmp "%cmp93" (IPred.ule) 64 (Operand.reg "%add92") (Operand.reg "%n"),
   Instr.icmp "%cmp97" (IPred.ult) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x000000000000000c#64)),
   Instr.select "%15" (Ty.int 1) (Operand.reg "%cmp93") (Operand.reg "%cmp97") (Operand.imm (Const.int 1 0x0#1))]

theorem findBlock_fpCleanup112 :
    numFastBody.findBlock "cleanup112" =
      some ⟨"cleanup112", fpCleanup112Instrs,
        Term.condbr (Operand.reg "%15") "while.body100" "while.end115"⟩ := by
  simpa only [fpCleanup112Instrs] using numFast_findBlock_cleanup112

/-- `cleanup112`'s environment: the fraction's folded word, the advanced index,
the two guards and the three `phi` cells. -/
def fpCleanup112Env (env : Env) (fr add92 add96 nv : BitVec 64) (w : BitVec 32) : Env :=
  ("%15", .int 1 (fpGuard (add92 + 0x8#64) add96 nv)) ::
  ("%cmp97", .int 1 (evalICmp .ult add96 (0xc#64))) ::
  ("%cmp93", .int 1 (evalICmp .ule (add92 + 0x8#64) nv)) ::
  ("%add92", .int 64 (add92 + 0x8#64)) ::
  ("%add109", .int 64 (fr * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) ::
  ("%conv108", .int 64 (BitVec.ofNat 64 w.toNat)) ::
  ("%14", .int 32 w) ::
  ("%mul107", .int 64 (fr * (0x5f5e100#64))) ::
  ("%add96588941", .int 64 add96) ::
  ("%add92587942", .int 64 add92) ::
  ("%fr.0584943", .int 64 fr) :: env

/-- `cleanup112` from the first group: the preheader's zero fraction, the
preheader's index, the reader's word, and the advanced count `8`. -/
theorem fpCleanup112_denote_pre {epow : Int → Option EPow} {env : Env} {s : State}
    {fr add92 nv : BitVec 64} {v8a : Nat} {w : BitVec 32}
    (hpre : s.pre = some "while.body100.preheader")
    (hfr : lookupName env "%add92582" = some (.int 64 add92))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hread : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpCleanup112Instrs (stateAt env s) =
      some (stateAt (fpCleanup112Env env 0 add92 (0x0000000000000008#64) nv w) s) := by
  unfold fpCleanup112Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 0
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add92582" _ hfr
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 (0x0000000000000008#64)
  rw [denoteCode_mul_imm _ _ _ "%mul107" "%fr.0584943" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 _ _ _ "%14" "%v8101"
    (by block_lk) hread _]
  rw [denoteCode_zext _ _ _ "%conv108" "%14" 32 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add109" "%mul107" "%conv108" (by block_lk) (by block_lk) _]
  rw [denoteCode_lifetimeEnd_fp epow (ptr := "%v8101") (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%add92" "%add92587942" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp93" "%add92" "%n"
    .ule 64 (by block_lk) (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp97"
    "%add96588941" .ult (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_select_bit_reg_imm_w _ _ _ "%15"
    "%cmp93" "%cmp97" 1 (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, fpCleanup112Env, fpGuard, runCells]

/-- `cleanup112` from the second group: `while.body100`'s cells on the same
shape. -/
theorem fpCleanup112_denote_body {epow : Int → Option EPow} {env : Env} {s : State}
    {fr add92 add96 nv : BitVec 64} {v8a : Nat} {w : BitVec 32}
    (hpre : s.pre = some "while.body100")
    (hfr : lookupName env "%add109" = some (.int 64 fr))
    (h92 : lookupName env "%add92" = some (.int 64 add92))
    (h96 : lookupName env "%add96" = some (.int 64 add96))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hread : readBytes s.mem v8a 4 = some (natToBytes w.toNat 4))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpCleanup112Instrs (stateAt env s) =
      some (stateAt (fpCleanup112Env env fr add92 add96 nv w) s) := by
  unfold fpCleanup112Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add109" _ hfr
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add92" _ h92
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add96" _ h96
  rw [denoteCode_mul_imm _ _ _ "%mul107" "%fr.0584943" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_load_i32 _ _ _ "%14" "%v8101"
    (by block_lk) hread _]
  rw [denoteCode_zext _ _ _ "%conv108" "%14" 32 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add109" "%mul107" "%conv108" (by block_lk) (by block_lk) _]
  rw [denoteCode_lifetimeEnd_fp epow (ptr := "%v8101") (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%add92" "%add92587942" (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp93" "%add92" "%n"
    .ule 64 (by block_lk) (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp97"
    "%add96588941" .ult (by block_lk) _]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_select_bit_reg_imm_w _ _ _ "%15"
    "%cmp93" "%cmp97" 1 (by block_lk) (by block_lk) _]
  simp only [denoteCode_nil, stateAt, fpCleanup112Env, fpGuard, runCells]

/-- `cleanup112`'s step into the second group: both guards passed. -/
theorem fpCleanup112_step_body {epow : Int → Option EPow} {env : Env} {s : State}
    {fr add92 add96 nv : BitVec 64} {w : BitVec 32}
    (hpc : s.pc = "cleanup112")
    (hden : denoteCode (stage2NumFastCalls epow) fpCleanup112Instrs (stateAt env s) =
      some (stateAt (fpCleanup112Env env fr add92 add96 nv w) s))
    (hbit : fpGuard (add92 + 0x8#64) add96 nv = 1) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanup112Env env fr add92 add96 nv w)
        { s with pc := "while.body100", pre := some "cleanup112" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanup112Env env fr add92 add96 nv w) s)
    (b := ⟨"cleanup112", fpCleanup112Instrs,
      Term.condbr (Operand.reg "%15") "while.body100" "while.end115"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanup112Instrs] using findBlock_fpCleanup112
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpCleanup112Env env fr add92 add96 nv w) "%15"
        = some (.int 1 (fpGuard (add92 + 0x8#64) add96 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%15" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `cleanup112`'s step out of the loop: one guard failed. -/
theorem fpCleanup112_step_end {epow : Int → Option EPow} {env : Env} {s : State}
    {fr add92 add96 nv : BitVec 64} {w : BitVec 32}
    (hpc : s.pc = "cleanup112")
    (hden : denoteCode (stage2NumFastCalls epow) fpCleanup112Instrs (stateAt env s) =
      some (stateAt (fpCleanup112Env env fr add92 add96 nv w) s))
    (hbit : fpGuard (add92 + 0x8#64) add96 nv = 0) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanup112Env env fr add92 add96 nv w)
        { s with pc := "while.end115", pre := some "cleanup112" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanup112Env env fr add92 add96 nv w) s)
    (b := ⟨"cleanup112", fpCleanup112Instrs,
      Term.condbr (Operand.reg "%15") "while.body100" "while.end115"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanup112Instrs] using findBlock_fpCleanup112
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpCleanup112Env env fr add92 add96 nv w) "%15"
        = some (.int 1 (fpGuard (add92 + 0x8#64) add96 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%15" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `while.body100`'s instructions, from its pin. -/
def fpBody100Instrs : List Instr :=
  [Instr.binop "%add96" (BinOp.add) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                        (Ty.ptr, (Operand.reg "%v8101"))],
   Instr.gep "%add.ptr102" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add92587942"),
   Instr.call "%call103" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102")),
                        (Ty.ptr, (Operand.reg "%v8101"))],
   Instr.icmp "%tobool104.not" (IPred.eq) 32 (Operand.reg "%call103") (Operand.imm (Const.int 32 0x00000000#32))]

theorem findBlock_fpBody100 :
    numFastBody.findBlock "while.body100" =
      some ⟨"while.body100", fpBody100Instrs,
        Term.condbr (Operand.reg "%tobool104.not") "cleanup112.thread" "cleanup112"⟩ := by
  simpa only [fpBody100Instrs] using numFast_findBlock_while_body100

/-- `while.body100`'s environment. -/
def fpBody100Env (env : Env) (a v8a : Nat) (idx add96 : BitVec 64)
    (call : BitVec 32) : Env :=
  ("%tobool104.not", .int 1 (evalICmp .eq call (0x0#32))) ::
  ("%call103", .int 32 call) ::
  ("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
  ("%add96", .int 64 (add96 + 0x8#64)) :: env

/-- `while.body100` at a successful reader. -/
theorem fpBody100_denote_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx add96 : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add92587942" = some (.int 64 idx))
    (hcnt : lookupName env "%add96588941" = some (.int 64 add96))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    denoteCode (stage2NumFastCalls epow) fpBody100Instrs (stateAt env s) =
      some (stateAt (fpBody100Env env a v8a idx add96 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }) := by
  unfold fpBody100Instrs
  rw [denoteCode_add_imm (stage2NumFastCalls epow) env s "%add96" "%add96588941"
    (by block_lk) _]
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
    (("%add96", .int 64 (add96 + 0x8#64)) :: env) s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8101"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") (by block_lk))
    (stage2NumFastCalls_lifetime_end epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow)
    (("%add96", .int 64 (add96 + 0x8#64)) :: env) _ "%add.ptr102" "%p" "%add92587942"
    (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add96", .int 64 (add96 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call103" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr102")), (Ty.ptr, (Operand.reg "%v8101"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 1, mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add96", .int 64 (add96 + 0x8#64)) :: env) "%add.ptr102"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add96", .int 64 (add96 + 0x8#64)) :: env) "%v8101"
          = some (.ptr v8a) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_read hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call103", .int 32 1) :: ("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add96", .int 64 (add96 + 0x8#64)) :: env)
    { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    "%tobool104.not" "%call103" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode_nil, stateAt, fpBody100Env]

/-- `while.body100` at a refused reader. -/
theorem fpBody100_denote_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx add96 : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add92587942" = some (.int 64 idx))
    (hcnt : lookupName env "%add96588941" = some (.int 64 add96))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    denoteCode (stage2NumFastCalls epow) fpBody100Instrs (stateAt env s) =
      some (stateAt (fpBody100Env env a v8a idx add96 0)
        { s with mem := s.mem, next := s.next }) := by
  unfold fpBody100Instrs
  rw [denoteCode_add_imm (stage2NumFastCalls epow) env s "%add96" "%add96588941"
    (by block_lk) _]
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
    (("%add96", .int 64 (add96 + 0x8#64)) :: env) s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8101"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") (by block_lk))
    (stage2NumFastCalls_lifetime_end epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow)
    (("%add96", .int 64 (add96 + 0x8#64)) :: env) _ "%add.ptr102" "%p" "%add92587942"
    (by block_lk) (by block_lk) hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add96", .int 64 (add96 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call103" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr102")), (Ty.ptr, (Operand.reg "%v8101"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 0, mem := s.mem, next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add96", .int 64 (add96 + 0x8#64)) :: env) "%add.ptr102"
          = some (.ptr (a + (idx.signExtend 64).toNat)) := lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
           ("%add96", .int 64 (add96 + 0x8#64)) :: env) "%v8101"
          = some (.ptr v8a) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_refuse hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call103", .int 32 0) :: ("%add.ptr102", .ptr (a + (idx.signExtend 64).toNat)) ::
     ("%add96", .int 64 (add96 + 0x8#64)) :: env)
    { s with mem := s.mem, next := s.next }
    "%tobool104.not" "%call103" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode_nil, stateAt, fpBody100Env]

/-- `while.body100`'s step at a successful reader. -/
theorem fpBody100_step_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx add96 : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body100")
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add92587942" = some (.int 64 idx))
    (hcnt : lookupName env "%add96588941" = some (.int 64 add96))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpBody100Env env a v8a idx add96 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next,
                 pc := "cleanup112", pre := some "while.body100" }) := by
  have hbit : evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32) = 0 := by decide
  refine numFast_step_at (s' := stateAt (fpBody100Env env a v8a idx add96 1)
      { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next })
    (b := ⟨"while.body100", fpBody100Instrs,
      Term.condbr (Operand.reg "%tobool104.not") "cleanup112.thread" "cleanup112"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBody100Instrs] using findBlock_fpBody100
  · simpa only [denoteCode_nil] using
      fpBody100_denote_ok (epow := epow) hp hidx hcnt hv8 hpos hread hval hw
  · have hlk : lookupName (fpBody100Env env a v8a idx add96 1) "%tobool104.not"
        = some (.int 1 (evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_zero _ "%tobool104.not" "cleanup112.thread" "cleanup112"
      hlk rfl]
    simp only [stateAt, hpc]

/-- `while.body100`'s step at a refused reader. -/
theorem fpBody100_step_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx add96 : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body100")
    (hp : lookupName env "%p" = some (.ptr a))
    (hidx : lookupName env "%add92587942" = some (.int 64 idx))
    (hcnt : lookupName env "%add96588941" = some (.int 64 add96))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpBody100Env env a v8a idx add96 0)
        { s with pc := "cleanup112.thread", pre := some "while.body100" }) := by
  have hbit : evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32) = 1 := by decide
  refine numFast_step_at (s' := stateAt (fpBody100Env env a v8a idx add96 0)
      { s with mem := s.mem, next := s.next })
    (b := ⟨"while.body100", fpBody100Instrs,
      Term.condbr (Operand.reg "%tobool104.not") "cleanup112.thread" "cleanup112"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBody100Instrs] using findBlock_fpBody100
  · simpa only [denoteCode_nil] using
      fpBody100_denote_refuse (epow := epow) hp hidx hcnt hv8 hpos hread hval
  · have hlk : lookupName (fpBody100Env env a v8a idx add96 0) "%tobool104.not"
        = some (.int 1 (evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_one _ "%tobool104.not" "cleanup112.thread" "cleanup112"
      hlk rfl]
    simp only [stateAt, hpc]

/-- `while.end115`'s environment: the three merged cells and the test. -/
def fpWhileEnd115Env (env : Env) (i fr fdig nv : BitVec 64) : Env :=
  ("%cmp117592", .int 1 (evalICmp .ult i nv)) ::
  ("%i.6552", .int 64 i) :: ("%fdig.0554", .int 64 fdig) ::
  ("%fr.0556", .int 64 fr) :: env

/-- `while.end115`'s three `phi`s and its test, from the block's pin. -/
def fpWhileEnd115Instrs : List Instr :=
  [Instr.phi "%fr.0556" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fr.0584.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add109"))],
   Instr.phi "%fdig.0554" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fdig.0585.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add96588941"))],
   Instr.phi "%i.6552" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%i.6586.lcssa")),
                                       ("while.cond91.preheader", (Operand.reg "%inc77")),
                                       ("cleanup112", (Operand.reg "%add92587942"))],
   Instr.icmp "%cmp117592" (IPred.ult) 64 (Operand.reg "%i.6552") (Operand.reg "%n")]

theorem findBlock_fpWhileEnd115 :
    numFastBody.findBlock "while.end115" =
      some ⟨"while.end115", fpWhileEnd115Instrs,
        Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144"⟩ := by
  simpa only [fpWhileEnd115Instrs] using numFast_findBlock_while_end115

/-- `while.end115` from `cleanup112`: the folded fraction, the advanced count
and the advanced index. -/
theorem fpWhileEnd115_denote_cleanup {epow : Int → Option EPow} {env : Env} {s : State}
    {frr fdigr ir nv : BitVec 64}
    (hpre : s.pre = some "cleanup112")
    (hfr : lookupName env "%add109" = some (.int 64 frr))
    (hfd : lookupName env "%add96588941" = some (.int 64 fdigr))
    (hi : lookupName env "%add92587942" = some (.int 64 ir))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpWhileEnd115Instrs (stateAt env s) =
      some (stateAt (fpWhileEnd115Env env ir frr fdigr nv) s) := by
  unfold fpWhileEnd115Instrs
  block_eval

/-- `while.end115` from `cleanup112.thread`: the refusal carries the
preheader's zero fraction, its count and its index. -/
theorem fpWhileEnd115_denote_thread {epow : Int → Option EPow} {env : Env} {s : State}
    {frr fdigr ir nv : BitVec 64}
    (hpre : s.pre = some "cleanup112.thread")
    (hfr : lookupName env "%fr.0584.lcssa" = some (.int 64 frr))
    (hfd : lookupName env "%fdig.0585.lcssa" = some (.int 64 fdigr))
    (hi : lookupName env "%i.6586.lcssa" = some (.int 64 ir))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode (stage2NumFastCalls epow) fpWhileEnd115Instrs (stateAt env s) =
      some (stateAt (fpWhileEnd115Env env ir frr fdigr nv) s) := by
  unfold fpWhileEnd115Instrs
  block_eval

/-- `while.end115`'s step to the fraction head. -/
theorem fpWhileEnd115_step_head {epow : Int → Option EPow} {env : Env} {s : State}
    {i fr fdig nv : BitVec 64}
    (hpc : s.pc = "while.end115")
    (hden : denoteCode (stage2NumFastCalls epow) fpWhileEnd115Instrs (stateAt env s) =
      some (stateAt (fpWhileEnd115Env env i fr fdig nv) s))
    (hbit : evalICmp .ult i nv = 1) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpWhileEnd115Env env i fr fdig nv)
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) := by
  refine numFast_step_at (s' := stateAt (fpWhileEnd115Env env i fr fdig nv) s)
    (b := ⟨"while.end115", fpWhileEnd115Instrs,
      Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpWhileEnd115Instrs] using findBlock_fpWhileEnd115
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpWhileEnd115Env env i fr fdig nv) "%cmp117592"
        = some (.int 1 (evalICmp .ult i nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp117592" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `while.end115`'s step to the marker's block: the index reached the length. -/
theorem fpWhileEnd115_step_merge {epow : Int → Option EPow} {env : Env} {s : State}
    {i fr fdig nv : BitVec 64}
    (hpc : s.pc = "while.end115")
    (hden : denoteCode (stage2NumFastCalls epow) fpWhileEnd115Instrs (stateAt env s) =
      some (stateAt (fpWhileEnd115Env env i fr fdig nv) s))
    (hbit : evalICmp .ult i nv = 0) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpWhileEnd115Env env i fr fdig nv)
        { s with pc := "if.end144", pre := some "while.end115" }) := by
  refine numFast_step_at (s' := stateAt (fpWhileEnd115Env env i fr fdig nv) s)
    (b := ⟨"while.end115", fpWhileEnd115Instrs,
      Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpWhileEnd115Instrs] using findBlock_fpWhileEnd115
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (fpWhileEnd115Env env i fr fdig nv) "%cmp117592"
        = some (.int 1 (evalICmp .ult i nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp117592" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### Axiom footprints

The seams and the transport are instruction chains over the blocks' pins, so
nothing here is more than `propext` and the fold's own arithmetic.  The two
compositions that consume a run's exit predicate inherit the run instances'
`Classical.choice` (`ult_zero_iff`'s two-valued branch), and the fast path's
steps are at `stage2NumFastCalls`, whose reader answer is the model's. -/

#print axioms NumFastSeams.ifEnd68_denote_head
#print axioms NumFastSeams.intRunExit_end68
#print axioms NumFastSeams.intExit_dispatch_dot
#print axioms NumFastSeams.nodot_seam
#print axioms NumFastSeams.preheader_denote
#print axioms NumFastSeams.seven_tie
#print axioms NumFastSeams.ifEnd62_denote_back
#print axioms NumFastSeams.ifEnd62_step_end
#print axioms NumFastSeams.intExit_gate
#print axioms NumFastSeams.intRunExit_gate
#print axioms NumFastSeams.foldl_digits_add
#print axioms NumFastSeams.d8Value_eq_fold
#print axioms NumFastSeams.numD8Answer_writes
#print axioms NumFastSeams.fpPreheader_denote_ok
#print axioms NumFastSeams.fpPreheader_step
#print axioms NumFastSeams.fpPreheader_step_refuse
#print axioms NumFastSeams.fastGuard_two_groups
#print axioms NumFastSeams.stage2NumFastCalls_lifetime_end
#print axioms NumFastSeams.fpCleanupThread_step
#print axioms NumFastSeams.fpWhileEnd_denote_thread
#print axioms NumFastSeams.fpWhileEnd_step_head
#print axioms NumFastSeams.fpWhileEnd_step_merge
#print axioms NumFastSeams.denoteCode_lifetimeEnd_fp
#print axioms NumFastSeams.fpCleanup_denote_pre
#print axioms NumFastSeams.fpCleanup_denote_body
#print axioms NumFastSeams.fpCleanup_step_body
#print axioms NumFastSeams.fpCleanup_step_end
#print axioms NumFastSeams.fpWhileEnd_denote_cleanup
#print axioms NumFastSeams.fpBody_denote_ok
#print axioms NumFastSeams.fpBody_denote_refuse
#print axioms NumFastSeams.fpBody_step_ok
#print axioms NumFastSeams.fpBody_step_refuse
#print axioms NumFastSeams.fpCleanup112_denote_pre
#print axioms NumFastSeams.fpCleanup112_denote_body
#print axioms NumFastSeams.fpCleanup112_step_body
#print axioms NumFastSeams.fpCleanup112_step_end
#print axioms NumFastSeams.fpBody100_denote_ok
#print axioms NumFastSeams.fpBody100_denote_refuse
#print axioms NumFastSeams.fpBody100_step_ok
#print axioms NumFastSeams.fpBody100_step_refuse
#print axioms NumFastSeams.fpWhileEnd115_denote_cleanup
#print axioms NumFastSeams.fpWhileEnd115_denote_thread
#print axioms NumFastSeams.fpWhileEnd115_step_head
#print axioms NumFastSeams.fpWhileEnd115_step_merge
#print axioms NumFastSeams.digitFold_split
#print axioms NumFastSeams.readBytes_take_le
#print axioms NumFastSeams.d8Value_slice
#print axioms NumFastSeams.digitFold_one
#print axioms NumFastSeams.fpFirstFold
#print axioms NumFastSeams.fpSecondFold
#print axioms NumFastSeams.fpGuard_second_group
#print axioms NumFastSeams.fpCleanupThread_denote_body
#print axioms NumFastSeams.fpCleanupThread_step_body
#print axioms NumFastSeams.fpFirstEnv_p
#print axioms NumFastSeams.fpFirstEnv_add568934
#print axioms NumFastSeams.fpFirstEnv_add29569933
#print axioms NumFastSeams.fpFirstEnv_v8
#print axioms NumFastSeams.fpBodyEnv2_add35
#print axioms NumFastSeams.fpBodyEnv2_add
#print axioms NumFastSeams.fpBodyEnv2_add29
#print axioms NumFastSeams.fpBodyEnv2_v8
#print axioms NumFastSeams.fpBodyEnv2_n
#print axioms NumFastSeams.fpBodyEnv2r_add35
#print axioms NumFastSeams.fpBodyEnv2r_add568934
#print axioms NumFastSeams.fpBodyEnv2r_add29569933
#print axioms NumFastSeams.fpBodyEnv2r_v8
#print axioms NumFastSeams.fpFastSecond_run
#print axioms NumFastSeams.fpFastSecond_run_refuse

end NumFastSeams

end LeanLLVM.Refinement
