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
two groups.  What is *not* composed is the loop: `cleanup`'s own block (three
`phi`s, the `i32` load, the `@ 10 ^ 8` multiply, the zero-extend and its two
tests) has no chain lemma yet, and with it the second group's `while.body` and
the exit's `while.end` merge.  The registers `intRun_start` and `fracRun_start`
consume are that loop's exit, so the fast-path loop remains their boundary.

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

end NumFastSeams

end LeanLLVM.Refinement
