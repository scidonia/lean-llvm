/-
`num_fast_el1`'s numeric arm at the pinned body: what the body proves, and where
the correspondence to `strtodSpec` stops.

`JsonStage2NumFastBody` proves the refusal arm of `numFastBody` at the empty
lexeme, and `JsonStage2Body` proves the conversion at the *model*
(`numFastEmitted_strtodSpec`, unconditional on well-formed lexemes).  Between
those two statements is the body's conversion arm: the inlined dispatch and
scan, the inlined tier-1 arithmetic, the inlined fallback, and three callees the
body leaves out of line.

**The stopping points, as facts about the body and the walk's environment.**
`s2HelperCalls` is `stage2Calls noCalls`: two lifetime markers, `memset`, the
trap, and nothing else.  The conversion's three out-of-line callees — the
eight-digit reader `num_d8_el1`, the 128-bit kernel `num_el_el1` and the
fallback's big multiply `stk_mul_u64` — are not entries of it, and at each of
their call sites the body's `step` is `ub`: the run does not fall through to a
scalar or a slower path, because the call is not guarded by an answer.  The
theorems below state that at the body's own blocks, with `runFuel`'s `.ub` as
the conclusion.  A proof that ran the body at this environment would therefore
arrive at `ub` at each call site, so the conversion's arithmetic is unreachable
there: the numeric arm cannot be carried by the body's run alone.

**What is proved.**  Three facts about the body and the walk's environment, at
the body's own blocks, plus the arm's statement at the vocabulary a proof must
use:

* `s2HelperCalls` has no entry for `num_d8_el1`, `num_el_el1` or `stk_mul_u64`,
  and the lifetime marker's entry is the control that the same reading of
  `stage2Calls` answers `some` where it does;
* at `while.body.preheader` (the fast path's eight-digit reader), at
  `if.end268` (the 128-bit kernel) and at `if.then178.i.i` (the fallback's big
  multiply) the block's `denoteCode` is `none` and the body's `step` is `ub`, so
  the run is `some .ub`;
* `NumFastBodyArm` is the arm's statement at the body: a `Calls` selection that
  answers the three callees, a staging that stages the two tables
  (`NumFastTables`), and the conclusion — `strtodSpec`'s eight bytes at `out`,
  `err` untouched, the cursor unchanged, the memory outside the two slots the
  caller's.

**What the supplied environment changes, and what it does not.**  The `calls`
parameter is no longer missing a value: `JsonStage2NumFastCalls.numFastCalls`
answers the three callees (each modelled from its measured C text),
`stage2NumFastCalls` is that selection composed with the walk's `s2HelperCalls`,
and at each of the three sites the block's `denoteCode` is now `some` and its
`step` a jump (`numFast_ifEnd268_denote_some`/`_step_jump`,
`numFast_whileBodyPreheader_denote_some`/`_step_jump`,
`numFast_ifThen178_denote_some`/`_step_jump`).  The three `ub` theorems above
remain true of `s2HelperCalls`, which is why they are kept: they are the
statement that the walk's own selection does not answer.

`NumFastTables` is inhabited at a concrete staging
(`JsonStage2NumFastCalls.numFastTables_holds`), and
`JsonStage2NumFastCounters` reads the merge block's two counters at the model.
The arm itself is still **not** claimed.  What the tree now supplies beyond the
environment is the runs: `JsonStage2NumFastDigitRuns` discharges all three
`BoundLoop` instances — `intRun_run` at `land.lhs.true41`, `fracRun_run` at
`land.lhs.true119`, `expRun_run` at `land.lhs.true195` — each with the exit
carrying its counters, and `JsonStage2NumFastStarts` supplies the runs' *starts*
at the dispatch's edges.  Tier 2 is not on the list: `JsonStage2NumFastTier2`
proves the model is the guard's decision on the kernel's `w < 2 ^ 64` domain
(`NumFastElAgrees`, from `numElEl1_eq_elTier2Code`), and
`not_numFastElUnbounded` shows the bound is the kernel's, not the proof's.

A proof needs four things, of which the first two the tree supplies outright and
the other two only in part:

1. **A `Calls` selection answering the three callees.**  Supplied by
   `JsonStage2NumFastCalls`: each of the three is modelled from its measured C
   text (`numf_el1.h`, `numel_el.h`, `stage2.c`), the selection composes with
   the walk's `s2HelperCalls`, and the three sites' steps are jumps at it.
2. **The two tables' contents.**  Supplied as a concrete staging:
   `JsonStage2NumFastCalls.numFastTables_holds` is `NumFastTables` at
   `numFastTableEnv`/`numFastTableMem`, twenty `NUMF_EL1_P10` rows and
   twenty-three `NUMF_EL1_POW10` rows, proved from `readBytes`' definition.
3. **The inlined scan's counters, at the runs.**  `JsonStage2NumFastScan` fixes
   the `BoundLoop` shape, `JsonStage2NumFastDigitRuns` discharges the three
   instances, `JsonStage2NumFastCounters` reads the merge block's two counters
   at the model, and `JsonStage2NumFastStarts` closes the runs' starts:
   * `intRun_start`: from the sign check at `land.lhs.true`, with the lead a
     `'1' … '9'` and the eight-digit guard at `if.then22` refused, seven steps
     reach `land.lhs.true41` with `intRunInv … (negIndex b + 1) 1 bs … 0` — the
     index after the lead and the one digit counted;
   * the `0`-alone arm is `ifThen11_step`/`ifEnd68_denote_zero`, which fix
     `%i.5 = %inc12`, `%idig.4 = 1`, `%ip.5 = 0` and never enter the run;
   * `fracRun_start`: from the `.` test at `land.lhs.true71`, with a digit after
     the `.` and the eight-digit guard at `while.cond91.preheader` refused, six
     steps reach `land.lhs.true119` with `fracRunInv … (i5 + 1) 0 bs … 0`;
   * `expRun_start`: from the digit gate at `lor.lhs.false180`, one step reaches
     `land.lhs.true195` with `expRunInv … i11 bs … 0`.

   What remains of the scan, and is *not* claimed here: the two eight-digit fast
   paths (`while.body`/`cleanup` at `if.then22` and
   `while.body100`/`cleanup112` at `while.cond91.preheader`), whose registers
   the starts above are proved *behind* the guard of — the integer one's entry is
   `JsonStage2NumFastTaken.fpIfThen22_entry` and the fraction's is
   `JsonStage2NumFastTaken.fracWhileCond91_entry`, the four reader answers at
   each guard's zero; and the exponent's marker nest between `if.end144` and `lor.lhs.false180`
   (`land.lhs.true147`, `NodeBlock`, `LeafBlock`/`LeafBlock1`, `if.then157`,
   `land.lhs.true161`, `NodeBlock7`, `LeafBlock5`/`LeafBlock3`, `if.then171`,
   `if.end177`), whose four path shapes (marker `e`/`E` × sign present/absent)
   fix `%i.11`, the index `expRun_start` takes.  `JsonStage2NumFastStarts`'s own
   header names both, and `expRun_start`'s docstring names the nest register by
   register.
4. **The inlined tier-1 arithmetic, and tier 3's traversal.**  Two boundaries,
   each stated at the block it stops before.

   *Tier 1.*  The body's tier-1 path is `if.end230` (the counters, proved) →
   `if.then241` (the mantissa word `%add244 = %30 * %ip + %fr` with
   `%30 = NUMF_EL1_P10[%fdig]`, and the narrow class test `%or.cond306`) →
   `if.then253` (`%conv256 = uitofp %add244`, the sign test `%cmp254`) →
   `cond.true`/`cond.false` (the `NUMF_EL1_POW10` load and `fmul`/`fdiv`) →
   `cleanup282.thread` (`fneg`, the sign select, the store at `%out`).  Against
   `StrtodTier1.emittedRefinesOn_tier1` the missing links are four:
   (a) `denoteCode` chain steps for `uitofp`, `fmul`, `fdiv`, `fneg` and an
   eight-byte `double` load — `evalInstr` defines all four operations
   (`Semantics.lean:547-562`) and `JsonStage2NumFastTier1` supplies the
   `evalInstr_*`/`step_*`/`denoteCode_*` lemmas, so this path's blocks are
   steppable and the module's header records where its own chain stops; (b) the class test: `%or.cond304` at `if.end230`
   (`%add232 <u 20` and `%sub231 + 45 <u 91`) and `%or.cond306` at `if.then241`
   (`%add232 <u 16`, `%sub231 + 22 <u 45`) against `StrtodRefine.Tier1`,
   `digitCount d ≤ 15 ∧ |eff| ≤ 22`; (c) the mantissa: `%add244` against
   `Decimal.mantissa d` inside that window — `%ip`'s accumulator agreement and
   the `NUMF_EL1_P10` rows (`NumFastTables`), with the `idig < 19` cap inert at
   `≤ 15` digits; (d) the tick algebra: `uitofpBits`, `fmulBits`, `fdivBits`
   and `fnegBits` are *defined* as `packMag ∘ roundMag` (`Binary64.lean:1424-
   1450`), so the single correctly rounded operation the tier module names as
   outside the tree is the tree's own definition, and what is left is the
   arithmetic `fmulBits (packMag (roundMag (10 ^ k * 2 ^ 1074) 1)) (uitofpBits
   mant) = packMag (roundMag (mant * 10 ^ k * 2 ^ 1074) 1)`, the division's
   mirror, and the `F64.ofBits (packMag _)` readbacks those two read through.
   `StrtodTier1`'s `opP_eq_ticks`/`opD_eq_ticks` then supply the `(P, D)` both
   `roundMag`s share.  None of the four is a platform axiom: `(d)` closes on
   the tree's definitions, not on hardware.

   *Tier 3.*  The body's fallback is reached at `if.end285` and is the inlined
   `num_scan` second reader — `g_nume1_slow`'s increment, `if.end6.i` …
   `if.else35.i`, `land.lhs.true40.i`, `if.then45.i`, `if.end77.i`,
   `land.lhs.true80.i`/`NodeBlock13`/`LeafBlock11`/`LeafBlock9`, `if.then90.i`,
   `if.then104.i`, `if.end106.i`, `lor.lhs.false109.i`, `if.then119.i`,
   `while.body135.i`, `if.end138.i`, `if.then141.i`, `if.then143.i` — and then
   the inlined `to_double`: `for.body.outer.i.outer.i`, the window copy
   (`for.body87.i.i`, its three unrolled copies and `for.inc98.i.i`, `.epil`,
   `for.end100.i.i`), the `T`/`F` parse (`for.body.i.i`, `if.then31.i.i`,
   `if.then36.i.i`, `if.else46.i.i`, `for.end.i.i`), the lead clamps
   (`if.then113.i.i`, `if.end120.i.i`, `if.then123.i.i`, `if.end126.i.i`), the
   big multiply (`for.body.i.i.i`, `stk_mul_u64.exit.i.i`, `while.end.i.i`) and
   the ladder (`if.else164.i.i`, `while.body173.i.i`, `while.cond184.preheader
   .i.i`).  The model's decision half is complete (`walkLoop_computes_tier3Mag`
   is the loop's answer at `tier3Mag`'s ticks, and the tier-3 module's
   `What is not proved` names what it takes).  Of the three links that remained,
   `JsonStage2NumFastTier3` now states all three and proves each at its
   statement: (a) the region's `runFuel` simulation — the `poison` edges bind
   the marker rather than being unreachable (the peeled entry takes them at
   counts 1–3), the residual block's own step is a jump, and
   `t3_traversal_counts_1_3` composes the two steps with the reached state's
   markers unread; what remains is the region's other blocks, from
   `for.body.i.i566.i.i.epil`; (b) the window tie — `copy_retained` is the
   retained array as `m / 10 ^ stkDrop m`, `copy_sticky` the copy's sticky bit
   as the model's remainder test, `copy_counters` the emitted `S`/`f` as
   `E + stkDrop m`/`leadM`, and `t3_copy_denote` the store block at its pin;
   the loop's blocks are then stepped per edge
   (`JsonStage2NumFastTier3CopySteps`), the residual loop's shape is fixed
   (`t3EpilLoopOf`) and its two visits are discharged (`t3Epil_step_exit_test`,
   `t3Epil_step_loop_test`, `t3EpilLoop`, `t3EpilLoop_run_at'`), so the unrolled
   nest's shape is the piece not composed; and
   (c) the proximity estimate — `roundMag_dist_le_step`,
   `fmulBits_dist_le_step`/`fdivBits_dist_le_step`, `proximity_scale` and
   `t3_scale_of_ulp`, which concludes `shift_of_near`'s premise from the tree's
   own rounding, with the fold's two blocks and its two-step error now in
   `JsonStage2NumFastTier3Fold` and the ladder's repetition at the emitted rows
   in `JsonStage2NumFastTier3Ladder`: the rows compose to the model's one row,
   one rounding each, at most sixteen, the bracket composes at that many steps,
   and the rows' steps are charged at the final row's scale
   (`t3RoundStep_mono`, `t3RoundStep_mul_le`, `t3Ladder_charge`).  The ladder's
   two loops are stated at their own blocks — their `findBlock` pins exist in
   `JsonStage2HelperIRNumFast` — with each head's jumps proved and each row
   block's per-edge step the arm still to supply.

   Neither boundary is a `sorry`, and neither is a paragraph: each is a
   statement in the module named above, with what it leaves open named there.

**What `JsonStage2NumFastScanRun` now supplies, against that list.**  Item 3's
scan has its exponent nest: `nestTo157_e`/`nestTo157_E` take the marker's byte
through `land.lhs.true147`/`NodeBlock`/`LeafBlock*`, `nestFrom157_nosign`/`_sign`
reach `lor.lhs.false180` with `%i.11` and `%esign.0` — the registers
`expRun_start` consumes — and `nest_nomarker` takes the no-exponent branch to
`if.end226`.  `intScan_run` is the integer dispatch and its run from `entry`, and
`fracScan_run` is the fraction dispatch and its run from `land.lhs.true71`; both
are `runFuel` prefixes with the fuel as a term of the arguments.  Item 1's merge
is `cleanup223.thread`'s two edges, `if.end226`'s four, and
`expMerge_run_inc`/`expMerge_run_head` into `mergeEntry`; `if.end230`'s bound edge
is `ifEnd230_denote_end62`/`ifEnd230_step_end62`.  Of item 1's mantissa, the
word-level ties are `ip_word_digitsNat`/`fr_word_digitsNat`, fed by
`intRunExit_end230`/`fracRunExit_end230`; at the merge they are
`JsonStage2NumFastSeams.t1_intRun_tie` and `t1_fracRun_tie`, with `t1_headTie`
the `if.end68` seam and `t1_fracCount_tie` the fraction's count preheader.  Still
open on this list: the
eight-digit fast paths' `runFuel` composition.  Both are now composed at their
guards' taken edges.  The integer one is `JsonStage2NumFastTaken.fpIfThen22_entry`:
the guard's zero through `while.body.preheader` and the loop's four branches to
`intRunInv`, at `(start + 1, 1)`, `(start + 9, 9)` or `(start + 17, 17)`.  The
fraction's is `JsonStage2NumFastTaken.fracWhileCond91_entry`, the same four
answers at `while.cond91.preheader`'s zero and the counts `0`, `8`, `8` and `16`.
The guard's *two* answers are one statement in `JsonStage2NumFastJoin.guard_join`:
`if.then22`'s `condbr` splits on `%add563` and `%n`, the refusal reaches
`intRunInv` at `(start + 1, 1)` in three steps — given the successor's presence,
which `intScan_run` also carries — and the taken answer is
`fpIfThen22_entry`'s four shapes, so `intScan_run`'s refused-guard dispatch and
the guarded run continue at the same predicate.  Also open: the seam steps that
would thread one theorem from `entry` to `if.end230` — the merge's registers are
tied, but the scan's blocks are composed one seam at a time rather than as one
run from `entry` — and tier 3's region beyond
its poison edge (`JsonStage2NumFastTier3` states the edge's traversal, the window
tie and the proximity estimate).  The accumulator's tie at `if.end230` is
stated: `intRunExit_gate` reads the run's `%ip.4` and `%7` as the merge's
`%ip.5708717729` and `%idig.4709716730`, the exit's own `%n` cell fixes the
run's stop index as the lexeme's end, and `t1_intRun_tie`/`t1_fracRun_tie` read
the merged registers as `Decimal.digitsNat`.


**Where the arm stands after the tier-3 modules.**  The environment (item 1) and
the staging (item 2) are values, each *site*'s step is a jump at them, and the
scan's three runs and their starts are discharged, with the two eight-digit fast
paths composed at their guards' taken edges; the seam steps that would thread one
run from `entry` to `if.end230` are still composed one at a time rather than as a
single trace.  Item 4's tier-1 chain is stated at its blocks with its four links
named ((a) the instruction steps, which the tier-1 module supplies; (b) the class
test; (c) the mantissa; (d) the tick algebra).  Tier 3's window tie and proximity
estimate are at their statements, the residual copy loop is now an induction at the
emitted blocks (`JsonStage2NumFastTier3CopyLoop.t3EpilLoop`, with
`t3EpilLoop_run_at'` its budget), and the emitted ladder's repetition is
`JsonStage2NumFastTier3Ladder`'s: the rows compose to the model's one row, each is
one rounding, the bracket composes at the row count, and the rows' steps are
charged at the final row's scale.  The loops themselves are stated at their pins
(`t3MulLoopOf`/`t3DivLoopOf`, with each head's jumps proved); the arm they still
omit is each row block's per-edge step.  What the arm needs beyond that is the run
itself: the copy's four-way unrolled main loop as a `BoundLoop`, the seam steps
above, and tier 1's store chain from the exponent edge.  No theorem below claims
the arm, and none is instantiated at the walk's own `s2HelperCalls`; the kernel's
`w < 2 ^ 64` bound is met at the body's own word
(`JsonStage2NumFastTier3.numFast_ifEnd268_domain`), so the bound is not what stops
the arm — the run's composition is.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastBody

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval

/-! ### The walk's environment answers none of the conversion's callees

`s2HelperCalls` resolves the two lifetime markers, `memset` and the trap.  A
conversion callee reaches `noCalls`, which answers `none`.  The control is the
lifetime marker's own entry: the same reading of `stage2Calls` answers `some`
there, so the instrument below discriminates rather than answering `none`
everywhere. -/

/-- The eight-digit reader is not in the walk's environment. -/
theorem s2HelperCalls_num_d8_el1 (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "num_d8_el1" args mem next = none := rfl

/-- The 128-bit kernel is not in the walk's environment. -/
theorem s2HelperCalls_num_el_el1 (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "num_el_el1" args mem next = none := rfl

/-- The fallback's big multiply is not in the walk's environment. -/
theorem s2HelperCalls_stk_mul_u64 (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "stk_mul_u64" args mem next = none := rfl

/-- The control: the same reading answers a lifetime marker. -/
theorem s2HelperCalls_lifetime_start (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "llvm.lifetime.start.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := rfl

/-! ### A block whose chain reaches an unanswered call is `ub`

The body's `step` is `.ub` where a block's instruction list cannot denote: the
`denoteCode` is `none` and `step` reads that as `ub`.  Two chain steps are the
whole mechanism: a `call` the environment does not answer, and the void form the
fallback's big multiply takes.  Each is stated as `denoteCode … = none` at the
state the block began from, so a caller composes it with the block's earlier
instructions. -/

/-- A `call` whose answer the environment does not have makes the block `ub`. -/
theorem denoteCode_call_none (calls : Calls) (env : Env) (s : State) (d : String)
    (ty : Ty) (callee : String) (args : List (Ty × Operand)) (vs : List Value)
    (hargs : evalOperands (stateAt env s) args = some vs)
    (hnone : calls callee vs s.mem s.next = none) (is : List Instr) :
    denoteCode calls (.call d ty callee args :: is) (stateAt env s) = none := by
  simp only [denoteCode, denoteRun, evalInstr, State.bindAll]
  rw [hargs]
  dsimp only [stateAt]
  rw [hnone]

/-- A void `call` whose answer the environment does not have makes the block
`ub`. -/
theorem denoteCode_callVoid_none (calls : Calls) (env : Env) (s : State)
    (callee : String) (args : List (Ty × Operand)) (vs : List Value)
    (hargs : evalOperands (stateAt env s) args = some vs)
    (hnone : calls callee vs s.mem s.next = none) (is : List Instr) :
    denoteCode calls (.callVoid callee args :: is) (stateAt env s) = none := by
  simp only [denoteCode, denoteRun, evalInstr, State.bindAll]
  rw [hargs]
  dsimp only [stateAt]
  rw [hnone]

/-- A void `call` the environment answers: the chain continues at its outcome's
memory and allocator state. -/
theorem denoteCode_callVoid_some (calls : Calls) (env : Env) (s : State)
    (callee : String) (args : List (Ty × Operand)) (vs : List Value) (r : CallOutcome)
    (hargs : evalOperands (stateAt env s) args = some vs)
    (hsome : calls callee vs s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.callVoid callee args :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ ?_]
  simp only [evalInstr]
  rw [hargs]
  dsimp only [stateAt]
  rw [hsome]

/-- The lifetime marker's two arguments: the byte count and the object. -/
theorem evalOperands_lifetimeMark {env : Env} {s : State} {q w : Nat} {ptr : String}
    (hd : lookupName env ptr = some (.ptr q)) :
    evalOperands (stateAt env s)
      [((Ty.int 64), (Operand.imm (Const.int 64 (BitVec.ofNat 64 w)))),
       (Ty.ptr, (Operand.reg ptr))] = some [.int 64 (BitVec.ofNat 64 w), .ptr q] := by
  simp only [evalOperands, evalOperand, Const.toValue, stateAt, hd]

/-! ### The tier-2 site: `if.end268`'s `@num_el_el1` call

The block's three instructions, as its pin states them. -/

/-- `if.end268`, from its `findBlock` pin. -/
def numFastIfEnd268Instrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
       (Ty.ptr, (Operand.reg "%d269"))],
   Instr.call "%call270" (Ty.int 32) "num_el_el1"
      [((Ty.int 64), (Operand.reg "%add244")),
       ((Ty.int 64), (Operand.reg "%sub231")),
       (Ty.ptr, (Operand.reg "%d269"))],
   Instr.icmp "%tobool271.not" (IPred.eq) 32 (Operand.reg "%call270")
     (Operand.imm (Const.int 32 0x00000000#32))]

/-- The pin, at the named list: the block is the parse's. -/
theorem numFast_findBlock_if_end268_named :
    numFastBody.findBlock "if.end268" =
      some ⟨"if.end268", numFastIfEnd268Instrs,
        Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by
  simpa only [numFastIfEnd268Instrs] using numFast_findBlock_if_end268

/-- The block's `denoteCode` is `none`: the lifetime marker resolves and the
kernel's call does not. -/
theorem numFast_ifEnd268_denote_none {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    denoteCode s2HelperCalls numFastIfEnd268Instrs (stateAt env s) = none := by
  unfold numFastIfEnd268Instrs
  rw [denoteCode_callVoid_some _ _ _ _ _ _ _
    (evalOperands_lifetimeMark (s := s) hd) (s2HelperCalls_lifetime_start _ _ _) _]
  rw [denoteCode_call_none _ _ _ _ _ _ _ (vs := [.int 64 a, .int 64 b, .ptr q])
    (by simp only [evalOperands, evalOperand, stateAt, ha, hb, hd])
    (s2HelperCalls_num_el_el1 _ _ _) _]

/-- The tier-2 site's step is `ub`. -/
theorem numFast_step_ifEnd268_ub {env : Env} {s : State} {a b : BitVec 64} {q : Nat}
    (hpc : s.pc = "if.end268")
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    step s2HelperCalls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.end268", numFastIfEnd268Instrs,
        Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by
    rw [show (stateAt env s).pc = "if.end268" from hpc]
    exact numFast_findBlock_if_end268_named
  simp only [step, hfind, numFast_ifEnd268_denote_none ha hb hd]

/-- **The tier-2 arm is `ub` at the walk's environment**: one control step from
`if.end268` stops. -/
theorem numFast_runFuel_ifEnd268_ub {env : Env} {s : State} {a b : BitVec 64}
    {q k : Nat} (hpc : s.pc = "if.end268")
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    runFuel s2HelperCalls (k + 1) numFastBody (stateAt env s) = some .ub := by
  simp only [runFuel, numFast_step_ifEnd268_ub hpc ha hb hd]

/-! ### The fast path's site: `while.body.preheader`'s `@num_d8_el1` call

The eight-digit reader is called from the scan's SIMD run, so it is on the path
of every lexeme whose integer part or fraction has at least eight digits left
inside the counter's guard.  The block's own chain is the lifetime marker, the
pointer arithmetic and the call. -/

/-- `while.body.preheader`, from its `findBlock` pin. -/
def numFastWhileBodyPreheaderInstrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8"))],
   Instr.gep "%add.ptr930" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc26"),
   Instr.call "%call931" (Ty.int 32) "num_d8_el1"
      [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))],
   Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931")
     (Operand.imm (Const.int 32 0x00000000#32))]

/-- The pin, at the named list. -/
theorem numFast_findBlock_while_body_preheader_named :
    numFastBody.findBlock "while.body.preheader" =
      some ⟨"while.body.preheader", numFastWhileBodyPreheaderInstrs,
        Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩ := by
  simpa only [numFastWhileBodyPreheaderInstrs] using numFast_findBlock_while_body_preheader

/-- A lookup one cell deeper than the environment it is stated at: the head's
cell is another name.  The named arguments keep the name comparison decideable
where the environment is a literal cons. -/
theorem lookupName_cons_tail {env : Env} {k n : String} {v x : Value} (hne : k ≠ n)
    (h : lookupName env n = some x) : lookupName ((k, v) :: env) n = some x := by
  rw [lookupName_cons_ne v env hne]; exact h

/-- The block's `denoteCode` is `none`: the marker resolves, the reader's call
does not. -/
theorem numFast_whileBodyPreheader_denote_none {env : Env} {s : State} {a v8a : Nat}
    {idx : BitVec 64}
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    denoteCode s2HelperCalls numFastWhileBodyPreheaderInstrs (stateAt env s) = none := by
  have h1 : denoteCode s2HelperCalls numFastWhileBodyPreheaderInstrs (stateAt env s) =
      denoteCode s2HelperCalls
        [Instr.gep "%add.ptr930" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc26"),
         Instr.call "%call931" (Ty.int 32) "num_d8_el1"
           [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))],
         Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931")
           (Operand.imm (Const.int 32 0x00000000#32))]
        (stateAt env { s with mem := s.mem, next := s.next }) :=
    denoteCode_callVoid_some s2HelperCalls env s "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) hv8) (s2HelperCalls_lifetime_start _ _ _) _
  rw [h1]
  have h2 : denoteCode s2HelperCalls
        [Instr.gep "%add.ptr930" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc26"),
         Instr.call "%call931" (Ty.int 32) "num_d8_el1"
           [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))],
         Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931")
           (Operand.imm (Const.int 32 0x00000000#32))]
        (stateAt env { s with mem := s.mem, next := s.next }) =
      denoteCode s2HelperCalls
        [Instr.call "%call931" (Ty.int 32) "num_d8_el1"
           [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))],
         Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931")
           (Operand.imm (Const.int 32 0x00000000#32))]
        (stateAt (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          { s with mem := s.mem, next := s.next }) :=
    denoteCode_gep8_reg s2HelperCalls env { s with mem := s.mem, next := s.next }
      "%add.ptr930" "%p" "%inc26" hp ho hpos _
  rw [h2]
  have h3 : evalOperands
      (stateAt (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
        { s with mem := s.mem, next := s.next })
      [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))]
      = some [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a] := by
    have hcell : lookupName
        (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%add.ptr930"
        = some (.ptr (a + (idx.signExtend 64).toNat)) :=
      lookupName_cons_self "%add.ptr930" (.ptr (a + (idx.signExtend 64).toNat)) env
    have htail : lookupName
        (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%v8"
        = some (.ptr v8a) :=
      lookupName_cons_tail (k := "%add.ptr930")
        (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
    simp only [evalOperands, evalOperand, stateAt, hcell, htail]
  rw [denoteCode_call_none s2HelperCalls
    (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
    { s with mem := s.mem, next := s.next } "%call931" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr930")), (Ty.ptr, (Operand.reg "%v8"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a] h3
    (s2HelperCalls_num_d8_el1 _ _ _) _]

/-- The fast path's site's step is `ub`. -/
theorem numFast_step_whileBodyPreheader_ub {env : Env} {s : State} {a v8a : Nat}
    {idx : BitVec 64} (hpc : s.pc = "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    step s2HelperCalls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"while.body.preheader", numFastWhileBodyPreheaderInstrs,
        Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩ := by
    rw [show (stateAt env s).pc = "while.body.preheader" from hpc]
    exact numFast_findBlock_while_body_preheader_named
  simp only [step, hfind, numFast_whileBodyPreheader_denote_none hp ho hv8 hpos]

/-- **The fast path's reader is `ub` at the walk's environment.** -/
theorem numFast_runFuel_whileBodyPreheader_ub {env : Env} {s : State} {a v8a : Nat}
    {idx : BitVec 64} {k : Nat} (hpc : s.pc = "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    runFuel s2HelperCalls (k + 1) numFastBody (stateAt env s) = some .ub := by
  simp only [runFuel, numFast_step_whileBodyPreheader_ub hpc hp ho hv8 hpos]

/-! ### The fallback's site: `if.then178.i.i`'s `@stk_mul_u64` call

The fallback's own conversion is inlined, but its big multiply is not: the
inlined walk reaches `stk_mul_u64` inside the exponent-scaling loop, so the
fallback arm stops here too, after the block's leading `phi`, the table load and
the call. -/

/-- `if.then178.i.i`, from its `findBlock` pin. -/
def numFastIfThen178Instrs : List Instr :=
  [Instr.phi "%k168.0.lcssa829.i.i" (Ty.int 64)
      [("while.end176.thread.i.i", (Operand.reg "%sub169.i.i")),
       ("while.end176.i.i", (Operand.reg "%sub175.i.i"))],
   Instr.gep "%arrayidx180.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10")
     (Operand.reg "%k168.0.lcssa829.i.i"),
   Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
   Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
     ((Ty.int 64), (Operand.reg "%107"))]]

/-- The pin, at the named list. -/
theorem numFast_findBlock_if_then178_named :
    numFastBody.findBlock "if.then178.i.i" =
      some ⟨"if.then178.i.i", numFastIfThen178Instrs, Term.br "if.end198.i.i"⟩ := by
  simpa only [numFastIfThen178Instrs] using numFast_findBlock_if_then178_i_i

/-- The index's own chain step: a `getelementptr i64` adds eight bytes per step. -/
theorem denoteCode_gep_i64 (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 64) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * (Ty.int 64).sizeBytes)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ ?_]
  simp only [evalInstr, evalOperand, stateAt, hb, ho, hpos, ite_true, State.bind]

/-- The `phi`'s incoming operand at the block's own predecessor. -/
theorem numFast_ifThen178_phiIncoming :
    phiIncoming "while.end176.i.i"
      [("while.end176.thread.i.i", (Operand.reg "%sub169.i.i")),
       ("while.end176.i.i", (Operand.reg "%sub175.i.i"))]
      = some (Operand.reg "%sub175.i.i") := by
  simp [phiIncoming]

/-- The block's `denoteCode` is `none`: the `phi`, the table load and the call,
of which the call has no answer. -/
theorem numFast_ifThen178_denote_none {env : Env} {s : State} {p10 pow : Nat}
    {k v : BitVec 64}
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    denoteCode s2HelperCalls numFastIfThen178Instrs (stateAt env s) = none := by
  have h1 : denoteCode s2HelperCalls numFastIfThen178Instrs (stateAt env s) =
      denoteCode s2HelperCalls
        [Instr.gep "%arrayidx180.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10")
           (Operand.reg "%k168.0.lcssa829.i.i"),
         Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
         Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
           ((Ty.int 64), (Operand.reg "%107"))]]
        (stateAt (("%k168.0.lcssa829.i.i", .int 64 k) :: env) s) :=
    denoteCode_phi s2HelperCalls env s "%k168.0.lcssa829.i.i" (Ty.int 64)
      [("while.end176.thread.i.i", (Operand.reg "%sub169.i.i")),
       ("while.end176.i.i", (Operand.reg "%sub175.i.i"))]
      (p := "while.end176.i.i") (op := Operand.reg "%sub175.i.i") (v := .int 64 k)
      hpre numFast_ifThen178_phiIncoming
      (by simp only [evalOperand, stateAt, hk])
      _ (by simp only [startsWithPhi])
  rw [h1]
  have hbase : lookupName (("%k168.0.lcssa829.i.i", .int 64 k) :: env) "@NUMF_EL1_P10"
      = some (.ptr p10) :=
    lookupName_cons_tail (k := "%k168.0.lcssa829.i.i") (v := .int 64 k) (by decide) hg
  have hidx : lookupName (("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%k168.0.lcssa829.i.i"
      = some (.int 64 k) := lookupName_cons_self "%k168.0.lcssa829.i.i" (.int 64 k) env
  have h2 : denoteCode s2HelperCalls
        [Instr.gep "%arrayidx180.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10")
           (Operand.reg "%k168.0.lcssa829.i.i"),
         Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
         Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
           ((Ty.int 64), (Operand.reg "%107"))]]
        (stateAt (("%k168.0.lcssa829.i.i", .int 64 k) :: env) s) =
      denoteCode s2HelperCalls
        [Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
         Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
           ((Ty.int 64), (Operand.reg "%107"))]]
        (stateAt (("%arrayidx180.i.i",
            .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
          :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) s) :=
    denoteCode_gep_i64 s2HelperCalls (("%k168.0.lcssa829.i.i", .int 64 k) :: env) s
      "%arrayidx180.i.i" "@NUMF_EL1_P10" "%k168.0.lcssa829.i.i" hbase hidx hpos _
  rw [h2]
  have hload : lookupName
      (("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
        :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%arrayidx180.i.i"
      = some (.ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) :=
    lookupName_cons_self "%arrayidx180.i.i"
      (.ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
      (("%k168.0.lcssa829.i.i", .int 64 k) :: env)
  rw [denoteCode_load64 s2HelperCalls
    (("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
      :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) s
    "%107" "%arrayidx180.i.i" hload hread _]
  have hargs : evalOperands
      (stateAt (("%107", .int 64 v) :: ("%arrayidx180.i.i",
          .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
        :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) s)
      [(Ty.ptr, (Operand.reg "%pow.i.i")), ((Ty.int 64), (Operand.reg "%107"))]
      = some [.ptr pow, .int 64 v] := by
    have h107 : lookupName
        (("%107", .int 64 v) :: ("%arrayidx180.i.i",
          .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
          :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%107" = some (.int 64 v) :=
      lookupName_cons_self "%107" (.int 64 v)
        (("%arrayidx180.i.i",
          .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
          :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env)
    have hpow' : lookupName
        (("%107", .int 64 v) :: ("%arrayidx180.i.i",
          .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
          :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%pow.i.i" = some (.ptr pow) :=
      lookupName_cons_tail (k := "%107") (v := .int 64 v) (by decide)
        (lookupName_cons_tail (k := "%arrayidx180.i.i")
          (v := .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) (by decide)
          (lookupName_cons_tail (k := "%k168.0.lcssa829.i.i") (v := .int 64 k) (by decide) hpow))
    simp only [evalOperands, evalOperand, stateAt, h107, hpow']
  rw [denoteCode_callVoid_none s2HelperCalls
    (("%107", .int 64 v) :: ("%arrayidx180.i.i",
        .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
      :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env) s
    "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")), ((Ty.int 64), (Operand.reg "%107"))]
    [.ptr pow, .int 64 v] hargs (s2HelperCalls_stk_mul_u64 _ _ _) _]

/-- The fallback's site's step is `ub`. -/
theorem numFast_step_ifThen178_ub {env : Env} {s : State} {p10 pow : Nat}
    {k v : BitVec 64}
    (hpc : s.pc = "if.then178.i.i")
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    step s2HelperCalls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.then178.i.i", numFastIfThen178Instrs, Term.br "if.end198.i.i"⟩ := by
    rw [show (stateAt env s).pc = "if.then178.i.i" from hpc]
    exact numFast_findBlock_if_then178_named
  simp only [step, hfind, numFast_ifThen178_denote_none hpre hk hg hpos hread hpow]

/-- **The fallback's big multiply is `ub` at the walk's environment.** -/
theorem numFast_runFuel_ifThen178_ub {env : Env} {s : State} {p10 pow : Nat}
    {k v : BitVec 64} {n : Nat}
    (hpc : s.pc = "if.then178.i.i")
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    runFuel s2HelperCalls (n + 1) numFastBody (stateAt env s) = some .ub := by
  simp only [runFuel, numFast_step_ifThen178_ub hpc hpre hk hg hpos hread hpow]

/-! ### The arm, stated at the body

The three `ub` facts above are the *environment's* half of the boundary.  The
other half is the staging: the conversion reads two tables whose contents the
contract's `s2NumFastPre` does not name — it fixes the four arguments and the
lexeme, and says nothing about `@NUMF_EL1_P10` or `@NUMF_EL1_POW10` — while the
body's tier-1 and fallback arithmetic is a function of them.  A body-level proof
of the numeric arm is therefore a statement about a `Calls` selection that
answers the three callees and a staging that stages both tables; the definition
below is that statement, so the obligation a later proof discharges is a value
rather than a paragraph.  It is not claimed here. -/

/-- The two tables, as the emitted initialisers give them: `NUMF_EL1_P10[i]` is
`10 ^ i` for the twenty entries a `uint64` holds, and `NUMF_EL1_POW10[i]` is the
binary64 `10 ^ i` for the twenty-three entries the tier-1 expression reads,
stated as the encoding `uitofpBits` gives a value below `2 ^ 53` (every `10 ^ i`,
`i ≤ 22`, is one: `5 ^ 22 < 2 ^ 53`). -/
def NumFastTables (env : Env) (mem : Mem) : Prop :=
  ∃ p10 pd : Nat,
    lookupName env "@NUMF_EL1_P10" = some (.ptr p10) ∧
    lookupName env "@NUMF_EL1_POW10" = some (.ptr pd) ∧
    (∀ i, i < 20 → readBytes mem (p10 + 8 * i) 8 = some (natToBytes ((10 : Nat) ^ i) 8)) ∧
    (∀ i, i < 23 →
      readBytes mem (pd + 8 * i) 8 = some (natToBytes (uitofpBits ((10 : Nat) ^ i)).toNat 8))

/-- **The numeric arm at the pinned body.**  At a staging whose four arguments
are the walk's, whose lexeme at `p` is a well-formed number's (`lex` is the
bytes, and `literal lex` the lexeme they denote), and whose two tables are
`NumFastTables`, the body runs — under a `Calls` selection that answers its
three out-of-line callees — to its return, writing `strtodSpec`'s eight bytes at
`out`, leaving `err` untouched, the allocator cursor unchanged, and every byte
outside the two slots the caller's.

The `calls` parameter is not decoration: at the walk's own `s2HelperCalls` the
run is `ub` at each callee (the theorems above), so no instantiation of this
statement exists there. -/
def NumFastBodyArm (calls : Calls) : Prop :=
  ∀ (d : Decimal) (lex : List UInt8) (env : Env) (s : State) (p out err : Nat),
    d.wellFormed →
    ByteString.literal lex = d.lexeme →
    lookupName env "%p" = some (.ptr p) →
    lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 lex.length)) →
    lookupName env "%out" = some (.ptr out) →
    lookupName env "%err" = some (.ptr err) →
    readBytes s.mem p lex.length = some lex →
    NumFastTables env s.mem →
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      o.next = s.next ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)]

/-- **The arm is not instantiated at the walk's environment.**  The tier-2
site's step is `ub` there (`numFast_step_ifEnd268_ub`), so the arm's conclusion
— a returned value with `out` written — has no witness in that `Calls`; the
`calls` parameter is what a body-level proof must supply first. -/
theorem numFastArm_witness_is_ub :
    ∃ (env : Env), step s2HelperCalls numFastBody
      (stateAt env { env := [], mem := [], next := 0, pc := "if.end268", pre := none }) = .ub := by
  refine ⟨[("%add244", .int 64 0), ("%sub231", .int 64 0), ("%d269", .ptr 0)], ?_⟩
  exact numFast_step_ifEnd268_ub rfl rfl rfl rfl

/-! ### Axiom footprints

`#print axioms` on the boundary theorems, pinned with `#guard_msgs` so the build
checks the footprint rather than printing it.  The instrument prints `sorryAx`
for a `sorry`-backed declaration — §7.6's control — and it did here while the arm
definition was malformed: the failed elaboration left `sorryAx` in
`NumFastBodyArm`'s footprint, which is why the pin below is evidence and not
decoration. -/

/-- info: 'LeanLLVM.Refinement.numFast_entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_entry_denote

/-- info: 'LeanLLVM.Refinement.s2HelperCalls_num_d8_el1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s2HelperCalls_num_d8_el1

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd268_denote_none

/-- info: 'LeanLLVM.Refinement.numFast_runFuel_ifEnd268_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_runFuel_ifEnd268_ub

/-- info: 'LeanLLVM.Refinement.numFast_whileBodyPreheader_denote_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_whileBodyPreheader_denote_none

/-- info: 'LeanLLVM.Refinement.numFast_runFuel_whileBodyPreheader_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_runFuel_whileBodyPreheader_ub

/-- info: 'LeanLLVM.Refinement.numFast_ifThen178_denote_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifThen178_denote_none

/-- info: 'LeanLLVM.Refinement.NumFastBodyArm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NumFastBodyArm

end LeanLLVM.Refinement
