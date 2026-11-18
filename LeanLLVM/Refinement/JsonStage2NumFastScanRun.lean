/-
`num_fast_el1`'s scan, from the dispatch to the merge: the exponent's marker nest,
the merge blocks, and the composition of the digit runs with the dispatch around
them.

`JsonStage2NumFastScan` fixes the runs' `BoundLoop` shape and
`JsonStage2NumFastDigitRuns` discharges the three instances, but each instance is
stated at the run's own start.  `JsonStage2NumFastStarts` closes the dispatch's
straight-line steps into each run's start and names two regions it does not
cover: the two eight-digit fast paths, and the exponent's marker nest between
`if.end144` and `lor.lhs.false180`.  This module is the nest, the merge blocks
after the exponent run, and the composed scan.

**The nest.**  Eleven blocks decide whether the lexeme carries an exponent and
what its sign is: `land.lhs.true147` loads the byte at `%i.10` and `NodeBlock`
pivots on a signed compare against `0x65`, so `LeafBlock` tests `0x45` and
`LeafBlock1` tests `0x65`; either leaf's equality takes `if.then157` and anything
else `if.end226` — the lexeme has no exponent, and the merge reads `%exp10.4 = 0`
there.  `if.then157` forms `%inc158 = %i.10 + 1` and tests it against the
length; `land.lhs.true161`/`NodeBlock7`/`LeafBlock5`/`LeafBlock3` read the byte
at `%inc158` against `0x2d` and `0x2b`; `if.then171` sets `%i.11 = %i.10 + 2`
with `%esign.0 = (%22 != 0x2d)`, and `if.end177`'s other three edges set
`%i.11 = %inc158` with `%esign.0 = 1`.  The pivot's signedness never has to be
decided for a byte that is not a marker: whichever leaf the pivot reaches, the
leaf's equality is read on the same byte and fails.

**The merge, after the exponent run.**  `cleanup223.thread` folds the run's
accumulator and the exponent's sign into `%spec.select446`, `if.end226` carries
the accumulator and the stop index, and its equality test against `%n` is what
opens `if.end230`.  A lexeme that stops short of its end does not reach the
merge: `if.end226` takes `if.then229`, and `cleanup223`/`if.then229` are the
refusals that store the offset at `%err`.

**What the composition fixes.**  `nestTo157_e`/`nestTo157_E` take the marker's
byte through `land.lhs.true147`/`NodeBlock`/`LeafBlock*` to `if.then157`;
`nestFrom157_nosign`/`nestFrom157_sign` carry it from there to
`lor.lhs.false180` with `%i.11 = %i.10 + 1`, `%esign.0 = 1` or
`%i.11 = %i.10 + 2`, `%esign.0 = (%22 != 0x2d)` — the registers `expRun_start`
consumes — and `nest_nomarker` takes the no-exponent branch to `if.end226`.
`cleanup223.thread`'s step is stated at both of the run's exits,
`expMerge_run_inc` composes the back edge's two-step merge into `mergeEntry`, the
state `JsonStage2NumFastTier1`'s `t1_ifEnd230_denote` names, and the head edge —
whose index is short of the length — is the refusal: `ifThen229_step_refuse`
stores it at `%err` and `cleanup300_step_refuse` returns zero.  The scan's own
composition is `intScan_run`: from `entry` at a non-empty lexeme whose `int` part
leads with `'1' … '9'` and whose eight-digit guard is refused, the body reaches
the integer run's exit predicate within `8 + (n - i0 + 1) * 4` control steps —
a term of the arguments, not of the trip count — carrying the counters and the
accumulator's fold.  `intScan_end230` is the same trace with the arm fixed: for a
lexeme whose bytes from the run's start to its end are all digits, the exit is
the end-of-lexeme one and the body reaches `if.end230` within the same bound.
`intScan_run`'s calls are arbitrary, because the blocks it crosses call nothing:
the run instance it composes is stated at an arbitrary `Calls`
(`JsonStage2NumFastDigitRuns.intRunBoundLoop`) and the dispatch's steps are too,
so the trace instantiates at the walk's `s2HelperCalls` and at the conversion's
`stage2NumFastCalls epow` alike.

**The exit's cells, and the transport.**  The runs' exit predicates hand what a
composition reads past them, because the exit state is existential to that
composition: `%p` and `%n` (every successor reads them), the predecessor the
merge's `phi` selection depends on, `%7`/`%17` (the counts the merge's phis
read), and — on the non-digit arms — the byte the run stopped on with its
non-digit answer.  `intRunEndWord` and `fracRunEndWord` are the two
end-of-lexeme arms at exactly the lexeme's end, so `%ip.4`'s move into
`%ip.5708717729` is `ifEnd230_step_end62` fed by the exit's own cells
(`JsonStage2NumFastSeams.intRunExit_gate`), and `%7`'s reading as the digit
count is the same statement.

**The tie's arithmetic, and half the register tie.**  The runs carry
`digitFold`'s value; the model folds the decimal part's own bytes.  `intRunExit_end230`
and `fracRunExit_end230` expose the run's index and word at the `if.end230` edge,
`digitFold_tie` and `digitsNat_word` read such a word as the part's fold with the
`19`-digit guard inert, and `ip_word_digitsNat`/`fr_word_digitsNat` are the two
premises `JsonStage2NumFastTier1`'s `t1_add244_eq_mantissa` takes — `%ip`'s and
`%fr`'s ties to `Decimal.digitsNat`.

**What is not proved here.**  Four things, each named at the block or the
register it stops at.

*The two eight-digit fast paths* (`while.body`/`cleanup` at `if.then22`,
`while.body100`/`cleanup112` at `while.cond91.preheader`) are not this module's,
and every dispatch step it composes is the one `JsonStage2NumFastStarts` proves
behind their guard: the compositions are the branch on which
`%cmp27564.not`/`%cmp93583.not` are one, i.e. the guard refused.  A lexeme with
nine or more digits left takes the other branch, and that branch's loop is the
eight-digit reader's.

*The exponent run's exit shape* is not decided by any theorem in the tree:
`expRunExit` names the two exits' registers, not which exit the run took.
`expMerge_run_inc` needs no index hypothesis, because `if.end216`'s
`%i.12.lcssa.ph` is `%n` by construction and the test is its reflexivity; the
head edge's index is the run's own counter, short of the length, and its tail is
the refusal (`ifThen229_step_refuse`, `cleanup300_step_refuse`).  A well-formed
lexeme's exponent digits are maximal by the grammar, so the run's exit is the
back edge's; that argument is the arm's, not this module's.

*The scan's middle* is one run on the integer part's route and pieces elsewhere:
`intScan_run` reaches the integer run's exit, `intScan_end230` fixes the arm and
reaches `if.end230`, and `JsonStage2NumFastSeams.intScan_merge` appends the
merge block's step; `fracScan_run` runs the fraction dispatch
(`land.lhs.true71` → `land.lhs.true119`) and the fraction run to its exit,
`nestEntry_run` carries the fraction run's `if.end144` exit into the nest, and
the nest, the merge and `if.end230`'s bound edge are proved.  What is *not*
composed is the fraction's and the exponent's routes to the merge: the integer
run's `if.end68` exit to `land.lhs.true71`
(`JsonStage2NumFastStarts.ifEnd68_step`), the fraction run's `if.end144` exit's
predecessor (`ifEnd144_denote_frac` takes it as a hypothesis), and the chain from
`land.lhs.true71`'s no-dot edge (`landLhsTrue71_step_nodot`) straight to
`if.end144` are each one block, not one trace.

*The reader's agreement* — `num_d8_el1`'s answer at the fast path against the
eight bytes at its pointer — is untouched: `JsonStage2NumFastCalls` models the
reader, and no theorem yet reads its model against `readBytes`.

-/
import LeanLLVM.Refinement.JsonStage2NumFastStarts
import LeanLLVM.Refinement.JsonStage2NumFastTier1

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

/- The nest's own vocabulary.  Namespaced because the escape bodies carry blocks
named `NodeBlock`/`if.end` too, and their lemmas are already in
`LeanLLVM.Refinement`. -/
namespace NumFastScanRun

-- The scan's seams run through the digit runs' region, which calls nothing:
-- the dispatch's blocks are the sign and lead-digit reads, the `.` test and the
-- marker nest, and the nest's blocks are byte loads and comparisons.  A seam is
-- therefore a statement about an arbitrary `Calls`, which is what lets a caller
-- at `stage2NumFastCalls epow` compose it with a run proved once.
variable {calls : Calls}

/-! ### `if.end144`: the integer part's four exits

The merge of the integer part reads three `phi`s — the fraction's accumulator,
its digit count and the index the scan stopped at — and tests the index against
the length.  The four edges are `land.lhs.true71` and `if.end68` (a `'.'` absent
or refused, so no fraction), `while.end115` (no digit after the `'.'`, or the
`'.'` at the end of the lexeme) and `land.lhs.true119` (the fraction run's
non-digit exit).  The builder is the block's own environment; `%i.10` is
carried as the word the edge wrote, because the nest reads it and nothing else
here does. -/

/-- The three `phi`s of `if.end144`. -/
def ifEnd144PhiEnv (env : Env) (fr5 fdig4 i10 : BitVec 64) : Env :=
  ("%i.10", .int 64 i10) :: ("%fdig.4", .int 64 fdig4) :: ("%fr.5", .int 64 fr5) :: env

/-- `if.end144`'s environment: the three `phi`s and the index's test. -/
def ifEnd144Env (env : Env) (fr5 fdig4 i10 nv : BitVec 64) : Env :=
  ("%cmp145", .int 1 (evalICmp .ult i10 nv)) :: ifEnd144PhiEnv env fr5 fdig4 i10

/-- `if.end144` from a `'.'` that is not followed by a digit, or that ends the
lexeme: no fraction, so the fraction's accumulator is zero and the count is
zero. -/
theorem ifEnd144_denote_dot {calls : Calls} {env : Env} {s : State}
    {i5 nv : BitVec 64}
    (hpre : s.pre = some "land.lhs.true71")
    (hi : lookupName env "%i.5" = some (.int 64 i5))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env 0 0 i5 nv) s) := by
  unfold numFastIfEnd144Instrs
  block_eval

/-- `if.end144` from the integer run's exit without a `'.'`: the same three
values as the `'.'`-refused edge, with `%i.5` the integer run's stop index. -/
theorem ifEnd144_denote_nodot {calls : Calls} {env : Env} {s : State}
    {i5 nv : BitVec 64}
    (hpre : s.pre = some "if.end68")
    (hi : lookupName env "%i.5" = some (.int 64 i5))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env 0 0 i5 nv) s) := by
  unfold numFastIfEnd144Instrs
  block_eval

/-- `if.end144` from `while.end115`: the fraction's accumulator and count are
the dispatch's zeroes and the index is `%i.6552`. -/
theorem ifEnd144_denote_end {calls : Calls} {env : Env} {s : State}
    {fr fdig i nv : BitVec 64}
    (hpre : s.pre = some "while.end115")
    (hfr : lookupName env "%fr.0556" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.0554" = some (.int 64 fdig))
    (hi : lookupName env "%i.6552" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env fr fdig i nv) s) := by
  unfold numFastIfEnd144Instrs
  block_eval

/-- `if.end144` from the fraction run's non-digit exit. -/
theorem ifEnd144_denote_frac {calls : Calls} {env : Env} {s : State}
    {fr fdig i nv : BitVec 64}
    (hpre : s.pre = some "land.lhs.true119")
    (hfr : lookupName env "%fr.3593" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hi : lookupName env "%i.9595" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env fr fdig i nv) s) := by
  unfold numFastIfEnd144Instrs
  block_eval

/-- `if.end144`'s step, once its chain is fixed: a test taken leaves for the
marker's block, a test refused for the merge that carries no exponent. -/
theorem ifEnd144_step {calls : Calls} {env : Env} {s : State}
    {fr fdig i10 nv : BitVec 64}
    (hpc : s.pc = "if.end144")
    (hden : denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env fr fdig i10 nv) s))
    (hbit : evalICmp .ult i10 nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd144Env env fr fdig i10 nv)
        { s with pc := "land.lhs.true147", pre := some "if.end144" }) := by
  refine numFast_step_at
    (s' := stateAt (ifEnd144Env env fr fdig i10 nv) s)
    (b := ⟨"if.end144", numFastIfEnd144Instrs,
      Term.condbr (Operand.reg "%cmp145") "land.lhs.true147" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd144Instrs] using numFast_findBlock_if_end144
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd144Env env fr fdig i10 nv) "%cmp145"
        = some (.int 1 (evalICmp .ult i10 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp145" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `if.end144`'s step to the merge: the index is not inside the lexeme, so
there is no exponent marker to read. -/
theorem ifEnd144_step_end {calls : Calls} {env : Env} {s : State}
    {fr fdig i10 nv : BitVec 64}
    (hpc : s.pc = "if.end144")
    (hden : denoteCode calls numFastIfEnd144Instrs (stateAt env s) =
      some (stateAt (ifEnd144Env env fr fdig i10 nv) s))
    (hbit : evalICmp .ult i10 nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd144Env env fr fdig i10 nv)
        { s with pc := "if.end226", pre := some "if.end144" }) := by
  refine numFast_step_at
    (s' := stateAt (ifEnd144Env env fr fdig i10 nv) s)
    (b := ⟨"if.end144", numFastIfEnd144Instrs,
      Term.condbr (Operand.reg "%cmp145") "land.lhs.true147" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd144Instrs] using numFast_findBlock_if_end144
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd144Env env fr fdig i10 nv) "%cmp145"
        = some (.int 1 (evalICmp .ult i10 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp145" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `land.lhs.true147`, `NodeBlock`, `LeafBlock`, `LeafBlock1`

The marker's byte is loaded once, at `%arcidx148`, and the three tests read that
one cell: the pivot is a signed compare against `0x65`, the two leaves equalities
against `0x45` and `0x65`.  Neither leaf's equality is reached by a byte the
pivot would route the other way — `%Pivot`'s bit is decidable and the pivot is
signed, so `0x45` pivots to `LeafBlock` and `0x65` to `LeafBlock1`. -/

/-- `land.lhs.true147`'s two instructions. -/
def t147Instrs : List Instr :=
  [Instr.gep "%arrayidx148" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.10"),
   Instr.load "%21" (Ty.int 8) (Operand.reg "%arrayidx148")]

theorem findBlock_t147 :
    numFastBody.findBlock "land.lhs.true147" =
      some ⟨"land.lhs.true147", t147Instrs, Term.br "NodeBlock"⟩ := by
  simpa only [t147Instrs] using numFast_findBlock_land_lhs_true147

/-- `land.lhs.true147`'s environment: the address and the byte. -/
def t147Env (env : Env) (a i10 : Nat) (b1 : UInt8) : Env :=
  ("%21", .int 8 (JsonScanLane.vByte b1)) ::
  ("%arrayidx148", .ptr (a + i10)) :: env

theorem t147_denote {calls : Calls} {env : Env} {s : State} {a i10 : Nat} {b1 : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hj : i10 < 2 ^ 63)
    (hread : readByte s.mem (a + i10) = some b1) :
    denoteCode calls t147Instrs (stateAt env s) =
      some (stateAt (t147Env env a i10 b1) s) := by
  unfold t147Instrs
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx148" "%p" "%i.10" hp hi
    (by rw [sExt_ofNat64 hj]; exact hj) _]
  rw [sExt_ofNat64 hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%21" "%arrayidx148" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, t147Env]

theorem t147_step {calls : Calls} {env : Env} {s : State} {a i10 : Nat} {b1 : UInt8}
    (hpc : s.pc = "land.lhs.true147")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hj : i10 < 2 ^ 63)
    (hread : readByte s.mem (a + i10) = some b1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t147Env env a i10 b1)
        { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) := by
  refine numFast_step_at (s' := stateAt (t147Env env a i10 b1) s)
    (b := ⟨"land.lhs.true147", t147Instrs, Term.br "NodeBlock"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using findBlock_t147
  · simpa only [denoteCode_nil] using t147_denote (calls := calls) hp hi hj hread
  · simp only [execTerm, stateAt, hpc]

/-- `NodeBlock`'s environment: the pivot's bit. -/
def nodeBlockEnv (env : Env) (b1 : UInt8) : Env :=
  ("%Pivot", .int 1 (evalICmp .slt (JsonScanLane.vByte b1) 0x65#8)) :: env

theorem nodeBlock_denote {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1))) :
    denoteCode calls
        [Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%21")
          (Operand.imm (Const.int 8 0x65#8))]
        (stateAt env s) =
      some (stateAt (nodeBlockEnv env b1) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%Pivot" "%21" .slt
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, nodeBlockEnv]

theorem nodeBlock_step {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "NodeBlock")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .slt (JsonScanLane.vByte b1) 0x65#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (nodeBlockEnv env b1)
        { s with pc := "LeafBlock", pre := some "NodeBlock" }) := by
  refine numFast_step_at (s' := stateAt (nodeBlockEnv env b1) s)
    (b := ⟨"NodeBlock",
      [Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x65#8))],
      Term.condbr (Operand.reg "%Pivot") "LeafBlock" "LeafBlock1"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_NodeBlock
  · simpa only [denoteCode_nil] using nodeBlock_denote (calls := calls) hb
  · have hlk : lookupName (nodeBlockEnv env b1) "%Pivot"
        = some (.int 1 (evalICmp .slt (JsonScanLane.vByte b1) 0x65#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%Pivot" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem nodeBlock_step_false {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "NodeBlock")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .slt (JsonScanLane.vByte b1) 0x65#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (nodeBlockEnv env b1)
        { s with pc := "LeafBlock1", pre := some "NodeBlock" }) := by
  refine numFast_step_at (s' := stateAt (nodeBlockEnv env b1) s)
    (b := ⟨"NodeBlock",
      [Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x65#8))],
      Term.condbr (Operand.reg "%Pivot") "LeafBlock" "LeafBlock1"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_NodeBlock
  · simpa only [denoteCode_nil] using nodeBlock_denote (calls := calls) hb
  · have hlk : lookupName (nodeBlockEnv env b1) "%Pivot"
        = some (.int 1 (evalICmp .slt (JsonScanLane.vByte b1) 0x65#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%Pivot" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock`'s environment: the `'E'` equality's bit. -/
def leafBlockEnv (env : Env) (b1 : UInt8) : Env :=
  ("%SwitchLeaf", .int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x45#8)) :: env

theorem leafBlock_denote {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1))) :
    denoteCode calls
        [Instr.icmp "%SwitchLeaf" (IPred.eq) 8 (Operand.reg "%21")
          (Operand.imm (Const.int 8 0x45#8))]
        (stateAt env s) =
      some (stateAt (leafBlockEnv env b1) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%SwitchLeaf" "%21" .eq
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, leafBlockEnv]

theorem leafBlock_step_marker {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "LeafBlock")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b1) 0x45#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlockEnv env b1)
        { s with pc := "if.then157", pre := some "LeafBlock" }) := by
  refine numFast_step_at (s' := stateAt (leafBlockEnv env b1) s)
    (b := ⟨"LeafBlock",
      [Instr.icmp "%SwitchLeaf" (IPred.eq) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x45#8))],
      Term.condbr (Operand.reg "%SwitchLeaf") "if.then157" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock
  · simpa only [denoteCode_nil] using leafBlock_denote (calls := calls) hb
  · have hlk : lookupName (leafBlockEnv env b1) "%SwitchLeaf"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x45#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%SwitchLeaf" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem leafBlock_step_nomarker {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "LeafBlock")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b1) 0x45#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlockEnv env b1)
        { s with pc := "if.end226", pre := some "LeafBlock" }) := by
  refine numFast_step_at (s' := stateAt (leafBlockEnv env b1) s)
    (b := ⟨"LeafBlock",
      [Instr.icmp "%SwitchLeaf" (IPred.eq) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x45#8))],
      Term.condbr (Operand.reg "%SwitchLeaf") "if.then157" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock
  · simpa only [denoteCode_nil] using leafBlock_denote (calls := calls) hb
  · have hlk : lookupName (leafBlockEnv env b1) "%SwitchLeaf"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x45#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock1`'s environment: the `'e'` equality's bit. -/
def leafBlock1Env (env : Env) (b1 : UInt8) : Env :=
  ("%SwitchLeaf2", .int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x65#8)) :: env

theorem leafBlock1_denote {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1))) :
    denoteCode calls
        [Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%21")
          (Operand.imm (Const.int 8 0x65#8))]
        (stateAt env s) =
      some (stateAt (leafBlock1Env env b1) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%SwitchLeaf2" "%21" .eq
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, leafBlock1Env]

theorem leafBlock1_step_marker {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "LeafBlock1")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b1) 0x65#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock1Env env b1)
        { s with pc := "if.then157", pre := some "LeafBlock1" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock1Env env b1) s)
    (b := ⟨"LeafBlock1",
      [Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x65#8))],
      Term.condbr (Operand.reg "%SwitchLeaf2") "if.then157" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock1
  · simpa only [denoteCode_nil] using leafBlock1_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock1Env env b1) "%SwitchLeaf2"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x65#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%SwitchLeaf2" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem leafBlock1_step_nomarker {calls : Calls} {env : Env} {s : State} {b1 : UInt8}
    (hpc : s.pc = "LeafBlock1")
    (hb : lookupName env "%21" = some (.int 8 (JsonScanLane.vByte b1)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b1) 0x65#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock1Env env b1)
        { s with pc := "if.end226", pre := some "LeafBlock1" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock1Env env b1) s)
    (b := ⟨"LeafBlock1",
      [Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%21")
        (Operand.imm (Const.int 8 0x65#8))],
      Term.condbr (Operand.reg "%SwitchLeaf2") "if.then157" "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock1
  · simpa only [denoteCode_nil] using leafBlock1_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock1Env env b1) "%SwitchLeaf2"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b1) 0x65#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf2" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.then157`, `land.lhs.true161`, `NodeBlock7`, `LeafBlock3`, `LeafBlock5`

The marker is consumed: the successor index `%inc158` is formed and tested
against the length, so a marker at the last byte leaves with no exponent digits
(`if.end177`, whose `%i.11` is the index `%cmp178.not` then tests), and the byte
at `%inc158` decides the sign: `NodeBlock7` pivots against `0x2d`, `LeafBlock5`
tests it for the `-` and `LeafBlock3` for the `+`. -/

/-- `if.then157`'s environment: the successor index and its test. -/
def then157Env (env : Env) (i10 : Nat) (nv : BitVec 64) : Env :=
  ("%cmp159", .int 1 (evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) nv)) ::
  ("%inc158", .int 64 (BitVec.ofNat 64 i10 + 0x1#64)) :: env

theorem then157_denote {calls : Calls} {env : Env} {s : State} {i10 : Nat}
    {nv : BitVec 64}
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls
        [Instr.binop "%inc158" (BinOp.add) 64 (Operand.reg "%i.10")
          (Operand.imm (Const.int 64 0x0000000000000001#64)),
         Instr.icmp "%cmp159" (IPred.ult) 64 (Operand.reg "%inc158") (Operand.reg "%n")]
        (stateAt env s) =
      some (stateAt (then157Env env i10 nv) s) := by
  rw [denoteCode_add_imm _ _ _ "%inc158" "%i.10" hi _]
  rw [JsonScanLane.denoteCode_icmp_reg_w _ _ _ "%cmp159" "%inc158" "%n" .ult 64
    (lookupName_cons_self ..) hn _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, then157Env]

theorem then157_step_more {calls : Calls} {env : Env} {s : State} {i10 : Nat}
    {nv : BitVec 64}
    (hpc : s.pc = "if.then157")
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then157Env env i10 nv)
        { s with pc := "land.lhs.true161", pre := some "if.then157" }) := by
  refine numFast_step_at (s' := stateAt (then157Env env i10 nv) s)
    (b := ⟨"if.then157",
      [Instr.binop "%inc158" (BinOp.add) 64 (Operand.reg "%i.10")
        (Operand.imm (Const.int 64 0x0000000000000001#64)),
       Instr.icmp "%cmp159" (IPred.ult) 64 (Operand.reg "%inc158") (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp159") "land.lhs.true161" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then157
  · simpa only [denoteCode_nil] using then157_denote (calls := calls) hi hn
  · have hlk : lookupName (then157Env env i10 nv) "%cmp159"
        = some (.int 1 (evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) nv)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp159" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem then157_step_end {calls : Calls} {env : Env} {s : State} {i10 : Nat}
    {nv : BitVec 64}
    (hpc : s.pc = "if.then157")
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then157Env env i10 nv)
        { s with pc := "if.end177", pre := some "if.then157" }) := by
  refine numFast_step_at (s' := stateAt (then157Env env i10 nv) s)
    (b := ⟨"if.then157",
      [Instr.binop "%inc158" (BinOp.add) 64 (Operand.reg "%i.10")
        (Operand.imm (Const.int 64 0x0000000000000001#64)),
       Instr.icmp "%cmp159" (IPred.ult) 64 (Operand.reg "%inc158") (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp159") "land.lhs.true161" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then157
  · simpa only [denoteCode_nil] using then157_denote (calls := calls) hi hn
  · have hlk : lookupName (then157Env env i10 nv) "%cmp159"
        = some (.int 1 (evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) nv)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp159" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The successor index's address: `%p + (%i.10 + 1)`. -/
theorem t161_addr {i10 : Nat} (h : i10 + 1 < 2 ^ 63) :
    (((BitVec.ofNat 64 i10 + 0x1#64)).signExtend 64).toNat = i10 + 1 := by
  rw [ofNat64_add_one (by omega)]
  exact sExt_ofNat64 h

/-- `land.lhs.true161`'s environment: the successor's address and byte. -/
def t161Env (env : Env) (a i10 : Nat) (b2 : UInt8) : Env :=
  ("%22", .int 8 (JsonScanLane.vByte b2)) ::
  ("%arrayidx162", .ptr (a + (i10 + 1))) :: env

theorem t161_denote {calls : Calls} {env : Env} {s : State} {a i10 : Nat}
    {b2 : UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc158" = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)))
    (hj : i10 + 1 < 2 ^ 63)
    (hread : readByte s.mem (a + (i10 + 1)) = some b2) :
    denoteCode calls
        [Instr.gep "%arrayidx162" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc158"),
         Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx162")]
        (stateAt env s) =
      some (stateAt (t161Env env a i10 b2) s) := by
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx162" "%p" "%inc158" hp hi
    (by rw [t161_addr hj]; exact hj) _]
  rw [t161_addr hj]
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%22" "%arrayidx162" (lookupName_cons_self ..)
    (readBytes_one_some.mpr hread) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, t161Env]

theorem t161_step {calls : Calls} {env : Env} {s : State} {a i10 : Nat} {b2 : UInt8}
    (hpc : s.pc = "land.lhs.true161")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc158" = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)))
    (hj : i10 + 1 < 2 ^ 63)
    (hread : readByte s.mem (a + (i10 + 1)) = some b2) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t161Env env a i10 b2)
        { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) := by
  refine numFast_step_at (s' := stateAt (t161Env env a i10 b2) s)
    (b := ⟨"land.lhs.true161",
      [Instr.gep "%arrayidx162" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc158"),
       Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx162")],
      Term.br "NodeBlock7"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true161
  · simpa only [denoteCode_nil] using t161_denote (calls := calls) hp hi hj hread
  · simp only [execTerm, stateAt, hpc]

/-- `NodeBlock7`'s environment: the sign pivot's bit. -/
def nodeBlock7Env (env : Env) (b2 : UInt8) : Env :=
  ("%Pivot8", .int 1 (evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8)) :: env

theorem nodeBlock7_denote {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2))) :
    denoteCode calls
        [Instr.icmp "%Pivot8" (IPred.slt) 8 (Operand.reg "%22")
          (Operand.imm (Const.int 8 0x2d#8))]
        (stateAt env s) =
      some (stateAt (nodeBlock7Env env b2) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%Pivot8" "%22" .slt
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, nodeBlock7Env]

theorem nodeBlock7_step_minus {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "NodeBlock7")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (nodeBlock7Env env b2)
        { s with pc := "LeafBlock5", pre := some "NodeBlock7" }) := by
  refine numFast_step_at (s' := stateAt (nodeBlock7Env env b2) s)
    (b := ⟨"NodeBlock7",
      [Instr.icmp "%Pivot8" (IPred.slt) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2d#8))],
      Term.condbr (Operand.reg "%Pivot8") "LeafBlock3" "LeafBlock5"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_NodeBlock7
  · simpa only [denoteCode_nil] using nodeBlock7_denote (calls := calls) hb
  · have hlk : lookupName (nodeBlock7Env env b2) "%Pivot8"
        = some (.int 1 (evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%Pivot8" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem nodeBlock7_step_plus {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "NodeBlock7")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (nodeBlock7Env env b2)
        { s with pc := "LeafBlock3", pre := some "NodeBlock7" }) := by
  refine numFast_step_at (s' := stateAt (nodeBlock7Env env b2) s)
    (b := ⟨"NodeBlock7",
      [Instr.icmp "%Pivot8" (IPred.slt) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2d#8))],
      Term.condbr (Operand.reg "%Pivot8") "LeafBlock3" "LeafBlock5"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_NodeBlock7
  · simpa only [denoteCode_nil] using nodeBlock7_denote (calls := calls) hb
  · have hlk : lookupName (nodeBlock7Env env b2) "%Pivot8"
        = some (.int 1 (evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%Pivot8" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock3`'s environment: the `'+'` equality's bit. -/
def leafBlock3Env (env : Env) (b2 : UInt8) : Env :=
  ("%SwitchLeaf4", .int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2b#8)) :: env

theorem leafBlock3_denote {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2))) :
    denoteCode calls
        [Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%22")
          (Operand.imm (Const.int 8 0x2b#8))]
        (stateAt env s) =
      some (stateAt (leafBlock3Env env b2) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%SwitchLeaf4" "%22" .eq
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, leafBlock3Env]

theorem leafBlock3_step_sign {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "LeafBlock3")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b2) 0x2b#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock3Env env b2)
        { s with pc := "if.then171", pre := some "LeafBlock3" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock3Env env b2) s)
    (b := ⟨"LeafBlock3",
      [Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2b#8))],
      Term.condbr (Operand.reg "%SwitchLeaf4") "if.then171" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock3
  · simpa only [denoteCode_nil] using leafBlock3_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock3Env env b2) "%SwitchLeaf4"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2b#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%SwitchLeaf4" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem leafBlock3_step_nosign {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "LeafBlock3")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b2) 0x2b#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock3Env env b2)
        { s with pc := "if.end177", pre := some "LeafBlock3" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock3Env env b2) s)
    (b := ⟨"LeafBlock3",
      [Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2b#8))],
      Term.condbr (Operand.reg "%SwitchLeaf4") "if.then171" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock3
  · simpa only [denoteCode_nil] using leafBlock3_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock3Env env b2) "%SwitchLeaf4"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2b#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf4" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `LeafBlock5`'s environment: the `'-'` equality's bit. -/
def leafBlock5Env (env : Env) (b2 : UInt8) : Env :=
  ("%SwitchLeaf6", .int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2d#8)) :: env

theorem leafBlock5_denote {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2))) :
    denoteCode calls
        [Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%22")
          (Operand.imm (Const.int 8 0x2d#8))]
        (stateAt env s) =
      some (stateAt (leafBlock5Env env b2) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%SwitchLeaf6" "%22" .eq
    (by simpa only [stateAt] using hb) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, leafBlock5Env]

theorem leafBlock5_step_sign {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "LeafBlock5")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b2) 0x2d#8 = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock5Env env b2)
        { s with pc := "if.then171", pre := some "LeafBlock5" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock5Env env b2) s)
    (b := ⟨"LeafBlock5",
      [Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2d#8))],
      Term.condbr (Operand.reg "%SwitchLeaf6") "if.then171" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock5
  · simpa only [denoteCode_nil] using leafBlock5_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock5Env env b2) "%SwitchLeaf6"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2d#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%SwitchLeaf6" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem leafBlock5_step_nosign {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    (hpc : s.pc = "LeafBlock5")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hbit : evalICmp .eq (JsonScanLane.vByte b2) 0x2d#8 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leafBlock5Env env b2)
        { s with pc := "if.end177", pre := some "LeafBlock5" }) := by
  refine numFast_step_at (s' := stateAt (leafBlock5Env env b2) s)
    (b := ⟨"LeafBlock5",
      [Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2d#8))],
      Term.condbr (Operand.reg "%SwitchLeaf6") "if.then171" "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_LeafBlock5
  · simpa only [denoteCode_nil] using leafBlock5_denote (calls := calls) hb
  · have hlk : lookupName (leafBlock5Env env b2) "%SwitchLeaf6"
        = some (.int 1 (evalICmp .eq (JsonScanLane.vByte b2) 0x2d#8)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%SwitchLeaf6" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### `if.then171` and `if.end177`

`if.then171` reads the sign's own byte into `%cmp174` (`%22 != 0x2d`) and forms
`%i.11 = %i.10 + 2`; `if.end177`'s other three edges write `%esign.0 = 1` and
`%i.11 = %inc158` instead.  The merge then tests `%i.11` against the length: a
lexeme that ends after the marker leaves with no exponent digits
(`cleanup223`'s refusal), and one that has a byte there goes on to
`lor.lhs.false180`, whose digit gate is `JsonStage2NumFastStarts`'. -/

/-- `if.then171`'s environment: the sign's comparison and the two-byte index. -/
def then171Env (env : Env) (b2 : UInt8) (i10 : Nat) : Env :=
  ("%inc176", .int 64 (BitVec.ofNat 64 i10 + 0x2#64)) ::
  ("%cmp174", .int 1 (evalICmp .ne (JsonScanLane.vByte b2) 0x2d#8)) :: env

theorem then171_denote {calls : Calls} {env : Env} {s : State} {b2 : UInt8}
    {i10 : Nat}
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10))) :
    denoteCode calls
        [Instr.icmp "%cmp174" (IPred.ne) 8 (Operand.reg "%22")
          (Operand.imm (Const.int 8 0x2d#8)),
         Instr.binop "%inc176" (BinOp.add) 64 (Operand.reg "%i.10")
          (Operand.imm (Const.int 64 0x0000000000000002#64))]
        (stateAt env s) =
      some (stateAt (then171Env env b2 i10) s) := by
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp174" "%22" .ne
    (by simpa only [stateAt] using hb) _]
  rw [denoteCode_add_imm _ _ _ "%inc176" "%i.10"
    (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, then171Env]

theorem then171_step {calls : Calls} {env : Env} {s : State} {b2 : UInt8} {i10 : Nat}
    (hpc : s.pc = "if.then171")
    (hb : lookupName env "%22" = some (.int 8 (JsonScanLane.vByte b2)))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then171Env env b2 i10)
        { s with pc := "if.end177", pre := some "if.then171" }) := by
  refine numFast_step_at (s' := stateAt (then171Env env b2 i10) s)
    (b := ⟨"if.then171",
      [Instr.icmp "%cmp174" (IPred.ne) 8 (Operand.reg "%22")
        (Operand.imm (Const.int 8 0x2d#8)),
       Instr.binop "%inc176" (BinOp.add) 64 (Operand.reg "%i.10")
        (Operand.imm (Const.int 64 0x0000000000000002#64))],
      Term.br "if.end177"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then171
  · simpa only [denoteCode_nil] using then171_denote (calls := calls) hb hi
  · simp only [execTerm, stateAt, hpc]

/-- `if.end177`, from its `findBlock` pin. -/
def numFastIfEnd177Instrs : List Instr :=
  [Instr.phi "%esign.0" (Ty.int 1)
      [("if.then171", (Operand.reg "%cmp174")),
       ("if.then157", (Operand.imm (Const.int 1 0x1#1))),
       ("LeafBlock3", (Operand.imm (Const.int 1 0x1#1))),
       ("LeafBlock5", (Operand.imm (Const.int 1 0x1#1)))],
   Instr.phi "%i.11" (Ty.int 64)
      [("if.then171", (Operand.reg "%inc176")),
       ("if.then157", (Operand.reg "%inc158")),
       ("LeafBlock3", (Operand.reg "%inc158")),
       ("LeafBlock5", (Operand.reg "%inc158"))],
   Instr.icmp "%cmp178.not" (IPred.ult) 64 (Operand.reg "%i.11") (Operand.reg "%n")]

theorem numFast_findBlock_if_end177_named :
    numFastBody.findBlock "if.end177" =
      some ⟨"if.end177", numFastIfEnd177Instrs,
        Term.condbr (Operand.reg "%cmp178.not") "lor.lhs.false180" "cleanup223"⟩ := by
  simpa only [numFastIfEnd177Instrs] using numFast_findBlock_if_end177

/-- `if.end177`'s environment: the exponent's sign bit, the index and its test. -/
def end177Env (env : Env) (esign : BitVec 1) (i11 nv : BitVec 64) : Env :=
  ("%cmp178.not", .int 1 (evalICmp .ult i11 nv)) ::
  ("%i.11", .int 64 i11) :: ("%esign.0", .int 1 esign) :: env

theorem end177_denote_signed {calls : Calls} {env : Env} {s : State}
    {b2 : UInt8} {i10 : Nat} {nv : BitVec 64}
    (hpre : s.pre = some "if.then171")
    (hc : lookupName env "%cmp174"
      = some (.int 1 (evalICmp .ne (JsonScanLane.vByte b2) 0x2d#8)))
    (hinc : lookupName env "%inc176"
      = some (.int 64 (BitVec.ofNat 64 i10 + 0x2#64)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env (evalICmp .ne (JsonScanLane.vByte b2) 0x2d#8)
        (BitVec.ofNat 64 i10 + 0x2#64) nv) s) := by
  unfold numFastIfEnd177Instrs
  block_eval

theorem end177_denote_157 {calls : Calls} {env : Env} {s : State}
    {i10 : Nat} {nv : BitVec 64}
    (hpre : s.pre = some "if.then157")
    (hinc : lookupName env "%inc158"
      = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env 1 (BitVec.ofNat 64 i10 + 0x1#64) nv) s) := by
  unfold numFastIfEnd177Instrs
  block_eval

theorem end177_denote_leaf3 {calls : Calls} {env : Env} {s : State}
    {i10 : Nat} {nv : BitVec 64}
    (hpre : s.pre = some "LeafBlock3")
    (hinc : lookupName env "%inc158"
      = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env 1 (BitVec.ofNat 64 i10 + 0x1#64) nv) s) := by
  unfold numFastIfEnd177Instrs
  block_eval

theorem end177_denote_leaf5 {calls : Calls} {env : Env} {s : State}
    {i10 : Nat} {nv : BitVec 64}
    (hpre : s.pre = some "LeafBlock5")
    (hinc : lookupName env "%inc158"
      = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env 1 (BitVec.ofNat 64 i10 + 0x1#64) nv) s) := by
  unfold numFastIfEnd177Instrs
  block_eval

theorem end177_step_more {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {i11 nv : BitVec 64}
    (hpc : s.pc = "if.end177")
    (hden : denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env esign i11 nv) s))
    (hbit : evalICmp .ult i11 nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end177Env env esign i11 nv)
        { s with pc := "lor.lhs.false180", pre := some "if.end177" }) := by
  refine numFast_step_at (s' := stateAt (end177Env env esign i11 nv) s)
    (b := ⟨"if.end177", numFastIfEnd177Instrs,
      Term.condbr (Operand.reg "%cmp178.not") "lor.lhs.false180" "cleanup223"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd177Instrs] using numFast_findBlock_if_end177
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (end177Env env esign i11 nv) "%cmp178.not"
        = some (.int 1 (evalICmp .ult i11 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp178.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem end177_step_end {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {i11 nv : BitVec 64}
    (hpc : s.pc = "if.end177")
    (hden : denoteCode calls numFastIfEnd177Instrs (stateAt env s) =
      some (stateAt (end177Env env esign i11 nv) s))
    (hbit : evalICmp .ult i11 nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end177Env env esign i11 nv)
        { s with pc := "cleanup223", pre := some "if.end177" }) := by
  refine numFast_step_at (s' := stateAt (end177Env env esign i11 nv) s)
    (b := ⟨"if.end177", numFastIfEnd177Instrs,
      Term.condbr (Operand.reg "%cmp178.not") "lor.lhs.false180" "cleanup223"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd177Instrs] using numFast_findBlock_if_end177
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (end177Env env esign i11 nv) "%cmp178.not"
        = some (.int 1 (evalICmp .ult i11 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp178.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The pivot's and the leaves' bits at a marker

The signed comparison and the two equalities, at the two marker bytes.  `0x45`
is below `0x65` so it pivots to `LeafBlock`; `0x65` is not, so it goes to
`LeafBlock1`, and each leaf's equality is then the one its own byte satisfies. -/

theorem slt_e_65 : evalICmp .slt (JsonScanLane.vByte 0x65) 0x65#8 = 0 := by decide

theorem slt_E_65 : evalICmp .slt (JsonScanLane.vByte 0x45) 0x65#8 = 1 := by decide

theorem eq_E_45 : evalICmp .eq (JsonScanLane.vByte 0x45) 0x45#8 = 1 := by decide

theorem eq_e_65 : evalICmp .eq (JsonScanLane.vByte 0x65) 0x65#8 = 1 := by decide

theorem slt_plus_minus : evalICmp .slt (JsonScanLane.vByte 0x2b) 0x2d#8 = 1 := by decide

theorem slt_minus_minus : evalICmp .slt (JsonScanLane.vByte 0x2d) 0x2d#8 = 0 := by decide

theorem eq_plus : evalICmp .eq (JsonScanLane.vByte 0x2b) 0x2b#8 = 1 := by decide

theorem eq_minus : evalICmp .eq (JsonScanLane.vByte 0x2d) 0x2d#8 = 1 := by decide

/-- An equality at a byte the leaf's own value is not: one byte differs exactly
when its 8-bit reading does. -/
theorem eq_bit_zero_of_ne {c : BitVec 8} {b : UInt8} (h : JsonScanLane.vByte b ≠ c) :
    evalICmp .eq (JsonScanLane.vByte b) c = 0 := by
  rw [NumFastStarts.eq_zero_iff]
  exact h

/-- A 64-bit `Nat` read at an offset below `2 ^ 63`: the word is its numeral. -/
theorem ofNat_toNat_of_lt {j : Nat} (h : j < 2 ^ 63) :
    (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The successor test at a marker's index: `%inc158 < %n` is one when a byte
follows the marker. -/
theorem inc158_ult_one {i10 n : Nat} (hin : i10 + 1 < n) (hnlt : n < 2 ^ 63) :
    evalICmp .ult (BitVec.ofNat 64 i10 + 0x1#64) (BitVec.ofNat 64 n) = 1 := by
  rw [NumFastStarts.ult_iff_one,
    NumFastStarts.toNat_add_const (by omega), ofNat_toNat_of_lt hnlt]
  exact hin

/-- The merge's index test at the sign's successor: `%i.11 < %n` with
`%i.11 = %i.10 + 2`. -/
theorem inc176_ult_one {i10 n : Nat} (hin : i10 + 3 ≤ n) (hnlt : n < 2 ^ 63) :
    evalICmp .ult (BitVec.ofNat 64 i10 + 0x2#64) (BitVec.ofNat 64 n) = 1 := by
  rw [NumFastStarts.ult_iff_one,
    NumFastStarts.toNat_add_const (by omega), ofNat_toNat_of_lt hnlt]
  omega

/-- The merge's index test: `%i.14 == %n`. -/
theorem i14_eq_one {n : Nat} (hnlt : n < 2 ^ 63) :
    evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 n) = 1 :=
  NumFastStarts.eq_iff_one _ _ |>.mpr rfl

/-! ### The marker's three blocks, from `land.lhs.true147` to `if.then157`

`nestTo157` reads the byte at `%i.10` and takes the marker's own leaf.  The
byte is a parameter, and the two marker shapes are the two lemmas: the pivot's
signedness decides which leaf is reached, and that is what makes `'E'` a
`LeafBlock` byte and `'e'` a `LeafBlock1` one. -/

/-- **The `'e'` shape.**  From `land.lhs.true147` with the byte at `%i.10` a
`'e'`, three steps reach `if.then157`. -/
theorem nestTo157_e {calls : Calls} {env : Env} {s : State} {a i10 : Nat}
    (hpc : s.pc = "land.lhs.true147")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hj : i10 < 2 ^ 63)
    (hread : readByte s.mem (a + i10) = some 0x65) :
    ∀ k, runFuel calls (3 + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (leafBlock1Env (nodeBlockEnv (t147Env env a i10 0x65) 0x65) 0x65)
          { s with pc := "if.then157", pre := some "LeafBlock1" }) := by
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (t147Env env a i10 0x65)
        { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) :=
    t147_step (calls := calls) hpc hp hi hj hread
  have h2 : step calls numFastBody
      (stateAt (t147Env env a i10 0x65) { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) =
      .jump (stateAt (nodeBlockEnv (t147Env env a i10 0x65) 0x65)
        { s with pc := "LeafBlock1", pre := some "NodeBlock" }) :=
    nodeBlock_step_false (calls := calls) rfl (by simp only [t147Env]; block_lk)
      slt_e_65
  have h3 : step calls numFastBody
      (stateAt (nodeBlockEnv (t147Env env a i10 0x65) 0x65)
        { s with pc := "LeafBlock1", pre := some "NodeBlock" }) =
      .jump (stateAt (leafBlock1Env (nodeBlockEnv (t147Env env a i10 0x65) 0x65) 0x65)
        { s with pc := "if.then157", pre := some "LeafBlock1" }) :=
    leafBlock1_step_marker (calls := calls) rfl
      (by simp only [nodeBlockEnv, t147Env, lookupName_cons_self,
        Function.comp_apply]; rfl) eq_e_65
  intro k
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]

/-- **The `'E'` shape.** -/
theorem nestTo157_E {calls : Calls} {env : Env} {s : State} {a i10 : Nat}
    (hpc : s.pc = "land.lhs.true147")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hj : i10 < 2 ^ 63)
    (hread : readByte s.mem (a + i10) = some 0x45) :
    ∀ k, runFuel calls (3 + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (leafBlockEnv (nodeBlockEnv (t147Env env a i10 0x45) 0x45) 0x45)
          { s with pc := "if.then157", pre := some "LeafBlock" }) := by
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (t147Env env a i10 0x45)
        { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) :=
    t147_step (calls := calls) hpc hp hi hj hread
  have h2 : step calls numFastBody
      (stateAt (t147Env env a i10 0x45) { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) =
      .jump (stateAt (nodeBlockEnv (t147Env env a i10 0x45) 0x45)
        { s with pc := "LeafBlock", pre := some "NodeBlock" }) :=
    nodeBlock_step (calls := calls) rfl (by simp only [t147Env]; block_lk)
      slt_E_65
  have h3 : step calls numFastBody
      (stateAt (nodeBlockEnv (t147Env env a i10 0x45) 0x45)
        { s with pc := "LeafBlock", pre := some "NodeBlock" }) =
      .jump (stateAt (leafBlockEnv (nodeBlockEnv (t147Env env a i10 0x45) 0x45) 0x45)
        { s with pc := "if.then157", pre := some "LeafBlock" }) :=
    leafBlock_step_marker (calls := calls) rfl
      (by simp only [nodeBlockEnv, t147Env, lookupName_cons_self,
        Function.comp_apply]; rfl) eq_E_45
  intro k
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]

/-- **The byte is no marker.**  Whichever leaf the pivot reaches, its equality
is read on the same byte, so the block leaves for the merge that carries no
exponent.  The endpoint is stated by its registers rather than by the builder
chain: the caller runs `if.end226` from either leaf. -/
theorem nest_nomarker {calls : Calls} {env : Env} {s : State} {a i10 n : Nat}
    {b1 : UInt8}
    (hpc : s.pc = "land.lhs.true147")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hj : i10 < 2 ^ 63)
    (hread : readByte s.mem (a + i10) = some b1)
    (hne65 : b1 ≠ 0x65) (hne45 : b1 ≠ 0x45) :
    ∃ e : State, e.pc = "if.end226" ∧ e.mem = s.mem ∧
      (e.pre = some "LeafBlock" ∨ e.pre = some "LeafBlock1") ∧
      lookupName e.env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      ∀ k, runFuel calls (3 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (t147Env env a i10 b1)
        { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) :=
    t147_step (calls := calls) hpc hp hi hj hread
  by_cases hpiv : evalICmp .slt (JsonScanLane.vByte b1) 0x65#8 = 1
  · -- the pivot's leaf is `LeafBlock`, whose `0x45` equality fails
    have h2 : step calls numFastBody
        (stateAt (t147Env env a i10 b1) { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) =
        .jump (stateAt (nodeBlockEnv (t147Env env a i10 b1) b1)
          { s with pc := "LeafBlock", pre := some "NodeBlock" }) :=
      nodeBlock_step (calls := calls) rfl (by simp only [t147Env]; block_lk) hpiv
    have h3 : step calls numFastBody
        (stateAt (nodeBlockEnv (t147Env env a i10 b1) b1)
          { s with pc := "LeafBlock", pre := some "NodeBlock" }) =
        .jump (stateAt (leafBlockEnv (nodeBlockEnv (t147Env env a i10 b1) b1) b1)
          { s with pc := "if.end226", pre := some "LeafBlock" }) :=
      leafBlock_step_nomarker (calls := calls) rfl (by simp only [nodeBlockEnv, t147Env]; block_lk) (eq_bit_zero_of_ne (fun hh => hne45 (NumFastStarts.vByte_inj hh)))
    refine ⟨stateAt (leafBlockEnv (nodeBlockEnv (t147Env env a i10 b1) b1) b1)
      { s with pc := "if.end226", pre := some "LeafBlock" }, rfl, rfl, Or.inl rfl, ?_, ?_, ?_⟩
    · simp only [leafBlockEnv, nodeBlockEnv, t147Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [leafBlockEnv, nodeBlockEnv, t147Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · intro k
      rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]
  · have hpiv0 : evalICmp .slt (JsonScanLane.vByte b1) 0x65#8 = 0 := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt (JsonScanLane.vByte b1) 0x65#8)
        with h | h
      · exact h
      · exact absurd h hpiv
    have h2 : step calls numFastBody
        (stateAt (t147Env env a i10 b1) { s with pc := "NodeBlock", pre := some "land.lhs.true147" }) =
        .jump (stateAt (nodeBlockEnv (t147Env env a i10 b1) b1)
          { s with pc := "LeafBlock1", pre := some "NodeBlock" }) :=
      nodeBlock_step_false (calls := calls) rfl (by simp only [t147Env]; block_lk) hpiv0
    have h3 : step calls numFastBody
        (stateAt (nodeBlockEnv (t147Env env a i10 b1) b1)
          { s with pc := "LeafBlock1", pre := some "NodeBlock" }) =
        .jump (stateAt (leafBlock1Env (nodeBlockEnv (t147Env env a i10 b1) b1) b1)
          { s with pc := "if.end226", pre := some "LeafBlock1" }) :=
      leafBlock1_step_nomarker (calls := calls) rfl (by simp only [nodeBlockEnv, t147Env]; block_lk) (eq_bit_zero_of_ne (fun hh => hne65 (NumFastStarts.vByte_inj hh)))
    refine ⟨stateAt (leafBlock1Env (nodeBlockEnv (t147Env env a i10 b1) b1) b1)
      { s with pc := "if.end226", pre := some "LeafBlock1" }, rfl, rfl, Or.inr rfl, ?_, ?_, ?_⟩
    · simp only [leafBlock1Env, nodeBlockEnv, t147Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [leafBlock1Env, nodeBlockEnv, t147Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · intro k
      rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
        runFuel_jump_prefix h1, runFuel_jump_prefix h2, runFuel_jump_prefix h3]

/-! ### From `if.then157` to `lor.lhs.false180`

The marker is consumed and the byte at `%inc158` decides the sign.  The two
shapes are the two lemmas: without a sign the merge takes `%inc158` and
`%esign.0 = 1`; with one it takes `%inc176 = %i.10 + 2` and `%esign.0` the
sign's own comparison, `%22 != 0x2d`. -/

/-- **No exponent sign.**  From `if.then157`, five steps reach
`lor.lhs.false180` with `%i.11 = %i.10 + 1` and `%esign.0 = 1`.  None of the
blocks the path crosses writes the four cells `if.end230`'s `phi`s read, so the
endpoint carries them (`ExpRunCells`) from the state the argument names. -/
theorem nestFrom157_nosign {calls : Calls} {env : Env} {s : State} {a i10 n : Nat}
    {b2 : UInt8}
    (hpc : s.pc = "if.then157")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hnlt : n < 2 ^ 63) (hin : i10 + 2 ≤ n)
    (hread : readByte s.mem (a + (i10 + 1)) = some b2)
    (hnosign : b2 ≠ 0x2b ∧ b2 ≠ 0x2d) :
    ∃ e : State, e.pc = "lor.lhs.false180" ∧ e.mem = s.mem ∧
      lookupName e.env "%p" = some (.ptr a) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%i.11" = some (.int 64 (BitVec.ofNat 64 (i10 + 1))) ∧
      lookupName e.env "%esign.0" = some (.int 1 1) ∧
      (∀ (idig5 ip5 fr5 fd5 : BitVec 64),
        ExpRunCells idig5 ip5 fr5 fd5 (stateAt env s) →
          ExpRunCells idig5 ip5 fr5 fd5 e) ∧
      ∀ k, runFuel calls (5 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have h4 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (then157Env env i10 (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true161", pre := some "if.then157" }) :=
    then157_step_more (calls := calls) hpc hi hn (inc158_ult_one (by omega) hnlt)
  have h5 : step calls numFastBody
      (stateAt (then157Env env i10 (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true161", pre := some "if.then157" }) =
      .jump (stateAt (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2)
        { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) :=
    t161_step (calls := calls) rfl hp
      (by simp only [then157Env]; block_lk) (by omega) hread
  have h22 : lookupName (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2)
      "%22" = some (.int 8 (JsonScanLane.vByte b2)) := by
    simp only [t161Env]; block_lk
  by_cases hpiv : evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8 = 1
  · -- `LeafBlock3`, whose `'+'` equality fails
    have h6 : step calls numFastBody
        (stateAt (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2)
          { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) =
        .jump (stateAt
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2)
          { s with pc := "LeafBlock3", pre := some "NodeBlock7" }) :=
      nodeBlock7_step_plus (calls := calls) rfl h22 hpiv
    have h23 : lookupName
        (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) "%22"
        = some (.int 8 (JsonScanLane.vByte b2)) := by
      simp only [nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h7 : step calls numFastBody
        (stateAt
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2)
          { s with pc := "LeafBlock3", pre := some "NodeBlock7" }) =
        .jump (stateAt
          (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
          { s with pc := "if.end177", pre := some "LeafBlock3" }) :=
      leafBlock3_step_nosign (calls := calls) rfl h23
        (eq_bit_zero_of_ne (fun hh => hnosign.1 (NumFastStarts.vByte_inj hh)))
    have hden := end177_denote_leaf3 (calls := calls)
      (env := leafBlock3Env
        (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
      (s := { s with pc := "if.end177", pre := some "LeafBlock3" })
      rfl (by simp only [leafBlock3Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
      (by simp only [leafBlock3Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have h8 : step calls numFastBody
        (stateAt
          (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
          { s with pc := "if.end177", pre := some "LeafBlock3" }) =
        .jump (stateAt
          (end177Env
            (leafBlock3Env
              (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
            1 (BitVec.ofNat 64 i10 + 0x1#64) (BitVec.ofNat 64 n))
          { s with pc := "lor.lhs.false180", pre := some "if.end177" }) :=
      end177_step_more (calls := calls) rfl hden (inc158_ult_one (by omega) hnlt)
    let eF : State := stateAt
      (end177Env
        (leafBlock3Env
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
        1 (BitVec.ofNat 64 i10 + 0x1#64) (BitVec.ofNat 64 n))
      { s with pc := "lor.lhs.false180", pre := some "if.end177" }
    have hi11 : lookupName eF.env "%i.11"
        = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)) := by
      simp only [eF, stateAt, end177Env]; block_lk
    have huniv : ∀ k, runFuel calls (5 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody eF := by
      intro k
      rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5, runFuel_jump_prefix h6,
        runFuel_jump_prefix h7, runFuel_jump_prefix h8]
    refine ⟨eF, rfl, rfl, ?_, ?_, ?_, ?_, ?_, huniv⟩
    · simp only [eF, end177Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [eF, end177Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · rw [ofNat64_add_one (by omega)] at hi11
      exact hi11
    · simp only [eF, end177Env]; block_lk
    · intro idig5 ip5 fr5 fd5 hcells
      obtain ⟨h1, h2, h3, h4⟩ := hcells
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [eF, end177Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
        first
         | (simp only [stateAt]; block_lk)
         | block_lk
  · -- `LeafBlock5`, whose `'-'` equality fails
    have hpiv0 : evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8 = 0 := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt (JsonScanLane.vByte b2) 0x2d#8) with h | h
      · exact h
      · exact absurd h hpiv
    have h6 : step calls numFastBody
        (stateAt (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2)
          { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) =
        .jump (stateAt
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2)
          { s with pc := "LeafBlock5", pre := some "NodeBlock7" }) :=
      nodeBlock7_step_minus (calls := calls) rfl h22 hpiv0
    have h23 : lookupName
        (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) "%22"
        = some (.int 8 (JsonScanLane.vByte b2)) := by
      simp only [nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h7 : step calls numFastBody
        (stateAt
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2)
          { s with pc := "LeafBlock5", pre := some "NodeBlock7" }) =
        .jump (stateAt
          (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
          { s with pc := "if.end177", pre := some "LeafBlock5" }) :=
      leafBlock5_step_nosign (calls := calls) rfl h23
        (eq_bit_zero_of_ne (fun hh => hnosign.2 (NumFastStarts.vByte_inj hh)))
    have hden := end177_denote_leaf5 (calls := calls)
      (env := leafBlock5Env
        (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
      (s := { s with pc := "if.end177", pre := some "LeafBlock5" })
      rfl (by simp only [leafBlock5Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
      (by simp only [leafBlock5Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have h8 : step calls numFastBody
        (stateAt
          (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
          { s with pc := "if.end177", pre := some "LeafBlock5" }) =
        .jump (stateAt
          (end177Env
            (leafBlock5Env
              (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
            1 (BitVec.ofNat 64 i10 + 0x1#64) (BitVec.ofNat 64 n))
          { s with pc := "lor.lhs.false180", pre := some "if.end177" }) :=
      end177_step_more (calls := calls) rfl hden (inc158_ult_one (by omega) hnlt)
    let eF : State := stateAt
      (end177Env
        (leafBlock5Env
          (nodeBlock7Env (t161Env (then157Env env i10 (BitVec.ofNat 64 n)) a i10 b2) b2) b2)
        1 (BitVec.ofNat 64 i10 + 0x1#64) (BitVec.ofNat 64 n))
      { s with pc := "lor.lhs.false180", pre := some "if.end177" }
    have hi11 : lookupName eF.env "%i.11"
        = some (.int 64 (BitVec.ofNat 64 i10 + 0x1#64)) := by
      simp only [eF, stateAt, end177Env]; block_lk
    have huniv : ∀ k, runFuel calls (5 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody eF := by
      intro k
      rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5, runFuel_jump_prefix h6,
        runFuel_jump_prefix h7, runFuel_jump_prefix h8]
    refine ⟨eF, rfl, rfl, ?_, ?_, ?_, ?_, ?_, huniv⟩
    · simp only [eF, end177Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [eF, end177Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · rw [ofNat64_add_one (by omega)] at hi11
      exact hi11
    · simp only [eF, end177Env]; block_lk
    · intro idig5 ip5 fr5 fd5 hcells
      obtain ⟨h1, h2, h3, h4⟩ := hcells
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [eF, end177Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
        first
         | (simp only [stateAt]; block_lk)
         | block_lk

/-- **With an exponent sign.**  The sign's byte is `'+'` or `'-'`, six steps
reach `lor.lhs.false180` with `%i.11 = %i.10 + 2` and `%esign.0` the sign's
comparison `%22 != 0x2d` — one for `'+'` and zero for `'-'`.  The four cells
`if.end230`'s `phi`s read survive the path as they do without a sign. -/
theorem nestFrom157_sign {calls : Calls} {env : Env} {s : State} {a i10 n : Nat}
    {b2 : UInt8}
    (hpc : s.pc = "if.then157")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hnlt : n < 2 ^ 63) (hin : i10 + 3 ≤ n)
    (hread : readByte s.mem (a + (i10 + 1)) = some b2)
    (hsign : b2 = 0x2b ∨ b2 = 0x2d) :
    ∃ e : State, e.pc = "lor.lhs.false180" ∧ e.mem = s.mem ∧
      lookupName e.env "%p" = some (.ptr a) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%i.11" = some (.int 64 (BitVec.ofNat 64 (i10 + 2))) ∧
      lookupName e.env "%esign.0"
        = some (.int 1 (evalICmp .ne (JsonScanLane.vByte b2) 0x2d#8)) ∧
      (∀ (idig5 ip5 fr5 fd5 : BitVec 64),
        ExpRunCells idig5 ip5 fr5 fd5 (stateAt env s) →
          ExpRunCells idig5 ip5 fr5 fd5 e) ∧
      ∀ k, runFuel calls (6 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  let nv : BitVec 64 := BitVec.ofNat 64 n
  have h4 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (then157Env env i10 nv)
        { s with pc := "land.lhs.true161", pre := some "if.then157" }) :=
    then157_step_more (calls := calls) hpc hi hn (inc158_ult_one (by omega) hnlt)
  have h5 : step calls numFastBody
      (stateAt (then157Env env i10 nv)
        { s with pc := "land.lhs.true161", pre := some "if.then157" }) =
      .jump (stateAt (t161Env (then157Env env i10 nv) a i10 b2)
        { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) :=
    t161_step (calls := calls) rfl hp
      (by simp only [then157Env]; block_lk) (by omega) hread
  have h22 : lookupName (t161Env (then157Env env i10 nv) a i10 b2) "%22"
      = some (.int 8 (JsonScanLane.vByte b2)) := by
    simp only [t161Env]; block_lk
  rcases hsign with rfl | rfl
  · -- the `'+'` leaf: `NodeBlock7` pivots to `LeafBlock3`
    have h6 : step calls numFastBody
        (stateAt (t161Env (then157Env env i10 nv) a i10 0x2b)
          { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) =
        .jump (stateAt (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b)
          { s with pc := "LeafBlock3", pre := some "NodeBlock7" }) :=
      nodeBlock7_step_plus (calls := calls) rfl
        (by simp only [t161Env]; block_lk) slt_plus_minus
    have h23 : lookupName
        (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) "%22"
        = some (.int 8 (JsonScanLane.vByte 0x2b)) := by
      simp only [nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h7 : step calls numFastBody
        (stateAt (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b)
          { s with pc := "LeafBlock3", pre := some "NodeBlock7" }) =
        .jump (stateAt (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b)
          { s with pc := "if.then171", pre := some "LeafBlock3" }) :=
      leafBlock3_step_sign (calls := calls) rfl h23 eq_plus
    have h2b : lookupName
        (leafBlock3Env (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b)
        "%22" = some (.int 8 (JsonScanLane.vByte 0x2b)) := by
      simp only [leafBlock3Env, nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h8 : step calls numFastBody
        (stateAt (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b)
          { s with pc := "if.then171", pre := some "LeafBlock3" }) =
        .jump (stateAt
          (then171Env (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b) 0x2b i10)
          { s with pc := "if.end177", pre := some "if.then171" }) :=
      then171_step (calls := calls) rfl h2b
        (by simp only [leafBlock3Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have hden := end177_denote_signed (calls := calls)
      (env := then171Env (leafBlock3Env
        (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b) 0x2b i10)
      (s := { s with pc := "if.end177", pre := some "if.then171" })
      (b2 := 0x2b) rfl
      (by simp only [then171Env]; block_lk)
      (by simp only [then171Env]; block_lk)
      (by simp only [then171Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have h9 : step calls numFastBody
        (stateAt (then171Env (leafBlock3Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b) 0x2b i10)
          { s with pc := "if.end177", pre := some "if.then171" }) =
        .jump (stateAt
          (end177Env (then171Env (leafBlock3Env
              (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b) 0x2b i10)
            (evalICmp .ne (JsonScanLane.vByte 0x2b) 0x2d#8)
            (BitVec.ofNat 64 i10 + 0x2#64) nv)
          { s with pc := "lor.lhs.false180", pre := some "if.end177" }) :=
      end177_step_more (calls := calls) rfl hden (inc176_ult_one (by omega) hnlt)
    let eF : State := stateAt
      (end177Env (then171Env (leafBlock3Env
          (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2b) 0x2b) 0x2b) 0x2b i10)
        (evalICmp .ne (JsonScanLane.vByte 0x2b) 0x2d#8)
        (BitVec.ofNat 64 i10 + 0x2#64) nv)
      { s with pc := "lor.lhs.false180", pre := some "if.end177" }
    have hi11 : lookupName eF.env "%i.11"
        = some (.int 64 (BitVec.ofNat 64 i10 + 0x2#64)) := by
      simp only [eF, stateAt, end177Env]; block_lk
    have huniv : ∀ k, runFuel calls (6 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody eF := by
      intro k
      rw [show 6 + k = 1 + (1 + (1 + (1 + (1 + (1 + k))))) from by omega,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5, runFuel_jump_prefix h6,
        runFuel_jump_prefix h7, runFuel_jump_prefix h8, runFuel_jump_prefix h9]
    refine ⟨eF, rfl, rfl, ?_, ?_, ?_, ?_, ?_, huniv⟩
    · simp only [eF, end177Env, then171Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [eF, end177Env, then171Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · rw [NumFastStarts.ofNat64_add_const (by omega)] at hi11
      exact hi11
    · simp only [eF, end177Env]; block_lk
    · intro idig5 ip5 fr5 fd5 hcells
      obtain ⟨h1, h2, h3, h4⟩ := hcells
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [eF, end177Env, then171Env, leafBlock3Env, nodeBlock7Env, t161Env, then157Env]
        first
         | (simp only [stateAt]; block_lk)
         | block_lk
  · -- the `'-'` leaf: `NodeBlock7` pivots to `LeafBlock5`
    have h6 : step calls numFastBody
        (stateAt (t161Env (then157Env env i10 nv) a i10 0x2d)
          { s with pc := "NodeBlock7", pre := some "land.lhs.true161" }) =
        .jump (stateAt (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d)
          { s with pc := "LeafBlock5", pre := some "NodeBlock7" }) :=
      nodeBlock7_step_minus (calls := calls) rfl
        (by simp only [t161Env]; block_lk) slt_minus_minus
    have h23 : lookupName
        (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) "%22"
        = some (.int 8 (JsonScanLane.vByte 0x2d)) := by
      simp only [nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h7 : step calls numFastBody
        (stateAt (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d)
          { s with pc := "LeafBlock5", pre := some "NodeBlock7" }) =
        .jump (stateAt (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d)
          { s with pc := "if.then171", pre := some "LeafBlock5" }) :=
      leafBlock5_step_sign (calls := calls) rfl h23 eq_minus
    have h2d : lookupName
        (leafBlock5Env (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d)
        "%22" = some (.int 8 (JsonScanLane.vByte 0x2d)) := by
      simp only [leafBlock5Env, nodeBlock7Env, t161Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    have h8 : step calls numFastBody
        (stateAt (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d)
          { s with pc := "if.then171", pre := some "LeafBlock5" }) =
        .jump (stateAt
          (then171Env (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d) 0x2d i10)
          { s with pc := "if.end177", pre := some "if.then171" }) :=
      then171_step (calls := calls) rfl h2d
        (by simp only [leafBlock5Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have hden := end177_denote_signed (calls := calls)
      (env := then171Env (leafBlock5Env
        (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d) 0x2d i10)
      (s := { s with pc := "if.end177", pre := some "if.then171" })
      (b2 := 0x2d) rfl
      (by simp only [then171Env]; block_lk)
      (by simp only [then171Env]; block_lk)
      (by simp only [then171Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]; block_lk)
    have h9 : step calls numFastBody
        (stateAt (then171Env (leafBlock5Env
            (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d) 0x2d i10)
          { s with pc := "if.end177", pre := some "if.then171" }) =
        .jump (stateAt
          (end177Env (then171Env (leafBlock5Env
              (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d) 0x2d i10)
            (evalICmp .ne (JsonScanLane.vByte 0x2d) 0x2d#8)
            (BitVec.ofNat 64 i10 + 0x2#64) nv)
          { s with pc := "lor.lhs.false180", pre := some "if.end177" }) :=
      end177_step_more (calls := calls) rfl hden (inc176_ult_one (by omega) hnlt)
    let eF : State := stateAt
      (end177Env (then171Env (leafBlock5Env
          (nodeBlock7Env (t161Env (then157Env env i10 nv) a i10 0x2d) 0x2d) 0x2d) 0x2d i10)
        (evalICmp .ne (JsonScanLane.vByte 0x2d) 0x2d#8)
        (BitVec.ofNat 64 i10 + 0x2#64) nv)
      { s with pc := "lor.lhs.false180", pre := some "if.end177" }
    have hi11 : lookupName eF.env "%i.11"
        = some (.int 64 (BitVec.ofNat 64 i10 + 0x2#64)) := by
      simp only [eF, stateAt, end177Env]; block_lk
    have huniv : ∀ k, runFuel calls (6 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody eF := by
      intro k
      rw [show 6 + k = 1 + (1 + (1 + (1 + (1 + (1 + k))))) from by omega,
        runFuel_jump_prefix h4, runFuel_jump_prefix h5, runFuel_jump_prefix h6,
        runFuel_jump_prefix h7, runFuel_jump_prefix h8, runFuel_jump_prefix h9]
    refine ⟨eF, rfl, rfl, ?_, ?_, ?_, ?_, ?_, huniv⟩
    · simp only [eF, end177Env, then171Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · simp only [eF, end177Env, then171Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
      first
       | (simp only [stateAt]; block_lk)
       | block_lk
    · rw [NumFastStarts.ofNat64_add_const (by omega)] at hi11
      exact hi11
    · simp only [eF, end177Env]; block_lk
    · intro idig5 ip5 fr5 fd5 hcells
      obtain ⟨h1, h2, h3, h4⟩ := hcells
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [eF, end177Env, then171Env, leafBlock5Env, nodeBlock7Env, t161Env, then157Env]
        first
         | (simp only [stateAt]; block_lk)
         | block_lk

/-! ### The merge: `cleanup223.thread`, `if.end226`, `if.end230`

The exponent run's exit folds its accumulator with the sign — `%sub221 = 0 -
%exp10` and the select on `%esign.0` — and `if.end226` carries the result with
the stop index, whose equality with `%n` is what opens the merge.  The two
`cleanup223.thread` edges are the run's exits (`land.lhs.true195`'s non-digit
byte and `if.end216`'s end-of-lexeme test), so `%i.12.lcssa.ph` is the run's
index at the head exit and `%n` at the back-edge exit. -/

/-- `cleanup223.thread`'s environment: the folded accumulator, the index and the
sign's select. -/
def cleanup223ThreadEnv (env : Env) (exp10 iv : BitVec 64) (esign : BitVec 1) : Env :=
  ("%spec.select446", .int 64 (if esign = 1 then exp10 else 0 - exp10)) ::
  ("%sub221", .int 64 (0 - exp10)) ::
  ("%i.12.lcssa.ph", .int 64 iv) ::
  ("%exp10.0.lcssa.ph", .int 64 exp10) :: env

theorem cleanup223Thread_denote_head {calls : Calls} {env : Env} {s : State}
    {exp10 iv : BitVec 64} {esign : BitVec 1}
    (hpre : s.pre = some "land.lhs.true195")
    (he : lookupName env "%exp10.0603" = some (.int 64 exp10))
    (hi : lookupName env "%i.12604" = some (.int 64 iv))
    (hesign : lookupName env "%esign.0" = some (.int 1 esign)) :
    denoteCode calls numFastCleanup223ThreadInstrs (stateAt env s) =
      some (stateAt (cleanup223ThreadEnv env exp10 iv esign) s) := by
  unfold numFastCleanup223ThreadInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%exp10.0603" _ he
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%i.12604" _ hi
  · simp only [runCells]
    rw [NumFastTier1.denoteCode_sub_imm_reg _ _ _ "%sub221" "%exp10.0.lcssa.ph"
      (by block_lk) _]
    rw [denoteCode_select_bit_reg _ _ _ "%spec.select446" "%esign.0"
      "%exp10.0.lcssa.ph" "%sub221" (by block_lk) (by block_lk) (by block_lk) _]
    rw [denoteCode_nil]
    rfl

theorem cleanup223Thread_denote_inc {calls : Calls} {env : Env} {s : State}
    {exp10 iv : BitVec 64} {esign : BitVec 1}
    (hpre : s.pre = some "if.end216")
    (he : lookupName env "%exp10.1" = some (.int 64 exp10))
    (hi : lookupName env "%n" = some (.int 64 iv))
    (hesign : lookupName env "%esign.0" = some (.int 1 esign)) :
    denoteCode calls numFastCleanup223ThreadInstrs (stateAt env s) =
      some (stateAt (cleanup223ThreadEnv env exp10 iv esign) s) := by
  unfold numFastCleanup223ThreadInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%exp10.1" _ he
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%n" _ hi
  · simp only [runCells]
    rw [NumFastTier1.denoteCode_sub_imm_reg _ _ _ "%sub221" "%exp10.0.lcssa.ph"
      (by block_lk) _]
    rw [denoteCode_select_bit_reg _ _ _ "%spec.select446" "%esign.0"
      "%exp10.0.lcssa.ph" "%sub221" (by block_lk) (by block_lk) (by block_lk) _]
    rw [denoteCode_nil]
    rfl

theorem cleanup223Thread_step_head {calls : Calls} {env : Env} {s : State}
    {exp10 iv : BitVec 64} {esign : BitVec 1}
    (hpc : s.pc = "cleanup223.thread")
    (hpre : s.pre = some "land.lhs.true195")
    (he : lookupName env "%exp10.0603" = some (.int 64 exp10))
    (hi : lookupName env "%i.12604" = some (.int 64 iv))
    (hesign : lookupName env "%esign.0" = some (.int 1 esign)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cleanup223ThreadEnv env exp10 iv esign)
        { s with pc := "if.end226", pre := some "cleanup223.thread" }) := by
  refine numFast_step_at (s' := stateAt (cleanup223ThreadEnv env exp10 iv esign) s)
    (b := ⟨"cleanup223.thread", numFastCleanup223ThreadInstrs, Term.br "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastCleanup223ThreadInstrs] using numFast_findBlock_cleanup223_thread
  · simpa only [denoteCode_nil] using
      cleanup223Thread_denote_head (calls := calls) hpre he hi hesign
  · simp only [execTerm, stateAt, hpc]

theorem cleanup223Thread_step_inc {calls : Calls} {env : Env} {s : State}
    {exp10 iv : BitVec 64} {esign : BitVec 1}
    (hpc : s.pc = "cleanup223.thread")
    (hpre : s.pre = some "if.end216")
    (he : lookupName env "%exp10.1" = some (.int 64 exp10))
    (hi : lookupName env "%n" = some (.int 64 iv))
    (hesign : lookupName env "%esign.0" = some (.int 1 esign)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cleanup223ThreadEnv env exp10 iv esign)
        { s with pc := "if.end226", pre := some "cleanup223.thread" }) := by
  refine numFast_step_at (s' := stateAt (cleanup223ThreadEnv env exp10 iv esign) s)
    (b := ⟨"cleanup223.thread", numFastCleanup223ThreadInstrs, Term.br "if.end226"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastCleanup223ThreadInstrs] using numFast_findBlock_cleanup223_thread
  · simpa only [denoteCode_nil] using
      cleanup223Thread_denote_inc (calls := calls) hpre he hi hesign
  · simp only [execTerm, stateAt, hpc]

/-- `if.end226`'s environment: the carried accumulator, the stop index and its
test against the length. -/
def ifEnd226Env (env : Env) (exp10 i14 nv : BitVec 64) : Env :=
  ("%cmp227.not", .int 1 (evalICmp .eq i14 nv)) ::
  ("%i.14", .int 64 i14) :: ("%exp10.4", .int 64 exp10) :: env

theorem ifEnd226_denote_thread {calls : Calls} {env : Env} {s : State}
    {exp10 i14 nv : BitVec 64}
    (hpre : s.pre = some "cleanup223.thread")
    (he : lookupName env "%spec.select446" = some (.int 64 exp10))
    (hi : lookupName env "%i.12.lcssa.ph" = some (.int 64 i14))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env exp10 i14 nv) s) := by
  unfold numFastIfEnd226Instrs
  block_eval

theorem ifEnd226_denote_end144 {calls : Calls} {env : Env} {s : State}
    {i10 nv : BitVec 64}
    (hpre : s.pre = some "if.end144")
    (hi : lookupName env "%i.10" = some (.int 64 i10))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env 0 i10 nv) s) := by
  unfold numFastIfEnd226Instrs
  block_eval

theorem ifEnd226_denote_leafBlock {calls : Calls} {env : Env} {s : State}
    {i10 nv : BitVec 64}
    (hpre : s.pre = some "LeafBlock")
    (hi : lookupName env "%i.10" = some (.int 64 i10))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env 0 i10 nv) s) := by
  unfold numFastIfEnd226Instrs
  block_eval

theorem ifEnd226_denote_leafBlock1 {calls : Calls} {env : Env} {s : State}
    {i10 nv : BitVec 64}
    (hpre : s.pre = some "LeafBlock1")
    (hi : lookupName env "%i.10" = some (.int 64 i10))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env 0 i10 nv) s) := by
  unfold numFastIfEnd226Instrs
  block_eval

theorem ifEnd226_step_merge {calls : Calls} {env : Env} {s : State}
    {exp10 i14 nv : BitVec 64}
    (hpc : s.pc = "if.end226")
    (hden : denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env exp10 i14 nv) s))
    (hbit : evalICmp .eq i14 nv = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd226Env env exp10 i14 nv)
        { s with pc := "if.end230", pre := some "if.end226" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd226Env env exp10 i14 nv) s)
    (b := ⟨"if.end226", numFastIfEnd226Instrs,
      Term.condbr (Operand.reg "%cmp227.not") "if.end230" "if.then229"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd226Instrs] using numFast_findBlock_if_end226
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd226Env env exp10 i14 nv) "%cmp227.not"
        = some (.int 1 (evalICmp .eq i14 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_one _ "%cmp227.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

theorem ifEnd226_step_refuse {calls : Calls} {env : Env} {s : State}
    {exp10 i14 nv : BitVec 64}
    (hpc : s.pc = "if.end226")
    (hden : denoteCode calls numFastIfEnd226Instrs (stateAt env s) =
      some (stateAt (ifEnd226Env env exp10 i14 nv) s))
    (hbit : evalICmp .eq i14 nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (ifEnd226Env env exp10 i14 nv)
        { s with pc := "if.then229", pre := some "if.end226" }) := by
  refine numFast_step_at (s' := stateAt (ifEnd226Env env exp10 i14 nv) s)
    (b := ⟨"if.end226", numFastIfEnd226Instrs,
      Term.condbr (Operand.reg "%cmp227.not") "if.end230" "if.then229"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd226Instrs] using numFast_findBlock_if_end226
  · simpa only [denoteCode_nil] using hden
  · have hlk : lookupName (ifEnd226Env env exp10 i14 nv) "%cmp227.not"
        = some (.int 1 (evalICmp .eq i14 nv)) := lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp227.not" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The refusing exit

`if.end226`'s equality test is what admits a lexeme into the merge, and a
lexeme whose exponent digits stop short of its end fails it: the block takes
`if.then229`, which stores the stop index at `%err`, and `cleanup300` returns
zero.  The two blocks are the head exit's tail; `if.then229`'s store is
`ifThen229_step_refuse` and the `phi` at the `if.then229` incoming is
`cleanup300_step_refuse`'s zero. -/

/-- `if.then229`'s step: the stop index, stored at `%err`, then the jump to
`cleanup300`. -/
theorem ifThen229_step_refuse {calls : Calls} {env : Env} {s : State}
    {i14 : BitVec 64} {err : Nat}
    (hpc : s.pc = "if.then229")
    (hi : lookupName env "%i.14" = some (.int 64 i14))
    (herr : lookupName env "%err" = some (.ptr err)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env
        { s with mem := writeBytes s.mem err (natToBytes i14.toNat 8),
                 pc := "cleanup300", pre := some "if.then229" }) := by
  refine numFast_step_at
    (s' := stateAt env { s with mem := writeBytes s.mem err (natToBytes i14.toNat 8) })
    (b := ⟨"if.then229",
      [Instr.store (Ty.int 64) (Operand.reg "%i.14") (Operand.reg "%err")],
      Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then229
  · rw [denoteCode_store64 calls env s "%i.14" "%err" hi herr, denoteCode_nil]
  · simp only [execTerm, stateAt, hpc]

/-- `cleanup300`'s run at the refusal's edge: the thirteen-member `phi`'s
`if.then229` incoming is the literal zero. -/
theorem cleanup300_denote_refuse {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "if.then229") :
    denoteCode calls numFastCleanup300Instrs (stateAt env s) =
      some (stateAt (numFastCleanup300Env env) s) := by
  unfold numFastCleanup300Instrs
  block_eval

/-- **The refusal's return.**  At `cleanup300` entered from `if.then229`, the
body returns the `phi`'s zero and leaves the memory the error store wrote. -/
theorem cleanup300_step_refuse {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "cleanup300") (hpre : s.pre = some "if.then229") :
    step calls numFastBody (stateAt env s) =
      .ret (some (.int 32 0)) (stateAt (numFastCleanup300Env env) s) := by
  refine numFast_step_at (s' := stateAt (numFastCleanup300Env env) s)
    (b := ⟨"cleanup300", numFastCleanup300Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_cleanup300
  · simpa only [denoteCode_nil] using cleanup300_denote_refuse (calls := calls) hpre
  · simp only [execTerm, evalOperand, stateAt, numFastCleanup300Env]
    rw [lookupName_cons_self]

/-! ### The merge opens

`if.end226`'s equality test is what admits a lexeme into the merge.  At the
back-edge exit the index is `%n` by construction (`%i.12.lcssa.ph` selects `%n`
there), so the test is `n = n` and the merge is taken; the head exit's index is
the run's own counter and is short of the length, so that edge is the refusal
above rather than the merge.  `expMerge_run_inc` ends at the merge's entry, which
is the state `JsonStage2NumFastTier1`'s `t1_ifEnd230_denote` names. -/

/-- **The merge's entry.**  The state at `if.end230` from the `if.end226` edge:
its predecessor, its memory, and the five registers the merge reads.  The
`%exp10.4` cell is the unfolded accumulator — the sign's select — so the caller
sees the sign rather than a name for it. -/
def mergeEntry (mem : Mem) (exp10 idig ip fr fdig : BitVec 64) (e : State) : Prop :=
  e.pc = "if.end230" ∧ e.pre = some "if.end226" ∧ e.mem = mem ∧
  lookupName e.env "%exp10.4" = some (.int 64 exp10) ∧
  lookupName e.env "%idig.4" = some (.int 64 idig) ∧
  lookupName e.env "%ip.5" = some (.int 64 ip) ∧
  lookupName e.env "%fr.5" = some (.int 64 fr) ∧
  lookupName e.env "%fdig.4" = some (.int 64 fdig)

/-- **The merge, from the exponent run's back-edge exit.**  `%i.12.lcssa.ph` is
`%n` there, so the index test is its own reflexivity and the merge is taken. -/
theorem expMerge_run_inc {calls : Calls} {env : Env} {s : State}
    {exp10 idig ip fr fdig : BitVec 64} {esign : BitVec 1} {n : Nat}
    (hpc : s.pc = "cleanup223.thread")
    (hpre : s.pre = some "if.end216")
    (he : lookupName env "%exp10.1" = some (.int 64 exp10))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hesign : lookupName env "%esign.0" = some (.int 1 esign))
    (hid : lookupName env "%idig.4" = some (.int 64 idig))
    (hip : lookupName env "%ip.5" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.4" = some (.int 64 fdig)) :
    ∃ e : State,
      mergeEntry s.mem (if esign = 1 then exp10 else 0 - exp10) idig ip fr fdig e ∧
      ∀ k, runFuel calls (2 + k) numFastBody (stateAt env s) = runFuel calls k numFastBody e := by
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (cleanup223ThreadEnv env exp10 (BitVec.ofNat 64 n) esign)
        { s with pc := "if.end226", pre := some "cleanup223.thread" }) :=
    cleanup223Thread_step_inc (calls := calls) hpc hpre he hn hesign
  have h2 : step calls numFastBody
      (stateAt (cleanup223ThreadEnv env exp10 (BitVec.ofNat 64 n) esign)
        { s with pc := "if.end226", pre := some "cleanup223.thread" }) =
      .jump (stateAt
        (ifEnd226Env (cleanup223ThreadEnv env exp10 (BitVec.ofNat 64 n) esign)
          (if esign = 1 then exp10 else 0 - exp10) (BitVec.ofNat 64 n) (BitVec.ofNat 64 n))
        { s with pc := "if.end230", pre := some "if.end226" }) :=
    ifEnd226_step_merge (calls := calls) rfl
      (ifEnd226_denote_thread (calls := calls) rfl
        (by simp only [cleanup223ThreadEnv, lookupName_cons_self])
        (by block_lk)
        (by block_lk))
      (NumFastStarts.eq_iff_one _ _ |>.mpr rfl)
  refine ⟨stateAt
      (ifEnd226Env (cleanup223ThreadEnv env exp10 (BitVec.ofNat 64 n) esign)
        (if esign = 1 then exp10 else 0 - exp10) (BitVec.ofNat 64 n) (BitVec.ofNat 64 n))
      { s with pc := "if.end230", pre := some "if.end226" },
    ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [stateAt, ifEnd226Env, cleanup223ThreadEnv]
    block_lk
  · simp only [stateAt, ifEnd226Env, cleanup223ThreadEnv]; block_lk
  · simp only [stateAt, ifEnd226Env, cleanup223ThreadEnv]; block_lk
  · simp only [stateAt, ifEnd226Env, cleanup223ThreadEnv]; block_lk
  · simp only [stateAt, ifEnd226Env, cleanup223ThreadEnv]; block_lk
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1, runFuel_jump_prefix h2]

/-! ### The accumulator's value, at the model's fold

The digit runs carry `digitFold bs start len` — the bytes at `start`, the first
`len` of them, folded base ten — while the model's `Decimal.digitsNat` folds the
whole of its argument.  The two agree when the run starts at the first digit and
covers all of them, and the run's `19`-digit guard is inert when the count is
inside it: the tie is then the model's own fold, read at the run's counters. -/

/-- A run's fold over the whole list is the model's `digitsNat`. -/
theorem digitFold_eq_digitsNat (bs : Bytes) :
    digitFold bs.data.toList 0 bs.length =
      Decimal.digitsNat bs := by
  have hlen : bs.data.toList.length = bs.length := Array.length_toList
  simp only [digitFold, Decimal.digitsNat, List.drop_zero, ← hlen, List.take_length]

/-- The guard's `min` is inert below the cap. -/
theorem min_eq_left_of_le {a b : Nat} (h : a ≤ b) : min a b = a :=
  Nat.min_eq_left h

/-- **The tie's shape.**  A run that starts at the first of `bs`'s digits and
covers all of them computes the model's fold of the bytes it covered, with the
`19`-digit guard inert. -/
theorem digitFold_tie {bs : List UInt8} {ipBytes : List UInt8} {start len : Nat}
    (hbytes : ipBytes = (bs.drop start).take len) (hlen : len ≤ 19) :
    digitFold bs start (min len 19) =
      ipBytes.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 := by
  rw [min_eq_left_of_le hlen, digitFold, hbytes]

/-! ### `entry` to the integer run's exit

The scan begins at `entry`, which branches on the lexeme's emptiness: a
non-empty lexeme goes to the sign check, and the dispatch from there is
`JsonStage2NumFastStarts.intRun_start`'s seven steps.  The integer run then
consumes the `int` part and stops at one of its two exits, `if.end68` (a
non-digit) or `if.end230` (the lexeme's end).  The fuel is a term of the
arguments: one step for the emptiness test, seven for the dispatch, and
`(n - i0 + 1) * 4` for the run.

The staging this theorem consumes is a well-formed `int` part — its lead a
`'1' … '9'`, the eight-digit fast path's guard refused, and the lexeme's length
past the lead.  Which of the run's two exits is taken depends on the bytes, so
the conclusion is the run's own exit predicate rather than one of the two
branches. -/

theorem entry_step_land {calls : Calls} {env : Env} {s : State} {nv : BitVec 64}
    (hpc : s.pc = "entry") (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .eq nv 0x0000000000000000#64 = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64))
        { s with next := s.next + 768 + 1568 + 4 + 4 + 8,
                 pc := "land.lhs.true", pre := some "entry" }) := by
  refine numFast_step_at
    (s' := stateAt (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64))
      { s with next := s.next + 768 + 1568 + 4 + 4 + 8 })
    (b := ⟨"entry", numFastEntryInstrs,
      Term.condbr (Operand.reg "%cmp.not") "if.end" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_entry
  · simpa only [denoteCode_nil, stateAt] using
      numFast_entry_denote (calls := calls) (env := env) (s := s) (nxt := s.next) hn
  · have hlk : lookupName
        (numFastEntryEnv env s.next (evalICmp .eq nv 0x0000000000000000#64)) "%cmp.not"
        = some (.int 1 (evalICmp .eq nv 0x0000000000000000#64)) := by
      simp only [stateAt, numFastEntryEnv]
      block_lk
    rw [numFast_execTerm_condbr_zero _ "%cmp.not" "if.end" "land.lhs.true" hlk hbit]
    simp only [stateAt, hpc]

/-- The `entry` block's five cells are behind every parameter read. -/
theorem entry_env_lookup_p {env : Env} {nxt : Nat} {cmp : BitVec 1} {a : Nat}
    (hp : lookupName env "%p" = some (.ptr a)) :
    lookupName (numFastEntryEnv env nxt cmp) "%p" = some (.ptr a) := by
  simp only [numFastEntryEnv]
  block_lk

theorem entry_env_lookup_n {env : Env} {nxt : Nat} {cmp : BitVec 1} {n : Nat}
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    lookupName (numFastEntryEnv env nxt cmp) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
  simp only [numFastEntryEnv]
  block_lk

/-- **The scan reaches the integer run's exit.**  From `entry` at a non-empty
lexeme whose `int` part leads with `'1' … '9'` and whose eight-digit guard is
refused, the body runs to `if.end68` or `if.end230` within
`8 + (n - i0 + 1) * 4` control steps, the run's own exit predicate carrying the
counters and the accumulator's fold. -/
theorem intScan_run {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {b b0 : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + NumFastStarts.negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n)
    (hnext : NumFastStarts.negIndex b + 1 < n)
    (hfast : n < NumFastStarts.negIndex b + 9) (hnlt : n < 2 ^ 63) :
    ∃ (e : State) (j : Nat), j ≤ 8 + (n - (NumFastStarts.negIndex b + 1) + 1) * 4 ∧
      intRunExit s.mem bs a n (NumFastStarts.negIndex b + 1) 1 e ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hn64 : n < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 n ≠ 0x0000000000000000#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at h2
    simp at h2
    omega
  let cmp : BitVec 1 := evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64
  have hbit0 : cmp = 0 := NumFastStarts.eq_zero_iff _ _ |>.mpr hne
  let s1 : State := { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "land.lhs.true", pre := some "entry" }
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (numFastEntryEnv env s.next cmp) s1) :=
    entry_step_land (calls := calls) hpc hn hbit0
  obtain ⟨e0, hinv0, _, hrun0⟩ :=
    NumFastStarts.intRun_start (calls := calls)
      (env := numFastEntryEnv env s.next cmp) (s := s1)
      (env0 := numFastEntryEnv env s.next cmp)
      rfl rfl
      (entry_env_lookup_p hp) (entry_env_lookup_n hn)
      hread hsign hbyte hlead hltn hnext hfast hnlt
      (numFastKept_stateAt _ s1)
  obtain ⟨e1, j1, hj1, _hexitb, hexitw, hrun1⟩ :=
    (intRunBoundLoop s.mem a n (NumFastStarts.negIndex b + 1) 1 bs 4 (by omega)).run_from
      (n - (NumFastStarts.negIndex b + 1)) e0 0 hinv0
  refine ⟨e1, 1 + (7 + j1), ?_, hexitw, ?_⟩
  · rw [show 1 + (7 + j1) = 8 + j1 from by omega]
    exact Nat.add_le_add_left hj1 8
  · intro k
    rw [show 1 + (7 + j1) + k = 1 + (7 + (j1 + k)) from by omega,
      runFuel_jump_prefix h1]
    exact (hrun0 (j1 + k)).trans (hrun1 k)

/-! ### The merge's entry from the bound exit

The integer run's `if.end230` exit is written by `if.end62`'s end-of-lexeme test,
and the merge's five `phi`s read that edge's three registers with the two
zeroes.  The block's own gate is `JsonStage2NumFastTier1`'s `t1GateEnv`, so this
lemma is the state its `t1_ifEnd230_step` consumes. -/

theorem ifEnd230_denote_end62 {calls : Calls} {env : Env} {s : State}
    {i7 ip : BitVec 64}
    (hpre : s.pre = some "if.end62")
    (h7 : lookupName env "%7" = some (.int 64 i7))
    (hip : lookupName env "%ip.4" = some (.int 64 ip)) :
    denoteCode calls numFastIfEnd230Instrs (stateAt env s) =
      some (stateAt (NumFastTier1.t1GateEnv env 0 i7 ip 0 0) s) := by
  unfold numFastIfEnd230Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%7" _ h7
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%ip.4" _ hip
  · simp only [phiIncoming]; rfl
  · rfl
  · simp only [phiIncoming]; rfl
  · rfl
  · rw [denoteCode_sub_reg _ _ _ "%sub231" "%exp10.4731" "%fdig.4719727"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_add_reg _ _ _ "%add232" "%fdig.4719727" "%idig.4709716730"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_icmp_ult_imm _ _ _ "%cmp233" "%add232" (by block_lk) _]
    rw [denoteCode_add_imm _ _ _ "%28" "%sub231" (by block_lk) _]
    rw [denoteCode_icmp_ult_imm _ _ _ "%29" "%28" (by block_lk) _]
    rw [NumFastTier1.denoteCode_select_bit1_imm _ _ _ "%or.cond304" "%cmp233" "%29"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_nil]
    rfl

theorem ifEnd230_step_end62 {calls : Calls} {env : Env} {s : State}
    {i7 ip : BitVec 64}
    (hpc : s.pc = "if.end230")
    (hpre : s.pre = some "if.end62")
    (h7 : lookupName env "%7" = some (.int 64 i7))
    (hip : lookupName env "%ip.4" = some (.int 64 ip))
    (hbit : evalICmp .ult (0 + i7) (20#64) = 1 ∧
      evalICmp .ult ((0 - 0) + (45#64)) (91#64) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastTier1.t1GateEnv env 0 i7 ip 0 0)
        { s with pc := "if.then241", pre := some "if.end230" }) := by
  refine numFast_step_at (s' := stateAt (NumFastTier1.t1GateEnv env 0 i7 ip 0 0) s)
    (b := ⟨"if.end230", numFastIfEnd230Instrs,
      Term.condbr (Operand.reg "%or.cond304") "if.then241" "if.end285"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd230Instrs] using numFast_findBlock_if_end230
  · simpa only [denoteCode_nil] using ifEnd230_denote_end62 (calls := calls) hpre h7 hip
  · have hlk : lookupName (NumFastTier1.t1GateEnv env 0 i7 ip 0 0) "%or.cond304"
        = some (.int 1
          (if evalICmp .ult (0 + i7) (20#64) = 1 then
            evalICmp .ult ((0 - 0) + (45#64)) (91#64) else 0)) := by
      simp only [NumFastTier1.t1GateEnv]
      block_lk
    have hone : (if evalICmp .ult (0 + i7) (20#64) = 1 then
        evalICmp .ult ((0 - 0) + (45#64)) (91#64) else 0) = 1 := by
      rw [if_pos hbit.1]
      exact hbit.2
    rw [numFast_execTerm_condbr_one _ "%or.cond304" _ _ hlk hone]
    simp only [stateAt, hpc]

/-! ### Axiom footprints

The pins are the build's check that no step, no run and no composition has
acquired an axiom.  `Classical.choice` appears only through the digit windows'
`by_contra` lemmas (`JsonStage2NumFastStarts`), which is where the scan's tests
are decided; the merge blocks and the folds are at `[propext, Quot.sound]`, and
the tie's arithmetic at `[propext]`. -/

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nestTo157_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestTo157_e

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nestTo157_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestTo157_E

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nest_nomarker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nest_nomarker

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nestFrom157_nosign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestFrom157_nosign

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nestFrom157_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nestFrom157_sign

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.cleanup223Thread_denote_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cleanup223Thread_denote_head

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.expMerge_run_inc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms expMerge_run_inc

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.intScan_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_run

/-- **The scan reaches the merge.**  From `entry` at a non-empty lexeme whose
`int` part leads with `'1' … '9'`, whose eight-digit guard is refused and whose
bytes from the run's start to the lexeme's end are all digits, the body reaches
`if.end230` within `8 + (n - i0 + 1) * 4` control steps with the end-of-lexeme
exit word: the cursor, the length, the count `d0 + (n - i0)` and the folded
accumulator, plus the predecessor `if.end62`, `%7` and the memory the fold was
taken at.  The dispatch reads the sign at position 0 and the lead digit, which is
what fixes `i0 = negIndex b + 1` and `d0 = 1`; the decimal point is not read on
this route, because the lexeme ends at the integer part. -/
theorem intScan_end230 {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {b b0 : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + NumFastStarts.negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n)
    (hnext : NumFastStarts.negIndex b + 1 < n)
    (hfast : n < NumFastStarts.negIndex b + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, NumFastStarts.negIndex b + 1 ≤ k → k < n →
      IsDigitB (bs.getD k 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 8 + (n - (NumFastStarts.negIndex b + 1) + 1) * 4 ∧
      intRunEndWord s.mem bs a n (NumFastStarts.negIndex b + 1) 1 e ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hn64 : n < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 n ≠ 0x0000000000000000#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at h2
    simp at h2
    omega
  let cmp : BitVec 1 := evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64
  have hbit0 : cmp = 0 := NumFastStarts.eq_zero_iff _ _ |>.mpr hne
  let s1 : State := { s with next := s.next + 768 + 1568 + 4 + 4 + 8, pc := "land.lhs.true", pre := some "entry" }
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (numFastEntryEnv env s.next cmp) s1) :=
    entry_step_land (calls := calls) hpc hn hbit0
  obtain ⟨e0, hinv0, _, hrun0⟩ :=
    NumFastStarts.intRun_start (calls := calls)
      (env := numFastEntryEnv env s.next cmp) (s := s1)
      (env0 := numFastEntryEnv env s.next cmp)
      rfl rfl
      (entry_env_lookup_p hp) (entry_env_lookup_n hn)
      hread hsign hbyte hlead hltn hnext hfast hnlt
      (numFastKept_stateAt _ s1)
  obtain ⟨e1, j1, hj1, _, hexitw, hrun1⟩ :=
    (intRunEndBoundLoop s.mem a n (NumFastStarts.negIndex b + 1) 1 bs 4 (by omega)
      hdigits).run_from (n - (NumFastStarts.negIndex b + 1)) e0 0 hinv0
  refine ⟨e1, 1 + (7 + j1), ?_, hexitw, ?_⟩
  · rw [show 1 + (7 + j1) = 8 + j1 from by omega]
    exact Nat.add_le_add_left hj1 8
  · intro k
    rw [show 1 + (7 + j1) + k = 1 + (7 + (j1 + k)) from by omega,
      runFuel_jump_prefix h1]
    exact (hrun0 (j1 + k)).trans (hrun1 k)

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.intScan_end230' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_end230

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.ifEnd230_denote_end62' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd230_denote_end62

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.ifEnd230_step_end62' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd230_step_end62

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.digitFold_eq_digitsNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms digitFold_eq_digitsNat

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.digitFold_tie' does not depend on any axioms -/
#guard_msgs in
#print axioms digitFold_tie

/-! ### The accumulators, read as the model's folds

The runs' exit predicates carry the accumulated word as `digitFold` over the
lexeme's bytes.  `Decimal.digitsNat` folds the *decimal part's* own bytes.  The
tie between the two is the pair below: `intRunExit_end230` and
`fracRunExit_end230` expose the run's index and word at the `if.end230` edge, and
`digitsNat_word` reads that word as the part's fold once the run's
bytes are the part's and the count is inside the `19`-digit guard.  The count's
bound is the caller's: the guard is the accumulators' `%idig < 19` / `%fdig < 19`,
so a lexeme inside the tier-1 window (`≤ 15` digits) satisfies it outright. -/

/-- **The integer run's word at the lexeme's end.** -/
theorem intRunExit_end230 {mem0 : Mem} {bs : List UInt8} {p n i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end230") (he : intRunExit mem0 bs p n i0 d0 e) :
    lookupName e.env "%inc64" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%inc63"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
      lookupName e.env "%ip.4" = some (.int 64
        (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))) := by
  rcases he with hleft | ⟨h230, _, _, _, _, _, hi, hid, hip, _⟩
  · rw [hleft.1] at hpc; exact absurd hpc (by decide)
  · exact ⟨hi, hid, hip⟩

/-- **The fraction run's word at the lexeme's end.** -/
theorem fracRunExit_end230 {mem0 : Mem} {bs : List UInt8} {p n i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end230") (he : fracRunExit mem0 bs p n i0 d0 e) :
    lookupName e.env "%inc142" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%inc141"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
      lookupName e.env "%fr.4" = some (.int 64
        (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))) := by
  rcases he with hleft | ⟨h230, _, _, _, _, hi, hid, hfr, _, _⟩
  · rw [hleft.1] at hpc; exact absurd hpc (by decide)
  · exact ⟨hi, hid, hfr⟩

/-- **A run's accumulated word is the model's fold of the part's bytes.**  The
run's bytes at its start are the decimal part's, and the count is inside the
`19`-digit guard. -/
theorem digitsNat_word {bs : List UInt8} {part : List UInt8} {start len : Nat}
    (hshape : part = (bs.drop start).take len) (hlen : len ≤ 19) :
    BitVec.ofNat 64 (digitFold bs start (min len 19)) =
      BitVec.ofNat 64 (part.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0) := by
  rw [digitFold_tie hshape hlen]

/-- **The integer part's value at the model.**  When the bytes the integer run
consumed are `d.ip`'s and the count is inside the guard, the run's word is
`Decimal.digitsNat d.ip` — the premise `JsonStage2NumFastTier1`'s
`t1_add244_eq_mantissa` takes as `hip`. -/
theorem ip_word_digitsNat {bs : List UInt8} {d : Decimal} {start len : Nat}
    (hshape : d.ip.data.toList = (bs.drop start).take len) (hlen : len ≤ 19)
    {ip : BitVec 64} (hip : ip = BitVec.ofNat 64 (digitFold bs start (min len 19))) :
    ip = BitVec.ofNat 64 (Decimal.digitsNat d.ip) := by
  rw [hip, digitFold_tie (ipBytes := (bs.drop start).take len) rfl hlen, ← hshape]
  rfl

/-- **The fraction part's value at the model.**  The same tie for the fraction
run's word, read as the `hfr` premise of `t1_add244_eq_mantissa`. -/
theorem fr_word_digitsNat {bs : List UInt8} {fs : Bytes} {start len : Nat}
    (hshape : fs.data.toList = (bs.drop start).take len) (hlen : len ≤ 19)
    {fr : BitVec 64} (hfr : fr = BitVec.ofNat 64 (digitFold bs start (min len 19))) :
    fr = BitVec.ofNat 64 (Decimal.digitsNat fs) := by
  rw [hfr, digitFold_tie (ipBytes := (bs.drop start).take len) rfl hlen, ← hshape]
  rfl

/-! ### Axiom footprints of the ties

Nothing here is more than the fold's own arithmetic: the extraction lemmas are
projections, and the model reads are `digitFold_tie` and the definition of
`Decimal.digitsNat`. -/

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.intRunExit_end230' does not depend on any axioms -/
#guard_msgs in
#print axioms intRunExit_end230

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.fracRunExit_end230' does not depend on any axioms -/
#guard_msgs in
#print axioms fracRunExit_end230

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.digitsNat_word' does not depend on any axioms -/
#guard_msgs in
#print axioms digitsNat_word

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.ip_word_digitsNat' does not depend on any axioms -/
#guard_msgs in
#print axioms ip_word_digitsNat

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.fr_word_digitsNat' does not depend on any axioms -/
#guard_msgs in
#print axioms fr_word_digitsNat

/-! ### The fraction run's composition, and the nest's entry

`fracRun_start` closes the fraction dispatch from `land.lhs.true71`, and the run
is a `BoundLoop` over `land.lhs.true119`; this composes the two.  The fraction
run's `if.end144` exit is the nest's entry: `ifEnd144_denote_frac` reads the three
registers and `ifEnd144_step` takes the marker's block, so `nestEntry_run` carries
an exit state to `land.lhs.true147` with `%i.10` fixed. -/

/-- **The fraction scan reaches its exit.**  From `land.lhs.true71` — the `.`
test, taken — with a digit after the `.`, the length past it and the eight-digit
guard refused, the dispatch and the run reach the run's exit predicate within
`6 + (n - i0 + 1) * 4` control steps, `i0 = i5 + 1`. -/
theorem fracScan_run {env : Env} {s : State} {a n : Nat} {bs : List UInt8}
    {i5 : Nat} {bd bd2 : UInt8}
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
    ∃ (e : State) (j : Nat), j ≤ 6 + (n - (i5 + 1) + 1) * 4 ∧
      fracRunExit s.mem bs a n (i5 + 1) 0 e ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  obtain ⟨e0, hinv0, _hcell0, _, hrun0⟩ :=
    NumFastStarts.fracRun_start (calls := calls) hpc hp hn hread hi5 hparts
      hdot hdoteq hd2 hd2digit hltn hfast hnlt
  obtain ⟨e1, j1, hj1, _hexitb, hexitw, hrun1⟩ :=
    (fracRunBoundLoop s.mem a n (i5 + 1) 0 bs 4 (by omega)).run_from
      (n - (i5 + 1)) e0 0 hinv0
  refine ⟨e1, 6 + j1, ?_, hexitw, ?_⟩
  · exact Nat.add_le_add_left hj1 6
  · intro k
    rw [show 6 + j1 + k = 6 + (j1 + k) from by omega, hrun0 (j1 + k)]
    exact hrun1 k

/-- **The nest's entry from the fraction run's exit.**  The `if.end144` edge that
the fraction run leaves by reads `%fr.3593`, `%fdig.3594` and `%i.9595`, and the
block's own test then takes the marker's block: one control step from
`if.end144` to `land.lhs.true147` with `%i.10` fixed at the run's stop index and
the run's two cells carried as `if.end144`'s phis. -/
theorem nestEntry_run {calls : Calls} {env : Env} {s : State} {a : Nat}
    {fr fdig i10 nv : BitVec 64}
    (hpc : s.pc = "if.end144")
    (hpre : s.pre = some "land.lhs.true119")
    (hp : lookupName env "%p" = some (.ptr a))
    (hfr : lookupName env "%fr.3593" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hi : lookupName env "%i.9595" = some (.int 64 i10))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ult i10 nv = 1) :
    ∃ e : State, e.pc = "land.lhs.true147" ∧ e.pre = some "if.end144" ∧
      e.mem = s.mem ∧
      lookupName e.env "%i.10" = some (.int 64 i10) ∧
      lookupName e.env "%p" = some (.ptr a) ∧
      lookupName e.env "%n" = some (.int 64 nv) ∧
      lookupName e.env "%fr.5" = some (.int 64 fr) ∧
      lookupName e.env "%fdig.4" = some (.int 64 fdig) ∧
      ∀ k, runFuel calls (1 + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hden := ifEnd144_denote_frac (calls := calls) (s := s) hpre hfr hfd hi hn
  have hstep := ifEnd144_step (calls := calls) hpc hden hbit
  refine ⟨stateAt (ifEnd144Env env fr fdig i10 nv)
    { s with pc := "land.lhs.true147", pre := some "if.end144" },
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, ifEnd144Env, ifEnd144PhiEnv]
    block_lk
  · simp only [stateAt, ifEnd144Env, ifEnd144PhiEnv]
    block_lk
  · simp only [stateAt, ifEnd144Env, ifEnd144PhiEnv]
    block_lk
  · simp only [stateAt, ifEnd144Env, ifEnd144PhiEnv]
    block_lk
  · simp only [stateAt, ifEnd144Env, ifEnd144PhiEnv]
    block_lk
  · intro k
    rw [runFuel_jump_prefix hstep k]

/-! ### Axiom footprints of the fraction scan -/

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.fracScan_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracScan_run

/-- info: 'LeanLLVM.Refinement.NumFastScanRun.nestEntry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nestEntry_run

end NumFastScanRun

end LeanLLVM.Refinement
