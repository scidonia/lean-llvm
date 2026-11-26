/-
The release theorem's number-conversion assumption, stated as one value beside
its compiler and ABI steps.

`JsonNumberPremises` proved what the tree's definitions allow at the walk's number
arm and named the two obstructions: the scanner's token extent (Premise 1, the
`NumberTokenExtentAt` lane) and the emitted accumulators' agreement with the
reader's decimal (Premise 2, this lane).  The release theorem does not discharge
either; it carries them.  This module states the second as a named structure,
`JsonNumFastAssumed`, so the assumption list cites one value per number token
instead of prose, and proves that the value is exactly what the body arm consumes.

## The assumption

`JsonNumFastAssumed calls epow bs d i0 d0 n` has two fields.

**The callee half — `NumFastCalleesAnswered calls epow`.**  The conversion's
`Calls` selection is the tree's model of the three out-of-line functions:
`num_d8_el1` (`kernel/json/measured/numf_el1.h`, modelled as `numD8Answer`),
`num_el_el1` (`numel_el.h`, modelled as `numElAnswer epow`) and `stk_mul_u64`
(`kernel/json/stage2.c`, modelled as `numStkMulAnswer`).  `stage2NumFastCalls epow`
is that model: `numFastCalls` answers the three symbols and delegates the rest to
the walk's `s2HelperCalls`.  The field says the release theorem's selection is
this value; the content that the compiled bodies behave as their measured C text
is the trust statement the structure names, and is what the discharge path below
would replace with refined bodies.  At `s2HelperCalls` the three sites are `ub`
(`JsonStage2NumFastArm.numFast_step_ifEnd268_ub` and its siblings), which is why
the arm takes `calls` as a parameter at all.

**The segmentation half — `NumFastScanSegmentation bs d i0 d0 n`.**  The emitted
scan's digit run at the lexeme's integer part segments the lexeme the way the
tie takes it: `intDigits d = d0 + (n - i0)`, and `d.ip`'s bytes are the run's own
slice `(bs.drop (i0 - d0)).take (d0 + (n - i0))`.  These are exactly
`NumFastSeams.t1_intRun_tie`'s `hint` and `hshape`, and the fraction and exponent
runs take the same shape at their own seams (`t1_fracRun_tie`, `expExit_merge_back`).

## Its consumer, and the chain

`JsonStage2NumFastArm.NumFastBodyArm` is the body statement the release theorem's
number arm needs: at a staged entry state the conversion runs to its return,
writes `strtodSpec`'s eight bytes at `%out` and returns `1`.  Its `calls`
parameter is the callee half's value, and its `if.end230`/`if.then241` arm reads
the five merge registers that the agreement names.

The chain, each link proved here or in `JsonNumberPremises`:

* `numFast_ifEnd268_denote_of_assumed`, `numFast_whileBodyPreheader_denote_of_assumed`,
  `numFast_ifThen178_denote_of_assumed` — the callee half answers the three sites:
  the tree's own `_denote_some` facts at `stage2NumFastCalls epow` are the
  selection's;
* `numFastAccumulatorAgreement_of_assumed` — the segmentation half plus the run's
  end-of-lexeme exit gives `NumFastAccumulatorAgreement` at the run's successor,
  by `JsonNumberPremises.numFastAccumulatorAgreement_intRun`;
* `numFastAccumulatorAgreement_merge` — the merge environment `numFastGateAt env d
  (d.fr.getD empty)` *is* the agreement, definitionally, for every decimal;
* `numFastKernelAt_agreement` — the agreement survives into the tier-1 region's
  environment `numFastKernelAt`, which is `t1MantEnv` over `numFastGateAt`, so the
  `if.then241` arm that `NumFastBodyArm` runs reads the model's five cells;
* `numFastBodyArm_of_calleesAnswered` and `numFastBodyArm_answer_of_assumed` —
  `NumFastBodyArm` at any selection the callee half answers is the arm at the
  model, and at that selection its answer is `strtodSpec`'s bytes.

## The discharge path

* **The callee half.**  Refined LLVM bodies for the three functions, each proved
  to refine its model at the `Calls` entry, plus the measurements that pin the
  bodies: the captured IR from `probes/install/ir/capture-stage2.sh` at the
  measured line, the C text in `kernel/json/measured/numf_el1.h`,
  `kernel/json/measured/numel_el.h` and `kernel/json/stage2.c`, the hashes in
  `kernel/json/measured/SHA256SUMS`, and `docs/contract.md`'s `num_fast_el1` row
  for the pins.  The proofs would live in new modules beside
  `JsonStage2NumFastCalls.lean` — a `JsonStage2NumFastCalleeBodies.lean` (or one
  module per callee) stating `numD8Answer`/`numElAnswer`/`numStkMulAnswer` against
  the captured bodies, in the shape `JsonStage2NumFastCalls` already uses for the
  site denotations.
* **The segmentation half.**  The emitted scan's reader agreement: the run's own
  counters and bytes against `StrtodReader.reader`'s decimal, including
  `num_d8_el1`'s eight-digit fast path (`JsonStage2NumFastScanFast.lean`) and the
  fraction and exponent runs' seams.  A proof would extend
  `JsonStage2NumFastDigitRuns.lean`/`JsonStage2NumFastSeams.lean` from the exits
  to the reader, or sit in a new `JsonStage2NumFastScanSegmentation.lean`.
* **Tier 3.**  The remaining blocks of the fallback region, from
  `for.body.i.i566.i.i.epil`, in `JsonStage2NumFastTier3.lean`: the traversal
  (`t3_traversal_counts_1_3`), the copy (`copy_retained`, `copy_sticky`,
  `copy_counters`, `t3_copy_denote`) and the proximity estimate
  (`roundMag_dist_le_step`, `proximity_scale`, `t3_scale_of_ulp`) are closed at
  their statements; the composition over the remaining blocks, and
  `JsonStage2NumFastToDouble.lean`'s window, are not.

## What it is not

It is not a proof about the C.  No semantics of C, no compiler translation and no
link step appears here; `numD8Answer`, `numElAnswer` and `numStkMulAnswer` are
Lean readings of the measured text, and the field says the release theorem's
selection is that model.  It is not a refinement of the three callees: no LLVM
body of `num_d8_el1`, `num_el_el1` or `stk_mul_u64` is modelled or proved, which
is exactly the gap the discharge path names.  It is not the token-extent premise:
`JsonNumberPremises.NumberTokenExtentAt` is the other half, and holds the span's
bytes; this structure takes those bytes (`bs`) as given and holds only their split
into parts.  And it does not weaken or restate any existing definition or theorem:
`NumFastBodyArm`, `numFastAccumulatorAgreement_intRun`, `t1_intRun_tie` and the
site denotations keep their statements, and this module only names what they
consume.

It adds no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonNumberPremises
import LeanLLVM.Refinement.JsonStage2NumFastCalls

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open ByteString

/-! ### The two halves

The callee half is the selection; the segmentation half is the seam's two
hypotheses, at the run's parameters. -/

/-- **The callee half.**  The conversion's `Calls` selection is the tree's model
of the three out-of-line functions: `numFastCalls` answers `num_d8_el1`,
`num_el_el1` and `stk_mul_u64` from the measured C text and delegates the rest to
the walk's helpers.  The content that the compiled bodies behave as that text is
the trust statement, not an equality this module proves. -/
def NumFastCalleesAnswered (calls : Calls) (epow : Int → Option EPow) : Prop :=
  calls = stage2NumFastCalls epow

/-- **The segmentation half.**  The emitted scan's integer run, at its own start
`i0`, accumulator count `d0` and lexeme length `n`, consumes exactly the decimal's
integer-part digits: the count is `intDigits d`, and `d.ip` is the lexeme's slice
from where the part begins.  These are `t1_intRun_tie`'s `hint` and `hshape`. -/
def NumFastScanSegmentation (bs : List UInt8) (d : Decimal) (i0 d0 n : Nat) : Prop :=
  intDigits d = d0 + (n - i0) ∧
    d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0))

/-- **The release theorem's number-conversion assumption.**  One value per number
token, cited beside the compiler and ABI steps: the conversion's three out-of-line
callees are the tree's model of their measured C text, and the emitted scan's
segmentation is the one the seams take.  The token-extent premise is the other
lane (`JsonNumberPremises.NumberTokenExtentAt`) and is not repeated here. -/
structure JsonNumFastAssumed (calls : Calls) (epow : Int → Option EPow)
    (bs : List UInt8) (d : Decimal) (i0 d0 n : Nat) : Prop where
  /-- The selection is the model of the three out-of-line callees. -/
  callees : NumFastCalleesAnswered calls epow
  /-- The scan's integer run segments the decimal the way the tie takes it. -/
  segmentation : NumFastScanSegmentation bs d i0 d0 n

/-- **The callee half is inhabited by the tree's model.**  The selection the tree
already supplies answers the three symbols by construction; what the assumption
adds is that the compiled bodies agree with that model. -/
theorem numFastCalleesAnswered_model (epow : Int → Option EPow) :
    NumFastCalleesAnswered (stage2NumFastCalls epow) epow := rfl

/-! ### The callee half at its three sites

The tree's `_denote_some` facts are stated at `stage2NumFastCalls epow`; the
assumption rewrites the selection to the model, so each site's run is the model's.
`NumFastBodyArm`'s `calls` parameter is what these three sites read. -/

/-- **`if.end268`'s site, at the assumed selection.**  The kernel call resolves and
the block binds its answer. -/
theorem numFast_ifEnd268_denote_of_assumed {calls : Calls} {epow : Int → Option EPow}
    {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n)
    {env : Env} {s : State} {a b : BitVec 64} {q : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    ∃ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x ∧
      denoteCode calls numFastIfEnd268Instrs (stateAt env s) =
        some (stateAt
          (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
           ("%call270", .int 32 x) :: env)
          { s with mem := r.mem, next := r.next }) := by
  have hc := h.callees
  unfold NumFastCalleesAnswered at hc
  rw [hc]
  exact numFast_ifEnd268_denote_some epow ha hb hd

/-- **`while.body.preheader`'s site, at the assumed selection.**  The eight-digit
reader resolves and the block binds its answer. -/
theorem numFast_whileBodyPreheader_denote_of_assumed {calls : Calls}
    {epow : Int → Option EPow} {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n)
    {env : Env} {s : State} {a v8a : Nat} {idx : BitVec 64}
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    ∃ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x ∧
      denoteCode calls numFastWhileBodyPreheaderInstrs (stateAt env s) =
        some (stateAt
          (("%tobool.not932", .int 1 (evalICmp .eq x 0)) ::
           ("%call931", .int 32 x) ::
           ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          { s with mem := r.mem, next := r.next }) := by
  have hc := h.callees
  unfold NumFastCalleesAnswered at hc
  rw [hc]
  exact numFast_whileBodyPreheader_denote_some epow hp ho hv8 hpos

/-- **`if.then178.i.i`'s site, at the assumed selection.**  The big multiply
resolves and the block denotes. -/
theorem numFast_ifThen178_denote_of_assumed {calls : Calls} {epow : Int → Option EPow}
    {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n)
    {env : Env} {s : State} {p10 pow : Nat} {k v : BitVec 64}
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    ∃ s' : State,
      denoteCode calls numFastIfThen178Instrs (stateAt env s) = some s' := by
  have hc := h.callees
  unfold NumFastCalleesAnswered at hc
  rw [hc]
  exact numFast_ifThen178_denote_some epow hpre hk hg hpos hread hpow

/-! ### The segmentation half at the merge

The run's end-of-lexeme exit plus the segmentation is the agreement at its
successor; the merge environment is the agreement unconditionally; and the
tier-1 region's environment extends it.  This is the chain `NumFastBodyArm` reads
at `if.end230` and `if.then241`. -/

/-- **The agreement at the run's successor, from the assumption.**  At the integer
run's end-of-lexeme exit `if.end230`, the segmentation half is the tie's `hint`
and `hshape`, so the successor's five merge registers are the reader's decimal
fields.  This is `numFastAccumulatorAgreement_intRun` with the assumption's
segmentation, and it is the state the tier-1 region starts from. -/
theorem numFastAccumulatorAgreement_of_assumed {calls : Calls} {epow : Int → Option EPow}
    {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n)
    {mem0 : Mem} {p : Nat} {e : State}
    (hpc : e.pc = "if.end230") (he : intRunExit mem0 bs p n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hdig : digitCount d ≤ 15) (hfr : d.fr = none) (hex : d.ex = none) :
    ∃ o : State, o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧ o.mem = e.mem ∧
      NumFastAccumulatorAgreement o.env d ∧
        ∀ k, runFuel calls (1 + k) numFastBody (stateAt e.env e) =
          runFuel calls k numFastBody o := by
  have hs := h.segmentation
  unfold NumFastScanSegmentation at hs
  obtain ⟨hhint, hshape⟩ := hs
  exact numFastAccumulatorAgreement_intRun (calls := calls) hpc he hi0 hbn hhint hshape
    hdig hfr hex

/-- **The agreement at the merge, for every decimal.**  `numFastGateAt` is built
from the model's five values, so the merge environment is the agreement by
definition: the merge half asks nothing of the scan. -/
theorem numFastAccumulatorAgreement_at_merge (env : Env) (d : Decimal) :
    NumFastAccumulatorAgreement (numFastGateAt env d (d.fr.getD ByteString.empty)) d :=
  numFastAccumulatorAgreement_merge env d

/-- **The agreement inside the tier-1 region.**  `numFastKernelAt` is
`t1MantEnv` over `numFastGateAt`, and the eight cells `t1MantEnv` binds are not
the agreement's five, so the merge's five cells survive into the region's
environment unchanged.  This is the environment `NumFastBodyArm`'s `if.then241`
arm hands to `if.end268`. -/
theorem numFastKernelAt_agreement (env : Env) (d : Decimal)
    (p10 : Nat) (ten : BitVec 64) :
    NumFastAccumulatorAgreement
      (numFastKernelAt env d (d.fr.getD ByteString.empty) p10 ten) d := by
  unfold NumFastAccumulatorAgreement
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [numFastKernelAt, numFastGateAt, NumFastTier1.t1MantEnv,
      NumFastTier1.t1GateEnv];
     block_lk)

/-! ### The body consumer

`JsonStage2NumFastArm.NumFastBodyArm` is the statement the release theorem's
number arm consumes.  Its `calls` parameter is the callee half's value, and its
conclusion is the conversion's answer at a staged entry state. -/

/-- **The arm is the callee half's consumer.**  An arm at any selection the
assumption answers is the arm at the tree's model: the two statements are the same
statement about the three out-of-line callees. -/
theorem numFastBodyArm_of_calleesAnswered {calls : Calls} {epow : Int → Option EPow}
    (h : NumFastCalleesAnswered calls epow) (harm : NumFastBodyArm calls) :
    NumFastBodyArm (stage2NumFastCalls epow) := by
  unfold NumFastCalleesAnswered at h
  rw [← h]
  exact harm

/-- **The arm's answer at the assumed selection.**  From the assumption and the
arm at its selection, the conversion runs to its return at a staged entry state:
it returns `1`, writes `strtodSpec`'s eight bytes at `%out`, leaves `%err` alone
and the cursor the caller's.  The run is stated at the model, which is the
selection the callee half names. -/
theorem numFastBodyArm_answer_of_assumed {calls : Calls} {epow : Int → Option EPow}
    {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n) (harm : NumFastBodyArm calls)
    (dd : Decimal) (lex : List UInt8) (env : Env) (mem : Mem) (next : Nat)
    (p out err : Nat)
    (hd : dd.wellFormed) (hl : ByteString.literal lex = dd.lexeme)
    (hp : lookupName env "%p" = some (.ptr p))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 lex.length)))
    (ho : lookupName env "%out" = some (.ptr out))
    (herr : lookupName env "%err" = some (.ptr err))
    (hr : readBytes mem p lex.length = some lex)
    (ht : NumFastTables env mem) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody
          (stateAt env { env := [], mem := mem, next := next, pc := "entry",
                         pre := none }) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes mem out (wordBytes 8 (strtodSpec dd).toBits) ∧
      o.next = next ∧
      UnchangedOutside mem o.mem [(out, 8), (err, 8)] := by
  have hc := h.callees
  unfold NumFastCalleesAnswered at hc
  rw [hc] at harm ⊢
  exact numFastBodyArm_at_entry (calls := stage2NumFastCalls epow) (h := harm)
    (d := dd) (lex := lex) (env := env) (mem := mem) (next := next) (p := p)
    (out := out) (err := err) hd hl hp hn ho herr hr ht

/-! ### Axiom footprints -/

#print axioms numFastCalleesAnswered_model
#print axioms numFast_ifEnd268_denote_of_assumed
#print axioms numFast_whileBodyPreheader_denote_of_assumed
#print axioms numFast_ifThen178_denote_of_assumed
#print axioms numFastAccumulatorAgreement_of_assumed
#print axioms numFastAccumulatorAgreement_at_merge
#print axioms numFastKernelAt_agreement
#print axioms numFastBodyArm_of_calleesAnswered
#print axioms numFastBodyArm_answer_of_assumed

end LeanLLVM.Refinement
