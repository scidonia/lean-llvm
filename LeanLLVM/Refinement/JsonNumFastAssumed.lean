/-
The release theorem's number-conversion assumption, stated as named values beside
its compiler and ABI steps.

`JsonNumberPremises` proved what the tree's definitions allow at the walk's number
arm and named the two obstructions: the scanner's token extent (Premise 1, the
`NumberTokenExtentAt` lane) and the emitted accumulators' agreement with the
reader's decimal (Premise 2, this lane).  The release theorem does not discharge
either; it carries them.  This module states the second as named structures,
`JsonNumFastAssumed` and its one remaining shape's sibling `JsonNumFastSegAssumed`,
so the assumption list cites one value per number token instead of prose, and
proves that the value is exactly what the body arm consumes.
`JsonNumberSegmentation` proves the reader's own cut of the lexeme at the token's
end and at either run's stop inside it, so the segmentation is nowhere a field;
`JsonNumFastSegAssumed` remains as the name of the one shape whose run stops
inside the token, a fraction an exponent follows.

## The assumption

The assumption is the callee half.  `JsonNumFastAssumed calls epow bs d i0 d0 n`
states it for the shapes whose run reaches the token's end and has one field;
`JsonNumFastSegAssumed` names the remaining shape by its reader facts beside the
callee half, and has no segmentation field either.

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

**The segmentation half — proved, for all four shapes.**  `JsonNumberSegmentation`
proves the reader's cut of the lexeme in the seams' shape: `intRun_of_reader` at
the integer run reaching the token's end (`t1_intRun_tie`'s `hint`/`hshape`),
`intHead_of_reader` at an in-lexeme stop (`t1_headTie`'s), `fracRun_of_reader` at
the fraction run reaching the token's end (`t1_fracRun_tie`'s/
`t1_fracCount_tie`'s `hintF`/`hshape`), and `fracHead_of_reader` at the fraction
run's stop inside the token — the same `hintF`/`hshape` at its stop `i1`, the
exponent marker's index.  The assumption therefore carries no segmentation:
`numFastScanSegmentation_of_reader`, `numFastFracSegmentation_of_reader` and
`numFastFracHeadSegmentation_of_reader` state the three conjunctions as theorems,
and the consumers take them where a seam needs the hypotheses.  The eight-digit
fast path is not a segmentation shape: it is `num_d8_el1`, one of the callee
half's three.  Tier 3's `to_double` window is the region after the merge and lies
outside both values.

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
* `numFastAccumulatorAgreement_of_assumed` — `numFastScanSegmentation_of_reader`'s
  proved segmentation, which is `JsonNumberSegmentation.intRun_of_reader` at the
  scan's counters, plus the run's end-of-lexeme exit gives
  `NumFastAccumulatorAgreement` at the run's successor, by
  `JsonNumberPremises.numFastAccumulatorAgreement_intRun`; the assumption is cited
  only for its callee half, which makes `calls` the model's selection;
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
* **The segmentation half, proved.**  `JsonNumberSegmentation` derives all four
  cuts from `StrtodReader.reader`: the integer run at the token's end
  (`intRun_of_reader`) and at its interior stop (`intHead_of_reader`), and the
  fraction run at the token's end (`fracRun_of_reader`) and at its stop inside it
  (`fracHead_of_reader`, the fraction analog of the integer head wrapper).  What
  remains for the `fracExp` shape is the seam, not a reader fact: a head-form
  fraction tie that reads `hintF`/`hshape` at the stop `i1` and carries the run's
  cells into the exponent route, beside `t1_headTie`'s role for the integer run.
  The eight-digit fast path (`num_d8_el1`, `JsonStage2NumFastScanFast.lean`) is
  one of the three callees and belongs to the callee half above.
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
selection is that model.  It is not a refinement of the three callees: no
refinement of the emitted `num_d8_el1`, `num_el_el1` or `stk_mul_u64` body against
its model is proved — the bodies are pinned as ASTs
(`JsonStage2NumFastCalleeD8.numD8Body`, `JsonStage2NumFastCalleeEl.numElBody`),
and what remains is the run of each against its model at the `Calls` entry, which
is exactly the gap the discharge path names.  It is not the token-extent premise:
`JsonNumberPremises.NumberTokenExtentAt` is the other half, and holds the span's
bytes; these values take those bytes (`bs`) as given, and no field of either
structure splits them into parts.  And it does not
weaken or restate any existing definition or theorem:
`NumFastBodyArm`, `numFastAccumulatorAgreement_intRun`, `t1_intRun_tie` and the
site denotations keep their statements, and this module only names what they
consume.

It adds no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonNumberPremises
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.JsonNumberSegmentation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open ByteString

/-! ### The assumption's parts

The callee half is the selection.  The segmentation is a theorem for every shape:
the reader's own cut reaches the integer run, the fraction run that ends the
token, and the fraction run that an exponent stops inside. -/

/-- **The callee half.**  The conversion's `Calls` selection is the tree's model
of the three out-of-line functions: `numFastCalls` answers `num_d8_el1`,
`num_el_el1` and `stk_mul_u64` from the measured C text and delegates the rest to
the walk's helpers.  The content that the compiled bodies behave as that text is
the trust statement, not an equality this module proves. -/
def NumFastCalleesAnswered (calls : Calls) (epow : Int → Option EPow) : Prop :=
  calls = stage2NumFastCalls epow

/-- **The integer run's segmentation at the lexeme's end.**  The emitted scan's
integer run, at its own start `i0`, accumulator count `d0` and lexeme length `n`,
consumes exactly the decimal's integer-part digits: the count is `intDigits d`,
and `d.ip` is the lexeme's slice from where the part begins.  These are
`t1_intRun_tie`'s `hint` and `hshape`; `numFastScanSegmentation_of_reader` proves
them from the reader's cut. -/
def NumFastScanSegmentation (bs : List UInt8) (d : Decimal) (i0 d0 n : Nat) : Prop :=
  intDigits d = d0 + (n - i0) ∧
    d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0))

/-- **The fraction run's segmentation at the lexeme's end.**  The fraction's
digits, at the run's start `i0`, count `d0` and lexeme length `n`, are the slice
one byte past the integer part and the `.`; these are
`t1_fracRun_tie`'s/`t1_fracCount_tie`'s `hintF` and `hshape`, and
`numFastFracSegmentation_of_reader` proves them from the reader's cut. -/
def NumFastFracSegmentation (bs : List UInt8) (fs : Bytes) (d : Decimal)
    (i0 d0 n : Nat) : Prop :=
  fracDigits d = d0 + (n - i0) ∧
    fs.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0))

/-- **The fraction run's segmentation at an interior stop.**  When an exponent
follows the fraction's run, the run stops at `i1`, inside the token, so the
end-form `NumFastFracSegmentation` does not apply: the count and bytes are the
slice up to `i1`.  `fracHead_of_reader` derives it from the reader's cut at the
head indices, where the end form uses the token's length. -/
def NumFastFracHeadSegmentation (bs : List UInt8) (fs : Bytes) (d : Decimal)
    (i0 d0 i1 : Nat) : Prop :=
  fracDigits d = d0 + (i1 - i0) ∧
    fs.data.toList = (bs.drop (i0 - d0)).take (d0 + (i1 - i0))

/-- **The release theorem's number-conversion assumption, for the shapes the
reader's own cut reaches.**  One value per number token, cited beside the compiler
and ABI steps: the conversion's three out-of-line callees are the tree's model of
their measured C text.  The emitted scan's segmentation is not a field here —
`JsonNumberSegmentation` proves it from `StrtodReader.reader` at the integer run's
end (`intRun_of_reader`), at an in-lexeme integer stop (`intHead_of_reader`), at
the fraction run's end (`fracRun_of_reader`) and at a fraction run that an
exponent stops inside the token (`fracHead_of_reader`), and the consumers below
take those theorems where a seam needs `hint`/`hshape`/`hintF`.  The token-extent
premise is the other lane (`JsonNumberPremises.NumberTokenExtentAt`) and is not
repeated here. -/
structure JsonNumFastAssumed (calls : Calls) (epow : Int → Option EPow)
    (bs : List UInt8) (d : Decimal) (i0 d0 n : Nat) : Prop where
  /-- The selection is the model of the three out-of-line callees. -/
  callees : NumFastCalleesAnswered calls epow

/-- **The one shape whose run stops inside the token: a fraction followed by an
exponent.**  The fraction run stops at the exponent marker, so the end-form
`fracRun_of_reader` does not apply and the run's slicing at its stop `i1` is
`numFastFracHeadSegmentation_of_reader`'s, not a field.  The structure names the
shape by its reader facts beside the callee half; its parameters are the token's
counters and the run's stop, as in `JsonNumFastAssumed`.  The eight-digit fast path
is not here: it is `num_d8_el1`, one of the callee half's three.  Tier 3's
`to_double` window is the region after the merge and is outside both values. -/
structure JsonNumFastSegAssumed (calls : Calls) (epow : Int → Option EPow)
    (bs : List UInt8) (d : Decimal) (fs : Bytes) (i0 d0 i1 : Nat) : Prop where
  /-- The selection is the model of the three out-of-line callees. -/
  callees : NumFastCalleesAnswered calls epow
  /-- The lexeme has a fraction, whose run is the one the theorem slices. -/
  fraction : d.fr = some fs
  /-- The lexeme has an exponent, which is why the run stops before the end. -/
  exponent : d.ex ≠ none

/-- **The callee half is inhabited by the tree's model.**  The selection the tree
already supplies answers the three symbols by construction; what the assumption
adds is that the compiled bodies agree with that model. -/
theorem numFastCalleesAnswered_model (epow : Int → Option EPow) :
    NumFastCalleesAnswered (stage2NumFastCalls epow) epow := rfl

/-! ### The covered shapes' segmentation, proved

The two end-form cuts the seams take, instantiated at this module's counters from
`JsonNumberSegmentation`.  Neither is a field of `JsonNumFastAssumed`: a consumer
holding the reader's cut cites the theorem where the seam needs `hint`/`hshape`. -/

/-- **The integer run's segmentation, from the reader's own cut.**  This is
`JsonNumberSegmentation.intRun_of_reader` at `i0 = negIndex b + 1`, `d0 = 1` and
`n = bs.length`, in the shape `t1_intRun_tie` consumes. -/
theorem numFastScanSegmentation_of_reader {lex : Bytes} {d : Decimal}
    {bs : List UInt8} {b : UInt8} {rest : Bytes} {i0 d0 n : Nat}
    (hread : StrtodReader.reader lex = some d) (hlex : lex = b +: rest)
    (hbs : bs = lex.data.toList)
    (hfr : d.fr = none) (hex : d.ex = none)
    (hi0 : i0 = NumFastStarts.negIndex b + 1) (hd0 : d0 = 1) (hn : n = bs.length) :
    NumFastScanSegmentation bs d i0 d0 n :=
  intRun_of_reader hread hlex hbs hfr hex hi0 hd0 hn

/-- **The fraction run's segmentation, from the reader's own cut.**  This is
`JsonNumberSegmentation.fracRun_of_reader` at `i0 = signLen + intDigits d + 1`,
`d0 = 0` and `n = bs.length`, in the shape `t1_fracRun_tie`/`t1_fracCount_tie`
consume: a fraction whose run reaches the lexeme's end, so no exponent. -/
theorem numFastFracSegmentation_of_reader {lex : Bytes} {d : Decimal}
    {bs : List UInt8} {fs : Bytes} {i0 d0 n : Nat}
    (hread : StrtodReader.reader lex = some d) (hfr : d.fr = some fs)
    (hex : d.ex = none) (hbs : bs = lex.data.toList)
    (hi0 : i0 = (Decimal.signBytes d.neg).length + intDigits d + 1)
    (hd0 : d0 = 0) (hn : n = bs.length) :
    NumFastFracSegmentation bs fs d i0 d0 n :=
  fracRun_of_reader hread hfr hex hbs hi0 hd0 hn

/-- **The fraction run's segmentation at its stop inside the token, from the
reader's own cut.**  This is `JsonNumberSegmentation.fracHead_of_reader` at
`i0 = signLen + intDigits d + 1`, `d0 = 0` and `i1` the exponent marker's index
`signLen + intDigits d + 1 + fracDigits d`, in the shape a fraction run's head
seam takes: `hintF`/`hshape` at `i1`.  The end form above used the token's length,
which an exponent makes longer than the run; here the stop is the run's own. -/
theorem numFastFracHeadSegmentation_of_reader {lex : Bytes} {d : Decimal}
    {bs : List UInt8} {fs : Bytes} {i0 d0 i1 : Nat}
    (hread : StrtodReader.reader lex = some d) (hfr : d.fr = some fs)
    (hbs : bs = lex.data.toList)
    (hi0 : i0 = (Decimal.signBytes d.neg).length + intDigits d + 1)
    (hd0 : d0 = 0)
    (hi1 : i1 = (Decimal.signBytes d.neg).length + intDigits d + 1 + fracDigits d) :
    NumFastFracHeadSegmentation bs fs d i0 d0 i1 :=
  fracHead_of_reader hread hfr hbs hi0 hd0 hi1

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

/-! ### The segmentation at the merge

The run's end-of-lexeme exit plus the reader's own cut is the agreement at its
successor; the merge environment is the agreement unconditionally; and the
tier-1 region's environment extends it.  This is the chain `NumFastBodyArm` reads
at `if.end230` and `if.then241`. -/

/-- **The agreement at the run's successor, from the reader's own cut.**  At the
integer run's end-of-lexeme exit `if.end230`, the tie's `hint` and `hshape` are
`numFastScanSegmentation_of_reader`'s conclusion at the scan's counters, so the
successor's five merge registers are the reader's decimal fields.  This is
`numFastAccumulatorAgreement_intRun` with the segmentation proved; the assumption
is cited only for its callee half, which makes `calls` the model's selection. -/
theorem numFastAccumulatorAgreement_of_assumed {calls : Calls} {epow : Int → Option EPow}
    {bs : List UInt8} {d : Decimal} {i0 d0 n : Nat}
    (h : JsonNumFastAssumed calls epow bs d i0 d0 n)
    {lex : Bytes} {b : UInt8} {rest : Bytes}
    (hread : StrtodReader.reader lex = some d) (hlex : lex = b +: rest)
    (hbs : bs = lex.data.toList)
    (hi0c : i0 = NumFastStarts.negIndex b + 1) (hd0c : d0 = 1) (hnc : n = bs.length)
    {mem0 : Mem} {p : Nat} {e : State}
    (hpc : e.pc = "if.end230") (he : intRunExit mem0 bs p n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hdig : digitCount d ≤ 15) (hfr : d.fr = none) (hex : d.ex = none) :
    ∃ o : State, o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧ o.mem = e.mem ∧
      NumFastAccumulatorAgreement o.env d ∧
        ∀ k, runFuel calls (1 + k) numFastBody (stateAt e.env e) =
          runFuel calls k numFastBody o := by
  obtain ⟨hhint, hshape⟩ :=
    numFastScanSegmentation_of_reader hread hlex hbs hfr hex hi0c hd0c hnc
  have hc := h.callees
  unfold NumFastCalleesAnswered at hc
  rw [hc]
  exact numFastAccumulatorAgreement_intRun (calls := stage2NumFastCalls epow) hpc he hi0
    hbn hhint hshape hdig hfr hex

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
#print axioms numFastScanSegmentation_of_reader
#print axioms numFastFracSegmentation_of_reader
#print axioms numFastFracHeadSegmentation_of_reader
#print axioms numFast_ifEnd268_denote_of_assumed
#print axioms numFast_whileBodyPreheader_denote_of_assumed
#print axioms numFast_ifThen178_denote_of_assumed
#print axioms numFastAccumulatorAgreement_of_assumed
#print axioms numFastAccumulatorAgreement_at_merge
#print axioms numFastKernelAt_agreement
#print axioms numFastBodyArm_of_calleesAnswered
#print axioms numFastBodyArm_answer_of_assumed

end LeanLLVM.Refinement
