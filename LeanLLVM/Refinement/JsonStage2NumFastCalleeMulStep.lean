/-
`stk_mul_u64`'s group block, composed at the step level.

`JsonStage2NumFastCalleeMul` pins `for.body.i` and proves its four nine-instruction
limb steps, and records that composing them back into the block's thirty-six-cell
statement exceeds the elaboration budget in four formulations.  What every one of
them ended with is the same thing: a definitional check between the run's nested
environment and a nested builder, and it is that check the heartbeat budget
refuses.  Forming the denotation is not what is expensive; the split proves that.
*Naming* its endpoint is.

So this module never names it.  Each limb's denotation is restated in the form the
composition threads — an existential output environment, the cells the next limb
reads, the state its store leaves, and nothing else — so no declaration holds more
than one limb's cells.  The composition then chains the five statements with
`JsonEntrySteps.denoteCode_append`, the way that module's eight-group block does.
The block's `step` follows from the composed denotation and the branch bit, and
`step` is one control step whatever the denotation cost: `stkMulGrp_step_condbr_one`
is stated at an arbitrary `s'`, so the step itself never sees the nested state.

**Cost.**  Each limb wrapper re-derives only the cells it hands on: the carry out
and the next index at the head of its own builder, and the four pass-through cells
eight cons cells down.  The composition is five `rw`s and no cell resolution at
all; the endpoint is an existential variable, so the closing check is `rfl` between
two occurrences of the same state term.

**What moves where.**  The index arithmetic — each limb's address above the last
written word — is a hypothesis of the composition, not a proof inside it, because
the loop that supplies it also needs it.  The four reads are likewise of the
*original* memory; each limb wrapper carries its own read past the previous limb's
store with `stkLimbState_read_above`.

**What it costs, and what that measurement decided.**  The composition and the step
elaborate in seconds: the four limb wrappers, the composed denotation and the step
read one branch bit, in a module that `lake build`s in about six seconds, against
the eight-million-heartbeat ceiling (316-614 s) the four formulations
`JsonStage2NumFastCalleeMul` records reached.  The measurement that fixed the shape
is narrower: reducing a *bundled* state's field — a `def` whose field is the
four-write memory, or a `State.mk` with that memory as an argument — exceeds two
million heartbeats, while the same fields of a structure update `{ s with mem := … }`
close by `rfl` at once.  So nothing here bundles the memory: the composition's
endpoint is the update, and the step is stated at an arbitrary state the block
wrote.  Joining the two *at one concrete state* is what still costs more than four
million heartbeats at `whnf`, which is why the join is a consumer's `refine` rather
than a declaration here; the loop and the run above it are unproved.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMul

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### One limb's carry, and the cell tactic

The four-limb statement's cells nest their carries four deep.  `stkMulCarry` names
one level of that nesting, so a state can be threaded through the composition
without any declaration spelling the whole chain; `stkMulGrpMem` is the four
writes, and the closing normalisation turns the chain of four limb states into it. -/

/-- One limb step's carry out: the high half of `limb * multiplier + carry in`. -/
def stkMulCarry (x : BitVec 64) (mw cv : BitVec 128) : BitVec 128 :=
  (BitVec.ofNat 128 x.toNat * mw + cv) >>> 64

/-- Resolve a read against the limb builders: unfold the one the environment is
headed by, peel the cells above the target, and take the cell itself.  A read that
survives into the incoming environment is the hypothesis that names it. -/
macro "stkMul_cell" : tactic => `(tactic|
  (first
   | assumption
   | rfl
   | (simp only [stkMulLimb0Env, stkMulLimb1Env, stkMulLimb2Env, stkMulLimb3Env,
        stkMulTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | (rw [lookupName_cons_self]; rfl)
       | assumption
       | rfl)))

/-! ### The block's four pieces -/

/-- The block is its leading `phi` run, four limbs and the counter tail. -/
theorem stkMul_forBodyI_split :
    stkMulForBodyIInstrs =
      stkMulGroupPhisInstrs ++ (stkMulLimb0Instrs ++ (stkMulLimb1Instrs ++
        (stkMulLimb2Instrs ++ (stkMulLimb3Instrs ++ stkMulTailInstrs)))) := by
  simp only [stkMulForBodyIInstrs, stkMulGroupPhisInstrs, stkMulLimb0Instrs,
    stkMulLimb1Instrs, stkMulLimb2Instrs, stkMulLimb3Instrs, stkMulTailInstrs,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The iteration's memory: the four limb words, written where the four limb steps
write them.  Spelled as the writes rather than as four nested `stkMulLimbState`s,
so that the state's own block, predecessor and allocator cursor stay the incoming
ones *as themselves*, so a consumer of the step — the loop — reaches them by
reducing a literal rather than a bundled definition. -/
def stkMulGrpMem (mem : Mem) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x0 x1 x2 x3 : BitVec 64) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes mem (a + iv.toNat * (Ty.int 64).sizeBytes)
          (natToBytes (BitVec.ofNat 64
            ((BitVec.ofNat 128 x0.toNat * mw + cv).toNat % 2 ^ 64)).toNat 8))
        (a + (iv ||| 0x0000000000000001#64).toNat * (Ty.int 64).sizeBytes)
        (natToBytes (BitVec.ofNat 64
          ((BitVec.ofNat 128 x1.toNat * mw +
            stkMulCarry x0 mw cv).toNat % 2 ^ 64)).toNat 8))
      (a + (iv ||| 0x0000000000000002#64).toNat * (Ty.int 64).sizeBytes)
      (natToBytes (BitVec.ofNat 64
        ((BitVec.ofNat 128 x2.toNat * mw +
          stkMulCarry x1 mw (stkMulCarry x0 mw cv)).toNat % 2 ^ 64)).toNat 8))
    (a + (iv ||| 0x0000000000000003#64).toNat * (Ty.int 64).sizeBytes)
    (natToBytes (BitVec.ofNat 64
      ((BitVec.ofNat 128 x3.toNat * mw +
        stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))).toNat
          % 2 ^ 64)).toNat 8)

/-! ### The limbs, as the composition reads them

Each wrapper re-exposes the cells the next step consumes: the cells it computes,
plus the incoming ones it does not shadow.  The denotation's endpoint is an
existential environment, which is what keeps the composed statement one limb wide.
-/

/-- The first limb step: its carry, its index, and the cells it passes through. -/
theorem stkMulGrpLimb0_run {calls : Calls} {p : Env} {s : State}
    {a : Nat} {iv x niter unroll : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName p "%a" = some (.ptr a))
    (hiv : lookupName p "%indvars.iv.i" = some (.int 64 iv))
    (hcv : lookupName p "%carry.029.i" = some (.int 128 cv))
    (hmw : lookupName p "%conv3.i" = some (.int 128 mw))
    (hn : lookupName p "%niter" = some (.int 64 niter))
    (hu : lookupName p "%unroll_iter" = some (.int 64 unroll))
    (hpos : iv.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + iv.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    ∃ p', denoteCode calls stkMulLimb0Instrs (stateAt p s) =
        some (stateAt p' (stkMulLimbState s a iv cv mw x)) ∧
      lookupName p' "%a" = some (.ptr a) ∧
      lookupName p' "%conv3.i" = some (.int 128 mw) ∧
      lookupName p' "%indvars.iv.i" = some (.int 64 iv) ∧
      lookupName p' "%niter" = some (.int 64 niter) ∧
      lookupName p' "%unroll_iter" = some (.int 64 unroll) ∧
      lookupName p' "%indvars.iv.next.i" =
        some (.int 64 (iv ||| 0x0000000000000001#64)) ∧
      lookupName p' "%shr.i" = some (.int 128 (stkMulCarry x mw cv)) := by
  refine ⟨stkMulLimb0Env p a iv cv mw x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stkMul_limb0_denote ha hiv hcv hmw hpos hread
  all_goals stkMul_cell

/-- The second limb step, at the first one's index and carry. -/
theorem stkMulGrpLimb1_run {calls : Calls} {p : Env} {s : State}
    {a : Nat} {ivn ivb x niter unroll : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName p "%a" = some (.ptr a))
    (hivn : lookupName p "%indvars.iv.next.i" = some (.int 64 ivn))
    (hivb : lookupName p "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName p "%shr.i" = some (.int 128 cv))
    (hmw : lookupName p "%conv3.i" = some (.int 128 mw))
    (hn : lookupName p "%niter" = some (.int 64 niter))
    (hu : lookupName p "%unroll_iter" = some (.int 64 unroll))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    ∃ p', denoteCode calls stkMulLimb1Instrs (stateAt p s) =
        some (stateAt p' (stkMulLimbState s a ivn cv mw x)) ∧
      lookupName p' "%a" = some (.ptr a) ∧
      lookupName p' "%conv3.i" = some (.int 128 mw) ∧
      lookupName p' "%indvars.iv.i" = some (.int 64 ivb) ∧
      lookupName p' "%niter" = some (.int 64 niter) ∧
      lookupName p' "%unroll_iter" = some (.int 64 unroll) ∧
      lookupName p' "%indvars.iv.next.i.1" =
        some (.int 64 (ivb ||| 0x0000000000000002#64)) ∧
      lookupName p' "%shr.i.1" = some (.int 128 (stkMulCarry x mw cv)) := by
  refine ⟨stkMulLimb1Env p a ivn ivb cv mw x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stkMul_limb1_denote ha hivn hivb hcv hmw hpos hread
  all_goals stkMul_cell

/-- The third limb step. -/
theorem stkMulGrpLimb2_run {calls : Calls} {p : Env} {s : State}
    {a : Nat} {ivn ivb x niter unroll : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName p "%a" = some (.ptr a))
    (hivn : lookupName p "%indvars.iv.next.i.1" = some (.int 64 ivn))
    (hivb : lookupName p "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName p "%shr.i.1" = some (.int 128 cv))
    (hmw : lookupName p "%conv3.i" = some (.int 128 mw))
    (hn : lookupName p "%niter" = some (.int 64 niter))
    (hu : lookupName p "%unroll_iter" = some (.int 64 unroll))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    ∃ p', denoteCode calls stkMulLimb2Instrs (stateAt p s) =
        some (stateAt p' (stkMulLimbState s a ivn cv mw x)) ∧
      lookupName p' "%a" = some (.ptr a) ∧
      lookupName p' "%conv3.i" = some (.int 128 mw) ∧
      lookupName p' "%indvars.iv.i" = some (.int 64 ivb) ∧
      lookupName p' "%niter" = some (.int 64 niter) ∧
      lookupName p' "%unroll_iter" = some (.int 64 unroll) ∧
      lookupName p' "%indvars.iv.next.i.2" =
        some (.int 64 (ivb ||| 0x0000000000000003#64)) ∧
      lookupName p' "%shr.i.2" = some (.int 128 (stkMulCarry x mw cv)) := by
  refine ⟨stkMulLimb2Env p a ivn ivb cv mw x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stkMul_limb2_denote ha hivn hivb hcv hmw hpos hread
  all_goals stkMul_cell

/-- The fourth limb step: its index is the loop's `+ 4`, and its sum the join's
`%add4.i.3`. -/
theorem stkMulGrpLimb3_run {calls : Calls} {p : Env} {s : State}
    {a : Nat} {ivn ivb x : BitVec 64} {cv mw : BitVec 128} {niter unroll : BitVec 64}
    (ha : lookupName p "%a" = some (.ptr a))
    (hivn : lookupName p "%indvars.iv.next.i.2" = some (.int 64 ivn))
    (hivb : lookupName p "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName p "%shr.i.2" = some (.int 128 cv))
    (hmw : lookupName p "%conv3.i" = some (.int 128 mw))
    (hn : lookupName p "%niter" = some (.int 64 niter))
    (hu : lookupName p "%unroll_iter" = some (.int 64 unroll))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    ∃ p', denoteCode calls stkMulLimb3Instrs (stateAt p s) =
        some (stateAt p' (stkMulLimbState s a ivn cv mw x)) ∧
      lookupName p' "%a" = some (.ptr a) ∧
      lookupName p' "%conv3.i" = some (.int 128 mw) ∧
      lookupName p' "%niter" = some (.int 64 niter) ∧
      lookupName p' "%unroll_iter" = some (.int 64 unroll) ∧
      lookupName p' "%indvars.iv.next.i.3" =
        some (.int 64 (ivb + 0x0000000000000004#64)) ∧
      lookupName p' "%shr.i.3" = some (.int 128 (stkMulCarry x mw cv)) ∧
      lookupName p' "%add4.i.3" =
        some (.int 128 (BitVec.ofNat 128 x.toNat * mw + cv)) := by
  refine ⟨stkMulLimb3Env p a ivn ivb cv mw x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stkMul_limb3_denote ha hivn hivb hcv hmw hpos hread
  all_goals stkMul_cell

/-- The counter tail: the group count's step and the branch test. -/
theorem stkMulGrpTail_run {calls : Calls} {p : Env} {s : State}
    {a : Nat} {niter unroll iv3 : BitVec 64} {mw shr3 add43 : BitVec 128}
    (ha : lookupName p "%a" = some (.ptr a))
    (hmw : lookupName p "%conv3.i" = some (.int 128 mw))
    (hu : lookupName p "%unroll_iter" = some (.int 64 unroll))
    (hn : lookupName p "%niter" = some (.int 64 niter))
    (hiv3 : lookupName p "%indvars.iv.next.i.3" = some (.int 64 iv3))
    (hshr3 : lookupName p "%shr.i.3" = some (.int 128 shr3))
    (hadd43 : lookupName p "%add4.i.3" = some (.int 128 add43)) :
    ∃ p', denoteCode calls stkMulTailInstrs (stateAt p s) = some (stateAt p' s) ∧
      lookupName p' "%niter.ncmp.3" =
        some (.int 1 (evalICmp .eq (niter + 0x0000000000000004#64) unroll)) ∧
      lookupName p' "%niter.next.3" =
        some (.int 64 (niter + 0x0000000000000004#64)) ∧
      lookupName p' "%a" = some (.ptr a) ∧
      lookupName p' "%conv3.i" = some (.int 128 mw) ∧
      lookupName p' "%unroll_iter" = some (.int 64 unroll) ∧
      lookupName p' "%indvars.iv.next.i.3" = some (.int 64 iv3) ∧
      lookupName p' "%shr.i.3" = some (.int 128 shr3) ∧
      lookupName p' "%add4.i.3" = some (.int 128 add43) := by
  refine ⟨stkMulTailEnv p niter unroll, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stkMul_tail_denote hn hu
  all_goals stkMul_cell

/-! ### The block's denotation, five statements wide -/

/-- `for.body.i`'s denotation, composed: the four limb statements chained after the
leading `phi` run.  Nothing here names the nested environment, so the endpoint is
the composition's own existential variable and the closing check normalises one
state term into the other rather than deciding their equality. -/
theorem stkMulGrp_denote {calls : Calls} {env q : Env} {s : State}
    {a : Nat} {iv niter unroll : BitVec 64} {cv mw : BitVec 128}
    {x0 x1 x2 x3 : BitVec 64}
    (hphis : denoteCode calls stkMulGroupPhisInstrs (stateAt env s) =
      some (stateAt q s))
    (ha : lookupName q "%a" = some (.ptr a))
    (hmw : lookupName q "%conv3.i" = some (.int 128 mw))
    (hu : lookupName q "%unroll_iter" = some (.int 64 unroll))
    (hiv : lookupName q "%indvars.iv.i" = some (.int 64 iv))
    (hcv : lookupName q "%carry.029.i" = some (.int 128 cv))
    (hn : lookupName q "%niter" = some (.int 64 niter))
    (hpos0 : iv.toNat < 2 ^ 63)
    (hstep1 : iv.toNat + 1 ≤ (iv ||| 0x0000000000000001#64).toNat)
    (hpos1 : (iv ||| 0x0000000000000001#64).toNat < 2 ^ 63)
    (hstep2 : (iv ||| 0x0000000000000001#64).toNat + 1 ≤
      (iv ||| 0x0000000000000002#64).toNat)
    (hpos2 : (iv ||| 0x0000000000000002#64).toNat < 2 ^ 63)
    (hstep3 : (iv ||| 0x0000000000000002#64).toNat + 1 ≤
      (iv ||| 0x0000000000000003#64).toNat)
    (hpos3 : (iv ||| 0x0000000000000003#64).toNat < 2 ^ 63)
    (hread0 : readBytes s.mem (a + iv.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x0.toNat 8))
    (hread1 : readBytes s.mem
        (a + (iv ||| 0x0000000000000001#64).toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x1.toNat 8))
    (hread2 : readBytes s.mem
        (a + (iv ||| 0x0000000000000002#64).toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x2.toNat 8))
    (hread3 : readBytes s.mem
        (a + (iv ||| 0x0000000000000003#64).toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x3.toNat 8)) :
    ∃ q', denoteCode calls stkMulForBodyIInstrs (stateAt env s) =
        some (stateAt q' ({ s with mem := stkMulGrpMem s.mem a iv cv mw x0 x1 x2 x3 } : State)) ∧
      lookupName q' "%niter.ncmp.3" =
        some (.int 1 (evalICmp .eq (niter + 0x0000000000000004#64) unroll)) ∧
      lookupName q' "%niter.next.3" =
        some (.int 64 (niter + 0x0000000000000004#64)) ∧
      lookupName q' "%indvars.iv.next.i.3" =
        some (.int 64 (iv + 0x0000000000000004#64)) ∧
      lookupName q' "%shr.i.3" = some (.int 128
        (stkMulCarry x3 mw (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))))) ∧
      lookupName q' "%add4.i.3" = some (.int 128
        (BitVec.ofNat 128 x3.toNat * mw +
          stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)))) ∧
      lookupName q' "%a" = some (.ptr a) ∧
      lookupName q' "%conv3.i" = some (.int 128 mw) ∧
      lookupName q' "%unroll_iter" = some (.int 64 unroll) := by
  obtain ⟨p1, h1, h1a, h1mw, h1iv, h1n, h1u, h1ivn, h1shr⟩ :=
    stkMulGrpLimb0_run (p := q) (s := s) (a := a) (iv := iv) (x := x0)
      (cv := cv) (mw := mw) (niter := niter) (unroll := unroll)
      ha hiv hcv hmw hn hu hpos0 hread0
  obtain ⟨p2, h2, h2a, h2mw, h2iv, h2n, h2u, h2ivn, h2shr⟩ :=
    stkMulGrpLimb1_run (p := p1) (s := stkMulLimbState s a iv cv mw x0)
      (a := a) (ivn := iv ||| 0x0000000000000001#64) (ivb := iv) (x := x1)
      (cv := stkMulCarry x0 mw cv) (mw := mw) (niter := niter) (unroll := unroll)
      h1a h1ivn h1iv h1shr h1mw h1n h1u hpos1
      (by
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        exact hread1)
  obtain ⟨p3, h3, h3a, h3mw, h3iv, h3n, h3u, h3ivn, h3shr⟩ :=
    stkMulGrpLimb2_run (p := p2)
      (s := stkMulLimbState (stkMulLimbState s a iv cv mw x0)
        a (iv ||| 0x0000000000000001#64) (stkMulCarry x0 mw cv) mw x1)
      (a := a) (ivn := iv ||| 0x0000000000000002#64) (ivb := iv) (x := x2)
      (cv := stkMulCarry x1 mw (stkMulCarry x0 mw cv)) (mw := mw)
      (niter := niter) (unroll := unroll)
      h2a h2ivn h2iv h2shr h2mw h2n h2u hpos2
      (by
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        exact hread2)
  obtain ⟨p4, h4, h4a, h4mw, h4n, h4u, h4ivn, h4shr, h4add⟩ :=
    stkMulGrpLimb3_run (p := p3)
      (s := stkMulLimbState (stkMulLimbState (stkMulLimbState s a iv cv mw x0)
        a (iv ||| 0x0000000000000001#64) (stkMulCarry x0 mw cv) mw x1)
        a (iv ||| 0x0000000000000002#64)
        (stkMulCarry x1 mw (stkMulCarry x0 mw cv)) mw x2)
      (a := a) (ivn := iv ||| 0x0000000000000003#64) (ivb := iv) (x := x3)
      (cv := stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)))
      (mw := mw) (niter := niter) (unroll := unroll)
      h3a h3ivn h3iv h3shr h3mw h3n h3u hpos3
      (by
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        rw [stkLimbState_read_above _ _ _ _ _ _ 8
          (by rw [show (Ty.int 64).sizeBytes = 8 from rfl]; omega)]
        exact hread3)
  obtain ⟨p5, h5, h5nc, h5ni, h5a, h5mw, h5u, h5iv3, h5shr3, h5add3⟩ :=
    stkMulGrpTail_run (p := p4) (a := a) (niter := niter) (unroll := unroll)
      (iv3 := iv + 0x0000000000000004#64)
      (mw := mw) (shr3 := stkMulCarry x3 mw
        (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))))
      (add43 := BitVec.ofNat 128 x3.toNat * mw +
        stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)))
      h4a h4mw h4u h4n h4ivn h4shr h4add
  refine ⟨p5, ?_, h5nc, h5ni, h5iv3, h5shr3, h5add3, h5a, h5mw, h5u⟩
  rw [stkMul_forBodyI_split,
    LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append, hphis] <;>
    (first | rfl | decide | skip)
  simp only [Option.bind_some]
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append, h1] <;>
    (first | rfl | decide | skip)
  simp only [Option.bind_some]
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append, h2] <;>
    (first | rfl | decide | skip)
  simp only [Option.bind_some]
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append, h3] <;>
    (first | rfl | decide | skip)
  simp only [Option.bind_some]
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append, h4] <;>
    (first | rfl | decide | skip)
  simp only [Option.bind_some]
  rw [h5]
  simp only [stateAt, stkMulGrpMem, stkMulLimbState, stkMulCarry]

/-! ### The `phi` run at the loop's entry

The back-edge shape is `JsonStage2NumFastCalleeMul`'s `stkMul_groupPhis_denote`; at
the preheader the three cells are the literals the incoming names. -/

/-- The group iteration's leading run, entered from the widened count. -/
theorem stkMulGrp_phis_entry {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "for.body.lr.ph.i.new") :
    denoteCode calls stkMulGroupPhisInstrs (stateAt env s) =
      some (stateAt
        (("%niter", .int 64 0x0000000000000000#64) ::
          ("%carry.029.i", .int 128 0x00000000000000000000000000000000#128) ::
          ("%indvars.iv.i", .int 64 0x0000000000000000#64) :: env) s) := by
  unfold stkMulGroupPhisInstrs
  simp only [denoteCode]
  rw [denoteRun_phi_int (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new", .imm (.int 64 0x0000000000000000#64)),
        ("for.body.i", .reg "%indvars.iv.next.i.3")])
      (w := 64) (x := 0x0000000000000000#64) hpre (by decide)]
  rw [denoteRun_phi_int (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new",
          .imm (.int 128 0x00000000000000000000000000000000#128)),
        ("for.body.i", .reg "%shr.i.3")])
      (w := 128) (x := 0x00000000000000000000000000000000#128) hpre (by decide)]
  rw [denoteRun_phi_int (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new", .imm (.int 64 0x0000000000000000#64)),
        ("for.body.i", .reg "%niter.next.3")])
      (w := 64) (x := 0x0000000000000000#64) hpre (by decide)]
  rfl

/-! ### The block's step

One control step, at the branch's known bit.  The block's denotation is what says
where the step lands, and a consumer supplies it at the state its own invariant has
— usually an existential one.  The step is therefore stated at an *arbitrary* `s'`
the block wrote, and its destination is the `execTerm` normal form
`State.mk q' s'.mem s'.next t (some s'.pc)`: the block's own memory and cursor, the
branch's target, and the incoming block as the predecessor.  Nothing here names a
nested state, and nothing projects one: a consumer's own `s'` is a memory update,
whose cursor and predecessor are the fields it did not touch.

The branch's bit is read at the state `execTerm` reads it at, so the `simp` below
rewrites it as the branch's value without a definitional detour. -/

/-- A block ending in a `condbr` whose bit is one, at a state the block wrote. -/
theorem stkMulGrp_step_condbr_one {calls : Calls} {env q' : Env} {s s' : State}
    {instrs : List Instr} {block t f c : String} {x : BitVec 1}
    (hpc : s.pc = block)
    (hfind : stkMulBody.findBlock block =
      some ⟨block, instrs, Term.condbr (Operand.reg c) t f⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt q' s'))
    (hbit : evalOperand (stateAt q' s') (.reg c) = some (.int 1 x)) (hx : x = 1) :
    step calls stkMulBody (stateAt env s) =
      .jump (State.mk q' s'.mem s'.next t (some s'.pc)) := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } =
        some (stateAt q' s') := by
    rw [← hpc]
    exact hden
  have hlit : evalOperand (State.mk q' s'.mem s'.next s'.pc s'.pre) (.reg c) =
      some (.int 1 x) := hbit
  subst hx
  simp only [stateAt, step, hpc, hfind, hrec, execTerm, hlit, if_true]
  try rfl

/-- A block ending in a `condbr` whose bit is zero, at a state the block wrote. -/
theorem stkMulGrp_step_condbr_zero {calls : Calls} {env q' : Env} {s s' : State}
    {instrs : List Instr} {block t f c : String} {x : BitVec 1}
    (hpc : s.pc = block)
    (hfind : stkMulBody.findBlock block =
      some ⟨block, instrs, Term.condbr (Operand.reg c) t f⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt q' s'))
    (hbit : evalOperand (stateAt q' s') (.reg c) = some (.int 1 x)) (hx : x = 0) :
    step calls stkMulBody (stateAt env s) =
      .jump (State.mk q' s'.mem s'.next f (some s'.pc)) := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } =
        some (stateAt q' s') := by
    rw [← hpc]
    exact hden
  have hlit : evalOperand (State.mk q' s'.mem s'.next s'.pc s'.pre) (.reg c) =
      some (.int 1 x) := hbit
  subst hx
  simp only [stateAt, step, hpc, hfind, hrec, execTerm, hlit, if_true, if_false,
    if_neg (show ¬((0 : BitVec 1) = 1) from by decide)]
  try rfl

/-- The group iteration's step, taken: the count is exhausted, and the loop leaves
for its exit. -/
theorem stkMulGrp_step_taken {calls : Calls} {env q' : Env} {s s' : State}
    {niter unroll : BitVec 64}
    (hpc : s.pc = "for.body.i")
    (hden : denoteCode calls stkMulForBodyIInstrs (stateAt env s) = some (stateAt q' s'))
    (hnc : lookupName q' "%niter.ncmp.3" =
      some (.int 1 (evalICmp .eq (niter + 0x0000000000000004#64) unroll)))
    (hb : evalICmp .eq (niter + 0x0000000000000004#64) unroll =
      0x0000000000000001#1) :
    step calls stkMulBody (stateAt env s) =
      .jump (State.mk q' s'.mem s'.next
        "while.cond.preheader.i.unr-lcssa.loopexit" (some s'.pc)) := by
  refine stkMulGrp_step_condbr_one hpc stkMul_findBlock_for_body_i hden ?_ rfl
  refine evalOperand_reg_of q' s' "%niter.ncmp.3" (.int 1 (0x0000000000000001#1)) ?_
  rw [hb] at hnc
  exact hnc

/-- The group iteration's step, not taken: another group follows. -/
theorem stkMulGrp_step_loop {calls : Calls} {env q' : Env} {s s' : State}
    {niter unroll : BitVec 64}
    (hpc : s.pc = "for.body.i")
    (hden : denoteCode calls stkMulForBodyIInstrs (stateAt env s) = some (stateAt q' s'))
    (hnc : lookupName q' "%niter.ncmp.3" =
      some (.int 1 (evalICmp .eq (niter + 0x0000000000000004#64) unroll)))
    (hb : evalICmp .eq (niter + 0x0000000000000004#64) unroll =
      0x0000000000000000#1) :
    step calls stkMulBody (stateAt env s) =
      .jump (State.mk q' s'.mem s'.next "for.body.i" (some s'.pc)) := by
  refine stkMulGrp_step_condbr_zero hpc stkMul_findBlock_for_body_i hden ?_ rfl
  refine evalOperand_reg_of q' s' "%niter.ncmp.3" (.int 1 (0x0000000000000000#1)) ?_
  rw [hb] at hnc
  exact hnc

end LeanLLVM.Refinement
