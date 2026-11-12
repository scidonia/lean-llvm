/-
The stage-2 walk's seed run: `entry`, the preheader, and the header's first pass
as control steps.

`walkEntry_denote` (`JsonStage2WalkRun`) states the entry block's fifty-seven
instructions as one `denoteCode` equality.  This module turns that equality and
the two blocks after it into the steps that reach `NodeBlock21`, which is where
`WalkSeedState` (`JsonStage2WalkScope`) is asserted:

* `walkEntry_step` — the entry block's step, in both arms of its own test: the
  terminator is `condbr %cmp.i247.not, if.then492.i, while.body.i.lr.ph`, and the
  test bit is `%nep == 0`, so the zero arm jumps to `if.then492.i` and the
  non-zero arm to the preheader.  The statement is a single `if` on `nep`, so one
  theorem carries both.
* `walkPreheader_denote` — `while.body.i.lr.ph`'s five literal-offset
  `getelementptr`s, at a state's own environment, and `walkPreheader_step` — the
  unconditional edge into `while.body.i`.
* `whileBodyFirst_denote` — `while.body.i`'s leading `phi` run selecting the
  preheader's arm (`%k.0.i249 = 0`, `%sp.i.0248 = 0`), then the lane and document
  loads and the cursor store, and `walkHeader_step` — the edge into
  `NodeBlock21`.

Each step is stated at a `denoteCode` equality the caller supplies, so the run
composes with the block equalities the rest of the tree proves.  `runFuel` forms
(`walkEntry_runFuel`, `walkPreheader_runFuel`, `walkHeader_runFuel`) shift one
fuel unit per step, which is the shape a prefix is composed in.

What remains for `WalkSeedState`'s production is the state's *content* at
`NodeBlock21`: the register clauses are lookups in the environment this module
leaves (`whileBodyOut` over the preheader's and the entry's cells), and the
memory clauses are reads through the entry run's named folds.  That assembly is
the open row; the steps and the equalities it reads are here.
-/
import LeanLLVM.Refinement.JsonStage2WalkRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### The entry block's step -/

/-- The entry block's branch target, at the state its run leaves: `if.then492.i`
when the entry count is zero and the preheader otherwise. -/
def walkEntryJump (s : State) (nep : Nat) : State :=
  { s with
    pc := if nep = 0 then "if.then492.i" else "while.body.i.lr.ph"
    pre := some "entry" }

/-- `BitVec.ofNat 64` is zero exactly when the `Nat` is. -/
theorem walkOfNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have htoNat : (BitVec.ofNat 64 n).toNat = n := walkToNat_ofNat64 hn
    rw [h] at htoNat
    simpa using htoNat.symm
  · intro h
    subst h
    rfl

/-- **The entry block's step**, in both arms of its own test.  `%cmp.i247.not`
is `%nep == 0` (`walkEntryEnv4`), and the terminator branches on it: the zero arm
jumps to the flush arm, the non-zero arm to the preheader. -/
theorem walkEntry_step (s : State) (hpc : s.pc = "entry") {s₁ : State} {nep : Nat}
    (hden : denoteCode (stage2Calls stage2SubCalls) walkEntryInstrs s = some s₁)
    (hne : lookupName s₁.env "%cmp.i247.not" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))))
    (hne64 : nep < 2 ^ 64) (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (walkEntryJump s₁ nep) := by
  have hfind : stage2Body.findBlock s.pc = some walkEntryBlock := by
    rw [hpc]; exact walkEntryBlock_find
  simp only [LeanLLVM.step, hfind, walkEntryBlock, hden]
  dsimp only [execTerm]
  rw [show evalOperand s₁ (Operand.reg "%cmp.i247.not") =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))) by
    simp [evalOperand, hne]]
  by_cases h0 : nep = 0
  · have hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) = 1 :=
      (evalICmp_eq_one_iff _ _).2 (by simpa using (walkOfNat64_eq_zero hne64).2 h0)
    rw [hbit]
    simp [walkEntryJump, h0, hpc, hpc₁]
  · have hnz : (BitVec.ofNat 64 nep) ≠ (0 : BitVec 64) :=
      fun h => h0 ((walkOfNat64_eq_zero hne64).1 h)
    have hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) = 0 :=
      (evalICmp_eq_zero_iff _ _).2 (by simpa using hnz)
    rw [hbit]
    simp [walkEntryJump, h0, hpc, hpc₁]

/-- **The entry block's one-step prefix.** -/
theorem walkEntry_runFuel (s : State) (hpc : s.pc = "entry") {s₁ : State} {nep : Nat}
    (hden : denoteCode (stage2Calls stage2SubCalls) walkEntryInstrs s = some s₁)
    (hne : lookupName s₁.env "%cmp.i247.not" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))))
    (hne64 : nep < 2 ^ 64) (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body (walkEntryJump s₁ nep) := by
  have hs := walkEntry_step s hpc hden hne hne64 hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### The preheader -/

/-- **`while.body.i.lr.ph`'s run** at a state's own environment: five
literal-offset `getelementptr`s, `%k11.i` first (`%c.i + 32`). -/
theorem walkPreheader_denote {calls : Calls} (s : State)
    {c z tok : Nat}
    (hc : lookupName s.env "%c.i" = some (.ptr c))
    (hz : lookupName s.env "%z" = some (.ptr z))
    (ht : lookupName s.env "%t352.i" = some (.ptr tok)) :
    denoteCode calls walkPreheaderInstrs s =
      some (s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
        |>.bind "%gap.i" (.ptr (tok + 20)) |>.bind "%end.i" (.ptr (tok + 8))
        |>.bind "%kind404.i" (.ptr (tok + 16))) := by
  simp only [walkPreheaderInstrs]
  rw [walkDenoteCode_gep8_imm (calls := calls) (s := s) (d := "%k11.i") (base := "%c.i")
    (a := c) (c := 32) hc (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32))) (d := "%h1.i.i.i51") (base := "%z")
    (a := z) (c := 24)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact hz)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24)))
    (d := "%gap.i") (base := "%t352.i") (a := tok) (c := 20)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
      |>.bind "%gap.i" (.ptr (tok + 20)))
    (d := "%end.i") (base := "%t352.i") (a := tok) (c := 8)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
      |>.bind "%gap.i" (.ptr (tok + 20)) |>.bind "%end.i" (.ptr (tok + 8)))
    (d := "%kind404.i") (base := "%t352.i") (a := tok) (c := 16)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rfl

/-- **The preheader's step**: the unconditional edge into `while.body.i`. -/
theorem walkPreheader_step {s s₁ : State}
    (hpc : s.pc = "while.body.i.lr.ph")
    (hden : denoteCode (stage2Calls stage2SubCalls) walkPreheaderInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s =
      .jump { s₁ with pc := "while.body.i", pre := some "while.body.i.lr.ph" } := by
  have hfind : stage2Body.findBlock s.pc = some walkPreheaderBlock := by
    rw [hpc]; exact walkPreheaderBlock_find
  simp only [LeanLLVM.step, hfind, walkPreheaderBlock, hden]
  simp only [execTerm, hpc, hpc₁]

/-- **The preheader's one-step prefix.** -/
theorem walkPreheader_runFuel {s s₁ : State}
    (hpc : s.pc = "while.body.i.lr.ph")
    (hden : denoteCode (stage2Calls stage2SubCalls) walkPreheaderInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body
        { s₁ with pc := "while.body.i", pre := some "while.body.i.lr.ph" } := by
  have hs := walkPreheader_step hpc hden hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### The header's first pass -/

/-- **`while.body.i`'s first pass**: both `phi`s take the preheader's arm, so the
index and the depth are zero; then the block count into `%inc.i`, the lane at the
first entry position, the document byte that lane selects, and the cursor store.
The header's latch-entered run is `whileBody_denote` (`JsonStage2WalkScope`); the
difference is exactly the `phi` selection, which is why this is the first pass and
not a special case of that theorem's hypotheses. -/
theorem whileBodyFirst_denote {calls : Calls} (env : Env) (s : State)
    {ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (h5 : lookupName env "%5" = some (.ptr ep))
    (h3 : lookupName env "%3" = some (.ptr b))
    (hK : lookupName env "%k11.i" = some (.ptr (c + 32)))
    (hpre : s.pre = some "while.body.i.lr.ph")
    (hread : readBytes s.mem ep 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) :
    denoteCode calls whileBodyInstrs (stateAt env s) =
      some (stateAt (whileBodyOut env 0 0 b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 1) }) := by
  simp only [whileBodyInstrs, whileBodyOut]
  walk_eval

/-- **The header's first-pass step**: the edge into `NodeBlock21`. -/
theorem walkHeader_step {s s₁ : State}
    (hpc : s.pc = "while.body.i")
    (hden : denoteCode (stage2Calls stage2SubCalls) whileBodyInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s =
      .jump { s₁ with pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hfind : stage2Body.findBlock s.pc = some whileBodyBlock := by
    rw [hpc]; exact whileBody_find
  simp only [LeanLLVM.step, hfind, whileBodyBlock, hden]
  simp only [execTerm, hpc, hpc₁]

/-- **The header's first-pass one-step prefix.** -/
theorem walkHeader_runFuel {s s₁ : State}
    (hpc : s.pc = "while.body.i")
    (hden : denoteCode (stage2Calls stage2SubCalls) whileBodyInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body
        { s₁ with pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hs := walkHeader_step hpc hden hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntry_step

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntry_runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntry_runFuel

/-- info: 'LeanLLVM.Refinement.WalkScope.walkPreheader_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkPreheader_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkPreheader_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkPreheader_step

/-- info: 'LeanLLVM.Refinement.WalkScope.whileBodyFirst_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.whileBodyFirst_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkHeader_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkHeader_step

end WalkScope
end LeanLLVM.Refinement
