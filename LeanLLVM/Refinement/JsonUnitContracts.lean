/-
The memory-aware contracts of the proved JSON stage-1 units, and the call-level
form the bridge gives each of them.

Three units are proved here as `Satisfies` instances: the mask unit
(`masks_satisfies`), the two entry emitters (`entry_pos8_satisfies`,
`entry_b8_satisfies`) and the UTF-8 stage (`utf8_satisfies`).  Each record is
read at the caller's memory and allocator, and each wrapper turns the unit's
own headline theorem into the record's guarantee.  The next-independence
lemmas are the bridge between the headline theorems (stated at the entry
state's allocator base) and `Satisfies`, which quantifies the allocator freely;
they rest on the fact that none of the bodies allocates, and that each unit's
call environment answers with the allocator it was handed.

The controls that make the records non-vacuous — concrete staged states, `post`
not implied by `pre`, the `ub` refusal, the value-irrelevance refusal, the
call-site control and the composition site — are collected under "The controls",
and each claim's axiom footprint is pinned at the end of this module and again in
`LeanLLVMTest/Refinement.lean`.  Nothing here assembles the records into a
whole-program call environment: that needs the escape and stage-2 bodies, which
this module does not have.
-/
import LeanLLVM.Refinement.JsonS1MasksSteps
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonB8Steps
import LeanLLVM.Refinement.JsonUtf8Steps
import LeanLLVM.Refinement.Relation

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonB8Steps
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.JSON

/-! ### Allocator irrelevance

`Satisfies` quantifies the state's allocator base, while each unit's headline
theorem is stated at `initState`'s base.  The bodies execute no `alloca`, and
their call environments answer the same values and memory at either base, so
the run's outcome is independent of it.  The lemmas below are the congruence
at the instruction, code, step and run levels; `SameApartFromNext` is the
relation two such states satisfy.
-/

def SameApartFromNext (s t : State) : Prop :=
  s.env = t.env ∧ s.mem = t.mem ∧ s.pc = t.pc ∧ s.pre = t.pre

def OptStateRel : Option State → Option State → Prop
  | some s, some t => SameApartFromNext s t
  | none, none => True
  | _, _ => False

def CtrlSameApartFromNext : Ctrl → Ctrl → Prop
  | .ub, .ub => True
  | .ret v s, .ret w t => v = w ∧ SameApartFromNext s t
  | .jump s, .jump t => SameApartFromNext s t
  | _, _ => False

attribute [local simp] OptStateRel SameApartFromNext State.bind

theorem OptStateRel_none {r : Option State} : OptStateRel none r ↔ r = none := by
  cases r with
  | none => simp [OptStateRel]
  | some t => simp [OptStateRel]

theorem OptStateRel_some {s : State} {r : Option State} :
    OptStateRel (some s) r ↔ ∃ t, r = some t ∧ SameApartFromNext s t := by
  cases r with
  | none => simp [OptStateRel]
  | some t => simp [OptStateRel]

def HasAlloca : Instr → Bool
  | .alloca .. => true
  | _ => false

def allocaFree (f : Function) : Bool :=
  f.blocks.all fun b => b.instrs.all fun i => !HasAlloca i

def CallsNextIrr (calls : Calls) : Prop :=
  ∀ sym args mem n1 n2,
    (calls sym args mem n1).map (fun r => (r.ret, r.mem)) =
    (calls sym args mem n2).map (fun r => (r.ret, r.mem))

theorem evalOperand_env_eq {s t : State} (h : s.env = t.env) (o : Operand) :
    evalOperand s o = evalOperand t o := by
  cases o <;> simp [evalOperand, h]

theorem evalOperands_env_eq {s t : State} (h : s.env = t.env)
    (args : List (Ty × Operand)) :
    evalOperands s args = evalOperands t args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨ty, op⟩ := a
      simp only [evalOperands, evalOperand_env_eq h, ih]

-- The congruence proofs below case-split the operand and instruction shapes and
-- discharge every branch with one `all_goals (simp [...])`, so on any single
-- branch part of the shared simp set is unused.  The linter cannot see across the
-- branches; the same idiom is silenced in `DepthCountRefine.lean`.
set_option linter.unusedSimpArgs false in
theorem storeValue_next {s t : State} (h : SameApartFromNext s t)
    (ty : Ty) (v : Value) (addr : Nat) :
    OptStateRel (storeValue s ty v addr) (storeValue t ty v addr) := by
  obtain ⟨henv, hmem, hpc, hpre⟩ := h
  cases ty with
  | vec n elem =>
      cases elem <;> cases v <;> simp only [storeValue]
      all_goals (repeat' split)
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | _ =>
      cases v <;> simp only [storeValue]
      all_goals (repeat' split)
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])

set_option linter.unusedSimpArgs false in
theorem evalInstr_next_irr {calls : Calls} (hcalls : CallsNextIrr calls)
    {s t : State} (h : SameApartFromNext s t) (i : Instr)
    (hi : HasAlloca i = false) :
    OptStateRel (evalInstr calls s i) (evalInstr calls t i) := by
  obtain ⟨henv, hmem, hpc, hpre⟩ := h
  cases i with
  | phi d ty inc =>
      cases htp : t.pre with
      | none =>
          have hsn : s.pre = none := hpre.trans htp
          simp [evalInstr, hsn, htp, OptStateRel]
      | some p =>
          cases hinc : phiIncoming p inc with
          | none => simp [evalInstr, htp, hinc, hpre]
          | some op =>
              simp only [evalInstr, htp, hinc, hpre]
              rw [evalOperand_env_eq henv op]
              cases evalOperand t op <;>
                simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
  | binop d op w a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | icmp d pred w a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | icmpPtr d pred a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      cases evalOperand t a with
      | none => simp [OptStateRel]
      | some va =>
        cases evalOperand t b with
        | none => simp [OptStateRel]
        | some vb =>
          cases va with
          | int w x =>
              cases vb <;> simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
          | vec n w l =>
              cases vb <;> simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
          | ptr x =>
              cases vb with
              | int w y => simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
              | vec n w l => simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
              | ptr y =>
                  cases hic : evalICmpPtr pred x y with
                  | none => simp [hic, OptStateRel]
                  | some r =>
                      simp [hic, OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre]
  | select d ty c a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv c, evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | trunc d wIn wOut v =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | zext d wIn wOut v =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | sext d wIn wOut v =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | alloca d ty align => simp [HasAlloca] at hi
  | load d ty ptr =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv ptr, hmem]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | store ty val ptr =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv val, evalOperand_env_eq henv ptr]
      cases evalOperand t val with
      | none => exact trivial
      | some vv =>
        cases evalOperand t ptr with
        | none => exact trivial
        | some pv =>
          cases pv with
          | int w x => exact trivial
          | vec n w l => exact trivial
          | ptr addr => exact storeValue_next ⟨henv, hmem, hpc, hpre⟩ ty vv addr
  | gep d elemTy base off =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv base, evalOperand_env_eq henv off]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | icmpVec d pred n w a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | binopVec d op n w a b =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | bitcastMask d n v =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | extractelement d n w v idx =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v, evalOperand_env_eq henv idx]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | insertelement d n w v elt idx =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v, evalOperand_env_eq henv elt, evalOperand_env_eq henv idx]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | shuffleVec d n w a b mask =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv a, evalOperand_env_eq henv b]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | vecBitcast d n w m jw v =>
      simp only [evalInstr]
      rw [evalOperand_env_eq henv v]
      repeat' split
      all_goals (simp [OptStateRel, SameApartFromNext, State.bind, henv, hmem, hpc, hpre])
  | call d retTy callee args =>
      simp only [evalInstr]
      rw [evalOperands_env_eq henv args, hmem]
      cases hargs : evalOperands t args with
      | none => simp only [hargs]; exact trivial
      | some vs =>
        cases ht : calls callee vs t.mem t.next with
        | none =>
            have hm := hcalls callee vs t.mem s.next t.next
            rw [ht] at hm
            cases hl : calls callee vs t.mem s.next with
            | none => simp [hargs, hl, ht, OptStateRel]
            | some r => rw [hl] at hm; simp at hm
        | some r =>
            have hm := hcalls callee vs t.mem s.next t.next
            rw [ht] at hm
            cases hl : calls callee vs t.mem s.next with
            | none => rw [hl] at hm; simp at hm
            | some r' =>
                rw [hl] at hm
                simp at hm
                obtain ⟨hret, hmem'⟩ := hm
                simp only [hargs, hl, ht]
                simp only [OptStateRel, SameApartFromNext]
                simp [henv, hmem, hret, hmem', hpc, hpre]
  | callVoid callee args =>
      simp only [evalInstr]
      rw [evalOperands_env_eq henv args, hmem]
      cases hargs : evalOperands t args with
      | none => simp only [hargs]; exact trivial
      | some vs =>
        cases ht : calls callee vs t.mem t.next with
        | none =>
            have hm := hcalls callee vs t.mem s.next t.next
            rw [ht] at hm
            cases hl : calls callee vs t.mem s.next with
            | none => simp [hargs, hl, ht, OptStateRel]
            | some r => rw [hl] at hm; simp at hm
        | some r =>
            have hm := hcalls callee vs t.mem s.next t.next
            rw [ht] at hm
            cases hl : calls callee vs t.mem s.next with
            | none => rw [hl] at hm; simp at hm
            | some r' =>
                rw [hl] at hm
                simp at hm
                obtain ⟨hret, hmem'⟩ := hm
                simp only [hargs, hl, ht]
                simp only [OptStateRel, SameApartFromNext]
                simp [henv, hmem, hmem', hpc, hpre]

set_option linter.unusedSimpArgs false in
theorem execTerm_next_irr {s t : State} (h : SameApartFromNext s t) (term : Term) :
    CtrlSameApartFromNext (execTerm s term) (execTerm t term) := by
  obtain ⟨henv, hmem, hpc, hpre⟩ := h
  cases term with
  | ret ty v =>
      cases ty with
      | void => cases v <;> simp [execTerm, CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre]
      | int w =>
          cases v with
          | none => simp [execTerm, CtrlSameApartFromNext]
          | some o =>
              simp only [execTerm]
              rw [evalOperand_env_eq henv o]
              cases evalOperand t o <;>
                simp [CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre]
      | ptr =>
          cases v with
          | none => simp [execTerm, CtrlSameApartFromNext]
          | some o =>
              simp only [execTerm]
              rw [evalOperand_env_eq henv o]
              cases evalOperand t o <;>
                simp [CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre]
      | vec n elem =>
          cases v with
          | none => simp [execTerm, CtrlSameApartFromNext]
          | some o =>
              simp only [execTerm]
              rw [evalOperand_env_eq henv o]
              cases evalOperand t o <;>
                simp [CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre]
  | br dest =>
      simp [execTerm, CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre]
  | condbr c t' f =>
      simp only [execTerm]
      rw [evalOperand_env_eq henv c]
      cases hc : evalOperand t c with
      | none => simp [hc, CtrlSameApartFromNext]
      | some vc =>
          cases vc with
          | int w bit =>
              repeat' split
              all_goals (simp [CtrlSameApartFromNext, SameApartFromNext, henv, hmem, hpc, hpre])
          | ptr a => simp [hc, CtrlSameApartFromNext]
          | vec n w l => simp [hc, CtrlSameApartFromNext]
  | unreachable => simp [execTerm, CtrlSameApartFromNext]

set_option linter.unusedSimpArgs false in
theorem noAlloca_block {f : Function} (hf : allocaFree f = true) {b : Block}
    (hb : b ∈ f.blocks) : ∀ i ∈ b.instrs, HasAlloca i = false := by
  simp only [allocaFree, List.all_eq_true] at hf
  have hb' := hf b hb
  simp only [List.all_eq_true, Bool.not_eq_true'] at hb'
  intro i hi
  exact hb' i hi

set_option linter.unusedSimpArgs false in
theorem denoteCode_next_irr {calls : Calls} (hcalls : CallsNextIrr calls) :
    ∀ (is : List Instr) {s t : State}, SameApartFromNext s t →
      (∀ i ∈ is, HasAlloca i = false) →
      OptStateRel (denoteCode calls is s) (denoteCode calls is t)
  | [], s, t, h, _ => by simpa only [denoteCode, OptStateRel] using h
  | i :: rest, s, t, h, hno => by
      have hi : HasAlloca i = false := hno i (by simp)
      have hrest : ∀ j ∈ rest, HasAlloca j = false := by
        intro j hj; exact hno j (by simp [hj])
      have hstep := evalInstr_next_irr hcalls h i hi
      cases hsi : evalInstr calls s i with
      | none =>
          have hti : evalInstr calls t i = none := by
            rw [hsi] at hstep
            exact OptStateRel_none.mp hstep
          simp only [denoteCode, hsi, hti, OptStateRel]
      | some s' =>
          have hti : ∃ t', evalInstr calls t i = some t' ∧ SameApartFromNext s' t' := by
            rw [hsi] at hstep
            exact OptStateRel_some.mp hstep
          obtain ⟨t', hti', hrel⟩ := hti
          simp only [denoteCode, hsi, hti']
          exact denoteCode_next_irr hcalls rest hrel hrest

set_option linter.unusedSimpArgs false in
theorem step_next_irr {calls : Calls} (hcalls : CallsNextIrr calls)
    {f : Function} (hf : allocaFree f = true) {s t : State}
    (h : SameApartFromNext s t) :
    CtrlSameApartFromNext (step calls f s) (step calls f t) := by
  obtain ⟨henv, hmem, hpc, hpre⟩ := h
  unfold step
  rw [show t.pc = s.pc from hpc.symm]
  cases hfind : f.findBlock s.pc with
  | none => simp [CtrlSameApartFromNext]
  | some b =>
      simp only [hfind]
      have hno := noAlloca_block hf (findBlockList_mem hfind)
      have hcode := denoteCode_next_irr hcalls b.instrs ⟨henv, hmem, hpc, hpre⟩ hno
      cases hsi : denoteCode calls b.instrs s with
      | none =>
          have hti : denoteCode calls b.instrs t = none := by
            rw [hsi] at hcode
            exact OptStateRel_none.mp hcode
          simp only [hsi, hti, CtrlSameApartFromNext]
      | some s' =>
          have hti : ∃ t', denoteCode calls b.instrs t = some t' ∧ SameApartFromNext s' t' := by
            rw [hsi] at hcode
            exact OptStateRel_some.mp hcode
          obtain ⟨t', hti', hrel⟩ := hti
          simp only [hsi, hti']
          exact execTerm_next_irr hrel b.term

theorem runFuel_next_irr {calls : Calls} (hcalls : CallsNextIrr calls)
    {f : Function} (hf : allocaFree f = true) :
    ∀ (fuel : Nat) {s t : State}, SameApartFromNext s t →
      runFuel calls fuel f s = runFuel calls fuel f t
  | 0, s, t, _ => rfl
  | fuel + 1, s, t, h => by
      simp only [runFuel]
      have hstep := step_next_irr hcalls hf h
      cases hs : step calls f s with
      | ub =>
          have hb : step calls f t = .ub := by
            rw [hs] at hstep
            cases ht : step calls f t with
            | ub => rfl
            | ret v s' => simp only [CtrlSameApartFromNext, ht] at hstep
            | jump s' => simp only [CtrlSameApartFromNext, ht] at hstep
          simp only [hb]
      | ret v s' =>
          rw [hs] at hstep
          cases ht : step calls f t with
          | ub => simp only [CtrlSameApartFromNext, ht] at hstep
          | ret w t' =>
              simp only [CtrlSameApartFromNext, ht] at hstep
              obtain ⟨hvw, hrel⟩ := hstep
              simp only [hvw, hrel.2.1]
          | jump t' => simp only [CtrlSameApartFromNext, ht] at hstep
      | jump s' =>
          rw [hs] at hstep
          cases ht : step calls f t with
          | ub => simp only [CtrlSameApartFromNext, ht] at hstep
          | ret w t' => simp only [CtrlSameApartFromNext, ht] at hstep
          | jump t' =>
              simp only [CtrlSameApartFromNext, ht] at hstep
              exact runFuel_next_irr hcalls hf fuel hstep


/-! ### The extractor's decode

`wordsAt_eq` turns the record's budget into the headline theorem's own `ent`:
after rewriting the `pre`'s `hent` and `hnblk`, the goal is
`b8RunSteps (wordsAt mem e ent.length) + …`, and the equality is the decode
below rather than a bound. -/

theorem ofNat_toNat (w : BitVec 64) : BitVec.ofNat 64 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

theorem wordsAt_eq {mem : Mem} {e n : Nat} {ent : List (BitVec 64)}
    (hn : n = ent.length) (h : readBytes mem e (8 * n) = some (wordsOf ent)) :
    wordsAt mem e n = ent := by
  subst hn
  unfold wordsAt
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range]
    have hread := readBytes_wordsOf mem e ent h i hi2
    rw [hread]
    simp only [Option.getD_some]
    have hbytes : bytesToNat (natToBytes (ent[i]).toNat 8) = (ent[i]).toNat := by
      rw [natToBytes_toNat]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
      exact Nat.mod_eq_of_lt (ent[i]).isLt
    rw [hbytes, ofNat_toNat]

/-! ### The units do not allocate, and their call environments ignore the base -/

/-- The mask unit executes no `alloca`. -/
theorem s1Masks_noAlloca : allocaFree s1MasksFunction = true := by decide

/-- The POS8 entry emitter executes no `alloca`. -/
theorem entryPos8_noAlloca : allocaFree entryPos8Function = true := by decide

/-- The B8 entry emitter executes no `alloca`. -/
theorem entryB8_noAlloca : allocaFree entryB8Function = true := by decide

/-- The UTF-8 stage executes no `alloca`. -/
theorem utf8_noAlloca : allocaFree utf8Function = true := by decide

theorem s1Calls_nextIrr : CallsNextIrr s1Calls := by
  intro sym args mem n1 n2
  simp only [s1Calls]
  repeat' split <;> simp

theorem entryCalls_nextIrr : CallsNextIrr entryCalls := by
  intro sym args mem n1 n2
  simp only [entryCalls]
  repeat' split <;> simp

theorem utf8Calls_nextIrr : CallsNextIrr utf8Calls := by
  intro sym args mem n1 n2
  simp only [utf8Calls]
  repeat' split <;> simp

/-- The mask unit's run does not depend on the allocator base it is seeded with:
the body allocates nothing and its intrinsics echo the base. -/
theorem masks_next_independent (args : List Value) (mem : Mem) (fuel : Nat) (n m : Nat) :
    runFuel s1Calls fuel s1MasksFunction (EntryState s1MasksFunction args mem n) =
      runFuel s1Calls fuel s1MasksFunction (EntryState s1MasksFunction args mem m) :=
  runFuel_next_irr s1Calls_nextIrr s1Masks_noAlloca fuel ⟨rfl, rfl, rfl, rfl⟩

/-- The POS8 emitter's run does not depend on the allocator base. -/
theorem entry_pos8_next_independent (args : List Value) (mem : Mem) (fuel : Nat)
    (n m : Nat) :
    runFuel entryCalls fuel entryPos8Function (EntryState entryPos8Function args mem n) =
      runFuel entryCalls fuel entryPos8Function (EntryState entryPos8Function args mem m) :=
  runFuel_next_irr entryCalls_nextIrr entryPos8_noAlloca fuel ⟨rfl, rfl, rfl, rfl⟩

/-- The B8 emitter's run does not depend on the allocator base. -/
theorem entry_b8_next_independent (args : List Value) (mem : Mem) (fuel : Nat) (n m : Nat) :
    runFuel entryCalls fuel entryB8Function (EntryState entryB8Function args mem n) =
      runFuel entryCalls fuel entryB8Function (EntryState entryB8Function args mem m) :=
  runFuel_next_irr entryCalls_nextIrr entryB8_noAlloca fuel ⟨rfl, rfl, rfl, rfl⟩

/-- The UTF-8 stage's run does not depend on the allocator base. -/
theorem utf8_next_independent (args : List Value) (mem : Mem) (fuel : Nat) (n m : Nat) :
    runFuel utf8Calls fuel utf8Function (EntryState utf8Function args mem n) =
      runFuel utf8Calls fuel utf8Function (EntryState utf8Function args mem m) :=
  runFuel_next_irr utf8Calls_nextIrr utf8_noAlloca fuel ⟨rfl, rfl, rfl, rfl⟩

/-! ### The mask unit's record -/

/-- The mask unit's claim about the memory it leaves: the six specification masks
at the output slot, the outgoing carry at the carry slot, and every byte outside
the two store regions unchanged.

The regions are the **store** regions, `c … c+24` and `o … o+48`, not the
headline sweep's three excluded slots: the input block at `p` is one of that
sweep's excluded slots even though the body only reads it, and a caller's
input-unchanged claim needs it. -/
def masksPost (args : List Value) (mem m : Mem) : Prop :=
  ∃ (p c o : Nat) (lo hi : Block32) (st : ClassState) (opened ppar : Bool),
    args = [.ptr p, .ptr c, .ptr o] ∧
    readBytes mem p 64 = some (block64 lo hi) ∧
    readBytes mem c 24 = some (carrySlot opened ppar st.inside) ∧
    st.oddRun = (opened && ppar) ∧
    readBytes m o 8 = some (natToBytes (specQuote64 lo hi st).toNat 8) ∧
    readBytes m (o + 8) 8 = some (natToBytes (specDelimiter64 lo hi st).toNat 8) ∧
    readBytes m (o + 16) 8 = some (natToBytes (specInString64 lo hi st).toNat 8) ∧
    readBytes m (o + 24) 8 = some (natToBytes (specSpace64 lo hi st).toNat 8) ∧
    readBytes m (o + 32) 8 = some (natToBytes (specBackslash64 lo hi st).toNat 8) ∧
    readBytes m (o + 40) 8 = some (natToBytes (specControl64 lo hi st).toNat 8) ∧
    readBytes m c 24 = some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩))
      (carry64 lo hi st).oddRun (carry64 lo hi st).inside) ∧
    (∀ a, ¬ (c ≤ a ∧ a < c + 24) → ¬ (o ≤ a ∧ a < o + 48) →
      readByte m a = readByte mem a)

/-- The mask unit's boundary record.  Its budget is the single step the body
runs, its `pre` is `s1_masks_refines`' hypothesis set, and its `post` is
`masksPost`; `.ub` is refused by the `match`. -/
def Γ_masks : MemContract where
  budget := fun _ _ => 1
  pre := fun args mem _ =>
    ∃ (p c o : Nat) (lo hi : Block32) (st : ClassState) (opened ppar : Bool),
      args = [.ptr p, .ptr c, .ptr o] ∧
      readBytes mem p 64 = some (block64 lo hi) ∧
      readBytes mem c 24 = some (carrySlot opened ppar st.inside) ∧
      st.oddRun = (opened && ppar) ∧
      (p + 64 ≤ c ∨ c + 24 ≤ p) ∧
      (p + 64 ≤ o ∨ o + 48 ≤ p) ∧
      (c + 24 ≤ o ∨ o + 48 ≤ c)
  post := fun args mem _ o =>
    match o with
    | .ub => False
    | .ret _ m => masksPost args mem m

/-- The mask record's guarantee ignores the returned value. -/
theorem masks_valueIrrelevant : ValueIrrelevant Γ_masks := by
  intro args mem next v v' m
  rfl

/-- The mask record refuses `ub`: its `post` is `False` at that outcome, so
"the record forbids undefined behaviour" is a proposition. -/
theorem masks_ub_false (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Γ_masks.post args mem next .ub := by
  intro h; exact h

/-- **The mask record's unchanged conjunct is over the store regions.**  It is
stronger than the headline's three-slot sweep, which is silent about the input
block the body only reads. -/
theorem masks_written_extent (k : Ctx) (mem : Mem) :
    ∀ a, ¬ (k.c ≤ a ∧ a < k.c + 24) → ¬ (k.o ≤ a ∧ a < k.o + 48) →
      readByte (s1SlotMem k mem) a = readByte mem a := by
  intro a hc ho
  have hc' : a < k.c ∨ k.c + 24 ≤ a := by
    rcases Nat.lt_or_ge a k.c with h | h
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_not_lt fun hlt => hc ⟨h, hlt⟩)
  have ho' : a < k.o ∨ k.o + 48 ≤ a := by
    rcases Nat.lt_or_ge a k.o with h | h
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_not_lt fun hlt => ho ⟨h, hlt⟩)
  simp only [s1SlotMem]
  repeat' rw [readByte_writeBytes_outside _ _ (by rw [natToBytes_length]; omega)]

/-- **The mask unit satisfies its record.**  The headline theorem is applied at
its own one-step fuel, and the allocator base is rewritten by
`masks_next_independent`.  The unchanged conjunct is
`masks_written_extent`'s, after the run is identified with `s1SlotMem`. -/
theorem masks_satisfies : Satisfies s1Calls s1MasksFunction Γ_masks := by
  intro args mem next hpre
  obtain ⟨p, c, o, lo, hi, st, opened, ppar, hargs, hblock, hcarry, hodd,
    hd1, hd2, hd3⟩ := hpre
  subst args
  let k : Ctx := ⟨p, c, o, lo, hi, opened, ppar, st⟩
  -- the headline's own run leaves `s1SlotMem`
  have hl0 : readBytes mem p 32 = some (List.ofFn lo) := by
    obtain ⟨h1, _⟩ := readBytes_split mem p 32 32 hblock
    rw [block64, blockTake lo hi] at h1
    exact h1
  have hl1 : readBytes mem (p + 32) 32 = some (List.ofFn hi) := by
    obtain ⟨_, h2⟩ := readBytes_split mem p 32 32 hblock
    rw [block64, blockDrop lo hi] at h2
    exact h2
  have hd0 : readBytes mem c 8 = some (natToBytes (if opened then 1 else 0) 8) := by
    obtain ⟨h1, _⟩ := readBytes_split mem c 8 16 hcarry
    rw [carrySlot, List.append_assoc, slotTake] at h1
    exact h1
  have hdrest : readBytes mem (c + 8) 16
      = some (natToBytes (if ppar then 1 else 0) 8 ++
          natToBytes (if st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8) := by
    obtain ⟨_, h2⟩ := readBytes_split mem c 8 16 hcarry
    rw [carrySlot, List.append_assoc, slotDrop] at h2
    exact h2
  have hd1' : readBytes mem (c + 8) 8 = some (natToBytes (if ppar then 1 else 0) 8) := by
    obtain ⟨h1, _⟩ := readBytes_split mem (c + 8) 8 8 hdrest
    rw [slotTake] at h1
    exact h1
  have hd2' : readBytes mem (c + 16) 8
      = some (natToBytes (if st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8) := by
    obtain ⟨_, h2⟩ := readBytes_split mem (c + 8) 8 8 hdrest
    rw [show c + 8 + 8 = c + 16 from by omega, slotDrop] at h2
    exact h2
  have hp : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%p"
      = some (.ptr p) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
  have hc : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%c"
      = some (.ptr c) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
    rfl
  have ho : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%o"
      = some (.ptr o) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
    rfl
  have hrunSlot : runFuel s1Calls 1 s1MasksFunction
      { (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]) with mem := mem }
      = some (.ret none (s1SlotMem k mem)) := by
    have h := s1_runFuel (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env
      { (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]) with mem := mem } k
      rfl hp hc ho hl0 hl1 hd0 hd1' hd2'
    simpa only [k, JsonS1MasksSteps.withEnv] using h
  have hrunE : runFuel s1Calls 1 s1MasksFunction
      (EntryState s1MasksFunction [.ptr p, .ptr c, .ptr o] mem 1)
      = some (.ret none (s1SlotMem k mem)) := by
    change runFuel s1Calls 1 s1MasksFunction
      { (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]) with mem := mem }
      = some (.ret none (s1SlotMem k mem))
    exact hrunSlot
  obtain ⟨mem', hrun, hw1, hw2, hw3, hw4, hw5, hw6, hw7, _hunchanged⟩ :=
    s1_masks_refines lo hi st opened ppar hodd mem p c o hblock hcarry hd1 hd2 hd3
  have hmem' : mem' = s1SlotMem k mem := by
    have hrun2 := hrun
    rw [hrunSlot] at hrun2
    have h1 := Option.some.inj hrun2
    have h2 := congrArg (fun o : Outcome => match o with | .ret _ m => m | .ub => []) h1
    exact h2.symm
  have hunchanged : ∀ a, ¬ (c ≤ a ∧ a < c + 24) → ¬ (o ≤ a ∧ a < o + 48) →
      readByte mem' a = readByte mem a := by
    intro a hcc hoo
    rw [hmem']
    exact masks_written_extent k mem a hcc hoo
  have hbudget : Γ_masks.budget [.ptr p, .ptr c, .ptr o] mem = 1 := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨none, mem', ?_⟩
    rw [hbudget]
    rw [masks_next_independent [.ptr p, .ptr c, .ptr o] mem 1 next 1, hmem']
    exact hrunE
  · intro out hout
    rcases hout with ⟨n, hnub⟩ | ⟨n, hn⟩
    · rw [masks_next_independent [.ptr p, .ptr c, .ptr o] mem n next 1] at hnub
      cases n with
      | zero => simp [runFuel] at hnub
      | succ k =>
          have h := runFuel_mono hrunE (d := k)
          rw [show 1 + k = k + 1 from by omega] at h
          rw [h] at hnub
          cases hnub
    · rw [masks_next_independent [.ptr p, .ptr c, .ptr o] mem n next 1] at hn
      have ho' : out = .ret none mem' := by
        cases n with
        | zero => simp [runFuel] at hn
        | succ k =>
            have h := runFuel_mono hrunE (d := k)
            rw [show 1 + k = k + 1 from by omega] at h
            rw [h] at hn
            have h1 := Option.some.inj hn
            rw [← hmem'] at h1
            exact h1.symm
      subst ho'
      exact ⟨p, c, o, lo, hi, st, opened, ppar, rfl, hblock, hcarry, hodd,
        hw1, hw2, hw3, hw4, hw5, hw6, hw7, hunchanged⟩

/-! ### The completion's shape on the pinned ASTs

`satisfies_calls` takes `retsValued body = true`, the **completion's** shape and
not the header's: `execTerm` decides a return's shape from the terminator's own
`ty`, and the parser accepts a `ret` whose `ty` disagrees with the header.  The
property is decidable on the pinned AST, so it is a `#guard` at each unit rather
than a proof obligation in prose.  The mask body is the negative control: its
terminator is `.ret .void none`, so it takes the void bridge instead. -/

#guard retsValued entryPos8Function
#guard retsValued entryB8Function
#guard retsValued utf8Function
#guard !retsValued s1MasksFunction

/-! ### The entry emitters' records -/

/-- The POS8 emitter's claim about the memory it leaves. -/
def entryPos8Post (args : List Value) (mem : Mem) (v : Value) (m : Mem) : Prop :=
  ∃ (e o tab : Nat) (blk0 nblk k : BitVec 64) (ent : List (BitVec 64)) (k' : Nat),
    args = [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] ∧
    v = .int 64 (BitVec.ofNat 64 k') ∧
    k' = k.toNat + (ent.map BitLanes.ctpop).sum ∧
    readLanes32 m (o + 4 * k.toNat) (k' - k.toNat)
      = streamPrefix ent blk0.toNat nblk.toNat ∧
    -- the mask words the call read, named: the stream's positions are lanes of
    -- *these* words.  Without it a consumer holds a stream whose positions are
    -- `streamPrefix ent …` for an existential `ent` it cannot bound, although the
    -- written lanes determine `ent` in fact — an existential unique in fact is
    -- still not a fact the record states.
    nblk.toNat = ent.length ∧
    readBytes mem e (8 * ent.length) = some (wordsOf ent) ∧
    -- the frame starts at the *written* extent's base: the lanes are written from
    -- `o + 4 * k`, so the prefix an earlier call wrote is untouched.  Stated at the
    -- headline's own hypothesis, a loosening of it would refuse the composition.
    (∀ a, a < o + 4 * k.toNat ∨ o + 4 * (k' + 8) ≤ a →
      readByte m a = readByte mem a)

/-- The POS8 emitter's boundary record.  Its budget is the headline theorem's
own `3 * nblk + 3`, and its `pre` names every hypothesis of that theorem, with
`outCap` instantiated by the `pre` because the body does not carry it. -/
def Γ_entry_pos8 : MemContract where
  budget := fun args _ =>
    match args with
    | [_, _, .int 64 nblk, _, _, _] => 3 * nblk.toNat + 3
    | _ => 0
  pre := fun args mem _ =>
    ∃ (e o tab : Nat) (blk0 nblk k : BitVec 64) (ent : List (BitVec 64)) (outCap : Nat),
      args = [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] ∧
      nblk.toNat = ent.length ∧
      64 * (blk0.toNat + nblk.toNat) + 63 < 2 ^ 32 ∧
      readBytes mem e (8 * ent.length) = some (wordsOf ent) ∧
      readBytes mem tab 8192 = some pos8Table ∧
      ((e + 8 * ent.length ≤ o ∨ o + 4 * (k.toNat + 64 * ent.length + 8) ≤ e) ∧
       (tab + 8192 ≤ o ∨ o + 4 * (k.toNat + 64 * ent.length + 8) ≤ tab)) ∧
      k.toNat + 64 * ent.length + 9 ≤ outCap ∧
      k.toNat + 64 * ent.length + 9 < 2 ^ 63
  post := fun args mem _ o =>
    match o with
    | .ret (some v) m => entryPos8Post args mem v m
    | _ => False

/-- The B8 emitter's claim about the memory it leaves. -/
def entryB8Post (args : List Value) (mem : Mem) (v : Value) (m : Mem) : Prop :=
  ∃ (e o : Nat) (blk0 nblk k : BitVec 64) (ent : List (BitVec 64)) (k' : Nat),
    args = [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] ∧
    v = .int 64 (BitVec.ofNat 64 k') ∧
    k' = k.toNat + (ent.map BitLanes.ctpop).sum ∧
    readLanes32 m (o + 4 * k.toNat) (k' - k.toNat)
      = streamPrefix ent blk0.toNat nblk.toNat ∧
    -- the mask words the call read, named (see the POS8 post).
    nblk.toNat = ent.length ∧
    readBytes mem e (8 * ent.length) = some (wordsOf ent) ∧
    -- the frame starts at the written extent's base (see the POS8 post).
    (∀ a, a < o + 4 * k.toNat ∨ o + 4 * (k' + 7) ≤ a →
      readByte m a = readByte mem a)

/-- The B8 emitter's boundary record.  Its budget folds over the words read out
of memory, which is why the field takes the memory as well as the arguments. -/
def Γ_entry_b8 : MemContract where
  budget := fun args mem =>
    match args with
    | [.ptr e, _, .int 64 nblk, _, _] =>
        b8RunSteps (wordsAt mem e nblk.toNat) + nblk.toNat + 2
    | _ => 0
  pre := fun args mem _ =>
    ∃ (e o : Nat) (blk0 nblk k : BitVec 64) (ent : List (BitVec 64)),
      args = [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] ∧
      nblk.toNat = ent.length ∧
      64 * (blk0.toNat + nblk.toNat) + 63 < 2 ^ 32 ∧
      readBytes mem e (8 * ent.length) = some (wordsOf ent) ∧
      (e + 8 * ent.length ≤ o ∨ o + 4 * (k.toNat + 64 * ent.length + 8) ≤ e) ∧
      k.toNat + 64 * ent.length + 9 < 2 ^ 63
  post := fun args mem _ o =>
    match o with
    | .ret (some v) m => entryB8Post args mem v m
    | _ => False

/-! ### The UTF-8 stage's record -/

/-- The UTF-8 stage's claim about the memory it leaves: the verdict, the window
relation, and **the full byte equality** `m = mem`.  The stage writes nothing, so
the equality is the strongest form of the unchanged conjunct and is what the
headline proves; an observable `readByte` agreement outside the window would leave
an implementation free to write inside it, which the run does not do. -/
def utf8Post (args : List Value) (mem : Mem) (v : Value) (m : Mem) : Prop :=
  ∃ (b : Nat) (n : BitVec 64) (gate : BitVec 32) (bs : Bytes) (nb : Nat)
    (err' : BitVec 64),
    args = [.ptr b, .int 64 n, .int 32 gate] ∧
    v = .int 64 err' ∧
    (err' = 0 ∨ err' = 1) ∧
    (err' = 0 ↔ utf8WinPrefix (utf8Window bs.toList n.toNat nb)) ∧
    n.toNat = bs.length ∧ nb = (n.toNat + 63) / 64 ∧
    readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs.toList n.toNat nb) ∧
    0 < n.toNat ∧
    m = mem

/-- The UTF-8 stage's boundary record. -/
def Γ_utf8 : MemContract where
  budget := fun args _ =>
    match args with
    | [_, .int 64 n, _] => fuelOf ((n.toNat + 63) / 64)
    | _ => 0
  pre := fun args mem _ =>
    ∃ (b : Nat) (n : BitVec 64) (gate : BitVec 32) (ungated : Bool) (bs : Bytes) (nb : Nat),
      args = [.ptr b, .int 64 n, .int 32 gate] ∧
      gate = BitVec.ofNat 32 (if ungated then 1 else 0) ∧
      n.toNat = bs.length ∧ nb = (n.toNat + 63) / 64 ∧
      3 ≤ b ∧ n.toNat + 63 < 2 ^ 64 ∧ n.toNat < 2 ^ 63 ∧
      readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs.toList n.toNat nb) ∧
      0 < n.toNat
  post := fun args mem _ o =>
    match o with
    | .ret (some v) m => utf8Post args mem v m
    | _ => False

/-! ### The entries satisfy their records -/

/-- **The POS8 emitter satisfies its record**, from `entry_pos8_refines` at the
headline's own fuel, with the allocator base rewritten. -/
theorem entry_pos8_satisfies : Satisfies entryCalls entryPos8Function Γ_entry_pos8 := by
  intro args mem next hpre
  obtain ⟨e, o, tab, blk0, nblk, k, ent, outCap, hargs, hnb, hblk, hent, htab,
    hdisj, hcap, hk63⟩ := hpre
  subst args
  -- The headline theorem is the wrapper's only substantive input, and the negative
  -- build (`tests/json-unit-contracts/negative.sh`) replaces the marked line with
  -- a hole of this type: the residual goal is the theorem's own conclusion.
  have hheadline : ∃ (k' : Nat) (mem' : Mem),
      runFuel entryCalls (3 * nblk.toNat + 3) entryPos8Function
        { (initState entryPos8Function
            [.ptr e, .int 64 blk0.toNat, .int 64 nblk.toNat, .ptr o, .int 64 k.toNat,
              .ptr tab]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') ∧
      k' = k.toNat + (ent.map BitLanes.ctpop).sum ∧
      readLanes32 mem' (o + 4 * k.toNat) (k' - k.toNat)
        = streamPrefix ent blk0.toNat nblk.toNat ∧
      (∀ a, a < o + 4 * k.toNat ∨ o + 4 * (k' + 8) ≤ a →
        readByte mem' a = readByte mem a) := by
    exact entry_pos8_refines ent blk0.toNat nblk.toNat k.toNat mem e o tab outCap hnb hblk hent htab hdisj hcap hk63 -- negative-build-anchor
  obtain ⟨k', mem', hrun, hk', hread, hunch⟩ := hheadline
  have hbudget : Γ_entry_pos8.budget
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] mem
      = 3 * nblk.toNat + 3 := rfl
  -- `initState` receives the arguments as `Nat`s while the record carries the
  -- words, so the entry environments differ in `BitVec.ofNat w w.toNat` for the
  -- three words.  The roundtrip is `ofNat_toNat`, stated on the `NatCast` form
  -- the goal actually carries.
  have hb0 : (↑blk0.toNat : BitVec 64) = blk0 := ofNat_toNat blk0
  have hnb0 : (↑nblk.toNat : BitVec 64) = nblk := ofNat_toNat nblk
  have hk0 : (↑k.toNat : BitVec 64) = k := ofNat_toNat k
  have hstate : EntryState entryPos8Function
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] mem 1
      = { (initState entryPos8Function
          [.ptr e, .int 64 blk0.toNat, .int 64 nblk.toNat, .ptr o, .int 64 k.toNat,
            .ptr tab]) with mem := mem } := by
    simp only [EntryState, initState, hb0, hnb0, hk0]
  have hrunE : runFuel entryCalls (3 * nblk.toNat + 3) entryPos8Function
      (EntryState entryPos8Function
        [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] mem 1)
      = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') := by
    rw [hstate]
    exact hrun
  have hsingle : ∀ (n : Nat) (out : Outcome),
      runFuel entryCalls n entryPos8Function
        (EntryState entryPos8Function
          [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab] mem 1)
        = some out →
      out = .ret (some (.int 64 (BitVec.ofNat 64 k'))) mem' := by
    intro n out hn
    rcases Nat.le_total n (3 * nblk.toNat + 3) with hle | hge
    · have h1 := runFuel_mono_le hle hn
      rw [hrunE] at h1
      exact (Option.some.inj h1).symm
    · have h1 := runFuel_mono_le hge hrunE
      rw [h1] at hn
      exact (Option.some.inj hn).symm
  refine ⟨?_, ?_⟩
  · refine ⟨some (.int 64 (BitVec.ofNat 64 k')), mem', ?_⟩
    rw [hbudget, entry_pos8_next_independent _ mem (3 * nblk.toNat + 3) next 1, hrunE]
  · intro out hout
    rcases hout with ⟨n, hb⟩ | ⟨n, hr⟩
    · rw [entry_pos8_next_independent _ mem n next 1] at hb
      have h := hsingle n .ub hb
      cases h
    · rw [entry_pos8_next_independent _ mem n next 1] at hr
      have h := hsingle n out hr
      subst h
      exact ⟨e, o, tab, blk0, nblk, k, ent, k', rfl, rfl, hk', hread, hnb, hent, hunch⟩

/-- **The B8 emitter satisfies its record**, with its memory-indexed budget
turned into the headline's own `ent` by `wordsAt_eq`. -/
theorem entry_b8_satisfies : Satisfies entryCalls entryB8Function Γ_entry_b8 := by
  intro args mem next hpre
  obtain ⟨e, o, blk0, nblk, k, ent, hargs, hnb, hblk, hent, hdisj, hk63⟩ := hpre
  subst args
  obtain ⟨k', mem', hrun, hk', hread, hunch⟩ :=
    entry_b8_refines ent blk0.toNat nblk.toNat k.toNat mem e o
      hnb hblk hent hdisj hk63
  have hwa : wordsAt mem e nblk.toNat = ent :=
    wordsAt_eq hnb (by rw [hnb]; exact hent)
  have hbudget : Γ_entry_b8.budget
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] mem
      = b8RunSteps (wordsAt mem e nblk.toNat) + nblk.toNat + 2 := rfl
  have hb0 : (↑blk0.toNat : BitVec 64) = blk0 := ofNat_toNat blk0
  have hnb0 : (↑nblk.toNat : BitVec 64) = nblk := ofNat_toNat nblk
  have hk0 : (↑k.toNat : BitVec 64) = k := ofNat_toNat k
  have hstate : EntryState entryB8Function
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] mem 1
      = { (initState entryB8Function
          [.ptr e, .int 64 blk0.toNat, .int 64 nblk.toNat, .ptr o, .int 64 k.toNat])
          with mem := mem } := by
    simp only [EntryState, initState, hb0, hnb0, hk0]
  have hrunE : runFuel entryCalls
      (b8RunSteps (wordsAt mem e nblk.toNat) + nblk.toNat + 2) entryB8Function
      (EntryState entryB8Function
        [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] mem 1)
      = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') := by
    rw [hwa, hstate]
    exact hrun
  have hsingle : ∀ (n : Nat) (out : Outcome),
      runFuel entryCalls n entryB8Function
        (EntryState entryB8Function
          [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] mem 1)
        = some out →
      out = .ret (some (.int 64 (BitVec.ofNat 64 k'))) mem' := by
    intro n out hn
    rcases Nat.le_total n (b8RunSteps (wordsAt mem e nblk.toNat) + nblk.toNat + 2)
      with hle | hge
    · have h1 := runFuel_mono_le hle hn
      rw [hrunE] at h1
      exact (Option.some.inj h1).symm
    · have h1 := runFuel_mono_le hge hrunE
      rw [h1] at hn
      exact (Option.some.inj hn).symm
  refine ⟨?_, ?_⟩
  · refine ⟨some (.int 64 (BitVec.ofNat 64 k')), mem', ?_⟩
    rw [hbudget, entry_b8_next_independent _ mem (b8RunSteps (wordsAt mem e nblk.toNat)
      + nblk.toNat + 2) next 1, hrunE]
  · intro out hout
    rcases hout with ⟨n, hb⟩ | ⟨n, hr⟩
    · rw [entry_b8_next_independent _ mem n next 1] at hb
      have h := hsingle n .ub hb
      cases h
    · rw [entry_b8_next_independent _ mem n next 1] at hr
      have h := hsingle n out hr
      subst h
      exact ⟨e, o, blk0, nblk, k, ent, k', rfl, rfl, hk', hread, hnb, hent, hunch⟩

/-! ### The UTF-8 stage satisfies its record -/

/-- **The UTF-8 stage satisfies its record**, from `utf8_stage_refines` at the
headline's own fuel. -/
theorem utf8_satisfies : Satisfies utf8Calls utf8Function Γ_utf8 := by
  intro args mem next hpre
  obtain ⟨b, n, gate, ungated, bs, nb, hargs, hgate, hn, hnb, hb, hlen, haddr,
    hread, hpos⟩ := hpre
  subst args
  subst nb
  obtain ⟨err', mem', hrun, herr01, herr0, hmem⟩ :=
    utf8_stage_refines bs n.toNat ((n.toNat + 63) / 64) mem b ungated
      hn rfl hb hlen haddr hread hpos
  have hbudget : Γ_utf8.budget [.ptr b, .int 64 n, .int 32 gate] mem
      = fuelOf ((n.toNat + 63) / 64) := rfl
  have hnat : (↑n.toNat : BitVec 64) = n := ofNat_toNat n
  -- The gate reaches `initState` as an `OfNat` literal rather than a `Nat` cast.
  have hg32 : BitVec.ofNat 32 (if ungated then 1 else 0)
      = (if ungated then (1 : BitVec 32) else 0) := by
    cases ungated <;> rfl
  have hstate : EntryState utf8Function [.ptr b, .int 64 n, .int 32 gate] mem 1
      = { (initState utf8Function
          [.ptr b, .int 64 n.toNat, .int 32 (if ungated then 1 else 0)]) with mem := mem } := by
    rw [hgate]
    simp only [EntryState, initState, hnat, hg32]
  have hrunE : runFuel utf8Calls (fuelOf ((n.toNat + 63) / 64)) utf8Function
      (EntryState utf8Function [.ptr b, .int 64 n, .int 32 gate] mem 1)
      = some (.ret (some (.int 64 err')) mem') := by
    rw [hstate]
    exact hrun
  have hsingle : ∀ (m : Nat) (out : Outcome),
      runFuel utf8Calls m utf8Function
        (EntryState utf8Function [.ptr b, .int 64 n, .int 32 gate] mem 1) = some out →
      out = .ret (some (.int 64 err')) mem' := by
    intro m out hm
    rcases Nat.le_total m (fuelOf ((n.toNat + 63) / 64)) with hle | hge
    · have h1 := runFuel_mono_le hle hm
      rw [hrunE] at h1
      exact (Option.some.inj h1).symm
    · have h1 := runFuel_mono_le hge hrunE
      rw [h1] at hm
      exact (Option.some.inj hm).symm
  refine ⟨?_, ?_⟩
  · refine ⟨some (.int 64 err'), mem', ?_⟩
    rw [hbudget, utf8_next_independent _ mem (fuelOf ((n.toNat + 63) / 64)) next 1, hrunE]
  · intro out hout
    rcases hout with ⟨m, hb⟩ | ⟨m, hr⟩
    · rw [utf8_next_independent _ mem m next 1] at hb
      have h := hsingle m .ub hb
      cases h
    · rw [utf8_next_independent _ mem m next 1] at hr
      have h := hsingle m out hr
      subst h
      -- The headline's verdict is a `Nat` word; the record's is the `BitVec 64`
      -- the return carries.  The two facts transfer because the verdict is 0 or 1.
      have hv01 : (↑err' : BitVec 64) = 0 ∨ (↑err' : BitVec 64) = 1 := by
        rcases herr01 with h0 | h0 <;> (subst h0; simp)
      have hv0 : ((↑err' : BitVec 64) = 0 ↔
          utf8WinPrefix (utf8Window bs.toList n.toNat ((n.toNat + 63) / 64))) := by
        rcases herr01 with h0 | h0 <;> (subst h0; simpa using herr0)
      exact ⟨b, n, gate, bs, (n.toNat + 63) / 64, err', rfl, rfl, hv01, hv0,
        hn, rfl, hread, hpos, hmem⟩

/-! ### The controls

The wrappers above would be vacuous if a record's `pre` admitted nothing, or if
`pre` already implied `post`.  Six controls, each with the observation that makes
it **fail** — that is, that shows it has caught a defect rather than passed:

1. **`pre` inhabited** (`masks_pre_inhabited`, `entry_pos8_pre_inhabited`,
   `entry_b8_pre_inhabited`, `utf8_pre_inhabited`): each record's `pre` is proved
   at a concrete staged memory, built with `writeBytes` from the empty memory and
   read back with `readBytes_writeBytes_same`.  It fails if a `pre` conjunct is
   unsatisfiable at the staging it claims to describe — the proof of the concrete
   read then has no inhabitant.
2. **`pre` does not imply `post`** (`masks_post_not_implied` and the three
   siblings): a state the record's `pre` admits is paired with an outcome the
   record's `post` refuses.  It fails if the record's `post` is derivable from its
   `pre`, because the refusal then also closes.
3. **The headline theorem is load-bearing** — `tests/json-unit-contracts/negative.sh`
   copies this module, replaces the anchor line — the one comment-marked
   `negative-build-anchor` — with a hole of the enclosing `have`'s type, and
   builds the copy by name.  With
   `entry_pos8_refines` removed from `entry_pos8_satisfies`'s inputs the residual
   goal is exactly that theorem's conclusion (`∃ k' mem', runFuel … = some (.ret …)
   ∧ …`), the context still holds every `pre` conjunct and cannot produce it, and
   the footprint pin reports the `sorryAx` carrier beside the named declaration.
   The check fails if the build succeeds or fails anywhere else.
4. **`ValueIrrelevant` is not free** (`readsValue_not_valueIrrelevant`): a record
   whose `post` reads the returned value fails it, so `satisfies_calls_void`
   cannot attach to it.  It fails if the value-refusing record turns out
   value-irrelevant, because the negation then has no witness.
5. **The call-site control** (`masks_shifted_calls_refused`): a selection that runs
   the mask body at a state whose memory is not the caller's answers `none`, so
   `CallSatisfies` — which requires the selection to resolve — is false at the mask
   symbol with `Γ_masks`, the symbol and record a caller resolving the mask unit
   uses.
   It fails if the shifted selection still resolves to an admitted call.
6. **The composition site, and the law's other half**
   (`masksStaged_satisfies`, `masksStaged_calls`, and `masksMispost_not_satisfies`
   with `masksMispost_witness`): `Satisfies.mono` is applied at the one site the
   records need — the mask call, with the caller's staging precondition and the
   post and budget unchanged — and the void bridge still attaches there because
   the post is unchanged.  The positive application fails if the site has to
   weaken the post: a weakened post need not be value-irrelevant, which control 4
   exhibits, and the bridge would then not attach.  The refutation is the other
   half: with the budget equal pointwise and the `pre` unchanged, a record whose
   post the unit's does not imply is **not** satisfied, so the law's `hw` cannot
   be dropped — the failure is attributable to the post rather than to a smaller
   budget or a stronger pre.

The staged memories are
built with `writeBytes` from the empty memory, which is what
`readBytes_writeBytes_same` reads back, and their segments are disjoint by
construction.
-/

/-- The mask unit's ABI symbol, read from its pinned AST rather than retyped. -/
def masksSym : String := s1MasksFunction.name

/-- The all-`NUL` block: a concrete `Block32` for the staged input.  The fixture
only needs it to be a value the staged memory and the record's `pre` both name. -/
def nulBlock32 : Block32 := fun _ => 0

/-- The all-`NUL` sixty-four-byte block.  -/
def nulBlock64 : List UInt8 := block64 nulBlock32 nulBlock32

theorem nulBlock64_length : nulBlock64.length = 64 := by
  simp [nulBlock64, block64]

theorem carrySlot_length (opened ppar inside : Bool) :
    (carrySlot opened ppar inside).length = 24 := by
  simp [carrySlot, natToBytes_length]

/-- The mask record's staged memory: the block at `0` and the carry slot at `64`,
one contiguous write of eighty-eight bytes. -/
def masksMem (opened ppar inside : Bool) : Mem :=
  writeBytes [] 0 (nulBlock64 ++ carrySlot opened ppar inside)

/-- A range read of the empty memory is absent. -/
theorem readBytes_nil_succ (addr n : Nat) : readBytes ([] : Mem) addr (n + 1) = none :=
  rfl

theorem masksMem_full (opened ppar inside : Bool) :
    readBytes (masksMem opened ppar inside) 0 (64 + 24)
      = some (nulBlock64 ++ carrySlot opened ppar inside) := by
  rw [masksMem]
  rw [show (64 + 24) = (nulBlock64 ++ carrySlot opened ppar inside).length from by
    simp [nulBlock64_length, carrySlot_length]]
  exact readBytes_writeBytes_same [] (bs := nulBlock64 ++ carrySlot opened ppar inside)
    (addr := 0)

theorem masksMem_block : readBytes (masksMem true false false) 0 64
    = some nulBlock64 := by
  obtain ⟨h1, -⟩ := readBytes_split (masksMem true false false) 0 64 24
    (masksMem_full true false false)
  have htake : (nulBlock64 ++ carrySlot true false false).take 64 = nulBlock64 := by
    rw [show 64 = nulBlock64.length from by simp [nulBlock64_length]]
    exact List.take_left
  rw [h1, htake]

theorem masksMem_carry : readBytes (masksMem true false false) 64 24
    = some (carrySlot true false false) := by
  obtain ⟨-, h2⟩ := readBytes_split (masksMem true false false) 0 64 24
    (masksMem_full true false false)
  have hdrop : (nulBlock64 ++ carrySlot true false false).drop 64
      = carrySlot true false false := by
    rw [show 64 = nulBlock64.length from by simp [nulBlock64_length]]
    exact List.drop_left
  rw [h2, hdrop]

/-- Control (i), mask record: `pre` is inhabited at a concrete staged state. -/
theorem masks_pre_inhabited :
    Γ_masks.pre [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1 := by
  refine ⟨0, 64, 128, nulBlock32, nulBlock32, ⟨false, false⟩, true, false,
    rfl, masksMem_block, masksMem_carry, rfl, ?_, ?_, ?_⟩
  all_goals exact Or.inl (by simp)

/-- The POS8 record's staged memory: the emitter's table at `256`.  The stack
prefix the entry test builds lies at the caller's `o`, which the record leaves
unwritten, so nothing else need be present. -/
def pos8Mem : Mem := writeBytes [] 256 pos8Table

theorem pos8Mem_table : readBytes pos8Mem 256 8192 = some pos8Table := by
  rw [pos8Mem, ← pos8Table_length]
  exact readBytes_writeBytes_same [] (bs := pos8Table) (addr := 256)

/-- Control (i), POS8 record: `pre` is inhabited at a concrete staged state.  The
input stream is empty (`nblk = 0`), so its readability is `readBytes mem e 0`. -/
theorem entry_pos8_pre_inhabited :
    Γ_entry_pos8.pre [.ptr 0, .int 64 0, .int 64 0, .ptr 128, .int 64 0, .ptr 256]
      pos8Mem 1 := by
  refine ⟨0, 128, 256, 0, 0, 0, ([] : List (BitVec 64)), 9, rfl, rfl, ?_, rfl, ?_,
    ?_, ?_, ?_⟩
  · simp
  · exact pos8Mem_table
  · exact ⟨by simp, by simp⟩
  · simp
  · simp

/-- Control (i), B8 record: `pre` is inhabited at a concrete staged state.  The
record needs no table, and an empty input stream makes its readability `rfl`. -/
theorem entry_b8_pre_inhabited :
    Γ_entry_b8.pre [.ptr 0, .int 64 0, .int 64 0, .ptr 128, .int 64 0] [] 1 := by
  refine ⟨0, 128, 0, 0, 0, ([] : List (BitVec 64)), rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp
  · exact Or.inl (by simp)
  · simp

/-- The UTF-8 record's staged memory: the three zero prefix bytes and one
sixty-four-byte window holding a single `A`, at `0`. -/
def utf8Mem : Mem := writeBytes [] 0 (utf8Window [0x41] 1 1)

theorem utf8Mem_window : readBytes utf8Mem (3 - 3) (3 + 64 * 1)
    = some (utf8Window [0x41] 1 1) := by
  rw [utf8Mem, show 3 - 3 = 0 from rfl]
  rw [← utf8Window_length (doc := [0x41]) (n := 1) (nb := 1) rfl rfl]
  exact readBytes_writeBytes_same [] (bs := utf8Window [0x41] 1 1) (addr := 0)

/-- Control (i), UTF-8 record: `pre` is inhabited at a concrete staged state. -/
theorem utf8_pre_inhabited :
    Γ_utf8.pre [.ptr 3, .int 64 1, .int 32 (BitVec.ofNat 32 1)]
      utf8Mem 1 := by
  refine ⟨3, 1, BitVec.ofNat 32 1, true, ByteString.literal [0x41], 1, rfl, rfl,
    ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ByteString.length, ByteString.size_literal]
  · simp
  · simp
  · simp
  · simpa using utf8Mem_window
  · simp

/-! #### Control (ii): `pre` does not imply `post` -/

/-- Control (ii), mask record: the staged state `pre` admits, with the outcome
that wrote nothing.  The record's six output words at the slot it names are then
absent, so `post` refuses it. -/
theorem masks_post_not_implied :
    ∃ args mem next o,
      Γ_masks.pre args mem next ∧ ¬ Γ_masks.post args mem next o := by
  refine ⟨[.ptr 0, .ptr 64, .ptr 128], masksMem true false false, 1, .ret none [],
    masks_pre_inhabited, ?_⟩
  intro h
  obtain ⟨p, c, o, lo, hi, st, opened, ppar, -, -, -, -, hw1, -, -, -, -, -, -, -⟩ := h
  rw [readBytes_nil_succ] at hw1
  cases hw1

/-- Control (ii), POS8 record: `pre` admits the staged state, and `post` refuses
a void return. -/
theorem entry_pos8_post_not_implied :
    ∃ args mem next o,
      Γ_entry_pos8.pre args mem next ∧ ¬ Γ_entry_pos8.post args mem next o := by
  refine ⟨_, pos8Mem, 1, .ret none pos8Mem, entry_pos8_pre_inhabited, ?_⟩
  intro h
  exact h

/-- Control (ii), B8 record: `pre` admits the staged state, and `post` refuses a
void return. -/
theorem entry_b8_post_not_implied :
    ∃ args mem next o,
      Γ_entry_b8.pre args mem next ∧ ¬ Γ_entry_b8.post args mem next o := by
  refine ⟨_, [], 1, .ret none [], entry_b8_pre_inhabited, ?_⟩
  intro h
  exact h

/-- Control (ii), UTF-8 record: `pre` admits the staged state, and `post` refuses
a void return. -/
theorem utf8_post_not_implied :
    ∃ args mem next o,
      Γ_utf8.pre args mem next ∧ ¬ Γ_utf8.post args mem next o := by
  refine ⟨_, utf8Mem, 1, .ret none utf8Mem, utf8_pre_inhabited, ?_⟩
  intro h
  exact h

/-! #### The `ub` refusal, one per record -/

/-- The POS8 record refuses `ub`. -/
theorem entry_pos8_post_ub_false (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Γ_entry_pos8.post args mem next .ub := by
  intro h; exact h

/-- The B8 record refuses `ub`. -/
theorem entry_b8_post_ub_false (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Γ_entry_b8.post args mem next .ub := by
  intro h; exact h

/-- The UTF-8 record refuses `ub`. -/
theorem utf8_post_ub_false (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Γ_utf8.post args mem next .ub := by
  intro h; exact h

/-! #### The bridges: the refusal, the control, and the composition site -/

/-- A record that reads the value it is handed: `post` admits only returns that
carry `voidRet`.  It stands for the record `satisfies_calls_void` refuses rather
than guesses at: a boundary outcome's return carries `Option Value`, a call's
carries a `Value`, and only a value-irrelevant guarantee can cross that gap. -/
def Γ_readsValue : MemContract where
  budget := fun _ _ => 1
  pre := fun _ _ _ => True
  post := fun _ _ _ o =>
    match o with
    | .ub => False
    | .ret v _ => v = some voidRet

/-- The void bridge's hypothesis is not free: a record that reads the value fails
`ValueIrrelevant`, and `satisfies_calls_void` therefore does not attach to it. -/
theorem readsValue_not_valueIrrelevant : ¬ ValueIrrelevant Γ_readsValue := by
  intro h
  have hiff := h [] [] 0 none (some voidRet) []
  exact absurd (hiff.mpr rfl) (by intro h; cases h)

/-- The mask record presented with the caller's staging precondition: the
caller names the three slots it staged, which the record's own `pre` leaves
existential.  The `post` and the `budget` are the record's own. -/
def Γ_masksStaged (p c o : Nat) : MemContract where
  budget := Γ_masks.budget
  pre := fun args mem next => Γ_masks.pre args mem next ∧ args = [.ptr p, .ptr c, .ptr o]
  post := Γ_masks.post

/-- The staged record still ignores the returned value, because its `post` is the
mask record's: weakening a post does not preserve `ValueIrrelevant`, which is why
the composition site does not weaken it. -/
theorem masksStaged_valueIrrelevant (p c o : Nat) : ValueIrrelevant (Γ_masksStaged p c o) :=
  masks_valueIrrelevant

/-- **`Satisfies.mono`'s single site**: the mask call, where the caller presents
`Γ_masks` with its own staging precondition and leaves the post and the budget
unchanged.  The three hypotheses are `Nat.le_refl`, the staging implication, and
the identity on the post. -/
theorem masksStaged_satisfies (p c o : Nat) :
    Satisfies s1Calls s1MasksFunction (Γ_masksStaged p c o) :=
  Satisfies.mono masks_satisfies
    (fun _ _ => Nat.le_refl 1)
    (fun _ _ _ h => h.1)
    (fun _ _ _ _ h => h)

/-- The void bridge attaches at that site: the staged record is value-irrelevant
and the mask body returns nothing. -/
theorem masksStaged_calls :
    CallSatisfies (envForUnit masksSym (Γ_masksStaged 0 64 128) s1Calls s1MasksFunction)
      (Γ_masksStaged 0 64 128) masksSym :=
  satisfies_calls_void (masksStaged_satisfies 0 64 128) (masksStaged_valueIrrelevant 0 64 128)

/-! #### The composition law's other half: `hw` is not removable -/

/-- A record with the mask record's `budget` and `pre` whose `post` also pins the
caller's allocator.  Naming the allocator is exactly the mistake the relation's
shape removes: `next` is the caller's, so a guarantee about it is false wherever
the caller's base differs from the one the record names. -/
def Γ_masksMispost : MemContract where
  budget := Γ_masks.budget
  pre := Γ_masks.pre
  post := fun args mem next o => Γ_masks.post args mem next o ∧ next = 0

/-- **The witness.**  At the staged state the mask record admits, the unit's own
`post` holds at the completing outcome and the misnaming record's does not. -/
theorem masksMispost_witness :
    ∃ args mem next o,
      Γ_masks.post args mem next o ∧ ¬ Γ_masksMispost.post args mem next o := by
  obtain ⟨v, m, hrun⟩ :=
    (masks_satisfies [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1
      masks_pre_inhabited).1
  refine ⟨[.ptr 0, .ptr 64, .ptr 128], masksMem true false false, 1, .ret v m, ?_, ?_⟩
  · exact (masks_satisfies [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1
      masks_pre_inhabited).2 (.ret v m) (Or.inr ⟨1, hrun⟩)
  · intro hc
    exact absurd hc.2 (by simp)

/-- **The law's conclusion is not available without `hw`.**  The budget is equal
pointwise and the `pre` unchanged, so the law's other two hypotheses hold as
`Nat.le_refl` and the identity, and the conclusion still fails — while
`Satisfies s1Calls s1MasksFunction Γ_masks` holds.  The failure is therefore
attributable to the post, not to a smaller budget or a stronger pre. -/
theorem masksMispost_not_satisfies :
    ¬ Satisfies s1Calls s1MasksFunction Γ_masksMispost := by
  intro h
  obtain ⟨v, m, hrun⟩ :=
    (h [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1 masks_pre_inhabited).1
  have hpost := (h [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1
    masks_pre_inhabited).2 (.ret v m) (Or.inr ⟨1, hrun⟩)
  exact absurd hpost.2 (by simp)

/-- A selection that runs one unit body at a state whose memory is not the
caller's: the wrong-pointer staging.  It is `envForUnit` with `mem` replaced by
`d mem` at the body's entry state, and the record's budget is still read at the
caller's `(args, mem)`, so the only thing that moves is the memory the body sees. -/
def envForUnitAt (sym : String) (Γ : MemContract) (calls : Calls) (f : Function)
    (d : Mem → Mem) : Calls :=
  fun callee args mem next =>
    if callee = sym then
      match runFuel calls (Γ.budget args mem) f (EntryState f args (d mem) next) with
      | some (.ret (some v) m) => some { ret := v, mem := m, next := next + 0 }
      | some (.ret none m)     => some { ret := voidRet, mem := m, next := next + 0 }
      | _                      => none
    else none

/-- **The call-site control, at the mask symbol.**  A selection that hands the
mask body an empty memory — the wrong-pointer staging, where nothing of the
caller's block is present — answers `none`, so the bridge's conclusion is false
there: `CallSatisfies` requires the selection to resolve.  The symbol is the one
the mask record's own AST carries and the record is `Γ_masks`, so the control goes
through the void bridge rather than the value one; it fires because
`s1_masks_undefined_of_no_read` makes the absent block a `ub` run, which
`envForUnitAt`'s match maps to `none`. -/
theorem masks_shifted_calls_refused :
    ¬ CallSatisfies (envForUnitAt masksSym Γ_masks s1Calls s1MasksFunction (fun _ => []))
      Γ_masks masksSym := by
  intro h
  obtain ⟨r, hr, -, -⟩ :=
    h [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1 masks_pre_inhabited
  have hpc : (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1).pc = "entry" := rfl
  have hp : lookupName (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1).env "%p"
      = some (.ptr 0) := by
    simp only [EntryState, s1MasksFunction, List.map, List.zip, List.zipWith,
      lookupName, ite_true]
  have h64 : readBytes (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1).mem 0 64
      = none :=
    readBytes_nil_succ 0 63
  have hrun : runFuel s1Calls 1 s1MasksFunction
      (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1) = some .ub := by
    have h' := s1_masks_undefined_of_no_read
      (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1).env
      (EntryState s1MasksFunction [.ptr 0, .ptr 64, .ptr 128] [] 1)
      ⟨0, 64, 128, nulBlock32, nulBlock32, true, false, ⟨false, false⟩⟩ hpc hp h64
    simpa only [JsonS1MasksSteps.withEnv] using h'
  have hnone : envForUnitAt masksSym Γ_masks s1Calls s1MasksFunction (fun _ => [])
      masksSym [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) 1 = none := by
    unfold envForUnitAt
    rw [ite_eq_left rfl]
    rw [show Γ_masks.budget [.ptr 0, .ptr 64, .ptr 128] (masksMem true false false) = 1
      from rfl]
    rw [hrun]
  rw [hnone] at hr
  cases hr


/-! ### Axiom footprints

Every claim above is inside the tree's ceiling — `propext`, `Quot.sound`, and
`Classical.choice` where the unit's own headline theorem already carried it.  Each
footprint below was measured with `#print axioms` at the declaration it names, so a
proof that reaches a new carrier fails the build here rather than being found
later. -/

-- The relation's support and the extractor's decode.
/-- info: 'LeanLLVM.Refinement.ofNat_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofNat_toNat

/-- info: 'LeanLLVM.Refinement.wordsAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wordsAt_eq

-- The units allocate nothing, and their call environments ignore the base.
/-- info: 'LeanLLVM.Refinement.s1Masks_noAlloca' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s1Masks_noAlloca

/-- info: 'LeanLLVM.Refinement.entryPos8_noAlloca' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryPos8_noAlloca

/-- info: 'LeanLLVM.Refinement.entryB8_noAlloca' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryB8_noAlloca

/-- info: 'LeanLLVM.Refinement.utf8_noAlloca' depends on axioms: [propext] -/
#guard_msgs in
#print axioms utf8_noAlloca

/-- info: 'LeanLLVM.Refinement.s1Calls_nextIrr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms s1Calls_nextIrr

/-- info: 'LeanLLVM.Refinement.entryCalls_nextIrr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryCalls_nextIrr

/-- info: 'LeanLLVM.Refinement.utf8Calls_nextIrr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Calls_nextIrr

-- The next-independence lemmas, the bridge `Satisfies` needs to quantify `next`.
/-- info: 'LeanLLVM.Refinement.masks_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_next_independent

/-- info: 'LeanLLVM.Refinement.entry_pos8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_pos8_next_independent

/-- info: 'LeanLLVM.Refinement.entry_b8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_next_independent

/-- info: 'LeanLLVM.Refinement.utf8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8_next_independent

-- The mask record's value-irrelevance, its written extent and its refusal of `ub`.
/-- info: 'LeanLLVM.Refinement.masks_valueIrrelevant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_valueIrrelevant

/-- info: 'LeanLLVM.Refinement.masks_ub_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_ub_false

/-- info: 'LeanLLVM.Refinement.masks_written_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_written_extent

-- The four wrappers, which are what the records are for.
/-- info: 'LeanLLVM.Refinement.masks_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masks_satisfies

/-- info: 'LeanLLVM.Refinement.entry_pos8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_pos8_satisfies

/-- info: 'LeanLLVM.Refinement.entry_b8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_satisfies

/-- info: 'LeanLLVM.Refinement.utf8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms utf8_satisfies

-- The fixture: the reads that make each `pre` inhabited.
/-- info: 'LeanLLVM.Refinement.readBytes_nil_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms readBytes_nil_succ

/-- info: 'LeanLLVM.Refinement.masksMem_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksMem_full

/-- info: 'LeanLLVM.Refinement.masksMem_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksMem_block

/-- info: 'LeanLLVM.Refinement.masksMem_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksMem_carry

/-- info: 'LeanLLVM.Refinement.masks_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_pre_inhabited

/-- info: 'LeanLLVM.Refinement.pos8Mem_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pos8Mem_table

/-- info: 'LeanLLVM.Refinement.entry_pos8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_pos8_pre_inhabited

/-- info: 'LeanLLVM.Refinement.entry_b8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_pre_inhabited

/-- info: 'LeanLLVM.Refinement.utf8Mem_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Mem_window

/-- info: 'LeanLLVM.Refinement.utf8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8_pre_inhabited

-- Controls (ii) and the `ub` refusal.
/-- info: 'LeanLLVM.Refinement.masks_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_post_not_implied

/-- info: 'LeanLLVM.Refinement.entry_pos8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_pos8_post_not_implied

/-- info: 'LeanLLVM.Refinement.entry_b8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_post_not_implied

/-- info: 'LeanLLVM.Refinement.utf8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8_post_not_implied

/-- info: 'LeanLLVM.Refinement.entry_pos8_post_ub_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entry_pos8_post_ub_false

/-- info: 'LeanLLVM.Refinement.entry_b8_post_ub_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_post_ub_false

/-- info: 'LeanLLVM.Refinement.utf8_post_ub_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms utf8_post_ub_false

-- The bridges: the value-refusal, the composition site, and the call-site control.
/-- info: 'LeanLLVM.Refinement.readsValue_not_valueIrrelevant' does not depend on any axioms -/
#guard_msgs in
#print axioms readsValue_not_valueIrrelevant

/-- info: 'LeanLLVM.Refinement.masksStaged_valueIrrelevant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksStaged_valueIrrelevant

/-- info: 'LeanLLVM.Refinement.masksStaged_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masksStaged_satisfies

/-- info: 'LeanLLVM.Refinement.masksStaged_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masksStaged_calls

/-- info: 'LeanLLVM.Refinement.masks_shifted_calls_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masks_shifted_calls_refused

-- The composition law's other half: the refutation and its witness.
/-- info: 'LeanLLVM.Refinement.masksMispost_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masksMispost_witness

/-- info: 'LeanLLVM.Refinement.masksMispost_not_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksMispost_not_satisfies

end LeanLLVM.Refinement
