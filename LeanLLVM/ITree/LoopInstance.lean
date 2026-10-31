/-
The repository's concrete instances of the directed relation.

The first is a genuinely recurring tree: a step that visibly emits the same call
and returns a recursive seed at every response, related to itself through
`simtt_loop`'s continuation position.  The second is the comma-mask fixture.  Its
left tree is the parsed loop at the budget its correctness proof uses; its right
tree is the unrolled candidate.  The postcondition is
`Outcome.AgreesOutside (loopFrame x)`: the returned values are equal and the
memories agree outside the band the loop's own allocations cover.

Both are instances of the general rule in `LoopRule`, not rules of their own.
The loop's seed family carries the condition invariant, the budget arithmetic
and the strictly decreasing measure the rule's return obligation is discharged
with, and the proof installs nothing.
-/
import LeanLLVM.ITree.LoopRule
import LeanLLVM.ITree.Bridge
import LeanLLVM.Vellum.CommaMaskLoop

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open LeanLLVM.Vellum
open LeanLLVM.Vellum.CommaMaskLoop
open LeanLLVM.Vellum.CommaMaskIR

/-- The loop's tree at the budget its proof uses. -/
def loopTree (x : BitVec 64) : ITree.Tree Ev Outcome :=
  runT noCalls 19 loopFunction (initState loopFunction [.int 64 x])

/-- The unrolled candidate's tree. -/
def candidateTree (x : BitVec 64) : ITree.Tree Ev Outcome :=
  runT noCalls 10000 candidateFunction (initState candidateFunction [.int 64 x])

theorem loop_init_mem (x : BitVec 64) :
    (initState loopFunction [.int 64 x]).mem = [] := rfl

/-- The band's first local, throughout its eight bytes. -/
theorem inFrame_one (x : BitVec 64) : InFrame (loopFrame x) 1 (.int 64) := by
  intro k hk
  rw [loopFrame_eq]
  simp only [Ty.sizeBytes] at hk
  exact ⟨by omega, by omega⟩

/-- The band's second local, throughout its eight bytes. -/
theorem inFrame_nine (x : BitVec 64) : InFrame (loopFrame x) 9 (.int 64) := by
  intro k hk
  rw [loopFrame_eq]
  simp only [Ty.sizeBytes] at hk
  exact ⟨by omega, by omega⟩

/-- The exit block: one in-frame load, then the return, silently. -/
theorem done_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64)
    (hpos : 0 < fuel) (hpc : s.pc = "done") (hf : LoopFacts s m acc 8) :
    RawSilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
      (ITree.ret (Outcome.ret (some (.int 64 acc)) s.mem), s.mem) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hfind : loopFunction.findBlock s.pc = some doneBlock := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, doneBlock, doneInstrs,
      condBody, bodyBlock]
  rw [runT_succ, hfind]
  simp only [doneBlock, doneInstrs, codeT, instrT, evalOperand, hf.accPtr]
  refine RawSilentHead.step (RawSilentStep.load 1 (.int 64) _ s.mem (.int 64 acc)
    hf.accLoad (inFrame_one x)) ?_
  simp only [State.bind, termT, execTerm, evalOperand, lookup_bind_self]
  exact RawSilentHead.refl _ _

/-- The entry block: two in-frame zero stores, then the jump to `cond`,
silently. -/
theorem entry_silent (x : BitVec 64) (n : Nat) :
    RawSilentHead (loopFrame x)
      (runT noCalls (n + 1) loopFunction (initState loopFunction [.int 64 x]),
        (initState loopFunction [.int 64 x]).mem)
      (runT noCalls n loopFunction (entryState x), (entryState x).mem) := by
  have hpc : (initState loopFunction [.int 64 x]).pc = "entry" := rfl
  have hfind : loopFunction.findBlock "entry" =
      some { name := "entry", instrs := entryInstrs, term := .br "cond" } := by
    simp [loopFunction, Function.findBlock, findBlockList]
  rw [runT_succ, hpc, hfind]
  simp only [entryInstrs, codeT]
  simp [instrT, pureInstrT, evalInstr, evalOperand, evalBinopNat, evalBinop, Value.intToNat,
    Const.toValue, State.bind, lookupName, storeValue, termT, execTerm, Ty.sizeBytes,
    entryState, initState, List.map, List.zip, List.zipWith, loopFunction, Function.entry?,
    List.head?, Option.getD, c]
  refine RawSilentHead.step (RawSilentStep.store 1 (.int 64) (.int 64 0) _ [] (inFrame_one x)) ?_
  refine RawSilentHead.step (RawSilentStep.store 9 (.int 64) (.int 64 0) _ _ (inFrame_nine x)) ?_
  refine RawSilentHead.step (RawSilentStep.step _ _) ?_
  exact RawSilentHead.refl _ _

/-- One trip through the condition block, silently: the counter load, the
comparison, and the jump to `body`. -/
theorem cond_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64) (k : Nat)
    (hpos : 0 < fuel) (hk : k < 8) (hinv : LoopInv s m acc k) :
    ∃ s', loopFunction.findBlock s.pc = some condBody ∧ s'.pc = "body" ∧
      LoopFacts s' m acc k ∧
      lookupName s'.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      RawSilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
        (runT noCalls (fuel - 1) loopFunction s', s'.mem) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  obtain ⟨hpc, hf⟩ := hinv
  let s1 : State := s.bind "%i1" (.int 64 (BitVec.ofNat 64 k))
  let s2 : State :=
    s1.bind "%c" (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 k).ult (8 : BitVec 64))))
  let s3 : State := { s2 with pc := "body" }
  have hli1 : lookupName s1.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) :=
    lookup_bind_self s "%i1" _
  have hlc : lookupName s2.env "%c" =
      some (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 k).ult (8 : BitVec 64)))) :=
    lookup_bind_self s1 "%c" _
  have e1 : evalInstr noCalls s (.load "%i1" (.int 64) (.reg "%i")) = some s1 := by
    have h := eval_load_64 noCalls s "%i1" (.reg "%i") 9 (BitVec.ofNat 64 k)
      hf.iPtr hf.iLoad
    simpa [s1] using h
  have e2 : evalInstr noCalls (s.bind "%i1" (.int 64 (BitVec.ofNat 64 k)))
      (.icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 (8 : BitVec 64)))) = some s2 := by
    have h := evalInstr_icmp_ult_imm noCalls s1 "%c" "%i1" (8 : BitVec 64)
    simp only [hli1] at h
    simpa [s2] using h
  have hfind : loopFunction.findBlock s.pc = some condBody := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, condBody, condInstrs]
  have hterm : execTerm s2 (.condbr (.reg "%c") "body" "done") = .jump s3 := by
    simp only [execTerm, evalOperand, hlc, ofBool_ult k hk, s3]
    rfl
  refine ⟨s3, hfind, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp [s3, s2, s1, State.bind, hf.accLoad]
    · simp [s3, s2, s1, State.bind, hf.iLoad]
    · simp [s3, s2, s1, State.bind, hf.nextEq]
    · simpa [s3, s2, s1, State.bind] using hf.memBand
  · simp [s3, s2, s1, State.bind, lookupName]
  · rw [runT_succ, hfind]
    simp only [condBody, condInstrs, codeT, instrT, evalOperand, hf.iPtr]
    refine RawSilentHead.step (RawSilentStep.load 9 (.int 64) _ s.mem (.int 64 (BitVec.ofNat 64 k))
      hf.iLoad (inFrame_nine x)) ?_
    simp only [instrT, pureInstrT, e2, termT, hterm]
    exact RawSilentHead.step (RawSilentStep.step _ _) (RawSilentHead.refl _ _)

/-- One trip through the body block, silently: the lane arithmetic, the
accumulator load, the two in-frame stores, and the jump back to `cond`. -/
theorem body_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64) (k : Nat)
    (hpos : 0 < fuel) (hk : k < 8) (hacc : acc = maskPrefix m k) (hpc : s.pc = "body")
    (hf : LoopFacts s m acc k)
    (hi1 : lookupName s.env "%i1" = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ s', s'.pc = "cond" ∧ LoopFacts s' m (maskPrefix m (k + 1)) (k + 1) ∧
      RawSilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
        (runT noCalls (fuel - 1) loopFunction s', s'.mem) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  let shv : BitVec 64 := BitVec.ofNat 64 k * (8 : BitVec 64)
  let bv : BitVec 64 := m >>> shv.toNat
  let b2v : BitVec 64 := bv &&& (255 : BitVec 64)
  let zv : BitVec 1 := BitVec.ofBool (b2v = (0 : BitVec 64))
  let bitv : BitVec 64 := (128 : BitVec 64) <<< shv.toNat
  let a1v : BitVec 64 := acc ||| bitv
  let a2v : BitVec 64 := if zv = 1 then a1v else acc
  let s1 : State := s.bind "%sh" (.int 64 shv)
  let s2 : State := s1.bind "%b" (.int 64 bv)
  let s3 : State := s2.bind "%b2" (.int 64 b2v)
  let s4 : State := s3.bind "%z" (.int 1 zv)
  let s5 : State := s4.bind "%a0" (.int 64 acc)
  let s6 : State := s5.bind "%bit" (.int 64 bitv)
  let s7 : State := s6.bind "%a1" (.int 64 a1v)
  let s8 : State := s7.bind "%a2" (.int 64 a2v)
  have hstore1 : storeValue s8 (.int 64) (.int 64 a2v) 1 =
      some { s8 with mem := writeBytes s8.mem 1 (natToBytes a2v.toNat 8) } :=
    (loadValue_storeValue_64 s8 a2v 1).1
  let s9 : State := { s8 with mem := writeBytes s8.mem 1 (natToBytes a2v.toNat 8) }
  let i2v : BitVec 64 := BitVec.ofNat 64 k + (1 : BitVec 64)
  let s10 : State := s9.bind "%i2" (.int 64 i2v)
  have hstore2 : storeValue s10 (.int 64) (.int 64 i2v) 9 =
      some { s10 with mem := writeBytes s10.mem 9 (natToBytes i2v.toNat 8) } :=
    (loadValue_storeValue_64 s10 i2v 9).1
  let s11 : State := { s10 with mem := writeBytes s10.mem 9 (natToBytes i2v.toNat 8) }
  let s12 : State := { s11 with pc := "cond" }
  have e1 : evalInstr noCalls s (.binop "%sh" .mul 64 (.reg "%i1") (.imm (.int 64 8))) = some s1 := by
    have h := evalInstr_mul_imm noCalls s "%sh" "%i1" (8 : BitVec 64)
    simp only [hi1] at h
    simpa [s1, shv] using h
  have hl1 : lookupName s1.env "%m" = some (.int 64 m) := by
    simp [s1, State.bind, lookupName, hf.mReg]
  have hl2 : lookupName s1.env "%sh" = some (.int 64 shv) := by
    simp [s1, State.bind, shv]
  have e2 : evalInstr noCalls s1 (.binop "%b" .lshr 64 (.reg "%m") (.reg "%sh")) = some s2 := by
    have h := evalInstr_lshr_reg noCalls s1 "%b" "%m" "%sh"
    simp only [hl1, hl2] at h
    simpa [s2, bv] using h
  have hl3 : lookupName s2.env "%b" = some (.int 64 bv) := by
    simp [s2, State.bind, bv]
  have e3 : evalInstr noCalls s2 (.binop "%b2" .and 64 (.reg "%b") (.imm (.int 64 255))) = some s3 := by
    have h := evalInstr_and_imm noCalls s2 "%b2" "%b" (255 : BitVec 64)
    simp only [hl3] at h
    simpa [s3, b2v] using h
  have hl4 : lookupName s3.env "%b2" = some (.int 64 b2v) := by
    simp [s3, State.bind, b2v]
  have e4 : evalInstr noCalls s3 (.icmp "%z" .eq 64 (.reg "%b2") (.imm (.int 64 0))) = some s4 := by
    have h := evalInstr_icmp_eq_imm noCalls s3 "%z" "%b2" (0 : BitVec 64)
    simp only [hl4] at h
    simpa [s4, zv] using h
  have hl_acc4 : lookupName s4.env "%acc" = some (.ptr 1) := by
    simp [s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
  have e6 : evalInstr noCalls s5 (.binop "%bit" .shl 64 (.imm (.int 64 128)) (.reg "%sh")) = some s6 := by
    have hl_sh2 : lookupName s5.env "%sh" = some (.int 64 shv) := by
      simp [s5, s4, s3, s2, s1, State.bind, lookupName, shv]
    have h := evalInstr_shl_imm_reg noCalls s5 "%bit" "%sh" (128 : BitVec 64)
    simp only [hl_sh2] at h
    simpa [s6, bitv] using h
  have hl_a0 : lookupName s6.env "%a0" = some (.int 64 acc) := by
    simp [s6, s5, s4, s3, s2, s1, State.bind, lookupName]
  have hl_bit : lookupName s6.env "%bit" = some (.int 64 bitv) := by
    simp [s6, State.bind, bitv]
  have e7 : evalInstr noCalls s6 (.binop "%a1" .or 64 (.reg "%a0") (.reg "%bit")) = some s7 := by
    have h := evalInstr_or_reg noCalls s6 "%a1" "%a0" "%bit"
    simp only [hl_a0, hl_bit] at h
    simpa [s7, a1v] using h
  have hl_z : lookupName s7.env "%z" = some (.int 1 zv) := by
    simp [s7, s6, s5, s4, State.bind, lookupName, zv]
  have hl_a1 : lookupName s7.env "%a1" = some (.int 64 a1v) := by
    simp [s7, State.bind, a1v]
  have hl_a0b : lookupName s7.env "%a0" = some (.int 64 acc) := by
    simp [s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName]
  have e8 : evalInstr noCalls s7 (.select "%a2" (.int 64) (.reg "%z") (.reg "%a1") (.reg "%a0")) = some s8 := by
    have h := evalInstr_select_reg noCalls s7 "%a2" "%z" "%a1" "%a0"
    simp only [hl_z, hl_a1, hl_a0b] at h
    simp only [ite_int] at h
    simpa [s8, a2v] using h
  have hl_a2 : lookupName s8.env "%a2" = some (.int 64 a2v) := by
    simp [s8, State.bind, a2v]
  have hl_acc8 : lookupName s8.env "%acc" = some (.ptr 1) := by
    simp [s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
  have hl_i1_9 : lookupName s9.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hi1]
  have e10 : evalInstr noCalls s9 (.binop "%i2" .add 64 (.reg "%i1") (.imm (.int 64 1))) = some s10 := by
    have h := evalInstr_add_imm noCalls s9 "%i2" "%i1" (1 : BitVec 64)
    simp only [hl_i1_9] at h
    simpa [s10, i2v] using h
  have hl_i2 : lookupName s10.env "%i2" = some (.int 64 i2v) := by
    simp [s10, State.bind, i2v]
  have hl_i10 : lookupName s10.env "%i" = some (.ptr 9) := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.iPtr]
  have hfind : loopFunction.findBlock s.pc = some bodyBlock := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, bodyBlock, bodyInstrs, condBody]
  have hterm : execTerm s11 (.br "cond") = .jump s12 := rfl
  refine ⟨s12, rfl, ?_, ?_⟩
  · have hsh : shv.toNat = 8 * k := by
      simp only [shv]
      rw [ofNat_mul_eight_lit k hk, ofNat_eight_mul_toNat k hk]
    have hbit : bitv = (0x80 : BitVec 64) <<< (8 * k) := by
      simp only [bitv, hsh]
    have hz : (zv = 1) ↔ isZeroByte m k := by
      simp only [zv, ofBool_eq_one]
      simp only [b2v, bv, hsh, isZeroByte]
    have ha2 : a2v = maskPrefix m (k + 1) := by
      simp only [a2v, a1v, hacc]
      rw [maskPrefix_succ]
      by_cases hp : isZeroByte m k
      · rw [ite_eq_left (hz.mpr hp), ite_eq_left hp, hbit]
      · rw [ite_eq_right (fun h => hp (hz.mp h)), ite_eq_right hp]
        simp
    have hi2 : i2v = BitVec.ofNat 64 (k + 1) := by
      simp only [i2v]
      rw [ofNat_add_one_lit k hk]
    have hbelow : loadValue
        (writeBytes (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) 9 (natToBytes i2v.toNat 8))
        (.int 64) 1 =
        loadValue (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) (.int 64) 1 :=
      loadValue_writeBytes_below (writeBytes s.mem 1 (natToBytes a2v.toNat 8))
        (natToBytes i2v.toNat 8) 64 1 9 (by decide)
    have hrt1 : loadValue (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) (.int 64) 1 =
        some (.int 64 a2v) :=
      (loadValue_storeValue_64 s a2v 1).2
    have hrt2 : loadValue
        (writeBytes (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) 9 (natToBytes i2v.toNat 8))
        (.int 64) 9 = some (.int 64 i2v) :=
      (loadValue_storeValue_64
        { s with mem := writeBytes s.mem 1 (natToBytes a2v.toNat 8) } i2v 9).2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind]
      rw [hbelow, hrt1, ha2]
    · simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind]
      rw [hrt2, hi2]
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, hf.nextEq]
    · have h1 : MemConfined 1 s.next
          (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) :=
        MemConfined.writeBytes hf.memBand (by simp [natToBytes_length, hf.nextEq])
          (by omega)
      have h2 : MemConfined 1 s.next
          (writeBytes (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) 9
            (natToBytes i2v.toNat 8)) :=
        MemConfined.writeBytes h1 (by simp [natToBytes_length, hf.nextEq]) (by omega)
      simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind]
      exact h2
  · rw [runT_succ, hfind]
    simp only [bodyBlock, bodyInstrs, codeT, instrT, evalOperand, pureInstrT,
      e1, e2, e3, e4, hl_acc4]
    refine RawSilentHead.step (RawSilentStep.load 1 (.int 64) _ s.mem (.int 64 acc)
      hf.accLoad (inFrame_one x)) ?_
    dsimp only [s5] at e6
    simp only [instrT, pureInstrT, e6, e7, e8, hl_a2, hl_acc8]
    refine RawSilentHead.step (RawSilentStep.store 1 (.int 64) (.int 64 a2v) _ _ (inFrame_one x)) ?_
    dsimp only [s9] at e10
    simp only [hstore1, instrT, pureInstrT, e10, hl_i2, hl_i10]
    refine RawSilentHead.step (RawSilentStep.store 9 (.int 64) (.int 64 i2v) _ _ (inFrame_nine x)) ?_
    dsimp only [s11] at hterm
    simp only [hstore2, termT, hterm]
    exact RawSilentHead.step (RawSilentStep.step _ _) (RawSilentHead.refl _ _)

/-- The condition block at counter eight, silently: the branch to `done`. -/
theorem cond_done_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64)
    (hpos : 0 < fuel) (hinv : LoopInv s m acc 8) :
    ∃ s', s'.pc = "done" ∧ LoopFacts s' m acc 8 ∧
      RawSilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
        (runT noCalls (fuel - 1) loopFunction s', s'.mem) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  obtain ⟨hpc, hf⟩ := hinv
  let s1 : State := s.bind "%i1" (.int 64 (BitVec.ofNat 64 8))
  let s2 : State :=
    s1.bind "%c" (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 8).ult (8 : BitVec 64))))
  let s3 : State := { s2 with pc := "done" }
  have hli1 : lookupName s1.env "%i1" = some (.int 64 (BitVec.ofNat 64 8)) :=
    lookup_bind_self s "%i1" _
  have hlc : lookupName s2.env "%c" =
      some (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 8).ult (8 : BitVec 64)))) :=
    lookup_bind_self s1 "%c" _
  have e1 : evalInstr noCalls s (.load "%i1" (.int 64) (.reg "%i")) = some s1 := by
    have h := eval_load_64 noCalls s "%i1" (.reg "%i") 9 (BitVec.ofNat 64 8)
      hf.iPtr hf.iLoad
    simpa [s1] using h
  have e2 : evalInstr noCalls (s.bind "%i1" (.int 64 (BitVec.ofNat 64 8)))
      (.icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 (8 : BitVec 64)))) = some s2 := by
    have h := evalInstr_icmp_ult_imm noCalls s1 "%c" "%i1" (8 : BitVec 64)
    simp only [hli1] at h
    simpa [s1, s2] using h
  have hfind : loopFunction.findBlock s.pc = some condBody := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, condBody, condInstrs]
  have hterm : execTerm s2 (.condbr (.reg "%c") "body" "done") = .jump s3 := by
    simp only [execTerm, evalOperand, hlc, ofBool_ult_eight, s3]
    rfl
  refine ⟨s3, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp [s3, s2, s1, State.bind, hf.accLoad]
    · simp [s3, s2, s1, State.bind, hf.iLoad]
    · simp [s3, s2, s1, State.bind, hf.nextEq]
    · simpa [s3, s2, s1, State.bind] using hf.memBand
  · rw [runT_succ, hfind]
    simp only [condBody, condInstrs, codeT, instrT, evalOperand, hf.iPtr]
    refine RawSilentHead.step (RawSilentStep.load 9 (.int 64) _ s.mem (.int 64 (BitVec.ofNat 64 8))
      hf.iLoad (inFrame_nine x)) ?_
    simp only [instrT, pureInstrT, e2, termT, hterm]
    exact RawSilentHead.step (RawSilentStep.step _ _) (RawSilentHead.refl _ _)

/-- Straight-line code with no memory events is its continuation at the code's
final state. -/
def NoEvents : Instr → Bool
  | .load _ _ _ => false
  | .store _ _ _ => false
  | .call _ _ _ _ => false
  | _ => true

theorem codeT_eq_of_noEvents (calls : Calls) :
    ∀ (is : List Instr) (s : State) (k : State → ITree.Tree Ev Outcome) (s' : State),
      is.all NoEvents = true → denoteCode calls is s = some s' → codeT calls is s k = k s'
  | [], s, k, s', _, h => by
      simp only [denoteCode, Option.some.injEq] at h
      subst h
      rfl
  | i :: is, s, k, s', hne, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hne
      obtain ⟨hi, his⟩ := hne
      simp only [denoteCode] at h
      split at h
      · cases h
      · rename_i s1 heq
        have hih := codeT_eq_of_noEvents calls is s1 k s' his h
        cases i with
        | load d ty p => simp [NoEvents] at hi
        | store ty v p => simp [NoEvents] at hi
        | call d rt c args => simp [NoEvents] at hi
        | binop d op w a b =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | icmp d p w a b =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | select d ty c a b =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | trunc d wi wo v =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | zext d wi wo v =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | sext d wi wo v =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih
        | alloca d ty al =>
            simpa only [codeT, instrT, pureInstrT, heq] using hih

/-! ### The loop's seed family

The condition invariant is indexed by a seed: the seed's budget is the one the
loop actually has left, its counter is at most eight, its accumulator is the lane
prefix of the symbolic memory, and that memory is the run's own.  The entry seed
stands apart only because its budget is the run's, one entry block before the
condition's.  The general rule's invariant and the measure derivation below are
both stated over this family.
-/

/-- A seed of the loop's tree family. -/
structure LoopSeed where
  /-- The budget the seed's tree is built at. -/
  fuel : Nat
  /-- The machine state the seed's tree starts from. -/
  st : State
  /-- The symbolic memory the loop's `%m` register holds. -/
  m : BitVec 64
  /-- The accumulator the loop's `%acc` local holds. -/
  acc : BitVec 64
  /-- The loop's counter. -/
  k : Nat

namespace LoopSeed

/-- The seed's raw source tree, paired with the memory its state records. -/
def toRaw (p : LoopSeed) : RawTS :=
  (runT noCalls p.fuel loopFunction p.st, p.st.mem)

/-- The seed's handled tree. -/
noncomputable def tree (x : BitVec 64) (p : LoopSeed) : OTree :=
  handle (loopFrame x) p.st.mem (runT noCalls p.fuel loopFunction p.st)

/-- A condition seed: at `cond`, with the loop invariant and a counter of at most
eight; the budget is exactly the two block steps each remaining iteration costs;
the accumulator is the lane prefix of the symbolic memory, and that memory is the
run's own. -/
def atCond (x : BitVec 64) (p : LoopSeed) : Prop :=
  LoopInv p.st p.m p.acc p.k ∧ p.k ≤ 8 ∧ p.fuel = 2 * (8 - p.k) + 2 ∧
    p.acc = maskPrefix p.m p.k ∧ p.m = x ^^^ c 3182967604875373612

/-- The run's entry seed: its own initial state at its own budget. -/
def isEntry (x : BitVec 64) (p : LoopSeed) : Prop :=
  p.fuel = 19 ∧ p.st = initState loopFunction [.int 64 x]

/-- The two kinds of seed the loop's tree family starts from. -/
def inv (x : BitVec 64) (p : LoopSeed) : Prop := p.isEntry x ∨ p.atCond x

end LoopSeed

/-- The condition seed the entry block hands over to: no lanes folded yet, at
the budget the eight iterations cost. -/
def entryCondSeed (x : BitVec 64) : LoopSeed :=
  { fuel := 18, st := entryState x, m := x ^^^ c 3182967604875373612, acc := 0, k := 0 }

/-- The entry block's hand-over satisfies the condition invariant. -/
theorem entryCondSeed_atCond (x : BitVec 64) : (entryCondSeed x).atCond x := by
  have hk : (entryCondSeed x).k = 0 := rfl
  have hfuel : (entryCondSeed x).fuel = 18 := rfl
  have hacc : (entryCondSeed x).acc = 0 := rfl
  refine ⟨entry_inv x, ?_, ?_, ?_, rfl⟩
  · rw [hk]; decide
  · rw [hfuel, hk]
  · rw [hacc, hk]
    exact (maskPrefix_zero _).symm

/-- A memory confined to the loop's band is private to the loop's footprint. -/
theorem memPrivate_of_confined {x : BitVec 64} {mem : Mem}
    (h : MemConfined 1 17 mem) : MemPrivate (loopFrame x) mem := by
  rw [loopFrame_eq]
  exact h

/-- Every condition seed reaches the loop's return through finitely many private
steps: the returned value is the whole lane prefix of the run's symbolic memory,
and the memory the return records is confined to the loop's band.  One iteration
— the condition block, then the body block — supplies each step of the strictly
decreasing measure `8 - k`, and the exit block supplies the terminal. -/
theorem cond_run_silent (x : BitVec 64) (p : LoopSeed) (hinv : p.atCond x) :
    ∃ mem, MemConfined 1 17 mem ∧
      RawSilentHead (loopFrame x) p.toRaw
        (ITree.ret
          (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)))
            mem), mem) := by
  let P : RawTS → Prop := fun terminal =>
    ∃ v, terminal.1 = ITree.ret (Outcome.ret v terminal.2) ∧
      v = some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)) ∧
        MemConfined 1 17 terminal.2
  have hmain : ∃ terminal, P terminal ∧
      RawSilentHead (loopFrame x) p.toRaw terminal := by
    refine rawSilentHead_of_measure LoopSeed.toRaw (fun q => q.atCond x)
      (fun q => 8 - q.k) P ?_ ?_ hinv
    · -- one iteration: the condition block, then the body block
      intro q hq hpos
      have hk8 : q.k < 8 := by omega
      have hle : q.k ≤ 8 := hq.2.1
      have hfuelEq : q.fuel = 2 * (8 - q.k) + 2 := hq.2.2.1
      have haccEq : q.acc = maskPrefix q.m q.k := hq.2.2.2.1
      have hmEq : q.m = x ^^^ c 3182967604875373612 := hq.2.2.2.2
      have hinvC : LoopInv q.st q.m q.acc q.k := hq.1
      have hfuel : 0 < q.fuel := by omega
      obtain ⟨s1, _, hpc1, hf1, hi1, hs1⟩ :=
        cond_silent x q.fuel q.st q.m q.acc q.k hfuel hk8 hinvC
      obtain ⟨s2, hpc2, hf2, hs2⟩ :=
        body_silent x (q.fuel - 1) s1 q.m q.acc q.k (by omega) hk8 haccEq hpc1 hf1 hi1
      have hk1 : q.k + 1 ≤ 8 := by omega
      have hfuel' : (q.fuel - 1) - 1 = 2 * (8 - (q.k + 1)) + 2 := by omega
      refine ⟨⟨(q.fuel - 1) - 1, s2, q.m, maskPrefix q.m (q.k + 1), q.k + 1⟩,
        ?_, ?_, ?_⟩
      · exact ⟨⟨hpc2, hf2⟩, hk1, hfuel', rfl, hmEq⟩
      · show 8 - (q.k + 1) < 8 - q.k
        omega
      · exact hs1.trans hs2
    · -- the exit: the condition block at eight, then the done block
      intro q hq hzero
      have hle : q.k ≤ 8 := hq.2.1
      have hk8 : q.k = 8 := by omega
      have hfuelEq : q.fuel = 2 * (8 - q.k) + 2 := hq.2.2.1
      have haccEq : q.acc = maskPrefix q.m q.k := hq.2.2.2.1
      have hmEq : q.m = x ^^^ c 3182967604875373612 := hq.2.2.2.2
      have hfuel : 0 < q.fuel := by omega
      have hinv8 : LoopInv q.st q.m q.acc 8 := hk8 ▸ hq.1
      have hacc8 : q.acc = maskPrefix (x ^^^ c 3182967604875373612) 8 := by
        rw [haccEq, hk8, hmEq]
      obtain ⟨s1, hpc1, hf1, hs1⟩ := cond_done_silent x q.fuel q.st q.m q.acc hfuel hinv8
      have hs2 := done_silent x (q.fuel - 1) s1 q.m q.acc (by omega) hpc1 hf1
      refine ⟨(ITree.ret (Outcome.ret (some (.int 64 q.acc)) s1.mem), s1.mem),
        ⟨some (.int 64 q.acc), rfl, by rw [hacc8], ?_⟩, hs1.trans hs2⟩
      simpa [hf1.nextEq] using hf1.memBand
  obtain ⟨⟨t, mem⟩, ⟨v, ht, hv, hconf⟩, hhead⟩ := hmain
  have ht' : t = ITree.ret (Outcome.ret v mem) := ht
  have hv' : v = some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)) := hv
  have hpair : (t, mem) =
      (ITree.ret
        (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)))
          mem), mem) := by
    rw [ht', hv']
  exact ⟨mem, hconf, hpair ▸ hhead⟩

/-- The loop's tree reaches its return silently, with a memory private to the
band the loop's own allocations cover. -/
theorem loopTree_silent (x : BitVec 64) :
    ∃ mem, MemPrivate (loopFrame x) mem ∧
      RawSilentHead (loopFrame x) (loopTree x, ([] : Mem))
        (ITree.ret (Outcome.ret (some (.int 64 (spec x))) mem), mem) := by
  obtain ⟨mem, hconf, hrest⟩ :=
    cond_run_silent x (entryCondSeed x) (entryCondSeed_atCond x)
  refine ⟨mem, memPrivate_of_confined hconf, ?_⟩
  have hspec : maskPrefix (x ^^^ c 3182967604875373612) 8 = spec x := by
    rw [maskPrefix_eight, c_comma, ← spec_eq_maskFold]
  have hentry : RawSilentHead (loopFrame x)
      (runT noCalls 19 loopFunction (initState loopFunction [.int 64 x]),
        (initState loopFunction [.int 64 x]).mem)
      (runT noCalls 18 loopFunction (entryState x), (entryState x).mem) := by
    have e1 : (runT noCalls (18 + 1) loopFunction (initState loopFunction [.int 64 x]),
        (initState loopFunction [.int 64 x]).mem) =
        (runT noCalls 19 loopFunction (initState loopFunction [.int 64 x]),
          (initState loopFunction [.int 64 x]).mem) := rfl
    exact e1 ▸ entry_silent x 18
  have hrest' : RawSilentHead (loopFrame x)
      (runT noCalls 18 loopFunction (entryState x), (entryState x).mem)
      (ITree.ret (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8))) mem),
        mem) := hrest
  have := RawSilentHead.trans hentry hrest'
  rw [hspec] at this
  simpa [loopTree, initState] using this

/-- The candidate's tree is already a returned outcome: its single block has no
memory events. -/
theorem candidateTree_silent (x : BitVec 64) :
    RawSilentHead (loopFrame x) (candidateTree x, ([] : Mem))
      (ITree.ret (Outcome.ret (some (.int 64 (byteLoop x))) []), ([] : Mem)) := by
  rw [candidateTree]
  have hpc : (initState candidateFunction [.int 64 x]).pc = "bb" := rfl
  have hfind : candidateFunction.findBlock "bb" = some candidateBody := by
    simp [candidateFunction, candidateBody, Function.findBlock, findBlockList]
  rw [runT_succ, hpc, hfind]
  dsimp only [candidateBody]
  have hne : candidateInstrs.all NoEvents = true := by decide
  have hblock := candidate_block noCalls (initState candidateFunction [.int 64 x]) x
    (lookupName_initState_candidate x)
  rw [codeT_eq_of_noEvents noCalls candidateInstrs _ _ _ hne hblock]
  simp only [candidateBody, termT, execTerm, evalOperand, lookupName_candidateRun,
    candA7_eq_byteLoop, candidateRun_mem, candidate_initState_mem]
  exact RawSilentHead.refl _ _

/-- The candidate's handled tree at its fixed budget: the source side of the
fixed-budget instance. -/
noncomputable def candidateHandled (x : BitVec 64) : OTree :=
  runHandled noCalls (loopFrame x) 10000 candidateFunction
    (initState candidateFunction [.int 64 x])

/-- The candidate's handled tree reaches its return silently. -/
theorem candidateTree_head (x : BitVec 64) :
    TauHead (candidateHandled x)
      (ITree.ret (Outcome.ret (some (.int 64 (byteLoop x))) [])) := by
  refine tauHead_of_silentHead ?_
  have h := RawSilentHead.handle (candidateTree_silent x)
  simpa only [candidateHandled, runHandled, candidateTree, initState, handle_ret,
    finishOutcome] using h

/-- The loop's handled entry tree reaches the loop's return silently, with a
memory private to the loop's band. -/
theorem loopTree_head (x : BitVec 64) :
    ∃ mem, MemPrivate (loopFrame x) mem ∧
      TauHead (handle (loopFrame x) [] (loopTree x))
        (ITree.ret (Outcome.ret (some (.int 64 (spec x))) mem)) := by
  obtain ⟨mem, hpriv, hraw⟩ := loopTree_silent x
  refine ⟨mem, hpriv, tauHead_of_silentHead ?_⟩
  simpa only [handle_ret, finishOutcome] using RawSilentHead.handle hraw

/-- Every seed the loop's family starts from reaches the loop's return silently,
at the value the candidate produces. -/
theorem loopSeed_head (x : BitVec 64) (p : LoopSeed) (hinv : LoopSeed.inv x p) :
    ∃ mem, MemPrivate (loopFrame x) mem ∧
      TauHead (LoopSeed.tree x p)
        (ITree.ret (Outcome.ret (some (.int 64 (spec x))) mem)) := by
  rcases hinv with ⟨hfuel, hst⟩ | hcond
  · obtain ⟨mem, hpriv, hhead⟩ := loopTree_head x
    have htree : LoopSeed.tree x p = handle (loopFrame x) [] (loopTree x) := by
      simp only [LoopSeed.tree, hfuel, hst, loopTree, initState]
    exact ⟨mem, hpriv, htree ▸ hhead⟩
  · -- a condition seed: the measure derivation, then the handler transport
    obtain ⟨mem, hconf, hraw⟩ := cond_run_silent x p hcond
    have hspec : maskPrefix (x ^^^ c 3182967604875373612) 8 = spec x := by
      rw [maskPrefix_eight, c_comma, ← spec_eq_maskFold]
    have hhead : TauHead (LoopSeed.tree x p)
        (ITree.ret
          (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)))
            mem)) := by
      refine tauHead_of_silentHead ?_
      simpa only [LoopSeed.tree, LoopSeed.toRaw, handle_ret, finishOutcome]
        using RawSilentHead.handle hraw
    exact ⟨mem, memPrivate_of_confined hconf, hspec ▸ hhead⟩

/-! ### The first instance: a recurring visible call

`tickStep` visibly emits the same call and returns a recursive seed at every
response, so the tree it builds has a genuine recursive backedge behind a visible
event rather than a zero-iteration `.done`.  The rule's continuation position is
what closes that backedge, and the internal `.recur` guard says the backedge is a
positive finite delay of the next iteration. -/

/-- A step that visibly emits `call "tick" []` and recurs at every response. -/
def tickStep (_ : Unit) : ITree.Tree ObsEv (IterState Unit Outcome) :=
  vis (ObsEv.call "tick" []) (fun _ => ret (.recur ()))

/-- The tick loop shows its call after one silent step, and continues with the
step's iteration continuation. -/
theorem tickStep_head :
    TauHead (mfix tickStep ())
      (vis (ObsEv.call "tick" []) (fun _ => bindStep tickStep (ret (.recur ())))) :=
  ⟨TauClosure.later (TauClosure.now _),
    TauClosure.finite_later (TauClosure.finite_now _), by
    simp only [TauClosure.flatten_later, TauClosure.flatten_now, mfix_unfold, tickStep,
      bindStep_vis]⟩

/-- The continuation after the visible event is the next iteration: the internal
`.recur` guard is the positive delay of that backedge, flattened to the
continuation itself. -/
theorem tickStep_cont :
    TauHead (bindStep tickStep (ret (.recur ()))) (mfix tickStep ()) :=
  ⟨TauClosure.now (mfix tickStep ()), TauClosure.finite_now _, by
    rw [TauClosure.flatten_now, mfix_unfold, bindStep_ret_recur]⟩

/-- The general rule's first instantiation: a visibly recurring tree is simulated
by itself at the rule's framed `True` postcondition. -/
theorem tick_loop_simtt (frame : Nat → Prop) :
    simtt (fun oT oS => True ∧ oT.AgreesOutside frame oS)
      (mfix tickStep ()) (mfix tickStep ()) := by
  refine simtt_loop frame (fun _ _ => True) (fun _ : Unit => mfix tickStep ())
    (fun _ : Unit => mfix tickStep ()) (fun _ _ => True) ?_ () () trivial
  intro s t _
  cases s
  cases t
  exact TauSimttF.vis_call "tick" [] _ _ tickStep_head tickStep_head
    (fun _ => ⟨(), (), trivial, tickStep_cont, tickStep_cont⟩)

/-! ### The second instance: the fixed 19/10000 pair

The rule is applied at the loop's seed family against the candidate's single
tree.  Every seed's return obligation is the loop's own finite derivation, and the
rule's framed return relation is weakened back to the original postcondition, so
the public statement below is unchanged. -/

/-- The rule applied at the loop's seed family: the run's entry seed against the
candidate's 10000-step tree, at the rule's framed `True` postcondition. -/
theorem loop_seed_simtt (x : BitVec 64) :
    simtt (fun oT oS => True ∧ oT.AgreesOutside (loopFrame x) oS)
      (runHandled noCalls (loopFrame x) 19 loopFunction (initState loopFunction [.int 64 x]))
      (candidateHandled x) := by
  have hstep : ∀ (p : LoopSeed) (_ : Unit), LoopSeed.inv x p →
      TauSimttF (fun oT oS => True ∧ oT.AgreesOutside (loopFrame x) oS)
        (fun a b => ∃ (s' : LoopSeed) (t' : Unit), LoopSeed.inv x s' ∧
          TauHead a (LoopSeed.tree x s') ∧ TauHead b (candidateHandled x))
        (LoopSeed.tree x p) (candidateHandled x) := by
    intro p _ hinv
    obtain ⟨mem, hpriv, hleft⟩ := loopSeed_head x p hinv
    refine TauSimttF.ret_ret hleft (candidateTree_head x) ⟨trivial, ?_⟩
    exact ⟨by rw [byteLoop_eq_spec],
      by simpa using AgreesOutsideMem.of_private hpriv (MemPrivate.nil (fun _ => False))⟩
  have hentry : LoopSeed.inv x ⟨19, initState loopFunction [.int 64 x],
      x ^^^ c 3182967604875373612, 0, 0⟩ := Or.inl ⟨rfl, rfl⟩
  have hres := simtt_loop (loopFrame x) (fun _ _ => True) (LoopSeed.tree x)
    (fun _ => candidateHandled x) (fun p _ => LoopSeed.inv x p) hstep
    ⟨19, initState loopFunction [.int 64 x], x ^^^ c 3182967604875373612, 0, 0⟩ ()
    hentry
  simpa only [LoopSeed.tree, runHandled] using hres

/-- The loop, as left target, is simulated by the unrolled candidate, as right
source, at the framed postcondition. -/
theorem loop_candidate_simtt (x : BitVec 64) :
    simtt (Outcome.AgreesOutside (loopFrame x))
      (runHandled noCalls (loopFrame x) 19 loopFunction (initState loopFunction [.int 64 x]))
      (runHandled noCalls (loopFrame x) 10000 candidateFunction
        (initState candidateFunction [.int 64 x])) := by
  simpa only [candidateHandled] using
    simtt_post_mono (fun _ _ h => h.2) (loop_seed_simtt x)

/-- A memory that differs at address zero is outside the frame, so the framed
relation rejects it. -/
theorem address_zero_rejected (x : BitVec 64) :
    ¬ AgreesOutsideMem [(0, 1)] ([] : Mem) (loopFrame x) := by
  intro h
  have h0 : ¬ loopFrame x 0 := by
    simp only [loopFrame_eq, Band]
    omega
  have := h 0 h0
  simp [readByte] at this

/-- The same rejection, stated of returned outcomes: the postcondition does not
hold of a return whose memory differs at address zero. -/
theorem outcome_address_zero_rejected (x : BitVec 64) (v : Option Value) :
    ¬ (Outcome.ret v [(0, 1)]).AgreesOutside (loopFrame x) (Outcome.ret v []) := by
  intro h
  exact address_zero_rejected x h.2

/-- Every observable behaviour of the parsed loop on an `i64` argument is
matched by the unrolled candidate's behaviour, through the tree relation at the
loop's own budgets: the run's outcome is pinned by budget determinism, the
fixed 19/10000 tree relation transports it, and the postcondition hands back a
candidate behaviour agreeing outside the loop's band. -/
theorem loop_candidate_beh_bridge (x : BitVec 64) (o : Outcome)
    (ho : Beh noCalls loopFunction [.int 64 x] o) :
    ∃ o', Beh noCalls candidateFunction [.int 64 x] o' ∧
      o.AgreesOutside (loopFrame x) o' := by
  obtain ⟨mem, _, h19⟩ := loop_run_fuel x
  have ho' : o = Outcome.ret (some (.int 64 (spec x))) mem := by
    rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact absurd (runFuel_outcome_unique hn h19) (by intro h; nomatch h)
    · exact runFuel_outcome_unique hn h19
  subst ho'
  rcases simtt_runFuel_some noCalls (loopFrame x) (Outcome.AgreesOutside (loopFrame x))
      loopFunction candidateFunction [.int 64 x] 19 10000
      (Outcome.ret (some (.int 64 (spec x))) mem) (loop_candidate_simtt x) h19 with
    hub | ⟨vT, vS, memT, memS, hEq, hrS, hpost⟩
  · exact ⟨_, Or.inl ⟨10000, hub⟩, Outcome.agreesOutside_refl _ (loopFrame x)⟩
  · exact ⟨Outcome.ret vS memS, Or.inr ⟨10000, hrS⟩, by rw [hEq]; exact hpost⟩
