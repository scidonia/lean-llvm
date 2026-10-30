/-
The repository's concrete loop instance of the directed relation.

The left tree is the parsed comma-mask loop at the budget its correctness proof
uses; the right tree is the unrolled candidate.  The postcondition is
`Outcome.AgreesOutside (loopFrame x)`: the returned values are equal and the
memories agree outside the band the loop's own allocations cover.

This is one instance, not a general loop rule: the proof walks the loop's own
blocks and the candidate's single block, and installs nothing.
-/
import LeanLLVM.ITree.Simtt
import LeanLLVM.ITree.Bridge
import LeanLLVM.Vellum.CommaMaskLoop

namespace LeanLLVM.ITree

open LeanLLVM
open ITree
open LeanLLVM.Vellum
open LeanLLVM.Vellum.CommaMaskLoop
open LeanLLVM.Vellum.CommaMaskIR

/-- The loop's tree at the budget its proof uses. -/
def loopTree (x : BitVec 64) : ITree Ev Outcome :=
  runT noCalls 19 loopFunction (initState loopFunction [.int 64 x])

/-- The unrolled candidate's tree. -/
def candidateTree (x : BitVec 64) : ITree Ev Outcome :=
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
    SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
      (ITree.ret (Outcome.ret (some (.int 64 acc)) s.mem), s.mem) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hfind : loopFunction.findBlock s.pc = some doneBlock := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, doneBlock, doneInstrs,
      condBody, bodyBlock]
  rw [runT_succ, hfind]
  simp only [doneBlock, doneInstrs, codeT, instrT, evalOperand, hf.accPtr]
  refine SilentHead.step (SilentStep.load 1 (.int 64) _ s.mem (.int 64 acc)
    hf.accLoad (inFrame_one x)) ?_
  simp only [State.bind, termT, execTerm, evalOperand, lookup_bind_self]
  exact SilentHead.refl _ _

/-- The entry block: two in-frame zero stores, then the jump to `cond`,
silently. -/
theorem entry_silent (x : BitVec 64) (n : Nat) :
    SilentHead (loopFrame x)
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
  refine SilentHead.step (SilentStep.store 1 (.int 64) (.int 64 0) _ [] (inFrame_one x)) ?_
  refine SilentHead.step (SilentStep.store 9 (.int 64) (.int 64 0) _ _ (inFrame_nine x)) ?_
  refine SilentHead.step (SilentStep.tau _ _) ?_
  exact SilentHead.refl _ _

/-- One trip through the condition block, silently: the counter load, the
comparison, and the jump to `body`. -/
theorem cond_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64) (k : Nat)
    (hpos : 0 < fuel) (hk : k < 8) (hinv : LoopInv s m acc k) :
    ∃ s', loopFunction.findBlock s.pc = some condBody ∧ s'.pc = "body" ∧
      LoopFacts s' m acc k ∧
      lookupName s'.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
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
    refine SilentHead.step (SilentStep.load 9 (.int 64) _ s.mem (.int 64 (BitVec.ofNat 64 k))
      hf.iLoad (inFrame_nine x)) ?_
    simp only [instrT, pureInstrT, e2, termT, hterm]
    exact SilentHead.step (SilentStep.tau _ _) (SilentHead.refl _ _)

/-- One trip through the body block, silently: the lane arithmetic, the
accumulator load, the two in-frame stores, and the jump back to `cond`. -/
theorem body_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64) (k : Nat)
    (hpos : 0 < fuel) (hk : k < 8) (hacc : acc = maskPrefix m k) (hpc : s.pc = "body")
    (hf : LoopFacts s m acc k)
    (hi1 : lookupName s.env "%i1" = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ s', s'.pc = "cond" ∧ LoopFacts s' m (maskPrefix m (k + 1)) (k + 1) ∧
      SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
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
    refine SilentHead.step (SilentStep.load 1 (.int 64) _ s.mem (.int 64 acc)
      hf.accLoad (inFrame_one x)) ?_
    dsimp only [s5] at e6
    simp only [instrT, pureInstrT, e6, e7, e8, hl_a2, hl_acc8]
    refine SilentHead.step (SilentStep.store 1 (.int 64) (.int 64 a2v) _ _ (inFrame_one x)) ?_
    dsimp only [s9] at e10
    simp only [hstore1, instrT, pureInstrT, e10, hl_i2, hl_i10]
    refine SilentHead.step (SilentStep.store 9 (.int 64) (.int 64 i2v) _ _ (inFrame_nine x)) ?_
    dsimp only [s11] at hterm
    simp only [hstore2, termT, hterm]
    exact SilentHead.step (SilentStep.tau _ _) (SilentHead.refl _ _)

/-- The condition block at counter eight, silently: the branch to `done`. -/
theorem cond_done_silent (x : BitVec 64) (fuel : Nat) (s : State) (m acc : BitVec 64)
    (hpos : 0 < fuel) (hinv : LoopInv s m acc 8) :
    ∃ s', s'.pc = "done" ∧ LoopFacts s' m acc 8 ∧
      SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
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
    refine SilentHead.step (SilentStep.load 9 (.int 64) _ s.mem (.int 64 (BitVec.ofNat 64 8))
      hf.iLoad (inFrame_nine x)) ?_
    simp only [instrT, pureInstrT, e2, termT, hterm]
    exact SilentHead.step (SilentStep.tau _ _) (SilentHead.refl _ _)

/-- Straight-line code with no memory events is its continuation at the code's
final state. -/
def NoEvents : Instr → Bool
  | .load _ _ _ => false
  | .store _ _ _ => false
  | .call _ _ _ _ => false
  | _ => true

theorem codeT_eq_of_noEvents (calls : Calls) :
    ∀ (is : List Instr) (s : State) (k : State → ITree Ev Outcome) (s' : State),
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

/-- The loop's own induction, at the tree level: from the condition with `n`
remaining iterations, finitely many silent steps reach the full prefix and a
memory confined to the loop's band.  The fuel is a parameter so the three
closures in each step compose with syntactically equal middle trees. -/
theorem cond_run_silent (x : BitVec 64) :
    ∀ (n : Nat) (s : State) (m acc : BitVec 64) (k : Nat) (fuel : Nat),
      k ≤ 8 → 8 - k = n → fuel = 2 * n + 2 → acc = maskPrefix m k → LoopInv s m acc k →
      ∃ mem, MemConfined 1 17 mem ∧
        SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
          (ITree.ret (Outcome.ret (some (.int 64 (maskPrefix m 8))) mem), mem) := by
  intro n
  induction n with
  | zero =>
      intro s m acc k fuel hk hn hfuel hacc hinv
      have hk8 : k = 8 := by omega
      subst hk8
      let r1 := cond_done_silent x fuel s m acc (by omega) hinv
      let s1 := r1.choose
      have h1 := r1.choose_spec
      have hp1 : s1.pc = "done" := h1.1
      have hf1 : LoopFacts s1 m acc 8 := h1.2.1
      have hs1 : SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
          (runT noCalls (fuel - 1) loopFunction s1, s1.mem) := h1.2.2
      have hs2 := done_silent x (fuel - 1) s1 m acc (by omega) hp1 hf1
      refine ⟨s1.mem, ?_, ?_⟩
      · simpa [hf1.nextEq] using hf1.memBand
      · have := SilentHead.trans hs1 hs2
        rw [hacc] at this
        exact this
  | succ n ih =>
      intro s m acc k fuel hk hn hfuel hacc hinv
      have hk8 : k < 8 := by omega
      let r1 := cond_silent x fuel s m acc k (by omega) hk8 hinv
      let s1 := r1.choose
      have h1 := r1.choose_spec
      have hp1 : s1.pc = "body" := h1.2.1
      have hf1 : LoopFacts s1 m acc k := h1.2.2.1
      have hi1 : lookupName s1.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) := h1.2.2.2.1
      have hs1 : SilentHead (loopFrame x) (runT noCalls fuel loopFunction s, s.mem)
          (runT noCalls (fuel - 1) loopFunction s1, s1.mem) := h1.2.2.2.2
      let r2 := body_silent x (fuel - 1) s1 m acc k (by omega) hk8 hacc hp1 hf1 hi1
      let s2 := r2.choose
      have h2 := r2.choose_spec
      have hp2 : s2.pc = "cond" := h2.1
      have hf2 : LoopFacts s2 m (maskPrefix m (k + 1)) (k + 1) := h2.2.1
      have hs2 : SilentHead (loopFrame x)
          (runT noCalls (fuel - 1) loopFunction s1, s1.mem)
          (runT noCalls ((fuel - 1) - 1) loopFunction s2, s2.mem) := h2.2.2
      have hn' : 8 - (k + 1) = n := by omega
      have hfuel' : (fuel - 1) - 1 = 2 * n + 2 := by omega
      let r3 := ih s2 m (maskPrefix m (k + 1)) (k + 1) ((fuel - 1) - 1) (by omega) hn'
        hfuel' rfl ⟨hp2, hf2⟩
      let mem := r3.choose
      have h3 := r3.choose_spec
      have hconf : MemConfined 1 17 mem := h3.1
      have hrest : SilentHead (loopFrame x)
          (runT noCalls ((fuel - 1) - 1) loopFunction s2, s2.mem)
          (ITree.ret (Outcome.ret (some (.int 64 (maskPrefix m 8))) mem), mem) := h3.2
      refine ⟨mem, hconf, ?_⟩
      have := SilentHead.trans hs1 (SilentHead.trans hs2 hrest)
      simpa [show 2 * (n + 1) + 2 = 2 * n + 4 from by omega] using this

/-- The loop's tree reaches its return silently, with a memory private to the
band the loop's own allocations cover. -/
theorem loopTree_silent (x : BitVec 64) :
    ∃ mem, MemPrivate (loopFrame x) mem ∧
      SilentHead (loopFrame x) (loopTree x, ([] : Mem))
        (ITree.ret (Outcome.ret (some (.int 64 (spec x))) mem), mem) := by
  obtain ⟨mem, hconf, hrest⟩ := cond_run_silent x 8 (entryState x)
    (x ^^^ c 3182967604875373612) 0 0 18 (by decide) (by decide) (by decide)
    (maskPrefix_zero _).symm (entry_inv x)
  refine ⟨mem, ?_, ?_⟩
  · rw [loopFrame_eq]
    exact hconf
  · have hspec : maskPrefix (x ^^^ c 3182967604875373612) 8 = spec x := by
      rw [maskPrefix_eight, c_comma, ← spec_eq_maskFold]
    have e1 : (runT noCalls (18 + 1) loopFunction (initState loopFunction [.int 64 x]),
          (initState loopFunction [.int 64 x]).mem) =
        (runT noCalls 19 loopFunction (initState loopFunction [.int 64 x]),
          (initState loopFunction [.int 64 x]).mem) := rfl
    have hentry : SilentHead (loopFrame x)
        (runT noCalls 19 loopFunction (initState loopFunction [.int 64 x]),
          (initState loopFunction [.int 64 x]).mem)
        (runT noCalls 18 loopFunction (entryState x), (entryState x).mem) := e1 ▸ entry_silent x 18
    have hrest' : SilentHead (loopFrame x)
        (runT noCalls 18 loopFunction (entryState x), (entryState x).mem)
        (ITree.ret (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8))) mem),
          mem) := hrest
    have := SilentHead.trans hentry hrest'
    rw [hspec] at this
    simpa [loopTree, initState, show 18 + 1 = 19 from by omega] using this

/-- The candidate's tree is already a returned outcome: its single block has no
memory events. -/
theorem candidateTree_silent (x : BitVec 64) :
    SilentHead (loopFrame x) (candidateTree x, ([] : Mem))
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
  exact SilentHead.refl _ _

/-- The loop, as left target, is simulated by the unrolled candidate, as right
source, at the framed postcondition. -/
theorem loop_candidate_simtt (x : BitVec 64) :
    simtt (loopFrame x) (Outcome.AgreesOutside (loopFrame x))
      (loopTree x, ([] : Mem)) (candidateTree x, ([] : Mem)) := by
  obtain ⟨mem, hpriv, hleft⟩ := loopTree_silent x
  refine (simtt_iff _ _ _ _).mpr ?_
  refine SimttF.ret hleft (candidateTree_silent x) ?_
  · refine ⟨?_, ?_⟩
    · rw [byteLoop_eq_spec]
    · simpa using AgreesOutsideMem.of_private hpriv (MemPrivate.nil (fun _ => False))

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
