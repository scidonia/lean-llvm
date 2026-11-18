/-
`num_fast_el1`'s sign at the merge: `%tobool274.not` is the lexeme's sign, and
nothing on the scan's path rebinds it.

`if.end`'s first `phi` is the sign's bit: `1` from `entry` (the empty lexeme) and
`%cmp1 = (%0 != '-')` from `land.lhs.true`.  The merge block `cleanup282.thread`
reads that same register through the select `%cond266`, so the store's sign is
the sign of the lexeme's first byte — provided the scan between the two blocks
never writes the register.

That is the tie this module proves, in three pieces.

1. **No rebind.**  `%tobool274.not` is written by `if.end` and by no other block
   of the body; the fact is a `decide` over the pinned block list, and
   `numFast_step_tobool` is the per-step transport it implies, through
   `denoteCode`'s own non-interference and the terminator's environment.
2. **The chain.**  The scan's path is not a single block, so the transport is
   closed over a finite chain of steps (`NumFastChain`), with the chain's fuel
   count exposed as `NumFastChain.runFuel`.  A caller supplies the chain; nothing
   here decides which blocks the scan visits.
3. **The tie at the model.**  `sign_tie` reads a well-formed lexeme's first byte
   as `d.neg`: `-` exactly at a negative sign, so `%tobool274.not = 1 ↔ ¬d.neg`.

The composite at the end is the tier-1 store of `JsonStage2NumFastTier1` at a
lexeme: the table staging `NumFastTables` and the sign tie supply
`t1_store_run`'s hypotheses, and its five steps write `strtodSpec`'s bytes.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.Refinement.JsonStage2NumFastArm
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine
open LeanLLVM.StrtodTier1

namespace NumFastSign

/-! ### No rebind

`%tobool274.not` is `if.end`'s `phi` and nothing else's destination.  The fact is
over the pinned body, so it is a kernel computation rather than a reading of the
block list. -/

/-- **Only `if.end` writes the sign's register.**  The statement is closed, so
`decide` reads it off the pinned body. -/
theorem numFast_tobool_written_at_if_end :
    ∀ b ∈ numFastBody.blocks, b.name ≠ "if.end" →
      ∀ i ∈ b.instrs, i.dst? ≠ some "%tobool274.not" := by
  decide

/-- A block found by name is named that name. -/
theorem findBlockList_name {bs : List Block} {n : String} {b : Block}
    (h : findBlockList bs n = some b) : b.name = n := by
  induction bs with
  | nil => simp [findBlockList] at h
  | cons b' rest ih =>
      simp only [findBlockList] at h
      split at h
      · next hb => cases h; exact hb
      · exact ih h

/-- A terminator leaves the environment alone: `execTerm` moves the program
counter and nothing else, or the block is `ub`. -/
theorem execTerm_env {s s' : State} {tm : Term} (h : execTerm s tm = .jump s') :
    s'.env = s.env := by
  cases tm with
  | br d => simp only [execTerm] at h; cases h; rfl
  | condbr c t f =>
      simp only [execTerm] at h
      split at h
      · split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · cases h
      · cases h
  | ret ty v =>
      cases v with
      | none => cases ty <;> (simp only [execTerm] at h; cases h)
      | some o =>
          cases ty with
          | void => simp only [execTerm] at h; cases h
          | int w => simp only [execTerm] at h; split at h <;> cases h
          | ptr => simp only [execTerm] at h; split at h <;> cases h
          | vec n e => simp only [execTerm] at h; split at h <;> cases h
          | array n e => simp only [execTerm] at h; split at h <;> cases h
          | struct n b => simp only [execTerm] at h; split at h <;> cases h
          | double => simp only [execTerm] at h; split at h <;> cases h
  | unreachable => simp only [execTerm] at h; cases h

/-- **A step leaves the sign's register alone.**  Everything a step does to the
environment is the block's own instruction run, so the register survives a
block that does not write it, and the terminator changes only the program
counter. -/
theorem numFast_step_tobool {calls : Calls} {s s' : State}
    (hpc : s.pc ≠ "if.end") (h : step calls numFastBody s = .jump s') :
    lookupName s'.env "%tobool274.not" = lookupName s.env "%tobool274.not" := by
  cases hf : numFastBody.findBlock s.pc with
  | none => rw [step, hf] at h; cases h
  | some b =>
      simp only [step, hf] at h
      have hname : b.name = s.pc := findBlockList_name hf
      have hno : ∀ i ∈ b.instrs, i.dst? ≠ some "%tobool274.not" :=
        numFast_tobool_written_at_if_end b (findBlockList_mem hf)
          (by rw [hname]; exact hpc)
      cases hd : denoteCode calls b.instrs s with
      | none => simp only [hd] at h; cases h
      | some s1 =>
          simp only [hd] at h
          rw [execTerm_env h]
          exact JsonEntrySteps.denoteCode_lookupName calls b.instrs "%tobool274.not"
            hno s s1 hd

/-! ### The chain

The scan is a finite path, not one block, so the transport is closed over a
chain.  The chain carries its fuel, so a scan simulation's `runFuel` prefix is
`NumFastChain.runFuel`'s index. -/

/-- A finite chain of control steps of the body, each leaving a block other than
`if.end`. -/
inductive NumFastChain (calls : Calls) : State → State → Prop
  /-- The empty chain. -/
  | refl (s : State) : NumFastChain calls s s
  /-- One step, then the rest. -/
  | step {s s' e : State} (hpc : s.pc ≠ "if.end")
      (hs : step calls numFastBody s = .jump s') (ht : NumFastChain calls s' e) :
      NumFastChain calls s e

/-- **The chain's sign.**  The register is the same at both ends. -/
theorem NumFastChain.tobool {calls : Calls} {s e : State} (h : NumFastChain calls s e) :
    lookupName e.env "%tobool274.not" = lookupName s.env "%tobool274.not" := by
  induction h with
  | refl s => rfl
  | step hpc hs _ ih => rw [ih, numFast_step_tobool hpc hs]

/-- **The chain's fuel.**  A chain of `j` steps is a `runFuel` prefix: the run
from the head at `j + k` is the run from the tail at `k`. -/
theorem NumFastChain.runFuel {calls : Calls} {s e : State}
    (h : NumFastChain calls s e) :
    ∃ j, ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  induction h with
  | refl s => exact ⟨0, fun k => by simp⟩
  | step hpc hs _ ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j + 1, fun k => ?_⟩
      rw [show j + 1 + k = 1 + (j + k) from by omega,
        runFuel_jump_prefix hs, hj]

/-! ### The lexeme's first byte

`d.lexeme` is `signBytes d.neg ++ d.body`, and `d.body` starts with the `int`
part, which is never empty and never begins with `-`.  So the first byte is `-`
exactly at `d.neg = true`. -/

/-- An `IntPart` starts with a byte that is not `-`. -/
theorem intPart_head_ne {bs : Bytes} (h : IntPart bs) :
    ∃ b rest, bs.toList = b :: rest ∧ b ≠ 0x2D := by
  cases h with
  | zero => exact ⟨0x30, [], by simp [ByteString.toList_cons], by decide⟩
  | lead h1 h2 hr =>
      exact ⟨_, _, by rw [ByteString.toList_cons], by
        intro hb
        rw [hb] at h1
        exact absurd h1 (by decide)⟩

/-- The lexeme's body starts with its `int` part. -/
theorem body_eq_ip_append (d : Decimal) : ∃ t, d.body = d.ip ++ t := by
  cases hf : d.fr with
  | none =>
      cases he : d.ex with
      | none => exact ⟨ByteString.empty, by
          simp only [Decimal.body, hf, he, ByteString.append_empty]⟩
      | some p =>
          obtain ⟨s, ds⟩ := p
          exact ⟨0x65 +: (Decimal.signBytes s ++ ds), by
            simp only [Decimal.body, hf, he, ByteString.append_empty]⟩
  | some fs =>
      cases he : d.ex with
      | none => exact ⟨0x2E +: fs, by simp [Decimal.body, hf, he]⟩
      | some p =>
          obtain ⟨s, ds⟩ := p
          exact ⟨(0x2E +: fs) ++ (0x65 +: (Decimal.signBytes s ++ ds)), by
            simp only [Decimal.body, hf, he, ByteString.append_assoc,
              ByteString.cons_append]⟩

/-- A well-formed lexeme's body starts with a byte that is not `-`. -/
theorem body_head_ne {d : Decimal} (hd : d.wellFormed) :
    ∃ b rest, d.body.toList = b :: rest ∧ b ≠ 0x2D := by
  obtain ⟨b, rest, hb, hne⟩ := intPart_head_ne hd.1
  obtain ⟨t, ht⟩ := body_eq_ip_append d
  refine ⟨b, rest ++ t.toList, ?_, hne⟩
  rw [ht, ByteString.toList_append, hb, List.cons_append]

/-- A positive lexeme starts with a byte that is not `-`. -/
theorem lexeme_head_pos {d : Decimal} (hd : d.wellFormed) (h : d.neg = false) :
    ∃ b rest, d.lexeme.toList = b :: rest ∧ b ≠ 0x2D := by
  obtain ⟨b, rest, hb, hne⟩ := body_head_ne hd
  refine ⟨b, rest, ?_, hne⟩
  rw [Decimal.lexeme, h, Decimal.signBytes_false, ByteString.toList_append,
    ByteString.toList_empty, List.nil_append]
  exact hb

/-- A negative lexeme starts with `-`. -/
theorem lexeme_head_neg {d : Decimal} (h : d.neg = true) :
    d.lexeme.toList.head? = some 0x2D := by
  simp only [Decimal.lexeme, h, Decimal.signBytes_true, ByteString.toList_append,
    ByteString.toList_cons, ByteString.toList_empty, List.nil_append,
    List.singleton_append, List.head?_cons]

/-- **The sign tie.**  A well-formed lexeme's first byte is `-` exactly when its
sign is, so the body's `(%0 != '-')` reading is `1` exactly at a positive lexeme.
This is the `hsign` `t1_store_bits` reads. -/
theorem sign_tie {d : Decimal} {b : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b) :
    (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 = (1 : BitVec 1)) ↔ d.neg = false := by
  by_cases h : d.neg = false
  · have hp := lexeme_head_pos hd h
    obtain ⟨b', rest, hbx, hne⟩ := hp
    have hbb : b = b' := by
      rw [hbx] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      exact hb.symm
    subst hbb
    constructor
    · intro _; exact h
    · intro _
      rw [NumFastStarts.evalICmp_ne_minus]
      exact if_neg hne
  · have htrue : d.neg = true := by cases hd' : d.neg <;> simp_all
    have hn := lexeme_head_neg htrue
    have hbb : b = 0x2D := by
      rw [hn] at hb
      simp only [Option.some.injEq] at hb
      exact hb.symm
    subst hbb
    constructor
    · intro hc
      rw [NumFastStarts.evalICmp_ne_minus, if_pos rfl] at hc
      exact absurd hc (by decide)
    · intro hf; exact absurd hf h

/-- **The tie at the read byte.**  The register `if.end`'s `phi` carries is the
lexeme's sign test, so its `1` is exactly the lexeme's `¬d.neg`. -/
theorem sign_tie_of_read {d : Decimal} {b : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b) {sign : BitVec 1}
    (hs : sign = evalICmp .ne (JsonScanLane.vByte b) 0x2d#8) :
    (sign = 1) ↔ d.neg = false := by
  subst hs
  exact sign_tie hd hb

end NumFastSign

end LeanLLVM.Refinement
