/-
The no-event walk's scalar class, first segment: the whitespace skip.

`JsonStage2NoEventWalkClose` ends the `scalar` entry's `cond.end` extent test at
`land.lhs.true` (taken) and `if.end457` (not taken), carrying `%cond` and
`%idxprom.lcssa`.  This module takes the taken arm
(`probes/install/ir/stage2-noevent.candidate.ll:912-985`): the probe
`%gep1069 = getelementptr i8, %invariant.gep1068, i64 %cond`, the three-leaf
whitespace test on the byte it loads, the skip loop over `%b`, and then
`if.end457`'s eight-way merge, its `store i64 %inc.lcssa, ptr %k219` and the
number-or-minus guard `%or.cond901`, stopping at `if.then471`'s and
`if.else495`'s entries.  The two arms below those blocks are the next segments'
and are not modelled here.

**The class.**  The body classifies a byte with three leaf tests behind two
`icmp slt i8` pivots: a byte signed below 13 is on the `add i8 -9` /
`icmp ule i8 1` leaf (which admits 9 and 10), a byte signed at or above 13 and
below 32 is on the `icmp eq 13` leaf, and anything else is on the `icmp eq 32`
leaf.  `stage2SkipLeaf` is that control flow, so the branch proofs read it by
unfolding; `stage2SkipWs` names the four bytes it selects, and
`stage2SkipLeaf_eq_ws`/`stage2SkipWs_iff` are the two readings — the operational
one the arms consume, and the four-byte set the segment's statement reports.
Both equivalence proofs are kernel `decide` over `Fin 256`, not a per-byte case
analysis.

**The loop, and its polarity.**  The skip loop is `land.rhs` (the `%ee.01053`
`phi`, the `%b` `gep`, the byte load) and its test `NodeBlock62`, then
`while.body`'s increment and `%exitcond1170.not`.  Each pinned leaf takes its
true arm to `if.end457` and its false arm to `while.body`, so the loop advances
over non-members and leaves on the first member at or before the bound.  The
`LoopFuel.BoundLoop` instance `stage2SkipLoop` has head `NodeBlock62` — the first
block at which the cursor and the byte it loaded are both bound — bound `%cond`,
and exit test `stage2SkipAtBound`: the loaded byte is a class member, or the
increment has reached `%cond`.  The measure is the distance
`%cond - %ee.01053`, carried as the invariant's budget (`stage2SkipInvAt`); the
invariant also carries the non-membership of every position the loop has passed,
so the exit word, `stage2SkipExit`, states that the loop stopped at the first
member at or before `%cond` (or exhausted at the bound), with the merge's `%ee.1`
selection at that same position and the walk's invariant at the merge.  The
head's two three-way pivot splits (`stage2SkipAdvance`'s non-member to
`while.body`, `stage2SkipStop`'s member straight to the merge) and the increment
block's two one-link tails (`stage2SkipWhileBodyExit` at the bound,
`stage2SkipWhileBodyContinue` back to the head) are the rows the instance
consumes; `stage2SkipLoop_run` is the induction's run and its memory is the
entry state's.

**Hypotheses at the entry, and conclusions.**  The entry is `land.lhs.true`'s
state as `link_condEnd_true` delivers it, so the values it reads are hypotheses:
`%cond` (a `Nat` reading below `2 ^ 63`, so the `gep`'s sign extension is the
identity), `%invariant.gep1068` (the entry block's `%b - 1`, as an abstract
pointer `g`), `%idxprom.lcssa`, `%inc.lcssa`, `%.lcssa`, `%b`, `%k219` (the entry
block's `%c + 32`), and the byte the probe reads at
`%invariant.gep1068 + %cond`.  `%ep` and `%nep` are read by `scalar`'s own
`%cmp436` test before `cond.end` and are not read here, so they are not
hypotheses of this segment.  The conclusions are the control path, the position
the merge's `%ee.1` `phi` selects, the `%k219` write, and the guard's value: the
segment reaches `if.then471`'s or `if.else495`'s entry according to
`%or.cond901`.

**The store's frame.**  `%k219` is inside the cursor record `%c`
(`stage2NoEventCursorExtent = 1192`), so the write is inside the run's own
regions and `Stage2NoEventWalkInv.stack_write` transports the invariant;
`stage2SkipStoreRegion` turns `k219 = K.c + 32` and `k219 + 8 ≤ K.c + 1192`
into the per-byte `inRegions` fact the store needs.  Nothing here writes the
document, the entry stream, the scratch buffer or the four output words, and
every block before the store keeps the state's memory.

**What this module proves, and what it does not.**  It proves the class and its
four-byte characterization, the fifteen block pins, the fifteen block
denotations, the twenty-eight one-step links with their fuel compositions, the
`%k219` store's region fact, the loop's invariant and exit word with the
invariant's transport across cells and its budget's monotonicity, the merge's
invariant with its two constructors, the head's two block paths (`stage2SkipAdvance`/`stage2SkipStop`),
the increment block's two tails, the `LoopFuel.BoundLoop` instance
`stage2SkipLoop` and its run `stage2SkipLoop_run`, the merge's one-step run
`stage2SkipJoinRun`, the entry test `stage2SkipFirstTest`, and the composed
segment `stage2NoEventWalkScalarSkip` from `land.lhs.true` to
`if.then471`/`if.else495`.  The two arms below the merge's entries —
`if.then471`'s number path (`num_fast_el1`, the `%off` store, the
`od_gap_recover` call) and `if.else495`'s literal path — are not modelled here;
nor is the `cond.true` extent arm that produces `%cond` from a lane word, nor
the entry block's `%invariant.gep1068 = %b - 1`, nor `if.end545`'s reading below
the merge.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The whitespace class -/

/-- The skip loop's class test, read as the body decides it: signed below 13 is
the `add -9`/`ule 1` leaf, signed below 32 the `eq 13` leaf, else `eq 32`. -/
def stage2SkipLeaf (v : BitVec 8) : Bool :=
  if v.slt (BitVec.ofNat 8 13) then
    (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1)
  else if v.slt (BitVec.ofNat 8 32) then
    v == BitVec.ofNat 8 13
  else
    v == BitVec.ofNat 8 32

/-- The class the three leaves select: HT, LF, CR and space. -/
def stage2SkipWs (v : BitVec 8) : Bool :=
  v == BitVec.ofNat 8 9 || v == BitVec.ofNat 8 10 ||
    v == BitVec.ofNat 8 13 || v == BitVec.ofNat 8 32

/-- The two readings of the class agree at every byte. -/
theorem stage2SkipLeaf_eq_ws_fin (i : Fin 256) :
    stage2SkipLeaf (BitVec.ofNat 8 i.val) = stage2SkipWs (BitVec.ofNat 8 i.val) := by
  revert i
  decide

/-- The two readings of the class agree at every byte. -/
theorem stage2SkipLeaf_eq_ws (v : BitVec 8) : stage2SkipLeaf v = stage2SkipWs v := by
  have h := stage2SkipLeaf_eq_ws_fin ⟨v.toNat, v.isLt⟩
  have hv : BitVec.ofNat 8 v.toNat = v := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa [hv] using h

/-- A byte below the signed pivot 13 reads the `add -9` leaf. -/
theorem stage2SkipLeaf_slt13_true {v : BitVec 8}
    (h : v.slt (BitVec.ofNat 8 13) = true) :
    stage2SkipLeaf v = (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) := by
  unfold stage2SkipLeaf
  rw [if_pos h]

/-- A byte at or above the signed pivot 13 reads the second pivot. -/
theorem stage2SkipLeaf_slt13_false {v : BitVec 8}
    (h : v.slt (BitVec.ofNat 8 13) = false) :
    stage2SkipLeaf v =
      (if v.slt (BitVec.ofNat 8 32) = true then v == BitVec.ofNat 8 13
       else v == BitVec.ofNat 8 32) := by
  unfold stage2SkipLeaf
  rw [if_neg (by rw [h]; decide)]

/-- A byte at or above the signed pivot 13 and below 32 reads the `eq 13` leaf. -/
theorem stage2SkipLeaf_slt32_true {v : BitVec 8}
    (h13 : v.slt (BitVec.ofNat 8 13) = false)
    (h : v.slt (BitVec.ofNat 8 32) = true) :
    stage2SkipLeaf v = (v == BitVec.ofNat 8 13) := by
  unfold stage2SkipLeaf
  rw [if_neg (by rw [h13]; decide), if_pos h]

/-- A byte at or above both pivots reads the `eq 32` leaf. -/
theorem stage2SkipLeaf_slt32_false {v : BitVec 8}
    (h13 : v.slt (BitVec.ofNat 8 13) = false)
    (h : v.slt (BitVec.ofNat 8 32) = false) :
    stage2SkipLeaf v = (v == BitVec.ofNat 8 32) := by
  unfold stage2SkipLeaf
  rw [if_neg (by rw [h13]; decide), if_neg (by rw [h]; decide)]

/-- `BitVec.ofBool` at one. -/
theorem stage2Skip_ofBool_eq_one {p : Prop} [Decidable p] :
    (BitVec.ofBool p = (1 : BitVec 1)) ↔ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

/-- `BitVec.ofBool` at zero. -/
theorem stage2Skip_ofBool_eq_zero {p : Prop} [Decidable p] :
    (BitVec.ofBool p = (0 : BitVec 1)) ↔ ¬ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

/-- An `ule` leaf test taken, at the model's comparison. -/
theorem stage2Skip_ule_one_of {x : BitVec 8}
    (h : x.ule (BitVec.ofNat 8 1) = true) :
    evalICmp .ule x (BitVec.ofNat 8 1) = 1 := by
  rw [show evalICmp .ule x (BitVec.ofNat 8 1) =
    BitVec.ofBool (x.ule (BitVec.ofNat 8 1)) from rfl, h]
  rfl

/-- An `ule` leaf test refused, at the model's comparison. -/
theorem stage2Skip_ule_zero_of {x : BitVec 8}
    (h : x.ule (BitVec.ofNat 8 1) = false) :
    evalICmp .ule x (BitVec.ofNat 8 1) = 0 := by
  rw [show evalICmp .ule x (BitVec.ofNat 8 1) =
    BitVec.ofBool (x.ule (BitVec.ofNat 8 1)) from rfl, h]
  rfl

/-- An `eq` leaf test taken, at the model's comparison. -/
theorem stage2Skip_beq_one_of {v c : BitVec 8} (h : (v == c) = true) :
    evalICmp .eq v c = 1 := by
  have h' : v = c := by simpa using h
  rw [h']
  exact (stage2Skip_ofBool_eq_one (p := c = c)).2 rfl

/-- An `eq` leaf test refused, at the model's comparison. -/
theorem stage2Skip_beq_zero_of {v c : BitVec 8} (h : (v == c) = false) :
    evalICmp .eq v c = 0 := by
  have h' : ¬ (v = c) := by
    intro hv
    rw [hv] at h
    exact absurd h (by simp)
  exact (stage2Skip_ofBool_eq_zero (p := v = c)).2 h'

/-- `ofNat 8` is injective below `256`. -/
theorem stage2Skip_ofNat_eq {a b : Nat} (ha : a < 256) (hb : b < 256) :
    (BitVec.ofNat 8 a = BitVec.ofNat 8 b) ↔ a = b := by
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact h2
  · intro h
    rw [h]

/-- The class is the four bytes, at their `Nat` readings. -/
theorem stage2SkipWs_iff_fin (i : Fin 256) :
    stage2SkipWs (BitVec.ofNat 8 i.val) = true ↔
      (i.val = 9 ∨ i.val = 10 ∨ i.val = 13 ∨ i.val = 32) := by
  revert i
  decide

/-- The class is HT, LF, CR and space, at the bytes' `Nat` readings. -/
theorem stage2SkipWs_iff (v : BitVec 8) :
    stage2SkipWs v = true ↔
      (v.toNat = 9 ∨ v.toNat = 10 ∨ v.toNat = 13 ∨ v.toNat = 32) := by
  have h := stage2SkipWs_iff_fin ⟨v.toNat, v.isLt⟩
  have hv : BitVec.ofNat 8 v.toNat = v := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rwa [hv] at h

/-- The body's `load i8` binds `ofNat 8 u.toNat`; the class reads `u.toBitVec`. -/
theorem stage2Skip_uint8_toBitVec (u : UInt8) :
    BitVec.ofNat 8 u.toNat = u.toBitVec := by
  have h : UInt8.ofNat u.toNat = u := UInt8.ofNat_toNat
  conv => rhs; rw [← h]
  exact (UInt8.toBitVec_ofNat u.toNat).symm

/-- `ofNat 64` is injective below `2 ^ 64`. -/
theorem stage2Skip_ofNat64_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact h2
  · intro h
    rw [h]

/-- The `i64` increment at a `Nat` reading. -/
theorem stage2Skip_ofNat_succ {c : Nat} (h : c + 1 < 2 ^ 64) :
    BitVec.ofNat 64 c + BitVec.ofNat 64 1 = BitVec.ofNat 64 (c + 1) := by
  have hsum : (BitVec.ofNat 64 c + BitVec.ofNat 64 1).toNat = c + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : c < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.mod_eq_of_lt h]
  have hof : BitVec.ofNat 64 (BitVec.ofNat 64 c + BitVec.ofNat 64 1).toNat =
      BitVec.ofNat 64 c + BitVec.ofNat 64 1 := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← hof, hsum]

/-- The increment test at one, from the equation of the two readings. -/
theorem stage2Skip_eq_ofNat_one {a b : Nat} (h : a = b) :
    evalICmp .eq (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  simp only [evalICmp, stage2Skip_ofBool_eq_one, h]

/-- The increment test at zero, from the two readings differing. -/
theorem stage2Skip_eq_ofNat_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a ≠ b) :
    evalICmp .eq (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  simp only [evalICmp, stage2Skip_ofBool_eq_zero]
  intro hab
  exact h ((stage2Skip_ofNat64_eq ha hb).1 hab)

/-! ### The blocks, pinned -/

/-- `land.lhs.true`: the probe at `%invariant.gep1068 + %cond` and its byte. -/
def stage2SkipLandLhsTrueInstrs : List Instr :=
  [ Instr.gep "%gep1069" (Ty.int 8) (Operand.reg "%invariant.gep1068")
      (Operand.reg "%cond"),
    Instr.load "%57" (Ty.int 8) (Operand.reg "%gep1069") ]

theorem stage2SkipLandLhsTrue_find :
    stage2NoEventBody.findBlock "land.lhs.true" =
      some ⟨"land.lhs.true", stage2SkipLandLhsTrueInstrs, Term.br "NodeBlock51"⟩ := by
  decide

/-- `NodeBlock51`: the byte against signed 13. -/
def stage2SkipNodeBlock51Instrs : List Instr :=
  [ Instr.icmp "%Pivot52" IPred.slt 8 (Operand.reg "%57")
      (Operand.imm (.int 8 (BitVec.ofNat 8 13))) ]

theorem stage2SkipNodeBlock51_find :
    stage2NoEventBody.findBlock "NodeBlock51" =
      some ⟨"NodeBlock51", stage2SkipNodeBlock51Instrs,
        Term.condbr (Operand.reg "%Pivot52") "LeafBlock43" "NodeBlock49"⟩ := by
  decide

/-- `NodeBlock49`: the byte against signed 32. -/
def stage2SkipNodeBlock49Instrs : List Instr :=
  [ Instr.icmp "%Pivot50" IPred.slt 8 (Operand.reg "%57")
      (Operand.imm (.int 8 (BitVec.ofNat 8 32))) ]

theorem stage2SkipNodeBlock49_find :
    stage2NoEventBody.findBlock "NodeBlock49" =
      some ⟨"NodeBlock49", stage2SkipNodeBlock49Instrs,
        Term.condbr (Operand.reg "%Pivot50") "LeafBlock45" "LeafBlock47"⟩ := by
  decide

/-- `LeafBlock47`: the `space` test. -/
def stage2SkipLeafBlock47Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf48" IPred.eq 8 (Operand.reg "%57")
      (Operand.imm (.int 8 (BitVec.ofNat 8 32))) ]

theorem stage2SkipLeafBlock47_find :
    stage2NoEventBody.findBlock "LeafBlock47" =
      some ⟨"LeafBlock47", stage2SkipLeafBlock47Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf48") "land.rhs.preheader" "if.end457"⟩ := by
  decide

/-- `LeafBlock45`: the `CR` test. -/
def stage2SkipLeafBlock45Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf46" IPred.eq 8 (Operand.reg "%57")
      (Operand.imm (.int 8 (BitVec.ofNat 8 13))) ]

theorem stage2SkipLeafBlock45_find :
    stage2NoEventBody.findBlock "LeafBlock45" =
      some ⟨"LeafBlock45", stage2SkipLeafBlock45Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf46") "land.rhs.preheader" "if.end457"⟩ := by
  decide

/-- `LeafBlock43`: the `HT`/`LF` range test. -/
def stage2SkipLeafBlock43Instrs : List Instr :=
  [ Instr.binop "%.off" BinOp.add 8 (Operand.reg "%57")
      (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
    Instr.icmp "%SwitchLeaf44" IPred.ule 8 (Operand.reg "%.off")
      (Operand.imm (.int 8 (BitVec.ofNat 8 1))) ]

theorem stage2SkipLeafBlock43_find :
    stage2NoEventBody.findBlock "LeafBlock43" =
      some ⟨"LeafBlock43", stage2SkipLeafBlock43Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf44") "land.rhs.preheader" "if.end457"⟩ := by
  decide

/-- `land.rhs.preheader`: the loop's entry. -/
theorem stage2SkipLandRhsPreheader_find :
    stage2NoEventBody.findBlock "land.rhs.preheader" =
      some ⟨"land.rhs.preheader", [], Term.br "land.rhs"⟩ := by
  decide

/-- `land.rhs`'s `%ee.01053` incoming list. -/
def stage2SkipLandRhsIncoming : List (String × Operand) :=
  [("while.body", Operand.reg "%inc456"),
   ("land.rhs.preheader", Operand.reg "%idxprom.lcssa")]

/-- `land.rhs`: the cursor's `phi`, the `%b` `gep` and the byte load. -/
def stage2SkipLandRhsInstrs : List Instr :=
  [ Instr.phi "%ee.01053" (Ty.int 64) stage2SkipLandRhsIncoming,
    Instr.gep "%arrayidx453" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%ee.01053"),
    Instr.load "%58" (Ty.int 8) (Operand.reg "%arrayidx453") ]

theorem stage2SkipLandRhs_find :
    stage2NoEventBody.findBlock "land.rhs" =
      some ⟨"land.rhs", stage2SkipLandRhsInstrs, Term.br "NodeBlock62"⟩ := by
  decide

/-- `NodeBlock62`: the loaded byte against signed 13. -/
def stage2SkipNodeBlock62Instrs : List Instr :=
  [ Instr.icmp "%Pivot63" IPred.slt 8 (Operand.reg "%58")
      (Operand.imm (.int 8 (BitVec.ofNat 8 13))) ]

theorem stage2SkipNodeBlock62_find :
    stage2NoEventBody.findBlock "NodeBlock62" =
      some ⟨"NodeBlock62", stage2SkipNodeBlock62Instrs,
        Term.condbr (Operand.reg "%Pivot63") "LeafBlock53" "NodeBlock60"⟩ := by
  decide

/-- `NodeBlock60`: the loaded byte against signed 32. -/
def stage2SkipNodeBlock60Instrs : List Instr :=
  [ Instr.icmp "%Pivot61" IPred.slt 8 (Operand.reg "%58")
      (Operand.imm (.int 8 (BitVec.ofNat 8 32))) ]

theorem stage2SkipNodeBlock60_find :
    stage2NoEventBody.findBlock "NodeBlock60" =
      some ⟨"NodeBlock60", stage2SkipNodeBlock60Instrs,
        Term.condbr (Operand.reg "%Pivot61") "LeafBlock56" "LeafBlock58"⟩ := by
  decide

/-- `LeafBlock58`: the `space` test, leaving on whitespace. -/
def stage2SkipLeafBlock58Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf59" IPred.eq 8 (Operand.reg "%58")
      (Operand.imm (.int 8 (BitVec.ofNat 8 32))) ]

theorem stage2SkipLeafBlock58_find :
    stage2NoEventBody.findBlock "LeafBlock58" =
      some ⟨"LeafBlock58", stage2SkipLeafBlock58Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf59") "if.end457" "while.body"⟩ := by
  decide

/-- `LeafBlock56`: the `CR` test, leaving on whitespace. -/
def stage2SkipLeafBlock56Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf57" IPred.eq 8 (Operand.reg "%58")
      (Operand.imm (.int 8 (BitVec.ofNat 8 13))) ]

theorem stage2SkipLeafBlock56_find :
    stage2NoEventBody.findBlock "LeafBlock56" =
      some ⟨"LeafBlock56", stage2SkipLeafBlock56Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf57") "if.end457" "while.body"⟩ := by
  decide

/-- `LeafBlock53`: the `HT`/`LF` range test, leaving on whitespace. -/
def stage2SkipLeafBlock53Instrs : List Instr :=
  [ Instr.binop "%.off54" BinOp.add 8 (Operand.reg "%58")
      (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
    Instr.icmp "%SwitchLeaf55" IPred.ule 8 (Operand.reg "%.off54")
      (Operand.imm (.int 8 (BitVec.ofNat 8 1))) ]

theorem stage2SkipLeafBlock53_find :
    stage2NoEventBody.findBlock "LeafBlock53" =
      some ⟨"LeafBlock53", stage2SkipLeafBlock53Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf55") "if.end457" "while.body"⟩ := by
  decide

/-- `while.body`: the increment and its test against `%cond`. -/
def stage2SkipWhileBodyInstrs : List Instr :=
  [ Instr.binop "%inc456" BinOp.add 64 (Operand.reg "%ee.01053")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.icmp "%exitcond1170.not" IPred.eq 64 (Operand.reg "%inc456")
      (Operand.reg "%cond") ]

theorem stage2SkipWhileBody_find :
    stage2NoEventBody.findBlock "while.body" =
      some ⟨"while.body", stage2SkipWhileBodyInstrs,
        Term.condbr (Operand.reg "%exitcond1170.not") "if.end457" "land.rhs"⟩ := by
  decide

/-- `if.end457`'s `%ee.1` incoming list. -/
def stage2SkipIfEnd457EeIncoming : List (String × Operand) :=
  [("cond.end", Operand.reg "%idxprom.lcssa"),
   ("while.body", Operand.reg "%cond"),
   ("LeafBlock53", Operand.reg "%ee.01053"),
   ("LeafBlock56", Operand.reg "%ee.01053"),
   ("LeafBlock58", Operand.reg "%ee.01053"),
   ("LeafBlock43", Operand.reg "%cond"),
   ("LeafBlock45", Operand.reg "%cond"),
   ("LeafBlock47", Operand.reg "%cond")]

/-- `if.end457`: the merge's `phi`, the `%k219` store, and the number-or-minus
guard. -/
def stage2SkipIfEnd457Instrs : List Instr :=
  [ Instr.phi "%ee.1" (Ty.int 64) stage2SkipIfEnd457EeIncoming,
    Instr.store (Ty.int 64) (Operand.reg "%inc.lcssa") (Operand.reg "%k219"),
    Instr.icmp "%cmp462" IPred.eq 8 (Operand.reg "%.lcssa")
      (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
    Instr.binop "%59" BinOp.add 8 (Operand.reg "%.lcssa")
      (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
    Instr.icmp "%or.cond" IPred.ult 8 (Operand.reg "%59")
      (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
    Instr.binop "%or.cond901" BinOp.or 1 (Operand.reg "%cmp462")
      (Operand.reg "%or.cond") ]

theorem stage2SkipIfEnd457_find :
    stage2NoEventBody.findBlock "if.end457" =
      some ⟨"if.end457", stage2SkipIfEnd457Instrs,
        Term.condbr (Operand.reg "%or.cond901") "if.then471" "if.else495"⟩ := by
  decide

-- The pins resolve.
#guard decide (stage2NoEventBody.findBlock "land.lhs.true" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock51" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock49" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock43" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock45" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock47" ≠ none)
#guard decide (stage2NoEventBody.findBlock "land.rhs.preheader" ≠ none)
#guard decide (stage2NoEventBody.findBlock "land.rhs" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock62" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock60" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock53" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock56" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock58" ≠ none)
#guard decide (stage2NoEventBody.findBlock "while.body" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end457" ≠ none)

/-- A block's `phi` incoming list for a destination, read from the pins. -/
def stage2SkipPhiIncoming (b : Block) (d : String) : Option (List (String × Operand)) :=
  b.instrs.findSome? fun i =>
    match i with
    | .phi d' _ inc => if d' = d then some inc else none
    | _ => none

#guard decide
  (stage2SkipPhiIncoming
      ((stage2NoEventBody.findBlock "if.end457").getD ⟨"", [], .unreachable⟩) "%ee.1" =
    some stage2SkipIfEnd457EeIncoming)

/-! ### The byte shapes' step vocabulary

`BlockEval`'s chain steps are stated at `i64`; the segment needs an `i8` load and
an `i1` `or`.  The byte compares and the byte add are `WalkLoop`'s
width-general ones. -/

/-- Resolve a register read against a concrete cell list. -/
macro "skip_lk" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first | rw [lookupName_cons_self] | assumption))

/-- An `i8` load from a readable byte. -/
theorem stage2Skip_step_load8 (calls : Calls) (env : Env) (s : State)
    (d p : String) {a : Nat} {u : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hu : readByte s.mem a = some u) :
    evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (BitVec.ofNat 8 u.toNat)) :: env) s) := by
  have hrs : readBytes s.mem a 1 = some [u] := by
    rw [JsonEntrySteps.readBytes_one, hu]; rfl
  have h2 := DepthCountRefine.evalInstr_load8 calls (stateAt env s) d p a [u] hp hrs
  rw [h2]
  simp only [stateAt, State.bind]
  rw [show bytesToNat [u] = u.toNat from rfl]

/-- An `i8` load, as a chain step. -/
theorem stage2Skip_denote_load8 (calls : Calls) (env : Env) (s : State)
    (d p : String) {a : Nat} {u : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hu : readByte s.mem a = some u) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 u.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (stage2Skip_step_load8 calls env s d p hp hu)]

/-- An `i1` `or` of two registers. -/
theorem stage2Skip_denote_or_reg1 (calls : Calls) (env : Env) (s : State)
    (d a b : String) {x y : BitVec 1}
    (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) (is : List Instr) :
    denoteCode calls (.binop d .or 1 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (x ||| y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .or 1 (.reg a) (.reg b)) =
        some (stateAt ((d, .int 1 (x ||| y)) :: env) s) from by
      simp [evalInstr, evalOperand, stateAt, ha, hb, evalBinopNat, evalBinop,
        Value.intToNat, BitVec.ofNat_toNat, State.bind])]

/-! ### The blocks' runs -/

/-- `land.lhs.true`'s cells: the probe's address and its byte. -/
abbrev stage2SkipLandLhsTrueCells (env : Env) (g : Nat) (c : BitVec 64) (u : UInt8) :
    Env :=
  ("%57", .int 8 (BitVec.ofNat 8 u.toNat)) ::
    ("%gep1069", .ptr (g + (c.signExtend 64).toNat)) :: env

theorem stage2SkipLandLhsTrue_denote (calls : Calls) (env : Env) (s : State)
    {g : Nat} {c : BitVec 64} {u : UInt8}
    (hg : lookupName env "%invariant.gep1068" = some (.ptr g))
    (hc : lookupName env "%cond" = some (.int 64 c))
    (hcpos : (c.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (g + (c.signExtend 64).toNat) = some u) :
    denoteCode calls stage2SkipLandLhsTrueInstrs (stateAt env s) =
      some (stateAt (stage2SkipLandLhsTrueCells env g c u) s) := by
  unfold stage2SkipLandLhsTrueInstrs
  rw [denoteCode_gep8_reg (calls := calls) (env := env) (s := s)
    (d := "%gep1069") (base := "%invariant.gep1068") (off := "%cond")
    (a := g) (idx := c) hg hc hcpos]
  rw [stage2Skip_denote_load8 (calls := calls)
    (env := ("%gep1069", .ptr (g + (c.signExtend 64).toNat)) :: env) (s := s)
    (d := "%57") (p := "%gep1069") (a := g + (c.signExtend 64).toNat) (u := u)
    (by simp only [lookupName_cons_self]) hu]
  simp only [denoteCode_nil, stage2SkipLandLhsTrueCells]

theorem stage2SkipNodeBlock51_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h57 : lookupName env "%57" = some (.int 8 v)) :
    denoteCode calls stage2SkipNodeBlock51Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: env) s) := by
  unfold stage2SkipNodeBlock51Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%Pivot52") (a := "%57") (p := .slt) (w := 8) (x := v)
    (c := BitVec.ofNat 8 13) h57 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipNodeBlock49_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h57 : lookupName env "%57" = some (.int 8 v)) :
    denoteCode calls stage2SkipNodeBlock49Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: env) s) := by
  unfold stage2SkipNodeBlock49Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%Pivot50") (a := "%57") (p := .slt) (w := 8) (x := v)
    (c := BitVec.ofNat 8 32) h57 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock47_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h57 : lookupName env "%57" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock47Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: env) s) := by
  unfold stage2SkipLeafBlock47Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf48") (a := "%57") (p := .eq) (w := 8) (x := v)
    (c := BitVec.ofNat 8 32) h57 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock45_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h57 : lookupName env "%57" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock45Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: env) s) := by
  unfold stage2SkipLeafBlock45Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf46") (a := "%57") (p := .eq) (w := 8) (x := v)
    (c := BitVec.ofNat 8 13) h57 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock43_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h57 : lookupName env "%57" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock43Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf44",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: env) s) := by
  unfold stage2SkipLeafBlock43Instrs
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%.off") (a := "%57") (w := 8) (x := v) (c := BitVec.ofNat 8 247) h57]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: env) (s := s)
    (d := "%SwitchLeaf44") (a := "%.off") (p := .ule) (w := 8)
    (x := v + BitVec.ofNat 8 247) (c := BitVec.ofNat 8 1)
    (by simp only [lookupName_cons_self]) (is := [])]
  simp only [denoteCode_nil]

/-- `land.rhs`'s cells: the cursor, the address and the byte. -/
abbrev stage2SkipLandRhsCells (env : Env) (c : BitVec 64) (b : Nat) (u : UInt8) : Env :=
  ("%58", .int 8 (BitVec.ofNat 8 u.toNat)) ::
    ("%arrayidx453", .ptr (b + (c.signExtend 64).toNat)) ::
      ("%ee.01053", .int 64 c) :: env

theorem stage2SkipLandRhs_denote (calls : Calls) (env : Env) (s : State)
    {c : BitVec 64} {b : Nat} {u : UInt8} {op : Operand} {pre : String}
    (hpre : s.pre = some pre)
    (hinc : phiIncoming pre stage2SkipLandRhsIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 c))
    (hb : lookupName env "%b" = some (.ptr b))
    (hcpos : (c.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (b + (c.signExtend 64).toNat) = some u) :
    denoteCode calls stage2SkipLandRhsInstrs (stateAt env s) =
      some (stateAt (stage2SkipLandRhsCells env c b u) s) := by
  unfold stage2SkipLandRhsInstrs
  block_phi_run
  · change denoteCode calls
      [Instr.gep "%arrayidx453" (Ty.int 8) (Operand.reg "%b")
         (Operand.reg "%ee.01053"),
       Instr.load "%58" (Ty.int 8) (Operand.reg "%arrayidx453")]
      (stateAt (("%ee.01053", .int 64 c) :: env) s) =
      some (stateAt (stage2SkipLandRhsCells env c b u) s)
    rw [denoteCode_gep8_reg (calls := calls)
      (env := ("%ee.01053", .int 64 c) :: env) (s := s)
      (d := "%arrayidx453") (base := "%b") (off := "%ee.01053")
      (a := b) (idx := c)
      (by skip_lk)
      (by simp only [lookupName_cons_self]) hcpos]
    rw [stage2Skip_denote_load8 (calls := calls)
      (env := ("%arrayidx453", .ptr (b + (c.signExtend 64).toNat)) ::
        ("%ee.01053", .int 64 c) :: env) (s := s)
      (d := "%58") (p := "%arrayidx453") (a := b + (c.signExtend 64).toNat) (u := u)
      (by simp only [lookupName_cons_self]) hu]
    simp only [denoteCode_nil, stage2SkipLandRhsCells]
  · exact hpre
  · rfl
  · exact hinc
  · exact hop

theorem stage2SkipLandRhs_incoming_preheader :
    phiIncoming "land.rhs.preheader" stage2SkipLandRhsIncoming =
      some (.reg "%idxprom.lcssa") := by
  simp only [stage2SkipLandRhsIncoming, phiIncoming]
  rfl

theorem stage2SkipLandRhs_incoming_whileBody :
    phiIncoming "while.body" stage2SkipLandRhsIncoming = some (.reg "%inc456") := by
  simp only [stage2SkipLandRhsIncoming, phiIncoming]
  rfl

theorem stage2SkipNodeBlock62_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h58 : lookupName env "%58" = some (.int 8 v)) :
    denoteCode calls stage2SkipNodeBlock62Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: env) s) := by
  unfold stage2SkipNodeBlock62Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%Pivot63") (a := "%58") (p := .slt) (w := 8) (x := v)
    (c := BitVec.ofNat 8 13) h58 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipNodeBlock60_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h58 : lookupName env "%58" = some (.int 8 v)) :
    denoteCode calls stage2SkipNodeBlock60Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: env) s) := by
  unfold stage2SkipNodeBlock60Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%Pivot61") (a := "%58") (p := .slt) (w := 8) (x := v)
    (c := BitVec.ofNat 8 32) h58 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock58_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h58 : lookupName env "%58" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock58Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: env) s) := by
  unfold stage2SkipLeafBlock58Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf59") (a := "%58") (p := .eq) (w := 8) (x := v)
    (c := BitVec.ofNat 8 32) h58 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock56_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h58 : lookupName env "%58" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock56Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: env) s) := by
  unfold stage2SkipLeafBlock56Instrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf57") (a := "%58") (p := .eq) (w := 8) (x := v)
    (c := BitVec.ofNat 8 13) h58 (is := [])]
  simp only [denoteCode_nil]

theorem stage2SkipLeafBlock53_denote (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (h58 : lookupName env "%58" = some (.int 8 v)) :
    denoteCode calls stage2SkipLeafBlock53Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf55",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: env) s) := by
  unfold stage2SkipLeafBlock53Instrs
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%.off54") (a := "%58") (w := 8) (x := v) (c := BitVec.ofNat 8 247) h58]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: env) (s := s)
    (d := "%SwitchLeaf55") (a := "%.off54") (p := .ule) (w := 8)
    (x := v + BitVec.ofNat 8 247) (c := BitVec.ofNat 8 1)
    (by simp only [lookupName_cons_self]) (is := [])]
  simp only [denoteCode_nil]

/-- `while.body`'s cells: the increment and its test. -/
abbrev stage2SkipWhileBodyCells (env : Env) (c cd : BitVec 64) : Env :=
  ("%exitcond1170.not", .int 1 (evalICmp .eq (c + BitVec.ofNat 64 1) cd)) ::
    ("%inc456", .int 64 (c + BitVec.ofNat 64 1)) :: env

theorem stage2SkipWhileBody_denote (calls : Calls) (env : Env) (s : State)
    {c cd : BitVec 64}
    (hee : lookupName env "%ee.01053" = some (.int 64 c))
    (hcd : lookupName env "%cond" = some (.int 64 cd)) :
    denoteCode calls stage2SkipWhileBodyInstrs (stateAt env s) =
      some (stateAt (stage2SkipWhileBodyCells env c cd) s) := by
  unfold stage2SkipWhileBodyInstrs
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc456") (a := "%ee.01053") (w := 64) (x := c) (c := BitVec.ofNat 64 1) hee]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%inc456", .int 64 (c + BitVec.ofNat 64 1)) :: env) (s := s)
    (d := "%exitcond1170.not") (a := "%inc456") (b := "%cond") (p := .eq) (w := 64)
    (x := c + BitVec.ofNat 64 1) (y := cd)
    (by simp only [lookupName_cons_self])
    (by skip_lk) (is := [])]
  simp only [denoteCode_nil, stage2SkipWhileBodyCells]

/-- `if.end457`'s cells: the merge's word, the store's address and the guard. -/
abbrev stage2SkipIfEnd457Cells (env : Env) (p : Nat) (lc : BitVec 8) : Env :=
  ("%or.cond901",
      .int 1 (evalICmp .eq lc (BitVec.ofNat 8 45) |||
        evalICmp .ult (lc + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
    ("%or.cond", .int 1 (evalICmp .ult (lc + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
      ("%59", .int 8 (lc + BitVec.ofNat 8 208)) ::
        ("%cmp462", .int 1 (evalICmp .eq lc (BitVec.ofNat 8 45))) ::
          ("%ee.1", .int 64 (BitVec.ofNat 64 p)) :: env

theorem stage2SkipIfEnd457_denote (calls : Calls) (env : Env) (s : State)
    {p : Nat} {op : Operand} {pre : String} {inc : BitVec 64} {lc : BitVec 8}
    {k219 : Nat}
    (hpre : s.pre = some pre)
    (hinc : phiIncoming pre stage2SkipIfEnd457EeIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 (BitVec.ofNat 64 p)))
    (hincv : lookupName env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName env "%k219" = some (.ptr k219)) :
    denoteCode calls stage2SkipIfEnd457Instrs (stateAt env s) =
      some (stateAt (stage2SkipIfEnd457Cells env p lc)
        (stage2NoEventStepState s (writeBytes s.mem k219 (natToBytes inc.toNat 8))
          s.next)) := by
  unfold stage2SkipIfEnd457Instrs
  block_phi_run
  · change denoteCode calls
      [Instr.store (Ty.int 64) (Operand.reg "%inc.lcssa") (Operand.reg "%k219"),
       Instr.icmp "%cmp462" IPred.eq 8 (Operand.reg "%.lcssa")
         (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
       Instr.binop "%59" BinOp.add 8 (Operand.reg "%.lcssa")
         (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
       Instr.icmp "%or.cond" IPred.ult 8 (Operand.reg "%59")
         (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
       Instr.binop "%or.cond901" BinOp.or 1 (Operand.reg "%cmp462")
         (Operand.reg "%or.cond")]
      (stateAt (("%ee.1", .int 64 (BitVec.ofNat 64 p)) :: env) s) =
      some (stateAt (stage2SkipIfEnd457Cells env p lc)
        (stage2NoEventStepState s (writeBytes s.mem k219 (natToBytes inc.toNat 8))
          s.next))
    rw [stage2NoEventWalk_denote_store_int (calls := calls)
      (env := ("%ee.1", .int 64 (BitVec.ofNat 64 p)) :: env) (s := s)
      (v := "%inc.lcssa") (p := "%k219") (w := 64)
      (x := inc) (a := k219)
      (by skip_lk) (by skip_lk)]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := _) (s := _)
      (d := "%cmp462") (a := "%.lcssa") (p := .eq) (w := 8) (x := lc)
      (c := BitVec.ofNat 8 45)
      (by skip_lk) (is := _)]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := _)
      (d := "%59") (a := "%.lcssa") (w := 8) (x := lc) (c := BitVec.ofNat 8 208)
      (by skip_lk)]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := _) (s := _)
      (d := "%or.cond") (a := "%59") (p := .ult) (w := 8)
      (x := lc + BitVec.ofNat 8 208) (c := BitVec.ofNat 8 10)
      (by skip_lk) (is := _)]
    rw [stage2Skip_denote_or_reg1 (calls := calls) (env := _) (s := _)
      (d := "%or.cond901") (a := "%cmp462") (b := "%or.cond")
      (x := evalICmp .eq lc (BitVec.ofNat 8 45))
      (y := evalICmp .ult (lc + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by skip_lk) (by skip_lk) (is := [])]
    simp only [denoteCode_nil, stage2SkipIfEnd457Cells]
  · exact hpre
  · rfl
  · exact hinc
  · exact hop

/-! ### The segment's link vocabulary

The two-, three-, four- and five-link compositions, at literal counts, so a
caller's fuel price is a numeral rather than a chain's opaque step count. -/

theorem stage2SkipRun2 {calls : Calls} {mem : Mem} {K₀ K₁ K₂ : Stage2NoEventWalkCarry}
    {s₀ s₁ s₂ : State}
    (L₁ : Stage2NoEventWalkLink calls K₀ mem s₀ K₁ s₁)
    (L₂ : Stage2NoEventWalkLink calls K₁ mem s₁ K₂ s₂) :
    ∀ n, runFuel calls (2 + n) stage2NoEventBody s₀ =
      runFuel calls n stage2NoEventBody s₂ := by
  intro n
  rw [show 2 + n = 1 + (1 + n) from by omega, stage2NoEventWalkLink_runFuel L₁,
    stage2NoEventWalkLink_runFuel L₂]

theorem stage2SkipRun3 {calls : Calls} {mem : Mem} {K₀ K₁ K₂ K₃ : Stage2NoEventWalkCarry}
    {s₀ s₁ s₂ s₃ : State}
    (L₁ : Stage2NoEventWalkLink calls K₀ mem s₀ K₁ s₁)
    (L₂ : Stage2NoEventWalkLink calls K₁ mem s₁ K₂ s₂)
    (L₃ : Stage2NoEventWalkLink calls K₂ mem s₂ K₃ s₃) :
    ∀ n, runFuel calls (3 + n) stage2NoEventBody s₀ =
      runFuel calls n stage2NoEventBody s₃ := by
  intro n
  rw [show 3 + n = 1 + (2 + n) from by omega, stage2NoEventWalkLink_runFuel L₁,
    stage2SkipRun2 L₂ L₃]

theorem stage2SkipRun4 {calls : Calls} {mem : Mem}
    {K₀ K₁ K₂ K₃ K₄ : Stage2NoEventWalkCarry} {s₀ s₁ s₂ s₃ s₄ : State}
    (L₁ : Stage2NoEventWalkLink calls K₀ mem s₀ K₁ s₁)
    (L₂ : Stage2NoEventWalkLink calls K₁ mem s₁ K₂ s₂)
    (L₃ : Stage2NoEventWalkLink calls K₂ mem s₂ K₃ s₃)
    (L₄ : Stage2NoEventWalkLink calls K₃ mem s₃ K₄ s₄) :
    ∀ n, runFuel calls (4 + n) stage2NoEventBody s₀ =
      runFuel calls n stage2NoEventBody s₄ := by
  intro n
  rw [show 4 + n = 1 + (3 + n) from by omega, stage2NoEventWalkLink_runFuel L₁,
    stage2SkipRun3 L₂ L₃ L₄]

theorem stage2SkipRun5 {calls : Calls} {mem : Mem}
    {K₀ K₁ K₂ K₃ K₄ K₅ : Stage2NoEventWalkCarry} {s₀ s₁ s₂ s₃ s₄ s₅ : State}
    (L₁ : Stage2NoEventWalkLink calls K₀ mem s₀ K₁ s₁)
    (L₂ : Stage2NoEventWalkLink calls K₁ mem s₁ K₂ s₂)
    (L₃ : Stage2NoEventWalkLink calls K₂ mem s₂ K₃ s₃)
    (L₄ : Stage2NoEventWalkLink calls K₃ mem s₃ K₄ s₄)
    (L₅ : Stage2NoEventWalkLink calls K₄ mem s₄ K₅ s₅) :
    ∀ n, runFuel calls (5 + n) stage2NoEventBody s₀ =
      runFuel calls n stage2NoEventBody s₅ := by
  intro n
  rw [show 5 + n = 1 + (4 + n) from by omega, stage2NoEventWalkLink_runFuel L₁,
    stage2SkipRun4 L₂ L₃ L₄ L₅]

/-! ### The links

Each block's one control step at its two arms.  No block in this segment writes
memory except `if.end457`'s store, so every link before it transports the
invariant by `mem_congr`. -/

theorem link_skipLandLhsTrue {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {g : Nat} {c : BitVec 64} {u : UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.lhs.true")
    (hg : lookupName s.env "%invariant.gep1068" = some (.ptr g))
    (hc : lookupName s.env "%cond" = some (.int 64 c))
    (hcpos : (c.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (g + (c.signExtend 64).toNat) = some u) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (stage2SkipLandLhsTrueCells s.env g c u) s
        "NodeBlock51") := by
  have hcode := stage2SkipLandLhsTrue_denote (calls := calls) (env := s.env) (s := s)
    hg hc hcpos hu
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLandLhsTrue_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock51_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock51")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 13) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "LeafBlock43") := by
  have hcode := stage2SkipNodeBlock51_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock51_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock51_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock51")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 13) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock49") := by
  have hcode := stage2SkipNodeBlock51_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock51_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock49_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock49")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 32) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: s.env) s
        "LeafBlock45") := by
  have hcode := stage2SkipNodeBlock49_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock49_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock49_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock49")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 32) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: s.env) s
        "LeafBlock47") := by
  have hcode := stage2SkipNodeBlock49_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock49_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock47_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock47")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 32) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: s.env) s
        "land.rhs.preheader") := by
  have hcode := stage2SkipLeafBlock47_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock47_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock47_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock47")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 32) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock47_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock47_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock45_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock45")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 13) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: s.env) s
        "land.rhs.preheader") := by
  have hcode := stage2SkipLeafBlock45_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock45_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock45_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock45")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 13) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock45_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock45_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock43_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock43")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf44",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: s.env) s
        "land.rhs.preheader") := by
  have hcode := stage2SkipLeafBlock43_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock43_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock43_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock43")
    (h57 : lookupName s.env "%57" = some (.int 8 v))
    (hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf44",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock43_denote (calls := calls) (env := s.env) (s := s) h57
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock43_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLandRhsPreheader {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.rhs.preheader") :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext s.env s "land.rhs") := by
  have hcode : denoteCode calls ([] : List Instr) (stateAt s.env s) = some (stateAt s.env s) :=
    rfl
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (b := ⟨"land.rhs.preheader", [], Term.br "land.rhs"⟩)
    (by rw [hpc]; exact stage2SkipLandRhsPreheader_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLandRhs_preheader {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {b idx : Nat} {v : BitVec 64} {u : UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.rhs")
    (hpre : s.pre = some "land.rhs.preheader")
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 v))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hvpos : (v.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (b + (v.signExtend 64).toNat) = some u) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (stage2SkipLandRhsCells s.env v b u) s "NodeBlock62") := by
  have hcode := stage2SkipLandRhs_denote (calls := calls) (env := s.env) (s := s)
    (c := v) (b := b) (u := u) (op := .reg "%idxprom.lcssa") (pre := "land.rhs.preheader")
    hpre stage2SkipLandRhs_incoming_preheader
    (by simp only [stateAt, evalOperand, hidx]) hb hvpos hu
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLandRhs_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLandRhs_whileBody {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {b : Nat} {c : BitVec 64} {u : UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.rhs")
    (hpre : s.pre = some "while.body")
    (hinc : lookupName s.env "%inc456" = some (.int 64 c))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hcpos : (c.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (b + (c.signExtend 64).toNat) = some u) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (stage2SkipLandRhsCells s.env c b u) s "NodeBlock62") := by
  have hcode := stage2SkipLandRhs_denote (calls := calls) (env := s.env) (s := s)
    (c := c) (b := b) (u := u) (op := .reg "%inc456") (pre := "while.body")
    hpre stage2SkipLandRhs_incoming_whileBody
    (by simp only [stateAt, evalOperand, hinc]) hb hcpos hu
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLandRhs_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock62_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock62")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 13) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "LeafBlock53") := by
  have hcode := stage2SkipNodeBlock62_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock62_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock62_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock62")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 13) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock60") := by
  have hcode := stage2SkipNodeBlock62_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock62_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock60_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock60")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 32) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: s.env) s
        "LeafBlock56") := by
  have hcode := stage2SkipNodeBlock60_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock60_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipNodeBlock60_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock60")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .slt v (BitVec.ofNat 8 32) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: s.env) s
        "LeafBlock58") := by
  have hcode := stage2SkipNodeBlock60_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipNodeBlock60_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock58_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock58")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 32) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock58_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock58_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock58_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock58")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 32) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: s.env) s
        "while.body") := by
  have hcode := stage2SkipLeafBlock58_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock58_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock56_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock56")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 13) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock56_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock56_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock56_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock56")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .eq v (BitVec.ofNat 8 13) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: s.env) s
        "while.body") := by
  have hcode := stage2SkipLeafBlock56_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock56_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock53_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock53")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf55",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: s.env) s
        "if.end457") := by
  have hcode := stage2SkipLeafBlock53_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock53_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipLeafBlock53_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock53")
    (h58 : lookupName s.env "%58" = some (.int 8 v))
    (hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf55",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: s.env) s
        "while.body") := by
  have hcode := stage2SkipLeafBlock53_denote (calls := calls) (env := s.env) (s := s) h58
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipLeafBlock53_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipWhileBody_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c cd : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "while.body")
    (hee : lookupName s.env "%ee.01053" = some (.int 64 c))
    (hcd : lookupName s.env "%cond" = some (.int 64 cd))
    (hy : evalICmp .eq (c + BitVec.ofNat 64 1) cd = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (stage2SkipWhileBodyCells s.env c cd) s "if.end457") := by
  have hcode := stage2SkipWhileBody_denote (calls := calls) (env := s.env) (s := s) hee hcd
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipWhileBody_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

theorem link_skipWhileBody_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c cd : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "while.body")
    (hee : lookupName s.env "%ee.01053" = some (.int 64 c))
    (hcd : lookupName s.env "%cond" = some (.int 64 cd))
    (hy : evalICmp .eq (c + BitVec.ofNat 64 1) cd = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (stage2SkipWhileBodyCells s.env c cd) s "land.rhs") := by
  have hcode := stage2SkipWhileBody_denote (calls := calls) (env := s.env) (s := s) hee hcd
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by rw [hpc]; exact stage2SkipWhileBody_find) hcode rfl
    (by simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### The store's frame -/

/-- The `%k219` write is inside the cursor record.  `%k219` is `%c + 32`
(`entryA4`'s `gep`) and the record is 1192 bytes, so each of the eight bytes the
store writes lies in a staged region, which the run's own region list contains. -/
theorem stage2SkipStoreRegion {K : Stage2NoEventWalkCarry} {k219 : Nat}
    (hk : k219 = K.c + 32) :
    ∀ k, k < 8 → inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (k219 + k) := by
  intro k hk8
  refine ⟨(K.c, stage2NoEventCursorExtent), ?_, ?_, ?_⟩
  · refine List.mem_append_left _ ?_
    refine List.mem_cons_of_mem _ ?_
    refine List.mem_cons_of_mem _ ?_
    refine List.mem_cons_of_mem _ ?_
    exact List.mem_cons_self ..
  · omega
  · simp only [stage2NoEventCursorExtent]; omega

/-! ### Lookups through the builder, restated

`cells` is a right fold whose cons equation is definitional.  The canonical copy of
this lemma is `JsonStage2NoEventWalkClose`'s (private there) and
`JsonStage2NoEventWalkSegment`'s; this is the third restatement, and it is what
lets an arm transport every register the loop does not write in one step. -/

private theorem stage2SkipCells_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, w) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne w (cells cs env) hk]
      exact stage2SkipCells_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-! ### The route's frame

The scan reads a fixed register set — the entry chain's names, the scalar run's
`phi` outputs, the cursor record's index cell — and no block between
`land.lhs.true` and the merge's arms writes any of them.  `stage2SkipFrame s e`
says the exit state binds each of them as the entry did, so the arms below the
merge read the entry's values rather than re-deriving the `cells` chain. -/

/-- The registers the scan and the arms below it read and the scan does not
write, with the entry chain's stable live-ins the scan never binds.  The second
group is listed literally because this module sits below the head module; the
value module checks, by a closed computation
(`stage2NoEventWalkBaseNames_subset_skipFrame`), that the group still covers the
entry chain's table. -/
def stage2SkipFrameNames : List String :=
  ["%b", "%cond", "%idxprom.lcssa", "%inc.lcssa", "%.lcssa",
   "%arrayidx6.le1046", "%tokens.0.lcssa1073", "%terms.0.lcssa1079",
   "%frame.0.lcssa1097", "%sp.0.lcssa1091.wide", "%k219",
   "%alen.0.ph1405", "%arena.0.ph1406", "%d", "%ei",
   -- the entry chain's stable live-ins (the scan reads four of them)
   "%n", "%ep", "%nep", "%xp", "%nxp", "%scratch", "%scratchcap",
   "%tokens_out", "%values_out", "%sum_out", "%err", "%stk", "%e", "%c",
   "%invariant.gep1676", "%invariant.gep1674", "%invariant.gep1672",
   "%invariant.gep1670", "%invariant.gep1668", "%invariant.gep1666",
   "%invariant.gep1664", "%invariant.gep1662", "%invariant.gep1660",
   "%invariant.gep1658", "%invariant.gep1656", "%invariant.gep1654",
   "%invariant.gep1652", "%invariant.gep1650", "%cmp.not.peel1401.not",
   "%invariant.gep1068", "%invariant.gep", "%e3", "%nix", "%ix", "%n2",
   "%0", "%msg", "%off", "%outn205", "%outn", "%xj"]

/-- The scan's frame: every register it carries reads as it did at the entry. -/
def stage2SkipFrame (s e : State) : Prop :=
  ∀ n ∈ stage2SkipFrameNames, lookupName e.env n = lookupName s.env n

/-- The frame at one state. -/
theorem stage2SkipFrame.refl (s : State) : stage2SkipFrame s s := fun _ _ => rfl

/-- The frame composes. -/
theorem stage2SkipFrame.trans {s e f : State}
    (h₁ : stage2SkipFrame s e) (h₂ : stage2SkipFrame e f) : stage2SkipFrame s f :=
  fun n hn => (h₂ n hn).trans (h₁ n hn)

/-- The frame crosses a block's cells when they bind none of its names. -/
theorem stage2SkipFrame.mono {s e e' : State} {cs : List (String × Value)}
    (h : stage2SkipFrame s e) (henv : e'.env = cells cs e.env)
    (hnames : ∀ n ∈ stage2SkipFrameNames, n ∉ cs.map (·.1)) :
    stage2SkipFrame s e' := by
  intro n hn
  rw [henv, stage2SkipCells_notin cs n e.env (hnames n hn)]
  exact h n hn

/-- Discharging a block's "not a frame name" side condition. -/
macro "frame_names" : tactic => `(tactic|
  (intro n hn hmem
   simp only [stage2SkipFrameNames, List.mem_cons, List.not_mem_nil, or_false] at hn
   rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
   all_goals
     subst n
     simp only [List.map_cons, List.mem_cons, List.not_mem_nil, or_false] at hmem
     exact absurd hmem (by decide)))

/-! ### The loop's invariant and its exit word -/

/-- The loaded byte's class, read from the head state's `%58`. -/
def stage2SkipHeadClass (s : State) : Bool :=
  match lookupName s.env "%58" with
  | some (.int 8 v) => stage2SkipWs v
  | _ => false

/-- The head's exit test: the loaded byte is a class member, or the increment
reached `%cond`.  The loop's leaves take their true arm to the merge and their
false arm back through `while.body`, so the loop advances over non-members and
leaves on the first member at or before the bound. -/
def stage2SkipAtBound (cond : Nat) (s : State) (c : Nat) : Bool :=
  stage2SkipHeadClass s || (c + 1 == cond)

/-- The registers the loop reads and the merge's store and guard read; no block
between the head and the merge writes one of them. -/
def stage2SkipCarriedNames : List String :=
  ["%b", "%ee.01053", "%58", "%cond", "%inc.lcssa", "%.lcssa", "%k219"]

/-- **The skip loop's invariant, at a named block.**  The walk's invariant, the
registers the loop carries without writing, `%cond`'s bound, the budget
`cond ≤ c + r`, the cursor's range, the class membership of the positions the
loop has passed, and the document's byte function on the positions it may read.
`pc` is the block the state is at: the head `NodeBlock62` inside the loop, and
`while.body` between a leaf test and the increment's own test. -/
def stage2SkipInvAt (pc : String) (K : Stage2NoEventWalkCarry) (mem : Mem)
    (b idx cond : Nat) (σ : Nat → UInt8) (inc : BitVec 64) (lc : BitVec 8)
    (k219 : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = pc ∧
  Stage2NoEventWalkInv K mem s ∧
  lookupName s.env "%b" = some (.ptr b) ∧
  lookupName s.env "%ee.01053" = some (.int 64 (BitVec.ofNat 64 c)) ∧
  lookupName s.env "%58" = some (.int 8 (BitVec.ofNat 8 (σ c).toNat)) ∧
  lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)) ∧
  lookupName s.env "%inc.lcssa" = some (.int 64 inc) ∧
  lookupName s.env "%.lcssa" = some (.int 8 lc) ∧
  lookupName s.env "%k219" = some (.ptr k219) ∧
  cond < 2 ^ 63 ∧
  idx ≤ c ∧ c < cond ∧ cond ≤ c + r ∧
  (∀ j, idx ≤ j → j < c → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = false) ∧
  (∀ j, j < cond → readByte s.mem (b + j) = some (σ j))

/-- The loop's invariant at its head. -/
abbrev stage2SkipInv (K : Stage2NoEventWalkCarry) (mem : Mem) (b idx cond : Nat)
    (σ : Nat → UInt8) (inc : BitVec 64) (lc : BitVec 8) (k219 : Nat)
    (r : Nat) (s : State) (c : Nat) : Prop :=
  stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 r s c

/-- **The merge's invariant.**  `if.end457`'s `%ee.1` `phi` reads a position the
predecessor fixes, at or after `%idxprom.lcssa` and at or before `%cond`; the
three registers the merge's store and guard read are still bound. -/
def stage2SkipJoin (b idx cond : Nat) (σ : Nat → UInt8) (inc : BitVec 64)
    (lc : BitVec 8) (k219 : Nat) (e : State) : Prop :=
  e.pc = "if.end457" ∧
  (∃ (q : Nat) (op : Operand),
    phiIncoming (e.pre.getD "") stage2SkipIfEnd457EeIncoming = some op ∧
    evalOperand (stateAt e.env e) op = some (.int 64 (BitVec.ofNat 64 q)) ∧
    idx ≤ q ∧ q ≤ cond) ∧
  lookupName e.env "%inc.lcssa" = some (.int 64 inc) ∧
  lookupName e.env "%.lcssa" = some (.int 8 lc) ∧
  lookupName e.env "%k219" = some (.ptr k219)

/-- **The loop's exit word at its position**: the merge is entered from a named
predecessor with the walk's invariant intact, and the position `q` carries both
the merge's `%ee.1` selection and the first-member property. -/
def stage2SkipExitAt (K : Stage2NoEventWalkCarry) (mem : Mem) (b idx cond q : Nat)
    (σ : Nat → UInt8) (inc : BitVec 64) (lc : BitVec 8) (k219 : Nat) (e : State) : Prop :=
  e.pc = "if.end457" ∧
  Stage2NoEventWalkInv K mem e ∧
  ∃ (pre : String) (op : Operand),
    e.pre = some pre ∧
    phiIncoming pre stage2SkipIfEnd457EeIncoming = some op ∧
    evalOperand (stateAt e.env e) op = some (.int 64 (BitVec.ofNat 64 q)) ∧
    idx ≤ q ∧ q ≤ cond ∧
    (∀ j, idx ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = false) ∧
    (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (σ q).toNat) = true) ∧
    lookupName e.env "%inc.lcssa" = some (.int 64 inc) ∧
    lookupName e.env "%.lcssa" = some (.int 8 lc) ∧
    lookupName e.env "%k219" = some (.ptr k219)

/-- **The loop's exit word**: the exit state, at the position its merge selects. -/
def stage2SkipExit (K : Stage2NoEventWalkCarry) (mem : Mem) (b idx cond : Nat)
    (σ : Nat → UInt8) (inc : BitVec 64) (lc : BitVec 8) (k219 : Nat) (e : State) : Prop :=
  ∃ q, stage2SkipExitAt K mem b idx cond q σ inc lc k219 e

/-- The loop's exit word projects the merge's invariant. -/
theorem stage2SkipJoin_of_exit {e : State} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {b idx cond : Nat} {σ : Nat → UInt8} {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (h : stage2SkipExit K mem b idx cond σ inc lc k219 e) :
    stage2SkipJoin b idx cond σ inc lc k219 e := by
  obtain ⟨q, hpc, -, pre, op, hpre, hinc, hop, hidx, hcond, -, -, hincv, hlc, hk⟩ := h
  refine ⟨hpc, ⟨q, op, ?_, hop, hidx, hcond⟩, hincv, hlc, hk⟩
  rw [hpre]; exact hinc

/-- Discharging the "not a carried name" side condition of `InvAt_cells`. -/
macro "skip_names" : tactic => `(tactic|
  (intro x hx
   simp only [stage2SkipCarriedNames, List.mem_cons, List.not_mem_nil, or_false] at hx
   rcases hx with h | h | h | h | h | h | h <;> subst x <;> simp))

/-- **The invariant across cells of other names.**  Every register the loop reads
and the merge writes is untouched, so the predicate moves to the extended
environment unchanged, and the run's memory is the head's. -/
theorem stage2SkipInvAt_cells {pc pc' : String} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64} {lc : BitVec 8}
    {k219 r : Nat} {s s' : State} {cs : List (String × Value)}
    (h : stage2SkipInvAt pc K mem b idx cond σ inc lc k219 r s c)
    (hmem : s'.mem = s.mem) (hpc : s'.pc = pc') (henv : s'.env = cells cs s.env)
    (hnames : ∀ x ∈ stage2SkipCarriedNames, x ∉ cs.map (·.1)) :
    stage2SkipInvAt pc' K mem b idx cond σ inc lc k219 r s' c := by
  obtain ⟨-, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hlt, hidxle, hclt,
    hbudget, hpre, hbytes⟩ := h
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlt, hidxle, hclt, hbudget, hpre, ?_⟩
  · exact Stage2NoEventWalkInv.mem_congr (s' := s') hInv hmem
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%b" s.env
      (hnames "%b" (by simp only [stage2SkipCarriedNames]; decide))).trans hb)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%ee.01053" s.env
      (hnames "%ee.01053" (by simp only [stage2SkipCarriedNames]; decide))).trans hee)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%58" s.env
      (hnames "%58" (by simp only [stage2SkipCarriedNames]; decide))).trans h58)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%cond" s.env
      (hnames "%cond" (by simp only [stage2SkipCarriedNames]; decide))).trans hcond)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%inc.lcssa" s.env
      (hnames "%inc.lcssa" (by simp only [stage2SkipCarriedNames]; decide))).trans hincv)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%.lcssa" s.env
      (hnames "%.lcssa" (by simp only [stage2SkipCarriedNames]; decide))).trans hlc)
  · rw [henv]
    exact ((stage2SkipCells_notin cs "%k219" s.env
      (hnames "%k219" (by simp only [stage2SkipCarriedNames]; decide))).trans hk)
  · intro j hj; rw [hmem]; exact hbytes j hj

/-- **The invariant at a wider budget.**  `stage2SkipInvAt` reads its budget
argument only in `cond ≤ c + r`, so any budget that still covers the distance
from the cursor to `%cond` carries the same invariant. -/
theorem stage2SkipInvAt_budget {pc : String} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64} {lc : BitVec 8}
    {k219 r r' : Nat} {s : State}
    (h : stage2SkipInvAt pc K mem b idx cond σ inc lc k219 r s c)
    (hbudget : cond ≤ c + r') :
    stage2SkipInvAt pc K mem b idx cond σ inc lc k219 r' s c := by
  obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hlt, hidxle, hclt, -,
    hpre, hbytes⟩ := h
  exact ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hlt, hidxle, hclt, hbudget,
    hpre, hbytes⟩

/-- The merge's invariant at a cursor position, from a refusing leaf. -/
theorem stage2SkipJoin_leaf {e : State} {b idx cond q : Nat} {σ : Nat → UInt8}
    {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (hpc : e.pc = "if.end457")
    (hpre : e.pre = some "LeafBlock53" ∨ e.pre = some "LeafBlock56" ∨
      e.pre = some "LeafBlock58")
    (hee : lookupName e.env "%ee.01053" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : idx ≤ q) (hcond : q ≤ cond)
    (hincv : lookupName e.env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName e.env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName e.env "%k219" = some (.ptr k219)) :
    stage2SkipJoin b idx cond σ inc lc k219 e := by
  have hphi : phiIncoming (e.pre.getD "") stage2SkipIfEnd457EeIncoming =
      some (.reg "%ee.01053") := by
    rcases hpre with h | h | h <;> rw [h] <;> decide
  exact ⟨hpc, ⟨q, .reg "%ee.01053", hphi,
      evalOperand_reg_of e.env e "%ee.01053" (.int 64 (BitVec.ofNat 64 q)) hee,
      hidx, hcond⟩, hincv, hlc, hk⟩

/-- The merge's invariant at `%cond`, from the exhausted increment. -/
theorem stage2SkipJoin_whileBody {e : State} {b idx cond : Nat} {σ : Nat → UInt8}
    {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (hpc : e.pc = "if.end457") (hpre : e.pre = some "while.body")
    (hcd : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hidx : idx ≤ cond)
    (hincv : lookupName e.env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName e.env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName e.env "%k219" = some (.ptr k219)) :
    stage2SkipJoin b idx cond σ inc lc k219 e := by
  have hphi : phiIncoming (e.pre.getD "") stage2SkipIfEnd457EeIncoming =
      some (.reg "%cond") := by
    rw [hpre]; decide
  exact ⟨hpc, ⟨cond, .reg "%cond", hphi,
      evalOperand_reg_of e.env e "%cond" (.int 64 (BitVec.ofNat 64 cond)) hcd,
      hidx, Nat.le_refl _⟩, hincv, hlc, hk⟩


/-! ### The preheader state

`land.rhs.preheader` has no instructions: it is the loop's entry, and the facts
the loop is seeded with are the ones the first test carries to it. -/

/-- The state `land.rhs.preheader` is entered with: the loop's entry facts. -/
def stage2SkipPre (b idx cond : Nat) (σ : Nat → UInt8) (inc : BitVec 64)
    (lc : BitVec 8) (k219 : Nat) (e : State) : Prop :=
  e.pc = "land.rhs.preheader" ∧
  lookupName e.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)) ∧
  lookupName e.env "%b" = some (.ptr b) ∧
  lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)) ∧
  lookupName e.env "%inc.lcssa" = some (.int 64 inc) ∧
  lookupName e.env "%.lcssa" = some (.int 8 lc) ∧
  lookupName e.env "%k219" = some (.ptr k219)

/-! ### The head's two block paths -/

/-- **`NodeBlock62` to `while.body` on a class member.**  Three pivot cases, each
ending at the increment block with the cursor unchanged. -/
theorem stage2SkipAdvance {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {r : Nat}
    (h : stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 r s c)
    (hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false) :
    ∃ (e : State) (j : Nat), j ≤ 3 ∧
      stage2SkipInvAt "while.body" K mem b idx cond σ inc lc k219 r e c ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s e := by
  have hh := h
  obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt, -,
    hpre, hbytes⟩ := h
  let v : BitVec 8 := BitVec.ofNat 8 (σ c).toNat
  have hv : v = BitVec.ofNat 8 (σ c).toNat := rfl
  rw [← hv] at hws h58
  by_cases h13 : v.slt (BitVec.ofNat 8 13) = true
  · have hleaf : (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) = false := by
      rw [← stage2SkipLeaf_slt13_true h13, stage2SkipLeaf_eq_ws]; exact hws
    let S1 : State := stage2NoEventWalkNext
      (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s "LeafBlock53"
    have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
      link_skipNodeBlock62_true hInv hpc h58 (by
        show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 1
        rw [h13]; rfl)
    have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
      simp only [S1, stage2NoEventWalkNext]; skip_lk
    let S2 : State := stage2NoEventWalkNext
      (("%SwitchLeaf55", .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))) ::
        ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: S1.env) S1 "while.body"
    have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
      link_skipLeafBlock53_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
        h58₁ (stage2Skip_ule_zero_of hleaf)
    have henv : S2.env = cells
        [("%SwitchLeaf55", .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1))),
         ("%.off54", .int 8 (v + BitVec.ofNat 8 247)),
         ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))] s.env := rfl
    refine ⟨S2, 2, by omega, ?_, stage2SkipRun2 L1 L2,
      (by simp only [S2, S1, stage2NoEventWalkNext]),
      stage2SkipFrame.mono (stage2SkipFrame.refl s) henv (by frame_names)⟩
    exact stage2SkipInvAt_cells
      (cs := [("%SwitchLeaf55", .int 1 (evalICmp .ule
          (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
        ("%.off54", .int 8 (v + BitVec.ofNat 8 247)),
        ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
      hh (by rfl) (by rfl) henv (by skip_names)
  · have h13f : v.slt (BitVec.ofNat 8 13) = false := by
      cases h : v.slt (BitVec.ofNat 8 13) <;> simp_all
    by_cases h32 : v.slt (BitVec.ofNat 8 32) = true
    · have hleaf : (v == BitVec.ofNat 8 13) = false := by
        rw [← stage2SkipLeaf_slt32_true h13f h32, stage2SkipLeaf_eq_ws]; exact hws
      let S1 : State := stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock60"
      have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
        link_skipNodeBlock62_false hInv hpc h58 (by
          show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0
          rw [h13f]; rfl)
      have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
        simp only [S1, stage2NoEventWalkNext]; skip_lk
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S1.env) S1
        "LeafBlock56"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock60_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h58₁
          (by
            show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 1
            rw [h32]; rfl)
      have h58₂ : lookupName S2.env "%58" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: S2.env) S2
        "while.body"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock56_false L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h58₂ (stage2Skip_beq_zero_of hleaf)
      have henv : S3.env = cells
          [("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))),
           ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
           ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))] s.env := rfl
      refine ⟨S3, 3, by omega, ?_, stage2SkipRun3 L1 L2 L3,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]),
        stage2SkipFrame.mono (stage2SkipFrame.refl s) henv (by frame_names)⟩
      exact stage2SkipInvAt_cells
        (cs := [("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))),
          ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
          ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
        hh (by rfl) (by rfl) henv (by skip_names)
    · have h32f : v.slt (BitVec.ofNat 8 32) = false := by
        cases h : v.slt (BitVec.ofNat 8 32) <;> simp_all
      have hleaf : (v == BitVec.ofNat 8 32) = false := by
        rw [← stage2SkipLeaf_slt32_false h13f h32f, stage2SkipLeaf_eq_ws]; exact hws
      let S1 : State := stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock60"
      have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
        link_skipNodeBlock62_false hInv hpc h58 (by
          show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0
          rw [h13f]; rfl)
      have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
        simp only [S1, stage2NoEventWalkNext]; skip_lk
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S1.env) S1
        "LeafBlock58"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock60_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
          h58₁ (by
            show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 0
            rw [h32f]; rfl)
      have h58₂ : lookupName S2.env "%58" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: S2.env) S2
        "while.body"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock58_false L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h58₂ (stage2Skip_beq_zero_of hleaf)
      have henv : S3.env = cells
          [("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))),
           ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
           ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))] s.env := rfl
      refine ⟨S3, 3, by omega, ?_, stage2SkipRun3 L1 L2 L3,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]),
        stage2SkipFrame.mono (stage2SkipFrame.refl s) henv (by frame_names)⟩
      exact stage2SkipInvAt_cells
        (cs := [("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))),
          ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
          ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
        hh (by rfl) (by rfl) henv (by skip_names)

/-- **`NodeBlock62` to the merge on a class member.**  The same three pivots, each
leaf's true arm taken, ending at `if.end457` with the loop's exit word. -/
theorem stage2SkipStop {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {r : Nat}
    (h : stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 r s c)
    (hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = true) :
    ∃ (e : State) (j : Nat), j ≤ 3 ∧
      stage2SkipExitAt K mem b idx cond c σ inc lc k219 e ∧
      Stage2NoEventWalkInv K mem e ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s e := by
  obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt, -,
    hpre, hbytes⟩ := h
  have hexit : ∀ (e : State) (pre : String) (q : Nat), e.pc = "if.end457" →
      e.pre = some pre → Stage2NoEventWalkInv K mem e →
      (pre = "LeafBlock53" ∨ pre = "LeafBlock56" ∨ pre = "LeafBlock58") →
      lookupName e.env "%ee.01053" = some (.int 64 (BitVec.ofNat 64 q)) →
      idx ≤ q → q ≤ cond →
      lookupName e.env "%inc.lcssa" = some (.int 64 inc) →
      lookupName e.env "%.lcssa" = some (.int 8 lc) →
      lookupName e.env "%k219" = some (.ptr k219) →
      (∀ j, idx ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = false) →
      stage2SkipWs (BitVec.ofNat 8 (σ q).toNat) = true →
      stage2SkipExitAt K mem b idx cond q σ inc lc k219 e := by
    intro e pre q hpc' hpre' hinv' hmem hee' hidx' hq' hinc' hlc' hk' hprefix hstop
    have hphi : phiIncoming pre stage2SkipIfEnd457EeIncoming =
        some (.reg "%ee.01053") := by
      rcases hmem with h' | h' | h' <;> rw [h'] <;> decide
    exact ⟨hpc', hinv', pre, .reg "%ee.01053", hpre', hphi,
      evalOperand_reg_of e.env e "%ee.01053" (.int 64 (BitVec.ofNat 64 q)) hee',
      hidx', hq', hprefix, Or.inr hstop, hinc', hlc', hk'⟩
  let v : BitVec 8 := BitVec.ofNat 8 (σ c).toNat
  have hv : v = BitVec.ofNat 8 (σ c).toNat := rfl
  rw [← hv] at hws h58
  by_cases h13 : v.slt (BitVec.ofNat 8 13) = true
  · have hleaf : (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) = true := by
      rw [← stage2SkipLeaf_slt13_true h13, stage2SkipLeaf_eq_ws]; exact hws
    let S1 : State := stage2NoEventWalkNext
      (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s "LeafBlock53"
    have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
      link_skipNodeBlock62_true hInv hpc h58 (by
        show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 1
        rw [h13]; rfl)
    have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
      simp only [S1, stage2NoEventWalkNext]; skip_lk
    let S2 : State := stage2NoEventWalkNext
      (("%SwitchLeaf55", .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))) ::
        ("%.off54", .int 8 (v + BitVec.ofNat 8 247)) :: S1.env) S1 "if.end457"
    have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
      link_skipLeafBlock53_true L1.inv' (by simp only [S1, stage2NoEventWalkNext])
        h58₁ (stage2Skip_ule_one_of hleaf)
    refine ⟨S2, 2, by omega, ?_, L2.inv', stage2SkipRun2 L1 L2,
      (by simp only [S2, S1, stage2NoEventWalkNext]),
      stage2SkipFrame.mono (stage2SkipFrame.refl s)
        (cs := [("%SwitchLeaf55", .int 1 (evalICmp .ule
            (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
          ("%.off54", .int 8 (v + BitVec.ofNat 8 247)),
          ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
        (by simp only [S2, S1, stage2NoEventWalkNext, cells]) (by frame_names)⟩
    exact hexit S2 "LeafBlock53" c (by simp only [S2, stage2NoEventWalkNext])
      (by simp only [S2, S1, stage2NoEventWalkNext]) L2.inv' (Or.inl rfl)
      (by simp only [S2, stage2NoEventWalkNext]; skip_lk)
      hidxle (by omega)
      (by simp only [S2, stage2NoEventWalkNext]; skip_lk)
      (by simp only [S2, stage2NoEventWalkNext]; skip_lk)
      (by simp only [S2, stage2NoEventWalkNext]; skip_lk)
      (fun j hj hjlt => hpre j hj hjlt) hws
  · have h13f : v.slt (BitVec.ofNat 8 13) = false := by
      cases h : v.slt (BitVec.ofNat 8 13) <;> simp_all
    by_cases h32 : v.slt (BitVec.ofNat 8 32) = true
    · have hleaf : (v == BitVec.ofNat 8 13) = true := by
        rw [← stage2SkipLeaf_slt32_true h13f h32, stage2SkipLeaf_eq_ws]; exact hws
      let S1 : State := stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock60"
      have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
        link_skipNodeBlock62_false hInv hpc h58 (by
          show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0
          rw [h13f]; rfl)
      have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
        simp only [S1, stage2NoEventWalkNext]; skip_lk
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S1.env) S1
        "LeafBlock56"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock60_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h58₁
          (by
            show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 1
            rw [h32]; rfl)
      have h58₂ : lookupName S2.env "%58" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: S2.env) S2
        "if.end457"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock56_true L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h58₂ (stage2Skip_beq_one_of hleaf)
      refine ⟨S3, 3, by omega, ?_, L3.inv', stage2SkipRun3 L1 L2 L3,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]),
        stage2SkipFrame.mono (stage2SkipFrame.refl s)
          (cs := [("%SwitchLeaf57", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))),
            ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
            ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
          (by simp only [S3, S2, S1, stage2NoEventWalkNext, cells])
          (by frame_names)⟩
      exact hexit S3 "LeafBlock56" c (by simp only [S3, stage2NoEventWalkNext])
        (by simp only [S3, S2, stage2NoEventWalkNext]) L3.inv' (Or.inr (Or.inl rfl))
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        hidxle (by omega)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (fun j hj hjlt => hpre j hj hjlt) hws
    · have h32f : v.slt (BitVec.ofNat 8 32) = false := by
        cases h : v.slt (BitVec.ofNat 8 32) <;> simp_all
      have hleaf : (v == BitVec.ofNat 8 32) = true := by
        rw [← stage2SkipLeaf_slt32_false h13f h32f, stage2SkipLeaf_eq_ws]; exact hws
      let S1 : State := stage2NoEventWalkNext
        (("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: s.env) s
        "NodeBlock60"
      have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
        link_skipNodeBlock62_false hInv hpc h58 (by
          show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0
          rw [h13f]; rfl)
      have h58₁ : lookupName S1.env "%58" = some (.int 8 v) := by
        simp only [S1, stage2NoEventWalkNext]; skip_lk
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S1.env) S1
        "LeafBlock58"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock60_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
          h58₁ (by
            show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 0
            rw [h32f]; rfl)
      have h58₂ : lookupName S2.env "%58" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: S2.env) S2
        "if.end457"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock58_true L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h58₂ (stage2Skip_beq_one_of hleaf)
      refine ⟨S3, 3, by omega, ?_, L3.inv', stage2SkipRun3 L1 L2 L3,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]),
        stage2SkipFrame.mono (stage2SkipFrame.refl s)
          (cs := [("%SwitchLeaf59", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))),
            ("%Pivot61", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))),
            ("%Pivot63", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
          (by simp only [S3, S2, S1, stage2NoEventWalkNext, cells])
          (by frame_names)⟩
      exact hexit S3 "LeafBlock58" c (by simp only [S3, stage2NoEventWalkNext])
        (by simp only [S3, S2, stage2NoEventWalkNext]) L3.inv' (Or.inr (Or.inr rfl))
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        hidxle (by omega)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (by simp only [S3, stage2NoEventWalkNext]; skip_lk)
        (fun j hj hjlt => hpre j hj hjlt) hws

/-! ### The increment block's two tails -/

/-- The increment reached `%cond`: the loop exits at the merge. -/
theorem stage2SkipWhileBodyExit {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {r : Nat}
    (h : stage2SkipInvAt "while.body" K mem b idx cond σ inc lc k219 r s c)
    (htest : (c + 1 == cond) = true) (hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false) :
    ∃ (e : State), stage2SkipExitAt K mem b idx cond cond σ inc lc k219 e ∧
      Stage2NoEventWalkInv K mem e ∧
      (∀ n, runFuel calls (1 + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s e := by
  obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt,
    hbudget, hpre, hbytes⟩ := h
  have hce : c + 1 = cond := by simpa using htest
  have hy : evalICmp .eq (BitVec.ofNat 64 c + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 cond) = 1 := by
    rw [stage2Skip_ofNat_succ (by omega : c + 1 < 2 ^ 64)]
    exact stage2Skip_eq_ofNat_one hce
  let S1 : State := stage2NoEventWalkNext
    (stage2SkipWhileBodyCells s.env (BitVec.ofNat 64 c) (BitVec.ofNat 64 cond)) s
    "if.end457"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_skipWhileBody_true hInv hpc hee hcond hy
  refine ⟨S1, ?_, L1.inv', ?_,
    (by simp only [S1, stage2NoEventWalkNext]), ?_⟩
  · refine ⟨by simp only [S1, stage2NoEventWalkNext], L1.inv', "while.body",
      .reg "%cond", by simp only [S1, stage2NoEventWalkNext, hpc], ?_, ?_, by omega, by omega,
      ?_, Or.inl rfl,
      by simp only [S1, stage2NoEventWalkNext]; skip_lk,
      by simp only [S1, stage2NoEventWalkNext]; skip_lk,
      by simp only [S1, stage2NoEventWalkNext]; skip_lk⟩
    · decide
    · exact evalOperand_reg_of S1.env S1 "%cond"
        (.int 64 (BitVec.ofNat 64 cond)) (by
          simp only [S1, stage2NoEventWalkNext]; skip_lk)
    · intro j hj hjlt
      rcases Nat.lt_or_ge j c with h' | h'
      · exact hpre j hj h'
      · have hj' : j = c := by omega
        subst hj'
        exact hws
  · intro n
    exact stage2NoEventWalkLink_runFuel L1 n
  · exact stage2SkipFrame.mono (stage2SkipFrame.refl s)
      (cs := stage2SkipWhileBodyCells [] (BitVec.ofNat 64 c) (BitVec.ofNat 64 cond))
      (by simp only [S1, stage2NoEventWalkNext, stage2SkipWhileBodyCells, cells])
      (by frame_names)

/-- The increment is short of `%cond`: the loop re-enters the head, one budget
unit spent. -/
theorem stage2SkipWhileBodyContinue {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {r : Nat}
    (h : stage2SkipInvAt "while.body" K mem b idx cond σ inc lc k219 (r + 1) s c)
    (hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false)
    (htest : (c + 1 == cond) = false) :
    ∃ (e : State), stage2SkipInv K mem b idx cond σ inc lc k219 r e (c + 1) ∧
      (∀ n, runFuel calls (2 + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s e := by
  obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt,
    hbudget, hpre, hbytes⟩ := h
  have hne : c + 1 ≠ cond := by
    intro hc
    have h1 : (c + 1 == cond) = true := by simpa using hc
    rw [h1] at htest
    exact absurd htest (by decide)
  have hc1 : c + 1 < 2 ^ 64 := by omega
  have hy : evalICmp .eq (BitVec.ofNat 64 c + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 cond) = 0 := by
    rw [stage2Skip_ofNat_succ hc1]
    exact stage2Skip_eq_ofNat_zero (by omega) (by omega) hne
  let S1 : State := stage2NoEventWalkNext
    (stage2SkipWhileBodyCells s.env (BitVec.ofNat 64 c) (BitVec.ofNat 64 cond)) s
    "land.rhs"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_skipWhileBody_false hInv hpc hee hcond hy
  have hinc₁ : lookupName S1.env "%inc456" =
      some (.int 64 (BitVec.ofNat 64 (c + 1))) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self,
      stage2Skip_ofNat_succ hc1]
  have hb₁ : lookupName S1.env "%b" = some (.ptr b) := by
    simp only [S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hbyte : readByte S1.mem (b + (c + 1)) = some (σ (c + 1)) := by
    have hm : S1.mem = s.mem := rfl
    rw [hm]
    exact hbytes (c + 1) (by omega)
  let S2 : State := stage2NoEventWalkNext
    (stage2SkipLandRhsCells S1.env (BitVec.ofNat 64 (c + 1)) b (σ (c + 1))) S1
    "NodeBlock62"
  have hpos : ((BitVec.ofNat 64 (c + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc1]
    omega
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_skipLandRhs_whileBody L1.inv' (by simp only [S1, stage2NoEventWalkNext])
      (by simp only [S1, stage2NoEventWalkNext, hpc]) hinc₁ hb₁ hpos (by
        simpa only [stage2NoEventSignExtend_self, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hc1] using hbyte)
  refine ⟨S2, ?_, stage2SkipRun2 L1 L2,
    (by simp only [S2, S1, stage2NoEventWalkNext]), ?_⟩
  refine ⟨by simp only [S2, stage2NoEventWalkNext], L2.inv', ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hcondlt, by omega, by omega, by omega, ?_, ?_⟩
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · simp only [S2, stage2NoEventWalkNext]; rw [lookupName_cons_self]
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · simp only [S2, stage2NoEventWalkNext]; skip_lk
  · intro j hj hjlt
    rcases Nat.lt_or_ge j c with h' | h'
    · exact hpre j hj h'
    · have hj' : j = c := by omega
      subst hj'
      exact hws
  · intro j hj
    have hm2 : S2.mem = s.mem := by simp only [S2, S1, stage2NoEventWalkNext]
    rw [hm2]
    exact hbytes j (by omega)
  · have h1 : stage2SkipFrame s S1 :=
      stage2SkipFrame.mono (stage2SkipFrame.refl s)
        (cs := stage2SkipWhileBodyCells [] (BitVec.ofNat 64 c) (BitVec.ofNat 64 cond))
        (by simp only [S1, stage2NoEventWalkNext, stage2SkipWhileBodyCells, cells])
        (by frame_names)
    have h2 : stage2SkipFrame S1 S2 :=
      stage2SkipFrame.mono (stage2SkipFrame.refl S1)
        (cs := stage2SkipLandRhsCells [] (BitVec.ofNat 64 (c + 1)) b (σ (c + 1)))
        (by simp only [S2, stage2NoEventWalkNext, stage2SkipLandRhsCells, cells])
        (by frame_names)
    exact stage2SkipFrame.trans h1 h2

/-! ### The loop -/

/-- The skip loop, as `LoopFuel.BoundLoop`: the head is `NodeBlock62`, the bound
`%cond`, the exit test `stage2SkipAtBound`, and the exit word the loop's own. -/
def stage2SkipLoop (calls : Calls) (K : Stage2NoEventWalkCarry) (mem : Mem)
    (b idx cond : Nat) (σ : Nat → UInt8) (inc : BitVec 64) (lc : BitVec 8)
    (k219 : Nat) (M : Mem) (s0 : State) : BoundLoop calls stage2NoEventBody where
  head := "NodeBlock62"
  exitBlock := "if.end457"
  N := cond
  cost := 5
  Inv := fun r s c =>
    stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 r s c ∧ s.mem = M ∧
      stage2SkipFrame s0 s
  atBound := fun s c => stage2SkipAtBound cond s c
  ExitWord := fun e =>
    stage2SkipExit K mem b idx cond σ inc lc k219 e ∧ e.mem = M ∧ stage2SkipFrame s0 e
  step_exit := by
    intro r s c h hb
    obtain ⟨hinv, hmem, hfr⟩ := h
    have hinv0 := hinv
    obtain ⟨hpc, hInv, hbreg, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt, -,
      hpre, hbytes⟩ := hinv
    cases hcls : stage2SkipHeadClass s
    · have hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false := by
        simpa only [stage2SkipHeadClass, h58] using hcls
      have heq : (c + 1 == cond) = true := by
        have h1 : (false || (c + 1 == cond)) = true := by
          simpa only [stage2SkipAtBound, hcls] using hb
        simpa only [Bool.false_or] using h1
      obtain ⟨e₁, j₁, hj₁, hinv₁, hrun₁, hme₁, hfr₁⟩ := stage2SkipAdvance hinv0 hws
      obtain ⟨e₂, hexit₂, hinv₂, hrun₂, hme₂, hfr₂⟩ :=
        stage2SkipWhileBodyExit hinv₁ heq hws
      refine ⟨e₂, j₁ + 1, by omega, hexit₂.1, ⟨⟨cond, hexit₂⟩, ?_, ?_⟩, ?_⟩
      · rw [hme₂, hme₁, hmem]
      · exact stage2SkipFrame.trans hfr (stage2SkipFrame.trans hfr₁ hfr₂)
      · intro n
        rw [show j₁ + 1 + n = j₁ + (1 + n) from by omega, hrun₁ (1 + n), hrun₂ n]
    · have hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = true := by
        simpa only [stage2SkipHeadClass, h58] using hcls
      obtain ⟨e, j, hj, hexit, hinv, hrun, hme, hfr'⟩ := stage2SkipStop hinv0 hws
      exact ⟨e, j, by omega, hexit.1,
        ⟨⟨c, hexit⟩, by rw [hme, hmem], stage2SkipFrame.trans hfr hfr'⟩, hrun⟩
  step_loop := by
    intro r s c h hb
    obtain ⟨hinv, hmem, hfr⟩ := h
    have hinv0 := hinv
    obtain ⟨hpc, hInv, hbreg, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt, -,
      hpre, hbytes⟩ := hinv
    cases hcls : stage2SkipHeadClass s
    · have hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false := by
        simpa only [stage2SkipHeadClass, h58] using hcls
      have hne : (c + 1 == cond) = false := by
        have h1 : (false || (c + 1 == cond)) = false := by
          simpa only [stage2SkipAtBound, hcls] using hb
        simpa only [Bool.false_or] using h1
      obtain ⟨e₁, j₁, hj₁, hinv₁, hrun₁, hme₁, hfr₁⟩ := stage2SkipAdvance hinv0 hws
      obtain ⟨e₂, hinv₂, hrun₂, hme₂, hfr₂⟩ :=
        stage2SkipWhileBodyContinue hinv₁ hws hne
      refine ⟨e₂, c + 1, j₁ + 2, by omega, hinv₂.1, by omega,
        ⟨hinv₂, ?_, stage2SkipFrame.trans hfr (stage2SkipFrame.trans hfr₁ hfr₂)⟩, ?_⟩
      · rw [hme₂, hme₁, hmem]
      · intro n
        rw [show j₁ + 2 + n = j₁ + (2 + n) from by omega, hrun₁ (2 + n), hrun₂ n]
    · have h1 : (true || (c + 1 == cond)) = false := by
        simpa only [stage2SkipAtBound, hcls] using hb
      exact absurd h1 (by simp)
  exit_at_zero := by
    intro s c h
    obtain ⟨hinv, -, -⟩ := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hclt, hbudget, -⟩ := hinv
    exact absurd hbudget (by omega)
  budget := by
    intro r s c h
    obtain ⟨hinv, -, -⟩ := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hclt, hbudget, -⟩ := hinv
    exact ⟨by omega, hbudget⟩

/-- **The loop from its head**, at the whole budget: the run reaches the merge
within `(%cond + 1) * 5` steps, leaving the loop's exit word. -/
theorem stage2SkipLoop_run {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {b idx cond : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {M : Mem}
    (s0 : State) (hfr : stage2SkipFrame s0 s)
    (h : stage2SkipInv K mem b idx cond σ inc lc k219 cond s idx)
    (hmem : s.mem = M) :
    ∃ (e : State) (j : Nat), j ≤ (cond + 1) * 5 ∧
      stage2SkipExit K mem b idx cond σ inc lc k219 e ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s0 e := by
  let L : BoundLoop calls stage2NoEventBody :=
    stage2SkipLoop calls K mem b idx cond σ inc lc k219 M s0
  have hL : stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 cond s idx ∧
      s.mem = M ∧ stage2SkipFrame s0 s := ⟨h, hmem, hfr⟩
  obtain ⟨e, j, hj, hexitPc, hexitWord, hrun⟩ := L.run_from L.N s idx hL
  obtain ⟨hexit, hme, hfr'⟩ : stage2SkipExit K mem b idx cond σ inc lc k219 e ∧
      e.mem = M ∧ stage2SkipFrame s0 e := hexitWord
  refine ⟨e, j, ?_, hexit, hrun, ?_, hfr'⟩
  · simpa only [L, stage2SkipLoop] using hj
  · rw [hme, hmem]

/-- **The loop's run at its own trip count.**  From the head at `idx` the loop
reaches its merge at the exit position `q` — the cursor the test left from —
within `5 * (q - idx) + 4` steps: every back edge spends at most five steps and
advances the cursor by at least one, and the exit iteration spends at most four.
The position is exposed, so a caller's count is relative to the loop's own exit
rather than to the bound `%cond`. -/
theorem stage2SkipLoop_run_at {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {b idx cond : Nat} {σ : Nat → UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat} {M : Mem}
    (s0 : State) (hfr : stage2SkipFrame s0 s)
    (h : stage2SkipInv K mem b idx cond σ inc lc k219 cond s idx)
    (hmem : s.mem = M) :
    ∃ (e : State) (j q : Nat), j ≤ 5 * (q - idx) + 4 ∧ idx ≤ q ∧
      stage2SkipExitAt K mem b idx cond q σ inc lc k219 e ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ e.mem = s.mem ∧
      stage2SkipFrame s0 e := by
  have key : ∀ (r : Nat) (s : State) (c : Nat),
      stage2SkipInvAt "NodeBlock62" K mem b idx cond σ inc lc k219 r s c →
      s.mem = M → stage2SkipFrame s0 s →
      ∃ (e : State) (j q : Nat), j ≤ 5 * (q - c) + 4 ∧ c ≤ q ∧
        stage2SkipExitAt K mem b idx cond q σ inc lc k219 e ∧
        (∀ n, runFuel calls (j + n) stage2NoEventBody s =
          runFuel calls n stage2NoEventBody e) ∧ e.mem = M ∧
        stage2SkipFrame s0 e := by
    intro r
    induction r with
    | zero =>
        intro s c hinv hmem hf
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hclt, hbudget, -, -⟩ := hinv
        omega
    | succ r ih =>
        intro s c hinv hmem hf
        have hinv0 := hinv
        obtain ⟨hpc, hInv, hb, hee, h58, hcond, hincv, hlc, hk, hcondlt, hidxle, hclt,
          hbudget, hpre, hbytes⟩ := hinv
        cases hcls : stage2SkipHeadClass s
        · have hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = false := by
            simpa only [stage2SkipHeadClass, h58] using hcls
          by_cases htest : (c + 1 == cond) = true
          · obtain ⟨e₁, j₁, hj₁, hinv₁, hrun₁, hme₁, hfr₁⟩ :=
              stage2SkipAdvance hinv0 hws
            obtain ⟨e₂, hexit₂, hinv₂, hrun₂, hme₂, hfr₂⟩ :=
              stage2SkipWhileBodyExit hinv₁ htest hws
            refine ⟨e₂, j₁ + 1, cond, ?_, by omega, hexit₂, ?_, ?_, ?_⟩
            · omega
            · intro n
              rw [show j₁ + 1 + n = j₁ + (1 + n) from by omega,
                hrun₁ (1 + n), hrun₂ n]
            · rw [hme₂, hme₁, hmem]
            · exact stage2SkipFrame.trans hf (stage2SkipFrame.trans hfr₁ hfr₂)
          · have hne : (c + 1 == cond) = false := by
              cases h : (c + 1 == cond) <;> simp_all
            obtain ⟨e₁, j₁, hj₁, hinv₁, hrun₁, hme₁, hfr₁⟩ :=
              stage2SkipAdvance hinv0 hws
            obtain ⟨e₂, hinv₂, hrun₂, hme₂, hfr₂⟩ :=
              stage2SkipWhileBodyContinue hinv₁ hws hne
            obtain ⟨e, j, q, hj, hcq, hexit, hrun', hme', hfr'⟩ :=
              ih e₂ (c + 1) hinv₂ (by rw [hme₂, hme₁, hmem])
                (stage2SkipFrame.trans hf (stage2SkipFrame.trans hfr₁ hfr₂))
            refine ⟨e, j₁ + 2 + j, q, ?_, by omega, hexit, ?_, hme', hfr'⟩
            · omega
            · intro n
              rw [show j₁ + 2 + j + n = j₁ + (2 + (j + n)) from by omega,
                hrun₁ (2 + (j + n)), hrun₂ (j + n), hrun' n]
        · have hws : stage2SkipWs (BitVec.ofNat 8 (σ c).toNat) = true := by
            simpa only [stage2SkipHeadClass, h58] using hcls
          obtain ⟨e, j, hj, hexit, hinv', hrun, hme, hfr'⟩ := stage2SkipStop hinv0 hws
          refine ⟨e, j, c, ?_, le_rfl, hexit, hrun, ?_, ?_⟩
          · omega
          · rw [hme, hmem]
          · exact stage2SkipFrame.trans hf hfr'
  obtain ⟨e, j, q, hj, hq, hexit, hrun, hme, hfr'⟩ := key cond s idx h hmem hfr
  exact ⟨e, j, q, hj, hq, hexit, hrun, hme.trans hmem.symm, hfr'⟩

/-- **The merge's one step**, from its invariant: the `%ee.1` selection, the
`%k219` store, the number-or-minus guard, and the arm it selects. -/
theorem stage2SkipJoinRun {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {b idx cond q : Nat} {σ : Nat → UInt8} {op : Operand}
    {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end457")
    (hinc : phiIncoming (s.pre.getD "") stage2SkipIfEnd457EeIncoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 q)))
    (hincv : lookupName s.env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName s.env "%k219" = some (.ptr k219)) (hstore : k219 = K.c + 32) :
    ∃ (e : State),
      (e.pc = "if.then471" ∨ e.pc = "if.else495") ∧
      lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      Stage2NoEventWalkInv K mem e ∧
      e.mem = writeBytes s.mem k219 (natToBytes inc.toNat 8) ∧
      (∀ n, runFuel calls (1 + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧
      stage2SkipFrame s e := by
  have hcode : denoteCode calls stage2SkipIfEnd457Instrs (stateAt s.env s) =
      some (stateAt (stage2SkipIfEnd457Cells s.env q lc)
        (stage2NoEventStepState s (writeBytes s.mem k219 (natToBytes inc.toNat 8))
          s.next)) := by
    cases hp : s.pre with
    | none =>
        rw [hp] at hinc
        simp only [Option.getD_none] at hinc
        have hnone : phiIncoming "" stage2SkipIfEnd457EeIncoming = none := by decide
        rw [hnone] at hinc
        exact absurd hinc (by simp)
    | some pre =>
        simp only [hp, Option.getD_some] at hinc
        exact stage2SkipIfEnd457_denote (calls := calls) (env := s.env) (s := s)
          hp hinc hop hincv hlc hk
  let mid : State :=
    stage2NoEventStepState s (writeBytes s.mem k219 (natToBytes inc.toNat 8)) s.next
  have hmid : mid =
      stage2NoEventStepState s (writeBytes s.mem k219 (natToBytes inc.toNat 8)) s.next := rfl
  have hinv' : Stage2NoEventWalkInv K mem mid :=
    Stage2NoEventWalkInv.mem_congr (s' := mid)
      (Stage2NoEventWalkInv.stack_write (h := h) (a := k219)
        (bs := natToBytes inc.toNat 8) (stage2SkipStoreRegion hstore)) (by rfl)
  have hmem : mid.mem = writeBytes s.mem k219 (natToBytes inc.toNat 8) := rfl
  let env' : Env := stage2SkipIfEnd457Cells s.env q lc
  have henv' : env' = stage2SkipIfEnd457Cells s.env q lc := rfl
  have hval : lookupName env' "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) := by
    simp only [henv', stage2SkipIfEnd457Cells]
    skip_lk
  have hframe : ∀ pc : String,
      stage2SkipFrame s (stage2NoEventWalkNext env' mid pc) := by
    intro pc
    exact stage2SkipFrame.mono (stage2SkipFrame.refl s)
      (cs := stage2SkipIfEnd457Cells [] q lc)
      (by simp only [env', stage2NoEventWalkNext, stage2SkipIfEnd457Cells, cells])
      (by frame_names)
  rcases bitVec1_eq_zero_or_one (evalICmp .eq lc (BitVec.ofNat 8 45) |||
    evalICmp .ult (lc + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) with hg | hg
  · refine ⟨stage2NoEventWalkNext env' mid "if.else495", Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stage2NoEventWalkNext] using hval
    · exact Stage2NoEventWalkInv.mem_congr (s' :=
        stage2NoEventWalkNext env' mid "if.else495") hinv' (by
          simp only [stage2NoEventWalkNext])
    · simpa only [stage2NoEventWalkNext] using hmem
    · intro n
      have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody) (s := s)
        (b := ⟨"if.end457", stage2SkipIfEnd457Instrs,
          Term.condbr (Operand.reg "%or.cond901") "if.then471" "if.else495"⟩)
        (by rw [hpc]; exact stage2SkipIfEnd457_find) hcode rfl
        (by simp only [henv', stage2SkipIfEnd457Cells, stateAt, lookupName_cons_self, hg])
      rw [show 1 + n = n + 1 from by omega]
      simp only [runFuel, hstep]
      rfl
    · exact hframe "if.else495"
  · refine ⟨stage2NoEventWalkNext env' mid "if.then471", Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stage2NoEventWalkNext] using hval
    · exact Stage2NoEventWalkInv.mem_congr (s' :=
        stage2NoEventWalkNext env' mid "if.then471") hinv' (by
          simp only [stage2NoEventWalkNext])
    · simpa only [stage2NoEventWalkNext] using hmem
    · intro n
      have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody) (s := s)
        (b := ⟨"if.end457", stage2SkipIfEnd457Instrs,
          Term.condbr (Operand.reg "%or.cond901") "if.then471" "if.else495"⟩)
        (by rw [hpc]; exact stage2SkipIfEnd457_find) hcode rfl
        (by simp only [henv', stage2SkipIfEnd457Cells, stateAt, lookupName_cons_self, hg])
      rw [show 1 + n = n + 1 from by omega]
      simp only [runFuel, hstep]
      rfl
    · exact hframe "if.then471"

/-! ### The first test -/

/-- **`land.lhs.true` to the preheader or the merge.**  The probe's byte decides:
a class member enters the loop at `land.rhs.preheader`; a non-member goes
straight to the merge, whose `%ee.1` selection is `%cond`, and the probe's byte
is carried as the non-member it is. -/
theorem stage2SkipFirstTest {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {g b idx cond : Nat} {σ : Nat → UInt8} {u0 : UInt8} {inc : BitVec 64}
    {lc : BitVec 8} {k219 : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.lhs.true")
    (hg : lookupName s.env "%invariant.gep1068" = some (.ptr g))
    (hc : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincv : lookupName s.env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName s.env "%k219" = some (.ptr k219))
    (hread0 : readByte s.mem (g + cond) = some u0)
    (hidxlt : idx < cond) (hcondlt : cond < 2 ^ 63) :
    (∃ (e : State) (j : Nat), j ≤ 4 ∧ e.mem = s.mem ∧
      Stage2NoEventWalkInv K mem e ∧ stage2SkipPre b idx cond σ inc lc k219 e ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ stage2SkipFrame s e)
    ∨ (∃ (e : State) (j : Nat), j ≤ 4 ∧
      stage2SkipWs (BitVec.ofNat 8 u0.toNat) = false ∧ e.mem = s.mem ∧
      Stage2NoEventWalkInv K mem e ∧ e.pc = "if.end457" ∧
      phiIncoming (e.pre.getD "") stage2SkipIfEnd457EeIncoming = some (.reg "%cond") ∧
      lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)) ∧
      lookupName e.env "%inc.lcssa" = some (.int 64 inc) ∧
      lookupName e.env "%.lcssa" = some (.int 8 lc) ∧
      lookupName e.env "%k219" = some (.ptr k219) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧ stage2SkipFrame s e) := by
  let v : BitVec 8 := BitVec.ofNat 8 u0.toNat
  have hv : v = BitVec.ofNat 8 u0.toNat := rfl
  have hread0' : readByte s.mem (g + ((BitVec.ofNat 64 cond).signExtend 64).toNat)
      = some u0 := by
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cond < 2 ^ 64)]
    exact hread0
  have hpos0 : ((BitVec.ofNat 64 cond).signExtend 64).toNat < 2 ^ 63 := by
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cond < 2 ^ 64)]
    exact hcondlt
  let S1 : State := stage2NoEventWalkNext
    (stage2SkipLandLhsTrueCells s.env g (BitVec.ofNat 64 cond) u0) s "NodeBlock51"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_skipLandLhsTrue h hpc hg hc hpos0 hread0'
  have h57₁ : lookupName S1.env "%57" = some (.int 8 v) := by
    simp only [S1, stage2NoEventWalkNext]; skip_lk
  have hfr1 : stage2SkipFrame s S1 :=
    stage2SkipFrame.mono (stage2SkipFrame.refl s)
      (cs := stage2SkipLandLhsTrueCells [] g (BitVec.ofNat 64 cond) u0)
      (by simp only [S1, stage2NoEventWalkNext, stage2SkipLandLhsTrueCells, cells])
      (by frame_names)
  by_cases hws : stage2SkipWs v = true
  · have hleaf : stage2SkipLeaf v = true := by rw [stage2SkipLeaf_eq_ws]; exact hws
    by_cases h13 : v.slt (BitVec.ofNat 8 13) = true
    · have hb1 : (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) = true := by
        rw [← stage2SkipLeaf_slt13_true h13]; exact hleaf
      have hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 :=
        stage2Skip_ule_one_of hb1
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
        "LeafBlock43"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock51_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h57₁
          (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 1; rw [h13]; rfl)
      have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf44",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: S2.env) S2
        "land.rhs.preheader"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock43_true L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h57₂ hy
      refine Or.inl ⟨S3, 3, by omega,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]), L3.inv', ?_,
        stage2SkipRun3 L1 L2 L3, ?_⟩
      exact ⟨by simp only [S3, stage2NoEventWalkNext],
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk⟩
      · have hfr2 : stage2SkipFrame S1 S2 :=
          stage2SkipFrame.mono (stage2SkipFrame.refl S1)
            (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
            (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
        have hfr3 : stage2SkipFrame S2 S3 :=
          stage2SkipFrame.mono (stage2SkipFrame.refl S2)
            (cs := [("%SwitchLeaf44", .int 1 (evalICmp .ule
                (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
              ("%.off", .int 8 (v + BitVec.ofNat 8 247))])
            (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
        exact stage2SkipFrame.trans hfr1 (stage2SkipFrame.trans hfr2 hfr3)
    · have h13f : v.slt (BitVec.ofNat 8 13) = false := by
        cases h : v.slt (BitVec.ofNat 8 13) <;> simp_all
      by_cases h32 : v.slt (BitVec.ofNat 8 32) = true
      · have hleaf' : (v == BitVec.ofNat 8 13) = true := by
          rw [← stage2SkipLeaf_slt32_true h13f h32, stage2SkipLeaf_eq_ws]; exact hws
        have hy : evalICmp .eq v (BitVec.ofNat 8 13) = 1 := stage2Skip_beq_one_of hleaf'
        let S2 : State := stage2NoEventWalkNext
          (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
          "NodeBlock49"
        have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
          link_skipNodeBlock51_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
            h57₁ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0; rw [h13f]; rfl)
        have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
          simp only [S2, stage2NoEventWalkNext]; skip_lk
        let S3 : State := stage2NoEventWalkNext
          (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S2.env) S2
          "LeafBlock45"
        have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
          link_skipNodeBlock49_true L2.inv' (by simp only [S2, stage2NoEventWalkNext])
            h57₂ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 1; rw [h32]; rfl)
        have h57₃ : lookupName S3.env "%57" = some (.int 8 v) := by
          simp only [S3, stage2NoEventWalkNext]; skip_lk
        let S4 : State := stage2NoEventWalkNext
          (("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: S3.env) S3
          "land.rhs.preheader"
        have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
          link_skipLeafBlock45_true L3.inv' (by simp only [S3, stage2NoEventWalkNext])
            h57₃ hy
        refine Or.inl ⟨S4, 4, by omega,
          (by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]), L4.inv', ?_,
          stage2SkipRun4 L1 L2 L3 L4, ?_⟩
        exact ⟨by simp only [S4, stage2NoEventWalkNext],
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk⟩
        · have hfr2 : stage2SkipFrame S1 S2 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S1)
              (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
              (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr3 : stage2SkipFrame S2 S3 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S2)
              (cs := [("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32)))])
              (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr4 : stage2SkipFrame S3 S4 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S3)
              (cs := [("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13)))])
              (by simp only [S4, stage2NoEventWalkNext, cells]) (by frame_names)
          exact stage2SkipFrame.trans hfr1
            (stage2SkipFrame.trans hfr2 (stage2SkipFrame.trans hfr3 hfr4))
      · have h32f : v.slt (BitVec.ofNat 8 32) = false := by
          cases h : v.slt (BitVec.ofNat 8 32) <;> simp_all
        have hleaf' : (v == BitVec.ofNat 8 32) = true := by
          rw [← stage2SkipLeaf_slt32_false h13f h32f, stage2SkipLeaf_eq_ws]; exact hws
        have hy : evalICmp .eq v (BitVec.ofNat 8 32) = 1 := stage2Skip_beq_one_of hleaf'
        let S2 : State := stage2NoEventWalkNext
          (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
          "NodeBlock49"
        have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
          link_skipNodeBlock51_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
            h57₁ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0; rw [h13f]; rfl)
        have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
          simp only [S2, stage2NoEventWalkNext]; skip_lk
        let S3 : State := stage2NoEventWalkNext
          (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S2.env) S2
          "LeafBlock47"
        have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
          link_skipNodeBlock49_false L2.inv' (by simp only [S2, stage2NoEventWalkNext])
            h57₂ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 0; rw [h32f]; rfl)
        have h57₃ : lookupName S3.env "%57" = some (.int 8 v) := by
          simp only [S3, stage2NoEventWalkNext]; skip_lk
        let S4 : State := stage2NoEventWalkNext
          (("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: S3.env) S3
          "land.rhs.preheader"
        have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
          link_skipLeafBlock47_true L3.inv' (by simp only [S3, stage2NoEventWalkNext])
            h57₃ hy
        refine Or.inl ⟨S4, 4, by omega,
          (by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]), L4.inv', ?_,
          stage2SkipRun4 L1 L2 L3 L4, ?_⟩
        exact ⟨by simp only [S4, stage2NoEventWalkNext],
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk⟩
        · have hfr2 : stage2SkipFrame S1 S2 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S1)
              (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
              (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr3 : stage2SkipFrame S2 S3 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S2)
              (cs := [("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32)))])
              (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr4 : stage2SkipFrame S3 S4 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S3)
              (cs := [("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32)))])
              (by simp only [S4, stage2NoEventWalkNext, cells]) (by frame_names)
          exact stage2SkipFrame.trans hfr1
            (stage2SkipFrame.trans hfr2 (stage2SkipFrame.trans hfr3 hfr4))
  · have hwsf : stage2SkipWs v = false := by
      cases h : stage2SkipWs v <;> simp_all
    have hleaf : stage2SkipLeaf v = false := by rw [stage2SkipLeaf_eq_ws]; exact hwsf
    have hnot : ∀ (e : State), e.pc = "if.end457" →
        (e.pre = some "LeafBlock43" ∨ e.pre = some "LeafBlock45" ∨
          e.pre = some "LeafBlock47") →
        phiIncoming (e.pre.getD "") stage2SkipIfEnd457EeIncoming = some (.reg "%cond") := by
      intro e hpc' hpre'
      rcases hpre' with h' | h' | h'
      · rw [h']; decide
      · rw [h']; decide
      · rw [h']; decide
    by_cases h13 : v.slt (BitVec.ofNat 8 13) = true
    · have hb1 : (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) = false := by
        rw [← stage2SkipLeaf_slt13_true h13]; exact hleaf
      have hy : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0 :=
        stage2Skip_ule_zero_of hb1
      let S2 : State := stage2NoEventWalkNext
        (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
        "LeafBlock43"
      have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
        link_skipNodeBlock51_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h57₁
          (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 1; rw [h13]; rfl)
      have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
        simp only [S2, stage2NoEventWalkNext]; skip_lk
      let S3 : State := stage2NoEventWalkNext
        (("%SwitchLeaf44",
            .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
          ("%.off", .int 8 (v + BitVec.ofNat 8 247)) :: S2.env) S2 "if.end457"
      have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
        link_skipLeafBlock43_false L2.inv' (by simp only [S2, stage2NoEventWalkNext])
          h57₂ hy
      refine Or.inr ⟨S3, 3, by omega, hwsf,
        (by simp only [S3, S2, S1, stage2NoEventWalkNext]), L3.inv',
        (by simp only [S3, stage2NoEventWalkNext]),
        hnot S3 (by simp only [S3, stage2NoEventWalkNext])
          (Or.inl (by simp only [S3, S2, stage2NoEventWalkNext])),
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        by simp only [S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
        stage2SkipRun3 L1 L2 L3, ?_⟩
      · have hfr2 : stage2SkipFrame S1 S2 :=
          stage2SkipFrame.mono (stage2SkipFrame.refl S1)
            (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
            (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
        have hfr3 : stage2SkipFrame S2 S3 :=
          stage2SkipFrame.mono (stage2SkipFrame.refl S2)
            (cs := [("%SwitchLeaf44", .int 1 (evalICmp .ule
                (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
              ("%.off", .int 8 (v + BitVec.ofNat 8 247))])
            (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
        exact stage2SkipFrame.trans hfr1 (stage2SkipFrame.trans hfr2 hfr3)
    · have h13f : v.slt (BitVec.ofNat 8 13) = false := by
        cases h : v.slt (BitVec.ofNat 8 13) <;> simp_all
      by_cases h32 : v.slt (BitVec.ofNat 8 32) = true
      · have hleaf' : (v == BitVec.ofNat 8 13) = false := by
          rw [← stage2SkipLeaf_slt32_true h13f h32, stage2SkipLeaf_eq_ws]; exact hwsf
        have hy : evalICmp .eq v (BitVec.ofNat 8 13) = 0 := stage2Skip_beq_zero_of hleaf'
        let S2 : State := stage2NoEventWalkNext
          (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
          "NodeBlock49"
        have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
          link_skipNodeBlock51_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
            h57₁ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0; rw [h13f]; rfl)
        have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
          simp only [S2, stage2NoEventWalkNext]; skip_lk
        let S3 : State := stage2NoEventWalkNext
          (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S2.env) S2
          "LeafBlock45"
        have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
          link_skipNodeBlock49_true L2.inv' (by simp only [S2, stage2NoEventWalkNext])
            h57₂ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 1; rw [h32]; rfl)
        have h57₃ : lookupName S3.env "%57" = some (.int 8 v) := by
          simp only [S3, stage2NoEventWalkNext]; skip_lk
        let S4 : State := stage2NoEventWalkNext
          (("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: S3.env) S3
          "if.end457"
        have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
          link_skipLeafBlock45_false L3.inv' (by simp only [S3, stage2NoEventWalkNext])
            h57₃ hy
        refine Or.inr ⟨S4, 4, by omega, hwsf,
          (by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]), L4.inv',
          (by simp only [S4, stage2NoEventWalkNext]),
          hnot S4 (by simp only [S4, stage2NoEventWalkNext])
            (Or.inr (Or.inl (by simp only [S4, S3, stage2NoEventWalkNext]))),
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          stage2SkipRun4 L1 L2 L3 L4, ?_⟩
        · have hfr2 : stage2SkipFrame S1 S2 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S1)
              (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
              (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr3 : stage2SkipFrame S2 S3 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S2)
              (cs := [("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32)))])
              (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr4 : stage2SkipFrame S3 S4 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S3)
              (cs := [("%SwitchLeaf46", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13)))])
              (by simp only [S4, stage2NoEventWalkNext, cells]) (by frame_names)
          exact stage2SkipFrame.trans hfr1
            (stage2SkipFrame.trans hfr2 (stage2SkipFrame.trans hfr3 hfr4))
      · have h32f : v.slt (BitVec.ofNat 8 32) = false := by
          cases h : v.slt (BitVec.ofNat 8 32) <;> simp_all
        have hleaf' : (v == BitVec.ofNat 8 32) = false := by
          rw [← stage2SkipLeaf_slt32_false h13f h32f, stage2SkipLeaf_eq_ws]; exact hwsf
        have hy : evalICmp .eq v (BitVec.ofNat 8 32) = 0 := stage2Skip_beq_zero_of hleaf'
        let S2 : State := stage2NoEventWalkNext
          (("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: S1.env) S1
          "NodeBlock49"
        have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
          link_skipNodeBlock51_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
            h57₁ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) = 0; rw [h13f]; rfl)
        have h57₂ : lookupName S2.env "%57" = some (.int 8 v) := by
          simp only [S2, stage2NoEventWalkNext]; skip_lk
        let S3 : State := stage2NoEventWalkNext
          (("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: S2.env) S2
          "LeafBlock47"
        have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
          link_skipNodeBlock49_false L2.inv' (by simp only [S2, stage2NoEventWalkNext])
            h57₂ (by show BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) = 0; rw [h32f]; rfl)
        have h57₃ : lookupName S3.env "%57" = some (.int 8 v) := by
          simp only [S3, stage2NoEventWalkNext]; skip_lk
        let S4 : State := stage2NoEventWalkNext
          (("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: S3.env) S3
          "if.end457"
        have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
          link_skipLeafBlock47_false L3.inv' (by simp only [S3, stage2NoEventWalkNext])
            h57₃ hy
        refine Or.inr ⟨S4, 4, by omega, hwsf,
          (by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]), L4.inv',
          (by simp only [S4, stage2NoEventWalkNext]),
          hnot S4 (by simp only [S4, stage2NoEventWalkNext])
            (Or.inr (Or.inr (by simp only [S4, S3, stage2NoEventWalkNext]))),
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          by simp only [S4, S3, S2, S1, stage2NoEventWalkNext]; skip_lk,
          stage2SkipRun4 L1 L2 L3 L4, ?_⟩
        · have hfr2 : stage2SkipFrame S1 S2 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S1)
              (cs := [("%Pivot52", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13)))])
              (by simp only [S2, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr3 : stage2SkipFrame S2 S3 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S2)
              (cs := [("%Pivot50", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32)))])
              (by simp only [S3, stage2NoEventWalkNext, cells]) (by frame_names)
          have hfr4 : stage2SkipFrame S3 S4 :=
            stage2SkipFrame.mono (stage2SkipFrame.refl S3)
              (cs := [("%SwitchLeaf48", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32)))])
              (by simp only [S4, stage2NoEventWalkNext, cells]) (by frame_names)
          exact stage2SkipFrame.trans hfr1
            (stage2SkipFrame.trans hfr2 (stage2SkipFrame.trans hfr3 hfr4))

/-! ### The segment -/

/-- **The scalar class's whitespace skip.**  From `land.lhs.true`'s entry — the
state `link_condEnd_true` delivers — the segment probes `%invariant.gep1068 +
%cond`, classifies the byte with the first test, and either goes straight to the
merge (a non-member) or seeds the skip loop and runs it to the merge; then
`if.end457`'s `%ee.1` selection, `%k219` store and number-or-minus guard carry it
to `if.then471`'s or `if.else495`'s entry, with `Stage2NoEventWalkInv` at the end
and `%ee.1`'s position between `%idxprom.lcssa` and `%cond`.

The bound is relative to the scan's own start: the loop's budget is
`cond - idx`, so its run is at most `5 * (cond - idx + 1)` (`BoundLoop.run_from`'s
`(r + 1) * cost`), and the segment's non-loop steps are at most seven — four from
the first test, two from the preheader links and one from the merge — for
`12 + 5 * (cond - idx)` in all.

The scan's non-membership prefix `[idx, q)` is the scalar lexeme, and it is
exported for the arm that runs the loop.  The direct arm reads only the probe's
byte, so there it carries that byte as the non-member the first test found
(`q = cond`); an interior position of `[idx, cond)` is not constrained by that
arm. -/
theorem stage2NoEventWalkScalarSkip {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {g b idx cond : Nat} {σ : Nat → UInt8} {u0 : UInt8}
    {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "land.lhs.true")
    (hg : lookupName s.env "%invariant.gep1068" = some (.ptr g))
    (hc : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincv : lookupName s.env "%inc.lcssa" = some (.int 64 inc))
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 lc))
    (hk : lookupName s.env "%k219" = some (.ptr k219))
    (hstore : k219 = K.c + 32)
    (hread0 : readByte s.mem (g + cond) = some u0)
    (hbytes : ∀ j, j < cond → readByte s.mem (b + j) = some (σ j))
    (hidxlt : idx < cond) (hcondlt : cond < 2 ^ 63) :
    ∃ (e : State) (j q : Nat), j ≤ 12 + 5 * (cond - idx) ∧
      (e.pc = "if.then471" ∨ e.pc = "if.else495") ∧
      lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      idx ≤ q ∧ q ≤ cond ∧
      (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (σ q).toNat) = true) ∧
      ((∀ j, idx ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = false) ∨
        (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 u0.toNat) = false)) ∧
      ((j ≤ 12 + 5 * (q - idx) ∧
        (∀ j, idx ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = false)) ∨
        (j ≤ 6 ∧ q = cond)) ∧
      Stage2NoEventWalkInv K mem e ∧
      e.mem = writeBytes s.mem k219 (natToBytes inc.toNat 8) ∧
      (∀ n, runFuel calls (j + n) stage2NoEventBody s =
        runFuel calls n stage2NoEventBody e) ∧
      stage2SkipFrame s e := by
  rcases stage2SkipFirstTest (σ := σ) h hpc hg hc hidx hb hincv hlc hk hread0 hidxlt hcondlt with
    ⟨e₁, j₁, hj₁, hm₁, hinv₁, hpre₁, hrun₁, hfr₁⟩ |
    ⟨e₁, j₁, hj₁, hws₁, hm₁, hinv₁, hpc₁, hinc₁, hcond₁, hincv₁, hlc₁, hk₁, hrun₁,
      hfr₁⟩
  · -- the loop
    obtain ⟨hpc₀, hidx₀, hb₀, hcond₀, hincv₀, hlc₀, hk₀⟩ := hpre₁
    have hbytes₀ : readByte e₁.mem (b + idx) = some (σ idx) := by
      rw [hm₁]; exact hbytes idx hidxlt
    let S1 : State := stage2NoEventWalkNext e₁.env e₁ "land.rhs"
    have L1 : Stage2NoEventWalkLink calls K mem e₁ K S1 :=
      link_skipLandRhsPreheader hinv₁ hpc₀
    have hidx₁ : lookupName S1.env "%idxprom.lcssa" =
        some (.int 64 (BitVec.ofNat 64 idx)) := by
      simp only [S1, stage2NoEventWalkNext]; exact hidx₀
    have hb₁ : lookupName S1.env "%b" = some (.ptr b) := by
      simp only [S1, stage2NoEventWalkNext]; exact hb₀
    have hidxpos : ((BitVec.ofNat 64 idx).signExtend 64).toNat < 2 ^ 63 := by
      rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64)]
      omega
    have hbyte₁ : readByte S1.mem
        (b + ((BitVec.ofNat 64 idx).signExtend 64).toNat) = some (σ idx) := by
      have hm0 : S1.mem = e₁.mem := rfl
      rw [hm0, stage2NoEventSignExtend_self, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64)]
      exact hbytes₀
    let S2 : State := stage2NoEventWalkNext
      (stage2SkipLandRhsCells S1.env (BitVec.ofNat 64 idx) b (σ idx)) S1 "NodeBlock62"
    have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
      link_skipLandRhs_preheader (idx := idx) L1.inv'
        (by simp only [S1, stage2NoEventWalkNext])
        (by simp only [S1, stage2NoEventWalkNext, hpc₀]) hidx₁ hb₁ hidxpos hbyte₁
    have hm2 : S2.mem = s.mem := by
      simp only [S2, S1, stage2NoEventWalkNext, hm₁]
    have hfr2 : stage2SkipFrame e₁ S2 :=
      stage2SkipFrame.mono (stage2SkipFrame.refl e₁)
        (cs := stage2SkipLandRhsCells [] (BitVec.ofNat 64 idx) b (σ idx))
        (by simp only [S2, S1, stage2NoEventWalkNext, stage2SkipLandRhsCells, cells])
        (by frame_names)
    have hInv0 : stage2SkipInv K mem b idx cond σ inc lc k219 cond S2 idx := by
      refine ⟨by simp only [S2, stage2NoEventWalkNext], L2.inv', ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hcondlt, by omega, hidxlt, by omega, ?_, ?_⟩
      · simp only [S2, stage2NoEventWalkNext]; skip_lk
      · exact (by simp only [S2, stage2NoEventWalkNext]; skip_lk :
          lookupName S2.env "%ee.01053" = some (.int 64 (BitVec.ofNat 64 idx)))
      · simp only [S2, stage2NoEventWalkNext]; rw [lookupName_cons_self]
      · simp only [S2, stage2NoEventWalkNext]; skip_lk
      · simp only [S2, stage2NoEventWalkNext]; skip_lk
      · simp only [S2, stage2NoEventWalkNext]; skip_lk
      · simp only [S2, stage2NoEventWalkNext]; skip_lk
      · intro j hj hjlt; omega
      · intro j hj
        rw [hm2]; exact hbytes j hj
    obtain ⟨e₃, j₃, q₃, hj₃, hidxle₃, hexit₃, hrun₃, hmem₃, hfr₃⟩ :=
      stage2SkipLoop_run_at (calls := calls) (K := K) (mem := mem)
        (b := b) (idx := idx) (cond := cond) (σ := σ) (inc := inc) (lc := lc)
        (k219 := k219) (M := S2.mem) S2 (stage2SkipFrame.refl S2) hInv0 rfl
    obtain ⟨hpc₃, hinv₃, pre₃, op₃, hpre₃, hinc₃, hop₃, hidx₃, hq₃, hpre₃',
      hstop₃, hincv₃, hlc₃, hk₃⟩ := hexit₃
    obtain ⟨e₄, hpc₄, hq₄, hinv₄, hmem₄, hrun₄, hfr₄⟩ :=
      stage2SkipJoinRun (b := b) (idx := idx) (cond := cond) (σ := σ)
        hinv₃ hpc₃ (by rw [hpre₃]; exact hinc₃) hop₃ hincv₃ hlc₃ hk₃
        hstore
    refine ⟨e₄, j₁ + 2 + j₃ + 1, q₃, ?_, hpc₄, hq₄, hidx₃, hq₃, hstop₃,
      Or.inl hpre₃', Or.inl ⟨?_, hpre₃'⟩, hinv₄,
      (hmem₄.trans (by rw [hmem₃, hm2])), ?_,
      stage2SkipFrame.trans hfr₁
        (stage2SkipFrame.trans hfr2 (stage2SkipFrame.trans hfr₃ hfr₄))⟩
    · omega
    · omega
    · intro n
      rw [show j₁ + 2 + j₃ + 1 + n = j₁ + (2 + (j₃ + (1 + n))) from by omega,
        hrun₁ (2 + (j₃ + (1 + n))), stage2SkipRun2 L1 L2 (j₃ + (1 + n)),
        hrun₃ (1 + n), hrun₄ n]
  · -- the merge directly, with `%cond` as the selection
    obtain ⟨e₄, hpc₄, hq₄, hinv₄, hmem₄, hrun₄, hfr₄⟩ :=
      stage2SkipJoinRun (b := b) (idx := idx) (cond := cond) (σ := σ)
        hinv₁ hpc₁ hinc₁
        (evalOperand_reg_of e₁.env e₁ "%cond" (.int 64 (BitVec.ofNat 64 cond)) hcond₁)
        hincv₁ hlc₁ hk₁ hstore
    refine ⟨e₄, j₁ + 1, cond, ?_, hpc₄, hq₄, by omega, by omega, Or.inl rfl,
      Or.inr ⟨rfl, hws₁⟩, Or.inr ⟨?_, rfl⟩, hinv₄,
      (hmem₄.trans (by rw [hm₁])), ?_, stage2SkipFrame.trans hfr₁ hfr₄⟩
    · omega
    · omega
    · intro n
      rw [show j₁ + 1 + n = j₁ + (1 + n) from by omega, hrun₁ (1 + n), hrun₄ n]

/-! ### Axiom footprints -/

#print axioms stage2SkipFrame
#print axioms stage2SkipFrame.trans
#print axioms stage2SkipFrame.mono
#print axioms stage2SkipExit
#print axioms stage2SkipExitAt
#print axioms stage2SkipInvAt_cells
#print axioms stage2SkipInvAt_budget
#print axioms stage2SkipAdvance
#print axioms stage2SkipStop
#print axioms stage2SkipWhileBodyExit
#print axioms stage2SkipWhileBodyContinue
#print axioms stage2SkipLoop
#print axioms stage2SkipLoop_run
#print axioms stage2SkipLoop_run_at
#print axioms stage2SkipJoinRun
#print axioms stage2SkipFirstTest
#print axioms stage2NoEventWalkScalarSkip

end LeanLLVM.Refinement
