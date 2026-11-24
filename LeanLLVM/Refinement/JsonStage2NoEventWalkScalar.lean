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

**The loop's vocabulary.**  The skip loop is `land.rhs` (the `%ee.01053` `phi`,
the `%b` `gep`, the byte load) and its test `NodeBlock62`, then `while.body`'s
increment and `%exitcond1170.not`.  The module states the vocabulary the
`LoopFuel` instance consumes and does not yet contain the instance: the
bound-exit induction's head is `NodeBlock62` — the first block at which the
cursor and the byte it loaded are both bound — its bound is `%cond`, and its
exit test is the disjunction the body branches on, `stage2SkipAtBound`: the
loaded byte is out of the class, or the increment has reached `%cond`.  The
measure is the distance `%cond - %ee.01053`, carried as the invariant's budget
(`stage2SkipInvAt`); the invariant also carries the class membership of every
position the loop has passed, so the exit word, `stage2SkipExit`, states that
the loop stopped at the first non-whitespace position at or before `%cond`, with
the merge's `%ee.1` selection at that same position and the walk's invariant at
the merge.  The head's two three-way pivot splits — the member byte to
`while.body`, the non-member straight to the merge — and the increment block's
two one-link tails are the rows that instance is to consume; they, the instance
and the composed segment are the module's remaining work, and the header states
them in the future tense for that reason.

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
invariant's transport across cells, and the merge's invariant with its two
constructors.  It does **not** yet contain the head's two block paths
(`stage2SkipAdvance`/`stage2SkipStop`), the increment block's two tails, the
`LoopFuel.BoundLoop` instance and its run, the merge's one-step run, or the entry
test and the composed segment theorem to `if.then471`/`if.else495`; those are the
next work on this file.  The two arms below the merge's entries —
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

/-! ### The loop's invariant and its exit word -/

/-- The loaded byte's class, read from the head state's `%58`. -/
def stage2SkipHeadClass (s : State) : Bool :=
  match lookupName s.env "%58" with
  | some (.int 8 v) => stage2SkipWs v
  | _ => false

/-- The head's exit test: out of the class, or the increment reached `%cond`. -/
def stage2SkipAtBound (cond : Nat) (s : State) (c : Nat) : Bool :=
  !(stage2SkipHeadClass s) || (c + 1 == cond)

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
  (∀ j, idx ≤ j → j < c → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = true) ∧
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

/-- **The loop's exit word**: the merge's invariant and the first-non-member
property, at one and the same position. -/
def stage2SkipExit (b idx cond : Nat) (σ : Nat → UInt8) (inc : BitVec 64)
    (lc : BitVec 8) (k219 : Nat) (e : State) : Prop :=
  stage2SkipJoin b idx cond σ inc lc k219 e ∧
  ∃ (q : Nat),
    idx ≤ q ∧ q ≤ cond ∧
    (∀ j, idx ≤ j → j < q → stage2SkipWs (BitVec.ofNat 8 (σ j).toNat) = true) ∧
    (q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (σ q).toNat) = false)

/-- The loop's exit word projects the merge's invariant. -/
theorem stage2SkipJoin_of_exit {e : State} {b idx cond : Nat} {σ : Nat → UInt8}
    {inc : BitVec 64} {lc : BitVec 8} {k219 : Nat}
    (h : stage2SkipExit b idx cond σ inc lc k219 e) :
    stage2SkipJoin b idx cond σ inc lc k219 e := h.1

/-- Discharging the "not a carried name" side condition of `InvAt_cells`. -/
macro "skip_names" : tactic => `(tactic|
  (intro x hx
   simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
   rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))

/-- **The invariant across cells of other names.**  Every register the loop reads
and the merge writes is untouched, so the predicate moves to the extended
environment unchanged, and the run's memory is the head's. -/
theorem stage2SkipInvAt_cells {pc : String} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {b idx cond c : Nat} {σ : Nat → UInt8} {inc : BitVec 64} {lc : BitVec 8}
    {k219 r : Nat} {s s' : State} {cs : List (String × Value)}
    (h : stage2SkipInvAt pc K mem b idx cond σ inc lc k219 r s c)
    (hmem : s'.mem = s.mem) (hpc : s'.pc = pc) (henv : s'.env = cells cs s.env)
    (hnames : ∀ x ∈ stage2SkipCarriedNames, x ∉ cs.map (·.1)) :
    stage2SkipInvAt pc K mem b idx cond σ inc lc k219 r s' c := by
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

end LeanLLVM.Refinement
