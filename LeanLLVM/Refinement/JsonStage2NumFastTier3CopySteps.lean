/-
Tier 3's window copy: the per-edge `phi` steps of the loop's blocks.

`JsonStage2NumFastTier3` states the window's tie at the model (`copy_retained`,
`copy_sticky`, `copy_counters`).  What the copy loop itself needs is its run:
`to_double` copies the significant digits into its 768-byte array with an
unrolled ladder, and every block of that ladder opens with a `phi` run whose
operand is the predecessor the edge names.

**The ladder's blocks.**  `for.body87.i.i` is the head: three carried words (the
digit index, the accumulator, the unrolled counter) and the accumulator's test
against `10 ^ 6`.  Its store is `if.then90.i.i` (`%mul` by ten, the digit's byte
at the base plus the index, the widen and the two adds).  The same test repeats
three times (`for.inc98.i.i`, `.1`, `.2`) so that four digits are consumed per
visit of the head, and the last counter is incremented by four at
`for.inc98.i.i.3`, whose `%niter.ncmp.3` is the ladder's bound.  The residual
loop is `for.body87.i.i.epil` with the store `if.then90.i.i.epil` and the latch
`for.inc98.i.i.epil`, one digit per visit, bounded by `%xtraiter`.

**Why the steps are per edge.**  A `phi`'s taken incoming is a function of
`s.pre`, so a block with two in-edges reads its own instructions two ways:
`for.body87.i.i` reads `%i.2.i.i` from the preheader and `%inc99.i.i.3` from the
latch; `for.inc98.i.i` reads `%add96.i.i` after a store and its own carried value
after a refused test; `for.inc98.i.i.epil` reads `%add96.i.i.epil` or
`%e.0734.i.i.epil` the same way.  Each block therefore has one `denote` per edge
and one `step` per test outcome, and the arms of the two `BoundLoop` instances
(`JsonStage2NumFastTier3CopyLoop`) are those steps in sequence.

**The shapes are shared.**  The three unrolled tests differ from `for.inc98.i.i`
only in the names of their cells, and the stores likewise, so the test's and the
store's lemmas take the block's `findBlock` pin and the shape's names.  The
unrolled copies are instantiations, not re-readings.

**The accumulator.**  A store's chain is `%e * 10`, the digit's byte, the widen
and the two adds, so the successor cell holds `10 * e + d` as a `BitVec`.  The
`Nat` reading of that cell is what the tests compare, and `t3StoreEnv` names the
environment the chain binds so a successor block's hypotheses are projections of
it rather than a re-derivation.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonScanLane
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.NumFastTier3

namespace NumFastTier3Copy

/-! ### The accumulator's cap

`10 ^ 6` is the value `to_double` compares the accumulator against; a digit that
would take it past the cap is still counted (`%i` advances) but not accumulated.
The test is a signed compare, so the readings below are at `Nat` only while the
words are non-negative. -/

/-- `10 ^ 6` at `i64`: the copy's cap. -/
def t3Cap : BitVec 64 := 0xf4240#64

theorem t3Cap_toNat : t3Cap.toNat = 10 ^ 6 := by decide

theorem t3Cap_lt_two : t3Cap.toNat < 2 ^ 63 := by decide

/-- A signed compare of two non-negative words is their `Nat` compare. -/
theorem slt_one_iff {x k : BitVec 64} (hx : x.toNat < 2 ^ 63) (hk : k.toNat < 2 ^ 63) :
    evalICmp .slt x k = (1 : BitVec 1) ↔ x.toNat < k.toNat := by
  rw [show evalICmp .slt x k = BitVec.ofBool (x.slt k) from rfl,
    NumFastStarts.ofBool_bool, BitVec.slt_iff_toInt_lt]
  have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hx' : x.toInt = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  have hk' : k.toInt = (k.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  rw [hx', hk']
  constructor <;> intro h <;> omega

/-- The same compare at zero: the cap is not reached. -/
theorem slt_zero_iff {x k : BitVec 64} (hx : x.toNat < 2 ^ 63) (hk : k.toNat < 2 ^ 63) :
    evalICmp .slt x k = (0 : BitVec 1) ↔ ¬ x.toNat < k.toNat := by
  constructor
  · intro h hh
    have h1 : evalICmp .slt x k = (1 : BitVec 1) := (slt_one_iff hx hk).mpr hh
    rw [h1] at h; exact absurd h (by decide)
  · intro h
    rcases bitVec1_eq_zero_or_one (evalICmp .slt x k) with h0 | h0
    · exact h0
    · exact absurd ((slt_one_iff hx hk).mp h0) h

/-- The byte a widen reads back: `vByte`'s `Nat` value is the byte's. -/
theorem vByte_toNat (b : UInt8) : (vByte b).toNat = b.toNat := by
  have h2 : (2 : Nat) ^ 8 = 256 := by decide
  have hb : b.toNat < 256 := by
    have := b.toNat_lt
    omega
  simp only [vByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-! ### The `phi` runs at the state the edge delivered

`JsonEntrySteps`' runs are stated at its own `withEnv`, which is `stateAt`'s body
under another name.  The three bridges are that identification, so every step
below is at the `stateAt` shape the rest of `numFast`'s blocks use. -/

theorem t3_denoteCode_phi1 (calls : Calls) (env : Env) (s : State) (d : String)
    (ty : Ty) (inc : List (String × Operand)) {p : String} {op : Operand} {v : Value}
    (is : List Instr) (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some v) {hst : startsWithPhi is = false} :
    denoteCode calls (.phi d ty inc :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, v) :: env) s) := by
  simpa only [stateAt, JsonEntrySteps.withEnv] using
    JsonEntrySteps.denoteCode_phi1 calls env s d ty inc is hpre hinc hop (hst := hst)

theorem t3_denoteCode_phi3 (calls : Calls) (env : Env) (s : State)
    (d1 : String) (ty1 : Ty) (inc1 : List (String × Operand))
    (d2 : String) (ty2 : Ty) (inc2 : List (String × Operand))
    (d3 : String) (ty3 : Ty) (inc3 : List (String × Operand))
    {p : String} {op1 : Operand} {v1 : Value} {op2 : Operand} {v2 : Value}
    {op3 : Operand} {v3 : Value}
    (is : List Instr) (hpre : s.pre = some p)
    (hinc1 : phiIncoming p inc1 = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some v1)
    (hinc2 : phiIncoming p inc2 = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some v2)
    (hinc3 : phiIncoming p inc3 = some op3)
    (hop3 : evalOperand (stateAt env s) op3 = some v3)
    {hst : startsWithPhi is = false} :
    denoteCode calls (.phi d1 ty1 inc1 :: .phi d2 ty2 inc2 :: .phi d3 ty3 inc3 :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d3, v3) :: (d2, v2) :: (d1, v1) :: env) s) := by
  simpa only [stateAt, JsonEntrySteps.withEnv] using
    JsonEntrySteps.denoteCode_phi3 calls env s d1 ty1 inc1 d2 ty2 inc2 d3 ty3 inc3 is
      hpre hinc1 hop1 hinc2 hop2 hinc3 hop3 (hst := hst)

/-! ### The head: `for.body87.i.i`

Three carried `phi`s and the accumulator's test.  The entry edge carries the
dispatch's index and two zeros; the back edge carries the latch's three cells. -/

/-- The head's instructions, from its `findBlock` pin. -/
def t3HeadInstrs : List Instr :=
  [Instr.phi "%i.3735.i.i" (Ty.int 64)
     [("for.body87.i.i.preheader.new", (Operand.reg "%i.2.i.i")),
      ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
   Instr.phi "%e.0734.i.i" (Ty.int 64)
     [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
   Instr.phi "%niter" (Ty.int 64)
     [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc98.i.i.3", (Operand.reg "%niter.next.3"))],
   Instr.icmp "%cmp88.i.i" (IPred.slt) 64 (Operand.reg "%e.0734.i.i")
     (Operand.imm (Const.int 64 t3Cap))]

theorem t3_head_find :
    numFastBody.findBlock "for.body87.i.i" =
      some ⟨"for.body87.i.i", t3HeadInstrs,
        Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩ := by
  simpa only [t3HeadInstrs, t3Cap] using numFast_findBlock_for_body87_i_i

/-- The environment the head leaves: its three carried words and the test's bit. -/
def t3HeadEnv (env : Env) (i e n : BitVec 64) : Env :=
  ("%cmp88.i.i", .int 1 (evalICmp .slt e t3Cap)) ::
  ("%niter", .int 64 n) :: ("%e.0734.i.i", .int 64 e) :: ("%i.3735.i.i", .int 64 i) :: env

/-- The head at the entry edge: the dispatch's index and zero for both carried
counters. -/
theorem t3_head_denote_entry {calls : Calls} {env : Env} {s : State} {i : BitVec 64}
    (hpre : s.pre = some "for.body87.i.i.preheader.new")
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i)) :
    denoteCode calls t3HeadInstrs (stateAt env s) =
      some (stateAt (t3HeadEnv env i 0 0) s) := by
  unfold t3HeadInstrs
  rw [t3_denoteCode_phi3 (calls := calls) (env := env) (s := s)
    "%i.3735.i.i" (Ty.int 64) _
    "%e.0734.i.i" (Ty.int 64) _
    "%niter" (Ty.int 64) _
    [Instr.icmp "%cmp88.i.i" (IPred.slt) 64 (Operand.reg "%e.0734.i.i")
      (Operand.imm (Const.int 64 t3Cap))]
    hpre (by decide) (evalOperand_reg_of env s "%i.2.i.i" (.int 64 i) hi)
    (by decide) (evalOperand_lit_of (stateAt env s) 64 0)
    (by decide) (evalOperand_lit_of (stateAt env s) 64 0)
    (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls
    (("%niter", .int 64 0) :: ("%e.0734.i.i", .int 64 0) ::
      ("%i.3735.i.i", .int 64 i) :: env) s "%cmp88.i.i" "%e.0734.i.i" (IPred.slt)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3HeadEnv, stateAt]

/-- The head at the back edge: the latch's index, accumulator and counter. -/
theorem t3_head_denote_back {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.3" = some (.int 64 e))
    (hn : lookupName env "%niter.next.3" = some (.int 64 n)) :
    denoteCode calls t3HeadInstrs (stateAt env s) =
      some (stateAt (t3HeadEnv env i e n) s) := by
  unfold t3HeadInstrs
  rw [t3_denoteCode_phi3 (calls := calls) (env := env) (s := s)
    "%i.3735.i.i" (Ty.int 64) _
    "%e.0734.i.i" (Ty.int 64) _
    "%niter" (Ty.int 64) _
    [Instr.icmp "%cmp88.i.i" (IPred.slt) 64 (Operand.reg "%e.0734.i.i")
      (Operand.imm (Const.int 64 t3Cap))]
    hpre (by decide) (evalOperand_reg_of env s "%inc99.i.i.3" (.int 64 i) hi)
    (by decide) (evalOperand_reg_of env s "%e.1.i.i.3" (.int 64 e) he)
    (by decide) (evalOperand_reg_of env s "%niter.next.3" (.int 64 n) hn)
    (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls
    (("%niter", .int 64 n) :: ("%e.0734.i.i", .int 64 e) ::
      ("%i.3735.i.i", .int 64 i) :: env) s "%cmp88.i.i" "%e.0734.i.i" (IPred.slt)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3HeadEnv, stateAt]

/-- The head's step through the store at the entry edge. -/
theorem t3_head_step_entry_store {calls : Calls} {env : Env} {s : State}
    {i : BitVec 64}
    (hpc : s.pc = "for.body87.i.i")
    (hpre : s.pre = some "for.body87.i.i.preheader.new")
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i))
    (hbit : evalICmp .slt (0 : BitVec 64) t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3HeadEnv env i 0 0)
        { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3HeadEnv env i 0 0) s)
    (b := ⟨"for.body87.i.i", t3HeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_head_find
  · exact t3_head_denote_entry (calls := calls) hpre hi
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3HeadEnv env i 0 0) s) _
      "if.then90.i.i" "for.inc98.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step past the store at the entry edge. -/
theorem t3_head_step_entry_skip {calls : Calls} {env : Env} {s : State}
    {i : BitVec 64}
    (hpc : s.pc = "for.body87.i.i")
    (hpre : s.pre = some "for.body87.i.i.preheader.new")
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i))
    (hbit : evalICmp .slt (0 : BitVec 64) t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3HeadEnv env i 0 0)
        { s with pc := "for.inc98.i.i", pre := some "for.body87.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3HeadEnv env i 0 0) s)
    (b := ⟨"for.body87.i.i", t3HeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_head_find
  · exact t3_head_denote_entry (calls := calls) hpre hi
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3HeadEnv env i 0 0) s) _
      "if.then90.i.i" "for.inc98.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step through the store at the back edge. -/
theorem t3_head_step_back_store {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i")
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.3" = some (.int 64 e))
    (hn : lookupName env "%niter.next.3" = some (.int 64 n))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3HeadEnv env i e n)
        { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3HeadEnv env i e n) s)
    (b := ⟨"for.body87.i.i", t3HeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_head_find
  · exact t3_head_denote_back (calls := calls) hpre hi he hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3HeadEnv env i e n) s) _
      "if.then90.i.i" "for.inc98.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step past the store at the back edge. -/
theorem t3_head_step_back_skip {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i")
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.3" = some (.int 64 e))
    (hn : lookupName env "%niter.next.3" = some (.int 64 n))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3HeadEnv env i e n)
        { s with pc := "for.inc98.i.i", pre := some "for.body87.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3HeadEnv env i e n) s)
    (b := ⟨"for.body87.i.i", t3HeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_head_find
  · exact t3_head_denote_back (calls := calls) hpre hi he hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3HeadEnv env i e n) s) _
      "if.then90.i.i" "for.inc98.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The test: `for.inc98.i.i` and its unrolled copies

Two instructions — the carried accumulator and the cap's test — and a terminator
that chooses the store or the next test.  The shape is shared: the pin names the
cells, so the unrolled copies' tests are the same statement at their own names. -/

/-- A test block's instructions. -/
def t3TestInstrs (d cmp : String) (inc : List (String × Operand)) : List Instr :=
  [Instr.phi d (Ty.int 64) inc,
   Instr.icmp cmp (IPred.slt) 64 (Operand.reg d)
     (Operand.imm (Const.int 64 t3Cap))]

/-- The environment a test block leaves: the carried accumulator and the cap's
bit. -/
def t3TestEnv (env : Env) (d cmp : String) (e : BitVec 64) : Env :=
  (cmp, .int 1 (evalICmp .slt e t3Cap)) :: (d, .int 64 e) :: env

/-- A test block's chain at the edge that selected `op`. -/
theorem t3_test_denote {calls : Calls} {env : Env} {s : State} {d cmp : String}
    {inc : List (String × Operand)} {pre : String} {op : Operand} {e : BitVec 64}
    (hpre : s.pre = some pre) (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e)) :
    denoteCode calls (t3TestInstrs d cmp inc) (stateAt env s) =
      some (stateAt (t3TestEnv env d cmp e) s) := by
  unfold t3TestInstrs
  rw [t3_denoteCode_phi1 (calls := calls) (env := env) (s := s)
    d (Ty.int 64) inc
    [Instr.icmp cmp (IPred.slt) 64 (Operand.reg d)
      (Operand.imm (Const.int 64 t3Cap))]
    hpre hinc hop (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls ((d, .int 64 e) :: env) s cmp d (IPred.slt)
    (lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3TestEnv, stateAt]

/-- A test block's step through its store. -/
theorem t3_test_step_store (calls : Calls) (name d cmp : String)
    (inc : List (String × Operand)) (t f : String) {env : Env} {s : State}
    {pre : String} {op : Operand} {e : BitVec 64}
    (hpin : numFastBody.findBlock name =
      some ⟨name, t3TestInstrs d cmp inc, Term.condbr (Operand.reg cmp) t f⟩)
    (hpc : s.pc = name) (hpre : s.pre = some pre)
    (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env d cmp e) { s with pc := t, pre := some name }) := by
  refine numFast_step_at (s' := stateAt (t3TestEnv env d cmp e) s)
    (b := ⟨name, t3TestInstrs d cmp inc, Term.condbr (Operand.reg cmp) t f⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hpin
  · exact t3_test_denote (calls := calls) hpre hinc hop
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3TestEnv env d cmp e) s) _
      t f (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- A test block's step past its store. -/
theorem t3_test_step_skip (calls : Calls) (name d cmp : String)
    (inc : List (String × Operand)) (t f : String) {env : Env} {s : State}
    {pre : String} {op : Operand} {e : BitVec 64}
    (hpin : numFastBody.findBlock name =
      some ⟨name, t3TestInstrs d cmp inc, Term.condbr (Operand.reg cmp) t f⟩)
    (hpc : s.pc = name) (hpre : s.pre = some pre)
    (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env d cmp e) { s with pc := f, pre := some name }) := by
  refine numFast_step_at (s' := stateAt (t3TestEnv env d cmp e) s)
    (b := ⟨name, t3TestInstrs d cmp inc, Term.condbr (Operand.reg cmp) t f⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hpin
  · exact t3_test_denote (calls := calls) hpre hinc hop
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3TestEnv env d cmp e) s) _
      t f (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The three unrolled tests' pins and steps -/

theorem t3_inc98_find :
    numFastBody.findBlock "for.inc98.i.i" =
      some ⟨"for.inc98.i.i",
        t3TestInstrs "%e.1.i.i" "%cmp88.i.i.1"
          [("if.then90.i.i", (Operand.reg "%add96.i.i")),
           ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))],
        Term.condbr (Operand.reg "%cmp88.i.i.1") "if.then90.i.i.1" "for.inc98.i.i.1"⟩ := by
  simpa only [t3TestInstrs, t3Cap] using numFast_findBlock_for_inc98_i_i

theorem t3_inc98_find_1 :
    numFastBody.findBlock "for.inc98.i.i.1" =
      some ⟨"for.inc98.i.i.1",
        t3TestInstrs "%e.1.i.i.1" "%cmp88.i.i.2"
          [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
           ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))],
        Term.condbr (Operand.reg "%cmp88.i.i.2") "if.then90.i.i.2" "for.inc98.i.i.2"⟩ := by
  simpa only [t3TestInstrs, t3Cap] using numFast_findBlock_for_inc98_i_i_1

theorem t3_inc98_find_2 :
    numFastBody.findBlock "for.inc98.i.i.2" =
      some ⟨"for.inc98.i.i.2",
        t3TestInstrs "%e.1.i.i.2" "%cmp88.i.i.3"
          [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
           ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))],
        Term.condbr (Operand.reg "%cmp88.i.i.3") "if.then90.i.i.3" "for.inc98.i.i.3"⟩ := by
  simpa only [t3TestInstrs, t3Cap] using numFast_findBlock_for_inc98_i_i_2

/-- `for.inc98.i.i` through its store. -/
theorem t3_inc98_step_store {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i") (hpre : s.pre = some "if.then90.i.i")
    (he : lookupName env "%add96.i.i" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i" "%cmp88.i.i.1" e)
        { s with pc := "if.then90.i.i.1", pre := some "for.inc98.i.i" }) :=
  t3_test_step_store calls "for.inc98.i.i" "%e.1.i.i" "%cmp88.i.i.1"
    [("if.then90.i.i", (Operand.reg "%add96.i.i")),
     ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))]
    "if.then90.i.i.1" "for.inc98.i.i.1" t3_inc98_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%add96.i.i" (.int 64 e) he) hbit

/-- `for.inc98.i.i` past its store. -/
theorem t3_inc98_step_skip {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i") (hpre : s.pre = some "for.body87.i.i")
    (he : lookupName env "%e.0734.i.i" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i" "%cmp88.i.i.1" e)
        { s with pc := "for.inc98.i.i.1", pre := some "for.inc98.i.i" }) :=
  t3_test_step_skip calls "for.inc98.i.i" "%e.1.i.i" "%cmp88.i.i.1"
    [("if.then90.i.i", (Operand.reg "%add96.i.i")),
     ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))]
    "if.then90.i.i.1" "for.inc98.i.i.1" t3_inc98_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%e.0734.i.i" (.int 64 e) he) hbit

/-- `for.inc98.i.i.1` through its store. -/
theorem t3_inc98_step_store_1 {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.1") (hpre : s.pre = some "if.then90.i.i.1")
    (he : lookupName env "%add96.i.i.1" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i.1" "%cmp88.i.i.2" e)
        { s with pc := "if.then90.i.i.2", pre := some "for.inc98.i.i.1" }) :=
  t3_test_step_store calls "for.inc98.i.i.1" "%e.1.i.i.1" "%cmp88.i.i.2"
    [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
     ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))]
    "if.then90.i.i.2" "for.inc98.i.i.2" t3_inc98_find_1 hpc hpre (by decide)
    (evalOperand_reg_of env s "%add96.i.i.1" (.int 64 e) he) hbit

/-- `for.inc98.i.i.1` past its store. -/
theorem t3_inc98_step_skip_1 {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.1") (hpre : s.pre = some "for.inc98.i.i")
    (he : lookupName env "%e.1.i.i" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i.1" "%cmp88.i.i.2" e)
        { s with pc := "for.inc98.i.i.2", pre := some "for.inc98.i.i.1" }) :=
  t3_test_step_skip calls "for.inc98.i.i.1" "%e.1.i.i.1" "%cmp88.i.i.2"
    [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
     ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))]
    "if.then90.i.i.2" "for.inc98.i.i.2" t3_inc98_find_1 hpc hpre (by decide)
    (evalOperand_reg_of env s "%e.1.i.i" (.int 64 e) he) hbit

/-- `for.inc98.i.i.2` through its store. -/
theorem t3_inc98_step_store_2 {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.2") (hpre : s.pre = some "if.then90.i.i.2")
    (he : lookupName env "%add96.i.i.2" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i.2" "%cmp88.i.i.3" e)
        { s with pc := "if.then90.i.i.3", pre := some "for.inc98.i.i.2" }) :=
  t3_test_step_store calls "for.inc98.i.i.2" "%e.1.i.i.2" "%cmp88.i.i.3"
    [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
     ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))]
    "if.then90.i.i.3" "for.inc98.i.i.3" t3_inc98_find_2 hpc hpre (by decide)
    (evalOperand_reg_of env s "%add96.i.i.2" (.int 64 e) he) hbit

/-- `for.inc98.i.i.2` past its store. -/
theorem t3_inc98_step_skip_2 {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.2") (hpre : s.pre = some "for.inc98.i.i.1")
    (he : lookupName env "%e.1.i.i.1" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TestEnv env "%e.1.i.i.2" "%cmp88.i.i.3" e)
        { s with pc := "for.inc98.i.i.3", pre := some "for.inc98.i.i.2" }) :=
  t3_test_step_skip calls "for.inc98.i.i.2" "%e.1.i.i.2" "%cmp88.i.i.3"
    [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
     ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))]
    "if.then90.i.i.3" "for.inc98.i.i.3" t3_inc98_find_2 hpc hpre (by decide)
    (evalOperand_reg_of env s "%e.1.i.i.1" (.int 64 e) he) hbit

/-! ### The store: `if.then90.i.i` and its copies

`%e * 10`, the digit's byte at the base plus the index, the widen from `i8` to
`i64`, and the two adds.  The sum is `10 * e + d` at the `Nat` reading, which is
the accumulator the window's tie folds.  The block writes no memory: the array
`digVal` reads is written by the `T`/`F` parse's own `if.then31.i.i`. -/

/-- A store block's instructions. -/
def t3StoreInstrs (m eR ad baseR iR ld z s94 a96 : String) : List Instr :=
  [Instr.binop m (BinOp.mul) 64 (Operand.reg eR) (Operand.imm (Const.int 64 0x000000000000000a#64)),
   Instr.gep ad (Ty.int 8) (Operand.reg baseR) (Operand.reg iR),
   Instr.load ld (Ty.int 8) (Operand.reg ad),
   Instr.zext z 8 64 (Operand.reg ld),
   Instr.binop s94 (BinOp.add) 64 (Operand.reg m) (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
   Instr.binop a96 (BinOp.add) 64 (Operand.reg s94) (Operand.reg z)]

/-- The environment a store block leaves: the product, the address, the byte, its
widen, and the two sums. -/
def t3StoreEnv (env : Env) (m ad ld z s94 a96 : String) (e : BitVec 64)
    (d : UInt8) (a : Nat) : Env :=
  (a96, .int 64 (((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat)) ::
  (s94, .int 64 ((e * 10#64) + 0xffffffffffffffd0#64)) ::
  (z, .int 64 (BitVec.ofNat 64 (vByte d).toNat)) ::
  (ld, .int 8 (vByte d)) :: (ad, .ptr a) :: (m, .int 64 (e * 10#64)) :: env

/-- A store block's chain at the digit's byte. -/
theorem t3_store_denote {calls : Calls} {env : Env} {s : State}
    {m eR ad baseR iR ld z s94 a96 : String} {e : BitVec 64} {b : Nat}
    {idx : BitVec 64} {d : UInt8}
    (he : lookupName env eR = some (.int 64 e))
    (hbase : lookupName env baseR = some (.ptr b))
    (hidx : lookupName env iR = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d])
    (hmb : m ≠ baseR) (hmi : m ≠ iR) (hzm : z ≠ m) (hlm : ld ≠ m)
    (ham : ad ≠ m) (hsz : s94 ≠ z) :
    denoteCode calls (t3StoreInstrs m eR ad baseR iR ld z s94 a96) (stateAt env s) =
      some (stateAt (t3StoreEnv env m ad ld z s94 a96 e d
        (b + (idx.signExtend 64).toNat)) s) := by
  unfold t3StoreInstrs
  rw [denoteCode_mul_imm_w calls env s m eR 64 he]
  rw [denoteCode_gep8_reg calls ((m, .int 64 (e * 10#64)) :: env) s ad baseR iR
    (by rw [lookupName_cons_ne _ _ hmb]; exact hbase)
    (by rw [lookupName_cons_ne _ _ hmi]; exact hidx) hpos]
  rw [denoteCode_load_i8 calls _ s ld ad (lookupName_cons_self ..) hread]
  rw [denoteCode_zext calls _ s z ld 8 64 (lookupName_cons_self ..)]
  rw [denoteCode_add_imm calls _ s s94 m
    (by rw [lookupName_cons_ne _ _ hzm, lookupName_cons_ne _ _ hlm,
      lookupName_cons_ne _ _ ham]; exact lookupName_cons_self ..)]
  rw [denoteCode_add_reg calls _ s a96 s94 z (lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ hsz]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3StoreEnv, stateAt]

/-- A store block's step: the block writes no memory and jumps to the next
test. -/
theorem t3_store_step (calls : Calls) (name m eR ad baseR iR ld z s94 a96 : String)
    (nxt : String) {env : Env} {s : State} {e : BitVec 64} {b : Nat}
    {idx : BitVec 64} {d : UInt8}
    (hpin : numFastBody.findBlock name =
      some ⟨name, t3StoreInstrs m eR ad baseR iR ld z s94 a96, Term.br nxt⟩)
    (hpc : s.pc = name)
    (he : lookupName env eR = some (.int 64 e))
    (hbase : lookupName env baseR = some (.ptr b))
    (hidx : lookupName env iR = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d])
    (hmb : m ≠ baseR) (hmi : m ≠ iR) (hzm : z ≠ m) (hlm : ld ≠ m)
    (ham : ad ≠ m) (hsz : s94 ≠ z) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env m ad ld z s94 a96 e d
        (b + (idx.signExtend 64).toNat)) { s with pc := nxt, pre := some name }) := by
  refine numFast_step_at (s' := stateAt (t3StoreEnv env m ad ld z s94 a96 e d
      (b + (idx.signExtend 64).toNat)) s)
    (b := ⟨name, t3StoreInstrs m eR ad baseR iR ld z s94 a96, Term.br nxt⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hpin
  · simpa only [stateAt] using t3_store_denote (calls := calls) he hbase hidx hpos hread
      hmb hmi hzm hlm ham hsz
  · simp only [execTerm, stateAt, hpc]

/-! ### The store blocks' pins and steps -/

theorem t3_if_then90_find :
    numFastBody.findBlock "if.then90.i.i" =
      some ⟨"if.then90.i.i",
        t3StoreInstrs "%mul91.i.i" "%e.0734.i.i" "%arrayidx92.i.i" "%p" "%i.3735.i.i"
          "%64" "%conv93.i.i" "%sub94.i.i" "%add96.i.i",
        Term.br "for.inc98.i.i"⟩ := by
  simpa only [t3StoreInstrs] using numFast_findBlock_if_then90_i_i

theorem t3_if_then90_find_1 :
    numFastBody.findBlock "if.then90.i.i.1" =
      some ⟨"if.then90.i.i.1",
        t3StoreInstrs "%mul91.i.i.1" "%e.1.i.i" "%gep" "%invariant.gep" "%i.3735.i.i"
          "%65" "%conv93.i.i.1" "%sub94.i.i.1" "%add96.i.i.1",
        Term.br "for.inc98.i.i.1"⟩ := by
  simpa only [t3StoreInstrs] using numFast_findBlock_if_then90_i_i_1

theorem t3_if_then90_find_2 :
    numFastBody.findBlock "if.then90.i.i.2" =
      some ⟨"if.then90.i.i.2",
        t3StoreInstrs "%mul91.i.i.2" "%e.1.i.i.1" "%gep1192" "%invariant.gep1191" "%i.3735.i.i"
          "%66" "%conv93.i.i.2" "%sub94.i.i.2" "%add96.i.i.2",
        Term.br "for.inc98.i.i.2"⟩ := by
  simpa only [t3StoreInstrs] using numFast_findBlock_if_then90_i_i_2

theorem t3_if_then90_find_3 :
    numFastBody.findBlock "if.then90.i.i.3" =
      some ⟨"if.then90.i.i.3",
        t3StoreInstrs "%mul91.i.i.3" "%e.1.i.i.2" "%gep1194" "%invariant.gep1193" "%i.3735.i.i"
          "%67" "%conv93.i.i.3" "%sub94.i.i.3" "%add96.i.i.3",
        Term.br "for.inc98.i.i.3"⟩ := by
  simpa only [t3StoreInstrs] using numFast_findBlock_if_then90_i_i_3

theorem t3_if_then90_find_epil :
    numFastBody.findBlock "if.then90.i.i.epil" =
      some ⟨"if.then90.i.i.epil",
        t3StoreInstrs "%mul91.i.i.epil" "%e.0734.i.i.epil" "%arrayidx92.i.i.epil" "%p"
          "%i.3735.i.i.epil" "%68" "%conv93.i.i.epil" "%sub94.i.i.epil" "%add96.i.i.epil",
        Term.br "for.inc98.i.i.epil"⟩ := by
  simpa only [t3StoreInstrs] using numFast_findBlock_if_then90_i_i_epil

/-- `if.then90.i.i`: the unrolled nest's first digit. -/
theorem t3_if_then90_step {calls : Calls} {env : Env} {s : State}
    {e : BitVec 64} {b : Nat} {idx : BitVec 64} {d : UInt8}
    (hpc : s.pc = "if.then90.i.i")
    (he : lookupName env "%e.0734.i.i" = some (.int 64 e))
    (hbase : lookupName env "%p" = some (.ptr b))
    (hidx : lookupName env "%i.3735.i.i" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env "%mul91.i.i" "%arrayidx92.i.i" "%64"
        "%conv93.i.i" "%sub94.i.i" "%add96.i.i" e d (b + (idx.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i", pre := some "if.then90.i.i" }) :=
  t3_store_step calls "if.then90.i.i" "%mul91.i.i" "%e.0734.i.i" "%arrayidx92.i.i" "%p"
    "%i.3735.i.i" "%64" "%conv93.i.i" "%sub94.i.i" "%add96.i.i" "for.inc98.i.i"
    t3_if_then90_find hpc he hbase hidx hpos hread
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `if.then90.i.i.1`: the nest's second digit. -/
theorem t3_if_then90_step_1 {calls : Calls} {env : Env} {s : State}
    {e : BitVec 64} {b : Nat} {idx : BitVec 64} {d : UInt8}
    (hpc : s.pc = "if.then90.i.i.1")
    (he : lookupName env "%e.1.i.i" = some (.int 64 e))
    (hbase : lookupName env "%invariant.gep" = some (.ptr b))
    (hidx : lookupName env "%i.3735.i.i" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env "%mul91.i.i.1" "%gep" "%65"
        "%conv93.i.i.1" "%sub94.i.i.1" "%add96.i.i.1" e d (b + (idx.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.1", pre := some "if.then90.i.i.1" }) :=
  t3_store_step calls "if.then90.i.i.1" "%mul91.i.i.1" "%e.1.i.i" "%gep" "%invariant.gep"
    "%i.3735.i.i" "%65" "%conv93.i.i.1" "%sub94.i.i.1" "%add96.i.i.1" "for.inc98.i.i.1"
    t3_if_then90_find_1 hpc he hbase hidx hpos hread
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `if.then90.i.i.2`: the nest's third digit. -/
theorem t3_if_then90_step_2 {calls : Calls} {env : Env} {s : State}
    {e : BitVec 64} {b : Nat} {idx : BitVec 64} {d : UInt8}
    (hpc : s.pc = "if.then90.i.i.2")
    (he : lookupName env "%e.1.i.i.1" = some (.int 64 e))
    (hbase : lookupName env "%invariant.gep1191" = some (.ptr b))
    (hidx : lookupName env "%i.3735.i.i" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env "%mul91.i.i.2" "%gep1192" "%66"
        "%conv93.i.i.2" "%sub94.i.i.2" "%add96.i.i.2" e d (b + (idx.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.2", pre := some "if.then90.i.i.2" }) :=
  t3_store_step calls "if.then90.i.i.2" "%mul91.i.i.2" "%e.1.i.i.1" "%gep1192"
    "%invariant.gep1191" "%i.3735.i.i" "%66" "%conv93.i.i.2" "%sub94.i.i.2" "%add96.i.i.2"
    "for.inc98.i.i.2" t3_if_then90_find_2 hpc he hbase hidx hpos hread
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `if.then90.i.i.3`: the nest's fourth digit. -/
theorem t3_if_then90_step_3 {calls : Calls} {env : Env} {s : State}
    {e : BitVec 64} {b : Nat} {idx : BitVec 64} {d : UInt8}
    (hpc : s.pc = "if.then90.i.i.3")
    (he : lookupName env "%e.1.i.i.2" = some (.int 64 e))
    (hbase : lookupName env "%invariant.gep1193" = some (.ptr b))
    (hidx : lookupName env "%i.3735.i.i" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env "%mul91.i.i.3" "%gep1194" "%67"
        "%conv93.i.i.3" "%sub94.i.i.3" "%add96.i.i.3" e d (b + (idx.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.3", pre := some "if.then90.i.i.3" }) :=
  t3_store_step calls "if.then90.i.i.3" "%mul91.i.i.3" "%e.1.i.i.2" "%gep1194"
    "%invariant.gep1193" "%i.3735.i.i" "%67" "%conv93.i.i.3" "%sub94.i.i.3" "%add96.i.i.3"
    "for.inc98.i.i.3" t3_if_then90_find_3 hpc he hbase hidx hpos hread
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `if.then90.i.i.epil`: the residual loop's digit. -/
theorem t3_if_then90_step_epil {calls : Calls} {env : Env} {s : State}
    {e : BitVec 64} {b : Nat} {idx : BitVec 64} {d : UInt8}
    (hpc : s.pc = "if.then90.i.i.epil")
    (he : lookupName env "%e.0734.i.i.epil" = some (.int 64 e))
    (hbase : lookupName env "%p" = some (.ptr b))
    (hidx : lookupName env "%i.3735.i.i.epil" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (b + (idx.signExtend 64).toNat) 1 = some [d]) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3StoreEnv env "%mul91.i.i.epil" "%arrayidx92.i.i.epil" "%68"
        "%conv93.i.i.epil" "%sub94.i.i.epil" "%add96.i.i.epil" e d
        (b + (idx.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" }) :=
  t3_store_step calls "if.then90.i.i.epil" "%mul91.i.i.epil" "%e.0734.i.i.epil"
    "%arrayidx92.i.i.epil" "%p" "%i.3735.i.i.epil" "%68" "%conv93.i.i.epil"
    "%sub94.i.i.epil" "%add96.i.i.epil" "for.inc98.i.i.epil"
    t3_if_then90_find_epil hpc he hbase hidx hpos hread
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### The latches

Both latches are one shape: the carried accumulator's `phi`, the digit index's
increment, the counter's increment, and the equality of the counter's next value
with the bound.  The main latch advances by four against `%unroll_iter`; the
residual one by one against `%xtraiter`. -/

/-- A latch's instructions. -/
def t3LatchInstrs (eR iR nR incI : String) (cI : BitVec 64) (incN : String)
    (cN : BitVec 64) (uR cmp : String) (inc : List (String × Operand)) : List Instr :=
  [Instr.phi eR (Ty.int 64) inc,
   Instr.binop incI (BinOp.add) 64 (Operand.reg iR) (Operand.imm (Const.int 64 cI)),
   Instr.binop incN (BinOp.add) 64 (Operand.reg nR) (Operand.imm (Const.int 64 cN)),
   Instr.icmp cmp (IPred.eq) 64 (Operand.reg incN) (Operand.reg uR)]

/-- The environment a latch leaves: the carried accumulator, the two increments,
and the counter's test against the bound. -/
def t3LatchEnv (env : Env) (eR incI incN cmp : String) (e i n u : BitVec 64) : Env :=
  (cmp, .int 1 (evalICmp .eq n u)) :: (incN, .int 64 n) :: (incI, .int 64 i) ::
  (eR, .int 64 e) :: env

/-- A latch's chain at the edge that selected `op`. -/
theorem t3_latch_denote {calls : Calls} {env : Env} {s : State}
    {eR iR nR uR incI incN cmp : String} {inc : List (String × Operand)}
    {pre : String} {op : Operand} {e i n u cI cN : BitVec 64}
    (hpre : s.pre = some pre) (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e))
    (hi : lookupName env iR = some (.int 64 i))
    (hn : lookupName env nR = some (.int 64 n))
    (hu : lookupName env uR = some (.int 64 u))
    (hei : eR ≠ iR) (hin : incI ≠ nR) (hen : eR ≠ nR)
    (hnu : incN ≠ uR) (hiu : incI ≠ uR) (heu : eR ≠ uR) :
    denoteCode calls (t3LatchInstrs eR iR nR incI cI incN cN uR cmp inc) (stateAt env s) =
      some (stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u) s) := by
  unfold t3LatchInstrs
  rw [t3_denoteCode_phi1 (calls := calls) (env := env) (s := s)
    eR (Ty.int 64) inc
    [Instr.binop incI (BinOp.add) 64 (Operand.reg iR) (Operand.imm (Const.int 64 cI)),
     Instr.binop incN (BinOp.add) 64 (Operand.reg nR) (Operand.imm (Const.int 64 cN)),
     Instr.icmp cmp (IPred.eq) 64 (Operand.reg incN) (Operand.reg uR)]
    hpre hinc hop (hst := by rfl)]
  rw [denoteCode_add_imm calls ((eR, .int 64 e) :: env) s incI iR
    (by rw [lookupName_cons_ne _ _ hei]; exact hi)]
  rw [denoteCode_add_imm calls ((incI, .int 64 (i + cI)) :: (eR, .int 64 e) :: env) s
    incN nR
    (by rw [lookupName_cons_ne _ _ hin, lookupName_cons_ne _ _ hen]; exact hn)]
  rw [denoteCode_icmp_eq_reg calls
    ((incN, .int 64 (n + cN)) :: (incI, .int 64 (i + cI)) :: (eR, .int 64 e) :: env) s
    cmp incN uR (lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ hnu, lookupName_cons_ne _ _ hiu,
      lookupName_cons_ne _ _ heu]; exact hu)]
  simp only [denoteCode_nil, t3LatchEnv, stateAt]

/-- A latch's step at a counter that has reached the bound. -/
theorem t3_latch_step_taken (calls : Calls) (name eR iR nR uR incI incN cmp : String)
    (inc : List (String × Operand)) (cI cN : BitVec 64) (t f : String)
    {env : Env} {s : State} {pre : String} {op : Operand} {e i n u : BitVec 64}
    (hpin : numFastBody.findBlock name =
      some ⟨name, t3LatchInstrs eR iR nR incI cI incN cN uR cmp inc,
        Term.condbr (Operand.reg cmp) t f⟩)
    (hpc : s.pc = name) (hpre : s.pre = some pre)
    (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e))
    (hi : lookupName env iR = some (.int 64 i))
    (hn : lookupName env nR = some (.int 64 n))
    (hu : lookupName env uR = some (.int 64 u))
    (hei : eR ≠ iR) (hin : incI ≠ nR) (hen : eR ≠ nR)
    (hnu : incN ≠ uR) (hiu : incI ≠ uR) (heu : eR ≠ uR)
    (hbit : evalICmp .eq (n + cN) u = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u)
        { s with pc := t, pre := some name }) := by
  refine numFast_step_at (s' := stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u) s)
    (b := ⟨name, t3LatchInstrs eR iR nR incI cI incN cN uR cmp inc,
      Term.condbr (Operand.reg cmp) t f⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hpin
  · exact t3_latch_denote (calls := calls) hpre hinc hop hi hn hu
      hei hin hen hnu hiu heu
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u) s) _
      t f (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- A latch's step at a counter that has not reached the bound. -/
theorem t3_latch_step_back (calls : Calls) (name eR iR nR uR incI incN cmp : String)
    (inc : List (String × Operand)) (cI cN : BitVec 64) (t f : String)
    {env : Env} {s : State} {pre : String} {op : Operand} {e i n u : BitVec 64}
    (hpin : numFastBody.findBlock name =
      some ⟨name, t3LatchInstrs eR iR nR incI cI incN cN uR cmp inc,
        Term.condbr (Operand.reg cmp) t f⟩)
    (hpc : s.pc = name) (hpre : s.pre = some pre)
    (hinc : phiIncoming pre inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 e))
    (hi : lookupName env iR = some (.int 64 i))
    (hn : lookupName env nR = some (.int 64 n))
    (hu : lookupName env uR = some (.int 64 u))
    (hei : eR ≠ iR) (hin : incI ≠ nR) (hen : eR ≠ nR)
    (hnu : incN ≠ uR) (hiu : incI ≠ uR) (heu : eR ≠ uR)
    (hbit : evalICmp .eq (n + cN) u = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u)
        { s with pc := f, pre := some name }) := by
  refine numFast_step_at (s' := stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u) s)
    (b := ⟨name, t3LatchInstrs eR iR nR incI cI incN cN uR cmp inc,
      Term.condbr (Operand.reg cmp) t f⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hpin
  · exact t3_latch_denote (calls := calls) hpre hinc hop hi hn hu
      hei hin hen hnu hiu heu
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (t3LatchEnv env eR incI incN cmp e (i + cI) (n + cN) u) s) _
      t f (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The main latch: `for.inc98.i.i.3` -/

theorem t3_latch3_find :
    numFastBody.findBlock "for.inc98.i.i.3" =
      some ⟨"for.inc98.i.i.3",
        t3LatchInstrs "%e.1.i.i.3" "%i.3735.i.i" "%niter" "%inc99.i.i.3" 0x4#64
          "%niter.next.3" 0x4#64 "%unroll_iter" "%niter.ncmp.3"
          [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
           ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))],
        Term.condbr (Operand.reg "%niter.ncmp.3")
          "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"⟩ := by
  simpa only [t3LatchInstrs] using numFast_findBlock_for_inc98_i_i_3

/-- The main latch at its store edge: the counter's increment reaches the
bound, so the ladder leaves for the exit block. -/
theorem t3_latch3_step_exit {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.3") (hpre : s.pre = some "if.then90.i.i.3")
    (he : lookupName env "%add96.i.i.3" = some (.int 64 e))
    (hi : lookupName env "%i.3735.i.i" = some (.int 64 i))
    (hn : lookupName env "%niter" = some (.int 64 n))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x4#64) u = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.3" "%inc99.i.i.3" "%niter.next.3"
        "%niter.ncmp.3" e (i + 0x4#64) (n + 0x4#64) u)
        { s with pc := "for.end100.i.i.loopexit.unr-lcssa",
                 pre := some "for.inc98.i.i.3" }) :=
  t3_latch_step_taken calls "for.inc98.i.i.3" "%e.1.i.i.3" "%i.3735.i.i" "%niter"
    "%unroll_iter" "%inc99.i.i.3" "%niter.next.3" "%niter.ncmp.3"
    [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
     ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))]
    0x4#64 0x4#64 "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"
    t3_latch3_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%add96.i.i.3" (.int 64 e) he) hi hn hu
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit

/-- The main latch at its test edge: the counter's increment does not reach the
bound, so the ladder re-enters the head. -/
theorem t3_latch3_step_back {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.3") (hpre : s.pre = some "for.inc98.i.i.2")
    (he : lookupName env "%e.1.i.i.2" = some (.int 64 e))
    (hi : lookupName env "%i.3735.i.i" = some (.int 64 i))
    (hn : lookupName env "%niter" = some (.int 64 n))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x4#64) u = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.3" "%inc99.i.i.3" "%niter.next.3"
        "%niter.ncmp.3" e (i + 0x4#64) (n + 0x4#64) u)
        { s with pc := "for.body87.i.i", pre := some "for.inc98.i.i.3" }) :=
  t3_latch_step_back calls "for.inc98.i.i.3" "%e.1.i.i.3" "%i.3735.i.i" "%niter"
    "%unroll_iter" "%inc99.i.i.3" "%niter.next.3" "%niter.ncmp.3"
    [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
     ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))]
    0x4#64 0x4#64 "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"
    t3_latch3_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%e.1.i.i.2" (.int 64 e) he) hi hn hu
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit

/-! ### The residual latch: `for.inc98.i.i.epil` -/

theorem t3_latch_epil_find :
    numFastBody.findBlock "for.inc98.i.i.epil" =
      some ⟨"for.inc98.i.i.epil",
        t3LatchInstrs "%e.1.i.i.epil" "%i.3735.i.i.epil" "%epil.iter"
          "%inc99.i.i.epil" 0x1#64 "%epil.iter.next" 0x1#64 "%xtraiter"
          "%epil.iter.cmp.not"
          [("if.then90.i.i.epil", (Operand.reg "%add96.i.i.epil")),
           ("for.body87.i.i.epil", (Operand.reg "%e.0734.i.i.epil"))],
        Term.condbr (Operand.reg "%epil.iter.cmp.not")
          "for.end100.i.i" "for.body87.i.i.epil"⟩ := by
  simpa only [t3LatchInstrs] using numFast_findBlock_for_inc98_i_i_epil

/-- The residual latch at its store edge: the iteration count reaches the
peel's residue, so the loop leaves for `for.end100.i.i`. -/
theorem t3_latch_epil_step_exit {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.epil") (hpre : s.pre = some "if.then90.i.i.epil")
    (he : lookupName env "%add96.i.i.epil" = some (.int 64 e))
    (hi : lookupName env "%i.3735.i.i.epil" = some (.int 64 i))
    (hn : lookupName env "%epil.iter" = some (.int 64 n))
    (hu : lookupName env "%xtraiter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x1#64) u = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.epil" "%inc99.i.i.epil"
        "%epil.iter.next" "%epil.iter.cmp.not" e (i + 0x1#64) (n + 0x1#64) u)
        { s with pc := "for.end100.i.i", pre := some "for.inc98.i.i.epil" }) :=
  t3_latch_step_taken calls "for.inc98.i.i.epil" "%e.1.i.i.epil" "%i.3735.i.i.epil"
    "%epil.iter" "%xtraiter" "%inc99.i.i.epil" "%epil.iter.next" "%epil.iter.cmp.not"
    [("if.then90.i.i.epil", (Operand.reg "%add96.i.i.epil")),
     ("for.body87.i.i.epil", (Operand.reg "%e.0734.i.i.epil"))]
    0x1#64 0x1#64 "for.end100.i.i" "for.body87.i.i.epil"
    t3_latch_epil_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%add96.i.i.epil" (.int 64 e) he) hi hn hu
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit

/-- The residual latch at its test edge: the iteration count has not reached the
residue, so the loop re-enters the residual head. -/
theorem t3_latch_epil_step_back {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.epil") (hpre : s.pre = some "for.body87.i.i.epil")
    (he : lookupName env "%e.0734.i.i.epil" = some (.int 64 e))
    (hi : lookupName env "%i.3735.i.i.epil" = some (.int 64 i))
    (hn : lookupName env "%epil.iter" = some (.int 64 n))
    (hu : lookupName env "%xtraiter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x1#64) u = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.epil" "%inc99.i.i.epil"
        "%epil.iter.next" "%epil.iter.cmp.not" e (i + 0x1#64) (n + 0x1#64) u)
        { s with pc := "for.body87.i.i.epil", pre := some "for.inc98.i.i.epil" }) :=
  t3_latch_step_back calls "for.inc98.i.i.epil" "%e.1.i.i.epil" "%i.3735.i.i.epil"
    "%epil.iter" "%xtraiter" "%inc99.i.i.epil" "%epil.iter.next" "%epil.iter.cmp.not"
    [("if.then90.i.i.epil", (Operand.reg "%add96.i.i.epil")),
     ("for.body87.i.i.epil", (Operand.reg "%e.0734.i.i.epil"))]
    0x1#64 0x1#64 "for.end100.i.i" "for.body87.i.i.epil"
    t3_latch_epil_find hpc hpre (by decide)
    (evalOperand_reg_of env s "%e.0734.i.i.epil" (.int 64 e) he) hi hn hu
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit

/-! ### The residual head: `for.body87.i.i.epil`

The same test as the head, with the residual iteration counter carried beside it.
The entry edge is the exit block of the unrolled nest
(`for.end100.i.i.loopexit.unr-lcssa`), which hands it the index and accumulator
the nest stopped with and a zero counter; the back edge is the residual latch. -/

/-- The residual head's instructions, from its `findBlock` pin. -/
def t3EpilHeadInstrs : List Instr :=
  [Instr.phi "%i.3735.i.i.epil" (Ty.int 64)
     [("for.inc98.i.i.epil", (Operand.reg "%inc99.i.i.epil")),
      ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%i.3735.i.i.unr"))],
   Instr.phi "%e.0734.i.i.epil" (Ty.int 64)
     [("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil")),
      ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.0734.i.i.unr"))],
   Instr.phi "%epil.iter" (Ty.int 64)
     [("for.inc98.i.i.epil", (Operand.reg "%epil.iter.next")),
      ("for.end100.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
   Instr.icmp "%cmp88.i.i.epil" (IPred.slt) 64 (Operand.reg "%e.0734.i.i.epil")
     (Operand.imm (Const.int 64 t3Cap))]

theorem t3_epil_head_find :
    numFastBody.findBlock "for.body87.i.i.epil" =
      some ⟨"for.body87.i.i.epil", t3EpilHeadInstrs,
        Term.condbr (Operand.reg "%cmp88.i.i.epil")
          "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩ := by
  simpa only [t3EpilHeadInstrs, t3Cap] using numFast_findBlock_for_body87_i_i_epil

/-- The environment the residual head leaves. -/
def t3EpilHeadEnv (env : Env) (i e n : BitVec 64) : Env :=
  ("%cmp88.i.i.epil", .int 1 (evalICmp .slt e t3Cap)) ::
  ("%epil.iter", .int 64 n) :: ("%e.0734.i.i.epil", .int 64 e) ::
  ("%i.3735.i.i.epil", .int 64 i) :: env

/-- The residual head at its entry edge: the nest's carried words and a zero
counter. -/
theorem t3_epil_head_denote_entry {calls : Calls} {env : Env} {s : State}
    {i e : BitVec 64}
    (hpre : s.pre = some "for.end100.i.i.loopexit.unr-lcssa")
    (hi : lookupName env "%i.3735.i.i.unr" = some (.int 64 i))
    (he : lookupName env "%e.0734.i.i.unr" = some (.int 64 e)) :
    denoteCode calls t3EpilHeadInstrs (stateAt env s) =
      some (stateAt (t3EpilHeadEnv env i e 0) s) := by
  unfold t3EpilHeadInstrs
  rw [t3_denoteCode_phi3 (calls := calls) (env := env) (s := s)
    "%i.3735.i.i.epil" (Ty.int 64) _
    "%e.0734.i.i.epil" (Ty.int 64) _
    "%epil.iter" (Ty.int 64) _
    [Instr.icmp "%cmp88.i.i.epil" (IPred.slt) 64 (Operand.reg "%e.0734.i.i.epil")
      (Operand.imm (Const.int 64 t3Cap))]
    hpre (by decide) (evalOperand_reg_of env s "%i.3735.i.i.unr" (.int 64 i) hi)
    (by decide) (evalOperand_reg_of env s "%e.0734.i.i.unr" (.int 64 e) he)
    (by decide) (evalOperand_lit_of (stateAt env s) 64 0)
    (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls
    (("%epil.iter", .int 64 0) :: ("%e.0734.i.i.epil", .int 64 e) ::
      ("%i.3735.i.i.epil", .int 64 i) :: env) s
    "%cmp88.i.i.epil" "%e.0734.i.i.epil" (IPred.slt)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3EpilHeadEnv, stateAt]

/-- The residual head at its back edge. -/
theorem t3_epil_head_denote_back {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpre : s.pre = some "for.inc98.i.i.epil")
    (hi : lookupName env "%inc99.i.i.epil" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.epil" = some (.int 64 e))
    (hn : lookupName env "%epil.iter.next" = some (.int 64 n)) :
    denoteCode calls t3EpilHeadInstrs (stateAt env s) =
      some (stateAt (t3EpilHeadEnv env i e n) s) := by
  unfold t3EpilHeadInstrs
  rw [t3_denoteCode_phi3 (calls := calls) (env := env) (s := s)
    "%i.3735.i.i.epil" (Ty.int 64) _
    "%e.0734.i.i.epil" (Ty.int 64) _
    "%epil.iter" (Ty.int 64) _
    [Instr.icmp "%cmp88.i.i.epil" (IPred.slt) 64 (Operand.reg "%e.0734.i.i.epil")
      (Operand.imm (Const.int 64 t3Cap))]
    hpre (by decide) (evalOperand_reg_of env s "%inc99.i.i.epil" (.int 64 i) hi)
    (by decide) (evalOperand_reg_of env s "%e.1.i.i.epil" (.int 64 e) he)
    (by decide) (evalOperand_reg_of env s "%epil.iter.next" (.int 64 n) hn)
    (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls
    (("%epil.iter", .int 64 n) :: ("%e.0734.i.i.epil", .int 64 e) ::
      ("%i.3735.i.i.epil", .int 64 i) :: env) s
    "%cmp88.i.i.epil" "%e.0734.i.i.epil" (IPred.slt)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, t3EpilHeadEnv, stateAt]

/-- The residual head's step through its store at the entry edge. -/
theorem t3_epil_head_step_entry_store {calls : Calls} {env : Env} {s : State}
    {i e : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.epil")
    (hpre : s.pre = some "for.end100.i.i.loopexit.unr-lcssa")
    (hi : lookupName env "%i.3735.i.i.unr" = some (.int 64 i))
    (he : lookupName env "%e.0734.i.i.unr" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EpilHeadEnv env i e 0)
        { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" }) := by
  refine numFast_step_at (s' := stateAt (t3EpilHeadEnv env i e 0) s)
    (b := ⟨"for.body87.i.i.epil", t3EpilHeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i.epil")
        "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_epil_head_find
  · exact t3_epil_head_denote_entry (calls := calls) hpre hi he
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3EpilHeadEnv env i e 0) s) _
      "if.then90.i.i.epil" "for.inc98.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The residual head's step past its store at the entry edge. -/
theorem t3_epil_head_step_entry_skip {calls : Calls} {env : Env} {s : State}
    {i e : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.epil")
    (hpre : s.pre = some "for.end100.i.i.loopexit.unr-lcssa")
    (hi : lookupName env "%i.3735.i.i.unr" = some (.int 64 i))
    (he : lookupName env "%e.0734.i.i.unr" = some (.int 64 e))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EpilHeadEnv env i e 0)
        { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" }) := by
  refine numFast_step_at (s' := stateAt (t3EpilHeadEnv env i e 0) s)
    (b := ⟨"for.body87.i.i.epil", t3EpilHeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i.epil")
        "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_epil_head_find
  · exact t3_epil_head_denote_entry (calls := calls) hpre hi he
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3EpilHeadEnv env i e 0) s) _
      "if.then90.i.i.epil" "for.inc98.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The residual head's step through its store at the back edge. -/
theorem t3_epil_head_step_back_store {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.epil")
    (hpre : s.pre = some "for.inc98.i.i.epil")
    (hi : lookupName env "%inc99.i.i.epil" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.epil" = some (.int 64 e))
    (hn : lookupName env "%epil.iter.next" = some (.int 64 n))
    (hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EpilHeadEnv env i e n)
        { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" }) := by
  refine numFast_step_at (s' := stateAt (t3EpilHeadEnv env i e n) s)
    (b := ⟨"for.body87.i.i.epil", t3EpilHeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i.epil")
        "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_epil_head_find
  · exact t3_epil_head_denote_back (calls := calls) hpre hi he hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3EpilHeadEnv env i e n) s) _
      "if.then90.i.i.epil" "for.inc98.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The residual head's step past its store at the back edge. -/
theorem t3_epil_head_step_back_skip {calls : Calls} {env : Env} {s : State}
    {i e n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.epil")
    (hpre : s.pre = some "for.inc98.i.i.epil")
    (hi : lookupName env "%inc99.i.i.epil" = some (.int 64 i))
    (he : lookupName env "%e.1.i.i.epil" = some (.int 64 e))
    (hn : lookupName env "%epil.iter.next" = some (.int 64 n))
    (hbit : evalICmp .slt e t3Cap = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3EpilHeadEnv env i e n)
        { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" }) := by
  refine numFast_step_at (s' := stateAt (t3EpilHeadEnv env i e n) s)
    (b := ⟨"for.body87.i.i.epil", t3EpilHeadInstrs,
      Term.condbr (Operand.reg "%cmp88.i.i.epil")
        "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_epil_head_find
  · exact t3_epil_head_denote_back (calls := calls) hpre hi he hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3EpilHeadEnv env i e n) s) _
      "if.then90.i.i.epil" "for.inc98.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The accumulator's `Nat` reading

The chain's successor cell is `10 * e + d` as a `BitVec`.  What the ladder's
tests and its bound read is that cell's `Nat` value, and the four steps below
recover it: the byte is a digit (so `d >= 48`), the accumulator is inside the
bound (so the multiplication does not wrap), and the byte's widen is the byte. -/

/-- The `Nat` reading of a store's successor cell, at a digit's byte and an
accumulator small enough that the multiplication does not wrap. -/
theorem t3_store_next_toNat {e : BitVec 64} {d : UInt8}
    (he : e.toNat < 10 ^ 7) (hpos : 48 ≤ d.toNat) (hbyte : d.toNat ≤ 57) :
    (((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat).toNat
      = 10 * e.toNat + (d.toNat - 48) := by
  have hb : ((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat
      = BitVec.ofNat 64 (10 * e.toNat + (d.toNat - 48)) := by
    rw [vByte_toNat]
    bv_omega
  rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The successor cell's `Nat` reading is at most the cap's decade while the
accumulator is inside the bound: the store cannot leave a word above `10 ^ 7`. -/
theorem t3_store_next_lt {e : BitVec 64} {d : UInt8}
    (he : e.toNat < 10 ^ 6) (hpos : 48 ≤ d.toNat) (hbyte : d.toNat ≤ 57) :
    (((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat).toNat
        < 10 ^ 7 ∧
      10 * e.toNat + (d.toNat - 48) = (((e * 10#64) + 0xffffffffffffffd0#64) +
        BitVec.ofNat 64 (vByte d).toNat).toNat := by
  have hlt : e.toNat < 10 ^ 7 := by
    have : (10 : Nat) ^ 6 = 1000000 := by decide
    have : (10 : Nat) ^ 7 = 10000000 := by decide
    omega
  have hread := t3_store_next_toNat hlt hpos hbyte
  refine ⟨?_, hread.symm⟩
  rw [hread]
  have : (10 : Nat) ^ 7 = 10000000 := by decide
  omega

/-! ### Axiom footprints -/

#print axioms t3Cap_toNat
#print axioms slt_one_iff
#print axioms vByte_toNat
#print axioms t3_head_denote_entry
#print axioms t3_head_denote_back
#print axioms t3_test_denote
#print axioms t3_store_denote
#print axioms t3_latch_denote
#print axioms t3_epil_head_denote_entry
#print axioms t3_epil_head_denote_back
#print axioms t3_if_then90_step_epil
#print axioms t3_latch_epil_step_exit
#print axioms t3_store_next_toNat

end NumFastTier3Copy

end LeanLLVM.Refinement
