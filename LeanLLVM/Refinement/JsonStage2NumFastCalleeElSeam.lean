/-
The exponent's body at the release path's call.

`JsonStage2NumFastCalleeElRun` carries the pinned body's answer at the kernel's
argument list (`numElBodyCalls_eq` for a nonzero mantissa,
`numElBodyCalls_eq_zero` for the zero word).  The body is reached from
`if.end268`, the block that calls `num_el_el1` on the conversion's release path;
`JsonStage2NumFastArm` pins the block, `JsonStage2NumFastCalls` states its chain
at any answer the selection gives, and `JsonStage2NumFastTier2` ties the model's
table to the emitted rows.  This module is the composition: the site's
denotation read off the body's run, at the tree's own table.

**The identification.**  The body's selection answers only `num_el_el1` and
delegates every other symbol to its base, while the release selection
`stage2NumFastCalls` answers the reader and the multiply as well; the two are
different `Calls` values (`numElBodyCalls_ne_stage2NumFastCalls`), and no
statement can identify them.  What the site reads is one point: the kernel's
answer.  `numFast_numEl_selection_eq_body` identifies the two there —
`numElBodyCalls_eq` for the body's run, `stage2NumFastCalls_num_el` for the
selection's — so the site consumes the arm without pretending the selections
coincide.

**The table's three facts.**  `guardTable` is the emitted table under the model's
field names, and `JsonStage2NumFastTier2` proves the facts a row needs: its `hi`
is a sixty-four-bit word (`guardTable_hi_lt`), its `e` lies in the kernel's
`int32_t` slot (`guardTable_e_bounds`, the `decide` sweep of the ninety-one
`epow_table.h` rows), and a row exists only inside the range gate
(`guardTable_range`).  At `epow = guardTable` these are consequences of the
lookup, so the arm's own hypotheses — `hhi`, `heLo`, `heHi` and `hrange` — are
discharged by `hep` and only the staging remains: the row's bytes behind
`eRow q`, the counter's word, and the two body-side bounds.

**What is not here.**  The staging itself: `NumElRow mem (eRow q) t` says the
memory holds the row the emitted `getelementptr` addresses, and
`readBytes mem numElWindowAddr 8 = some (natToBytes k 8)` says the counter's cell
holds a word.  Neither is a fact about the release path's initial memory in this
tree — the table's 91 rows have no staging of their own, unlike
`NUMF_EL1_P10`/`NUMF_EL1_POW10` — so both are hypotheses here, not discharges.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier2
import LeanLLVM.Refinement.JsonStage2NumFastCalleeElRun

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The two selections

The kernel's answer is the one point the site reads, and there the two values
agree.  Everywhere else they do not, which is why the identification is stated
pointwise rather than as an equality of environments. -/

/-- **The two selections are not equal as `Calls`.**  `numElBodyCalls` answers the
kernel and delegates everything else to its base, while `stage2NumFastCalls`
answers the reader and the multiply too: at `num_d8_el1` the first is the walk's
`none` and the second is the reader's answer. -/
theorem numElBodyCalls_ne_stage2NumFastCalls (epow : Int → Option EPow) :
    numElBodyCalls s2HelperCalls epow ≠ stage2NumFastCalls epow := by
  intro h
  have hbody : numElBodyCalls s2HelperCalls epow "num_d8_el1" [.ptr 0, .ptr 0] [] 0
      = none := by
    simp only [numElBodyCalls, ite_eq_right (by decide : ¬ ("num_d8_el1" = "num_el_el1")),
      s2HelperCalls_num_d8_el1]
  have hsel : stage2NumFastCalls epow "num_d8_el1" [.ptr 0, .ptr 0] ([] : Mem) 0 ≠ none := by
    have hread : readBytes ([] : Mem) 0 8 = none := by decide
    rw [stage2NumFastCalls_num_d8]
    rw [show numD8Answer [.ptr 0, .ptr 0] ([] : Mem) 0
        = some { ret := .int 32 0, mem := [], next := 0 } from by
      simp only [numD8Answer, hread]]
    simp
  rw [h] at hbody
  exact hsel hbody

/-- **The body's answer is the release selection's at the kernel's call.**  At a
staged row and counter the release selection answers `num_el_el1` with the pinned
body's run: the selection's answer at this callee is the model's
(`stage2NumFastCalls_num_el`), and the arm is the model's
(`numElBodyCalls_eq`). -/
theorem numFast_numEl_selection_eq_body (base : Calls) (epow : Int → Option EPow)
    (w q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat) (t : EPow) (row k : Nat)
    (hrow : NumElRow mem row t) (hrowAddr : eRow q = row) (hhi : t.hi < 2 ^ 64)
    (hw : w ≠ 0) (hep : epow q.toInt = some t)
    (hrange : -45 ≤ q.toInt ∧ q.toInt ≤ 45)
    (heLo : -(2 ^ 31 : Int) ≤ t.e) (heHi : t.e < 2 ^ 31)
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub q).toNat < 2 ^ 63) :
    stage2NumFastCalls epow "num_el_el1" [.int 64 w, .int 64 q, .ptr out] mem next
      = numElBodyCalls base epow "num_el_el1" [.int 64 w, .int 64 q, .ptr out] mem next := by
  rw [stage2NumFastCalls_num_el]
  rw [← numElBodyCalls_eq base epow w q out mem next t row k hrow hrowAddr hhi hw hep
    hrange heLo heHi hcount hk hsub]

/-- **At the tree's table the arm's table facts are the lookup's.**  `hep` names
the row, and the guard's own sweep gives the row's `hi` word, its exponent bound
and the range gate it passed. -/
theorem numFast_numEl_selection_eq_body_guardTable (base : Calls)
    (w q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat) (t : EPow) (row k : Nat)
    (hrow : NumElRow mem row t) (hrowAddr : eRow q = row) (hw : w ≠ 0)
    (hep : guardTable q.toInt = some t)
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub q).toNat < 2 ^ 63) :
    stage2NumFastCalls guardTable "num_el_el1" [.int 64 w, .int 64 q, .ptr out] mem next
      = numElBodyCalls base guardTable "num_el_el1" [.int 64 w, .int 64 q, .ptr out]
          mem next := by
  obtain ⟨heLo, heHi⟩ := guardTable_e_bounds hep
  exact numFast_numEl_selection_eq_body base guardTable w q out mem next t row k hrow
    hrowAddr (guardTable_hi_lt hep) hw hep (guardTable_range hep) heLo heHi hcount hk hsub

/-- **The zero mantissa's answer is the release selection's at the kernel's
call.**  The range gate is the only table fact the zero word needs. -/
theorem numFast_numEl_selection_eq_body_zero (base : Calls) (epow : Int → Option EPow)
    (q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat)
    (hrange : -45 ≤ q.toInt ∧ q.toInt ≤ 45) :
    stage2NumFastCalls epow "num_el_el1" [.int 64 0#64, .int 64 q, .ptr out] mem next
      = numElBodyCalls base epow "num_el_el1" [.int 64 0#64, .int 64 q, .ptr out]
          mem next := by
  rw [stage2NumFastCalls_num_el, ← numElBodyCalls_eq_zero base epow q out mem next hrange]

/-! ### The site

`if.end268` is the block: the marker, the kernel's call and the decision's bit.
`numFast_ifEnd268_denote_answer` is its chain at any answer the selection gives;
the answer is the body's, through the identification above. -/

/-- **`if.end268` at the pinned body's answer.**  The release path's site denotes
at whatever outcome the body's run returns, at the tree's table: the kernel's
call is the run's answer and the block's bit is the run's return test. -/
theorem numFast_ifEnd268_denote_body (base : Calls) {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat} {r : CallOutcome} {x : BitVec 32}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hx : r.ret = .int 32 x)
    (hrun : numElRunAnswer guardTable a b q s.mem s.next = some r)
    (t : EPow) (row k : Nat) (hrow : NumElRow s.mem row t) (hrowAddr : eRow b = row)
    (hw : a ≠ 0) (hep : guardTable b.toInt = some t)
    (hcount : readBytes s.mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub b).toNat < 2 ^ 63) :
    denoteCode (stage2NumFastCalls guardTable) numFastIfEnd268Instrs (stateAt env s) =
      some (stateAt
        (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
         ("%call270", .int 32 x) :: env)
        { s with mem := r.mem, next := r.next }) := by
  have hsome : stage2NumFastCalls guardTable "num_el_el1"
      [.int 64 a, .int 64 b, .ptr q] s.mem s.next = some r := by
    rw [numFast_numEl_selection_eq_body_guardTable base a b q s.mem s.next t row k
      hrow hrowAddr hw hep hcount hk hsub, numElBodyCalls_num_el]
    exact hrun
  exact numFast_ifEnd268_denote_answer guardTable ha hb hd hx hsome

/-- **`if.end268` at the pinned body's zero-mantissa answer.**  The body's zero
arm writes `out` and returns one; the site's bit is the run's. -/
theorem numFast_ifEnd268_denote_body_zero (base : Calls) {env : Env} {s : State}
    {b : BitVec 64} {q : Nat} {r : CallOutcome} {x : BitVec 32}
    (ha : lookupName env "%add244" = some (.int 64 0#64))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hx : r.ret = .int 32 x)
    (hrun : numElRunAnswer guardTable 0#64 b q s.mem s.next = some r)
    (hrange : -45 ≤ b.toInt ∧ b.toInt ≤ 45) :
    denoteCode (stage2NumFastCalls guardTable) numFastIfEnd268Instrs (stateAt env s) =
      some (stateAt
        (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
         ("%call270", .int 32 x) :: env)
        { s with mem := r.mem, next := r.next }) := by
  have hsome : stage2NumFastCalls guardTable "num_el_el1"
      [.int 64 0#64, .int 64 b, .ptr q] s.mem s.next = some r := by
    rw [numFast_numEl_selection_eq_body_zero base guardTable b q s.mem s.next hrange,
      numElBodyCalls_num_el]
    exact hrun
  exact numFast_ifEnd268_denote_answer guardTable ha hb hd hx hsome

/-- **The block's accepted branch at the body's answer.**  At a run that returns
one — the kernel's acceptance — the site binds `%tobool271.not = 0` and
`%call270 = 1`, the branch to `cleanup282.thread462`, and its memory is the run's.
This is the seam's use: the block's bit is the body's return test. -/
theorem numFast_ifEnd268_denote_body_accepted (base : Calls) {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat} {m : Mem} {n : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hrun : numElRunAnswer guardTable a b q s.mem s.next =
      some { ret := .int 32 1, mem := m, next := n })
    (t : EPow) (row k : Nat) (hrow : NumElRow s.mem row t) (hrowAddr : eRow b = row)
    (hw : a ≠ 0) (hep : guardTable b.toInt = some t)
    (hcount : readBytes s.mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub b).toNat < 2 ^ 63) :
    denoteCode (stage2NumFastCalls guardTable) numFastIfEnd268Instrs (stateAt env s) =
      some (stateAt
        (("%tobool271.not", .int 1 0) ::
         ("%call270", .int 32 1) :: env)
        { s with mem := m, next := n }) := by
  rw [numFast_ifEnd268_denote_body base ha hb hd (r :=
    { ret := .int 32 1, mem := m, next := n }) (x := 1) rfl hrun t row k hrow
    hrowAddr hw hep hcount hk hsub]
  rfl

/-- **The block's refused branch at the body's answer.**  At a run that returns
zero — the kernel's refusal — the site binds `%tobool271.not = 1` and
`%call270 = 0`, the branch to `cleanup282`, and its memory is the run's. -/
theorem numFast_ifEnd268_denote_body_refused (base : Calls) {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat} {m : Mem} {n : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hrun : numElRunAnswer guardTable a b q s.mem s.next =
      some { ret := .int 32 0, mem := m, next := n })
    (t : EPow) (row k : Nat) (hrow : NumElRow s.mem row t) (hrowAddr : eRow b = row)
    (hw : a ≠ 0) (hep : guardTable b.toInt = some t)
    (hcount : readBytes s.mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub b).toNat < 2 ^ 63) :
    denoteCode (stage2NumFastCalls guardTable) numFastIfEnd268Instrs (stateAt env s) =
      some (stateAt
        (("%tobool271.not", .int 1 1) ::
         ("%call270", .int 32 0) :: env)
        { s with mem := m, next := n }) := by
  rw [numFast_ifEnd268_denote_body base ha hb hd (r :=
    { ret := .int 32 0, mem := m, next := n }) (x := 0) rfl hrun t row k hrow
    hrowAddr hw hep hcount hk hsub]
  rfl

/-- **The zero-mantissa branch at the body's answer.**  The zero arm returns one
and writes `out`; the site's bit is the run's. -/
theorem numFast_ifEnd268_denote_body_zero_accepted (base : Calls) {env : Env} {s : State}
    {b : BitVec 64} {q : Nat} {m : Mem} {n : Nat}
    (ha : lookupName env "%add244" = some (.int 64 0#64))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hrun : numElRunAnswer guardTable 0#64 b q s.mem s.next =
      some { ret := .int 32 1, mem := m, next := n })
    (hrange : -45 ≤ b.toInt ∧ b.toInt ≤ 45) :
    denoteCode (stage2NumFastCalls guardTable) numFastIfEnd268Instrs (stateAt env s) =
      some (stateAt
        (("%tobool271.not", .int 1 0) ::
         ("%call270", .int 32 1) :: env)
        { s with mem := m, next := n }) := by
  rw [numFast_ifEnd268_denote_body_zero base ha hb hd (r :=
    { ret := .int 32 1, mem := m, next := n }) (x := 1) rfl hrun hrange]
  rfl

/-! ### Axiom footprints

The sweep, the table's lemmas and the site carry no `sorryAx`; `decide` supplies
the table's bound and `Classical.choice` reaches the arm through
`numElBodyCalls_eq`'s bridge, as it does in that module.  The zero mantissa's
identification does not go through that bridge, so its footprint is the standard
one. -/

/-- info: 'LeanLLVM.Refinement.epow_rows_e_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms epow_rows_e_bounds

/-- info: 'LeanLLVM.Refinement.epow_e_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epow_e_bounds

/-- info: 'LeanLLVM.Refinement.epowAt_e_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epowAt_e_bounds

/-- info: 'LeanLLVM.Refinement.guardTable_e_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms guardTable_e_bounds

/-- info: 'LeanLLVM.Refinement.guardTable_hi_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms guardTable_hi_lt

/-- info: 'LeanLLVM.Refinement.guardTable_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms guardTable_range

/-- info: 'LeanLLVM.Refinement.numFast_numEl_selection_eq_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_numEl_selection_eq_body

/-- info: 'LeanLLVM.Refinement.numFast_numEl_selection_eq_body_guardTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms numFast_numEl_selection_eq_body_guardTable

/-- info: 'LeanLLVM.Refinement.numFast_numEl_selection_eq_body_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_numEl_selection_eq_body_zero

/-- info: 'LeanLLVM.Refinement.numElBodyCalls_ne_stage2NumFastCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numElBodyCalls_ne_stage2NumFastCalls

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd268_denote_body

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_body_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd268_denote_body_zero

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_body_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms numFast_ifEnd268_denote_body_accepted

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_body_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms numFast_ifEnd268_denote_body_refused

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_body_zero_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms numFast_ifEnd268_denote_body_zero_accepted

end LeanLLVM.Refinement
