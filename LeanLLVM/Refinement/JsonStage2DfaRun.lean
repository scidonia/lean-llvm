/-
The DFA walk's stack and its run, abstracted to the certified configurations.

`JsonStage2DfaTable` proves each table row is a certified value/container rule.
This module takes the next step: the stack the DFA keeps, the abstract run of
the certified rules over an entry trace, and the theorem that the DFA's run is
the certified run read through `Abs`.

## The stack

The C walk keeps `stk[SD_MAXD]` and `sp`; on opening a container it writes
`stk[sp - 1] = sd_restore[prev]` when `sp > 0`, and on closing it sets
`state = sp ? stk[sp - 1] : SD_ROOT_END`.  The slot at index `sp - 1` is the
current container's own resume slot: it is written when that container opens a
child, and read only when that child closes.  The deepest slot is therefore
never read before it is written, so the model keeps only the meaningful resume
bytes: `DfaState.parents`, in C order, whose `map Abs` is the abstract list of
parent configurations after their children's values.

`openParents` appends `sdRestore st` exactly when the current state is a
container, which is where the C's `if (sp)` guard writes; from the root it
appends nothing, because the root's resume is the depth-zero close rule.  The
proof that the appended byte is `afterValue (Abs st)` is `sdRestore_sound`.
Closing drops the last parent and resumes the new last one, or `SD_ROOT_END`
from the root; `resumeState_abs` and `map_dropLast_abs` carry the abstraction
across the list operations.

## The run

`stepAbs` is the certified rule at a configuration and a symbol, with a close
resuming the top parent and an open pushing the parent's after-value; `stepDfa`
is the table's rule with the stack.  `stepDfa_abs` states
`(stepDfa d sym).map dfaAbsState = stepAbs a sym`, so the DFA's step is the
certified step after abstraction.  `runDfa_abs` lifts this to a trace, and
`runDfa_some_of_abs` gives the acceptance statement: a trace the certified
rules accept is a trace the DFA runs without taking an `A_ERR` row.  The
row-level form is `stepDfa_eq_none_iff`; the `#guard`s beside it are the
detector's affirmative controls.

## What this module does not state

The `k`, `xj`, `z.alen`, `z.ev.len` and `mem` clauses of the walk's loop
invariant are body-level: they are read and written by the emitted instructions
and by the helper calls, not by the table.  This module states the abstract
state and stack equality; the cursor/memory equality is the remaining loop
obligation and needs the DFA body fixture, which is not in this tree.
-/
import LeanLLVM.Refinement.JsonStage2DfaTable

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The stack model -/

/-- The DFA's state and the meaningful stack slots, bottom first. -/
structure DfaState where
  st : St
  parents : List St
  deriving DecidableEq, Repr

/-- The certified configuration and its parents, bottom first. -/
structure AbsState where
  cfg : Cfg
  frames : List Cfg
  deriving DecidableEq, Repr

/-- The abstraction of a DFA state: the table state's configuration and the
resume bytes' parent configurations. -/
def dfaAbsState (d : DfaState) : AbsState :=
  ⟨Abs d.st, d.parents.map Abs⟩

/-- The slot each open container writes when it opens a child.  From the root
the C guard `if (sp)` writes nothing. -/
def openParents (d : DfaState) : List St :=
  if d.st = .root then d.parents else d.parents ++ [sdRestore d.st]

/-- The state a close resumes: the parent's resume byte, or the root's end. -/
def resumeState (parents : List St) : St :=
  parents.getLast?.getD .rootEnd

/-- The last parent configuration, or the root's end. -/
def resumeCfg (frames : List Cfg) : Cfg :=
  frames.getLast?.getD (.root true)

/-! ### List lemmas for the stack abstraction -/

/-- `getLast?` commutes with `map`. -/
theorem getLast?_map_abs (l : List St) :
    (l.map Abs).getLast? = (l.getLast?).map Abs := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b u => simpa [List.getLast?_cons_cons] using ih

/-- `dropLast` commutes with `map`. -/
theorem map_dropLast_abs (l : List St) :
    (l.dropLast).map Abs = (l.map Abs).dropLast := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b u => simp

/-- The resumed state's abstraction is the last parent's configuration. -/
theorem resumeState_abs (parents : List St) :
    Abs (resumeState parents) = resumeCfg (parents.map Abs) := by
  unfold resumeState resumeCfg
  induction parents with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b u => simpa [List.getLast?_cons_cons] using ih

/-- The same equation with `Abs` written out, so a `simp` that has already
unfolded `Abs` can still rewrite it. -/
theorem resumeState_abs_match (parents : List St) :
    (match resumeState parents with
     | .root => Cfg.root false
     | .rootEnd => .root true
     | .objFirst => .obj 0
     | .objKey => .obj 4
     | .objColon => .obj 1
     | .objVal => .obj 2
     | .objComma => .obj 3
     | .arrFirst => .arr 0
     | .arrVal => .arr 2
     | .arrComma => .arr 1) =
      resumeCfg (parents.map Abs) :=
  resumeState_abs parents

/-! ### Ground phase values, for the `simp` that unfolds `Abs` -/

@[simp] theorem fin5_val_zero : ((0 : Fin 5) : Nat) = 0 := by decide
@[simp] theorem fin5_val_one : ((1 : Fin 5) : Nat) = 1 := by decide
@[simp] theorem fin5_val_two : ((2 : Fin 5) : Nat) = 2 := by decide
@[simp] theorem fin5_val_three : ((3 : Fin 5) : Nat) = 3 := by decide
@[simp] theorem fin5_val_four : ((4 : Fin 5) : Nat) = 4 := by decide
@[simp] theorem fin3_val_zero : ((0 : Fin 3) : Nat) = 0 := by decide
@[simp] theorem fin3_val_one : ((1 : Fin 3) : Nat) = 1 := by decide
@[simp] theorem fin3_val_two : ((2 : Fin 3) : Nat) = 2 := by decide

/-- The resume equation at `objVal`, in the form a `simp` that has unfolded
`Abs` can read. -/
@[simp] theorem sdRestore_match_objVal :
    (match sdRestore .objVal with
     | .root => Cfg.root false
     | .rootEnd => .root true
     | .objFirst => .obj 0
     | .objKey => .obj 4
     | .objColon => .obj 1
     | .objVal => .obj 2
     | .objComma => .obj 3
     | .arrFirst => .arr 0
     | .arrVal => .arr 2
     | .arrComma => .arr 1) = .obj 3 := by decide

/-- The resume equation at `arrFirst`. -/
@[simp] theorem sdRestore_match_arrFirst :
    (match sdRestore .arrFirst with
     | .root => Cfg.root false
     | .rootEnd => .root true
     | .objFirst => .obj 0
     | .objKey => .obj 4
     | .objColon => .obj 1
     | .objVal => .obj 2
     | .objComma => .obj 3
     | .arrFirst => .arr 0
     | .arrVal => .arr 2
     | .arrComma => .arr 1) = .arr 1 := by decide

/-- The resume equation at `arrVal`. -/
@[simp] theorem sdRestore_match_arrVal :
    (match sdRestore .arrVal with
     | .root => Cfg.root false
     | .rootEnd => .root true
     | .objFirst => .obj 0
     | .objKey => .obj 4
     | .objColon => .obj 1
     | .objVal => .obj 2
     | .objComma => .obj 3
     | .arrFirst => .arr 0
     | .arrVal => .arr 2
     | .arrComma => .arr 1) = .arr 1 := by decide

/-! ### The two steps -/

/-- A configuration's current container is the root. -/
def Cfg.isRoot : Cfg → Bool
  | .root _ => true
  | _ => false

/-- The abstract open: a container parent records its after-value; the root
records nothing. -/
def openAbs (a : AbsState) (child : Cfg) : AbsState :=
  if a.cfg.isRoot then ⟨child, a.frames⟩
  else ⟨child, a.frames ++ [afterValue a.cfg]⟩

/-- The abstract close: resume the last parent, or the root's end. -/
def closeAbs (a : AbsState) : AbsState :=
  ⟨resumeCfg a.frames, a.frames.dropLast⟩

/-- The certified rule as a state transition, with a close resuming the stack. -/
def stepAbs (a : AbsState) (sym : Sym) : Option AbsState :=
  match certStep a.cfg sym with
  | none => none
  | some (act, next) =>
      match next with
      | some child =>
          if act = .openObj ∨ act = .openArr then some (openAbs a child)
          else some ⟨child, a.frames⟩
      | none => some (closeAbs a)

/-- The table's rule as a state transition, with the stack operations. -/
def stepDfa (d : DfaState) (sym : Sym) : Option DfaState :=
  match tableStep d.st sym with
  | none => none
  | some (act, next) =>
      match next with
      | some st' =>
          if act = .openObj ∨ act = .openArr then
            some ⟨st', openParents d⟩
          else some ⟨st', d.parents⟩
      | none =>
          some ⟨resumeState d.parents, d.parents.dropLast⟩

/-! ### The step refinement -/

/-- **The DFA's step is the certified step after abstraction.** -/
theorem stepDfa_abs (d : DfaState) (sym : Sym) :
    (stepDfa d sym).map dfaAbsState = stepAbs (dfaAbsState d) sym := by
  cases d with
  | mk st parents =>
      cases st <;> cases sym <;>
        simp [stepDfa, stepAbs, dfaAbsState, certStep, tableStep, sdTr, Abs,
          Cfg.isRoot, Cfg.tyByte, Cfg.cstByte, afterValue, openAbs, closeAbs,
          openParents, valuePos, valuePosOf, keyPos, closeOkObj, closeOkArr,
          commaOkObj, commaOkArr, colonOk, isClose, sdRestore,
          List.map_append, Bool.false_eq_true, reduceCtorEq]
      all_goals try exact resumeState_abs _

/-! ### The run over an entry trace -/

/-- Run the table's transition over a trace. -/
def runDfa : DfaState → List Sym → Option DfaState
  | d, [] => some d
  | d, s :: rest => stepDfa d s >>= fun d' => runDfa d' rest

/-- Run the certified rules over the same trace. -/
def runAbs : AbsState → List Sym → Option AbsState
  | a, [] => some a
  | a, s :: rest => stepAbs a s >>= fun a' => runAbs a' rest

/-- **The DFA's run is the certified run after abstraction.** -/
theorem runDfa_abs (d : DfaState) (trace : List Sym) :
    (runDfa d trace).map dfaAbsState = runAbs (dfaAbsState d) trace := by
  induction trace generalizing d with
  | nil => simp [runDfa, runAbs]
  | cons s rest ih =>
      cases hstep : stepDfa d s with
      | none =>
          have h := stepDfa_abs d s
          rw [hstep] at h
          simp only [Option.map_none] at h
          simp only [runDfa, runAbs, hstep]
          rw [← h]
          rfl
      | some d' =>
          have h := stepDfa_abs d s
          rw [hstep] at h
          simp only [Option.map_some] at h
          simp only [runDfa, runAbs, hstep]
          rw [← h]
          exact ih d'

/-! ### The entry cursor -/

/-- The number of entry positions a token consumes: a quote's closing entry is
the next one, as in `sd_walk`'s `ep[k++]` pair. -/
def symCost : Sym → Nat
  | .quote => 2
  | _ => 1

/-- The entry positions a token trace consumes. -/
def traceCost (trace : List Sym) : Nat :=
  (trace.map symCost).sum

/-- The run with its entry cursor: `k` advances by the token's cost. -/
def runDfaK : Nat → DfaState → List Sym → Option (Nat × DfaState)
  | k, d, [] => some (k, d)
  | k, d, s :: rest => stepDfa d s >>= fun d' => runDfaK (k + symCost s) d' rest

/-- **The cursor clause of the loop invariant, at the trace.**  The DFA's `k`
after the trace is the start plus the tokens' costs; the state is `runDfa`'s. -/
theorem runDfaK_eq (k : Nat) (d : DfaState) (trace : List Sym) :
    runDfaK k d trace = (runDfa d trace).map fun d' => (k + traceCost trace, d') := by
  induction trace generalizing k d with
  | nil => simp [runDfaK, runDfa, traceCost]
  | cons s rest ih =>
      cases hstep : stepDfa d s with
      | none => simp [runDfaK, runDfa, hstep, traceCost]
      | some d' =>
          simp [runDfaK, runDfa, hstep, traceCost, ih, Nat.add_assoc]

/-- **An accepted abstract trace is a DFA run that does not stop.**  The DFA
may take a different state representation, but every step it takes is a
non-`A_ERR` row: `stepDfa` returns `none` exactly at an `A_ERR` row
(`stepDfa_eq_none_iff`), and a run that returns is a run whose every step
returned. -/
theorem runDfa_some_of_abs (d : DfaState) (trace : List Sym) :
    runAbs (dfaAbsState d) trace ≠ none → runDfa d trace ≠ none := by
  intro h hd
  apply h
  have := runDfa_abs d trace
  rw [hd] at this
  simpa using this.symm

/-! ### The refusal row, and its detector -/

/-- The table marks this row `A_ERR`. -/
def rowIsErr (st : St) (sym : Sym) : Bool :=
  (sdTr st sym).1 == .err

/-- **A step stops exactly at an `A_ERR` row.** -/
theorem stepDfa_eq_none_iff (d : DfaState) (sym : Sym) :
    stepDfa d sym = none ↔ rowIsErr d.st sym = true := by
  cases d with
  | mk st parents =>
      cases st <;> cases sym <;>
        simp [stepDfa, tableStep, sdTr, rowIsErr, isClose, Bool.false_eq_true]

/-- A step that does not stop is a non-`A_ERR` row. -/
theorem stepDfa_row_not_err (d : DfaState) (sym : Sym)
    (h : stepDfa d sym ≠ none) : rowIsErr d.st sym = false := by
  cases hrow : rowIsErr d.st sym with
  | true => exact absurd ((stepDfa_eq_none_iff d sym).mpr hrow) h
  | false => rfl

/- The detector's affirmative control: a comma at the root is an `A_ERR`
row. -/
#guard rowIsErr .root .comma

/- The control the other way: an object opener at the root is not. -/
#guard !rowIsErr .root .lbrace

/- An accepted trace: the empty object runs from the root to the root's end on
both sides. -/
#guard decide (runDfa ⟨.root, []⟩ [.lbrace, .rbrace] = some ⟨.rootEnd, []⟩)
#guard decide (runAbs ⟨.root false, []⟩ [.lbrace, .rbrace] =
  some ⟨Cfg.root true, []⟩)

/- A refused trace: a comma at the root stops the DFA and the certified rules
both. -/
#guard decide (runDfa ⟨.root, []⟩ [.comma] = none)
#guard decide (runAbs ⟨.root false, []⟩ [.comma] = none)

/-- A successful nonempty run's first step does not stop. -/
theorem runDfa_cons_step_ne_none {d : DfaState} {sym : Sym} {rest : List Sym}
    {d' : DfaState} (h : runDfa d (sym :: rest) = some d') :
    stepDfa d sym ≠ none := by
  intro hnone
  simp [runDfa, hnone] at h

end LeanLLVM.Refinement
