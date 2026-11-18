/-
A block's write set, and the register transport a path across it licenses.

`Path` (`LoopFuel`) carries a property across a region when every admitted step
preserves it.  The property a caller usually has is about one **cell**: a register
or a symbol read out of the environment.  This module supplies the step-level
fact — a successful jump whose block writes none of a name leaves that name where
it was — and the three write-set readings of it:

* `UnwrittenBy f n`: no block of `f` writes `n`;
* `WrittenOnlyAt f n pc`: only the block `pc` writes `n`;
* `PreservedAlong f n ok`: every block the path's filter admits writes none of
  `n`, which is the hypothesis `Path.lookupName` takes.

The step lemma is the one `JsonStage2NumFastCells` used to state at its pinned
body, generalised once over the function.  Its proof is the block's
`denoteCode`, the entry emitter's instruction-list lemma, and the terminator,
which moves the program counter and nothing else.

`WrittenOnlyAt` is what makes a fact such as "the sign survives after leaving the
block that writes it" an instance rather than a second induction: the path's
filter excludes the one block, and `Path.lookupNameOutside` transports the
register along it.  For a store or a call, a register's survival says nothing
about its pointee; that is separation plus the callee's write frame, and is a
different rule.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The write-set readings -/

/-- **No block writes `n`.**  The strong form: a register or symbol that survives
every block of the body, so it survives any path without a filter.  An `abbrev`,
so a `decide` elaborates against the function's blocks. -/
abbrev UnwrittenBy (f : Function) (n : String) : Prop :=
  ∀ b ∈ f.blocks, ∀ i ∈ b.instrs, i.dst? ≠ some n

/-- **Only `pc` writes `n`.**  The narrow form the sign needs: the dispatch's
`if.end` leaves its `phi`'s cell, and a path that does not visit `if.end` carries
the value. -/
abbrev WrittenOnlyAt (f : Function) (n pc : String) : Prop :=
  ∀ b ∈ f.blocks, b.name ≠ pc → ∀ i ∈ b.instrs, i.dst? ≠ some n

/-- **The filter's write set.**  Every block a path's filter admits writes none of
`n`.  This is the hypothesis `Path.lookupName` consumes. -/
abbrev PreservedAlong (f : Function) (n : String) (ok : String → Prop) : Prop :=
  ∀ b ∈ f.blocks, ok b.name → ∀ i ∈ b.instrs, i.dst? ≠ some n

/-- An unwritten name is preserved along every filter. -/
theorem preservedAlong_of_unwritten {f : Function} {n : String} {ok : String → Prop}
    (h : UnwrittenBy f n) : PreservedAlong f n ok :=
  fun b hb _ => h b hb

/-- A name written only at `pc` is preserved along a filter that excludes it. -/
theorem preservedAlong_of_writtenOnlyAt {f : Function} {n pc : String}
    {ok : String → Prop} (h : WrittenOnlyAt f n pc) (hok : ∀ b, ok b → b ≠ pc) :
    PreservedAlong f n ok :=
  fun b hb hk => h b hb (hok b.name hk)

/-! ### A step's non-interference -/

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

/-- A block found by name is named that name.  Private: the walk's modules state
their own copy at their own bodies, and this one serves the step lemma below. -/
private theorem findBlockList_name {bs : List Block} {n : String} {b : Block}
    (h : findBlockList bs n = some b) : b.name = n := by
  induction bs with
  | nil => simp [findBlockList] at h
  | cons b' rest ih =>
      simp only [findBlockList] at h
      split at h
      · next hb => cases h; exact hb
      · exact ih h

/-- **A step's non-interference, over any function.**  A block that writes none
of `n` is a `denoteCode` that leaves `n` where it was, and the terminator changes
only the program counter.  This is `JsonStage2NumFastCells`'
`numFast_step_lookup` with the pinned body generalised to `f`. -/
theorem step_lookupName {calls : Calls} {f : Function} {s s' : State} {n : String}
    (hs : LeanLLVM.step calls f s = .jump s')
    (hno : ∀ b ∈ f.blocks, b.name = s.pc → ∀ i ∈ b.instrs, i.dst? ≠ some n) :
    lookupName s'.env n = lookupName s.env n := by
  cases hf : f.findBlock s.pc with
  | none => rw [step, hf] at hs; cases hs
  | some b =>
      simp only [step, hf] at hs
      have hname : b.name = s.pc := findBlockList_name hf
      have hmem : b ∈ f.blocks := findBlockList_mem hf
      cases hd : denoteCode calls b.instrs s with
      | none => simp only [hd] at hs; cases hs
      | some s1 =>
          simp only [hd] at hs
          rw [execTerm_env hs]
          exact JsonEntrySteps.denoteCode_lookupName calls b.instrs n
            (hno b hmem hname) s s1 hd

/-! ### Transport along a path -/

/-- **A path's register transport.**  A name none of the path's admitted blocks
writes is the same at the path's end as at its start. -/
theorem Path.lookupName {calls : Calls} {f : Function} {ok : String → Prop}
    {n : String} (hno : PreservedAlong f n ok) {s e : State}
    (h : Path calls f ok s e) :
    LeanLLVM.lookupName e.env n = LeanLLVM.lookupName s.env n :=
  Path.transport (P := fun t => LeanLLVM.lookupName t.env n = LeanLLVM.lookupName s.env n)
    (fun a b hk hs hP =>
      (step_lookupName hs (fun bl hb hbn => hno bl hb (by rw [hbn]; exact hk))).trans hP)
    h rfl

/-- **A path that avoids the one writer.**  The sign case: `n` is `pc`'s alone
and the path's filter excludes `pc`, so the value written before the path is the
value at its end. -/
theorem Path.lookupNameOutside {calls : Calls} {f : Function} {ok : String → Prop}
    {n pc : String} (hwrite : WrittenOnlyAt f n pc) (hok : ∀ b, ok b → b ≠ pc)
    {s e : State} (h : Path calls f ok s e) :
    LeanLLVM.lookupName e.env n = LeanLLVM.lookupName s.env n :=
  Path.lookupName (preservedAlong_of_writtenOnlyAt hwrite hok) h

/-- **A path's cell transport.**  The same, for a register already known to hold
a value: the value survives the path. -/
theorem Path.lookupName_eq {calls : Calls} {f : Function} {ok : String → Prop}
    {n : String} {v : Value} (hno : PreservedAlong f n ok) {s e : State}
    (h : Path calls f ok s e) (hs : LeanLLVM.lookupName s.env n = some v) :
    LeanLLVM.lookupName e.env n = some v :=
  (Path.lookupName hno h).trans hs

/-- **A path preserves a list of unwritten cells.**  The form the kept-cell
predicates take: every name of the list survives the path. -/
theorem Path.lookupName_all {calls : Calls} {f : Function} {ok : String → Prop}
    {ns : List String} (hno : ∀ n ∈ ns, PreservedAlong f n ok) {s e : State}
    (h : Path calls f ok s e) :
    ∀ n ∈ ns, LeanLLVM.lookupName e.env n = LeanLLVM.lookupName s.env n :=
  fun n hn => Path.lookupName (hno n hn) h

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.execTerm_env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms execTerm_env

/-- info: 'LeanLLVM.Refinement.step_lookupName' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_lookupName

/-- info: 'LeanLLVM.Refinement.Path.lookupName' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Path.lookupName

/-- info: 'LeanLLVM.Refinement.Path.lookupNameOutside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Path.lookupNameOutside

/-- info: 'LeanLLVM.Refinement.Path.lookupName_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Path.lookupName_eq

/-- info: 'LeanLLVM.Refinement.Path.lookupName_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Path.lookupName_all

end LeanLLVM.Refinement
