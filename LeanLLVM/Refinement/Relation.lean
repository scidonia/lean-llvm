/-
A refinement relation for a pure 64-bit seam, with an explicit boundary
contract `Γ`.

The shape is the one the LLVM development uses:

  Γ ⊢ target ⊑ source

meaning every behaviour the target can produce on an input admitted by Γ is a
behaviour the source can produce.  For total, deterministic pure functions the
relation is equality under `Γ.pre`; `SemRefines` records the option-valued form
so the same statement can be reused when partiality or undefined behaviour
enters.

A seam that touches memory uses the memory-aware record `MemContract` at the
end of this module: its `pre`, `post` and `budget` are indexed by the argument
list and the memory, and `Satisfies` runs the body from the entry state the
arguments build.  `Contract` stays the pure seam's record; the two are siblings,
not one a later form of the other.
-/
import LeanLLVM.Semantics

namespace LeanLLVM.Refinement

/-- A boundary contract for a pure `BitVec 64 → BitVec 64` seam.

`pre` admits the inputs the caller promises; `post` is the observable
guarantee the seam must meet.  This is the pure seam's record; a stage that
touches memory uses `MemContract` below, whose fields are indexed by the
argument list and the memory.  The staging and footprint requirements a
memory-using certificate records live in that record's `pre` and `post`; target
configuration is not a field of either record, because this model has one
configuration and a field with no theorem behind it would be a false promise. -/
structure Contract where
  pre : BitVec 64 → Prop
  post : BitVec 64 → BitVec 64 → Prop

/-- Total semantics of a pure function, in the shape used by the LLVM
refinement relation. -/
def Sem (f : BitVec 64 → BitVec 64) : BitVec 64 → Option (BitVec 64) :=
  fun x => some (f x)

/-- Behaviour inclusion under the contract's precondition. -/
def SemRefines (Γ : Contract) (target source : BitVec 64 → Option (BitVec 64)) : Prop :=
  ∀ x y, Γ.pre x → target x = some y → source x = some y

/-- Pure equality form: under the precondition, the target returns what the
source returns. -/
def Refines (Γ : Contract) (target source : BitVec 64 → BitVec 64) : Prop :=
  ∀ x, Γ.pre x → target x = source x

/-- `Γ ⊢ target ⊑ source`. -/
notation:50 Γ:max " ⊢ " target " ⊑ " source => Refines Γ target source

/-- The option-valued relation and the equality form agree for total pure
functions. -/
theorem semRefines_total {Γ : Contract} {t s : BitVec 64 → BitVec 64} :
    SemRefines Γ (Sem t) (Sem s) ↔ Refines Γ t s := by
  constructor
  · intro h x hx
    exact (Option.some.inj (h x (t x) hx rfl)).symm
  · intro h x y hx hy
    cases hy
    exact congrArg some (h x hx).symm

theorem Refines.refl (Γ : Contract) (f : BitVec 64 → BitVec 64) : Γ ⊢ f ⊑ f :=
  fun _ _ => rfl

theorem Refines.trans {Γ : Contract} {a b c : BitVec 64 → BitVec 64}
    (hab : Γ ⊢ a ⊑ b) (hbc : Γ ⊢ b ⊑ c) : Γ ⊢ a ⊑ c :=
  fun x hx => (hab x hx).trans (hbc x hx)

theorem Refines.symm {Γ : Contract} {a b : BitVec 64 → BitVec 64}
    (h : Γ ⊢ a ⊑ b) : Γ ⊢ b ⊑ a :=
  fun x hx => (h x hx).symm

/-- The source meets the contract's postcondition. -/
def Correct (Γ : Contract) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ x, Γ.pre x → Γ.post x (f x)

/-- Correctness transfers from source to target along refinement. -/
theorem Correct.of_refines {Γ : Contract} {t s : BitVec 64 → BitVec 64}
    (hr : Γ ⊢ t ⊑ s) (hs : Correct Γ s) : Correct Γ t :=
  fun x hx => by
    rw [hr x hx]
    exact hs x hx

/-! ### Contextual replacement -/

/-- A caller context: it computes with the seam at a list of arguments.  The
context is represented by the arguments it passes to the seam and a fold over
their results. -/
structure Context where
  args : BitVec 64 → List (BitVec 64)
  pre : BitVec 64 → Prop

/-- The context only calls the seam at admissible inputs. -/
def Context.admissible (Γ : Contract) (C : Context) : Prop :=
  ∀ x, C.pre x → ∀ a ∈ C.args x, Γ.pre a

/-- The observable result of a context, given a seam implementation. -/
def Context.run (C : Context) (f : BitVec 64 → BitVec 64) (x : BitVec 64) : BitVec 64 :=
  (C.args x).foldl (fun acc a => acc + f a) 0

theorem foldl_add_congr {f g : BitVec 64 → BitVec 64} (init : BitVec 64) :
    ∀ (l : List (BitVec 64)), (∀ a ∈ l, f a = g a) →
      l.foldl (fun acc a => acc + f a) init = l.foldl (fun acc a => acc + g a) init
  | [], _ => rfl
  | a :: as, h => by
      simp only [List.foldl_cons]
      rw [h a (by simp)]
      exact foldl_add_congr (init + g a) as (fun b hb => h b (by simp [hb]))

/-- Replacing a seam by a refinement preserves every caller that only calls it
at admissible inputs. -/
theorem Context.refines {Γ : Contract} {t s : BitVec 64 → BitVec 64} {C : Context}
    (h : Γ ⊢ t ⊑ s) (ha : C.admissible Γ) :
    ∀ x, C.pre x → C.run t x = C.run s x := by
  intro x hx
  unfold Context.run
  exact foldl_add_congr 0 (C.args x) (fun a ha' => h a (ha x hx a ha'))

/-! ### The memory-aware relation

`Contract` above is the pure seam's record.  A stage that writes the caller's
memory needs a record read at the caller's memory and allocator, and a relation
that runs its body from the state its arguments build.  `MemContract`,
`EntryState` and `Satisfies` are that record and relation; `envForUnit` and the
two bridges connect them to the call level, where a selection answers a
`CallOutcome` rather than an `Outcome`.
-/

open LeanLLVM

/-- The words an entry stream holds at `e`: `n` little-endian 64-bit words read
back out of memory.

This is the extractor a memory-indexed budget needs: `entry_b8_refines` binds
its `ent` from memory by `readBytes mem e (8 * ent.length) = some (wordsOf ent)`,
so a record whose budget folds over `ent` can only name that fuel by reading the
same words back out of the same memory. -/
def wordsAt (mem : Mem) (e n : Nat) : List (BitVec 64) :=
  (List.range n).map fun i =>
    BitVec.ofNat 64 (bytesToNat ((readBytes mem (e + 8 * i) 8).getD []))

/-- The boundary record of a stage that touches memory.

`budget` is a function of the argument list **and the memory**, not a constant
and not an `args`-only function: a fuel that folds over words read out of
memory (B8's `b8RunSteps ent + nblk + 2`, with `ent` bound by a `readBytes`
hypothesis) differs between two memories one `pre` admits, so the record reads
the words back with `wordsAt`.  `pre` and `post` are indexed by the same two
things rather than by a whole `State`, because a caller's environment and
program counter are its own: a record that named them would be false at every
call site.

`Satisfies` below is the relation this record is read at. -/
structure MemContract where
  /-- The fuel the record's completion conjunct is stated at, computed from the
  arguments and the memory. -/
  budget : List Value → Mem → Nat
  /-- What the caller promises about its staging. -/
  pre    : List Value → Mem → Nat → Prop
  /-- What the run must guarantee, at the outcome it produces. -/
  post   : List Value → Mem → Nat → Outcome → Prop

/-- The state a body is run from: its parameters bound to `args`, at its entry
block, with no predecessor.  `initState` is the `mem = []`, `next = 1` case, and
a call selection builds the `mem`, `next` case. -/
def EntryState (f : Function) (args : List Value) (mem : Mem) (next : Nat) : State :=
  { env := (f.params.zip args).map fun (v, a) => (v.1, a)
    mem := mem, next := next, pc := f.entry?.getD "", pre := none }

/-- `initState` is the empty-memory, allocator-base case of `EntryState`, so
every statement at `initState` is the corresponding statement at `EntryState`
with `next = 1`. -/
theorem initState_eq_entryState (f : Function) (args : List Value) :
    initState f args = EntryState f args [] 1 := rfl

/-- `Beh` at an arbitrary state. -/
def BehFromState (calls : Calls) (f : Function) (s : State) : Outcome → Prop :=
  fun o => (∃ n, runFuel calls n f s = some .ub) ∨ (∃ n, runFuel calls n f s = some o)

/-- `Γ` holds of `f`: **the run completes at the record's own budget for those
arguments**, and every behaviour satisfies the post.

The completion conjunct witnesses that the run has at least one behaviour, so a
body that only ever exhausts its fuel satisfies nothing, and it fixes a budget
per argument list and memory at which a call site can run the body.  The post is
forced of the run's own outcome, so a target cannot escape an inside-the-claim
conjunct by naming a different outcome; a post that refuses `.ub` therefore
makes undefined behaviour excluded by theorem, through the completion and
`runFuel_outcome_unique`, rather than by prose. -/
def Satisfies (calls : Calls) (f : Function) (Γ : MemContract) : Prop :=
  ∀ args mem next, Γ.pre args mem next →
    (∃ v m, runFuel calls (Γ.budget args mem) f (EntryState f args mem next) = some (.ret v m)) ∧
    ∀ o, BehFromState calls f (EntryState f args mem next) o → Γ.post args mem next o

/-- A record whose guarantee ignores the returned value.

Needed for a body that returns nothing: `Outcome`'s return carries
`Option Value`, a `CallOutcome`'s carries a `Value`, and `Value` has no void
constructor, so the two can only be related when the guarantee discards the
value. -/
def ValueIrrelevant (Γ : MemContract) : Prop :=
  ∀ args mem next v v' m, Γ.post args mem next (.ret v m) ↔ Γ.post args mem next (.ret v' m)

/-- The record at a **call site**: from a state the record admits, the
selection must resolve — return some `CallOutcome` — and what it returns must be
admitted, with a reservation that does not shrink.

The `∃ r` is not a convenience: without it the relation would be vacuously true
for a selection that answers `none`, which the semantics reads as `ub`, so a
call site whose body exhausted its fuel would satisfy the relation by answering
nothing. -/
def CallSatisfies (calls : Calls) (Γ : MemContract) (sym : String) : Prop :=
  ∀ args mem next, Γ.pre args mem next →
    ∃ r, calls sym args mem next = some r ∧
      Γ.post args mem next (.ret (some r.ret) r.mem) ∧ next ≤ r.next

/-- The placeholder `envForUnit` supplies for a return that carries no value.
`satisfies_calls_void`'s `ValueIrrelevant` hypothesis is what makes it
unobservable, so nothing else may read it. -/
def voidRet : Value := .int 1 0

/-- A selection that runs one unit body from the caller's memory and allocator,
under that unit's own intrinsic environment, at the record's budget for the
arguments and memory it is actually passed.

This generalises `envForBody`/`envForBodySym`, which fix the environment to
`noCalls`, fix the fuel to a constant, and refuse a `void` return.  Because the
run is at `Γ.budget args mem` — the very term `Satisfies` states its completion
at — a call site carries no separate fuel fact. -/
def envForUnit (sym : String) (Γ : MemContract) (calls : Calls) (f : Function) : Calls :=
  fun callee args mem next =>
    if callee = sym then
      match runFuel calls (Γ.budget args mem) f (EntryState f args mem next) with
      | some (.ret (some v) m) => some { ret := v, mem := m, next := next + 0 }
      | some (.ret none m)     => some { ret := voidRet, mem := m, next := next + 0 }
      | _                      => none
    else none

/-- A body whose every `ret` carries a value at a non-void type.  Decidable on
the pinned AST, so it is a `#guard` at each value-returning unit rather than a
proof obligation in prose. -/
def retsValued (f : Function) : Bool :=
  f.blocks.all fun b => match b.term with
    | .ret ty vp => (ty != Ty.void) && vp.isSome
    | _ => true

/-- A stronger record refines into a weaker one: the post may be weakened, the
pre strengthened, and the budget raised pointwise over `(args, mem)`.

The budget cannot be lowered: a lower budget would make the record claim a
completion it does not have, so the completion conjunct cannot be weakened into
"some behaviour exists" and weakening cannot restore a record to a body that
diverges. -/
theorem Satisfies.mono {Γ Γ' : MemContract} {calls : Calls} {f : Function}
    (h : Satisfies calls f Γ)
    (hb : ∀ args mem, Γ.budget args mem ≤ Γ'.budget args mem)
    (hp : ∀ args mem next, Γ'.pre args mem next → Γ.pre args mem next)
    (hw : ∀ args mem next o, Γ.post args mem next o → Γ'.post args mem next o) :
    Satisfies calls f Γ' := by
  intro args mem next hpre
  obtain ⟨hcom, hpost⟩ := h args mem next (hp args mem next hpre)
  refine ⟨?_, ?_⟩
  · obtain ⟨v, m, hrun⟩ := hcom
    exact ⟨v, m, runFuel_mono_le (hb args mem) hrun⟩
  · intro o ho
    exact hw args mem next o (hpost o ho)

/-! ### Completion, and the vacuity of behaviour inclusion alone

`Beh` records the outcomes a run reaches, and a run that never finishes reaches
none.  `Refines` is inclusion of the target's behaviours in the source's, so a
target with no behaviours refines every source — including one that terminates.
The witness below is the smallest instance: a one-block self-loop refines a body
that returns a constant.

The completion conjunct is what excludes it.  `Completes` names `Satisfies`'s
first conjunct on its own, and `RefinesCompleting` is the replacement claim that
adds it to behaviour inclusion.  The budget both read is a step count: the number
of control steps at which the completion argument counts the run down to its
return.  It witnesses finiteness at the declared inputs; it is not a performance
bound, because nothing here measures time or says the run is fast. -/

/-- The first conjunct of `Satisfies`, named: from every state the record admits,
the body reaches a defined return at the record's own budget for those arguments
and that memory.

The budget is a **completion witness**: a step count at which the run is shown to
finish, not a performance bound.  A body that only ever exhausts its fuel has no
such witness, which is exactly the difference `Refines` cannot see. -/
def Completes (calls : Calls) (f : Function) (Γ : MemContract) : Prop :=
  ∀ args mem next, Γ.pre args mem next →
    ∃ v m, runFuel calls (Γ.budget args mem) f (EntryState f args mem next) = some (.ret v m)

/-- `Satisfies` carries completion: its first conjunct is `Completes`. -/
theorem Satisfies.completes {calls : Calls} {f : Function} {Γ : MemContract}
    (h : Satisfies calls f Γ) : Completes calls f Γ :=
  fun args mem next hpre => (h args mem next hpre).1

/-- At the empty-memory, base-one call, completion is completion at `initState`:
`EntryState` builds that state there, so the record's completion witness speaks
about the same run `Refines` compares. -/
theorem Completes.initState {calls : Calls} {f : Function} {Γ : MemContract}
    (h : Completes calls f Γ) {args : List Value} (hp : Γ.pre args [] 1) :
    ∃ v m, runFuel calls (Γ.budget args []) f (initState f args) = some (.ret v m) := by
  simpa [initState_eq_entryState] using h args [] 1 hp

/-- The replacement claim with completion: the target's behaviours are the
source's, and the target finishes at the record's budget wherever the record
admits the call.

`Refines` itself is not this claim.  It is left unchanged because it is used as a
preorder and a function need not terminate — `Refines.refl` would fail if
completion were folded into it.  The completion conjunct is stated here instead,
so a candidate that loops forever is refused while every existing `Refines`
proof keeps its meaning. -/
def RefinesCompleting (calls : Calls) (Γ : MemContract)
    (target source : Function) : Prop :=
  LeanLLVM.Refines calls target source ∧ Completes calls target Γ

theorem RefinesCompleting.refines {calls : Calls} {Γ : MemContract}
    {target source : Function} (h : RefinesCompleting calls Γ target source) :
    LeanLLVM.Refines calls target source :=
  h.1

theorem RefinesCompleting.completes {calls : Calls} {Γ : MemContract}
    {target source : Function} (h : RefinesCompleting calls Γ target source) :
    Completes calls target Γ :=
  h.2

/-- Reflexivity on the completing functions: the completion witness is the
hypothesis, which is the conjunct `Refines` itself cannot supply. -/
theorem RefinesCompleting.refl {calls : Calls} {Γ : MemContract} {f : Function}
    (h : Completes calls f Γ) : RefinesCompleting calls Γ f f :=
  ⟨fun _ _ hb => hb, h⟩

/-- Transitivity: behaviour inclusion composes, and the completion witness is
the composed candidate's own, so the claim remains a preorder on the functions
that complete. -/
theorem RefinesCompleting.trans {calls : Calls} {Γ : MemContract}
    {a b c : Function} (hab : RefinesCompleting calls Γ a b)
    (hbc : RefinesCompleting calls Γ b c) : RefinesCompleting calls Γ a c :=
  ⟨fun args o hb => hbc.1 args o (hab.1 args o hb), hab.2⟩

/-! #### The witness -/

/-- A one-block self-loop: its entry branches to itself and it has no
instructions, so every step is a jump back to the state it left. -/
def spinningFunction : Function :=
  { name := "leanllvm_spin", retTy := .void, params := [],
    blocks := [{ name := "entry", instrs := [], term := .br "entry" }] }

/-- A body that returns the constant `7`. -/
def constantFunction : Function :=
  { name := "leanllvm_constant", retTy := .int 64, params := [],
    blocks := [{ name := "entry", instrs := [],
                 term := .ret (.int 64) (some (.imm (.int 64 7))) }] }

/-- A record that admits every call and guarantees nothing.  The witness needs a
record whose `pre` is inhabited: an unsatisfiable `pre` would make the completion
conjunct hold for free, which is a different defect. -/
def unconstrainedContract : MemContract where
  budget := fun _ _ => 0
  pre := fun _ _ _ => True
  post := fun _ _ _ _ => True

/-- One step of the self-loop is the jump it makes, from any state sitting at
its entry block. -/
theorem spinning_step (calls : Calls) (s : State) (h : s.pc = "entry") :
    step calls spinningFunction s =
      .jump { s with pc := "entry", pre := some s.pc } := by
  cases s with
  | mk env mem next pc pre =>
      simp_all [step, spinningFunction, Function.findBlock, findBlockList,
        denoteCode, denoteRun, State.bindAll, execTerm]

/-- No budget reaches an outcome from the self-loop: each step is a jump back to
the same block, so the fuel is spent without a return or an undefined result. -/
theorem spinning_runFuel_none (calls : Calls) :
    ∀ (n : Nat) (s : State), s.pc = "entry" →
      runFuel calls n spinningFunction s = none
  | 0, _, _ => rfl
  | n + 1, s, h => by
      simp only [runFuel, spinning_step calls s h]
      exact spinning_runFuel_none calls n _ (by simp)

/-- The self-loop has no behaviour at any argument list. -/
theorem spinning_no_beh (calls : Calls) (args : List Value) (o : Outcome) :
    ¬ Beh calls spinningFunction args o := by
  intro h
  have hpc : (initState spinningFunction args).pc = "entry" := rfl
  rw [Beh] at h
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hnone := spinning_runFuel_none calls n _ hpc
    rw [hnone] at hn
    cases hn
  · have hnone := spinning_runFuel_none calls n _ hpc
    rw [hnone] at hn
    cases hn

/-- The terminating body's one behaviour: it returns `7`. -/
theorem constant_beh (calls : Calls) :
    Beh calls constantFunction [] (.ret (some (.int 64 7)) ([] : Mem)) := by
  rw [Beh]
  refine Or.inr ⟨1, ?_⟩
  simp [runFuel, step, constantFunction, Function.findBlock, findBlockList,
    Function.entry?, denoteCode, denoteRun, State.bindAll, execTerm, evalOperand,
    Const.toValue, initState]

/-- A target with no behaviour refines every source: this is the vacuity in
general form. -/
theorem refines_of_no_beh {calls : Calls} {target : Function}
    (h : ∀ args o, ¬ Beh calls target args o) (source : Function) :
    LeanLLVM.Refines calls target source :=
  fun args o hb => absurd hb (h args o)

/-- The acceptance check's candidate: the looping body refines the terminating
body under the current relation, because it has no behaviour to include. -/
theorem spinning_refines_constant (calls : Calls) :
    LeanLLVM.Refines calls spinningFunction constantFunction :=
  refines_of_no_beh (fun args o => spinning_no_beh calls args o) constantFunction

/-- The vacuity is the target's, not the source's: the terminating body does not
refine the looping one, because its return has no source behaviour to match. -/
theorem constant_not_refines_spinning (calls : Calls) :
    ¬ LeanLLVM.Refines calls constantFunction spinningFunction := by
  intro h
  exact spinning_no_beh calls [] _
    (h [] _ (constant_beh calls))

/-- The loop reaches no return at any budget from any state a record admits, so
`Completes` fails wherever the record's `pre` is inhabited. -/
theorem spinning_not_completes (calls : Calls) (Γ : MemContract)
    (hpre : ∃ args mem next, Γ.pre args mem next) :
    ¬ Completes calls spinningFunction Γ := by
  intro h
  obtain ⟨args, mem, next, hp⟩ := hpre
  obtain ⟨v, m, hrun⟩ := h args mem next hp
  have hpc : (EntryState spinningFunction args mem next).pc = "entry" := rfl
  have hnone := spinning_runFuel_none calls (Γ.budget args mem) _ hpc
  rw [hnone] at hrun
  cases hrun

/-- The completion-added claim rejects the looping candidate that `Refines`
accepts. -/
theorem spinning_not_refinesCompleting (calls : Calls) :
    ¬ RefinesCompleting calls unconstrainedContract spinningFunction constantFunction :=
  fun h => spinning_not_completes calls unconstrainedContract ⟨[], [], 1, trivial⟩ h.2

/-- A block whose terminator satisfies `retsValued`'s guard. -/
theorem retsValued_block {f : Function} (h : retsValued f = true) {b : Block}
    (hb : b ∈ f.blocks) :
    (match b.term with | .ret ty vp => (ty != Ty.void) && vp.isSome | _ => true) = true := by
  simp only [retsValued] at h
  exact (List.all_eq_true.mp h) b hb

/-- A `ret` at a non-void type with a value operand returns a value: `execTerm`
decides the return's shape from the terminator's own `ty`, never from the
header. -/
theorem execTerm_ret_isSome {s : State} {ty : Ty} {vp : Option Operand}
    (hok : (ty != Ty.void) && vp.isSome = true)
    {v : Option Value} {s' : State}
    (h : execTerm s (.ret ty vp) = .ret v s') : v.isSome := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hne, hsome⟩ := hok
  cases ty with
  | void => simp at hne
  | int w =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl
  | ptr =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl
  | vec n elem =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl
  | array n elem =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl
  | struct name bytes =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl
  | double =>
      cases vp with
      | none => simp at hsome
      | some o =>
          cases hv : evalOperand s o with
          | none => simp [execTerm, hv] at h
          | some x =>
              simp only [execTerm, hv] at h
              cases h
              rfl

/-- A step that returns carries a value when every terminator's `ret` does. -/
theorem step_ret_isSome {calls : Calls} {f : Function} (hf : retsValued f = true)
    {s : State} {v : Option Value} {s' : State} (h : step calls f s = .ret v s') :
    v.isSome := by
  unfold step at h
  cases hfind : f.findBlock s.pc with
  | none => simp only [hfind] at h; cases h
  | some b =>
      simp only [hfind] at h
      cases hcode : denoteCode calls b.instrs s with
      | none => simp only [hcode] at h; cases h
      | some s'' =>
          simp only [hcode] at h
          have hb : b ∈ f.blocks := findBlockList_mem hfind
          have hterm := retsValued_block hf hb
          cases ht : b.term with
          | ret ty vp =>
              simp only [ht] at hterm
              rw [ht] at h
              exact execTerm_ret_isSome hterm h
          | br d => rw [ht] at h; simp [execTerm] at h
          | condbr c t e =>
              rw [ht] at h
              simp only [execTerm] at h
              cases hc : evalOperand s'' c with
              | none => simp [hc] at h
              | some x =>
                  cases x with
                  | float b => simp [hc] at h
                  | int w bit =>
                      cases w with
                      | zero => simp only [hc] at h; simp at h
                      | succ w =>
                          cases w with
                          | zero =>
                              simp only [hc] at h
                              split at h
                              · cases h
                              · split at h <;> cases h
                          | succ w => simp only [hc] at h; simp at h
                  | ptr a => rw [hc] at h; simp at h
                  | vec n w l => rw [hc] at h; simp at h
          | unreachable => rw [ht] at h; simp [execTerm] at h

/-- A completed run of a `retsValued` body carries a value.  `execTerm` decides
the return's shape from the terminator's own `ty`, not from the function header,
so a header `retTy ≠ .void` would not exclude `.ret .void none`; this guard on
the terminators does. -/
theorem ret_some_of_retsValued {calls : Calls} {f : Function} (h : retsValued f = true)
    {s : State} {n : Nat} {v : Option Value} {m : Mem}
    (hrun : runFuel calls n f s = some (.ret v m)) : v.isSome := by
  induction n generalizing s v m with
  | zero => cases hrun
  | succ n ih =>
      simp only [runFuel] at hrun
      split at hrun
      · cases hrun
      · rename_i v' s' _
        cases hrun
        exact step_ret_isSome h (by assumption)
      · rename_i s' _
        exact ih hrun

/-- The bridge for a body that returns a value: a `Satisfies` record becomes a
`CallSatisfies` one at the symbol `envForUnit` resolves.

`hv` is the completion's shape, not the header's, because the parser accepts a
terminator whose `ty` disagrees with the header.  There is no fuel hypothesis:
the selection runs at the very budget the record states its completion at, so
the lift is `Nat.le_refl`. -/
theorem satisfies_calls {calls : Calls} {body : Function} {Γ : MemContract}
    {sym : String} (h : Satisfies calls body Γ) (hv : retsValued body = true) :
    CallSatisfies (envForUnit sym Γ calls body) Γ sym := by
  intro args mem next hpre
  obtain ⟨hcom, hpost⟩ := h args mem next hpre
  obtain ⟨v, m, hrun⟩ := hcom
  have hsome : v.isSome := ret_some_of_retsValued hv hrun
  cases v with
  | none => simp at hsome
  | some v' =>
      refine ⟨{ ret := v', mem := m, next := next + 0 }, ?_, ?_, ?_⟩
      · simp only [envForUnit, hrun, ↓reduceIte]
      · exact hpost (.ret (some v') m) (Or.inr ⟨_, hrun⟩)
      · show next ≤ next + 0
        omega

/-- The bridge for a body that returns nothing.  `ValueIrrelevant` is what makes
`voidRet` unobservable, and it is required because `Outcome`'s return carries
`Option Value` while `CallOutcome.ret` carries a `Value`; a record that read the
value is refused rather than guessed at. -/
theorem satisfies_calls_void {calls : Calls} {body : Function} {Γ : MemContract}
    {sym : String} (h : Satisfies calls body Γ) (hirr : ValueIrrelevant Γ) :
    CallSatisfies (envForUnit sym Γ calls body) Γ sym := by
  intro args mem next hpre
  obtain ⟨hcom, hpost⟩ := h args mem next hpre
  obtain ⟨v, m, hrun⟩ := hcom
  cases v with
  | some v' =>
      refine ⟨{ ret := v', mem := m, next := next + 0 }, ?_, ?_, ?_⟩
      · simp only [envForUnit, hrun, ↓reduceIte]
      · exact hpost (.ret (some v') m) (Or.inr ⟨_, hrun⟩)
      · show next ≤ next + 0
        omega
  | none =>
      refine ⟨{ ret := voidRet, mem := m, next := next + 0 }, ?_, ?_, ?_⟩
      · simp only [envForUnit, hrun, ↓reduceIte]
      · have hpost' := hpost (.ret none m) (Or.inr ⟨_, hrun⟩)
        exact (hirr args mem next none (some voidRet) m).mp hpost'
      · show next ≤ next + 0
        omega


end LeanLLVM.Refinement
