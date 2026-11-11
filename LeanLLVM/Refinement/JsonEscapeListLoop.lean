/-
The lanes loop of the escape list body, closed on `LoopFuel`'s induction.

`escapeListFunction`'s `xl_lanes` closure is the shape `LoopFuel.CarriedLoop`
exists for: `do.body.i` carries one word in `%e.1.i`, computes the doubling map's
next iterate from it, and leaves the loop exactly when the iterate equals the
word it started from —

    %e.1.i  = phi [("do.body.i", %or23.i), ("if.end.i", %or13.i)]
    %shl21.i = shl %e.1.i, 2
    %and22.i = and %shl21.i, %and7.i
    %or23.i  = or  %and22.i, %e.1.i
    %cmp24.not.i = icmp eq %or23.i, %e.1.i
    condbr %cmp24.not.i, "xl_lanes.exit", "do.body.i"

with `%and7.i` the `(bs <<< 1) &&& bs` mask `if.end.i` formed and `stepWord bs` the
map `JsonEscapeListFixpoint` reasons about.

**The exit word is not identified in the step.**  The invariant says the word is
`stepN bs i (escapeSeed bs prevb prevs)`; the successor's word is `stepWord bs` of
it, which is `stepN`'s defining equation and nothing else.  The identification
with `specRunStarts` is `stepN_fixed_eq_specRunStarts`, a statement about the map,
and it is applied **once** at the end of `lanes_run` to the fixed iterate the
induction hands back — never to learn what the next iterate is.  A step that
needed that would be citing the loop's own conclusion.

**The bound is a term of the arguments.**  `N = 32` is the lane width's bound on
the map's closure (`stepN_32_is_fixed`), so the loop's whole cost whatever the data
does is `N + 1` control steps from its entry iteration — thirty-three from
iteration zero, thirty-one from `do.body.i`, because `if.end.i` performs the first
two doublings itself.  The record's budget is therefore `f(args, mem)`, not a trip
count; `lanes_run_at` states the run completed at exactly that fuel.

**The exit is a jump, not a `ret`.**  `xl_lanes.exit` continues into the store and
the batch loop, so the lemma concludes a prefix of the run, and it hands the exit
state its word *and* the cells the rest of the body reads — the loop's frame,
which `do.body.i` does not write.

The module is stated over the pinned AST and the map.  What the head block's
`denoteCode` needs is here; the seed blocks' trace and the exit block's trace are
stated in the modules that own those blocks, and both are composable with this one
through `step` and `runFuel` alone.
-/
import LeanLLVM.Refinement.LoopFuel
import LeanLLVM.Refinement.JsonEscapeListFixpoint
import LeanLLVM.Refinement.JsonEscapeListBody

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics

/-! ### The head block, from the pinned AST

The block is written out once, so the step below names the instructions it runs;
`lanes_findBlock_body` decides that it is the fixture's `do.body.i`, so a fixture
whose instruction moved would fail the equality rather than the proof. -/

/-- The `do.body.i` `phi`'s incoming list. -/
def lstDoBodyIncoming : List (String × Operand) :=
  [("do.body.i", .reg "%or23.i"), ("if.end.i", .reg "%or13.i")]

/-- The pinned `do.body.i` block. -/
def lanesBodyBlock : Block where
  name := "do.body.i"
  instrs :=
    [ .phi "%e.1.i" (.int 64) lstDoBodyIncoming,
      .binop "%shl21.i" .shl 64 (.reg "%e.1.i") (.imm (.int 64 (BitVec.ofInt 64 2))),
      .binop "%and22.i" .and 64 (.reg "%shl21.i") (.reg "%and7.i"),
      .binop "%or23.i" .or 64 (.reg "%and22.i") (.reg "%e.1.i"),
      .icmp "%cmp24.not.i" .eq 64 (.reg "%or23.i") (.reg "%e.1.i") ]
  term := .condbr (.reg "%cmp24.not.i") "xl_lanes.exit" "do.body.i"

theorem lanes_findBlock_body :
    escapeListFunction.findBlock "do.body.i" = some lanesBodyBlock := by
  decide

/-! ### The loop's frame

The cells `do.body.i` does not write and everything after it reads: the body's
arguments, `if.end.i`'s mask word, the block base, the output stream and count,
and both carry words.  Stated as "unchanged from the entry environment", because
that is the fact the exit block's trace needs and the fact the loop's step
preserves. -/

/-- The environment agrees with the loop's entry environment on every cell the
rest of the body reads. -/
structure lstLanesKeeps (env0 env : Env) : Prop where
  bsReg : lookupName env "%bs" = lookupName env0 "%bs"
  ctlReg : lookupName env "%ctl" = lookupName env0 "%ctl"
  imReg : lookupName env "%im" = lookupName env0 "%im"
  blk0Reg : lookupName env "%blk0" = lookupName env0 "%blk0"
  xpReg : lookupName env "%xp" = lookupName env0 "%xp"
  xnReg : lookupName env "%xn" = lookupName env0 "%xn"
  carryReg : lookupName env "%carry" = lookupName env0 "%carry"

/-! ### The head block's environment

One alias per instruction, so the `denoteCode` chain's intermediate states are
named rather than written out.  `%or23.i` is `stepWord bs w` — the map applied to
the carried word — by `or_comm`, and `%and7.i` is `stepMask bs`. -/

def ld1 (env : Env) (w : BitVec 64) : Env :=
  (["%e.1.i"] : List String).zip ([.int 64 w] : List Value) ++ env

def ld2 (env : Env) (w : BitVec 64) : Env :=
  (["%shl21.i"] : List String).zip ([.int 64 (w <<< 2)] : List Value) ++ ld1 env w

def ld3 (env : Env) (bs w : BitVec 64) : Env :=
  (["%and22.i"] : List String).zip ([.int 64 ((w <<< 2) &&& stepMask bs)] : List Value) ++
    ld2 env w

def ld4 (env : Env) (bs w : BitVec 64) : Env :=
  (["%or23.i"] : List String).zip ([.int 64 (stepWord bs w)] : List Value) ++ ld3 env bs w

def ld5 (env : Env) (bs w : BitVec 64) : Env :=
  (["%cmp24.not.i"] : List String).zip
      ([.int 1 (evalICmp .eq (stepWord bs w) w)] : List Value) ++ ld4 env bs w

/-- Unfolding every alias, so a lookup is again a walk over a cons chain. -/
macro "ld_simp" : tactic => `(tactic|
  (simp only [ld5, ld4, ld3, ld2, ld1, List.zip_cons_cons, List.zip_nil_right,
    List.cons_append, List.nil_append]))

/-- Reading a cell out of a binding prefix: the prefix is the block's bindings
zipped with their values, so walking past them reaches the incoming environment's
binding, which the hypothesis supplies. -/
macro "ld_lk" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
   | rw [lookupName_cons_self]
   | assumption))

/-- The same walk, closed by a named hypothesis rather than by `assumption`: a
frame field is a projection, which `assumption` does not see. -/
macro "ld_exact " h:term : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
   | rw [lookupName_cons_self]
   | exact $h))

/-- The block's `or` writes the map's value: the instruction's operands are in the
opposite order to `stepWord`'s. -/
theorem and_or_stepWord (bs w : BitVec 64) :
    ((w <<< 2) &&& stepMask bs) ||| w = stepWord bs w := by
  rw [stepWord, BitVec.or_comm]

/-- A state is its environment at its own block and predecessor: the block lemmas
are stated at a state and then `withEnv`'d, and the induction's states are
arbitrary, so this is the one conversion between the two. -/
theorem withEnv_self (s : State) : withEnv s.env s = s := by
  cases s
  rfl

/-! ### The equality test's two arms, at a one-bit value

`JsonEscapeListBody` carries the instruction shapes the block runs (its `b_shl64_two`,
`b_and64`, `b_or64`, `b_icmp_eq64`), the block's control step (`step_of`) and the two
`condbr` arms (`execTerm_condbr_one`/`_zero`); this module consumes them.  What is
left is the equality test's *clear* arm at a one-bit value, proved from the width so
it costs no carrier: `decide`'s false case is the step that reaches for
`Classical`, and a loop step that carried it would put `Classical.choice` into every
record built on the loop. -/

/-- A one-bit value is zero or one. -/
theorem bitVec_one_eq_zero_or_one (b : BitVec 1) : b = 0 ∨ b = 1 := by
  have h : b.toNat = 0 ∨ b.toNat = 1 := by have := b.isLt; omega
  rcases h with h | h
  · left; exact BitVec.toNat_inj.mp (by simpa using h)
  · right; exact BitVec.toNat_inj.mp (by simpa using h)

/-! ### The block's one control step -/

/-- The head block's `denoteCode`, as the binding prefix `ld5` it leaves: `%e.1.i`
the carried word, `%or23.i` its image under the map, and `%cmp24.not.i` the exit
test. -/
theorem lstDoBody_denote (env : Env) (s : State) (bs w : BitVec 64) (p : String) (op : Operand)
    (hpre : (withEnv env s).pre = some p)
    (hinc : phiIncoming p lstDoBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hmask : lookupName env "%and7.i" = some (.int 64 (stepMask bs))) :
    denoteCode escapeCalls lanesBodyBlock.instrs (withEnv env s) =
      some (withEnv (ld5 env bs w) s) := by
  rw [show lanesBodyBlock.instrs =
      [ .phi "%e.1.i" (.int 64) lstDoBodyIncoming,
        .binop "%shl21.i" .shl 64 (.reg "%e.1.i") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .binop "%and22.i" .and 64 (.reg "%shl21.i") (.reg "%and7.i"),
        .binop "%or23.i" .or 64 (.reg "%and22.i") (.reg "%e.1.i"),
        .icmp "%cmp24.not.i" .eq 64 (.reg "%or23.i") (.reg "%e.1.i") ] from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi hpre hinc hop)]
  rw [show (withEnv env s).bind "%e.1.i" (.int 64 w) = withEnv (ld1 env w) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_shl64_two _ s "%shl21.i" "%e.1.i" w (by ld_simp; ld_lk))]
  rw [show withEnv (("%shl21.i", .int 64 (w <<< 2)) :: ld1 env w) s =
    withEnv (ld2 env w) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and22.i" "%shl21.i" "%and7.i"
    (w <<< 2) (stepMask bs) (by ld_simp; ld_lk) (by ld_simp; ld_lk))]
  rw [show withEnv (("%and22.i", .int 64 ((w <<< 2) &&& stepMask bs)) :: ld2 env w) s =
    withEnv (ld3 env bs w) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or23.i" "%and22.i" "%e.1.i"
    ((w <<< 2) &&& stepMask bs) w (by ld_simp; ld_lk) (by ld_simp; ld_lk))]
  rw [show withEnv (("%or23.i", .int 64 (((w <<< 2) &&& stepMask bs) ||| w)) :: ld3 env bs w) s =
    withEnv (ld4 env bs w) s from by rw [and_or_stepWord]; rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64 _ s "%cmp24.not.i" "%or23.i" "%e.1.i"
    (stepWord bs w) w (by ld_simp; ld_lk) (by ld_simp; ld_lk))]
  rw [show withEnv (("%cmp24.not.i", .int 1 (evalICmp .eq (stepWord bs w) w)) :: ld4 env bs w) s =
    withEnv (ld5 env bs w) s from rfl]
  simp only [denoteCode]

/-- **`do.body.i`'s one control step.**  From the head with the carried word `w` in
the `phi`'s selected operand, the block computes `stepWord bs w` and jumps to
`xl_lanes.exit` exactly when that is `w`, otherwise back to itself.

The conclusion carries the frame the rest of the body reads, and the three cells
the next iteration and the exit block read.  Nothing here mentions `specRunStarts`:
the successor's word is `stepWord bs w`, which is `stepN`'s defining equation at
the next index. -/
theorem lstDoBody_step (env : Env) (s : State) (bs w : BitVec 64) (p : String) (op : Operand)
    (env0 : Env)
    (hpc : (withEnv env s).pc = "do.body.i")
    (hpre : (withEnv env s).pre = some p)
    (hinc : phiIncoming p lstDoBodyIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hmask : lookupName env "%and7.i" = some (.int 64 (stepMask bs)))
    (hkeeps : lstLanesKeeps env0 env) :
    step escapeCalls escapeListFunction (withEnv env s) =
      .jump (withEnv (ld5 env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) ∧
    lstLanesKeeps env0 (ld5 env bs w) ∧
    lookupName (ld5 env bs w) "%and7.i" = some (.int 64 (stepMask bs)) ∧
    lookupName (ld5 env bs w) "%e.1.i" = some (.int 64 w) ∧
    lookupName (ld5 env bs w) "%or23.i" = some (.int 64 (stepWord bs w)) := by
  have hbody : denoteCode escapeCalls lanesBodyBlock.instrs (withEnv env s) =
      some (withEnv (ld5 env bs w) s) :=
    lstDoBody_denote env s bs w p op hpre hinc hop hmask
  have hstep : step escapeCalls escapeListFunction (withEnv env s) =
      execTerm (withEnv (ld5 env bs w) s) lanesBodyBlock.term :=
    step_of (withEnv env s) "do.body.i" lanesBodyBlock (withEnv (ld5 env bs w) s)
      hpc lanes_findBlock_body hbody
  have hcells :
      lstLanesKeeps env0 (ld5 env bs w) ∧
      lookupName (ld5 env bs w) "%and7.i" = some (.int 64 (stepMask bs)) ∧
      lookupName (ld5 env bs w) "%e.1.i" = some (.int 64 w) ∧
      lookupName (ld5 env bs w) "%or23.i" = some (.int 64 (stepWord bs w)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨by ld_simp; ld_exact hkeeps.bsReg, by ld_simp; ld_exact hkeeps.ctlReg,
        by ld_simp; ld_exact hkeeps.imReg, by ld_simp; ld_exact hkeeps.blk0Reg,
        by ld_simp; ld_exact hkeeps.xpReg, by ld_simp; ld_exact hkeeps.xnReg,
        by ld_simp; ld_exact hkeeps.carryReg⟩
    · ld_simp; ld_lk
    · ld_simp; ld_lk
    · ld_simp; ld_lk
  refine ⟨?_, hcells⟩
  rw [hstep, show lanesBodyBlock.term =
    .condbr (.reg "%cmp24.not.i") "xl_lanes.exit" "do.body.i" from rfl]
  have hval : evalOperand (withEnv (ld5 env bs w) s) (.reg "%cmp24.not.i") =
      some (.int 1 (evalICmp .eq (stepWord bs w) w)) := by
    show lookupName (ld5 env bs w) "%cmp24.not.i" = _
    ld_simp
    rw [lookupName_cons_self]
  have hpcw : (withEnv (ld5 env bs w) s).pc = "do.body.i" := hpc
  by_cases hfix : stepWord bs w = w
  · rw [execTerm_condbr_one _ _ _ _ _ hval ((evalICmp_eq_one_iff _ _).mpr hfix), hpcw]
    simp only [hfix]
    rfl
  · have hz : evalICmp .eq (stepWord bs w) w = (0 : BitVec 1) := by
      rcases bitVec_one_eq_zero_or_one (evalICmp .eq (stepWord bs w) w) with h0 | h1
      · exact h0
      · exact absurd ((evalICmp_eq_one_iff _ _).mp h1) hfix
    rw [execTerm_condbr_zero _ _ _ _ _ hval hz, hpcw]
    simp only [hfix]
    rfl

/-- `stepN` is `LoopFuel.iter` at the map. -/
theorem stepN_eq_iter (bs : BitVec 64) (n : Nat) (x : BitVec 64) :
    stepN bs n x = iter (stepWord bs) n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, ih]; rfl

/-! ### The loop's invariant and exit state -/

/-- The invariant at the loop head: after `i` iterations the state is at
`do.body.i`, its `phi` selects the iterate, the mask is `stepMask bs`, and the
frame still agrees with the entry environment. -/
def lstLanesInv (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (i : Nat)
    (s : State) (w : BitVec 64) : Prop :=
  s.pc = "do.body.i" ∧
  lookupName s.env "%and7.i" = some (.int 64 (stepMask bs)) ∧
  (∃ (p : String) (op : Operand), s.pre = some p ∧
    phiIncoming p lstDoBodyIncoming = some op ∧
    evalOperand s op = some (.int 64 w)) ∧
  w = stepN bs i (escapeSeed bs prevb prevs) ∧
  i ≤ 32 ∧
  lstLanesKeeps env0 s.env

/-- What the loop leaves: the word the exit block's `phi` will read, and the frame
it reads with it. -/
def lstLanesExitWord (env0 : Env) (s : State) (w : BitVec 64) : Prop :=
  lookupName s.env "%e.1.i" = some (.int 64 w) ∧ lstLanesKeeps env0 s.env

/-- The lanes loop as a `CarriedLoop`: the map is `stepWord bs`, the seed the entry
blocks' `escapeSeed`, and the bound the lane width's thirty-two. -/
def lstLanesLoop (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) :
    CarriedLoop escapeCalls escapeListFunction where
  head := "do.body.i"
  exitBlock := "xl_lanes.exit"
  map := stepWord bs
  seed := escapeSeed bs prevb prevs
  N := 32
  Inv := lstLanesInv bs prevb prevs env0
  ExitWord := lstLanesExitWord env0
  step_exit := by
    intro i s w h hfix
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, _hiter, _hbound, hkeeps⟩ := h
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre hop ⊢
    obtain ⟨hstep, hkeeps', _hmask', he, _hor⟩ :=
      lstDoBody_step s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    exact ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, he, hkeeps'⟩
  step_loop := by
    intro i s w h hfix
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, hiter, hbound, hkeeps⟩ := h
    have hσ : s = withEnv s.env s := (withEnv_self s).symm
    rw [hσ] at hpc hpre hop ⊢
    obtain ⟨hstep, hkeeps', hmask', he, hor⟩ :=
      lstDoBody_step s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    refine ⟨withEnv (ld5 s.env bs w)
      { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
               pre := some "do.body.i" }, hstep, by simp only [hfix]; rfl, ?_⟩
    have hi32 : i ≠ 32 := by
      intro h32
      refine hfix ?_
      rw [hiter, h32]
      exact stepN_32_is_fixed bs prevb prevs
    refine ⟨by simp only [hfix]; rfl, hmask', ⟨"do.body.i", .reg "%or23.i", rfl, ?_, ?_⟩,
      ?_, by omega, hkeeps'⟩
    · decide
    · show evalOperand (withEnv (ld5 s.env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) (.reg "%or23.i") = some (.int 64 (stepWord bs w))
      simpa only [withEnv, evalOperand] using hor
    · rw [hiter, stepN_succ]
  word_iterate := by
    intro i s w h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := h
    rw [hiter, stepN_eq_iter]
  bound := by
    intro i s w h
    exact h.2.2.2.2.1
  fixed := by
    intro s w h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := h
    rw [hiter]
    exact stepN_32_is_fixed bs prevb prevs

/-! ### The loop's run, and the exit word

`CarriedLoop.run_from` does the induction; what is left is the one application of
`stepN_fixed_eq_specRunStarts` to the fixed iterate it hands back. -/

/-- The invariant at the head, entered from `if.end.i` with the seed word: the
three facts `if.end.i`'s step leaves, and the reflexive frame. -/
theorem lstLanesInv_entry (bs : BitVec 64) (prevb prevs : Bool) (σ : State)
    (hpc : σ.pc = "do.body.i")
    (hpre : σ.pre = some "if.end.i")
    (hseed : lookupName σ.env "%or13.i" =
      some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs))))
    (hmask : lookupName σ.env "%and7.i" = some (.int 64 (stepMask bs))) :
    lstLanesInv bs prevb prevs σ.env 2 σ (stepN bs 2 (escapeSeed bs prevb prevs)) := by
  refine ⟨hpc, hmask, ⟨"if.end.i", .reg "%or13.i", hpre, by decide, ?_⟩, rfl, by omega, ?_⟩
  · show evalOperand σ (.reg "%or13.i") =
      some (.int 64 (stepN bs 2 (escapeSeed bs prevb prevs)))
    simpa only [evalOperand] using hseed
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The lanes loop closes on the fuel induction.**  From the head at iteration
`i`, the run reaches `xl_lanes.exit` within `32 - i + 1` control steps, carrying
`specRunStarts bs (prevb && prevs)` in the word the exit block's `phi` reads and
the frame the rest of the body reads.

The identification with the rule's word happens here, once, on the fixed iterate
the induction returns; the induction itself never consumed it. -/
theorem lanes_run (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (i : Nat)
    (σ : State) (w : BitVec 64) (hinv : lstLanesInv bs prevb prevs env0 i σ w) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 32 - i + 1 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitWord env0 e (specRunStarts bs (prevb && prevs)) ∧
      runFuel escapeCalls (j + k) escapeListFunction σ =
        runFuel escapeCalls k escapeListFunction e := by
  obtain ⟨e, j, d, hj, hd, hpc, hexit, hfix, hrun⟩ :=
    (lstLanesLoop bs prevb prevs env0).run_from (32 - i) i σ w hinv rfl
  obtain hrun := hrun k
  refine ⟨e, j, hj, hpc, ?_, hrun⟩
  have hword : iter (stepWord bs) d (escapeSeed bs prevb prevs) =
      specRunStarts bs (prevb && prevs) := by
    rw [← stepN_eq_iter]
    exact stepN_fixed_eq_specRunStarts bs prevb prevs d (by rwa [stepN_eq_iter])
  have hexit' : lstLanesExitWord env0 e
      (iter (stepWord bs) d (escapeSeed bs prevb prevs)) := hexit
  rw [hword] at hexit'
  exact hexit'

/-- **The lanes loop from its head**: entered at iteration two, the run reaches the
exit within thirty-one control steps, carrying the rule's word.

Thirty-one is the loop's whole cost from `do.body.i` — `32 - 2 + 1` — and it is a
term of the arguments: the lane width's bound, not the trip count.  The loop's
contribution to a record's budget is therefore the constant it read here plus the
entry blocks' and the exit block's own, so the record's budget is `f(args, mem)`. -/
theorem lanes_run_from_head (bs : BitVec 64) (prevb prevs : Bool) (σ : State)
    (hinv : lstLanesInv bs prevb prevs σ.env 2 σ (stepN bs 2 (escapeSeed bs prevb prevs)))
    (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 31 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitWord σ.env e (specRunStarts bs (prevb && prevs)) ∧
      runFuel escapeCalls (j + k) escapeListFunction σ =
        runFuel escapeCalls k escapeListFunction e :=
  lanes_run bs prevb prevs σ.env 2 σ _ hinv k

/-- **The lanes loop at its bound.**  From the head, the run completes at
thirty-one control steps plus the exit continuation's own fuel.  Thirty-one is the
loop's whole cost from `do.body.i` — the lane width's thirty-two minus the two
doublings `if.end.i` performs, plus the exit test's own step — so it is a term of
the arguments and the record's budget over this loop is `31 + (the exit block's
own)`, never a number the run knows.

`hcont` is the exit block's trace; `lstLanesExitWord` is what it may assume, and it
carries the loop's frame for exactly that reason. -/
theorem lanes_run_at (bs : BitVec 64) (prevb prevs : Bool) (σ : State) (k : Nat)
    (hinv : lstLanesInv bs prevb prevs σ.env 2 σ (stepN bs 2 (escapeSeed bs prevb prevs)))
    {o : Outcome}
    (hcont : ∀ (e : State) (_j : Nat), e.pc = "xl_lanes.exit" →
      lstLanesExitWord σ.env e (specRunStarts bs (prevb && prevs)) →
      runFuel escapeCalls k escapeListFunction e = some o) :
    runFuel escapeCalls (31 + k) escapeListFunction σ = some o := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := lanes_run_from_head bs prevb prevs σ hinv k
  have hone : runFuel escapeCalls (j + k) escapeListFunction σ = some o := by
    rw [hrun]
    exact hcont e j hpc hexit
  exact runFuel_mono_le (by omega) hone

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.lstDoBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstDoBody_denote

/-- info: 'LeanLLVM.Refinement.lstDoBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstDoBody_step

/-- info: 'LeanLLVM.Refinement.bitVec_one_eq_zero_or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bitVec_one_eq_zero_or_one

/-- info: 'LeanLLVM.Refinement.lstLanesInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesInv_entry

/-- info: 'LeanLLVM.Refinement.lstLanesLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesLoop

/-- info: 'LeanLLVM.Refinement.lanes_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_run

/-- info: 'LeanLLVM.Refinement.lanes_run_from_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_run_from_head

/-- info: 'LeanLLVM.Refinement.lanes_run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_run_at

end LeanLLVM.Refinement
