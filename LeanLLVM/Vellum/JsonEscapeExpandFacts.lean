/-
The expander's four runs, composed from the trace's block steps.

`JsonEscapeExpandRun` states the expander's claim with `ExpandFacts` as its
hypothesis; this module starts discharging that bundle from the record's `pre`,
and it states the staged invariant the iteration and refusal arms need.

**Why the arms need more than `LatchInv`.**  `DecodeLatch`
(`JsonEscapeDecodeRun.lean`) binds the state's `%p`, `%xp`, `%tab`, `%pos0` and
`%n` to existentials and pins only `%dst` and `%nxp.toNat = nps`.  A state can
therefore satisfy `LatchInv` while `%xp` points at memory that holds no position
stream, and the first block after the latch — `while.body6`, whose `%arrayidx7`
load reads four bytes at `%xp + 4 * c` — then cannot be evaluated at all.  The
staging the iteration consumes is already stated, and already consumed by the two
copy-loop instances and the seed: `DecodeStaging`, `StagedDecodeInv` and
`StagedLatchInv` in `JsonEscapeCopyLoops.lean`.  `AssemblyLatchInv` is that
invariant plus the pinning of the five existentials, which is what makes every
block between the latch and the next latch a statement about the caller's own
body, position stream and table.  A cell holds one value, so the pinnings are not
a second claim beside `DecodeLatch`'s: they force the existentials equal, and
`assemblyLatchInv_paddr_eq` states that consequence rather than leaving it to be
rediscovered.

**What is proved here.**  The empty-list entry run: when the caller's cursor is
already at the list's end, `entry` and `while.end` reach `while.end35` in two
control steps and leave the exit word `DecodeEntryExit` names, with the goal the
walk's own seed produces.  It is the second arm of `ExpandSeed`, closed from the
trace's two steps and the caller's cursor read, and it needs no iteration at all.
-/
import LeanLLVM.Vellum.JsonEscapeExpandRun
import LeanLLVM.Vellum.JsonEscapeCompose

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The staged invariant the arms consume

`StagedLatchInv` carries the latch, the staging the copies read, and the `%add`
cell; the five pinnings below are the register cells the staging and the record's
`pre` are about.  They are stated as equalities of the cells, which is the same
fact as pinning `DecodeLatch`'s existentials: a cell holds one value, so a second
equality for the same name forces the two values equal, and
`assemblyLatchInv_paddr_eq` states that consequence rather than leaving it to be
rediscovered. -/
def AssemblyLatchInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (r c : Nat) (s : State) : Prop :=
  StagedLatchInv body st dst nps goal xp pos0 n ps r c s ∧
  lookupName s.env "%p" = some (.ptr b) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%tab" = some (.ptr tab) ∧
  lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n))

/-- The staged latch under the pinnings. -/
theorem assemblyLatchInv_staged {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    StagedLatchInv body st dst nps goal xp pos0 n ps r c s := h.1

/-- The latch's own invariant, which is what `decodeLatchTwoExit` consumes. -/
theorem assemblyLatchInv_latch {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    LatchInv body st dst nps goal r s c :=
  stagedLatchInv_latch h.1

/-- The caller's staging, on its own. -/
theorem assemblyLatchInv_staging {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    ∃ addv : BitVec 64,
      DecodeStaging s.mem nps xp pos0 n ps addv ∧
      lookupName s.env "%add" = some (.int 64 addv) :=
  stagedLatchInv_staging h.1

/-- The latch's budget pair. -/
theorem assemblyLatchInv_budget {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    c ≤ nps ∧ nps ≤ c + r :=
  stagedLatchInv_budget h.1

/-- The five parameter cells. -/
theorem assemblyLatchInv_params {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    lookupName s.env "%p" = some (.ptr b) ∧
      lookupName s.env "%xp" = some (.ptr xp) ∧
      lookupName s.env "%tab" = some (.ptr tab) ∧
      lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The pinning is a pinning of `DecodeLatch`'s existential, not a second claim
about the same cell: the two values are equal. -/
theorem assemblyLatchInv_paddr_eq {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s)
    {paddr : Nat} (hp : lookupName s.env "%p" = some (.ptr paddr)) : paddr = b := by
  have hb : lookupName s.env "%p" = some (.ptr b) := h.2.1
  rw [hp] at hb
  exact Value.ptr.inj (Option.some.inj hb)

/-! ### The position list's length is at most the body's -/

/-- `escAt` is a filter of the body's index range, so it is no longer than the
body. -/
theorem escAt_length_le (bs : List UInt8) (st : ClassState) (i : Nat) :
    (escAt bs st i).length ≤ bs.length := by
  unfold escAt
  simpa using List.length_filter_le
    (fun k => decide (i ≤ k) && laneAt bs st k) (List.range bs.length)

/-! ### The entry state's cells

`EntryState` binds the function's parameters to the arguments, in order.  The
four cells the entry run reads are the cursor, the body's window and the list's
length; each is a projection of the caller's argument list. -/
/-- The entry state's environment: the function's parameters bound to the
caller's arguments, in order. -/
theorem entryState_env {args : List Value} {mem : Mem} {next : Nat}
    {b n dst err xp xj nps pos0 tab : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err,
      .ptr xp, .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
      .ptr tab]) :
    (EntryState usDecFunction args mem next).env =
      [("%p", .ptr b), ("%n", .int 64 (BitVec.ofNat 64 n)), ("%dst", .ptr dst),
       ("%err", .ptr err), ("%xp", .ptr xp), ("%xj", .ptr xj),
       ("%nxp", .int 64 (BitVec.ofNat 64 nps)),
       ("%pos0", .int 64 (BitVec.ofNat 64 pos0)), ("%tab", .ptr tab)] := by
  subst hargs
  rfl

/-- The entry state's pc, predecessor and memory, and the three cells the entry
run reads.  `%0` is not among them: the `entry` block's first load binds it. -/
theorem entryState_cells {args : List Value} {mem : Mem} {next : Nat}
    {b n dst err xp xj nps pos0 tab : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err,
      .ptr xp, .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
      .ptr tab]) :
    (EntryState usDecFunction args mem next).pc = "entry" ∧
      (EntryState usDecFunction args mem next).pre = none ∧
      (EntryState usDecFunction args mem next).mem = mem ∧
      lookupName (EntryState usDecFunction args mem next).env "%xj" = some (.ptr xj) ∧
      lookupName (EntryState usDecFunction args mem next).env "%pos0" =
        some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName (EntryState usDecFunction args mem next).env "%n" =
        some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName (EntryState usDecFunction args mem next).env "%nxp" =
        some (.int 64 (BitVec.ofNat 64 nps)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  all_goals (rw [entryState_env hargs]; ud_lk)

/-! ### The empty-list entry run

The caller's cursor is at the list's end, so `entry`'s test is false and
`while.end`'s is false too: the run reaches `while.end35` in two control steps,
never visiting the latch.  The state carries the exit word's `DecodeEntryExit`
variant — the walk's own seed at `(0, nps, [])` and the `%k.0.lcssa` cell the
edge supplies — and the goal is the seed's `.decoded body nps`. -/
theorem emptySeedRun
    {args : List Value} {mem : Mem} {next : Nat}
    {b n dst err xp xj nps pos0 tab k0 : Nat}
    {body : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err,
      .ptr xp, .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
      .ptr tab])
    (hxj : readBytes mem xj 8 = some (wordBytes 8 k0))
    (hnpslen : (escAt body ⟨true, false⟩ 0).length = nps)
    (hk0 : k0 = nps)
    (hnps64 : nps < 2 ^ 64)
    (goal : EscapeOutcome)
    (hgoal : goal = .decoded body nps) :
    ∃ (e : State) (j : Nat), j ≤ entryBlocks ∧ e.pc = "while.end35" ∧
      goal = .decoded body nps ∧
      decodeTwoExitWord body ⟨true, false⟩ dst nps goal e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction
        (EntryState usDecFunction args mem next) = runFuel escapeCalls k usDecFunction e := by
  -- the caller's cursor is at the list's end, so both entry tests are false
  have hk0v : k0 < 2 ^ 64 := by omega
  have hcond : evalICmp .ult (BitVec.ofNat 64 k0) (BitVec.ofNat 64 nps) =
      (0 : BitVec 1) := by
    refine (evalICmp_ult_zero_iff _ _).2 ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk0v, Nat.mod_eq_of_lt hnps64]
    omega
  obtain ⟨hpc0, hpre0, hmem0, hxjcell, hpos0cell, hncell, hnxpcell⟩ :=
    entryState_cells (mem := mem) (next := next) hargs
  -- `entry` leaves for `while.end`
  let s1 : State :=
    { (withEnv (udEntryEnv (EntryState usDecFunction args mem next).env
          (BitVec.ofNat 64 k0) (BitVec.ofNat 64 pos0) (BitVec.ofNat 64 n)
          (BitVec.ofNat 64 nps)) (EntryState usDecFunction args mem next)) with
      pc := "while.end", pre := some "entry" }
  have hstep1 : step escapeCalls usDecFunction (EntryState usDecFunction args mem next) =
      .jump s1 := by
    have h := udEntry_step_zero (EntryState usDecFunction args mem next).env
      (EntryState usDecFunction args mem next) xj (BitVec.ofNat 64 k0)
      (BitVec.ofNat 64 pos0) (BitVec.ofNat 64 n) (BitVec.ofNat 64 nps) hpc0
      hxjcell (by
        rw [hmem0, hxj]
        rw [show (BitVec.ofNat 64 k0).toNat = k0 from by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk0v]]
        rfl) hpos0cell hncell hnxpcell hcond
    rw [show withEnv (EntryState usDecFunction args mem next).env
        (EntryState usDecFunction args mem next)
        = EntryState usDecFunction args mem next from rfl] at h
    exact h
  -- `while.end` leaves for `while.end35`
  let s2 : State :=
    { (withEnv (udWhileEndEnv s1.env (BitVec.ofNat 64 k0) (BitVec.ofNat 64 nps)) s1) with
      pc := "while.end35", pre := some "while.end" }
  have hstep2 : step escapeCalls usDecFunction s1 = .jump s2 := by
    have hinc : phiIncoming "entry" udWhileEndIncoming = some (.reg "%0") := by decide
    have h0 : lookupName s1.env "%0" = some (.int 64 (BitVec.ofNat 64 k0)) := by
      simp only [s1, udEntryEnv, withEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have hnxp : lookupName s1.env "%nxp" =
        some (.int 64 (BitVec.ofNat 64 nps)) := by
      simp only [s1, udEntryEnv, withEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), entryState_env hargs]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have h := udWhileEnd_step s1.env s1 "entry" (.reg "%0")
      (BitVec.ofNat 64 k0) (BitVec.ofNat 64 nps) (by rfl) (by rfl) hinc
      (evalOperand_reg_of s1.env s1 "%0" (.int 64 (BitVec.ofNat 64 k0)) h0)
      hnxp hcond
    rw [show withEnv s1.env s1 = s1 from rfl] at h
    exact h
  refine ⟨s2, 2, by decide, rfl, hgoal, ?_, ?_⟩
  · -- the exit word: `DecodeEntryExit` at the seed's walk
    refine Or.inr (Or.inr ⟨rfl, ⟨0, [], ?_, ?_, ?_⟩, ?_⟩)
    · -- the walk from the list's end is the goal
      show escapeDecodeGo body 0 nps ((escAt body ⟨true, false⟩ 0).drop nps) [] = goal
      have hnil : (escAt body ⟨true, false⟩ 0).drop nps = [] := by
        rw [List.drop_eq_nil_of_le]
        omega
      rw [hnil, escapeDecodeGo_nil, List.nil_append, List.drop_zero]
      exact hgoal.symm
    · -- nothing was written, so the empty prefix is in the store
      show readBytes s2.mem dst 0 = some []
      rfl
    · -- the list's length, which is `nps` by the staging
      exact hnpslen
    · -- the `%k.0.lcssa` cell the `while.end` edge supplies
      show lookupName s2.env "%k.0.lcssa" = some (.int 64 (BitVec.ofNat 64 nps))
      simp only [s2, udWhileEndEnv, withEnv]
      rw [lookupName_cons_ne _ _ (by decide), hk0]
      exact lookupName_cons_self _ _ _
  · -- two control steps
    intro k
    rw [show 2 + k = 1 + (1 + k) from by omega]
    rw [runFuel_jump_prefix hstep1 (1 + k)]
    rw [runFuel_jump_prefix hstep2 k]


/-! ### The refusal's return

The refusal's two stores happen in `if.then20`/`if.then22`
(`JsonEscapeIR.lean:384-385`, `:539-540`), and the exit state is `cleanup41`,
whose single `phi` carries the return value.  With the refusal edge's operand the
block returns `-1` in one control step and touches no memory, which is the run
half of `ExpandExit`'s refusal arm; the memory half is the exit word's two store
facts (`DecodeRefusalExit` names neither today). -/
theorem refusalReturn (s : State) (hs : s.pc = "cleanup41")
    (hpre : s.pre = some "if.then22") :
    runFuel escapeCalls 1 usDecFunction s =
      some (.ret (some (.int 64 (BitVec.ofInt 64 (-1)))) s.mem) := by
  have hinc : phiIncoming "if.then22" udCleanup41Incoming =
      some (.imm (.int 64 (BitVec.ofInt 64 (-1)))) := by decide
  have hop : evalOperand (withEnv s.env s) (.imm (.int 64 (BitVec.ofInt 64 (-1)))) =
      some (.int 64 (BitVec.ofInt 64 (-1))) := rfl
  have h := udCleanup41_step s.env s "if.then22" (.imm (.int 64 (BitVec.ofInt 64 (-1))))
    (BitVec.ofInt 64 (-1)) hs hpre hinc hop
  rw [show withEnv s.env s = s from rfl] at h
  simp only [runFuel, h]
  rfl

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchInv

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_latch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_latch

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_params' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_params

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_paddr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_paddr_eq

/-- info: 'LeanLLVM.Vellum.escAt_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escAt_length_le

/-- info: 'LeanLLVM.Vellum.entryState_env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryState_env

/-- info: 'LeanLLVM.Vellum.entryState_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryState_cells

/-- info: 'LeanLLVM.Vellum.emptySeedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emptySeedRun

/-- info: 'LeanLLVM.Vellum.refusalReturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalReturn

end LeanLLVM.Vellum
