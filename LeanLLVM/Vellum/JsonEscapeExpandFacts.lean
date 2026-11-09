/-
The expander's four runs, composed from the trace's block steps.

`JsonEscapeExpandRun` states the expander's claim with `ExpandFacts` as its
hypothesis; this module starts discharging that bundle from the record's `pre`.
The staged invariant and the arm statements the iteration and refusal consume are
in `JsonEscapeExpandStaged`, below `JsonEscapeExpandRun`.

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
import LeanLLVM.Vellum.JsonEscapeExpandStaged

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

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
      assemblyExitWord body ⟨true, false⟩ dst nps goal err xj e ∧
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
facts (`DecodeRefusalExit` names both). -/
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

/-! ### The exit stage's quantifier admits a state the walk never visits

`ExpandExit` quantifies over every state `decodeTwoExit` and the exit word admit.
Neither of the three edges records the state's predecessor, and every block at
which the walk ends — `while.end35` and `cleanup41` — starts with a `phi` whose
selection reads that field (`evalInstr`'s `.phi` arm: no predecessor, nothing
selected).  So a state with the exit's block, its cells and the word's stores but
no predecessor satisfies both premises and is stuck: the block's `phi` selects
nothing, `step` is `.ub`, and the record's `post` is `False` at that outcome.
`ExpandExit` therefore demands an outcome at a state where no outcome can satisfy
it, and the field is false at every staging — which makes `ExpandFacts`
uninhabited rather than merely unproved.

The failing clause is executable and the refutation below is it.  The state is at
`cleanup41`, so the refusal word is the one that admits it.

**The predecessor sets, read off the pinned block tables.**  `while.end35`'s
`phi` incoming list names `while.end`, `while.body6`, `cleanup32` and `while.body`
(`udWhileEnd35IncomingJ`/`_I`/`_K`), and `cleanup41`'s names `us_run.exit112`,
`if.then20` and `if.then22` (`udCleanup41Incoming`) — so a word that records the
block but not the predecessor admits states the body never reaches, and one that
records the predecessors must still cover all three of `cleanup41`'s.
`us_run.exit112` is not an edge case: it stores the cursor, computes
`%add40 = %sub38 + %j.0.lcssa`, and the `cleanup41` `phi` returns that value, so it
is where a successful call's returned length is concluded, and a refusal-only
predecessor set would leave the success path with no exit word at all.
`refusalReturn` already takes the refusal's predecessor as a hypothesis; the words
do not yet supply it.

**Which of `while.end35`'s edges are live.**  Under the record's `pre` the list is
exactly the body's escape positions and every entry `q` satisfies
`pos0 ≤ q < pos0 + n`.  `land.rhs → while.body` is taken only when
`pos0 > ps[k]`, and `while.body6 → while.end35` only when `ps[c] ≥ pos0 + n`;
neither is possible at an admissible staging, so `cleanup32` and `while.end` are
the reachable pair there.  The restriction is a fact about the staging, not about
the block, and a word that does not carry the staging cannot state it — which is
why the reachable-set claim is a separate statement about admissible stagings
rather than a widened docstring. -/

/-- A memory whose bytes are zero from address `0` to `n - 1`.  The refusal word's
two store clauses read eight bytes at the caller's destinations, so the refuting
state needs a memory that answers them. -/
def zeroMem (n : Nat) : Mem := (List.range n).map (fun i => ((i : Nat), (0 : UInt8)))

theorem readByte_append : ∀ (l1 l2 : Mem) (a : Nat),
    readByte (l1 ++ l2) a =
      match readByte l1 a with
      | some v => some v
      | none => readByte l2 a
  | [], l2, a => by simp [readByte]
  | (k, v) :: rest, l2, a => by
      simp only [List.cons_append, readByte]
      by_cases h : k = a
      · simp [h]
      · simp [h, readByte_append rest l2 a]

theorem zeroMem_succ (n : Nat) : zeroMem (n + 1) = zeroMem n ++ [(n, (0 : UInt8))] := by
  simp [zeroMem, List.range_succ, List.map_append]

theorem readByte_zeroMem_ge (N a : Nat) : N ≤ a → readByte (zeroMem N) a = none := by
  induction N with
  | zero => intro _; rfl
  | succ n ih =>
      intro ha
      rw [zeroMem_succ, readByte_append, ih (by omega)]
      rw [readByte]
      have hne : ¬ n = a := by omega
      simp [hne, readByte]

theorem readByte_zeroMem_lt (N a : Nat) (h : a < N) : readByte (zeroMem N) a = some 0 := by
  induction N with
  | zero => omega
  | succ n ih =>
      rw [zeroMem_succ, readByte_append]
      by_cases hlt : a < n
      · rw [ih hlt]
      · have hae : a = n := by omega
        rw [readByte_zeroMem_ge n a (by omega)]
        subst hae
        simp [readByte]

theorem readBytes_zeroMem : ∀ (k N a : Nat), a + k ≤ N →
    readBytes (zeroMem N) a k = some (List.replicate k (0 : UInt8)) := by
  intro k
  induction k with
  | zero => intro N a h; simp [readBytes]
  | succ k ih =>
      intro N a h
      have ha : a < N := by omega
      rw [readBytes]
      rw [readByte_zeroMem_lt N a ha]
      rw [ih N (a + 1) (by omega)]
      simp [List.replicate_succ]

theorem wordBytes_zero_eight :
    wordBytes 8 (BitVec.toNat (0 : BitVec 64)) = List.replicate 8 (0 : UInt8) := by decide

/-- The refuting state: `cleanup41`'s block with the refusal word's four cells and
its two stores, and no predecessor.  Nothing in `DecodeRefusalExit` excludes it,
because the word records neither the predecessor nor how the state was reached. -/
def stuckState (err xj : Nat) : State where
  env := [("%err", .ptr err), ("%xj", .ptr xj), ("%sub", .int 64 0), ("%inc11", .int 64 0)]
  mem := zeroMem (max err xj + 8)
  next := 0
  pc := "cleanup41"
  pre := none

theorem stuckState_err (err xj : Nat) :
    lookupName (stuckState err xj).env "%err" = some (.ptr err) := by
  simp only [stuckState, lookupName]
  simp

theorem stuckState_xj (err xj : Nat) :
    lookupName (stuckState err xj).env "%xj" = some (.ptr xj) := by
  simp only [stuckState, lookupName,
    if_neg (by decide : ("%err" : String) ≠ "%xj")]
  simp

theorem stuckState_sub (err xj : Nat) :
    lookupName (stuckState err xj).env "%sub" = some (.int 64 0) := by
  simp only [stuckState, lookupName,
    if_neg (by decide : ("%err" : String) ≠ "%sub"),
    if_neg (by decide : ("%xj" : String) ≠ "%sub")]
  simp

theorem stuckState_inc11 (err xj : Nat) :
    lookupName (stuckState err xj).env "%inc11" = some (.int 64 0) := by
  simp only [stuckState, lookupName,
    if_neg (by decide : ("%err" : String) ≠ "%inc11"),
    if_neg (by decide : ("%xj" : String) ≠ "%inc11"),
    if_neg (by decide : ("%sub" : String) ≠ "%inc11")]
  simp

/-- The refusal word admits the refuting state: its four cells and its two
stores, and nothing about how the block was entered. -/
theorem stuckState_refusal (err xj : Nat) : DecodeRefusalExit (stuckState err xj) := by
  refine ⟨rfl, 0, 0, err, xj, stuckState_sub err xj, stuckState_inc11 err xj,
    stuckState_err err xj, stuckState_xj err xj, ?_, ?_⟩
  · rw [show (stuckState err xj).mem = zeroMem (max err xj + 8) from rfl,
      readBytes_zeroMem 8 (max err xj + 8) err (by omega), wordBytes_zero_eight]
  · rw [show (stuckState err xj).mem = zeroMem (max err xj + 8) from rfl,
      readBytes_zeroMem 8 (max err xj + 8) xj (by omega), wordBytes_zero_eight]

/-- `cleanup41` at the refuting state is stuck: its one instruction is a `phi`
and there is no predecessor to select from, so the block is `.ub`. -/
theorem stuckState_step (err xj : Nat) :
    step escapeCalls usDecFunction (stuckState err xj) = .ub := by
  have hpc : (stuckState err xj).pc = "cleanup41" := rfl
  have hpre : (stuckState err xj).pre = none := rfl
  simp only [step, hpc, findBlock_udCleanup41, udCleanup41_instrs, denoteCode,
    evalInstr_phi_no_pred hpre]

theorem runFuel_stuck (err xj k : Nat) :
    runFuel escapeCalls (k + 1) usDecFunction (stuckState err xj) = some .ub := by
  simp only [runFuel, stuckState_step]

/-- **The exit stage is false at every staging.**  The state above satisfies
`decodeTwoExit` and the exit word's refusal edge, yet every run from it is `.ub`
and the record's `post` is `False` there, so the continuation `ExpandExit`
demands does not exist.  `body`, `st`, `dst`, `goal` and the record's
destinations are arbitrary: the refusal edge's cells are the state's own, so no
choice of them excludes the refuting state. -/
theorem expandExit_false (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst : Nat) (goal : EscapeOutcome)
    (err xj : Nat) :
    ¬ ExpandExit args mem next body st dst goal err xj := by
  intro h
  have hexit : decodeTwoExit (stuckState err xj) := Or.inr rfl
  have hword : assemblyExitWord body st dst (expandPosCount args) goal err xj
      (stuckState err xj) :=
    Or.inr (Or.inl ⟨stuckState_refusal err xj, stuckState_err err xj,
      stuckState_xj err xj⟩)
  obtain ⟨o, ho, hpost⟩ := h (stuckState err xj) hexit hword
  have hk : expandExitFuel args = (expandExitFuel args - 1) + 1 := by
    unfold expandExitFuel; omega
  have hub : runFuel escapeCalls (expandExitFuel args) usDecFunction
      (stuckState err xj) = some .ub := by
    rw [hk]; exact runFuel_stuck err xj _
  rw [hub] at ho
  have ho' : o = .ub := (Option.some.inj ho).symm
  subst ho'
  exact escape_expand_ub_false escapeExpandBudget args mem next hpost

/-- **The expander's bundle is uninhabited.**  `ExpandExit` is a field of
`ExpandFacts`, and it is false at every staging, so no provider exists and
`escape_expand_satisfies`'s hypothesis cannot be met — the record is not entitled
about `usDecFunction` until the exit word names the predecessor its block's `phi`
reads. -/
theorem expandFacts_uninhabited (args : List Value) (mem : Mem) (next : Nat) :
    ExpandFacts args mem next → False := by
  intro hf
  exact expandExit_false args mem next hf.body hf.st hf.dst hf.goal hf.err hf.xj hf.exit

/-! ### The two `while.end35` edges the staging kills

`while.end35`'s `phi` names four predecessors, so a word that records only the
latch's edge and the entry's would be asserting something about the body that is
true of the staging rather than of the block.  The two remaining edges are dead
for a reason the staging states and the block does not:

* `land.rhs → while.body` (the pre-scan skipping a position before the window) is
  taken on `ugt %pos0 %conv`, and the staging puts every entry at or above
  `pos0`, so the test is zero and the edge is not taken;
* `while.body6 → while.end35` (the loop leaving without copying) is taken on
  `%cmp9.not` zero, i.e. `ps[c] ≥ pos0 + n`, and the staging puts every entry
  below the window's end, so the test is one and the edge is not taken.

Both are stated against `DecodeStaging`, the staging predicate the invariant
carries, and both consume its range clause — the fact that makes the exclusion a
property of admissible stagings rather than of the pinned body. -/

/-- **The pre-scan's skip arm is dead at an admissible staging.**  `land.rhs` tests
`ugt %pos0 %conv` and reaches `while.body` only when the position it loaded is
below the window's start. -/
theorem staging_land_rhs_test {M : Mem} {nps xp pos0 n : Nat} {ps : List Nat}
    {addv pos0v conv : BitVec 64} {k q : Nat}
    (hstage : DecodeStaging M nps xp pos0 n ps addv)
    (hpos0 : pos0v = BitVec.ofNat 64 pos0)
    (hq : ps[k]? = some q) (hconv : conv = BitVec.ofNat 64 q)
    (h32 : pos0 + n ≤ 2 ^ 32) :
    evalICmp .ugt pos0v conv = (0 : BitVec 1) := by
  obtain ⟨-, -, hrange, -⟩ := hstage
  obtain ⟨hlo, hhi⟩ := hrange k q hq
  have hq32 : q < 2 ^ 64 := by omega
  refine (evalICmp_ugt_zero_iff _ _).2 ?_
  rw [hconv, hpos0, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hq32, Nat.mod_eq_of_lt (by omega : pos0 < 2 ^ 64)]
  omega

/-- **The loop's no-copy arm is dead at an admissible staging.**  `while.body6`
tests `ugt %add %conv8` and reaches `while.end35` only when the position it loaded
is at or past the window's end, so the test is one and the copy is taken. -/
theorem staging_whileBody6_test {M : Mem} {nps xp pos0 n : Nat} {ps : List Nat}
    {addv conv8 : BitVec 64} {c q : Nat}
    (hstage : DecodeStaging M nps xp pos0 n ps addv)
    (hadd : addv.toNat = pos0 + n)
    (hq : ps[c]? = some q) (hconv : conv8 = BitVec.ofNat 64 q)
    (h32 : pos0 + n ≤ 2 ^ 32) :
    evalICmp .ugt addv conv8 = (1 : BitVec 1) := by
  obtain ⟨-, -, hrange, -⟩ := hstage
  obtain ⟨hlo, hhi⟩ := hrange c q hq
  have hq32 : q < 2 ^ 64 := by omega
  have hlt : conv8.toNat < addv.toNat := by
    rw [hconv, hadd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
    omega
  have hne : evalICmp .ugt addv conv8 ≠ (0 : BitVec 1) := by
    intro h
    exact (evalICmp_ugt_zero_iff _ _).1 h hlt
  rcases bv1_cases (evalICmp .ugt addv conv8) with h | h
  · exact absurd h hne
  · exact h

/-! ### Axiom footprints: the exit stage's refutation -/

/-- info: 'LeanLLVM.Vellum.zeroMem' does not depend on any axioms -/
#guard_msgs in
#print axioms zeroMem

/-- info: 'LeanLLVM.Vellum.readBytes_zeroMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_zeroMem

/-- info: 'LeanLLVM.Vellum.stuckState_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stuckState_refusal

/-- info: 'LeanLLVM.Vellum.stuckState_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stuckState_step

/-- info: 'LeanLLVM.Vellum.expandExit_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms expandExit_false

/-- info: 'LeanLLVM.Vellum.expandFacts_uninhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms expandFacts_uninhabited

/-- info: 'LeanLLVM.Vellum.staging_land_rhs_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staging_land_rhs_test

/-- info: 'LeanLLVM.Vellum.staging_whileBody6_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staging_whileBody6_test

end LeanLLVM.Vellum
