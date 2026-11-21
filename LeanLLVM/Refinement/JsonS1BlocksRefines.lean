/-
The block unit's composition layer: the entry, the phase's exits, the fused
loop's exit, the peel, the tail and the post, joined at the unit's own call
environment.

`JsonS1BlocksRefine` states the ASCII phase's run (entry to `for.end101` or
`if.then38`), `JsonS1BlocksEntry` the fused loop's first page, `JsonS1BlocksLoop`
the fused loop's induction, `JsonS1BlocksExit` the bound's block at both edges,
`JsonS1BlocksCompose` the peeled tail's merge, escape record and arm paths, and
`JsonS1BlocksRecordFrame` the post's memory conjuncts.  This module joins them:

* the entry's first step at `s1BlocksInit`, on both arms of its length test
  (`s1BlocksInit_step_short`, `s1BlocksInit_step_blocks`);
* the four ways `if.end170` returns — the peel's silent merge, the peel's escape
  merge, the aligned document's empty arm and its last-byte arm — each as a
  `runFuel` prefix ending at the return, with the post's verdict clause
  (`tail_silent_run`, `tail_escape_run`, `tail_aligned_run`, `tail_byte_run`);
* `for.end101`'s step to the peel at the ASCII latch's edge
  (`asciiExit_step_peel`);
* the fused loop's exit to the return, at the loop's own edge
  (`s1BlocksFusedExit_run`) and the ASCII phase's exit to the return
  (`s1BlocksAsciiExit_run`);
* the junction at the post's own definition (`s1BlocksPost_of_peel`).

`s1_blocks_refines` is the record's refinement statement: from the caller's
staging, every outcome the unit's run produces satisfies `s1BlocksPost`.

## What the composition still owes

The composition is stated at the state each module hands over, so the pieces
below are the exact bridges a full `s1_blocks_refines` proof consumes; each is a
hypothesis of the theorem that needs it, not a weakening of a stated conclusion.

* **The entry's cells at the exits.**  `AsciiInv` carries the index, the bound,
  the four carried words, `%b`, `%ent` and the gate; it does not carry `%and`,
  `%n`, `%conv`, `%xp`, `%nxp` or `%xcarry`, and `FusedExit` carries `%b`, `%ent`
  and `%shr` only.  `s1BlocksAsciiExit_run` and `s1BlocksFusedExit_run` therefore
  take those reads as hypotheses.  They hold by construction — the entry binds the
  cells and `forIncEnv`/`forBodyOut`/`ifEndEnv`/`forBody54Out` lay fresh cells
  over the running one — but no module states the ride-through.  The inductions
  are the reason: `AsciiTerm e` and `FusedTerm e` carry the terminal state with
  its environment inside the constructor, so a caller reaches the terminal's
  `env`/`s`/`c` without knowing that `env` is the running one (the seed's, for the
  phase).  A terminal that carried its carry — `AsciiTerm`'s two constructors do,
  under the binder — or a lemma `runFuel`-to-terminal at a fixed environment
  would close this bridge without the per-cell hypotheses.
* **The phase's hand-off arm.**  `AsciiTerm.handoff` stands at `if.then38`; the
  run from there is `JsonS1BlocksRefine.asciiHandoff_run` (two steps to
  `for.body54.lr.ph`), `JsonS1BlocksEntry.entry_first_page` (at most six to a
  `FusedEnd`), `fusedInv_runFuel` (five per remaining page) and then
  `s1BlocksFusedExit_run`.  What blocks the join is the loop's *page*
  environment: `FusedExit` exposes `%b`, `%ent` and `%shr`, but not `%n`,
  `%and` or `%conv`, and no module states those cells through
  `forBody54Out`/`ifEnd98Env`; the exit-side composition takes them as its
  hypotheses.
* **The short-document arm.**  A document below sixty-four bytes goes
  `entry` → `if.end50` → `for.end101` → the peel.  No block denotation exists for
  `if.end50` at `pre = "entry"`, for `for.end101` at `pre = "if.end50"`, or for
  the peel at that edge (`JsonS1BlocksExit` states the `for.inc` and `if.end98`
  edges only).
* **The model carries.**  `s1BlocksAsciiExit_run` and `s1BlocksFusedExit_run`
  take the returns' `VerdictStaging` as a hypothesis.  On the fused edge it is
  `JsonS1BlocksEntry.fused_end_staging`'s three inputs — the two packed words
  (`packLanes c.ascii = bytesToNat (asciiAcc bs …)`,
  `packLanes c.u8k = bytesToNat (klAll gate bs)`) and the error bit's
  characterization — and on the latch edge it is the zero words' own staging.
  Neither module proves them: they are the loop's register-to-model identities.
* **The entry array and its frame.**  The post's entry-array read is
  `JsonS1BlocksRecordFrame.entryWords_of_prefix_full`/`entryWords_of_prefix_store`
  over `EntryPrefix` and `EntryFrame`, and the peel's slot is
  `if_then103_store_stage1Word` over `PeelWordAtModel`; the loop's invariant
  carries the per-slot reads, not the composed prefix, so these are the loop's
  obligations at its exit memory.
* **The escape-armed ASCII prefix.**  `AsciiInv.gate` is stated for
  `%tobool.not = 1`, i.e. `arm & 2 = 0`; the phase's per-block `if.then` call on
  the other arm has no invariant, so the compositions here take the gate's off
  value.
* **The count's room.**  On the tail's escape arm the call's pre
  (`Γ_escape_positions base escapePositionsBudget`'s) is a premise of
  `tail_escape_run`, as `JsonS1BlocksSeparation` keeps it: the cursor's room over
  the document is the caller's accounting, not a consequence of the staging.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonS1BlocksLoop
import LeanLLVM.Refinement.JsonS1BlocksEntry
import LeanLLVM.Refinement.JsonS1BlocksExit
import LeanLLVM.Refinement.JsonS1BlocksTail
import LeanLLVM.Refinement.JsonS1BlocksCompose
import LeanLLVM.Refinement.JsonS1BlocksContract

namespace LeanLLVM.Refinement.JsonS1BlocksRefines

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- The entry state at the unit's arguments and the caller's memory. -/
def s1BlocksInit (args : List Value) (mem : Mem) : State :=
  { (initState s1BlocksFunction args) with mem := mem }

/-! ### The entry's environment

The seven parameters are the ABI's slots, in the routine's own order.  The
lemmas below read each one at the initial state's environment, so the entry's
step has its three premise reads. -/

theorem s1BlocksInit_env_n (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%n" = some (.int 64 n) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_arm (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%arm" = some (.int 64 arm) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_b (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%b" = some (.ptr b) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_ent (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%ent" = some (.ptr ent) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_xp (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%xp" = some (.ptr xp) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_nxp (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%nxp" = some (.ptr nxp) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

theorem s1BlocksInit_env_xcarry (mem : Mem) (b ent xp nxp xcarry : Nat)
    (n arm : BitVec 64) :
    lookupName (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env "%xcarry" = some (.ptr xcarry) := by
  simp only [s1BlocksInit, initState, s1BlocksFunction, List.map, List.zip,
    List.zipWith, lookupName]
  simp (config := { decide := true }) only [ite_true, ite_false]

/-! ### A completed chain

A chain of admitted jumps ending in a return is a `runFuel` prefix that ends at
the return, and the returned memory is the state the return carries. -/

theorem runFuel_one_ret {calls : Calls} {f : Function} {s s' : State} {v : Option Value}
    (h : step calls f s = .ret v s') : runFuel calls 1 f s = some (.ret v s'.mem) := by
  simp only [runFuel, h]

theorem runFuel_jump1_ret {calls : Calls} {f : Function} {s0 s1 s2 : State}
    {v : Option Value}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .ret v s2) :
    runFuel calls 2 f s0 = some (.ret v s2.mem) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix h01 1]
  exact runFuel_one_ret h12

theorem runFuel_jump2_ret {calls : Calls} {f : Function} {s0 s1 s2 s3 : State}
    {v : Option Value}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .ret v s3) :
    runFuel calls 3 f s0 = some (.ret v s3.mem) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, runFuel_jump2 h01 h12 1]
  exact runFuel_one_ret h23

theorem runFuel_jump3_ret {calls : Calls} {f : Function} {s0 s1 s2 s3 s4 : State}
    {v : Option Value}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .jump s3) (h34 : step calls f s3 = .ret v s4) :
    runFuel calls 4 f s0 = some (.ret v s4.mem) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, runFuel_jump3 h01 h12 h23 1]
  exact runFuel_one_ret h34

theorem runFuel_jump4_ret {calls : Calls} {f : Function}
    {s0 s1 s2 s3 s4 s5 : State} {v : Option Value}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .jump s3) (h34 : step calls f s3 = .jump s4)
    (h45 : step calls f s4 = .ret v s5) :
    runFuel calls 5 f s0 = some (.ret v s5.mem) := by
  rw [show (5 : Nat) = 4 + 1 from rfl, runFuel_jump4 h01 h12 h23 h34 1]
  exact runFuel_one_ret h45

/-! ### The tail's arms

`if.end170`'s return is reached from four states: the peel's silent merge
(`if.end147`'s step to `if.end153.thread`, that block's zero test, and the
return), the peel's escape merge (`if.then150`'s call in place of the merge's
skip), the aligned document's `if.end153` with no byte to read, and the aligned
document's last byte at `if.then164`.  Each arm is a `runFuel` prefix ending at
the return, with the post's verdict clause read off the staging. -/

/-- A register read through `if.end153`'s three cells to the environment beneath
them. -/
theorem lookupName_ifEnd153Env_of (env : Env) (n : BitVec 64) (u8k : List (BitVec 64))
    {k : String} {v : Value} (h : lookupName env k = some v)
    (h1 : "%cmp158.not.not" ≠ k) (h2 : "%cmp155" ≠ k) (h3 : "%200" ≠ k) :
    lookupName (ifEnd153Env env n u8k) k = some v := by
  simp only [ifEnd153Env, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3]
  exact h

/-- The peel's test at `if.end153`'s output. -/
theorem lookupName_ifEnd153Env_cmp155 (env : Env) (n : BitVec 64)
    (u8k : List (BitVec 64)) :
    lookupName (ifEnd153Env env n u8k) "%cmp155" =
      some (.int 1 (evalICmp .eq (ptestzU8k u8k) 0)) := by
  simp only [ifEnd153Env, cells]
  block_lk_cons

/-- A register read through `if.then164`'s eight cells to the environment beneath
them. -/
theorem lookupName_ifThen164Env_of (env : Env) (p : Nat) (last : BitVec 8)
    (err : BitVec 1) {k : String} {v : Value} (h : lookupName env k = some v)
    (h1 : "%or169500" ≠ k) (h2 : "%204" ≠ k) (h3 : "%cmp3.i" ≠ k)
    (h4 : "%cmp.i" ≠ k) (h5 : "%203" ≠ k) (h6 : "%202" ≠ k)
    (h7 : "%arrayidx166" ≠ k) (h8 : "%201" ≠ k) :
    lookupName (ifThen164Env env p last err) k = some v := by
  simp only [ifThen164Env, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4,
    lookupName_cons_ne _ _ h5, lookupName_cons_ne _ _ h6,
    lookupName_cons_ne _ _ h7, lookupName_cons_ne _ _ h8]
  exact h

/-- The tail's silent arm: the merge's skip, the thread's zero test, and the
return — three control steps from `if.end147`'s state at the peel's store. -/
theorem tail_silent_run {esc : Calls} (env : Env) (s : State)
    (v : IfThen103Values) (u8k : List (BitVec 64)) (arm : BitVec 64)
    (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 1)
    (hstage : VerdictStaging v.or279 u8k bs n nb gate
      (evalICmp .eq (ptestzU8k u8k) 0)) :
    runFuel (s1BlocksCallsEsc esc) 3 s1BlocksFunction
        (stateAt (ifThen103Out env v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) =
      some (.ret (some (.int 64 (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0))))
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8))) ∧
      VerdictPost (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0)) bs := by
  obtain ⟨h1, h2, h3, hpost⟩ := tail_silent_path env s v u8k arm bs n nb gate
    hu8k harm hbit hstage
  exact ⟨by simpa only [stateAt] using runFuel_jump2_ret h1 h2 h3, hpost⟩

/-- The tail's escape arm: the merge's escape branch, the call's step, the
thread's zero test and the return — four control steps. -/
theorem tail_escape_run {esc : Calls} {base : Nat} (hEsc : escapeEntryAt esc base)
    (env : Env) (s : State) (v : IfThen103Values) (u8k : List (BitVec 64))
    (arm shr : BitVec 64) (xp nxp xcarry : Nat)
    (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (h136 : v.w136.length = 4) (h137 : v.w137.length = 4)
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 0)
    (hescPre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 v.mask391, .int 64 (ifThen150QuoteWord v.w136 v.w137), .int 64 v.xorI,
       .int 64 shr, .ptr xp, .ptr nxp, .ptr xcarry]
      (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) s.next)
    (hstage : VerdictStaging v.or279 u8k bs n nb gate
      (evalICmp .eq (ptestzU8k u8k) 0)) :
    ∃ (r : CallOutcome) (xn0 : Nat) (position : List Nat) (carryBytes : List UInt8),
      esc escapeListCallee
        [.int 64 v.mask391, .int 64 (ifThen150QuoteWord v.w136 v.w137), .int 64 v.xorI,
         .int 64 shr, .ptr xp, .ptr nxp, .ptr xcarry]
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) s.next = some r ∧
      runFuel (s1BlocksCallsEsc esc) 4 s1BlocksFunction
          (stateAt (ifThen103Out env v)
            { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                     pc := "if.end147", pre := some "if.then103" }) =
        some (.ret (some (.int 64
            (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0)))) r.mem) ∧
      VerdictPost (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0)) bs := by
  obtain ⟨r, xn0, position, carryBytes, hcall, -, -, -, h1, h2, h3, h4, hpost⟩ :=
    tail_escape_path hEsc env s v u8k arm shr xp nxp xcarry bs n nb gate
      hu8k harm h136 h137 hshr hxp hnxp hxcarry hbit hescPre hstage
  exact ⟨r, xn0, position, carryBytes, hcall, by simpa only [stateAt] using runFuel_jump3_ret h1 h2 h3 h4, hpost⟩

/-- The aligned document's empty arm: `if.end153`'s zero test and the return —
two control steps. -/
theorem tail_aligned_run {esc : Calls} (env : Env) (s : State)
    (n : BitVec 64) (u8k ascii : List (BitVec 64))
    (bs : List UInt8) (nb : Nat) (gate : Bool)
    (hpc : s.pc = "if.end153")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (hasc : lookupName env "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (hbit : evalICmp .eq n 0 = 1)
    (hstage : VerdictStaging ascii u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k u8k) 0)) :
    runFuel (s1BlocksCallsEsc esc) 2 s1BlocksFunction (stateAt env s) =
      some (.ret (some (.int 64 (verdictWord ascii (evalICmp .eq (ptestzU8k u8k) 0))))
        s.mem) ∧
      VerdictPost (verdictWord ascii (evalICmp .eq (ptestzU8k u8k) 0)) bs := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end153Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153
  have h1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.end170", pre := some "if.end153" }) := by
    rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
    exact if_end153_step_nothing env s n u8k hpc hn hu8k hbit
  have h2 := (if_end170_step_esc esc (ifEnd153Env env n u8k)
    { s with pc := "if.end170", pre := some "if.end153" } "if.end153"
    (.reg "%ascii.1.lcssa") (.reg "%cmp155") ascii u8k bs bs.length nb gate
    (evalICmp .eq (ptestzU8k u8k) 0) rfl rfl (by rfl)
    (evalOperand_reg_of _ _ _ _
      (lookupName_ifEnd153Env_of env n u8k hasc (by decide) (by decide) (by decide)))
    (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifEnd153Env_cmp155 env n u8k)) hstage)
  exact ⟨by simpa only [stateAt] using runFuel_jump1_ret h1 h2.1, h2.2⟩

/-- The aligned document's last-byte arm: `if.end153`'s test, `if.then164`'s two
byte tests, and the return — three control steps. -/
theorem tail_byte_run {esc : Calls} (env : Env) (s : State)
    (n : BitVec 64) (u8k ascii : List (BitVec 64)) (b : Nat) (last : UInt8)
    (bs : List UInt8) (nb : Nat) (gate : Bool)
    (hpc : s.pc = "if.end153")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (hasc : lookupName env "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (hb : lookupName env "%b" = some (.ptr b))
    (hbit : evalICmp .eq n 0 = 0)
    (hpos : (n.signExtend 64).toNat < 2 ^ 63)
    (hp : 1 ≤ b + (n.signExtend 64).toNat)
    (hr : readBytes s.mem (b + (n.signExtend 64).toNat - 1) 1 = some [last])
    (hstage : VerdictStaging ascii u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))) :
    runFuel (s1BlocksCallsEsc esc) 3 s1BlocksFunction (stateAt env s) =
      some (.ret (some (.int 64 (verdictWord ascii
          (evalICmp .eq (ptestzU8k u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat)))))
        s.mem) ∧
      VerdictPost (verdictWord ascii
        (evalICmp .eq (ptestzU8k u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))) bs := by
  have hfind153 : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end153Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153
  have h1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.then164", pre := some "if.end153" }) := by
    rw [step_esc_of_free esc s1BlocksFunction _ _ hfind153 (by decide)]
    exact if_end153_step_tail env s n u8k hpc hn hu8k hbit
  have hfind164 : s1BlocksFunction.findBlock
      (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.then164", pre := some "if.end153" }).pc =
      some if_then164Block := by
    rw [show (stateAt (ifEnd153Env env n u8k)
      { s with pc := "if.then164", pre := some "if.end153" }).pc = "if.then164" from rfl]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then164
  have h2 : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.then164", pre := some "if.end153" }) =
      .jump (stateAt
        (ifThen164Env (ifEnd153Env env n u8k) (b + (n.signExtend 64).toNat)
          (BitVec.ofNat 8 last.toNat) (evalICmp .eq (ptestzU8k u8k) 0))
        { s with pc := "if.end170", pre := some "if.then164" }) := by
    rw [step_esc_of_free esc s1BlocksFunction _ _ hfind164 (by decide)]
    exact if_then164_step (ifEnd153Env env n u8k)
      { s with pc := "if.then164", pre := some "if.end153" } n b last
      (evalICmp .eq (ptestzU8k u8k) 0) rfl
      (lookupName_ifEnd153Env_of env n u8k hn (by decide) (by decide) (by decide))
      (lookupName_ifEnd153Env_of env n u8k hb (by decide) (by decide) (by decide))
      (lookupName_ifEnd153Env_cmp155 env n u8k) hpos hp hr
  have h3 := (if_end170_step_esc esc
    (ifThen164Env (ifEnd153Env env n u8k) (b + (n.signExtend 64).toNat)
      (BitVec.ofNat 8 last.toNat) (evalICmp .eq (ptestzU8k u8k) 0))
    { s with pc := "if.end170", pre := some "if.then164" } "if.then164"
    (.reg "%ascii.1.lcssa") (.reg "%or169500") ascii u8k bs bs.length nb gate
    (evalICmp .eq (ptestzU8k u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))
    rfl rfl (by rfl)
    (evalOperand_reg_of _ _ _ _
      (lookupName_ifThen164Env_of _ _ _ _
        (lookupName_ifEnd153Env_of env n u8k hasc (by decide) (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
    (by rfl)
    (evalOperand_reg_of _ _ _ _
      (ifThen164Env_or169500 _ _ _ _)) hstage)
  exact ⟨by simpa only [stateAt] using runFuel_jump2_ret h1 h2 h3.1, h3.2⟩

/-! ### The fused loop's exit to the return

`FusedExit`'s state is at `for.end101` with `if.end98` as its predecessor.  The
block's run leaves the peel's test; the aligned document's arm is `if.end153` at
the block's output, and the partial one's is the peel at `if.then103`, whose
store is the loop's last write and whose merge joins the tail. -/

/-- The escape gate's bit is set when the arm's bit is clear. -/
theorem evalICmp_eq_zero_of_and_two_zero (arm : BitVec 64) (h : arm &&& 2 = 0) :
    evalICmp .eq (arm &&& 2) 0 = 1 := by
  unfold evalICmp
  rw [h]
  decide

/-- The peel's values at the fused edge, as the block builds them. -/
abbrev fusedPeelValues (env : Env) (c : FusedCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (conv : BitVec 32) : IfThen103Values :=
  ifThen103Values n c.b bs136 bs137 c.ascii c.st0 c.st9 c.st15 c.prevS andv
    c.shr c.ent conv c.prevAscii

theorem s1BlocksFusedExit_run {esc : Calls} (env : Env) (s : State) (c : FusedCarry)
    (andv n : BitVec 64) (conv : BitVec 32) (bs136 bs137 : List UInt8)
    (bs : List UInt8) (nb : Nat) (gate : Bool) (arm : BitVec 64)
    (h : FusedExit env s c)
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr c.b))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hasciilen : c.ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshr63 : c.shr.toNat < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧ 1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8, readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last])
    (hgateZero : arm &&& 2 = 0)
    (hsilent : ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      lookupName (ifThen103Out
        (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv) v)
        "%or.cond191" = some (.int 1 1))
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      VerdictStaging v.or279 c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstageByte : ∀ (last : UInt8),
      readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last] →
      VerdictStaging c.ascii c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction (stateAt env s) =
        some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  -- the block's own run and its peel test
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_end101Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, h.pc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  have hand' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hand (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hn' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hn (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hb' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hb (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hbitCell := lookupName_forEnd101OutOf_test env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv
  have hrun101 : denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv) s) :=
    fused_end_denote env s c andv h hand
  have hstep := step_at hfind hrun101
  by_cases hbitAligned : evalICmp .eq andv 0 = 1
  · -- the aligned document: the exit leaves for `if.end153`
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv) { s with pc := "if.end153", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      rw [hstep]
      rw [show for_end101Block.term = for_end101Term from rfl]
      simp only [for_end101Term]
      rw [execTerm_condbr_true (BlockEval.evalOperand_reg_of _ _ _ _ hbitCell) hbitAligned]
      simp only [stateAt, h.pc]
    by_cases hnz : evalICmp .eq n 0 = 1
    · -- the empty document
      have htail := tail_aligned_run (esc := esc) (env := forEnd101OutOf env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        { s with pc := "if.end153", pre := some "for.end101" } n c.u8k c.ascii
        bs nb gate rfl hn' (lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _)
        (lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _) hnz
        (by simpa only [stateAt] using hstage)
      exact ⟨1 + 2, _, _, by
        rw [show (1 + 2 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix hstep1 2]
        exact htail.1, htail.2⟩
    · -- the last byte
      have hnz0 : evalICmp .eq n 0 = 0 := by
        rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq n 0) with h0 | h1
        · exact h0
        · exact absurd h1 hnz
      obtain ⟨hposb, hpb⟩ := hnonzero hnz0
      obtain ⟨last, hlastr⟩ := hlast hnz0
      have htail := tail_byte_run (esc := esc) (env := forEnd101OutOf env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        { s with pc := "if.end153", pre := some "for.end101" } n c.u8k c.ascii
        c.b last bs nb gate rfl hn'
        (lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _)
        (lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _) hb' hnz0 hposb hpb
        (by simpa only [stateAt] using hlastr)
        (hstageByte last hlastr)
      exact ⟨1 + 3, _, _, by
        rw [show (1 + 3 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix hstep1 3]
        exact htail.1, htail.2⟩
  · -- the partial block: the peel's own run and the merge
    have hbit : evalICmp .eq andv 0 = 0 := by
      rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq andv 0) with h0 | h1
      · exact h0
      · exact absurd h1 hbitAligned
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv) { s with pc := "if.then103", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      rw [hstep]
      rw [show for_end101Block.term = for_end101Term from rfl]
      simp only [for_end101Term]
      rw [execTerm_condbr_false (BlockEval.evalOperand_reg_of _ _ _ _ hbitCell) hbit]
      simp only [stateAt, h.pc]
    let A : State := stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
      c.st0 c.st9 c.st15 andv) { s with pc := "if.then103", pre := some "for.end101" }
    let v : IfThen103Values := fusedPeelValues env c n andv bs136 bs137 conv
    have hden := fused_end_peel_denote env s c n andv conv bs136 bs137 h hn hconv
      hand hasciilen hpos h136 h137 hshr63
    have hbn := hsilent v rfl
    have hstep2 : step (s1BlocksCallsEsc esc) s1BlocksFunction A =
        .jump (stateAt (ifThen103Out (forEnd101OutOf env c.prevS c.ascii c.u8k
          c.prevAscii c.st0 c.st9 c.st15 andv) v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) := by
      have hfind103 : s1BlocksFunction.findBlock A.pc = some if_then103Block := by
        rw [show A.pc = "if.then103" from rfl]
        exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind103 (by decide)]
      exact if_then103_step_end147 _ A v rfl hbn (by
        rw [show A = stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv)
            { s with pc := "if.then103", pre := some "for.end101" } from rfl]
        exact hden)
    have htail := tail_silent_run (esc := esc)
      (env := forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv)
      A v c.u8k arm bs bs.length nb gate
      (lookupName_ifThen103Out_u8k _ v (lookupName_forEnd101OutOf_u8k env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv))
      (lookupName_ifThen103Out_arm _ v (lookupName_forEnd101OutOf_of env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv harm (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)))
      (evalICmp_eq_zero_of_and_two_zero arm hgateZero)
      (hstagePeel v rfl)
    exact ⟨1 + (1 + 3), _, _, by
      rw [show (1 + (1 + 3) : Nat) = 1 + (1 + 3) from rfl,
        runFuel_jump_prefix hstep1 (1 + 3), runFuel_jump_prefix hstep2 3]
      exact (by simpa only [A, stateAt] using htail.1), htail.2⟩


/-! ### The ASCII phase's exit to the return

`AsciiTerm.exit`'s state is at `for.end101` with `for.inc` as its predecessor.
The block's run reads the latch's four words and the arm's constants; the
aligned document's arm is `if.end153` at the block's output, and the partial
one's is the peel, whose values carry the latch's own words and the ASCII arm's
zero word. -/

/-- **`for.end101`'s step to the peel.**  A non-zero remainder leaves the block
for `if.then103` at the latch's own arm. -/
theorem asciiExit_step_peel (env : Env) (s : State) (c : AsciiCarry) (andv : BitVec 64)
    (hinv : AsciiInv env s c) (hand : lookupName env "%and" = some (.int 64 andv))
    (hbit : evalICmp .eq andv 0 = 0) :
    step s1BlocksCalls s1BlocksFunction (asciiExitState env s c) =
      .jump (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
        { s with pc := "if.then103", pre := some "for.end101" }) := by
  have hfind : s1BlocksFunction.findBlock (asciiExitState env s c).pc =
      some for_end101Block := by
    rw [show (asciiExitState env s c).pc = "for.end101" from rfl]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  rw [step_at hfind (asciiExit_denote env s c andv hinv hand)]
  rw [show for_end101Block.term = for_end101Term from rfl]
  simp only [for_end101Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [forEnd101Out_eq]
      exact for_end101_tobool102_not env c.prevS (List.replicate 4 0)
        (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv)) hbit]
  simp only [stateAt]

/-- **The ASCII phase's exit to the return.**  From the bound's arm's state, the
block's run and its arm, then the tail: the aligned document's byte arm or the
peel's silent merge.  The peel's own two windows are the last block's halves. -/
theorem s1BlocksAsciiExit_run {esc : Calls} (env : Env) (s : State) (c : AsciiCarry)
    (bs : List UInt8) (nb : Nat) (gate : Bool) (arm n andv : BitVec 64) (conv : BitVec 32)
    (h : AsciiInv env s c)
    (hread : readBytes c.mem c.b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hshr : c.shr = n >>> 6)
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hgateZero : arm &&& 2 = 0)
    (handEq : andv = n &&& 0x000000000000003f#64)
    (hbs63 : bs.length < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧
      1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8, ∃ p : Nat,
      readBytes s.mem p 1 = some [last] ∧ p = c.b + (n.signExtend 64).toNat - 1)
    (hsilent : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      lookupName (ifThen103Out (peelEntryEnv env c andv) v) "%or.cond191"
        = some (.int 1 1))
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstageByte : ∀ (last : UInt8),
      readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last] →
      VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0 |||
          lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction (asciiExitState env s c) =
        some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  have handE := lookupName_forIncEnv_of env c.i c.shr hand (by decide) (by decide)
  have hfind : s1BlocksFunction.findBlock (asciiExitState env s c).pc =
      some for_end101Block := by
    rw [show (asciiExitState env s c).pc = "for.end101" from rfl]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  have hrun101 : denoteCode s1BlocksCalls for_end101Instrs (asciiExitState env s c) =
      some (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
        (asciiExitState env s c)) :=
    asciiExit_denote env s c andv h hand
  have hbitCell : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%tobool102.not" = some (.int 1 (evalICmp .eq andv 0)) := by
    rw [forEnd101Out_eq]
    exact for_end101_tobool102_not env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
  have hnOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%n"
      = some (.int 64 n) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr hn (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hbOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%b"
      = some (.ptr c.b) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr h.base (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hascOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%ascii.1.lcssa" = some (.vec 4 64 (List.replicate 4 0)) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _
  have hu8kOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%u8k.1.lcssa" = some (.vec 4 64 (List.replicate 4 0)) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _
  have harmOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%arm"
      = some (.int 64 arm) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr harm (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  by_cases hbitAligned : evalICmp .eq andv 0 = 1
  · have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (asciiExitState env s c) =
        .jump (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
          { s with pc := "if.end153", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      exact asciiExit_step_aligned env s c andv h hand hbitAligned
    by_cases hnz : evalICmp .eq n 0 = 1
    · have htail := tail_aligned_run (esc := esc)
        (env := forEnd101Out (forIncEnv env c.i c.shr) c andv)
        { s with pc := "if.end153", pre := some "for.end101" } n
        (List.replicate 4 0) (List.replicate 4 0) bs nb gate rfl hnOut
        hu8kOut hascOut hnz hstage
      exact ⟨1 + 2, _, _, by
        rw [show (1 + 2 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix hstep1 2]
        exact (by simpa only [stateAt] using htail.1), htail.2⟩
    · have hnz0 : evalICmp .eq n 0 = 0 := by
        rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq n 0) with h0 | h1
        · exact h0
        · exact absurd h1 hnz
      obtain ⟨hposb, hpb⟩ := hnonzero hnz0
      obtain ⟨last, p, hp_read, hp_eq⟩ := hlast hnz0
      have htail := tail_byte_run (esc := esc)
        (env := forEnd101Out (forIncEnv env c.i c.shr) c andv)
        { s with pc := "if.end153", pre := some "for.end101" } n
        (List.replicate 4 0) (List.replicate 4 0) c.b last bs nb gate rfl hnOut
        hu8kOut hascOut hbOut hnz0 hposb hpb
        (by rw [← hp_eq]; exact hp_read)
        (hstageByte last (by rw [← hp_eq]; exact hp_read))
      exact ⟨1 + 3, _, _, by
        rw [show (1 + 3 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix hstep1 3]
        exact (by simpa only [stateAt] using htail.1), htail.2⟩
  · -- the peel
    have hbit : evalICmp .eq andv 0 = 0 := by
      rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq andv 0) with h0 | h1
      · exact h0
      · exact absurd h1 hbitAligned
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (asciiExitState env s c) =
        .jump (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
          { s with pc := "if.then103", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      exact asciiExit_step_peel env s c andv h hand hbit
    have hne : andv ≠ 0 := ne_zero_of_evalICmp_eq_zero andv hbit
    have hmod : n.toNat % 64 ≠ 0 := by
      intro h0
      apply hne
      apply BitVec.eq_of_toNat_eq
      rw [handEq, and_sixtythree_toNat, h0]
      rfl
    have hn63 : n.toNat < 2 ^ 63 := by rw [hbs]; exact hbs63
    have hshr63 : c.shr.toNat < 2 ^ 63 := by
      rw [hshr, ushr_six_toNat]
      omega
    have handv' : (n &&& 0xffffffffffffffc0#64).toNat = 64 * c.shr.toNat := by
      rw [and_high_mask_toNat, ← ushr_six_toNat, ← hshr]
    obtain ⟨h136, h137, hsucc⟩ :=
      for_end101_peel_last_block c.mem bs c.b n c hread hbs rfl hshr hmod
    have hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63 := by
      rw [signExtend_self_toNat, handv']
      have hle : 64 * c.shr.toNat ≤ n.toNat := by
        rw [hshr, ushr_six_toNat]
        have := Nat.div_mul_le_self n.toNat 64
        omega
      omega
    let A : State := stateAt (peelEntryEnv env c andv)
      { s with pc := "if.then103", pre := some "for.end101" }
    let v : IfThen103Values := ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1
    have hden := for_end101_peel_denote env s c n andv conv
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      h hn hconv hand hpos (by rw [h.mem]; exact h136) (by rw [h.mem]; exact h137)
      hshr63
    have hbn := hsilent v rfl
    have hstep2 : step (s1BlocksCallsEsc esc) s1BlocksFunction A =
        .jump (stateAt (ifThen103Out (peelEntryEnv env c andv) v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) := by
      have hfind103 : s1BlocksFunction.findBlock A.pc = some if_then103Block := by
        rw [show A.pc = "if.then103" from rfl]
        exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind103 (by decide)]
      exact if_then103_step_end147 _ A v rfl hbn (by
        rw [show A = stateAt (peelEntryEnv env c andv)
            { s with pc := "if.then103", pre := some "for.end101" } from rfl]
        exact hden)
    have htail := tail_silent_run (esc := esc) (env := peelEntryEnv env c andv)
      A v (List.replicate 4 0) arm bs bs.length nb gate
      (lookupName_ifThen103Out_u8k _ v (lookupName_peelEntryEnv_u8k env c andv))
      (lookupName_ifThen103Out_arm _ v (lookupName_peelEntryEnv_of env c andv harm
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)))
      (evalICmp_eq_zero_of_and_two_zero arm hgateZero)
      (hstagePeel v rfl)
    exact ⟨1 + (1 + 3), _, _, by
      rw [show (1 + (1 + 3) : Nat) = 1 + (1 + 3) from rfl,
        runFuel_jump_prefix hstep1 (1 + 3), runFuel_jump_prefix hstep2 3]
      exact (by simpa only [A, stateAt] using htail.1), htail.2⟩


/-! ### The post at the return

The tail's arms hand back the post's verdict clause (`VerdictPost`); the memory
clauses are the pieces `JsonS1BlocksRecordFrame` assembles.  The lemma below is
the junction: the post's own definition at the returned word, from the entry
array, the peel's arm's count, stream, carry and four-region frame, and the
caller's staged window. -/

/-- **`s1BlocksPost` at the return, on the gate's off arm.**  The peel's arm's
clauses (`peel_arm_memory`'s conclusion) are exactly the post's: the count slot
is the caller's, the stream's staged capacity is unchanged, the carry is the
all-false pair, the entry array is the model's, and the caller's window is the
one the pre staged. -/
theorem s1BlocksPost_of_peel {b ent xp nxp xcarry xn : Nat} {arm n r : BitVec 64}
    {bs : List UInt8} {mem m : Mem} {next : Nat}
    (hargs : (n : BitVec 64) = BitVec.ofNat 64 bs.length)
    (hwindow : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (hcountIn : readBytes mem nxp 8 = some (wordBytes 8 xn))
    (hverdict : VerdictPost r bs)
    (hent : readBytes m ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)))
    (hcount : readBytes m nxp 8 = some (wordBytes 8 xn))
    (hstream : readBytes m xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)) =
      readBytes mem xp (4 * (xn + 64 * blocksOf bs.length + batchReserve)))
    (hcarry : readBytes m xcarry 16 = some (flagBytes false ++ flagBytes false))
    (hframe : UnchangedOutside mem m
      [(ent, 8 * blocksOf bs.length), (xp, 4 * (xn + batchReserve)),
       (nxp, 8), (xcarry, 16)])
    (hgate : arm &&& 2 = (0 : BitVec 64)) :
    s1BlocksPost [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem next (.ret (some (.int 64 r)) m) := by
  unfold s1BlocksPost
  refine ⟨bs, xn, xn, [], hargs, hwindow, hcountIn, hverdict.1, hverdict.2.1,
    hverdict.2.2, hent, ?_, ?_, ?_⟩
  · intro _
    exact ⟨hcount, hstream, hcarry⟩
  · intro hne
    exact absurd hgate hne
  · exact hframe

/-- **The refinement the block unit owes its record.**  The statement the
composition above is aimed at; the residual pieces its proof still needs are
named in this module's documentation. -/
def s1_blocks_refines : Prop :=
  ∀ (esc : Calls) (base : Nat),
    escapeEntryAt esc base →
    ∀ (args : List Value) (mem : Mem) (next : Nat),
      s1BlocksPre args mem next →
      ∀ (o : Outcome),
        (∃ (n : Nat), runFuel (s1BlocksCallsEsc esc) n s1BlocksFunction
            (s1BlocksInit args mem) = some o) →
        s1BlocksPost args mem next o

/-! ### The entry's first step

The unit's run begins at `entry` with the seven ABI slots bound.  The block's
step is the phase's first link: the short document leaves for `if.end50`, the
rest for the ASCII preheader.  Both are stated at `s1BlocksCallsEsc esc`, since
`entry` makes no call. -/

theorem s1BlocksInit_pc (args : List Value) (mem : Mem) :
    (s1BlocksInit args mem).pc = "entry" := rfl

theorem s1BlocksInit_mem (args : List Value) (mem : Mem) :
    (s1BlocksInit args mem).mem = mem := rfl

/-- **The entry's step on a short document.** -/
theorem s1BlocksInit_step_short {esc : Calls} (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (hbit : evalICmp .ult n 64 = 1) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
          .ptr xcarry, .int 64 arm] mem) =
      .jump (stateAt
        (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv
          (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
            .ptr xcarry, .int 64 arm] mem).env n arm)
        { s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
            .ptr xcarry, .int 64 arm] mem with
          pc := "if.end50", pre := some "entry" }) := by
  have hfind : s1BlocksFunction.findBlock
      (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
        .ptr xcarry, .int 64 arm] mem).pc = some entryBlock :=
    LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_entry
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  exact entry_step_short
    (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env
    (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem) n arm rfl
    (s1BlocksInit_env_n mem b ent xp nxp xcarry n arm)
    (s1BlocksInit_env_arm mem b ent xp nxp xcarry n arm) hbit

/-- **The entry's step into the ASCII phase.** -/
theorem s1BlocksInit_step_blocks {esc : Calls} (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (hbit : evalICmp .ult n 64 = 0) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
          .ptr xcarry, .int 64 arm] mem) =
      .jump (stateAt
        (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv
          (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
            .ptr xcarry, .int 64 arm] mem).env n arm)
        { s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
            .ptr xcarry, .int 64 arm] mem with
          pc := "for.body.lr.ph", pre := some "entry" }) := by
  have hfind : s1BlocksFunction.findBlock
      (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
        .ptr xcarry, .int 64 arm] mem).pc = some entryBlock :=
    LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_entry
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  exact entry_step_blocks
    (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env
    (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem) n arm rfl
    (s1BlocksInit_env_n mem b ent xp nxp xcarry n arm)
    (s1BlocksInit_env_arm mem b ent xp nxp xcarry n arm) hbit

/-! ### Axiom footprints

The entry's lookups are the parameter list's cells; the tail arms and the two
exit compositions are the step lemmas' own equations composed by `runFuel`'s
prefix rule, so they carry the modules they consume: `propext`, `Classical.choice`
(the two-valued branch splits and the peel's value projections) and
`Quot.sound`.  No statement carries `sorryAx`. -/
#print axioms s1BlocksInit_env_n
#print axioms s1BlocksInit_env_b
#print axioms s1BlocksInit_step_short
#print axioms s1BlocksInit_step_blocks
#print axioms runFuel_one_ret
#print axioms runFuel_jump1_ret
#print axioms runFuel_jump2_ret
#print axioms runFuel_jump3_ret
#print axioms runFuel_jump4_ret
#print axioms tail_silent_run
#print axioms tail_escape_run
#print axioms tail_aligned_run
#print axioms tail_byte_run
#print axioms asciiExit_step_peel
#print axioms s1BlocksFusedExit_run
#print axioms s1BlocksAsciiExit_run
#print axioms s1BlocksPost_of_peel
#print axioms s1_blocks_refines

end LeanLLVM.Refinement.JsonS1BlocksRefines
