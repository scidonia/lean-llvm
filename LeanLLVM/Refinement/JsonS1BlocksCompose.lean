/-
The peeled tail's blocks, composed into the arm structure.

`JsonS1BlocksTail` traces the tail's four blocks at their own instruction lists
and stops at their terminators.  This module composes them: the accumulator merge
at `if.end147` is stated at each incoming arm's own state facts, the escape call at
`if.then150` is resolved at the caller's escape record and read through the
per-call frame, and the tail's model-side identities — the stored DFA word and the
two bits its arms hand `if.end170` — are stated in the contract's own vocabulary.

## The merge at `if.end147`

The merge's phi selects `%u8k.1.lcssa` on the peel's arm and `%or.i` on the partial
tail's.  Each arm's theorem takes the state the block itself leaves (the peel's
store in the memory, the partial tail's own environment) and the carried registers
the arm reads from its caller, and produces the merge's run and its two branch
steps.  The peel's `%u8k.1.lcssa` rides through the block untouched; the partial
tail's `%or.i` is the block's own accumulator join.

## The escape record at `if.then150`

The block's call is resolved at the caller's escape entry (`escapeEntryAt`), so
the outcome is the selection's and not the block's.  The record's `post` is
`escapePositionsPost`; its last clause is the per-call frame, restated once at the
block's three regions (`escapeReach_callRegions`).  The entry words the peel wrote
are outside that frame by the staging's separations, so the call cannot disturb
them (`escapeReach_keepsEntry`).  `escapeReach_of_post` is the bridge between the
post's existential and the record's own `EscapeReach` shape; it is where the
post's witnesses are identified with the block's argument vector.

## The tail's model-side identities

The stored DFA word: the peel masks its emitted word with the complement of the
all-ones shift at `%and`, and that complement is the model's `limMask` — the mask
`stage1Word` applies.  The store's bytes are the word in `wordsOf`'s spelling, so
the unit's entry-array clause reads them without a second encoding.

The two bits handed `if.end170`: the tail-byte arm's `%or169500` is the stage's own
`klTailByte` test (`lastByteBits_eq_utf8TailBit` with the verdict linkage's
`or169500_one_iff`), and the peeled arm's `%cmp155495` is the accumulator's
non-zero test (`ptestzU8k_icmp_eq_zero`).  The ASCII word the peeled arm hands is
`%or.i279`, whose probe is the ASCII predicate through
`asciiProbe_eq_one_iff_asciiBytes`.

## What remains, and is not here

**The peel arm's entry from `for.end101`.**  `JsonS1BlocksRefine` states the
merge's run at the ASCII phase's latch arm (`asciiExit_denote`) and both of that
arm's branches; the partial-block branch (`asciiExit_step_peel`) jumps to
`if.then103` at `forEnd101Out (forIncEnv env c.i c.shr) c andv`.  Two pieces of the
entry are still the loop's: (a) the `if.end98` arm — the fused loop's exit, whose
predecessor step is `if_end98_step_exit` but whose `for.end101` run is not stated,
so its seven phi selections (with `%u8k.1.lcssa = %u8k.2`) are unproved; and
(b) the tie from `forEnd101Out`'s seven cells to the peel's inputs: `%n` (the
caller's length), `%b`, `%ent`, `%shr = c.i`, the four carried words
(`%st.sroa.0/9/15` and `%prevS`), `%and` as the length's remainder, the merge's
`%u8k.1.lcssa`, and `%ascii.1.lcssa`/`%prev_ascii.1.lcssa`; and the peel's slot
must be the last one — `shr.toNat + 1 = blocksOf bs.length` with `bs136 ++ bs137`
the last block's two halves — which is what makes `%and` the model's `limMask`
argument at the last block and `%or135 &&& limMask` the last `stage1Word`.  None
of that is a fact about the peel block; it is the loop invariant's completion, and
the loop's step is `JsonS1BlocksRefine`'s.

**The record instance `s1_blocks_satisfies`.**  Its verdict conjuncts are
`VerdictStaging.satisfies_post`, so the record still owes
`VerdictStaging`'s three fields: `ascii_bytes` (the loop's `%ascii.1.lcssa` lane
OR is the document's high bits), `acc_pack` (`packLanes u8k = bytesToNat (klAll
gate bs)`, the fused loop's invariant) and `err_def` (this module's two bit
identities at the phi's arms).  Its memory conjuncts are the entry array
(the loop's prefix words plus this module's `if_then103_store_model` for the
peel's word), the escape stream and count (this module's `if_then150_escape_record`
and its frame), and the four-region `UnchangedOutside` — whose entry-array part is
`if_then150_escape_keepsEntry`.

The tail's blocks themselves are complete: every step above is a `step` equation
at the emitted function, with no hypothesis about the body that the block's own
instruction list does not supply.
-/
import LeanLLVM.Refinement.JsonS1BlocksTail
import LeanLLVM.Refinement.JsonS1BlocksVerdict
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonEscapeCallFrame

namespace LeanLLVM.Refinement.JsonS1BlocksCompose

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec (limMask limMask_getLsbD limMask_eq_allOnes
  shiftLeft_allOnes_getLsbD blocksOf)
open LeanLLVM.Refinement.JsonUtf8Steps (utf8TailBit)
open LeanLLVM.Refinement.JsonUtf8Spec (klTailByte)
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Reading the tail's environments

The tail's blocks build their environments with `cells`, so a register read is
resolved by unfolding the builder and peeling the cells the block bound.  The
names are literals, so each disequality is `decide`-able and no lookup asks
`isDefEq` to reduce an undecidable `if`.  The macro is the tail's own environment
list; every block below is one of them. -/
macro "tail_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only [ifThen103Out, ift103Env1,
        ift103Env2, ift103Env3, ift103Env4, ift103Env5, ift103Env6, ift103Env7,
        ift103Env8, ift103Env9, ift103Env10, ift103Env11, ift103Env12,
        ifThen144Out, ift144Env1, ift144Env2, ift144Env3, ift144Env4, ift144Env5,
        ift144Env6, ifThen150Env, ifThen164Env, ifEnd147Env, ifEnd153ThreadEnv,
        ifEnd170Env, cells]
      all_goals
        (repeat
          (first
           | exact lookupName_cons_self _ _ _
           | assumption
           | rfl
           | rw [lookupName_cons_ne _ _ (by decide)])))))

/-- `%u8k.1.lcssa` rides through the peeled block: the block does not bind it. -/
theorem lookupName_ifThen103Out_u8k (env : Env) (v : IfThen103Values)
    {u8k : List (BitVec 64)}
    (h : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k)) :
    lookupName (ifThen103Out env v) "%u8k.1.lcssa" = some (.vec 4 64 u8k) := by
  have hread : lookupName (ifThen103Out env v) "%u8k.1.lcssa" =
      lookupName env "%u8k.1.lcssa" := by tail_lk
  rw [hread, h]

/-- `%arm` rides through the peeled block. -/
theorem lookupName_ifThen103Out_arm (env : Env) (v : IfThen103Values)
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifThen103Out env v) "%arm" = some (.int 64 arm) := by
  have hread : lookupName (ifThen103Out env v) "%arm" = lookupName env "%arm" := by
    tail_lk
  rw [hread, h]

/-- `%136`: the peel's first window word. -/
theorem lookupName_ifThen103Out_136 (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%136" = some (.vec 4 64 v.w136) := by
  tail_lk

/-- `%137`: the peel's second window word. -/
theorem lookupName_ifThen103Out_137 (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%137" = some (.vec 4 64 v.w137) := by
  tail_lk

/-- `%or14.i391`: the peel's `0x5c` class word, the escape list's first argument. -/
theorem lookupName_ifThen103Out_or14 (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%or14.i391" = some (.int 64 v.mask391) := by
  tail_lk

/-- `%xor.i435`: the peel's in-string word, the escape list's third argument. -/
theorem lookupName_ifThen103Out_xor (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%xor.i435" = some (.int 64 v.xorI) := by
  tail_lk

/-- `%or.i279`: the peel's own ASCII join, the word `if.end170`'s ASCII phi reads
on the escape arm. -/
theorem lookupName_ifThen103Out_or279 (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%or.i279" = some (.vec 4 64 v.or279) := by
  tail_lk

/-- `%or.i`: the partial tail's accumulator join. -/
theorem lookupName_ifThen144Out_orI (env : Env) (v : IfThen144Values) :
    lookupName (ifThen144Out env v) "%or.i" = some (.vec 4 64 v.orI) := by
  tail_lk

/-- `%arm` rides through the partial tail. -/
theorem lookupName_ifThen144Out_arm (env : Env) (v : IfThen144Values)
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifThen144Out env v) "%arm" = some (.int 64 arm) := by
  have hread : lookupName (ifThen144Out env v) "%arm" = lookupName env "%arm" := by
    tail_lk
  rw [hread, h]

/-- A register read through the merge's three cells to the environment beneath
them. -/
theorem lookupName_ifEnd147Env_of (env : Env) (arm : BitVec 64)
    (u8k : List (BitVec 64)) {n : String} {v : Value}
    (h : lookupName env n = some v)
    (h1 : "%tobool149.not" ≠ n) (h2 : "%and148" ≠ n) (h3 : "%u8k.3" ≠ n) :
    lookupName (ifEnd147Env env arm u8k) n = some v := by
  simp only [ifEnd147Env, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3]
  exact h

/-- The merge's accumulator, as the merge leaves it. -/
theorem lookupName_ifEnd147Env_u8k3 (env : Env) (arm : BitVec 64)
    (u8k : List (BitVec 64)) :
    lookupName (ifEnd147Env env arm u8k) "%u8k.3" = some (.vec 4 64 u8k) := by
  tail_lk

/-- A register read through `if.then150`'s four cells to the environment beneath
them. -/
theorem lookupName_ifThen150Env_of (env : Env) (w136 w137 : List (BitVec 64))
    {n : String} {v : Value} (h : lookupName env n = some v)
    (h1 : "%or.i467" ≠ n) (h2 : "%198" ≠ n) (h3 : "%197" ≠ n) (h4 : "%196" ≠ n) :
    lookupName (ifThen150Env env w136 w137) n = some v := by
  simp only [ifThen150Env, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4]
  exact h

/-- A register read through `if.end153.thread`'s two cells to the environment
beneath them. -/
theorem lookupName_ifEnd153ThreadEnv_of (env : Env) (u8k : List (BitVec 64))
    {n : String} {v : Value} (h : lookupName env n = some v)
    (h1 : "%cmp155495" ≠ n) (h2 : "%199" ≠ n) :
    lookupName (ifEnd153ThreadEnv env u8k) n = some v := by
  simp only [ifEnd153ThreadEnv, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2]
  exact h

/-- The peeled arm's verdict bit, as `if.end153.thread` binds it. -/
theorem lookupName_ifEnd153ThreadEnv_cmp155495 (env : Env)
    (u8k : List (BitVec 64)) :
    lookupName (ifEnd153ThreadEnv env u8k) "%cmp155495" =
      some (.int 1 (evalICmp .eq (ptestzU8k u8k) 0)) := by
  tail_lk

/-! ### The `if.end147` phi merge

The merge's run at each incoming arm.  The peel's arm enters with the store in the
memory and its carried `%u8k.1.lcssa`; the partial tail's enters with its own
`%or.i`.  Both name the merge's phi selection explicitly. -/

/-- **The merge at the peel's arm.**  The phi selects `%u8k.1.lcssa`, which the
peel leaves at the caller's value, and the block's two instructions test the
carried `%arm`. -/
theorem if_end147_run_then103 (env : Env) (s : State) (v : IfThen103Values)
    (u8k : List (BitVec 64)) (arm : BitVec 64)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm)) :
    denoteCode s1BlocksCalls if_end147Instrs
      (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end147", pre := some "if.then103" }) =
    some (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
      { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
               pc := "if.end147", pre := some "if.then103" }) :=
  if_end147_denote (ifThen103Out env v)
    { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
             pc := "if.end147", pre := some "if.then103" }
    "if.then103" (.reg "%u8k.1.lcssa") arm u8k
    (lookupName_ifThen103Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen103Out_u8k env v hu8k))

/-- **The merge at the partial tail's arm.**  The phi selects `%or.i`, the block's
own accumulator join. -/
theorem if_end147_run_then144 (env : Env) (s : State) (v : IfThen144Values)
    (arm : BitVec 64) (harm : lookupName env "%arm" = some (.int 64 arm)) :
    denoteCode s1BlocksCalls if_end147Instrs
      (stateAt (ifThen144Out env v)
        { s with pc := "if.end147", pre := some "if.then144" }) =
    some (stateAt (ifEnd147Env (ifThen144Out env v) arm v.orI)
      { s with pc := "if.end147", pre := some "if.then144" }) :=
  if_end147_denote (ifThen144Out env v)
    { s with pc := "if.end147", pre := some "if.then144" }
    "if.then144" (.reg "%or.i") arm v.orI
    (lookupName_ifThen144Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen144Out_orI env v))

/-- **The merge's silent branch at the peel's arm.**  `%arm & 2 = 0`: the escape
gate is clear, so the merge goes straight to `if.end153.thread`. -/
theorem if_end147_step_then103_thread (env : Env) (s : State) (v : IfThen103Values)
    (u8k : List (BitVec 64)) (arm : BitVec 64)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 1) :
    step s1BlocksCalls s1BlocksFunction
      (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end147", pre := some "if.then103" }) =
    .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
      { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
               pc := "if.end153.thread", pre := some "if.end147" }) :=
  if_end147_step_thread (ifThen103Out env v)
    { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
             pc := "if.end147", pre := some "if.then103" }
    "if.then103" (.reg "%u8k.1.lcssa") arm u8k rfl
    (lookupName_ifThen103Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen103Out_u8k env v hu8k)) hbit

/-- **The merge's escape branch at the peel's arm.**  `%arm & 2 ≠ 0`: the peel's
masks selected the escape arm, so the merge goes to `if.then150`. -/
theorem if_end147_step_then103_escape (env : Env) (s : State) (v : IfThen103Values)
    (u8k : List (BitVec 64)) (arm : BitVec 64)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 0) :
    step s1BlocksCalls s1BlocksFunction
      (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end147", pre := some "if.then103" }) =
    .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
      { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
               pc := "if.then150", pre := some "if.end147" }) :=
  if_end147_step_escape (ifThen103Out env v)
    { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
             pc := "if.end147", pre := some "if.then103" }
    "if.then103" (.reg "%u8k.1.lcssa") arm u8k rfl
    (lookupName_ifThen103Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen103Out_u8k env v hu8k)) hbit

/-- **The merge's silent branch at the partial tail's arm.** -/
theorem if_end147_step_then144_thread (env : Env) (s : State) (v : IfThen144Values)
    (arm : BitVec 64) (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 1) :
    step s1BlocksCalls s1BlocksFunction
      (stateAt (ifThen144Out env v) { s with pc := "if.end147", pre := some "if.then144" }) =
    .jump (stateAt (ifEnd147Env (ifThen144Out env v) arm v.orI)
      { s with pc := "if.end153.thread", pre := some "if.end147" }) :=
  if_end147_step_thread (ifThen144Out env v)
    { s with pc := "if.end147", pre := some "if.then144" }
    "if.then144" (.reg "%or.i") arm v.orI rfl
    (lookupName_ifThen144Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen144Out_orI env v)) hbit

/-- **The merge's escape branch at the partial tail's arm.** -/
theorem if_end147_step_then144_escape (env : Env) (s : State) (v : IfThen144Values)
    (arm : BitVec 64) (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 0) :
    step s1BlocksCalls s1BlocksFunction
      (stateAt (ifThen144Out env v) { s with pc := "if.end147", pre := some "if.then144" }) =
    .jump (stateAt (ifEnd147Env (ifThen144Out env v) arm v.orI)
      { s with pc := "if.then150", pre := some "if.end147" }) :=
  if_end147_step_escape (ifThen144Out env v)
    { s with pc := "if.end147", pre := some "if.then144" }
    "if.then144" (.reg "%or.i") arm v.orI rfl
    (lookupName_ifThen144Out_arm env v harm) rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifThen144Out_orI env v)) hbit

/-! ### `if.then150`'s escape record

The block's call is the escape list's, and the unit leaves the callee unresolved:
the trace runs it at the caller's selection.  `escapeEntryAt` is that selection's
record, and its `post` is `escapePositionsPost`.  The record's clauses are read
back at the block's own argument vector: the outcome, the post, the cursor, the
frame at the block's three regions, and the count the next block reads.

The bridge is `escapeReach_of_post`: the post is an existential whose witnesses
are the call's arguments, and the block's argument vector pins the three
pointers, so the post's clauses are `EscapeReach`'s at the block's own numbers. -/

/-- **The per-call reach, at the unit's own argument list.**  The post's clauses,
read as `EscapeReach` at the caller's pointers.  The post's `position` is already
lifted by `blockAddr`; the reach's is the block's own list, which the theorem
recovers. -/
theorem escapeReach_of_post {base : Nat} {bs ctl im blk0 : BitVec 64}
    {xp xn carry : Nat} {mem M : Mem}
    (h : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn, .ptr carry]
      mem M) :
    ∃ (xn0 : Nat) (position : List Nat) (carryBytes : List UInt8),
      EscapeReach blk0 xp xn carry xn0 position carryBytes mem M := by
  obtain ⟨xp', xn', carry', blk0', bs', ctl', im', lo, hi, st, prevb, prevs, xn0,
    hargs, _hblock, _hbs, _hctl, _him, _hpairIn, _hcntIn, _hxn0, hcntOut, hposOut,
    hpairOut, hhasOut, hframeOut⟩ := h
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨_hbsE, _hctlE, _himE, hblkE, hxpE, hxnE, hcarryE⟩ := hargs
  subst hxpE; subst hxnE; subst hcarryE
  have hblkEq : blk0' = blk0 := (eq_of_heq hblkE).symm
  subst hblkEq
  refine ⟨xn0, escapePositionsFrom (block64 lo hi) st,
    flagBytes (IsBackslashB (hi ⟨31, by decide⟩)) ++ flagBytes (carry64 lo hi st).oddRun,
    ?_, ?_, hpairOut.1, hhasOut, ?_⟩
  · simpa using hcntOut
  · simpa [blockPositions] using hposOut
  · simpa [escapeRegions] using hframeOut

/-- **The per-call frame, at the unit's argument list.**  The three regions the
record is silent outside, with the stream at the run's touched count.  This is the
block's spelling of the frame: the same three numbers the block's own post names. -/
theorem escapePost_frame {base : Nat} {bs ctl im blk0 : BitVec 64}
    {xp xn carry : Nat} {mem M : Mem}
    (h : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn, .ptr carry]
      mem M) :
    ∃ (xn0 : Nat) (position : List Nat) (carryBytes : List UInt8),
      EscapeReach blk0 xp xn carry xn0 position carryBytes mem M ∧
      UnchangedOutside mem M
        (escapeCallRegions xp xn carry (xn0 + position.length)) := by
  obtain ⟨xn0, position, carryBytes, hreach⟩ := escapeReach_of_post h
  exact ⟨xn0, position, carryBytes, hreach, escapeReach_callRegions hreach⟩

/-- **The count the call leaves, at the word.**  The count's slot holds the
caller's count plus the block's position count.  The slot is eight bytes, so the
identity is the word's; a caller that needs the numeral also bounds the sum
(`wordBytes_eq_of_lt`). -/
theorem escapePost_count {base : Nat} {bs ctl im blk0 : BitVec 64}
    {xp xn carry : Nat} {mem M : Mem}
    (h : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn, .ptr carry]
      mem M) {count : Nat}
    (hread : readBytes M xn 8 = some (wordBytes 8 count)) :
    ∃ (xn0 : Nat) (position : List Nat),
      wordBytes 8 count = wordBytes 8 (xn0 + position.length) := by
  obtain ⟨xn0, position, carryBytes, hreach⟩ := escapeReach_of_post h
  exact ⟨xn0, position, Option.some.inj (hread.symm.trans hreach.1)⟩

/-- `if.then150`'s run at the escape-parametric environment: the block's five
instructions and the one call, whose outcome is the caller's selection's. -/
theorem if_then150_denote_esc (esc : Calls) (env : Env) (s : State)
    (w136 w137 : List (BitVec 64)) (h136 : w136.length = 4) (h137 : w137.length = 4)
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (h136v : lookupName env "%136" = some (.vec 4 64 w136))
    (h137v : lookupName env "%137" = some (.vec 4 64 w137))
    (hor : lookupName env "%or14.i391" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i435" = some (.int 64 xs))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : s1BlocksCallsEsc esc "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    denoteCode (s1BlocksCallsEsc esc) if_then150Instrs (stateAt env s) =
      some (stateAt (ifThen150Env env w136 w137)
        { s with mem := r.mem, next := r.next }) := by
  unfold if_then150Instrs ifThen150Env
  rw [denoteCode_shuffleVec (calls := s1BlocksCallsEsc esc) (env := env) (s := s)
    (d := "%196") (n := 4) (w := 64) (a := .reg "%136") (b := .reg "%137")
    (mask := [0, 1, 2, 3, 4, 5, 6, 7]) (l1 := w136) (l2 := w137)
    (ls := w136 ++ w137)
    (ha := evalOperand_reg_of env s "%136" (.vec 4 64 w136) h136v)
    (hb := evalOperand_reg_of env s "%137" (.vec 4 64 w137) h137v)
    (h1 := vecLanes_self h136) (h2 := vecLanes_self h137)
    (hm := mapM_pick8 h136 h137)]
  tail_eval

/-- **`if.then150`'s step at the escape-parametric environment.**  The join, the
masked count and the call; the call's outcome and its memory and cursor are the
selection's. -/
theorem if_then150_step_at (esc : Calls) (env : Env) (s : State)
    (w136 w137 : List (BitVec 64)) (h136 : w136.length = 4) (h137 : w137.length = 4)
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (hpc : s.pc = "if.then150")
    (h136v : lookupName env "%136" = some (.vec 4 64 w136))
    (h137v : lookupName env "%137" = some (.vec 4 64 w137))
    (hor : lookupName env "%or14.i391" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i435" = some (.int 64 xs))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : esc escapeListCallee
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThen150Env env w136 w137)
        { s with pc := "if.end153.thread", pre := some "if.then150",
                 mem := r.mem, next := r.next }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then150Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then150
  have hc' : s1BlocksCallsEsc esc "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r := by
    rw [show "leanllvm_json_escape_list" = escapeListCallee from rfl,
      s1BlocksCallsEsc_escape]
    exact hc
  rw [step_at hfind (if_then150_denote_esc esc env s w136 w137 h136 h137 or14 xs shr
    xp nxp xcarry r h136v h137v hor hxs hshr hxp hnxp hxcarry hc')]
  rw [show if_then150Block.term = if_then150Term from rfl]
  simp only [if_then150Term, execTerm]
  simp only [stateAt, hpc]

/-- **`if.then150`'s escape record.**  At the caller's escape entry and the
record's `pre` at the block's own argument vector, the call resolves, its `post`
holds, the per-call frame names the block's three regions, and the count's slot
holds the caller's count plus the block's position count.  The step is the
block's own, at the outcome the record selected. -/
theorem if_then150_escape_record {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base) (env : Env) (s : State)
    (w136 w137 : List (BitVec 64)) (h136 : w136.length = 4) (h137 : w137.length = 4)
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat)
    (hpc : s.pc = "if.then150")
    (h136v : lookupName env "%136" = some (.vec 4 64 w136))
    (h137v : lookupName env "%137" = some (.vec 4 64 w137))
    (hor : lookupName env "%or14.i391" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i435" = some (.int 64 xs))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hescPre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next) :
    ∃ (r : CallOutcome) (xn0 : Nat) (position : List Nat) (carryBytes : List UInt8),
      esc escapeListCallee
        [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
         .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r ∧
      escapePositionsPost base
        [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
         .ptr xp, .ptr nxp, .ptr xcarry] s.mem r.mem ∧
      EscapeReach shr xp nxp xcarry xn0 position carryBytes s.mem r.mem ∧
      s.next ≤ r.next ∧
      readBytes r.mem nxp 8 = some (wordBytes 8 (xn0 + position.length)) ∧
      UnchangedOutside s.mem r.mem
        (escapeCallRegions xp nxp xcarry (xn0 + position.length)) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (ifThen150Env env w136 w137)
          { s with pc := "if.end153.thread", pre := some "if.then150",
                   mem := r.mem, next := r.next }) := by
  obtain ⟨r, hcall, hpost, hnext⟩ := escapeEntry_call hEsc hescPre
  obtain ⟨xn0, position, carryBytes, hreach⟩ := escapeReach_of_post hpost
  exact ⟨r, xn0, position, carryBytes, hcall, hpost, hreach, hnext, hreach.1,
    escapeReach_callRegions hreach,
    if_then150_step_at esc env s w136 w137 h136 h137 or14 xs shr xp nxp xcarry r
      hpc h136v h137v hor hxs hshr hxp hnxp hxcarry hcall⟩

/-- **The escape call leaves the peel's entry words alone.**  The record's frame is
silent outside its three regions; a caller that separates the entry array from
each of them (at the frame's own stream extent) reads the array back unchanged
after the call.  The separations are the staging's, not the record's:
`Γ_escape_positions.pre` has no argument for the entry array. -/
theorem if_then150_escape_keepsEntry {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base) (s : State)
    (w136 w137 : List (BitVec 64))
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat)
    (hescPre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next) :
    ∃ (r : CallOutcome) (xn0 : Nat) (position : List Nat),
      esc escapeListCallee
        [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
         .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r ∧
      s.next ≤ r.next ∧
      ∀ (ent blocks : Nat),
        (ent + 8 * blocks ≤ xp ∨
          xp + 4 * (xn0 + position.length + batchReserve) ≤ ent) →
        (ent + 8 * blocks ≤ nxp ∨ nxp + 8 ≤ ent) →
        (ent + 8 * blocks ≤ xcarry ∨ xcarry + 16 ≤ ent) →
        readBytes r.mem ent (8 * blocks) = readBytes s.mem ent (8 * blocks) := by
  obtain ⟨r, hcall, hpost, hnext⟩ := escapeEntry_call hEsc hescPre
  obtain ⟨xn0, position, carryBytes, hreach⟩ := escapeReach_of_post hpost
  exact ⟨r, xn0, position, hcall, hnext,
    fun ent blocks hxp hxn hcarry => escapeReach_keepsEntry hreach hxp hxn hcarry⟩

/-! ### The tail's model-side identities

The stored DFA word and the two bits the tail's arms hand `if.end170`.  Each is
stated at the tail's own values and read in the contract's vocabulary. -/

/-- **The tail block's byte test is the stage's own bit.**  The mask drops the low
bit and the compare is the stage's unsigned order against `0xf4`. -/
theorem lastByteBits_eq_utf8TailBit (last : BitVec 8) :
    lastByteBits last = utf8TailBit last := by
  unfold lastByteBits utf8TailBit evalICmp
  rw [show (0xf4#8 : BitVec 8) = BitVec.ofNat 8 244 from rfl,
    show (BitVec.ofInt 8 (-12) : BitVec 8) = BitVec.ofNat 8 244 from by decide,
    show (BitVec.ofInt 8 (-2) : BitVec 8) = BitVec.ofNat 8 254 from by decide,
    show (BitVec.ofInt 8 (-64) : BitVec 8) = BitVec.ofNat 8 192 from by decide,
    show (0xfe#8 : BitVec 8) = BitVec.ofNat 8 254 from rfl,
    show (0xc0#8 : BitVec 8) = BitVec.ofNat 8 192 from rfl]

/-- **The peel's clamp is the model's.**  The complement of the all-ones shift at
the block's remaining bytes is `limMask`, the mask `stage1Word` applies. -/
theorem not_shiftLeft_allOnes_eq_limMask (k : Nat) :
    ~~~ (BitVec.allOnes 64 <<< k) = limMask k := by
  by_cases hk : k < 64
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [getLsbD_not_of_lt _ hj,
      show (BitVec.allOnes 64 : BitVec 64) = BitVec.ofInt 64 (-1) from by decide,
      shiftLeft_allOnes_getLsbD hj, limMask_getLsbD k j (by omega) hj]
    by_cases hjk : k ≤ j
    · rw [decide_eq_true hjk, decide_eq_false (by omega)]
      rfl
    · rw [decide_eq_false hjk, decide_eq_true (by omega)]
      rfl
  · rw [limMask_eq_allOnes (by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hshift : (BitVec.allOnes 64 <<< k).getLsbD j = false := by
      rw [show (BitVec.allOnes 64 : BitVec 64) = BitVec.ofInt 64 (-1) from by decide,
        shiftLeft_allOnes_getLsbD hj, decide_eq_false (by omega)]
    rw [getLsbD_not_of_lt _ hj, hshift,
      show (BitVec.ofInt 64 (-1) : BitVec 64) = BitVec.allOnes 64 from by decide,
      allOnes_getLsbD_of_lt hj]
    rfl

/-- **The peel's clamp mask.**  `%sub` is the model's `limMask` at `%and`, the
block's remaining bytes. -/
theorem ifThen103Values_sub_eq_limMask (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).sub = limMask andv.toNat := by
  show ((0xffffffffffffffff#64 : BitVec 64) <<< andv.toNat) ^^^
      (0xffffffffffffffff#64 : BitVec 64) = limMask andv.toNat
  rw [show (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
    BitVec.xor_allOnes]
  exact not_shiftLeft_allOnes_eq_limMask _

/-- **The stored DFA word is the peel's word at the model's clamp.**  `%and137`
is `%or135` masked with the model's `limMask`; that is the shape `stage1Word`
gives the entry word. -/
theorem ifThen103Values_and137_eq (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).and137 =
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 &&& limMask andv.toNat := by
  rw [show (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
        conv prevAscii).and137 =
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 &&&
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).sub from rfl,
    ifThen103Values_sub_eq_limMask]

/-- **The peel's store slot.**  The block writes at `ent + shr * 8`, the entry
array's slot for index `shr`. -/
theorem ifThen103Values_arrayidx (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).arrayidx = ent + shr.toNat * 8 := by
  show ent + (shr.signExtend 64).toNat * (Ty.int 64).sizeBytes = ent + shr.toNat * 8
  rw [show (Ty.int 64).sizeBytes = 8 from by decide,
    show (shr.signExtend 64).toNat = shr.toNat from by simp [BitVec.signExtend]]

/-- **The stored word, in the post's spelling.**  The peel's store writes
`natToBytes v.and137.toNat 8`, which is `wordsOf [v.and137]`; the slot reads back
as that word. -/
theorem if_then103_store_word (mem : Mem) (v : IfThen103Values) :
    readBytes
      (writeBytes mem v.arrayidx (natToBytes v.and137.toNat 8)) v.arrayidx 8 =
      some (wordsOf [v.and137]) := by
  have h := readBytes_writeBytes_same mem (wordsOf [v.and137]) (addr := v.arrayidx)
  rw [show (wordsOf [v.and137]).length = 8 from by
    simp [wordsOf, natToBytes_length]] at h
  simpa [wordsOf] using h

/-- **The tail-byte arm's bit against the stage's table rule.**  `%or169500`'s
byte summand is `utf8TailBit`, so the verdict linkage's `or169500_one_iff` reads
it as `klTailByte`. -/
theorem or169500_tailbit_one_iff (err : BitVec 1) (x : UInt8) :
    (err ||| lastByteBits x.toBitVec) = 1 ↔ err = 1 ∨ klTailByte x = true := by
  rw [lastByteBits_eq_utf8TailBit, bit1_or_eq_one, utf8TailBit_one_iff]

/-- The block's own `%or169500`, as `if.then164` binds it. -/
theorem ifThen164Env_or169500 (env : Env) (p : Nat) (last : BitVec 8)
    (err : BitVec 1) :
    lookupName (ifThen164Env env p last err) "%or169500" =
      some (.int 1 (err ||| lastByteBits last)) := by
  tail_lk

/-- **The accumulator's bit, as the peeled arm hands it.**  `%cmp155495` is
`ptestz u8k u8k = 0`, which is the accumulator's non-zero test — the verdict
linkage's `ptestzU8k_icmp_eq_zero` at the merge's own `%u8k.3`. -/
theorem ifEnd153ThreadEnv_cmp155495_one_iff (u8k : List (BitVec 64))
    (hu : u8k.length = 4) :
    evalICmp .eq (ptestzU8k u8k) 0 = 1 ↔
      ¬ (u8k.all (fun x => decide (x = 0x00)) = true) :=
  ptestzU8k_icmp_eq_zero u8k hu

/-- **The ASCII word the peeled arm hands.**  `%or.i279` is the peel's join of its
two window words into the ASCII accumulator; its probe is the ASCII predicate
through the verdict linkage's `asciiProbe_eq_one_iff_asciiBytes`. -/
theorem asciiProbe_or279 (or280 ascii : List (BitVec 64))
    (h280 : or280.length = 4) (ha : ascii.length = 4) :
    asciiProbe (List.zipWith (fun x y => x ||| y) or280 ascii) = 1 ↔
      ∀ b ∈ asciiBytes (List.zipWith (fun x y => x ||| y) or280 ascii),
        b.toNat < 0x80 :=
  asciiProbe_eq_one_iff_asciiBytes _ (by simp [List.length_zipWith, h280, ha])

/-- **The stored DFA word, composed.**  The peel's store writes the model's
clamped word — `%or135 &&& limMask` at `%and` — and the slot is `ent + shr * 8`. -/
theorem if_then103_store_model (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) (mem : Mem) :
    readBytes
      (writeBytes mem
        (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
          prevAscii).arrayidx
        (natToBytes
          (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
            prevAscii).and137.toNat 8))
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).arrayidx 8 =
      some (wordsOf
        [(ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
            prevAscii).or135 &&& limMask andv.toNat]) := by
  rw [ifThen103Values_and137_eq]
  have h := if_then103_store_word mem
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv prevAscii)
  rw [ifThen103Values_and137_eq] at h
  exact h

/-! ### The arm structure

The tail's two arms from the merge: the silent one goes straight to
`if.end153.thread`, the escape one runs the list first, and both reach
`if.end170` with the peel's ASCII word and the merge's accumulator.  The last
step is the verdict linkage's own, at the two bits the tail hands. -/

/-- `%shr` rides through the peeled block. -/
theorem lookupName_ifThen103Out_shr (env : Env) (v : IfThen103Values)
    {shr : BitVec 64} (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (ifThen103Out env v) "%shr" = some (.int 64 shr) := by
  have hread : lookupName (ifThen103Out env v) "%shr" = lookupName env "%shr" := by
    tail_lk
  rw [hread, h]

/-- `%xp` rides through the peeled block. -/
theorem lookupName_ifThen103Out_xp (env : Env) (v : IfThen103Values)
    {xp : Nat} (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (ifThen103Out env v) "%xp" = some (.ptr xp) := by
  have hread : lookupName (ifThen103Out env v) "%xp" = lookupName env "%xp" := by
    tail_lk
  rw [hread, h]

/-- `%nxp` rides through the peeled block. -/
theorem lookupName_ifThen103Out_nxp (env : Env) (v : IfThen103Values)
    {nxp : Nat} (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (ifThen103Out env v) "%nxp" = some (.ptr nxp) := by
  have hread : lookupName (ifThen103Out env v) "%nxp" = lookupName env "%nxp" := by
    tail_lk
  rw [hread, h]

/-- `%xcarry` rides through the peeled block. -/
theorem lookupName_ifThen103Out_xcarry (env : Env) (v : IfThen103Values)
    {xcarry : Nat} (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (ifThen103Out env v) "%xcarry" = some (.ptr xcarry) := by
  have hread : lookupName (ifThen103Out env v) "%xcarry" = lookupName env "%xcarry" := by
    tail_lk
  rw [hread, h]

/-- **`if.then150` from the merge's escape branch.**  The merge hands the block
its own environment; the block reads the peel's two words, its `0x5c` word and its
in-string word, plus the caller's `%shr` and pointers, and calls the list at the
record's selection. -/
theorem if_then150_step_after_merge_escape {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base) (env : Env) (s : State) (v : IfThen103Values)
    (u8k : List (BitVec 64)) (arm shr : BitVec 64) (xp nxp xcarry : Nat)
    (h136 : v.w136.length = 4) (h137 : v.w137.length = 4)
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hescPre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 v.mask391, .int 64 (ifThen150QuoteWord v.w136 v.w137), .int 64 v.xorI,
       .int 64 shr, .ptr xp, .ptr nxp, .ptr xcarry]
      (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) s.next) :
    ∃ (r : CallOutcome) (xn0 : Nat) (position : List Nat) (carryBytes : List UInt8),
      esc escapeListCallee
        [.int 64 v.mask391, .int 64 (ifThen150QuoteWord v.w136 v.w137), .int 64 v.xorI,
         .int 64 shr, .ptr xp, .ptr nxp, .ptr xcarry]
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) s.next = some r ∧
      EscapeReach shr xp nxp xcarry xn0 position carryBytes
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) r.mem ∧
      s.next ≤ r.next ∧
      UnchangedOutside
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) r.mem
        (escapeCallRegions xp nxp xcarry (xn0 + position.length)) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction
        (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.then150", pre := some "if.end147" }) =
        .jump (stateAt (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k)
            v.w136 v.w137)
          { s with mem := r.mem, next := r.next,
                   pc := "if.end153.thread", pre := some "if.then150" }) := by
  have h136v : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%136" =
      some (.vec 4 64 v.w136) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_136 env v)
      (by decide) (by decide) (by decide)
  have h137v : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%137" =
      some (.vec 4 64 v.w137) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_137 env v)
      (by decide) (by decide) (by decide)
  have hor : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%or14.i391" =
      some (.int 64 v.mask391) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_or14 env v)
      (by decide) (by decide) (by decide)
  have hxs : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%xor.i435" =
      some (.int 64 v.xorI) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_xor env v)
      (by decide) (by decide) (by decide)
  have hshrv : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%shr" =
      some (.int 64 shr) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_shr env v hshr)
      (by decide) (by decide) (by decide)
  have hxpv : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%xp" =
      some (.ptr xp) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_xp env v hxp)
      (by decide) (by decide) (by decide)
  have hnxpv : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%nxp" =
      some (.ptr nxp) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_nxp env v hnxp)
      (by decide) (by decide) (by decide)
  have hxcarryv : lookupName (ifEnd147Env (ifThen103Out env v) arm u8k) "%xcarry" =
      some (.ptr xcarry) :=
    lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_xcarry env v hxcarry)
      (by decide) (by decide) (by decide)
  obtain ⟨r, xn0, position, carryBytes, hcall, _hpost, hreach, hnext, _hcount,
    hframe, hstep⟩ :=
    if_then150_escape_record hEsc (ifEnd147Env (ifThen103Out env v) arm u8k)
      { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
               pc := "if.then150", pre := some "if.end147" }
      v.w136 v.w137 h136 h137 v.mask391 v.xorI shr xp nxp xcarry rfl
      h136v h137v hor hxs hshrv hxpv hnxpv hxcarryv hescPre
  exact ⟨r, xn0, position, carryBytes, hcall, hreach, hnext, hframe, hstep⟩

/-- **The verdict at the peeled arm.**  `if.end170`'s two phis select
`%or.i279` and `%cmp155495`, and the verdict linkage's staged post follows. -/
theorem if_end170_step_of_thread (env : Env) (s : State)
    (ascii u8k : List (BitVec 64)) (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (err : BitVec 1)
    (hpc : s.pc = "if.end170") (hpre : s.pre = some "if.end153.thread")
    (hasc : lookupName env "%or.i279" = some (.vec 4 64 ascii))
    (herr : lookupName env "%cmp155495" = some (.int 1 err))
    (hstage : VerdictStaging ascii u8k bs n nb gate err) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
        .ret (some (.int 64 (verdictWord ascii err)))
          (stateAt (ifEnd170Env env ascii err) s) ∧
      VerdictPost (verdictWord ascii err) bs :=
  if_end170_step_verdict env s "if.end153.thread" (.reg "%or.i279")
    (.reg "%cmp155495") ascii u8k err bs n nb gate hpc hpre (by rfl)
    (evalOperand_reg_of _ _ _ _ hasc) (by rfl)
    (evalOperand_reg_of _ _ _ _ herr) hstage

/-- **The verdict at the tail-byte arm.**  `if.end170`'s two phis select
`%ascii.1.lcssa` and `%or169500`, the block's own `err` joined with the last
byte's test. -/
theorem if_end170_step_of_then164 (env : Env) (s : State)
    (ascii u8k : List (BitVec 64)) (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (err : BitVec 1)
    (hpc : s.pc = "if.end170") (hpre : s.pre = some "if.then164")
    (hasc : lookupName env "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (herr : lookupName env "%or169500" = some (.int 1 err))
    (hstage : VerdictStaging ascii u8k bs n nb gate err) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
        .ret (some (.int 64 (verdictWord ascii err)))
          (stateAt (ifEnd170Env env ascii err) s) ∧
      VerdictPost (verdictWord ascii err) bs :=
  if_end170_step_verdict env s "if.then164" (.reg "%ascii.1.lcssa")
    (.reg "%or169500") ascii u8k err bs n nb gate hpc hpre (by rfl)
    (evalOperand_reg_of _ _ _ _ hasc) (by rfl)
    (evalOperand_reg_of _ _ _ _ herr) hstage

/-- The thread block's step at the escape-parametric environment, where its
instructions call no escape list. -/
theorem if_end153_thread_step_esc (esc : Calls) (env : Env) (s : State)
    (u8k : List (BitVec 64)) (hpc : s.pc = "if.end153.thread")
    (hu : lookupName env "%u8k.3" = some (.vec 4 64 u8k)) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153ThreadEnv env u8k)
        { s with pc := "if.end170", pre := some "if.end153.thread" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc =
      some if_end153_threadBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153_thread
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  exact if_end153_thread_step env s u8k hpc hu

/-- The return block's step at the escape-parametric environment. -/
theorem if_end170_step_esc (esc : Calls) (env : Env) (s : State)
    (p : String) (op1 op2 : Operand) (ascii u8k : List (BitVec 64))
    (bs : List UInt8) (n nb : Nat) (gate : Bool) (err : BitVec 1)
    (hpc : s.pc = "if.end170") (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("if.then164", .reg "%ascii.1.lcssa"),
      ("if.end153", .reg "%ascii.1.lcssa"),
      ("if.end153.thread", .reg "%or.i279")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.vec 4 64 ascii))
    (hinc2 : phiIncoming p [("if.then164", .reg "%or169500"),
      ("if.end153", .reg "%cmp155"),
      ("if.end153.thread", .reg "%cmp155495")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 1 err))
    (hstage : VerdictStaging ascii u8k bs n nb gate err) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .ret (some (.int 64 (verdictWord ascii err)))
          (stateAt (ifEnd170Env env ascii err) s) ∧
      VerdictPost (verdictWord ascii err) bs := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end170Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end170
  rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
  exact if_end170_step_verdict env s p op1 op2 ascii u8k err bs n nb gate
    hpc hpre hinc1 hop1 hinc2 hop2 hstage

/-- **The peeled arm's silent path.**  From the merge's silent branch: the merge
hands `%u8k.3` to `if.end153.thread`, which zero-tests it, and `if.end170`
returns the peel's ASCII word joined with that test. -/
theorem tail_silent_path {esc : Calls} (env : Env) (s : State)
    (v : IfThen103Values) (u8k : List (BitVec 64)) (arm : BitVec 64)
    (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hu8k : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 1)
    (hstage : VerdictStaging v.or279 u8k bs n nb gate
      (evalICmp .eq (ptestzU8k u8k) 0)) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (stateAt (ifThen103Out env v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) =
      .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end153.thread", pre := some "if.end147" }) ∧
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end153.thread", pre := some "if.end147" }) =
      .jump (stateAt (ifEnd153ThreadEnv (ifEnd147Env (ifThen103Out env v) arm u8k) u8k)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end170", pre := some "if.end153.thread" }) ∧
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (stateAt (ifEnd153ThreadEnv (ifEnd147Env (ifThen103Out env v) arm u8k) u8k)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end170", pre := some "if.end153.thread" }) =
      .ret (some (.int 64 (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0))))
        (stateAt
          (ifEnd170Env
            (ifEnd153ThreadEnv (ifEnd147Env (ifThen103Out env v) arm u8k) u8k)
            v.or279 (evalICmp .eq (ptestzU8k u8k) 0))
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end170", pre := some "if.end153.thread" }) ∧
    VerdictPost (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0)) bs := by
  have hstep := if_end147_step_then103_thread env s v u8k arm hu8k harm hbit
  have hstep' : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end147", pre := some "if.then103" }) =
      .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end153.thread", pre := some "if.end147" }) := by
    rw [step_esc_of_free esc s1BlocksFunction _ if_end147Block
      (LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end147) (by decide)]
    exact hstep
  have hthread := if_end153_thread_step_esc esc
    (ifEnd147Env (ifThen103Out env v) arm u8k)
    { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
             pc := "if.end153.thread", pre := some "if.end147" } u8k rfl
    (lookupName_ifEnd147Env_u8k3 _ _ _)
  have hreturn := (if_end170_step_esc esc
    (ifEnd153ThreadEnv (ifEnd147Env (ifThen103Out env v) arm u8k) u8k)
    { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
             pc := "if.end170", pre := some "if.end153.thread" }
    "if.end153.thread" (.reg "%or.i279") (.reg "%cmp155495") v.or279 u8k bs n nb
    gate (evalICmp .eq (ptestzU8k u8k) 0) rfl rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ (lookupName_ifEnd153ThreadEnv_of _ _
      (lookupName_ifEnd147Env_of _ _ _ (lookupName_ifThen103Out_or279 env v)
        (by decide) (by decide) (by decide)) (by decide) (by decide)))
    (by rfl)
    (evalOperand_reg_of _ _ _ _
      (lookupName_ifEnd153ThreadEnv_cmp155495 _ _)) hstage)
  exact ⟨hstep', hthread, hreturn.1, hreturn.2⟩

/-- **The peeled arm's escape path.**  From the merge's escape branch: the escape
list runs at the record's selection, and `if.end153.thread` and `if.end170` then
return the peel's ASCII word joined with the merge's accumulator test.  The
record's per-call frame is the `UnchangedOutside` conjunct; the entry words it
keeps are `escapeReach_keepsEntry`'s, at the caller's separations. -/
theorem tail_escape_path {esc : Calls} {base : Nat} (hEsc : escapeEntryAt esc base)
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
      EscapeReach shr xp nxp xcarry xn0 position carryBytes
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) r.mem ∧
      s.next ≤ r.next ∧
      UnchangedOutside
        (writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8)) r.mem
        (escapeCallRegions xp nxp xcarry (xn0 + position.length)) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction
          (stateAt (ifThen103Out env v)
            { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                     pc := "if.end147", pre := some "if.then103" }) =
        .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.then150", pre := some "if.end147" }) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction
          (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
            { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                     pc := "if.then150", pre := some "if.end147" }) =
        .jump (stateAt (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k)
            v.w136 v.w137)
          { s with mem := r.mem, next := r.next,
                   pc := "if.end153.thread", pre := some "if.then150" }) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction
          (stateAt
            (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137)
            { s with mem := r.mem, next := r.next,
                     pc := "if.end153.thread", pre := some "if.then150" }) =
        .jump (stateAt
          (ifEnd153ThreadEnv
            (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137)
            u8k)
          { s with mem := r.mem, next := r.next,
                   pc := "if.end170", pre := some "if.end153.thread" }) ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction
          (stateAt
            (ifEnd153ThreadEnv
              (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137)
              u8k)
            { s with mem := r.mem, next := r.next,
                     pc := "if.end170", pre := some "if.end153.thread" }) =
        .ret (some (.int 64 (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0))))
          (stateAt
            (ifEnd170Env
              (ifEnd153ThreadEnv
                (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k)
                  v.w136 v.w137) u8k)
              v.or279 (evalICmp .eq (ptestzU8k u8k) 0))
            { s with mem := r.mem, next := r.next,
                     pc := "if.end170", pre := some "if.end153.thread" }) ∧
      VerdictPost (verdictWord v.or279 (evalICmp .eq (ptestzU8k u8k) 0)) bs := by
  obtain ⟨r, xn0, position, carryBytes, hcall, hreach, hnext, hframe, hstep150⟩ :=
    if_then150_step_after_merge_escape hEsc env s v u8k arm shr xp nxp xcarry
      h136 h137 hshr hxp hnxp hxcarry hescPre
  have hmerge : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.end147", pre := some "if.then103" }) =
      .jump (stateAt (ifEnd147Env (ifThen103Out env v) arm u8k)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                 pc := "if.then150", pre := some "if.end147" }) := by
    rw [step_esc_of_free esc s1BlocksFunction _ if_end147Block
      (LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end147) (by decide)]
    exact if_end147_step_then103_escape env s v u8k arm hu8k harm hbit
  have hthread : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt
        (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137)
        { s with mem := r.mem, next := r.next,
                 pc := "if.end153.thread", pre := some "if.then150" }) =
      .jump (stateAt
        (ifEnd153ThreadEnv
          (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137)
          u8k)
        { s with mem := r.mem, next := r.next,
                 pc := "if.end170", pre := some "if.end153.thread" }) :=
    if_end153_thread_step_esc esc _
      { s with mem := r.mem, next := r.next,
               pc := "if.end153.thread", pre := some "if.then150" } u8k rfl
      (lookupName_ifThen150Env_of _ _ _
        (lookupName_ifEnd147Env_u8k3 _ _ _) (by decide) (by decide) (by decide)
        (by decide))
  have hreturn := (if_end170_step_esc esc
    (ifEnd153ThreadEnv
      (ifThen150Env (ifEnd147Env (ifThen103Out env v) arm u8k) v.w136 v.w137) u8k)
    { s with mem := r.mem, next := r.next,
             pc := "if.end170", pre := some "if.end153.thread" }
    "if.end153.thread" (.reg "%or.i279") (.reg "%cmp155495") v.or279 u8k bs n nb
    gate (evalICmp .eq (ptestzU8k u8k) 0) rfl rfl (by rfl)
    (evalOperand_reg_of _ _ _ _
      (lookupName_ifEnd153ThreadEnv_of _ _
        (lookupName_ifThen150Env_of _ _ _
          (lookupName_ifEnd147Env_of _ _ _
            (lookupName_ifThen103Out_or279 env v) (by decide) (by decide) (by decide))
          (by decide) (by decide) (by decide) (by decide))
        (by decide) (by decide)))
    (by rfl)
    (evalOperand_reg_of _ _ _ _
      (lookupName_ifEnd153ThreadEnv_cmp155495 _ _)) hstage)
  exact ⟨r, xn0, position, carryBytes, hcall, hreach, hnext, hframe, hmerge,
    hstep150, hthread, hreturn.1, hreturn.2⟩

/-- **The tail-byte arm's path.**  `if.then164` reads the document's last byte and
folds its two tests into the peel's `%cmp155`; `if.end170` then returns the
accumulated ASCII word joined with that sum.  This is the arm the aligned exit
takes, and its bit is the `%or169500` the verdict linkage reads. -/
theorem tail_byte_arm_verdict {esc : Calls} (env : Env) (s : State)
    (ascii u8k : List (BitVec 64)) (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (last : UInt8) (err : BitVec 1) (bn : Nat) (bl : BitVec 64)
    (hpc : s.pc = "if.then164")
    (hn : lookupName env "%n" = some (.int 64 bl))
    (hb : lookupName env "%b" = some (.ptr bn))
    (herr : lookupName env "%cmp155" = some (.int 1 err))
    (hpos : (bl.signExtend 64).toNat < 2 ^ 63)
    (hp : 1 ≤ bn + (bl.signExtend 64).toNat)
    (hr : readBytes s.mem (bn + (bl.signExtend 64).toNat - 1) 1 = some [last])
    (hasc : lookupName
      (ifThen164Env env (bn + (bl.signExtend 64).toNat)
        (BitVec.ofNat 8 last.toNat) err) "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (hstage : VerdictStaging ascii u8k bs n nb gate
      (err ||| lastByteBits (BitVec.ofNat 8 last.toNat))) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt
        (ifThen164Env env (bn + (bl.signExtend 64).toNat)
          (BitVec.ofNat 8 last.toNat) err)
        { s with pc := "if.end170", pre := some "if.then164" }) ∧
    step (s1BlocksCallsEsc esc) s1BlocksFunction
        (stateAt
          (ifThen164Env env (bn + (bl.signExtend 64).toNat)
            (BitVec.ofNat 8 last.toNat) err)
          { s with pc := "if.end170", pre := some "if.then164" }) =
      .ret (some (.int 64
        (verdictWord ascii (err ||| lastByteBits (BitVec.ofNat 8 last.toNat)))))
        (stateAt
          (ifEnd170Env
            (ifThen164Env env (bn + (bl.signExtend 64).toNat)
              (BitVec.ofNat 8 last.toNat) err)
            ascii (err ||| lastByteBits (BitVec.ofNat 8 last.toNat)))
          { s with pc := "if.end170", pre := some "if.then164" }) ∧
    VerdictPost
      (verdictWord ascii (err ||| lastByteBits (BitVec.ofNat 8 last.toNat))) bs := by
  have hstep : step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt
        (ifThen164Env env (bn + (bl.signExtend 64).toNat)
          (BitVec.ofNat 8 last.toNat) err)
        { s with pc := "if.end170", pre := some "if.then164" }) :=
    if_then164_step env s bl bn last err hpc hn hb herr hpos hp hr
  have hstep' : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt
        (ifThen164Env env (bn + (bl.signExtend 64).toNat)
          (BitVec.ofNat 8 last.toNat) err)
        { s with pc := "if.end170", pre := some "if.then164" }) := by
    have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then164Block := by
      rw [show (stateAt env s).pc = s.pc from rfl, hpc]
      exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then164
    rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
    exact hstep
  have hreturn := (if_end170_step_esc esc
    (ifThen164Env env (bn + (bl.signExtend 64).toNat)
      (BitVec.ofNat 8 last.toNat) err)
    { s with pc := "if.end170", pre := some "if.then164" }
    "if.then164" (.reg "%ascii.1.lcssa") (.reg "%or169500") ascii u8k bs n nb gate
    (err ||| lastByteBits (BitVec.ofNat 8 last.toNat)) rfl rfl (by rfl)
    (evalOperand_reg_of _ _ _ _ hasc) (by rfl)
    (evalOperand_reg_of _ _ _ _
      (ifThen164Env_or169500 env (bn + (bl.signExtend 64).toNat)
        (BitVec.ofNat 8 last.toNat) err)) hstage)
  exact ⟨hstep', hreturn.1, hreturn.2⟩

/-! ### Footprint

The merge, the escape record, the two bit readings and the two peeled-arm path
compositions depend on `[propext, Quot.sound]`.  Two groups also carry
`Classical.choice`, the carrier this module family already has: the four
statements that project the peel's own value structure
(`ifThen103Values_sub_eq_limMask`, `ifThen103Values_and137_eq`,
`ifThen103Values_arrayidx` and `if_then103_store_model`), and
`tail_byte_arm_verdict`, which composes the tail module's own
`if_then164_step` (whose footprint `JsonS1BlocksTail` already records as
`[propext, Classical.choice, Quot.sound]`).  No statement carries `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_run_then103
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_run_then144
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_step_then103_thread
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_step_then103_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_step_then144_thread
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end147_step_then144_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.escapeReach_of_post
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.escapePost_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.escapePost_count
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then150_denote_esc
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then150_step_at
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then150_escape_record
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then150_escape_keepsEntry
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.lastByteBits_eq_utf8TailBit
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.not_shiftLeft_allOnes_eq_limMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.ifThen103Values_sub_eq_limMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.ifThen103Values_and137_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.ifThen103Values_arrayidx
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then103_store_word
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then103_store_model
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.or169500_tailbit_one_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.ifThen164Env_or169500
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.ifEnd153ThreadEnv_cmp155495_one_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.asciiProbe_or279
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_then150_step_after_merge_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end170_step_of_thread
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.if_end170_step_of_then164
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.tail_silent_path
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.tail_escape_path
#print axioms LeanLLVM.Refinement.JsonS1BlocksCompose.tail_byte_arm_verdict

end LeanLLVM.Refinement.JsonS1BlocksCompose
