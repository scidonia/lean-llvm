/-
The loop's run with the accumulator's carry beside the model's.

`JsonS1BlocksLoopRun.loopRun_carry` carries the loop's model facts to
`for.end101`, but it hands the accumulator's fold and lane count to the caller
(`loopExitFacts_at`'s `hu8k` and `haccLen`).  `JsonS1BlocksAccFold` states that
fold as `AccCarry`, proves it at the entry's zero word and preserves it by each
of the four page shapes, but no run threads it to the exit.  This module is that
thread: the head invariant with the carry beside it, the same measure induction
with one page per row, and the exit facts at the terminal without the
accumulator's obligations.

## The invariant and the terminal

* **`AccInv`** — `JsonS1BlocksLoopRun.LoopInv` and `AccCarry` at the loop head;
* **`AccLatch`** — `LoopLatch` and `AccCarry` at the back edge;
* **`AccTerm`** — the exit terminal: `FusedExit`, `LoopCarry`, `AccCarry`.

## The page step

`loopAccLatch_page` is `JsonS1BlocksLoopRun.loopLatch_page` with the
accumulator's carry.  The decisions, the six row windows and the two loaded
words are the same; each of the four shapes pairs `fused_*_page`'s `FusedLatch`
with `loopCarry_*`'s model step and `JsonS1BlocksAccFold`'s `accLatch_*` step.
The DFA arm's word is `%or.i281`'s, the merge arm's is the body's; both pack to
`klAcc` at the successor index.

## The run and the exit

* `loopRun_accCarry_aux`, `loopRun_accCarry` — the induction, one page per row,
  at most five control steps per remaining row plus five.
* `loopExitFacts_of_accCarry` (`JsonS1BlocksAccFold`) — `LoopExitFacts` at the
  terminal from the frame alone, the accumulator's fold supplied by the carry.
* `loopExit_staging_of_accCarry`, `tail_facts_of_accCarry`,
  `tail_peel_facts_of_accCarry` — `JsonS1BlocksLoopRun`'s staging and tail facts
  at the carry instead of the two global obligations.
* `accTerm_exitFacts`, `loopAccRun_exitFacts` — the terminal's and the run's
  bundle.

## What remains

* **The page's `pre` at the call vectors.**  The escape call answers
  (`hcallAll`) and its answer keeps the document, the staged zeroes, the array's
  prefix and the stream's prefix (`hkeep`); the induction takes both as the
  caller's staging facts, exactly as `loopRun_carry` does.  The page's own
  precondition at the argument list — `sel escapeListCallee [...]` at the seven
  values — is the caller's until the call vectors are fixed.
* **The bounded prefix.**  The run starts at the loop head; the entry's
  `JsonS1BlocksLoopRun.OnePrefix`/`onePrefix_of_exit` expose the prefix's fuel
  as `N`, and the budget's arithmetic
  (`s1BlocksBudget_of_phaseCharge`) still bounds that `N`.  Nothing here says
  anything about the prefix.
* **The unit-post plug-in.**  The exit's `VerdictStaging` is
  `loopExit_staging_of_accCarry`; the unit post's own composition
  (`JsonS1BlocksUnitPost`) is unchanged, and the record's `err`-word identity is
  still its input.

The page's word identity (`PageModel`), the carried classifier state
(`PageCarry`) and the loop's own side conditions are the induction's inputs, as
in `loopRun_carry`.
-/
import LeanLLVM.Refinement.JsonS1BlocksAccFold
import LeanLLVM.Refinement.JsonS1BlocksLoopRun

namespace LeanLLVM.Refinement.JsonS1BlocksAccRun

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksPeelStaging
open LeanLLVM.Refinement.JsonS1BlocksPeelWindows
open LeanLLVM.Refinement.JsonS1BlocksSpecWindow
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksStream
open LeanLLVM.Refinement.JsonS1BlocksAccFold
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The invariant, the latch and the terminal -/

/-- **The loop head's invariant with the accumulator.**  The page invariant, the
model's carry and the accumulator's. -/
structure AccInv (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1) : Prop
    extends LoopInv mem0 xp xn ps bs env s c gate esc where
  /-- The accumulator's carry. -/
  acc : AccCarry bs c

/-- **The back edge's invariant with the accumulator.** -/
structure AccLatch (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (env : Env) (s : State) (i : BitVec 64) (c : FusedCarry) (gate esc : BitVec 1) :
    Prop extends LoopLatch mem0 xp xn ps bs env s i c gate esc where
  /-- The accumulator's carry. -/
  acc : AccCarry bs c

/-- **The loop's terminal with the accumulator.**  `for.end101` at the exit's
facts, with the model's carry and the accumulator's. -/
inductive AccTerm (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8) :
    State → Prop where
  | exit (env : Env) (s : State) (c : FusedCarry) :
      FusedExit env s c → LoopCarry mem0 xp xn ps bs c → AccCarry bs c →
      AccTerm mem0 xp xn ps bs (stateAt env s)

/-- Every accumulator-carrying terminal is the loop's own terminal. -/
theorem AccTerm.toLoopTerm {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {e : State} (h : AccTerm mem0 xp xn ps bs e) :
    LoopTerm mem0 xp xn ps bs e := by
  rcases h with ⟨env, s, c, hexit, hc, -⟩
  exact LoopTerm.exit env s c hexit hc

/-- Every accumulator-carrying terminal is the fused loop's terminal. -/
theorem AccTerm.toTerm {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {e : State} (h : AccTerm mem0 xp xn ps bs e) :
    FusedTerm e :=
  h.toLoopTerm.toTerm

/-! ### One page, with the accumulator

`loopLatch_page`'s four shapes at the same decisions, each pairing the page's
`FusedLatch` with the model's carry step and the accumulator's. -/

/-- **One page, with the accumulator's carry.**  From the head's invariant the
page reaches the latch at the successor's carry, in at most four control steps,
on whichever of the four shapes the two decisions select, with `AccCarry` at the
successor. -/
theorem loopAccLatch_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (bs73 bs74 : List UInt8)
    (mem0 : Mem) (xp xn : Nat) (ps : List Nat) (bs : List UInt8)
    (hinv : FusedInv env s c gate escBit)
    (hcarry : LoopCarry mem0 xp xn ps bs c)
    (hacc : AccCarry bs c)
    (hmodel : PageModel bs)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (r : CallOutcome)
    (hcall : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r)
    (hkeepDoc : ∀ j, j < c.shr.toNat →
      readBytes r.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hkeepZero : readBytes r.mem (c.b - 3) 3 = some [0, 0, 0])
    (hkeepPrefix : EntryPrefix r.mem c.ent bs (c.i.toNat + 1))
    (hkeepStream : StreamPrefix r.mem xp xn ps) :
    ∃ (env' : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 4 ∧
      (∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt env' core)) ∧
      AccLatch mem0 xp xn ps bs env' core c.i c' gate escBit ∧
      c'.b = c.b ∧ c'.ent = c.ent ∧ c'.xp = c.xp ∧ c'.nxp = c.nxp ∧
      c'.xcarry = c.xcarry ∧ c'.shr = c.shr ∧
      (∀ j, j < c.shr.toNat →
        readBytes c'.mem (c.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] := by
  have hi := hinv.index_lt
  have hwin : FusedWindows c.mem c.b c.shr.toNat c.i (docBlock bs) :=
    fused_windows c.mem c.b c.shr.toNat c.i (docBlock bs) hb3 hi hzero hdoc
  have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
      some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
  have h73 : bs73 = (docBlock bs c.i.toNat).take 32 := by
    obtain ⟨h, _⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
      (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
    rw [hread73] at h
    exact Option.some.inj h
  have h74 : bs74 = (docBlock bs c.i.toNat).drop 32 := by
    obtain ⟨_, h⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
      (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
    rw [hread74] at h
    exact Option.some.inj h
  have hpage : PageStep bs c bs73 bs74 :=
    { w73 := h73, w74 := h74
      store := hmodel.storeW c bs73 bs74 (by omega) (hstate c hi) h73 h74 }
  rcases BlockEval.bitVec1_eq_zero_or_one
    (fb54Select gate (fusedValues c bs73 bs74).v107) with hdec | hdec
  · -- the DFA arm
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · -- DFA, escape record: the page stores, then calls
      subst he
      obtain ⟨h01, h12, h23, h34, hl⟩ :=
        fused_dfa_escape_page sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
          hinv hshr57 hb3 hgap hread73 hread74 hdec
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r hcall
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 r.mem) :=
        loopCarry_fusedNext hcarry hpage (by omega) hblocks64 hkeepPrefix hkeepStream
      have hacc' : AccCarry bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 r.mem) :=
        accLatch_dfa_escape sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59 bs
          hinv hacc hshrLe hshrBlocks hshr57 hb3 hzero hdoc hread73 hread74
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r
      exact ⟨_, _, _, 4, by omega, fun j => runFuel_jump4 h01 h12 h23 h34 j,
        { toLoopLatch := { toFusedLatch := hl, model := hcarry' }, acc := hacc' },
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · -- DFA, skip the record
      subst he
      obtain ⟨h01, h12, h23, hl⟩ :=
        fused_dfa_skip_page sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
          hinv hshr57 hb3 hgap hread73 hread74 hdec
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 (fusedStore c bs73 bs74)) :=
        loopCarry_store hcarry hpage (by omega) hblocks64 hentXp
      have hacc' : AccCarry bs
          (fusedNext c bs73 bs74
            (fusedDfa90 c bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57
              hwin.bs58 hwin.bs59).or281 (fusedStore c bs73 bs74)) :=
        accLatch_dfa_skip sel env s c gate bs73 bs74
          hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59 bs
          hinv hacc hshrLe hshrBlocks hshr57 hb3 hzero hdoc hread73 hread74
          hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 (docBlock bs) hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j,
        { toLoopLatch := { toFusedLatch := hl, model := hcarry' }, acc := hacc' },
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩
  · -- the merge
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · -- merge, escape record
      subst he
      obtain ⟨h01, h12, h23, hl⟩ :=
        fused_merge_escape_page sel env s c gate bs73 bs74
          hinv hshr57 hread73 hread74 hdec r hcall
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74 c.u8k r.mem) :=
        loopCarry_fusedNext hcarry hpage (by omega) hblocks64 hkeepPrefix hkeepStream
      have hacc' : AccCarry bs (fusedNext c bs73 bs74 c.u8k r.mem) :=
        accLatch_merge_escape sel env s c gate bs73 bs74 bs
          hinv hacc hshrLe hshrBlocks hshr57 hdoc hread73 hread74 hdec r
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j,
        { toLoopLatch := { toFusedLatch := hl, model := hcarry' }, acc := hacc' },
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · -- merge, skip the record
      subst he
      obtain ⟨h01, h12, hl⟩ :=
        fused_merge_skip_page sel env s c gate bs73 bs74
          hinv hshr57 hread73 hread74 hdec
      have hcarry' : LoopCarry mem0 xp xn ps bs
          (fusedNext c bs73 bs74 c.u8k (fusedStore c bs73 bs74)) :=
        loopCarry_store hcarry hpage (by omega) hblocks64 hentXp
      have hacc' : AccCarry bs
          (fusedNext c bs73 bs74 c.u8k (fusedStore c bs73 bs74)) :=
        accLatch_merge_skip sel env s c gate bs73 bs74 bs
          hinv hacc hshrLe hshrBlocks hshr57 hdoc hread73 hread74 hdec
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 (docBlock bs) hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 2, by omega, fun j => runFuel_jump2 h01 h12 j,
        { toLoopLatch := { toFusedLatch := hl, model := hcarry' }, acc := hacc' },
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩

/-! ### The induction

The measure is the distance to the bound, one page per row; the page is
`loopAccLatch_page`'s, so each of the four shapes advances the model's carry and
the accumulator's.  At zero the latch's test is true and the run leaves
`for.end101` with the successor's carries; above zero it is false, the back edge
re-enters the head, and the page's own document and zeroes are the next page's.
The escape call enters through the caller's two facts, as in `fusedInv_runFuel`:
it answers (`hcall`) and its answer keeps the document, the staged zeroes, the
array's prefix and the stream's prefix (`hkeep`). -/

/-- **The loop's run, with the accumulator's carry.**  From the head's invariant,
the run at the escape selection reaches the bound's exit at `for.end101` in at
most five control steps per remaining row plus five, and the terminal carries
the loop's carry and the accumulator's. -/
theorem loopRun_accCarry_aux (sel : Calls) (mem0 : Mem) (xp xn : Nat) (ps : List Nat)
    (bs : List UInt8) (hmodel : PageModel bs) :
    ∀ (r : Nat) (env : Env) (s : State) (c : FusedCarry) (gate escBit : BitVec 1),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      c.shr.toNat ≤ blocksOf bs.length →
      blocksOf bs.length < 2 ^ 64 →
      AccInv mem0 xp xn ps bs env s c gate escBit →
      (∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c) →
      64 * c.shr.toNat ≤ bs.length →
      3 ≤ c.b →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat →
        readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j)) →
      readBytes c.mem (c.b - 3) 3 = some [0, 0, 0] →
      (c.ent + 8 * blocksOf bs.length ≤ xp ∨
        xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) →
      (∀ (args : List Value) (mem : Mem) (next : Nat),
        ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) →
      (∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
        (∀ j, j < c'.shr.toNat →
          readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
        readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
        EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
        StreamPrefix r.mem xp xn ps) →
      ∃ (e : State) (j : Nat), j ≤ 5 * r + 5 ∧ AccTerm mem0 xp xn ps bs e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e
  | 0, env, s, c, gate, escBit, hmeasure, hshr57, hshrLe, hblocks64, hinv, hstate,
    hshrBlocks, hb3, hgap, hdoc, hzero, hentXp, hcallAll, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsucc]
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero, hkeepPrefix, hkeepStream⟩ :=
        hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨env', core, c', k, hk, hrun, hl, hb', he', hxp', hnxp', hxc', hshr',
        -, -⟩ :=
        loopAccLatch_page sel env s c gate escBit ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) mem0 xp xn ps bs
          hinv.toLoopInv.toFusedInv hinv.model
          hinv.acc hmodel hstate hshrBlocks hshr57 hb3 hshrLe hblocks64 hgap hdoc hzero
          hentXp hread73 hread74 rc hcCall hkeepDoc hkeepZero hkeepPrefix hkeepStream
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 1 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).1.mpr hbound
      obtain ⟨hstep, hexit⟩ :=
        fused_latch_exit sel env' core c.i c' gate escBit hl.toLoopLatch.toFusedLatch hbit
      refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }, k + 1, by omega,
        AccTerm.exit (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.end101", pre := some "if.end98" }) c' hexit hl.model
          hl.acc,
        fun j => ?_⟩
      rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
        runFuel_jump_prefix hstep j]
  | r + 1, env, s, c, gate, escBit, hmeasure, hshr57, hshrLe, hblocks64, hinv, hstate,
    hshrBlocks, hb3, hgap, hdoc, hzero, hentXp, hcallAll, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 :=
        toNat_succ_of_lt (by omega)
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsucc] at hcongr
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 =
          some (docBlock bs c.i.toNat) := hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ :=
        readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hcCall⟩ := hcallAll _ _ _
      obtain ⟨hkeepDoc, hkeepZero, hkeepPrefix, hkeepStream⟩ :=
        hkeep c _ _ _ _ _ _ rc hcCall
      obtain ⟨env', core, c', k, hk, hrun, hl, hb', he', hxp', hnxp', hxc', hshr',
        hdoc', hzero'⟩ :=
        loopAccLatch_page sel env s c gate escBit ((docBlock bs c.i.toNat).take 32)
          ((docBlock bs c.i.toNat).drop 32) mem0 xp xn ps bs
          hinv.toLoopInv.toFusedInv hinv.model
          hinv.acc hmodel hstate hshrBlocks hshr57 hb3 hshrLe hblocks64 hgap hdoc hzero
          hentXp hread73 hread74 rc hcCall hkeepDoc hkeepZero hkeepPrefix hkeepStream
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 0 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      obtain ⟨hstep, hinv'⟩ :=
        fused_latch_loop sel env' core c.i c' gate escBit hl.toLoopLatch.toFusedLatch hbit
          (by rw [hshr']; exact hshr57)
      have hmeasure' : c'.shr.toNat - (c'.i.toNat + 1) = r := by
        rw [hshr', hl.succ, hsucc]
        omega
      have hshrLe' : c'.shr.toNat ≤ blocksOf bs.length := by rw [hshr']; exact hshrLe
      have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
        rw [hb', he', hshr']; exact hgap
      have hb3' : 3 ≤ c'.b := by rw [hb']; exact hb3
      have hentXp' : c'.ent + 8 * blocksOf bs.length ≤ xp ∨
          xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c'.ent := by
        rw [he']; exact hentXp
      obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
        loopRun_accCarry_aux sel mem0 xp xn ps bs hmodel r
          (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.body54", pre := some "if.end98" })
          c' gate escBit hmeasure' (by rw [hshr']; exact hshr57) hshrLe' hblocks64
          { toLoopInv := { toFusedInv := hinv', model := hl.model }, acc := hl.acc }
          hstate (by rw [hshr']; exact hshrBlocks) hb3' hgap'
          (by simpa only [hb', hshr'] using hdoc')
          (by simpa only [hb', hshr'] using hzero')
          hentXp' hcallAll hkeep
      refine ⟨e', (k + 1) + j, by omega, hterm, fun k' => ?_⟩
      rw [show (k + 1) + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's run from the head, with the accumulator's carry.**  The
auxiliary form at the head's own measure, `%shr - (i + 1)` pages to go. -/
theorem loopRun_accCarry (sel : Calls) (mem0 : Mem) (xp xn : Nat) (ps : List Nat)
    (bs : List UInt8) (hmodel : PageModel bs) (env : Env) (s : State)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : AccInv mem0 xp xn ps bs env s c gate escBit)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hcallAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
      (∀ j, j < c'.shr.toNat →
        readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
      EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
      StreamPrefix r.mem xp xn ps) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      AccTerm mem0 xp xn ps bs e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e :=
  loopRun_accCarry_aux sel mem0 xp xn ps bs hmodel
    (c.shr.toNat - (c.i.toNat + 1)) env s c gate escBit rfl hshr57 hshrLe hblocks64
    hinv hstate hshrBlocks hb3 hgap hdoc hzero hentXp hcallAll hkeep

/-! ### The exit facts, without the accumulator's obligations

`JsonS1BlocksLoopRun`'s exit bundle takes the accumulator's fold and lane count
as the run's obligations; at an `AccCarry` the terminal supplies both.  These are
that module's staging and tail lemmas with `hacc` in place of `hu8k` and
`haccLen`. -/

/-- **The staging at the exit, from the accumulator's carry.** -/
theorem loopExit_staging_of_accCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {env : Env} {s : State} {c : FusedCarry}
    (hexit : FusedExit env s c) (hc : LoopCarry mem0 xp xn ps bs c)
    (hacc : AccCarry bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    {n nb : Nat} {gate : Bool} {err : BitVec 1}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hi : c.i.toNat = nb)
    (herr : err = 1 ↔ ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs n nb gate err :=
  staging_of_exitFacts (loopExitFacts_of_accCarry hexit hc hacc hframe) hn hnb hi herr

/-- **The tail's two loop facts, from the accumulator's carry.** -/
theorem tail_facts_of_accCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hacc : AccCarry bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length)) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length) :=
  tail_facts_of_exit (hc.toLoopExitFacts hframe hacc.pack hacc.len)

/-- **The peel's three loop facts, from the accumulator's carry.** -/
theorem tail_peel_facts_of_accCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {c : FusedCarry} {w : BitVec 64}
    (hc : LoopCarry mem0 xp xn ps bs c)
    (hacc : AccCarry bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hslot : readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat)
        (natToBytes w.toNat 8)) (c.ent + 8 * c.i.toNat) 8 =
      some (wordsOf [stage1Word bs c.i.toNat])) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 (writeBytes c.mem (c.ent + 8 * c.i.toNat)
        (natToBytes w.toNat 8)) c.ent (blocksOf bs.length) ∧
      readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
        c.ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
  tail_peel_facts (hc.toLoopExitFacts hframe hacc.pack hacc.len)
    hsucc hslot

/-- **The terminal's exit facts.**  Every run the induction reaches carries the
loop's facts and the accumulator's; the run's own frame is the caller's
obligation. -/
theorem accTerm_exitFacts {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {e : State} (h : AccTerm mem0 xp xn ps bs e)
    (hframe : ∀ (env : Env) (s : State) (c : FusedCarry), FusedExit env s c →
      LoopCarry mem0 xp xn ps bs c →
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length)) :
    ∃ (env : Env) (s : State) (c : FusedCarry),
      FusedExit env s c ∧ LoopExitFacts mem0 bs c := by
  rcases h with ⟨env, s, c, hexit, hc, hacc⟩
  exact ⟨env, s, c, hexit,
    loopExitFacts_of_accCarry hexit hc hacc (hframe env s c hexit hc)⟩

/-- **The loop's exit facts from the head.**  The run at the head's own measure
and the terminal's bundle: from the head's invariant the loop reaches
`for.end101` with `LoopExitFacts`, the accumulator's fold supplied by the
invariant rather than by the caller. -/
theorem loopAccRun_exitFacts (sel : Calls) (mem0 : Mem) (xp xn : Nat) (ps : List Nat)
    (bs : List UInt8) (hmodel : PageModel bs) (env : Env) (s : State)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hstate : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : AccInv mem0 xp xn ps bs env s c gate escBit)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hcallAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r →
      (∀ j, j < c'.shr.toNat →
        readBytes r.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] ∧
      EntryPrefix r.mem c'.ent bs (c'.i.toNat + 1) ∧
      StreamPrefix r.mem xp xn ps)
    (hframe : ∀ (env : Env) (s : State) (c : FusedCarry), FusedExit env s c →
      LoopCarry mem0 xp xn ps bs c →
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length)) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      (∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) ∧
      ∃ (env' : Env) (s' : State) (c' : FusedCarry),
        FusedExit env' s' c' ∧ LoopExitFacts mem0 bs c' := by
  obtain ⟨e, j, hjle, hterm, hrun⟩ :=
    loopRun_accCarry sel mem0 xp xn ps bs hmodel env s c gate escBit hstate
      hshrBlocks hshr57 hshrLe hblocks64 hinv hb3 hgap hdoc hzero hentXp hcallAll hkeep
  exact ⟨e, j, hjle, hrun, accTerm_exitFacts hterm hframe⟩

/-! ### Axiom footprints

The page steps are `JsonS1BlocksAccFold`'s four shape lemmas and
`JsonS1BlocksLoopRun`'s model steps; the induction is on the measure with the
caller's two escape facts; the exit bundle is `loopExitFacts_of_accCarry` at the
terminal.  No statement reaches `sorryAx`.  The four DFA page shapes carry
`Classical.choice` through the page lemmas' `ifThen90Values_or281_length`, the
same footprint `JsonS1BlocksLoopRun`'s own induction reports; the merge shapes
and the exit's statements carry only `propext` and `Quot.sound`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.AccInv
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.AccLatch
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.AccTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.AccTerm.toLoopTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.AccTerm.toTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.loopAccLatch_page
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.loopRun_accCarry_aux
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.loopRun_accCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.loopExit_staging_of_accCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.tail_facts_of_accCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.tail_peel_facts_of_accCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.accTerm_exitFacts
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccRun.loopAccRun_exitFacts

end LeanLLVM.Refinement.JsonS1BlocksAccRun
