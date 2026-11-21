/-
The block unit's one-prefix bridge: the entry-to-exit run at the escape
selection, with the exit's cells recovered from the running environment.

`JsonS1BlocksRefines` composes the exits and the tails, but states each exit at a
caller-supplied `env`/`s`/`c`.  It cannot read those from the terminal the phase
and the loop hand back: `AsciiTerm e` and `FusedTerm e` bind their environment
inside the constructor, so a caller of `asciiPhase_from_seed` or
`fusedInv_runFuel` reaches the terminal `e` without knowing the environment the
terminal's block reads.  The exits therefore take `%and`, `%n`, `%conv`, `%arm`
and the bound's relation as hypotheses.

This module closes that gap the least invasive way: the terminals keep their
existing meaning, and the run lemmas are re-stated over a *cells-carrying*
invariant whose terminal exposes its environment.  The cells the entry's block
writes — `%conv`, `%and`, `%shr` — and the two parameters it passes through —
`%n`, `%arm` — are preserved by every environment builder of the phase and of the
fused loop, so both terminals carry them.  `EntryCells` is that bundle.

The re-stated runs are stated at `s1BlocksCallsEsc esc`, the unit's own
environment with the escape list resolved at the caller's selection; blocks that
make no call cross between the two environments by `step_esc_of_free`.  Their
terminals are `AsciiTermCells` and `FusedInvCells`/`FusedTermCells`, which mirror
`AsciiTerm`/`FusedTerm` and additionally carry the run's `EntryCells` at the
environment the terminal's own block reads.

The compositions are stated as the two terminals' consumers:

* `s1BlocksPrefix_terminal` runs from `s1BlocksInit`, on a document of at least
  one block, to a phase terminal whose environment carries the entry's cells, at
  the escape selection;
* `handoffPrefix_exit` runs from a hand-off terminal through the hand-off's two
  steps, the first page and the fused loop's own cells induction to the bound's
  exit at `for.end101`;
* `asciiExitCells_run` and `fusedExitCells_run` are `JsonS1BlocksRefines`'s two
  exits with their cell hypotheses discharged, on `AsciiInvCells` and
  `FusedExit` respectively.

## What still stands between the entry and the loop's exit

`s1BlocksPrefix_terminal`'s hand-off arm and `handoffPrefix_exit` do not yet
compose in one theorem, and the reason is a cell rather than a step.
`handoffPrefix_exit` seeds the fused loop, whose environment must bind `%xp`,
`%nxp` and `%xcarry`; the phase never reads those three, so `EntryCells` does not
carry them and `AsciiTermCells` cannot supply them at the terminal.  A
`StreamCells` extension of the bundle, preserved like `EntryCells` through the
phase's builders, closes that join; it is not a step or a memory fact.

The bridge's other hypotheses are the model's own carries, not environment facts:
the preheader's two words and its class test (`hread2`, `hread3`, `hfirst`), the
gate (`hgate`), the document window and its gap above the emit area (`hdoc`,
`hgap`), the peel's two halves and its staging family (`hsilent`, `hstage`,
`hstagePeel`, `hstageByte`), the hand-off page's row index and window bounds
(`hirow`, `hi63`, `hshl63`, `hread73`, `hread74`, `hascii_len`, `hu8k_len`), and
the escape selection's totality and frame (`hcall`, `hkeep`).
-/
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksEntry

namespace LeanLLVM.Refinement.JsonS1BlocksPrefix

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
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
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The cells the entry's block writes and the parameters it carries

`entry` binds `%conv`, `%and` and `%shr` and passes `%n` and `%arm` through.  No
block of the ASCII phase and no block of the fused loop rebinds any of the five,
so they are the same cells at every latch and at every loop head.  The bundle
states them at the values `entry` gave each one: `%conv` is the caller's 32-bit
word (the decode is folded into the value the caller names), `%and` is
`n &&& 63`, and `%shr` is `n >>> 6`. -/

/-- **The entry's five cells, at the running environment.**  The two parameters
and the three words the entry block writes, at the values the entry's own
`denoteCode` gives them. -/
structure EntryCells (env : Env) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) : Prop where
  /-- The document's length. -/
  n_cell : lookupName env "%n" = some (.int 64 n)
  /-- The caller's 32-bit word. -/
  conv_cell : lookupName env "%conv" = some (.int 32 conv)
  /-- The escape arm. -/
  arm_cell : lookupName env "%arm" = some (.int 64 arm)
  /-- The entry's partial-block word. -/
  and_cell : lookupName env "%and" = some (.int 64 (n &&& 63))
  /-- The entry's whole-block count. -/
  shr_cell : lookupName env "%shr" = some (.int 64 (n >>> 6))

/-! ### Reads that miss one builder's cells

Each builder below is a `cells` list whose keys the block itself wrote, so a read
of a name the list does not bind reaches the environment beneath.  The proofs
unfold the builder and peel its list; the side conditions are the literal keys'
disequalities. -/

theorem lookupName_lrPhEnv_n (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%n" = lookupName env "%n" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_and (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%and" = lookupName env "%and" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_conv (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%conv" = lookupName env "%conv" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_arm (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%arm" = lookupName env "%arm" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_shr (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%shr" = lookupName env "%shr" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_n (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%n" = lookupName env "%n" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_and (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%and" = lookupName env "%and" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_conv (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%conv" = lookupName env "%conv" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_arm (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%arm" = lookupName env "%arm" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_shr (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%shr" = lookupName env "%shr" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forBodyOut_n (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%n" = lookupName env "%n" := by
  handoff_lk

theorem lookupName_forBodyOut_and (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%and" = lookupName env "%and" := by
  handoff_lk

theorem lookupName_forBodyOut_conv (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%conv" = lookupName env "%conv" := by
  handoff_lk

theorem lookupName_forBodyOut_arm (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%arm" = lookupName env "%arm" := by
  handoff_lk

theorem lookupName_ifEndEnv_n (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%n" = lookupName env "%n" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_and (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%and" = lookupName env "%and" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_conv (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%conv" = lookupName env "%conv" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_arm (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%arm" = lookupName env "%arm" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_shr (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%shr" = lookupName env "%shr" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

/-! ### The same reads through the preheader's page

The phase's seed is the preheader's first pass; its environment is the
preheader's then the body's then the class test's, so the cells pass through all
four builders. -/

theorem lookupName_asciiSeedEnv_n (env : Env) (arm : BitVec 64) (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%n"
      = lookupName env "%n" := by
  rw [lookupName_ifEndEnv_n, lookupName_forBodyOut_n, lookupName_lrPhEnv_n]

theorem lookupName_asciiSeedEnv_conv (env : Env) (arm : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%conv"
      = lookupName env "%conv" := by
  rw [lookupName_ifEndEnv_conv, lookupName_forBodyOut_conv, lookupName_lrPhEnv_conv]

theorem lookupName_asciiSeedEnv_arm (env : Env) (arm : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%arm"
      = lookupName env "%arm" := by
  rw [lookupName_ifEndEnv_arm, lookupName_forBodyOut_arm, lookupName_lrPhEnv_arm]

theorem lookupName_asciiSeedEnv_and (env : Env) (arm : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%and"
      = lookupName env "%and" := by
  rw [lookupName_ifEndEnv_and, lookupName_forBodyOut_and, lookupName_lrPhEnv_and]

theorem lookupName_asciiSeedEnv_shr (env : Env) (arm : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%shr"
      = lookupName env "%shr" := by
  rw [lookupName_ifEndEnv_shr, lookupName_forBodyOut_shr, lookupName_lrPhEnv_shr]

/-! ### The phase's invariant with the entry's cells

`AsciiInv` is the latch's own reading.  The structure below adds the five cells
the exit's block reads, which the latch's invariant does not mention because no
pass changes them. -/

/-- **The latch's invariant with the entry's cells.**  The phase's own carry plus
the five cells `entry` left. -/
structure AsciiInvCells (env : Env) (s : State) (c : AsciiCarry) (b : Nat)
    (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64) : Prop
    extends AsciiInv env s c where
  /-- The row base is the one the phase's seed set. -/
  b_eq : c.b = b
  /-- The document's length. -/
  n_cell : lookupName env "%n" = some (.int 64 n)
  /-- The caller's 32-bit word. -/
  conv_cell : lookupName env "%conv" = some (.int 32 conv)
  /-- The escape arm. -/
  arm_cell : lookupName env "%arm" = some (.int 64 arm)
  /-- The entry's partial-block word. -/
  and_cell : lookupName env "%and" = some (.int 64 (n &&& 63))
  /-- The entry's whole-block count. -/
  shr_cell : lookupName env "%shr" = some (.int 64 (n >>> 6))


/-! ### The phase's terminals with their environment

The two terminals mirror `AsciiTerm`, but name the environment and the carry, so
the exit's block reads are the ones the last pass left.  `toTerm` records that
each is one of the old terminals. -/

/-- **The phase's terminals, with the running environment and the entry's
cells.**  Either the latch reached the bound and left for `for.end101` at the
final latch's environment, or the class test handed the block to `if.then38`. -/
inductive AsciiTermCells (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) : State → Prop where
  | exit (env : Env) (s : State) (c : AsciiCarry) :
      AsciiInvCells env s c b n conv arm → c.i + 1 = c.shr →
      AsciiTermCells b n conv arm (asciiExitState env s c)
  | handoff (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
      (v : ForBodyValues) :
      AsciiInvCells env s c b n conv arm →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 →
      c.i + 1 ≠ c.shr →
      v = asciiValues c bs2 bs3 →
      AsciiTermCells b n conv arm (asciiHandoffState env s c v)

/-- Every cells-carrying terminal is one of the phase's terminals. -/
theorem AsciiTermCells.toTerm {b : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm : BitVec 64} {e : State} (h : AsciiTermCells b n conv arm e) : AsciiTerm e := by
  cases h with
  | exit env s c hinv hbound => exact AsciiTerm.exit env s c hinv.toAsciiInv hbound
  | handoff env s c bs2 bs3 v hinv h2 h3 hne hv =>
      exact AsciiTerm.handoff env s c bs2 bs3 v hinv.toAsciiInv h2 h3 hv

/-! ### The phase's seed with the entry's cells

The preheader's first pass ends at the latch; `asciiInv_seed` gives the invariant,
and the cells read through its four builders. -/

/-- **The phase's seed, with the entry's cells.**  The preheader's first pass at
an environment that carries the entry's five cells. -/
theorem asciiInvCells_seed (env : Env) (s : State) (arm : BitVec 64)
    (bs2 bs3 : List UInt8) (b ent : Nat) (shr n : BitVec 64) (conv : BitVec 32)
    (hcells : EntryCells env n conv arm)
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hnpos : 0 < shr.toNat) :
    let v := forBodyValues 0 0 0 0 0 bs2 bs3 b ent
    let s1 := stateAt (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3)
      { s with
        pc := "for.inc",
        pre := some "if.end",
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }
    AsciiInvCells (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) s1
      { i := v.i, prevS := v.shr17, st0 := v.shrII, st9 := v.conv13II,
        st15 := v.shrI, b := b, ent := ent, shr := shr,
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) } b n conv arm := by
  intro v s1
  have hbase : AsciiInv (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) s1
      { i := v.i, prevS := v.shr17, st0 := v.shrII, st9 := v.conv13II,
        st15 := v.shrI, b := b, ent := ent, shr := shr,
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) } :=
    asciiInv_seed env s arm bs2 bs3 b ent shr harm hgate hshr hb hent hnpos
  refine
    { toAsciiInv := hbase
      b_eq := rfl
      n_cell := by rw [lookupName_asciiSeedEnv_n]; exact hcells.n_cell
      conv_cell := by rw [lookupName_asciiSeedEnv_conv]; exact hcells.conv_cell
      arm_cell := by rw [lookupName_asciiSeedEnv_arm]; exact hcells.arm_cell
      and_cell := by rw [lookupName_asciiSeedEnv_and]; exact hcells.and_cell
      shr_cell := by
        rw [lookupName_asciiSeedEnv_shr]; exact hcells.shr_cell }

/-! ### One pass preserves the cells

The latch's three steps are `asciiInv_step`'s; the cells read through `forIncEnv`,
the body's environment and the class test's. -/

/-- **One pass's cells.**  The back edge's three steps and the successor
invariant with the entry's cells carried through. -/
theorem asciiInvCells_step (env : Env) (s : State) (c : AsciiCarry)
    (bs2 bs3 : List UInt8) (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64)
    (hinv : AsciiInvCells env s c b n conv arm)
    (hloop : evalICmp .eq (c.i + 1) c.shr = 0)
    (hj : (c.i + 1).toNat < 2 ^ 57)
    (hread2 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2)
    (hread3 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3)
    (hbit : evalICmp .eq (ifEndTest (asciiValues c bs2 bs3).w2
      (asciiValues c bs2 bs3).w3) 0 = 0) :
    let v := asciiValues c bs2 bs3
    let s1 := stateAt (forIncEnv env c.i c.shr)
      { s with pc := "for.body", pre := some "for.inc" }
    let s2 := stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
      { s with
        pc := "if.end",
        pre := some "for.body",
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }
    let s3 := stateAt (ifEndEnv (forBodyOut (forIncEnv env c.i c.shr) v) v.w2 v.w3)
      { s with
        pc := "for.inc",
        pre := some "if.end",
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }
    step s1BlocksCalls s1BlocksFunction (stateAt env s) = .jump s1 ∧
    step s1BlocksCalls s1BlocksFunction s1 = .jump s2 ∧
    step s1BlocksCalls s1BlocksFunction s2 = .jump s3 ∧
    AsciiInvCells (ifEndEnv (forBodyOut (forIncEnv env c.i c.shr) v) v.w2 v.w3) s3
      (asciiNext c bs2 bs3) b n conv arm := by
  intro v s1 s2 s3
  obtain ⟨h01, h12, h23, hbase⟩ :=
    asciiInv_step env s c bs2 bs3 hinv.toAsciiInv hloop hj hread2 hread3 hbit
  refine ⟨h01, h12, h23, ?_⟩
  refine
    { toAsciiInv := hbase
      b_eq := by simpa only [asciiNext] using hinv.b_eq
      n_cell := by
        rw [lookupName_ifEndEnv_n, lookupName_forBodyOut_n, lookupName_forIncEnv_n]
        exact hinv.n_cell
      conv_cell := by
        rw [lookupName_ifEndEnv_conv, lookupName_forBodyOut_conv,
          lookupName_forIncEnv_conv]
        exact hinv.conv_cell
      arm_cell := by
        rw [lookupName_ifEndEnv_arm, lookupName_forBodyOut_arm,
          lookupName_forIncEnv_arm]
        exact hinv.arm_cell
      and_cell := by
        rw [lookupName_ifEndEnv_and, lookupName_forBodyOut_and,
          lookupName_forIncEnv_and]
        exact hinv.and_cell
      shr_cell := by
        rw [lookupName_ifEndEnv_shr, lookupName_forBodyOut_shr,
          lookupName_forIncEnv_shr]
        exact hinv.shr_cell }

/-! ### The phase's run at the escape selection

The existing induction is at `s1BlocksCalls`; the phase makes no call, so each
step crosses to `s1BlocksCallsEsc esc` by `step_esc_of_free` at the block the
state stands in.  The terminal exposes its environment, so the cells are readable
at the exit. -/

/-- A control step at `for.inc` is the same at either call environment. -/
theorem step_forInc_esc (esc : Calls) (env : Env) (s : State)
    (hpc : s.pc = "for.inc") :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      step s1BlocksCalls s1BlocksFunction (stateAt env s) :=
  step_esc_of_free esc s1BlocksFunction (stateAt env s) for_incBlock
    (by rw [show (stateAt env s).pc = s.pc from rfl, hpc]; exact findBlock_for_inc)
    (by decide)

/-- A control step at `for.body` is the same at either call environment. -/
theorem step_forBody_esc (esc : Calls) (env : Env) (s : State)
    (hpc : s.pc = "for.body") :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      step s1BlocksCalls s1BlocksFunction (stateAt env s) :=
  step_esc_of_free esc s1BlocksFunction (stateAt env s) for_bodyBlock
    (by rw [show (stateAt env s).pc = s.pc from rfl, hpc]; exact findBlock_for_body)
    (by decide)

/-- A control step at `if.end` is the same at either call environment. -/
theorem step_forIfEnd_esc (esc : Calls) (env : Env) (s : State)
    (hpc : s.pc = "if.end") :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      step s1BlocksCalls s1BlocksFunction (stateAt env s) :=
  step_esc_of_free esc s1BlocksFunction (stateAt env s) if_endBlock
    (by rw [show (stateAt env s).pc = s.pc from rfl, hpc]; exact findBlock_if_end)
    (by decide)

/-- **The phase's run, with the entry's cells.**  From a latch inside the bound,
the run at the escape selection reaches one of the phase's terminals in at most
`3` steps per remaining pass plus `4`, and the terminal names the environment
that carries the entry's five cells. -/
theorem asciiInvCells_runFuel_aux (esc : Calls) :
    ∀ (r : Nat) (env : Env) (s : State) (c : AsciiCarry) (b : Nat)
      (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
      (doc : Nat → List UInt8),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      AsciiInvCells env s c b n conv arm →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) →
      ∃ (e : State) (j : Nat), j ≤ 3 * r + 4 ∧ AsciiTermCells b n conv arm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc esc) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e
  | 0, env, s, c, b, n, conv, arm, doc, hmeasure, hshr, hinv, hgap, hdoc => by
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        have hl := hinv.index_lt
        omega
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsucc]
        have hl := hinv.index_lt
        omega
      have hstep : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
          .jump (stateAt (forIncEnv env c.i c.shr)
            { s with pc := "for.end101", pre := some "for.inc" }) := by
        rw [step_forInc_esc esc env s hinv.pc]
        exact asciiInv_exit env s c hinv.toAsciiInv hbound
      refine ⟨asciiExitState env s c, 1, by omega,
        AsciiTermCells.exit env s c hinv hbound, fun k => ?_⟩
      exact runFuel_jump_prefix hstep k
  | r + 1, env, s, c, b, n, conv, arm, doc, hmeasure, hshr, hinv, hgap, hdoc => by
      have hlt : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        omega
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsucc] at hcongr
        omega
      have hloop : evalICmp .eq (c.i + 1) c.shr = 0 :=
        (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      have hj57 : (c.i + 1).toNat < 2 ^ 57 := asciiPass_hj c hshr hlt
      have hneNat : c.i.toNat + 1 ≠ c.shr.toNat := by
        intro heq
        exact hne (BitVec.eq_of_toNat_eq (by rw [hsucc]; exact heq))
      have hblock : c.i.toNat + 1 < c.shr.toNat := by omega
      let blk := doc (c.i.toNat + 1)
      let bs2 := blk.take 32
      let bs3 := blk.drop 32
      have hblk : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 64 = some blk := by
        rw [hsucc]
        exact hdoc (c.i.toNat + 1) hblock
      obtain ⟨hread2, hread3⟩ :=
        readBytes_split c.mem (c.b + 64 * (c.i + 1).toNat) 32 32
          (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
      have hread2' : readBytes s.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 := by
        rw [hinv.mem]
        exact hread2
      have hread3' : readBytes s.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 := by
        rw [hinv.mem]
        exact hread3
      let v := asciiValues c bs2 bs3
      let E' := ifEndEnv (forBodyOut (forIncEnv env c.i c.shr) v) v.w2 v.w3
      let s3 := stateAt E'
        { s with
          pc := "for.inc",
          pre := some "if.end",
          mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }
      by_cases hbit : evalICmp .eq (ifEndTest v.w2 v.w3) 0 = (1 : BitVec 1)
      · -- the hand-off: three steps to `if.then38`
        obtain ⟨h01, h12, h23⟩ :=
          for_inc_page_handoff env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
            c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
            hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit
        have h01' : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
            .jump (stateAt (forIncEnv env c.i c.shr)
              { s with pc := "for.body", pre := some "for.inc" }) := by
          rw [step_forInc_esc esc env s hinv.pc]; exact h01
        have h12' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forIncEnv env c.i c.shr)
              { s with pc := "for.body", pre := some "for.inc" }) =
            .jump (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with pc := "if.end", pre := some "for.body", mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          rw [step_forBody_esc esc (forIncEnv env c.i c.shr)
            { s with pc := "for.body", pre := some "for.inc" } rfl]
          exact h12
        have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with pc := "if.end", pre := some "for.body", mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) =
            .jump (stateAt E'
              { s with pc := "if.then38", pre := some "if.end", mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
        refine ⟨asciiHandoffState env s c v, 3, by omega,
          AsciiTermCells.handoff env s c bs2 bs3 v hinv hread2 hread3 hne rfl,
          fun k => ?_⟩
        exact runFuel_jump3 h01' h12' h23' k
      · -- the back edge: three steps to the next latch, then the same induction
        have hbit0 : evalICmp .eq (ifEndTest v.w2 v.w3) 0 = 0 := by
          rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (ifEndTest v.w2 v.w3) 0)
            with h | h
          · exact h
          · exact absurd h hbit
        have h01' : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
            .jump (stateAt (forIncEnv env c.i c.shr)
              { s with pc := "for.body", pre := some "for.inc" }) := by
          obtain ⟨h01, -, -⟩ :=
            for_inc_page_ascii env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
              c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
              hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit0
          rw [step_forInc_esc esc env s hinv.pc]; exact h01
        have h12' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forIncEnv env c.i c.shr)
              { s with pc := "for.body", pre := some "for.inc" }) =
            .jump (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with pc := "if.end", pre := some "for.body", mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          obtain ⟨-, h12, -⟩ :=
            for_inc_page_ascii env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
              c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
              hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit0
          rw [step_forBody_esc esc (forIncEnv env c.i c.shr)
            { s with pc := "for.body", pre := some "for.inc" } rfl]
          exact h12
        have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with pc := "if.end", pre := some "for.body", mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) =
            .jump s3 := by
          obtain ⟨-, -, h23⟩ :=
            for_inc_page_ascii env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
              c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
              hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit0
          rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
        obtain ⟨-, -, -, hinv'⟩ :=
          asciiInvCells_step env s c bs2 bs3 b n conv arm hinv hloop hj57 hread2 hread3
            hbit0
        have hgap' : (asciiNext c bs2 bs3).b
            + 64 * (asciiNext c bs2 bs3).shr.toNat ≤ (asciiNext c bs2 bs3).ent := by
          simpa only [asciiNext] using hgap
        have hdoc' : ∀ j, j < (asciiNext c bs2 bs3).shr.toNat →
            readBytes (asciiNext c bs2 bs3).mem ((asciiNext c bs2 bs3).b + 64 * j) 64
              = some (doc j) := by
          intro j hj
          have hmem : (asciiNext c bs2 bs3).mem
              = writeBytes c.mem (c.ent + 8 * (c.i + 1).toNat)
                  (natToBytes v.or16.toNat 8) := by
            simp only [asciiNext, v]
            rw [asciiValues_arrayidx c bs2 bs3 hj57]
          have hb' : (asciiNext c bs2 bs3).b = c.b := rfl
          have hshr' : (asciiNext c bs2 bs3).shr = c.shr := rfl
          have hj' : j < c.shr.toNat := by simpa only [hshr'] using hj
          rw [hmem, hb']
          exact readBytes_writeBytes_doc c.mem _ (c.ent + 8 * (c.i + 1).toNat)
            c.b c.shr.toNat doc hdoc (by omega) j hj'
        have hmeasure' : (asciiNext c bs2 bs3).shr.toNat
            - ((asciiNext c bs2 bs3).i.toNat + 1) = r := by
          rw [show (asciiNext c bs2 bs3).shr = c.shr from rfl,
            show (asciiNext c bs2 bs3).i = c.i + 1 from rfl, hsucc]
          omega
        obtain ⟨e, j, hjle, hterm, hfuel⟩ :=
          asciiInvCells_runFuel_aux esc r E' s3 (asciiNext c bs2 bs3) b n conv arm doc
            hmeasure' hshr hinv' hgap' hdoc'
        refine ⟨e, 3 + j, by omega, hterm, fun k => ?_⟩
        rw [show 3 + j + k = 3 + (j + k) from by omega,
          runFuel_jump3 h01' h12' h23' (j + k)]
        exact hfuel k

/-- **The phase's run, with the entry's cells.**  The auxiliary form at the
latch's own measure. -/
theorem asciiInvCells_runFuel (esc : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (b : Nat) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (doc : Nat → List UInt8)
    (hshr : c.shr.toNat < 2 ^ 57) (hinv : AsciiInvCells env s c b n conv arm)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) :
    ∃ (e : State) (j : Nat),
      j ≤ 3 * (c.shr.toNat - (c.i.toNat + 1)) + 4 ∧ AsciiTermCells b n conv arm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc esc) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e :=
  asciiInvCells_runFuel_aux esc (c.shr.toNat - (c.i.toNat + 1)) env s c b n conv arm doc
    rfl hshr hinv hgap hdoc


/-! ### The fused loop's environment builders

The loop's environment is a stack of `cells` lists whose keys the loop's own
blocks wrote: the body's nine segments, the DFA arm's fifty cells, its merge's
`%u8k.2`, the escape record's four, the latch's two, and the preheader's three.
None of them binds `%n`, `%conv`, `%arm`, `%and` or `%shr`, so the entry's cells
are the same at every loop head, at every latch and at the exit. -/

/-- A read through the body's nine segment environments, at a value the
environment beneath already holds.  The list is a cons chain, so the `simp`
battery is the unfolding and `lookupName`'s literals decide the misses. -/
theorem lookupName_fb54Env9_n (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (fb54Env9 env v gate) "%n" = some (.int 64 n) := by
  simp only [fb54Env9, fb54Env1, fb54Env2, fb54Env3, fb54Env4, fb54Env5,
    fb54Env6, fb54Env7, fb54Env8, cells]
  exact h

theorem lookupName_fb54Env9_conv (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env9 env v gate) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env9, fb54Env1, fb54Env2, fb54Env3, fb54Env4, fb54Env5,
    fb54Env6, fb54Env7, fb54Env8, cells]
  exact h

theorem lookupName_fb54Env9_arm (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (fb54Env9 env v gate) "%arm" = some (.int 64 arm) := by
  simp only [fb54Env9, fb54Env1, fb54Env2, fb54Env3, fb54Env4, fb54Env5,
    fb54Env6, fb54Env7, fb54Env8, cells]
  exact h

theorem lookupName_fb54Env9_and (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {n : BitVec 64} (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (fb54Env9 env v gate) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [fb54Env9, fb54Env1, fb54Env2, fb54Env3, fb54Env4, fb54Env5,
    fb54Env6, fb54Env7, fb54Env8, cells]
  exact h

theorem lookupName_fb54Env9_shr' (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {n : BitVec 64} (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (fb54Env9 env v gate) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [fb54Env9, fb54Env1, fb54Env2, fb54Env3, fb54Env4, fb54Env5,
    fb54Env6, fb54Env7, fb54Env8, cells]
  exact h

/-- The DFA arm's key list omits the entry's five cells. -/
theorem not_mem_ift90Keys_n : ("%n" : String) ∉ ift90Keys := by decide
theorem not_mem_ift90Keys_conv : ("%conv" : String) ∉ ift90Keys := by decide
theorem not_mem_ift90Keys_arm : ("%arm" : String) ∉ ift90Keys := by decide
theorem not_mem_ift90Keys_and : ("%and" : String) ∉ ift90Keys := by decide
theorem not_mem_ift90Keys_shr : ("%shr" : String) ∉ ift90Keys := by decide

theorem lookupName_ifThen90Out_n (env : Env) (v : IfThen90Values) {n : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (ifThen90Out env v) "%n" = some (.int 64 n) :=
  lookupName_ifThen90Out_of (n := "%n") (val := .int 64 n) env v
    (fun k hk he => not_mem_ift90Keys_n (he ▸ hk)) h

theorem lookupName_ifThen90Out_conv (env : Env) (v : IfThen90Values)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifThen90Out env v) "%conv" = some (.int 32 conv) :=
  lookupName_ifThen90Out_of (n := "%conv") (val := .int 32 conv) env v
    (fun k hk he => not_mem_ift90Keys_conv (he ▸ hk)) h

theorem lookupName_ifThen90Out_arm (env : Env) (v : IfThen90Values)
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifThen90Out env v) "%arm" = some (.int 64 arm) :=
  lookupName_ifThen90Out_of (n := "%arm") (val := .int 64 arm) env v
    (fun k hk he => not_mem_ift90Keys_arm (he ▸ hk)) h

theorem lookupName_ifThen90Out_and (env : Env) (v : IfThen90Values) {n : BitVec 64}
    (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (ifThen90Out env v) "%and" = some (.int 64 (n &&& 63)) :=
  lookupName_ifThen90Out_of (n := "%and") (val := .int 64 (n &&& 63)) env v
    (fun k hk he => not_mem_ift90Keys_and (he ▸ hk)) h

theorem lookupName_ifThen90Out_shr (env : Env) (v : IfThen90Values) {n : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (ifThen90Out env v) "%shr" = some (.int 64 (n >>> 6)) :=
  lookupName_ifThen90Out_of (n := "%shr") (val := .int 64 (n >>> 6)) env v
    (fun k hk he => not_mem_ift90Keys_shr (he ▸ hk)) h

theorem lookupName_ifEnd93Env_n (env : Env) (u8k : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (ifEnd93Env env u8k) "%n" = some (.int 64 n) := by
  simp only [ifEnd93Env, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd93Env_conv (env : Env) (u8k : List (BitVec 64))
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd93Env env u8k) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd93Env, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd93Env_arm (env : Env) (u8k : List (BitVec 64))
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifEnd93Env env u8k) "%arm" = some (.int 64 arm) := by
  simp only [ifEnd93Env, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd93Env_and (env : Env) (u8k : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (ifEnd93Env env u8k) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [ifEnd93Env, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd93Env_shr (env : Env) (u8k : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (ifEnd93Env env u8k) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [ifEnd93Env, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifThen96Out_n (env : Env) (a2 a3 : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (ifThen96Out env a2 a3) "%n" = some (.int 64 n) := by
  simp only [ifThen96Out, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifThen96Out_conv (env : Env) (a2 a3 : List (BitVec 64))
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifThen96Out env a2 a3) "%conv" = some (.int 32 conv) := by
  simp only [ifThen96Out, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifThen96Out_arm (env : Env) (a2 a3 : List (BitVec 64))
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifThen96Out env a2 a3) "%arm" = some (.int 64 arm) := by
  simp only [ifThen96Out, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifThen96Out_and (env : Env) (a2 a3 : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (ifThen96Out env a2 a3) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [ifThen96Out, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifThen96Out_shr (env : Env) (a2 a3 : List (BitVec 64))
    {n : BitVec 64} (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (ifThen96Out env a2 a3) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [ifThen96Out, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_forBody54LrPhEnv_n (env : Env) (arm : BitVec 64) (conv : BitVec 32)
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (forBody54LrPhEnv env arm conv) "%n" = some (.int 64 n) := by
  simp only [forBody54LrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_forBody54LrPhEnv_conv' (env : Env) (arm : BitVec 64)
    (conv : BitVec 32) {conv' : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv')) :
    lookupName (forBody54LrPhEnv env arm conv) "%conv" = some (.int 32 conv') := by
  simp only [forBody54LrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_forBody54LrPhEnv_arm' (env : Env) (arm : BitVec 64)
    (conv : BitVec 32) {arm' : BitVec 64}
    (h : lookupName env "%arm" = some (.int 64 arm')) :
    lookupName (forBody54LrPhEnv env arm conv) "%arm" = some (.int 64 arm') := by
  simp only [forBody54LrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_forBody54LrPhEnv_and (env : Env) (arm : BitVec 64)
    (conv : BitVec 32) {n : BitVec 64}
    (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (forBody54LrPhEnv env arm conv) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [forBody54LrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_forBody54LrPhEnv_shr (env : Env) (arm : BitVec 64)
    (conv : BitVec 32) {n : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (forBody54LrPhEnv env arm conv) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [forBody54LrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd98Env_n (env : Env) (i shr : BitVec 64)
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (ifEnd98Env env i shr) "%n" = some (.int 64 n) := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd98Env_conv (env : Env) (i shr : BitVec 64)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd98Env env i shr) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd98Env_arm (env : Env) (i shr : BitVec 64)
    {arm : BitVec 64} (h : lookupName env "%arm" = some (.int 64 arm)) :
    lookupName (ifEnd98Env env i shr) "%arm" = some (.int 64 arm) := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd98Env_and (env : Env) (i shr : BitVec 64)
    {n : BitVec 64} (h : lookupName env "%and" = some (.int 64 (n &&& 63))) :
    lookupName (ifEnd98Env env i shr) "%and" = some (.int 64 (n &&& 63)) := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_ifEnd98Env_shr (env : Env) (i shr : BitVec 64)
    {n : BitVec 64} (h : lookupName env "%shr" = some (.int 64 (n >>> 6))) :
    lookupName (ifEnd98Env env i shr) "%shr" = some (.int 64 (n >>> 6)) := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The cells through each builder -/

theorem entryCells_fb54Env9 (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fb54Env9 env v gate) n conv arm :=
  { n_cell := lookupName_fb54Env9_n env v gate h.n_cell
    conv_cell := lookupName_fb54Env9_conv env v gate h.conv_cell
    arm_cell := lookupName_fb54Env9_arm env v gate h.arm_cell
    and_cell := lookupName_fb54Env9_and env v gate h.and_cell
    shr_cell := lookupName_fb54Env9_shr' env v gate h.shr_cell }

theorem entryCells_fusedE3 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fusedE3 env c gate bs73 bs74) n conv arm :=
  entryCells_fb54Env9 env (fusedValues c bs73 bs74) gate h

theorem entryCells_ifThen90Out (env : Env) (v : IfThen90Values)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifThen90Out env v) n conv arm :=
  { n_cell := lookupName_ifThen90Out_n env v h.n_cell
    conv_cell := lookupName_ifThen90Out_conv env v h.conv_cell
    arm_cell := lookupName_ifThen90Out_arm env v h.arm_cell
    and_cell := lookupName_ifThen90Out_and env v h.and_cell
    shr_cell := lookupName_ifThen90Out_shr env v h.shr_cell }

theorem entryCells_fusedDfaEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      n conv arm :=
  entryCells_ifThen90Out _ (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
    (entryCells_fusedE3 env c gate bs73 bs74 h)

theorem entryCells_ifEnd93Env (env : Env) (u8k : List (BitVec 64))
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifEnd93Env env u8k) n conv arm :=
  { n_cell := lookupName_ifEnd93Env_n env u8k h.n_cell
    conv_cell := lookupName_ifEnd93Env_conv env u8k h.conv_cell
    arm_cell := lookupName_ifEnd93Env_arm env u8k h.arm_cell
    and_cell := lookupName_ifEnd93Env_and env u8k h.and_cell
    shr_cell := lookupName_ifEnd93Env_shr env u8k h.shr_cell }

theorem entryCells_ifThen96Out (env : Env) (a2 a3 : List (BitVec 64))
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifThen96Out env a2 a3) n conv arm :=
  { n_cell := lookupName_ifThen96Out_n env a2 a3 h.n_cell
    conv_cell := lookupName_ifThen96Out_conv env a2 a3 h.conv_cell
    arm_cell := lookupName_ifThen96Out_arm env a2 a3 h.arm_cell
    and_cell := lookupName_ifThen96Out_and env a2 a3 h.and_cell
    shr_cell := lookupName_ifThen96Out_shr env a2 a3 h.shr_cell }

theorem entryCells_fusedE9 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fusedE9 env c gate bs73 bs74) n conv arm :=
  entryCells_ifEnd93Env _ c.u8k (entryCells_fusedE3 env c gate bs73 bs74 h)

theorem entryCells_fusedE96 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fusedE96 env c gate bs73 bs74) n conv arm :=
  entryCells_ifThen96Out _ (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
    (entryCells_fusedE9 env c gate bs73 bs74 h)

theorem entryCells_fusedDfaLatchEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      n conv arm :=
  entryCells_ifEnd93Env _
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
    (entryCells_fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 h)

theorem entryCells_fusedDfaEscapedLatchEnv (env : Env) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells
      (fusedDfaEscapedLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      n conv arm :=
  entryCells_ifThen96Out _
    (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
    (entryCells_fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 h)

theorem entryCells_ifEnd98Env (env : Env) (i shr : BitVec 64)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifEnd98Env env i shr) n conv arm :=
  { n_cell := lookupName_ifEnd98Env_n env i shr h.n_cell
    conv_cell := lookupName_ifEnd98Env_conv env i shr h.conv_cell
    arm_cell := lookupName_ifEnd98Env_arm env i shr h.arm_cell
    and_cell := lookupName_ifEnd98Env_and env i shr h.and_cell
    shr_cell := lookupName_ifEnd98Env_shr env i shr h.shr_cell }

theorem entryCells_forBody54LrPhEnv (env : Env) (arm : BitVec 64) (conv : BitVec 32)
    {n : BitVec 64} {conv' : BitVec 32} {arm' : BitVec 64}
    (h : EntryCells env n conv' arm') :
    EntryCells (forBody54LrPhEnv env arm conv) n conv' arm' :=
  { n_cell := lookupName_forBody54LrPhEnv_n env arm conv h.n_cell
    conv_cell := lookupName_forBody54LrPhEnv_conv' env arm conv h.conv_cell
    arm_cell := lookupName_forBody54LrPhEnv_arm' env arm conv h.arm_cell
    and_cell := lookupName_forBody54LrPhEnv_and env arm conv h.and_cell
    shr_cell := lookupName_forBody54LrPhEnv_shr env arm conv h.shr_cell }

/-! ### The loop's invariant and terminal with the entry's cells -/

/-- **The loop head's invariant with the entry's cells.** -/
structure FusedInvCells (env : Env) (s : State) (c : FusedCarry)
    (gate esc : BitVec 1) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64) : Prop
    extends FusedInv env s c gate esc where
  /-- The document's length. -/
  n_cell : lookupName env "%n" = some (.int 64 n)
  /-- The caller's 32-bit word. -/
  conv_cell : lookupName env "%conv" = some (.int 32 conv)
  /-- The escape arm. -/
  arm_cell : lookupName env "%arm" = some (.int 64 arm)
  /-- The entry's partial-block word. -/
  and_cell : lookupName env "%and" = some (.int 64 (n &&& 63))
  /-- The entry's whole-block count. -/
  shr_cell : lookupName env "%shr" = some (.int 64 (n >>> 6))

/-- The cells of a rich loop invariant. -/
theorem FusedInvCells.entryCells {env : Env} {s : State} {c : FusedCarry}
    {gate esc : BitVec 1} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : FusedInvCells env s c gate esc n conv arm) : EntryCells env n conv arm :=
  { n_cell := h.n_cell, conv_cell := h.conv_cell, arm_cell := h.arm_cell,
    and_cell := h.and_cell, shr_cell := h.shr_cell }

/-- The cells of a rich phase invariant. -/
theorem AsciiInvCells.entryCells {env : Env} {s : State} {c : AsciiCarry}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : AsciiInvCells env s c b n conv arm) : EntryCells env n conv arm :=
  { n_cell := h.n_cell, conv_cell := h.conv_cell, arm_cell := h.arm_cell,
    and_cell := h.and_cell, shr_cell := h.shr_cell }

/-- **The fused loop's terminal, with the entry's cells.**  The bound's exit at
`for.end101`, at an environment that carries the entry's five cells. -/
inductive FusedTermCells (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64) :
    State → Prop where
  | exit (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1) :
      EntryCells env n conv arm → c.ascii.length = 4 → FusedExit env s c →
      FusedTermCells n conv arm (stateAt env s)

/-- Every cells-carrying loop terminal is the loop's terminal. -/
theorem FusedTermCells.toTerm {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    {e : State} (h : FusedTermCells n conv arm e) : FusedTerm e := by
  cases h with
  | exit env s c gate esc hcells hascii hexit => exact FusedTerm.exit env s c hexit
/-! ### One page, with the cells

`fusedInv_page`'s four arms, each with the entry's cells carried through the
branch's own environment.  The page's successor environment is the arm's, so the
cells are read at the builder that arm wrote. -/

/-- **One page, with the entry's cells.**  From the head's rich invariant, one
page reaches the latch's invariant with the entry's cells at the arm's
environment, in at most four control steps. -/
theorem fusedInvCells_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (bs73 bs74 : List UInt8) (doc : Nat → List UInt8)
    (hinv : FusedInvCells env s c gate escBit n conv arm)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (r : CallOutcome)
    (hc : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r)
    (hkeepDoc : ∀ j, j < c.shr.toNat →
      readBytes r.mem (c.b + 64 * j) 64 = some (doc j))
    (hkeepZero : readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (env' : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 4 ∧
      (∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt env' core)) ∧
      FusedLatch env' core c.i c' gate escBit ∧
      EntryCells env' n conv arm ∧
      c'.b = c.b ∧ c'.ent = c.ent ∧ c'.xp = c.xp ∧ c'.nxp = c.nxp ∧
      c'.xcarry = c.xcarry ∧ c'.shr = c.shr ∧
      (∀ j, j < c.shr.toNat → readBytes c'.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] := by
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hwin : FusedWindows c.mem c.b c.shr.toNat c.i doc :=
    fused_windows c.mem c.b c.shr.toNat c.i doc hb3 hi hzero hdoc
  rcases BlockEval.bitVec1_eq_zero_or_one (fb54Select gate (fusedValues c bs73 bs74).v107)
    with hdec | hdec
  · -- the DFA arm
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · subst he
      obtain ⟨h01, h12, h23, h34, hl⟩ := fused_dfa_escape_page sel env s c gate bs73 bs74
        hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
        hinv.toFusedInv hshr57 hb3 hgap hread73 hread74 hdec
        hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r hc
      exact ⟨fusedDfaEscapedLatchEnv env c gate bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43
          hwin.bs57 hwin.bs58 hwin.bs59, _, _, 4, by omega,
        fun j => runFuel_jump4 h01 h12 h23 h34 j, hl,
        entryCells_fusedDfaEscapedLatchEnv env c gate bs73 bs74 hwin.bs41 hwin.bs42
          hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59 hinv.entryCells,
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · subst he
      obtain ⟨h01, h12, h23, hl⟩ := fused_dfa_skip_page sel env s c gate bs73 bs74
        hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
        hinv.toFusedInv hshr57 hb3 hgap hread73 hread74 hdec
        hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 doc hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨fusedDfaLatchEnv env c gate bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43
          hwin.bs57 hwin.bs58 hwin.bs59, _, _, 3, by omega,
        fun j => runFuel_jump3 h01 h12 h23 j, hl,
        entryCells_fusedDfaLatchEnv env c gate bs73 bs74 hwin.bs41 hwin.bs42 hwin.bs43
          hwin.bs57 hwin.bs58 hwin.bs59 hinv.entryCells,
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩
  · -- the merge
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · subst he
      obtain ⟨h01, h12, h23, hl⟩ := fused_merge_escape_page sel env s c gate bs73 bs74
        hinv.toFusedInv hshr57 hread73 hread74 hdec r hc
      exact ⟨fusedE96 env c gate bs73 bs74, _, _, 3, by omega,
        fun j => runFuel_jump3 h01 h12 h23 j, hl,
        entryCells_fusedE96 env c gate bs73 bs74 hinv.entryCells,
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · subst he
      obtain ⟨h01, h12, hl⟩ := fused_merge_skip_page sel env s c gate bs73 bs74
        hinv.toFusedInv hshr57 hread73 hread74 hdec
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 doc hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨fusedE9 env c gate bs73 bs74, _, _, 2, by omega,
        fun j => runFuel_jump2 h01 h12 j, hl,
        entryCells_fusedE9 env c gate bs73 bs74 hinv.entryCells,
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩
/-! ### The loop's run, with the cells

`fusedInv_runFuel_aux`'s induction with the successor's environment named: the
latch's own step adds `ifEnd98Env`, whose cells are the arm's.  The terminal is
`FusedTermCells`, so the exit's block reads the entry's five cells. -/

/-- **The loop's run, with the entry's cells.**  From the head's rich invariant,
the run at the escape selection reaches the bound's exit in at most five control
steps per remaining row plus five, at an environment that carries the entry's
five cells. -/
theorem fusedInvCells_runFuel_aux (sel : Calls) :
    ∀ (r : Nat) (env : Env) (s : State) (c : FusedCarry)
      (gate escBit : BitVec 1) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
      (doc : Nat → List UInt8),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      FusedInvCells env s c gate escBit n conv arm →
      3 ≤ c.b →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) →
      readBytes c.mem (c.b - 3) 3 = some [0, 0, 0] →
      (∀ (args : List Value) (mem : Mem) (next : Nat),
        ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) →
      (∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat) (r : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
        (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
        readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) →
      ∃ (e : State) (j : Nat), j ≤ 5 * r + 5 ∧ FusedTermCells n conv arm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e
  | 0, env, s, c, gate, escBit, n, conv, arm, doc, hmeasure, hshr57, hinv, hb3, hgap,
    hdoc, hzero, hcall, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        omega
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsucc]
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 = some (doc c.i.toNat) :=
        hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32 (by
        rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hc⟩ := hcall _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep _ _ _ _ _ _ rc hc
      obtain ⟨env', core, c', k, hk, hrun, hl, hcells, hb', he', hxp', hnxp', hxc',
        hshr', hdoc', hzero'⟩ :=
        fusedInvCells_page sel env s c gate escBit n conv arm ((doc c.i.toNat).take 32)
          ((doc c.i.toNat).drop 32) doc hinv hshr57 hb3 hgap hdoc hzero
          hread73 hread74 rc hc hkeepDoc hkeepZero
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 1 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).1.mpr hbound
      obtain ⟨hstep, hexit⟩ := fused_latch_exit sel env' core c.i c' gate escBit hl hbit
      refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }, k + 1, by omega,
        FusedTermCells.exit (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.end101", pre := some "if.end98" }) c' gate escBit
          (entryCells_ifEnd98Env env' c.i c'.shr hcells) hl.ascii_len hexit,
        fun j => ?_⟩
      rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
        runFuel_jump_prefix hstep j]
  | r + 1, env, s, c, gate, escBit, n, conv, arm, doc, hmeasure, hshr57, hinv, hb3,
    hgap, hdoc, hzero, hcall, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        omega
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsucc] at hcongr
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 = some (doc c.i.toNat) :=
        hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32 (by
        rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hc⟩ := hcall _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep _ _ _ _ _ _ rc hc
      obtain ⟨env', core, c', k, hk, hrun, hl, hcells, hb', he', hxp', hnxp', hxc',
        hshr', hdoc', hzero'⟩ :=
        fusedInvCells_page sel env s c gate escBit n conv arm ((doc c.i.toNat).take 32)
          ((doc c.i.toNat).drop 32) doc hinv hshr57 hb3 hgap hdoc hzero
          hread73 hread74 rc hc hkeepDoc hkeepZero
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 0 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      obtain ⟨hstep, hinv'⟩ :=
        fused_latch_loop sel env' core c.i c' gate escBit hl hbit
          (by rw [hshr']; exact hshr57)
      have hmeasure' : c'.shr.toNat - (c'.i.toNat + 1) = r := by
        rw [hshr', hl.succ, hsucc]
        omega
      have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
        rw [hb', he', hshr']; exact hgap
      have hb3' : 3 ≤ c'.b := by rw [hb']; exact hb3
      have hkeepUpd : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r' : CallOutcome),
          sel escapeListCallee
            [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
             .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
          (∀ j, j < c'.shr.toNat →
              readBytes r'.mem (c'.b + 64 * j) 64 = some (doc j)) ∧
          readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
        intro or14 mask xs i mem next r' hc'
        have h := hkeep or14 mask xs i mem next r' (by
          simpa only [hb', he', hxp', hnxp', hxc', hshr'] using hc')
        simpa only [hb', he', hxp', hnxp', hxc', hshr'] using h
      have hcells' : EntryCells (ifEnd98Env env' c.i c'.shr) n conv arm :=
        entryCells_ifEnd98Env env' c.i c'.shr hcells
      obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
        fusedInvCells_runFuel_aux sel r (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.body54", pre := some "if.end98" })
          c' gate escBit n conv arm doc hmeasure'
          (by rw [hshr']; exact hshr57)
          { toFusedInv := hinv'
            n_cell := hcells'.n_cell
            conv_cell := hcells'.conv_cell
            arm_cell := hcells'.arm_cell
            and_cell := hcells'.and_cell
            shr_cell := hcells'.shr_cell }
          hb3' hgap'
          (by simpa only [hb', hshr'] using hdoc')
          (by simpa only [hb'] using hzero') hcall hkeepUpd
      refine ⟨e', (k + 1) + j, by omega, hterm, fun k' => ?_⟩
      rw [show (k + 1) + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's run from the head, with the entry's cells.**  The auxiliary form
at the head's own measure. -/
theorem fusedInvCells_runFuel (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (doc : Nat → List UInt8)
    (hshr57 : c.shr.toNat < 2 ^ 57) (hinv : FusedInvCells env s c gate escBit n conv arm)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat) (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      FusedTermCells n conv arm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e :=
  fusedInvCells_runFuel_aux sel (c.shr.toNat - (c.i.toNat + 1)) env s c gate escBit n conv
    arm doc rfl hshr57 hinv hb3 hgap hdoc hzero hcall hkeep
/-! ### The exits, with their cells discharged

`s1BlocksAsciiExit_run` and `s1BlocksFusedExit_run` take the exit's block reads as
hypotheses.  The cells bundle supplies them: `%n`, `%conv`, `%arm`, `%and`, and
the bound's relation by injection from `%shr`.  What remains is the model's own
carries — the document window, the peel's reads, the verdict staging and the
loop's register-to-model identities — which are named in the hypotheses below. -/

/-- **The bound's exit to the return, from the running environment.**  The phase's
terminal at `for.end101` runs to the return on either of the block's arms, and
the post's verdict clause is read off the staging. -/
theorem asciiExitCells_run {esc : Calls} (env : Env) (s : State) (c : AsciiCarry)
    (b : Nat) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (bs : List UInt8) (nb : Nat) (g : Bool)
    (hinv : AsciiInvCells env s c b n conv arm) (hbound : c.i + 1 = c.shr)
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hread : readBytes c.mem c.b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hbs63 : bs.length < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧
      1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8, ∃ p : Nat,
      readBytes s.mem p 1 = some [last] ∧ p = c.b + (n.signExtend 64).toNat - 1)
    (hsilent : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS (n &&& 63) c.shr c.ent conv 1 →
      lookupName (ifThen103Out (peelEntryEnv env c (n &&& 63)) v) "%or.cond191"
        = some (.int 1 1))
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb g (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS (n &&& 63) c.shr c.ent conv 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb g
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstageByte : ∀ (last : UInt8) (p : Nat),
      readBytes s.mem p 1 = some [last] →
      VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length nb g
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0 |||
          lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction (asciiExitState env s c) =
        some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  have hshrEq : c.shr = n >>> 6 := by
    have h := hinv.bound.symm.trans hinv.shr_cell
    injection h with h'
    injection h' with h''
  have hgateZero : arm &&& 2 = 0 := (evalICmp_eq_one_iff (arm &&& 2) 0).mp hgate
  exact s1BlocksAsciiExit_run env s c bs nb g arm n (n &&& 63) conv
    hinv.toAsciiInv hread hbs hshrEq hinv.and_cell hinv.n_cell hinv.conv_cell
    hinv.arm_cell hgateZero rfl hbs63 hnonzero hlast hsilent hstage hstagePeel
    (fun last hr => hstageByte last (c.b + (n.signExtend 64).toNat - 1) hr)

/-- **The fused loop's exit to the return, from the running environment.**  The
loop's terminal at `for.end101` runs to the return; the exit's cells are the
terminal's own environment's. -/
theorem fusedExitCells_run {esc : Calls} (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (bs : List UInt8) (nb : Nat) (g : Bool) (bs136 bs137 : List UInt8)
    (hexit : FusedExit env s c) (hcells : EntryCells env n conv arm)
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hasciilen : c.ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshr63 : c.shr.toNat < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧
      1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8,
      readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last])
    (hsilent : ∀ (v : IfThen103Values), v = fusedPeelValues env c n (n &&& 63)
        bs136 bs137 conv →
      lookupName (ifThen103Out
        (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15
          (n &&& 63)) v) "%or.cond191" = some (.int 1 1))
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb g
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = fusedPeelValues env c n (n &&& 63)
        bs136 bs137 conv →
      VerdictStaging v.or279 c.u8k bs bs.length nb g
        (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstageByte : ∀ (last : UInt8) (p : Nat),
      readBytes s.mem p 1 = some [last] →
      VerdictStaging c.ascii c.u8k bs bs.length nb g
        (evalICmp .eq (ptestzU8k c.u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (N : Nat) (r : BitVec 64) (m : Mem),
      runFuel (s1BlocksCallsEsc esc) N s1BlocksFunction (stateAt env s) =
        some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  have hgateZero : arm &&& 2 = 0 := (evalICmp_eq_one_iff (arm &&& 2) 0).mp hgate
  exact s1BlocksFusedExit_run env s c (n &&& 63) n conv bs136 bs137 bs nb g arm
    hexit hcells.and_cell hcells.n_cell hexit.base hcells.conv_cell hcells.arm_cell
    hasciilen hpos h136 h137 hshr63 hnonzero hlast hgateZero hsilent hstage
    hstagePeel
    (fun last hr => hstageByte last (c.b + (n.signExtend 64).toNat - 1) hr)
/-! ### The hand-off's environment builders

The hand-off terminal's environment is `asciiHandoffEnv`; the join `if.end50`
adds `fb54PageEnv` and the preheader adds `forBody54LrPhEnv`.  None of the three
binds the entry's five cells, so they survive the whole hand-off chain. -/

theorem entryCells_forIncEnv (env : Env) (i shr : BitVec 64)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (forIncEnv env i shr) n conv arm :=
  { n_cell := by rw [lookupName_forIncEnv_n]; exact h.n_cell
    conv_cell := by rw [lookupName_forIncEnv_conv]; exact h.conv_cell
    arm_cell := by rw [lookupName_forIncEnv_arm]; exact h.arm_cell
    and_cell := by rw [lookupName_forIncEnv_and]; exact h.and_cell
    shr_cell := by rw [lookupName_forIncEnv_shr]; exact h.shr_cell }

theorem entryCells_forBodyOut (env : Env) (v : ForBodyValues)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (forBodyOut env v) n conv arm :=
  { n_cell := by rw [lookupName_forBodyOut_n]; exact h.n_cell
    conv_cell := by rw [lookupName_forBodyOut_conv]; exact h.conv_cell
    arm_cell := by rw [lookupName_forBodyOut_arm]; exact h.arm_cell
    and_cell := by rw [lookupName_forBodyOut_and]; exact h.and_cell
    shr_cell := by rw [lookupName_forBodyOut_shr]; exact h.shr_cell }

theorem entryCells_ifEndEnv (env : Env) (a2 a3 : List (BitVec 64))
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifEndEnv env a2 a3) n conv arm :=
  { n_cell := by rw [lookupName_ifEndEnv_n]; exact h.n_cell
    conv_cell := by rw [lookupName_ifEndEnv_conv]; exact h.conv_cell
    arm_cell := by rw [lookupName_ifEndEnv_arm]; exact h.arm_cell
    and_cell := by rw [lookupName_ifEndEnv_and]; exact h.and_cell
    shr_cell := by rw [lookupName_ifEndEnv_shr]; exact h.shr_cell }

theorem entryCells_asciiHandoffEnv (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (asciiHandoffEnv env c v) n conv arm :=
  entryCells_ifEndEnv _ v.w2 v.w3 (entryCells_forBodyOut _ v
    (entryCells_forIncEnv env c.i c.shr h))

theorem lookupName_ifThen38Out_n (env : Env) (v : IfThen38Values) :
    lookupName (ifThen38Out env v) "%n" = lookupName env "%n" := by
  ift_lk

theorem lookupName_ifThen38Out_conv (env : Env) (v : IfThen38Values) :
    lookupName (ifThen38Out env v) "%conv" = lookupName env "%conv" := by
  ift_lk

theorem lookupName_ifThen38Out_arm (env : Env) (v : IfThen38Values) :
    lookupName (ifThen38Out env v) "%arm" = lookupName env "%arm" := by
  ift_lk

theorem lookupName_ifThen38Out_and (env : Env) (v : IfThen38Values) :
    lookupName (ifThen38Out env v) "%and" = lookupName env "%and" := by
  ift_lk

theorem lookupName_ifThen38Out_shr (env : Env) (v : IfThen38Values) :
    lookupName (ifThen38Out env v) "%shr" = lookupName env "%shr" := by
  ift_lk

theorem entryCells_ifThen38Out (env : Env) (v : IfThen38Values)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifThen38Out env v) n conv arm :=
  { n_cell := by rw [lookupName_ifThen38Out_n]; exact h.n_cell
    conv_cell := by rw [lookupName_ifThen38Out_conv]; exact h.conv_cell
    arm_cell := by rw [lookupName_ifThen38Out_arm]; exact h.arm_cell
    and_cell := by rw [lookupName_ifThen38Out_and]; exact h.and_cell
    shr_cell := by rw [lookupName_ifThen38Out_shr]; exact h.shr_cell }

theorem entryCells_ifEnd50Out (env : Env) (shr17 st0 st9 st15 : BitVec 64)
    (oii or284 : List (BitVec 64)) (inc49 shr : BitVec 64)
    {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (ifEnd50Out env shr17 st0 st9 st15 oii or284 inc49 shr) n conv arm :=
  { n_cell := lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr
      h.n_cell (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    conv_cell := lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr
      h.conv_cell (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    arm_cell := lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr
      h.arm_cell (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    and_cell := lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr
      h.and_cell (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    shr_cell := lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr
      h.shr_cell (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) }

theorem entryCells_fb54PageEnv (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (h : EntryCells env n conv arm) :
    EntryCells (fb54PageEnv env c v v38) n conv arm :=
  entryCells_ifEnd50Out _ v.shr17 v.shrII v.conv13II v.shrI v38.or291 v38.or284
    v38.inc49 c.shr (entryCells_ifThen38Out _ v38 (entryCells_asciiHandoffEnv env c v h))
/-! ### The first page, with the cells

`entry_first_page` runs the hand-off's preheader and first body pass; the cells
are the page environment's.  Its terminal keeps the environment, so the loop's
cells induction can start from it. -/

/-- **The first page reaches the latch, with the cells.**  The preheader, the
first body pass, the DFA arm and the escape record or its skip reach a
`FusedLatch` with the entry's cells at the latch's environment. -/
theorem entryPageCells_latch (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64) (conv : BitVec 32)
    (bs73 bs74 : List UInt8) (b ent xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (n : BitVec 64) (arm' : BitVec 64)
    (hpc : s.pc = "for.body54.lr.ph")
    (hcellsPage : EntryCells (fb54PageEnv env c v v38) n conv arm')
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 c.shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hi63 : (v38.inc49.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes s.mem
      (b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes s.mem
      ((b + ((v38.inc49 <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : v38.or284.length = 4)
    (hu8k_len : v38.or291.length = 4)
    (hb3 : 3 ≤ b)
    (hzero : readBytes s.mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat → readBytes s.mem (b + 64 * j) 64 = some (doc j))
    (hirow : v38.inc49.toNat < c.shr.toNat)
    (hgap : b + 64 * c.shr.toNat ≤ ent)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
      (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr xp, .ptr nxp, .ptr xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (b - 3) 3 = some [0, 0, 0]) :
    ∃ (envL : Env) (core : State) (c' : FusedCarry) (k : Nat), k ≤ 5 ∧
      FusedLatch envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) ∧
      EntryCells envL n conv arm' ∧ c'.shr = c.shr ∧ c'.b = b ∧ c'.ent = ent ∧
      c'.xp = xp ∧ c'.nxp = nxp ∧ c'.xcarry = xcarry ∧
      (∀ j, j < c.shr.toNat → readBytes c'.mem (b + 64 * j) 64 = some (doc j)) ∧
      readBytes c'.mem (b - 3) 3 = some [0, 0, 0] ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction
        (stateAt (fb54PageEnv env c v v38) s) =
        runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt envL core) := by
  let c0 : FusedCarry := entryCarry c v v38 b ent xp nxp xcarry s.mem
  have hvalues : fusedValues c0 bs73 bs74 = fb54FirstPassValues v v38 bs73 bs74 b ent :=
    rfl
  let env0 : Env := LeanLLVM.Refinement.JsonS1BlocksEntry.entryEnv env c v v38 arm conv
  let s0 : State := { s with pc := "for.body54", pre := some "for.body54.lr.ph" }
  have hcells0 : EntryCells env0 n conv arm' :=
    entryCells_forBody54LrPhEnv (fb54PageEnv env c v v38) arm conv hcellsPage
  have hlr := (for_body54_lr_ph_page env s c v v38 arm conv bs73 bs74 b ent hpc
      (lookupName_fb54PageEnv_arm env c v v38 harm)
      (lookupName_fb54PageEnv_conv env c v v38 hconv) hb hent hi63 hshl63 hread73
      hread74 h73len h74len hascii_len)
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (stateAt (fb54PageEnv env c v v38) s) = .jump (stateAt env0 s0) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt (fb54PageEnv env c v v38) s)
      for_body54_lr_phBlock
      (by rw [show (stateAt (fb54PageEnv env c v v38) s).pc = s.pc from rfl, hpc]
          exact findBlock_for_body54_lr_ph) (by decide)]
    exact hlr.1
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env0 s0) =
      .jump (fusedDfaState env0 s0 c0 (evalICmp .eq conv 0) bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env0 s0) for_body54Block
      (by rw [show (stateAt env0 s0).pc = "for.body54" from rfl]
          exact findBlock_for_body54) (by decide)]
    dsimp only [env0, s0, LeanLLVM.Refinement.JsonS1BlocksEntry.entryEnv]
    rw [hlr.2]
    rfl
  have hw : FusedWindows s.mem b c.shr.toNat v38.inc49 doc :=
    fused_windows s.mem b c.shr.toNat v38.inc49 doc hb3 hirow hzero hdoc
  have h41 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 1) 32 = some hw.bs41 := hw.w41
  have h42 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 2) 32 = some hw.bs42 := hw.w42
  have h43 : readBytes c0.mem (c0.b + 64 * c0.i.toNat - 3) 32 = some hw.bs43 := hw.w43
  have h57 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 31) 32 = some hw.bs57 := hw.w57
  have h58 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 30) 32 = some hw.bs58 := hw.w58
  have h59 : readBytes c0.mem (c0.b + 64 * c0.i.toNat + 29) 32 = some hw.bs59 := hw.w59
  have harmCells : EntryArm env0 c0 :=
    { index_lt := hirow
      ascii_len := hascii_len
      u8k_len := hu8k_len
      base := lookupName_entryEnv_b env c v v38 arm conv hb
      emit := lookupName_entryEnv_ent env c v v38 arm conv hent
      bound := lookupName_entryEnv_shr env c v v38 arm conv hshr
      stream := lookupName_entryEnv_xp env c v v38 arm conv hxp
      count := lookupName_entryEnv_nxp env c v v38 arm conv hnxp
      carry := lookupName_entryEnv_xcarry env c v v38 arm conv hxcarry }
  have hgate : lookupName env0 "%tobool87" = some (.int 1 (evalICmp .eq conv 0)) :=
    lookupName_entryEnv_gate env c v v38 arm conv
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (arm &&& 2) 0) with hesc | hesc
  · -- the escape record runs
    obtain ⟨r, hc⟩ := hcall
      [.int 64 (fusedValues c0 bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c0 bs73 bs74).w73
         (fusedValues c0 bs73 bs74).w74),
       .int 64 (fusedValues c0 bs73 bs74).xorI, .int 64 c0.i,
       .ptr c0.xp, .ptr c0.nxp, .ptr c0.xcarry]
      (fusedStore c0 bs73 bs74) s0.next
    have hescape : lookupName env0 "%tobool95.not" = some (.int 1 0) := by
      simpa only [hesc] using lookupName_entryEnv_escape env c v v38 arm conv
    obtain ⟨h23, h34, h45, hl⟩ := entry_dfa_escape_arm sel env0 s0 c0
      (evalICmp .eq conv 0) bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59
      harmCells hgate hescape hshr57 hb3 hgap h41 h42 h43 h57 h58 h59 r hc
    refine ⟨fusedDfaEscapedLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59,
      fusedDfaEscapedLatchCore s0 c0 bs73 bs74 r,
      fusedNext c0 bs73 bs74
        (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59).or281
        r.mem, 5, by omega, ?_,
      entryCells_fusedDfaEscapedLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59 hcells0,
      rfl, rfl, rfl, rfl, rfl, rfl,
      (hkeep _ _ _ _ _ _ _ hc).1, (hkeep _ _ _ _ _ _ _ hc).2,
      fun j => ?_⟩
    · rw [hesc]
      simpa only [c0, entryCarry] using hl
    · exact runFuel_jump5 h01 h12 h23 h34 h45 j
  · -- the escape record is skipped
    have hescape : lookupName env0 "%tobool95.not" = some (.int 1 1) := by
      simpa only [hesc] using lookupName_entryEnv_escape env c v v38 arm conv
    obtain ⟨h23, h34, hl⟩ := entry_dfa_skip_arm sel env0 s0 c0 (evalICmp .eq conv 0)
      bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59 harmCells hgate hescape
      hshr57 hb3 hgap h41 h42 h43 h57 h58 h59
    refine ⟨fusedDfaLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59,
      fusedDfaLatchCore s0 c0 bs73 bs74,
      fusedNext c0 bs73 bs74
        (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59).or281
        (fusedStore c0 bs73 bs74), 4, by omega, ?_,
      entryCells_fusedDfaLatchEnv env0 c0 (evalICmp .eq conv 0) bs73 bs74
        hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58 hw.bs59 hcells0,
      rfl, rfl, rfl, rfl, rfl, rfl,
      (by
        have hmem : (fusedNext c0 bs73 bs74
            (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58
              hw.bs59).or281 (fusedStore c0 bs73 bs74)).mem = fusedStore c0 bs73 bs74 :=
          rfl
        intro j hj
        rw [hmem]
        exact readBytes_fusedStore_doc c0 bs73 bs74 doc hgap hdoc j hj),
      (by
        have hmem : (fusedNext c0 bs73 bs74
            (fusedDfa90 c0 bs73 bs74 hw.bs41 hw.bs42 hw.bs43 hw.bs57 hw.bs58
              hw.bs59).or281 (fusedStore c0 bs73 bs74)).mem = fusedStore c0 bs73 bs74 :=
          rfl
        rw [hmem, show b = c0.b from rfl,
          readBytes_fusedStore_zero c0 bs73 bs74 hb3 hgap,
          show c0.mem = s.mem from rfl, show c0.b = b from rfl]
        exact hzero),
      fun j => ?_⟩
    · rw [hesc]
      simpa only [c0, entryCarry] using hl
    · exact runFuel_jump4 h01 h12 h23 h34 j
/-! ### The exits' terminals

`ExitTermCells` is what the bridge reaches: either the phase's own exit at
`for.end101` or the fused loop's.  Both name the environment, so the exit
compositions above consume them. -/

/-- **The exit terminals with the entry's cells.** -/
inductive ExitTermCells (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) : State → Prop where
  | ascii (env : Env) (s : State) (c : AsciiCarry) :
      AsciiInvCells env s c b n conv arm → c.i + 1 = c.shr →
      ExitTermCells b n conv arm (asciiExitState env s c)
  | fused (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1) :
      EntryCells env n conv arm → c.ascii.length = 4 → FusedExit env s c →
      ExitTermCells b n conv arm (stateAt env s)

/-! ### The entry's environment and its cells

The entry block writes `%conv`, `%and` and `%shr` and passes `%n` and `%arm`
through.  The bundle at `entryEnv` below is the bridge's seed. -/

theorem lookupName_entryEnv_conv (env : Env) (n arm : BitVec 64) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%conv"
      = some (.int 32 (entryGate arm)) := by
  simp only [LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

theorem lookupName_entryEnv_and (env : Env) (n arm : BitVec 64) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%and"
      = some (.int 64 (n &&& 63)) := by
  simp only [LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv, cells]
  block_lk_cons

theorem lookupName_entryEnv_n (env : Env) (n arm : BitVec 64) {n' : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 n')) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%n"
      = some (.int 64 n') :=
  lookupName_entryEnv_of (k := "%n") (v := .int 64 n') env n arm h
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem lookupName_entryEnv_arm (env : Env) (n arm : BitVec 64) {arm' : BitVec 64}
    (h : lookupName env "%arm" = some (.int 64 arm')) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%arm"
      = some (.int 64 arm') :=
  lookupName_entryEnv_of (k := "%arm") (v := .int 64 arm') env n arm h
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The entry's cells at the seed environment of the one-prefix bridge. -/
theorem entryCells_entryEnv (env : Env) (n arm : BitVec 64)
    (hn : lookupName env "%n" = some (.int 64 n))
    (harm : lookupName env "%arm" = some (.int 64 arm)) :
    EntryCells (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm)
      n (entryGate arm) arm :=
  { n_cell := lookupName_entryEnv_n env n arm hn
    conv_cell := lookupName_entryEnv_conv env n arm
    arm_cell := lookupName_entryEnv_arm env n arm harm
    and_cell := lookupName_entryEnv_and env n arm
    shr_cell := LeanLLVM.Refinement.JsonS1BlocksRefine.lookupName_entryEnv_shr env n arm }

/-- A control step at `for.body.lr.ph` is the same at either call
environment. -/
theorem step_forBodyLrPh_esc (esc : Calls) (env : Env) (s : State)
    (hpc : s.pc = "for.body.lr.ph") :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      step s1BlocksCalls s1BlocksFunction (stateAt env s) :=
  step_esc_of_free esc s1BlocksFunction (stateAt env s) for_body_lr_phBlock
    (by rw [show (stateAt env s).pc = s.pc from rfl, hpc]
        exact findBlock_for_body_lr_ph) (by decide)
/-! ### The hand-off arm, to the exit

The phase's hand-off terminal stands at `if.then38`.  Two steps reach the fused
loop's preheader, the first page reaches a latch, and the latch either exits or
re-enters the loop; the loop's cells induction then reaches the bound's exit.  The
cells are the hand-off's own, carried through the join, the preheader and the
page. -/

/-- **The hand-off arm reaches the exit.**  From an `AsciiInvCells` hand-off
terminal, the run at the escape selection reaches `for.end101` on one of the two
exit terminals, at an environment that carries the entry's cells. -/
theorem handoffPrefix_exit (sel : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (bs2 bs3 : List UInt8) (doc : Nat → List UInt8)
    (b : Nat) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (xp nxp xcarry : Nat) (bs73 bs74 : List UInt8)
    (hinv : AsciiInvCells env s c b n conv arm)
    (hv : v = asciiValues c bs2 bs3)
    (hread2 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2)
    (hread3 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3)
    (hne : c.i + 1 ≠ c.shr)
    (hbit : evalICmp .ult (v.i + 1) c.shr = 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hb3 : 3 ≤ c.b)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hdocPage : ∀ j, j < c.shr.toNat →
      readBytes (asciiHandoffState env s c v).mem (c.b + 64 * j) 64 = some (doc j))
    (hzeroPage : readBytes (asciiHandoffState env s c v).mem (c.b - 3) 3 = some [0, 0, 0])
    (hirow : (v.i + 1).toNat < c.shr.toNat)
    (hi63 : ((v.i + 1).signExtend 64).toNat < 2 ^ 63)
    (hshl63 : (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes (asciiHandoffState env s c v).mem
      (c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes (asciiHandoffState env s c v).mem
      ((c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : (ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)).or284.length = 4)
    (hu8k_len : (ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)).or291.length = 4)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
      (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr xp, .ptr nxp, .ptr xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    let v38 := ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)
    let sH := asciiHandoffState env s c v
    let s4 := stateAt (ifThen38Out (asciiHandoffEnv env c v) v38)
      { sH with pc := "if.end50", pre := some "if.then38" }
    let s5 := stateAt (fb54PageEnv env c v v38)
      { s4 with pc := "for.body54.lr.ph", pre := some "if.end50" }
    ∃ (e : State) (N : Nat),
      (∀ k, runFuel (s1BlocksCallsEsc sel) (N + k) s1BlocksFunction sH =
        runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) ∧
      ExitTermCells b n conv arm e := by
  intro v38 sH s4 s5
  obtain ⟨h01, h12⟩ := asciiHandoff_run env s c v bs2 bs3 doc hinv.toAsciiInv hv
    hread2 hread3 hshr57 hne hgap hdoc hbit
  have h01' : step (s1BlocksCallsEsc sel) s1BlocksFunction sH = .jump s4 := by
    rw [step_esc_of_free sel s1BlocksFunction sH if_then38Block
      (by rw [show sH.pc = "if.then38" from rfl]; exact findBlock_if_then38) (by decide)]
    exact h01
  have h12' : step (s1BlocksCallsEsc sel) s1BlocksFunction s4 = .jump s5 := by
    rw [step_esc_of_free sel s1BlocksFunction s4 if_end50Block
      (by rw [show s4.pc = "if.end50" from rfl]; exact findBlock_if_end50) (by decide)]
    exact h12
  have hcellsPage : EntryCells (fb54PageEnv env c v v38) n conv arm :=
    entryCells_fb54PageEnv env c v v38 hinv.entryCells
  obtain ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', hrun⟩ :=
    entryPageCells_latch sel env s5 c v v38 arm conv bs73 bs74 c.b c.ent xp nxp
      xcarry doc n arm rfl hcellsPage hinv.arm_cell hinv.conv_cell hinv.base
      hinv.emit hinv.bound hxp hnxp hxcarry hi63 hshl63 hread73
      hread74 h73len h74len hascii_len hu8k_len hb3 hzeroPage hdocPage
      hirow
      hgap hshr57 hcall hkeep
  have hrun5 : ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction s5 =
      runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt envL core) :=
    fun j => hrun j
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (v38.inc49 + 1) c'.shr)
    with hbitL | hbitL
  · -- the back edge and the loop's own induction
    obtain ⟨hstep, hinv'⟩ :=
      fused_latch_loop sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbitL (by rw [hshrEq]; exact hshr57)
    have hcells' : EntryCells (ifEnd98Env envL (v38.inc49) c'.shr) n conv arm :=
      entryCells_ifEnd98Env envL (v38.inc49) c'.shr hcellsL
    have hshr57' : c'.shr.toNat < 2 ^ 57 := by rw [hshrEq]; exact hshr57
    have hb3' : 3 ≤ c'.b := by rw [hbEq]; exact hb3
    have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
      rw [hbEq, hshrEq, hentEq]; exact hgap
    have hdocLoop : ∀ j, j < c'.shr.toNat →
        readBytes c'.mem (c'.b + 64 * j) 64 = some (doc j) := by
      intro j hj
      rw [hshrEq] at hj
      rw [hbEq]
      exact hdoc' j hj
    have hzeroLoop : readBytes c'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
      rw [hbEq]; exact hzero'
    have hkeepLoop : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r' : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
        (∀ j, j < c'.shr.toNat →
            readBytes r'.mem (c'.b + 64 * j) 64 = some (doc j)) ∧
        readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
      intro or14 mask xs i mem next r' hc'
      have h := hkeep or14 mask xs i mem next r' (by
        simpa only [hxpEq, hnxpEq, hxcEq] using hc')
      simpa only [hbEq, hshrEq] using h
    obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
      fusedInvCells_runFuel sel (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.body54", pre := some "if.end98" })
        c' (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0) n conv arm doc
        hshr57'
        { toFusedInv := hinv'
          n_cell := hcells'.n_cell
          conv_cell := hcells'.conv_cell
          arm_cell := hcells'.arm_cell
          and_cell := hcells'.and_cell
          shr_cell := hcells'.shr_cell }
        hb3' hgap' hdocLoop hzeroLoop hcall hkeepLoop
    rcases hterm with ⟨envE, sE, cE, gateE, escE, hcellsE, hasciiE, hexitE⟩
    exact ⟨_, 2 + (k + (1 + j)),
      fun k' => by
        rw [show 2 + (k + (1 + j)) + k' = 2 + (k + (1 + (j + k'))) from by omega,
          runFuel_jump2 h01' h12' (k + (1 + (j + k'))), hrun5 (1 + (j + k')),
          runFuel_jump_prefix hstep (j + k')]
        exact hrun' k',
      ExitTermCells.fused envE sE cE gateE escE hcellsE hasciiE hexitE⟩
  · -- the bound's exit
    obtain ⟨hstep, hexit⟩ :=
      fused_latch_exit sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbitL
    exact ⟨_, 2 + (k + 1),
      (fun k' => by
        rw [show 2 + (k + 1) + k' = 2 + (k + (1 + k')) from by omega,
          runFuel_jump2 h01' h12' (k + (1 + k')), hrun5 (1 + k'),
          runFuel_jump_prefix hstep k']
        rfl),
      ExitTermCells.fused (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }) c'
        (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0)
        (entryCells_ifEnd98Env envL (v38.inc49) c'.shr hcellsL) hl.ascii_len hexit⟩
/-! ### The one-prefix bridge from the entry

The entry's block, the preheader's first pass and the phase's induction compose
into one `runFuel` prefix at the escape selection.  The terminal is
`AsciiTermCells`: the bound's exit carries `ExitTermCells.ascii`'s payload, and
the hand-off carries `handoffPrefix_exit`'s.  Every hypothesis below beyond the
document window is a model carry — the preheader's two word reads, the gate, the
peel's and the page's register facts — not an environment fact. -/

/-- **The entry reaches the phase's terminal.**  From `s1BlocksInit`, on a
document of at least one block, the run at the escape selection reaches a
terminal of the phase whose environment carries the entry's cells. -/
theorem s1BlocksPrefix_terminal (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8)
    (hlong : evalICmp .ult n 64 = 0)
    (hread2 : readBytes mem b 32 = some ((docBlock bs 0).take 32))
    (hread3 : readBytes mem (b + 32) 32 = some ((docBlock bs 0).drop 32))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hfirst : evalICmp .eq (ifEndTest
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w2
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w3) 0 = 0)
    (hgap : b + 64 * (n >>> 6).toNat ≤ ent)
    (hdoc : ∀ j, j < (n >>> 6).toNat →
      readBytes mem (b + 64 * j) 64 = some (doc j))
    (hshr57 : (n >>> 6).toNat < 2 ^ 57) :
    let args := [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm]
    ∃ (e : State) (N : Nat),
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
          (s1BlocksInit args mem) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      AsciiTermCells b n (entryGate arm) arm e := by
  intro args
  let init : State := s1BlocksInit args mem
  let E0 : Env := LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv init.env n arm
  let sLR : State := { init with pc := "for.body.lr.ph", pre := some "entry" }
  have hn : lookupName init.env "%n" = some (.int 64 n) :=
    s1BlocksInit_env_n mem b ent xp nxp xcarry n arm
  have harm : lookupName init.env "%arm" = some (.int 64 arm) :=
    s1BlocksInit_env_arm mem b ent xp nxp xcarry n arm
  have hb0 : lookupName init.env "%b" = some (.ptr b) :=
    s1BlocksInit_env_b mem b ent xp nxp xcarry n arm
  have hent0 : lookupName init.env "%ent" = some (.ptr ent) :=
    s1BlocksInit_env_ent mem b ent xp nxp xcarry n arm
  have hcells0 : EntryCells E0 n (entryGate arm) arm :=
    entryCells_entryEnv init.env n arm hn harm
  have harm0 : lookupName E0 "%arm" = some (.int 64 arm) :=
    lookupName_entryEnv_arm init.env n arm harm
  have hbE0 : lookupName E0 "%b" = some (.ptr b) :=
    lookupName_entryEnv_of (k := "%b") (v := .ptr b) init.env n arm hb0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hentE0 : lookupName E0 "%ent" = some (.ptr ent) :=
    lookupName_entryEnv_of (k := "%ent") (v := .ptr ent) init.env n arm hent0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hshrE0 : lookupName E0 "%shr" = some (.int 64 (n >>> 6)) :=
    LeanLLVM.Refinement.JsonS1BlocksRefine.lookupName_entryEnv_shr init.env n arm
  -- the entry's step
  have hstepEntry : step (s1BlocksCallsEsc esc) s1BlocksFunction init = .jump (stateAt E0 sLR) := by
    exact s1BlocksInit_step_blocks mem b ent xp nxp xcarry n arm hlong
  -- the preheader's first pass
  let v0 : ForBodyValues := forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32)
    ((docBlock bs 0).drop 32) b ent
  let s1' : State := { sLR with pc := "for.body", pre := some "for.body.lr.ph" }
  let s2' : State := { sLR with
    pc := "if.end"
    pre := some "for.body"
    mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  let Eseed : Env := ifEndEnv (forBodyOut (lrPhEnv E0 arm) v0) v0.w2 v0.w3
  let sSeed : State := stateAt Eseed { sLR with
    pc := "for.inc"
    pre := some "if.end"
    mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  obtain ⟨h01, h12, h23⟩ :=
    for_body_lr_ph_page_ascii E0 sLR arm ((docBlock bs 0).take 32)
      ((docBlock bs 0).drop 32) b ent rfl harm0 hgate hbE0 hentE0 hread2 hread3
      hfirst
  have h01' : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt E0 sLR) =
      .jump (stateAt (lrPhEnv E0 arm) s1') := by
    rw [step_forBodyLrPh_esc esc E0 sLR rfl]; exact h01
  have h12' : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (lrPhEnv E0 arm) s1') =
      .jump (stateAt (forBodyOut (lrPhEnv E0 arm) v0) s2') := by
    rw [step_forBody_esc esc (lrPhEnv E0 arm) s1' rfl]
    exact h12
  have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (forBodyOut (lrPhEnv E0 arm) v0) s2') =
      .jump sSeed := by
    rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
  -- the seed invariant
  let c0 : AsciiCarry :=
    { i := v0.i, prevS := v0.shr17, st0 := v0.shrII, st9 := v0.conv13II,
      st15 := v0.shrI, b := b, ent := ent, shr := n >>> 6,
      mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  have hseed : AsciiInvCells Eseed sSeed c0 b n (entryGate arm) arm :=
    asciiInvCells_seed E0 sLR arm ((docBlock bs 0).take 32)
      ((docBlock bs 0).drop 32) b ent (n >>> 6) n (entryGate arm) hcells0 harm0 hgate
      hshrE0 hbE0 hentE0 (by
        rw [ushr_six_toNat]
        have h64 : (64 : BitVec 64).toNat = 64 := by decide
        have hnot : ¬ BitVec.ult n 64 := by
          intro hlt
          have hone : evalICmp .ult n (64 : BitVec 64) = 1 := by
            show BitVec.ofBool (BitVec.ult n 64) = 1
            rw [hlt]; rfl
          rw [hone] at hlong
          exact absurd hlong (by decide)
        rw [BitVec.ult_iff_toNat_lt] at hnot
        rw [h64] at hnot
        omega)
  have hgapSeed : c0.b + 64 * c0.shr.toNat ≤ c0.ent := hgap
  have harr : v0.arrayidx = ent := forBodyValues_zero_arrayidx _ _ b ent
  have hdocSeed : ∀ j, j < c0.shr.toNat →
      readBytes c0.mem (c0.b + 64 * j) 64 = some (doc j) := by
    intro j hj
    have hshr0 : c0.shr = n >>> 6 := rfl
    have hj' : j < (n >>> 6).toNat := by simpa only [hshr0] using hj
    rw [show c0.mem = writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8)
        from rfl, show c0.b = b from rfl]
    rw [readBytes_writeBytes_below sLR.mem (natToBytes v0.or16.toNat 8) 64
      (b + 64 * j) v0.arrayidx (by rw [harr]; omega)]
    exact hdoc j hj'
  obtain ⟨e, j, -, hterm, hfuel⟩ :=
    asciiInvCells_runFuel esc Eseed sSeed c0 b n (entryGate arm) arm doc
      hshr57 hseed hgapSeed hdocSeed
  exact ⟨e, 1 + (3 + j),
    (fun k => by
      rw [show 1 + (3 + j) + k = 1 + (3 + (j + k)) from by omega,
        runFuel_jump_prefix hstepEntry (3 + (j + k)),
        runFuel_jump3 h01' h12' h23' (j + k)]
      exact hfuel k),
    hterm⟩

/-! ### Axiom footprints

The bridge's pieces are the modules' own step lemmas composed by `runFuel`'s
prefix rules and the cells' reads, so they carry `propext`, `Classical.choice`
(the branch splits and the peel's projections) and `Quot.sound`.  No statement
carries `sorryAx`. -/
#print axioms asciiInvCells_seed
#print axioms asciiInvCells_step
#print axioms asciiInvCells_runFuel
#print axioms fusedInvCells_page
#print axioms fusedInvCells_runFuel
#print axioms entryPageCells_latch
#print axioms asciiExitCells_run
#print axioms fusedExitCells_run
#print axioms handoffPrefix_exit
#print axioms s1BlocksPrefix_terminal

end LeanLLVM.Refinement.JsonS1BlocksPrefix
