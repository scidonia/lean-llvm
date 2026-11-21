/-
The stream's cells: the three loop pointers, carried from the entry to the loop.

`JsonS1BlocksPrefix`'s one-prefix bridge reaches the phase's terminal with the
entry's five cells, and `handoffPrefix_exit` runs the hand-off's two steps, the
first page and the fused loop's cells induction to the bound's exit.  The two do
not compose there for one reason: the fused loop's preheader reads `%xp`, `%nxp`
and `%xcarry`, and the phase never does, so `EntryCells` says nothing about them
and the hand-off terminal cannot supply the three lookups the loop's seed needs.

No block of the phase rebinds those three, so they are the same cells at the
entry's environment, at every latch and at the hand-off.  `StreamCells` is that
bundle.  This module carries it through the phase's seed and passes, restates the
phase's terminal with it (`AsciiTermStreamCells`), and joins the hand-off arm with
`handoffPrefix_exit`, yielding the single entry-to-exit run at the escape
selection.  The phase's invariant does not name the emit base, so the window
bound the hand-off's page uses is stated at the loop's own carry and is one of
`HandoffCarries`'s fields.

What remains between this prefix and the refinement is not a step or a cell: the
exit composition's own carries.  The document window at the terminal's memory,
its gap above the emit base, the page's row bound and two word reads, and the
fuse's two four-lane word lists are model facts about the document, and the
escape selection's totality and frame (`hcall`, `hkeep`) are the caller's
selection's; they are `s1BlocksPrefix_exit`'s `hready`, and its conclusion is
`ExitTermCells`, which `JsonS1BlocksRefines`'s exits consume.  Their own staging
family (`hsilent`, `hstage`, `hstagePeel`, `hstageByte`) and the `VerdictPost`
they reach are that module's to supply.
-/
import LeanLLVM.Refinement.JsonS1BlocksPrefix
import LeanLLVM.Refinement.JsonS1BlocksRefines

namespace LeanLLVM.Refinement.JsonS1BlocksStream

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
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The three cells the loop's preheader reads

`%xp`, `%nxp` and `%xcarry` are the ABI's three pointers, bound once at the
entry's environment.  The phase's blocks write `%conv`, `%and`, `%shr`, the
latch's `%exitcond.not` and `%inc`, the body's own cells and the class test's
three; none of them touches the pointers. -/

/-- **The three stream pointers, at the running environment.** -/
structure StreamCells (env : Env) (xp nxp xcarry : Nat) : Prop where
  /-- The escape stream's read cursor. -/
  xp_cell : lookupName env "%xp" = some (.ptr xp)
  /-- The escape stream's write cursor. -/
  nxp_cell : lookupName env "%nxp" = some (.ptr nxp)
  /-- The escape stream's carry. -/
  xcarry_cell : lookupName env "%xcarry" = some (.ptr xcarry)

/-! ### Reads that miss a builder's cells

Each builder is a `cells` list the block itself wrote; a read of one of the
pointers stops at whatever the environment beneath the list holds. -/

theorem lookupName_lrPhEnv_xp (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%xp" = lookupName env "%xp" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_nxp (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%nxp" = lookupName env "%nxp" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_lrPhEnv_xcarry (env : Env) (arm : BitVec 64) :
    lookupName (lrPhEnv env arm) "%xcarry" = lookupName env "%xcarry" := by
  simp only [lrPhEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_xp (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%xp" = lookupName env "%xp" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_nxp (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%nxp" = lookupName env "%nxp" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forIncEnv_xcarry (env : Env) (i shr : BitVec 64) :
    lookupName (forIncEnv env i shr) "%xcarry" = lookupName env "%xcarry" := by
  simp only [forIncEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]

theorem lookupName_forBodyOut_xp (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%xp" = lookupName env "%xp" := by
  handoff_lk

theorem lookupName_forBodyOut_nxp (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%nxp" = lookupName env "%nxp" := by
  handoff_lk

theorem lookupName_forBodyOut_xcarry (env : Env) (v : ForBodyValues) :
    lookupName (forBodyOut env v) "%xcarry" = lookupName env "%xcarry" := by
  handoff_lk

theorem lookupName_ifEndEnv_xp (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%xp" = lookupName env "%xp" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_nxp (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%nxp" = lookupName env "%nxp" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

theorem lookupName_ifEndEnv_xcarry (env : Env) (a2 a3 : List (BitVec 64)) :
    lookupName (ifEndEnv env a2 a3) "%xcarry" = lookupName env "%xcarry" := by
  simp only [ifEndEnv, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]

/-- A pointer read through the entry's six cells. -/
theorem lookupName_entryEnv_xp (env : Env) (n arm : BitVec 64) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%xp"
      = some (.ptr xp) :=
  lookupName_entryEnv_of env n arm h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem lookupName_entryEnv_nxp (env : Env) (n arm : BitVec 64) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%nxp"
      = some (.ptr nxp) :=
  lookupName_entryEnv_of env n arm h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem lookupName_entryEnv_xcarry (env : Env) (n arm : BitVec 64) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) "%xcarry"
      = some (.ptr xcarry) :=
  lookupName_entryEnv_of env n arm h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### The phase's two environments

The seed's environment is the preheader's then the body's then the class test's;
a pass's is the latch's then the body's then the class test's. -/

theorem lookupName_asciiSeedEnv_xp (env : Env) (arm : BitVec 64) (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%xp"
      = lookupName env "%xp" := by
  rw [lookupName_ifEndEnv_xp, lookupName_forBodyOut_xp, lookupName_lrPhEnv_xp]

theorem lookupName_asciiSeedEnv_nxp (env : Env) (arm : BitVec 64) (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%nxp"
      = lookupName env "%nxp" := by
  rw [lookupName_ifEndEnv_nxp, lookupName_forBodyOut_nxp, lookupName_lrPhEnv_nxp]

theorem lookupName_asciiSeedEnv_xcarry (env : Env) (arm : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) "%xcarry"
      = lookupName env "%xcarry" := by
  rw [lookupName_ifEndEnv_xcarry, lookupName_forBodyOut_xcarry,
    lookupName_lrPhEnv_xcarry]

theorem lookupName_asciiStepEnv_xp (env : Env) (i shr : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (forIncEnv env i shr) v) v.w2 v.w3) "%xp"
      = lookupName env "%xp" := by
  rw [lookupName_ifEndEnv_xp, lookupName_forBodyOut_xp, lookupName_forIncEnv_xp]

theorem lookupName_asciiStepEnv_nxp (env : Env) (i shr : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (forIncEnv env i shr) v) v.w2 v.w3) "%nxp"
      = lookupName env "%nxp" := by
  rw [lookupName_ifEndEnv_nxp, lookupName_forBodyOut_nxp, lookupName_forIncEnv_nxp]

theorem lookupName_asciiStepEnv_xcarry (env : Env) (i shr : BitVec 64)
    (v : ForBodyValues) :
    lookupName (ifEndEnv (forBodyOut (forIncEnv env i shr) v) v.w2 v.w3) "%xcarry"
      = lookupName env "%xcarry" := by
  rw [lookupName_ifEndEnv_xcarry, lookupName_forBodyOut_xcarry,
    lookupName_forIncEnv_xcarry]

/-! ### The bundle at the entry, the phase's seed and a pass -/

/-- The three pointers at the initial state's environment. -/
theorem streamCells_init (mem : Mem) (b ent xp nxp xcarry : Nat) (n arm : BitVec 64) :
    StreamCells (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp,
      .ptr xcarry, .int 64 arm] mem).env xp nxp xcarry :=
  { xp_cell := s1BlocksInit_env_xp mem b ent xp nxp xcarry n arm
    nxp_cell := s1BlocksInit_env_nxp mem b ent xp nxp xcarry n arm
    xcarry_cell := s1BlocksInit_env_xcarry mem b ent xp nxp xcarry n arm }

/-- The pointers through the entry's block. -/
theorem streamCells_entryEnv (env : Env) (n arm : BitVec 64) (xp nxp xcarry : Nat)
    (h : StreamCells env xp nxp xcarry) :
    StreamCells (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm)
      xp nxp xcarry :=
  { xp_cell := lookupName_entryEnv_xp env n arm h.xp_cell
    nxp_cell := lookupName_entryEnv_nxp env n arm h.nxp_cell
    xcarry_cell := lookupName_entryEnv_xcarry env n arm h.xcarry_cell }

/-- The pointers through the preheader's first pass. -/
theorem streamCells_asciiSeed (env : Env) (arm : BitVec 64) (v : ForBodyValues)
    (xp nxp xcarry : Nat) (h : StreamCells env xp nxp xcarry) :
    StreamCells (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3)
      xp nxp xcarry :=
  { xp_cell := by rw [lookupName_asciiSeedEnv_xp]; exact h.xp_cell
    nxp_cell := by rw [lookupName_asciiSeedEnv_nxp]; exact h.nxp_cell
    xcarry_cell := by rw [lookupName_asciiSeedEnv_xcarry]; exact h.xcarry_cell }

/-- The pointers through one pass's three builders. -/
theorem streamCells_asciiStep (env : Env) (i shr : BitVec 64) (v : ForBodyValues)
    (xp nxp xcarry : Nat) (h : StreamCells env xp nxp xcarry) :
    StreamCells (ifEndEnv (forBodyOut (forIncEnv env i shr) v) v.w2 v.w3)
      xp nxp xcarry :=
  { xp_cell := by rw [lookupName_asciiStepEnv_xp]; exact h.xp_cell
    nxp_cell := by rw [lookupName_asciiStepEnv_nxp]; exact h.nxp_cell
    xcarry_cell := by rw [lookupName_asciiStepEnv_xcarry]; exact h.xcarry_cell }

/-- The pointers at the hand-off state's own environment. -/
theorem streamCells_handoffState (env : Env) (s : State) (c : AsciiCarry)
    (v : ForBodyValues) (xp nxp xcarry : Nat)
    (h : StreamCells env xp nxp xcarry) :
    StreamCells (asciiHandoffState env s c v).env xp nxp xcarry := by
  rw [show (asciiHandoffState env s c v).env
      = ifEndEnv (forBodyOut (forIncEnv env c.i c.shr) v) v.w2 v.w3 from rfl]
  exact streamCells_asciiStep env c.i c.shr v xp nxp xcarry h

/-! ### The phase's invariant with the stream's cells

`AsciiInvCells` is the phase's own reading; the bundle adds the three pointers,
which no builder of the phase rebinds, so it is set once at the seed and read
back at every latch and at the hand-off. -/

/-- **The phase's cells with the stream's three pointers.** -/
structure StreamInvCells (env : Env) (s : State) (c : AsciiCarry) (b : Nat)
    (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (xp nxp xcarry : Nat) : Prop
    extends AsciiInvCells env s c b n conv arm where
  /-- The escape stream's read cursor. -/
  xp_cell : lookupName env "%xp" = some (.ptr xp)
  /-- The escape stream's write cursor. -/
  nxp_cell : lookupName env "%nxp" = some (.ptr nxp)
  /-- The escape stream's carry. -/
  xcarry_cell : lookupName env "%xcarry" = some (.ptr xcarry)

/-- The bundle's stream component at the same environment. -/
theorem StreamInvCells.toStreamCells {env : Env} {s : State} {c : AsciiCarry}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    {xp nxp xcarry : Nat} (h : StreamInvCells env s c b n conv arm xp nxp xcarry) :
    StreamCells env xp nxp xcarry :=
  { xp_cell := h.xp_cell
    nxp_cell := h.nxp_cell
    xcarry_cell := h.xcarry_cell }

/-- **The phase's terminals, with the entry's and the stream's cells.**  The
hand-off names the environment the invariant is stated at, so the fused loop's
three lookups are readable there. -/
inductive AsciiTermStreamCells (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) (xp nxp xcarry : Nat) : State → Prop where
  | exit (env : Env) (s : State) (c : AsciiCarry) :
      AsciiInvCells env s c b n conv arm → c.i + 1 = c.shr →
      AsciiTermStreamCells b n conv arm xp nxp xcarry (asciiExitState env s c)
  | handoff (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
      (v : ForBodyValues) :
      AsciiInvCells env s c b n conv arm →
      StreamCells env xp nxp xcarry →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 →
      c.i + 1 ≠ c.shr →
      v = asciiValues c bs2 bs3 →
      AsciiTermStreamCells b n conv arm xp nxp xcarry (asciiHandoffState env s c v)

/-- Every stream-carrying terminal is one of the phase's terminals. -/
theorem AsciiTermStreamCells.toTermCells {b : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm : BitVec 64} {xp nxp xcarry : Nat} {e : State}
    (h : AsciiTermStreamCells b n conv arm xp nxp xcarry e) :
    AsciiTermCells b n conv arm e := by
  cases h with
  | exit env s c hinv hbound => exact AsciiTermCells.exit env s c hinv hbound
  | handoff env s c bs2 bs3 v hinv _ h2 h3 hne hv =>
      exact AsciiTermCells.handoff env s c bs2 bs3 v hinv h2 h3 hne hv

/-! ### The phase's seed and passes carry the stream's cells

The two lemmas restate the phase's own seed and back edge with the bundle; the
step's stream component reads through the latch's, the body's and the class
test's builders. -/

/-- **The phase's seed, with the stream's cells.** -/
theorem streamInvCells_seed (env : Env) (s : State) (arm : BitVec 64)
    (bs2 bs3 : List UInt8) (b ent : Nat) (shr n : BitVec 64) (conv : BitVec 32)
    (xp nxp xcarry : Nat)
    (hcells : EntryCells env n conv arm)
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hnpos : 0 < shr.toNat)
    (hstream : StreamCells env xp nxp xcarry) :
    let v := forBodyValues 0 0 0 0 0 bs2 bs3 b ent
    let s1 := stateAt (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3)
      { s with
        pc := "for.inc",
        pre := some "if.end",
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }
    StreamInvCells (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) s1
      { i := v.i, prevS := v.shr17, st0 := v.shrII, st9 := v.conv13II,
        st15 := v.shrI, b := b, ent := ent, shr := shr,
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) } b n conv arm
      xp nxp xcarry := by
  intro v s1
  have hbase : AsciiInvCells (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) s1
      { i := v.i, prevS := v.shr17, st0 := v.shrII, st9 := v.conv13II,
        st15 := v.shrI, b := b, ent := ent, shr := shr,
        mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) } b n conv arm :=
    asciiInvCells_seed env s arm bs2 bs3 b ent shr n conv hcells harm hgate hshr hb hent
      hnpos
  exact
    { toAsciiInvCells := hbase
      xp_cell := by rw [lookupName_asciiSeedEnv_xp]; exact hstream.xp_cell
      nxp_cell := by rw [lookupName_asciiSeedEnv_nxp]; exact hstream.nxp_cell
      xcarry_cell := by
        rw [lookupName_asciiSeedEnv_xcarry]; exact hstream.xcarry_cell }

/-- **One pass's cells, with the stream's.** -/
theorem streamInvCells_step (env : Env) (s : State) (c : AsciiCarry)
    (bs2 bs3 : List UInt8) (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) (xp nxp xcarry : Nat)
    (hinv : StreamInvCells env s c b n conv arm xp nxp xcarry)
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
    StreamInvCells (ifEndEnv (forBodyOut (forIncEnv env c.i c.shr) v) v.w2 v.w3) s3
      (asciiNext c bs2 bs3) b n conv arm xp nxp xcarry := by
  intro v s1 s2 s3
  obtain ⟨h01, h12, h23, hbase⟩ :=
    asciiInvCells_step env s c bs2 bs3 b n conv arm hinv.toAsciiInvCells hloop hj
      hread2 hread3 hbit
  refine ⟨h01, h12, h23, ?_⟩
  exact
    { toAsciiInvCells := hbase
      xp_cell := by rw [lookupName_asciiStepEnv_xp]; exact hinv.xp_cell
      nxp_cell := by rw [lookupName_asciiStepEnv_nxp]; exact hinv.nxp_cell
      xcarry_cell := by
        rw [lookupName_asciiStepEnv_xcarry]; exact hinv.xcarry_cell }

/-! ### The phase's run, with the stream's cells

The run is `JsonS1BlocksPrefix`'s, re-stated over the bundle: the block reads,
the branch, the memory facts and the measure are the phase's own, and each
terminal carries the stream's cells at the environment its invariant names. -/

/-- **The phase's run, with the stream's cells.** -/
theorem streamInvCells_runFuel_aux (esc : Calls) :
    ∀ (r : Nat) (env : Env) (s : State) (c : AsciiCarry) (b : Nat)
      (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
      (xp nxp xcarry : Nat) (doc : Nat → List UInt8),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      StreamInvCells env s c b n conv arm xp nxp xcarry →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) →
      ∃ (e : State) (j : Nat), j ≤ 3 * r + 4 ∧
        AsciiTermStreamCells b n conv arm xp nxp xcarry e ∧
        ∀ k, runFuel (s1BlocksCallsEsc esc) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e
  | 0, env, s, c, b, n, conv, arm, xp, nxp, xcarry, doc, hmeasure, hshr, hinv,
      hgap, hdoc => by
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
        AsciiTermStreamCells.exit env s c hinv.toAsciiInvCells hbound, fun k => ?_⟩
      exact runFuel_jump_prefix hstep k
  | r + 1, env, s, c, b, n, conv, arm, xp, nxp, xcarry, doc, hmeasure, hshr, hinv,
      hgap, hdoc => by
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
              { s with
                pc := "if.end",
                pre := some "for.body",
                mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          rw [step_forBody_esc esc (forIncEnv env c.i c.shr)
            { s with pc := "for.body", pre := some "for.inc" } rfl]
          exact h12
        have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with
                pc := "if.end",
                pre := some "for.body",
                mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) =
            .jump (stateAt E'
              { s with
                pc := "if.then38",
                pre := some "if.end",
                mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
        refine ⟨asciiHandoffState env s c v, 3, by omega,
          AsciiTermStreamCells.handoff env s c bs2 bs3 v hinv.toAsciiInvCells
            hinv.toStreamCells hread2 hread3 hne rfl,
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
              { s with
                pc := "if.end",
                pre := some "for.body",
                mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
          obtain ⟨-, h12, -⟩ :=
            for_inc_page_ascii env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
              c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
              hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit0
          rw [step_forBody_esc esc (forIncEnv env c.i c.shr)
            { s with pc := "for.body", pre := some "for.inc" } rfl]
          exact h12
        have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
            (stateAt (forBodyOut (forIncEnv env c.i c.shr) v)
              { s with
                pc := "if.end",
                pre := some "for.body",
                mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) =
            .jump s3 := by
          obtain ⟨-, -, h23⟩ :=
            for_inc_page_ascii env s c.i c.shr c.prevS c.st0 c.st9 c.st15 bs2 bs3
              c.b c.ent hinv.pc hinv.index hinv.bound hinv.prevS hinv.st0 hinv.st9
              hinv.st15 hinv.gate hinv.base hinv.emit hloop hj57 hread2' hread3' hbit0
          rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
        obtain ⟨-, -, -, hinv'⟩ :=
          streamInvCells_step env s c bs2 bs3 b n conv arm xp nxp xcarry hinv hloop
            hj57 hread2 hread3 hbit0
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
          streamInvCells_runFuel_aux esc r E' s3 (asciiNext c bs2 bs3) b n conv arm
            xp nxp xcarry doc hmeasure' hshr hinv' hgap' hdoc'
        refine ⟨e, 3 + j, by omega, hterm, fun k => ?_⟩
        rw [show 3 + j + k = 3 + (j + k) from by omega,
          runFuel_jump3 h01' h12' h23' (j + k)]
        exact hfuel k

/-- **The phase's run, with the stream's cells**, at the latch's own measure. -/
theorem streamInvCells_runFuel (esc : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (b : Nat) (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64)
    (xp nxp xcarry : Nat) (doc : Nat → List UInt8)
    (hshr : c.shr.toNat < 2 ^ 57) (hinv : StreamInvCells env s c b n conv arm xp nxp xcarry)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) :
    ∃ (e : State) (j : Nat),
      j ≤ 3 * (c.shr.toNat - (c.i.toNat + 1)) + 4 ∧
        AsciiTermStreamCells b n conv arm xp nxp xcarry e ∧
        ∀ k, runFuel (s1BlocksCallsEsc esc) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e :=
  streamInvCells_runFuel_aux esc (c.shr.toNat - (c.i.toNat + 1)) env s c b n conv arm
    xp nxp xcarry doc rfl hshr hinv hgap hdoc

/-! ### The entry's prefix to the phase's terminal

The entry's block, the preheader's first pass and the phase's induction compose
into one `runFuel` prefix at the escape selection, now ending at a terminal that
names the environment and carries both bundles. -/

/-- **The entry reaches the phase's terminal, with the stream's cells.** -/
theorem s1BlocksPrefix_stream (esc : Calls) (mem : Mem)
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
      AsciiTermStreamCells b n (entryGate arm) arm xp nxp xcarry e := by
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
  have hstream0 : StreamCells init.env xp nxp xcarry :=
    streamCells_init mem b ent xp nxp xcarry n arm
  have hstreamE0 : StreamCells E0 xp nxp xcarry :=
    streamCells_entryEnv init.env n arm xp nxp xcarry hstream0
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
  have hstepEntry : step (s1BlocksCallsEsc esc) s1BlocksFunction init =
      .jump (stateAt E0 sLR) :=
    s1BlocksInit_step_blocks mem b ent xp nxp xcarry n arm hlong
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
  have hseed : StreamInvCells Eseed sSeed c0 b n (entryGate arm) arm xp nxp xcarry :=
    streamInvCells_seed E0 sLR arm ((docBlock bs 0).take 32)
      ((docBlock bs 0).drop 32) b ent (n >>> 6) n (entryGate arm) xp nxp xcarry
      hcells0 harm0 hgate hshrE0 hbE0 hentE0 (by
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
        omega) hstreamE0
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
    streamInvCells_runFuel esc Eseed sSeed c0 b n (entryGate arm) arm xp nxp xcarry
      doc hshr57 hseed hgapSeed hdocSeed
  exact ⟨e, 1 + (3 + j),
    (fun k => by
      rw [show 1 + (3 + j) + k = 1 + (3 + (j + k)) from by omega,
        runFuel_jump_prefix hstepEntry (3 + (j + k)),
        runFuel_jump3 h01' h12' h23' (j + k)]
      exact hfuel k),
    hterm⟩

/-! ### The hand-off's own carries

`handoffPrefix_exit` runs the fused loop from a hand-off terminal at the
environment the phase's invariant names.  Everything it needs beyond that
invariant, the stream's cells and the phase's seed facts is a model fact about
the document window, the page's register reads, the fuse's two word identities
and the escape selection.  They are bundled here, because the witness — the
phase's carry and the pass's values — is inside the terminal and cannot be a
parameter of the composed theorem. -/

/-- **The hand-off's window and register carries**, at one witness of the phase's
hand-off terminal. -/
structure HandoffCarries (esc : Calls) (env : Env) (s : State) (c : AsciiCarry)
    (bs2 bs3 : List UInt8) (v : ForBodyValues) (doc : Nat → List UInt8)
    (bs73 bs74 : List UInt8) (xp nxp xcarry : Nat) : Prop where
  /-- The document window ends at or below the pass's emit base. -/
  entGap : c.b + 64 * c.shr.toNat ≤ c.ent
  /-- The document survives the pass's store. -/
  docMem : ∀ j, j < c.shr.toNat →
    readBytes c.mem (c.b + 64 * j) 64 = some (doc j)
  /-- The document survives the hand-off page's store. -/
  docPage : ∀ j, j < c.shr.toNat →
    readBytes (asciiHandoffState env s c v).mem (c.b + 64 * j) 64 = some (doc j)
  /-- The three bytes below the base are zero after the page. -/
  zeroPage : readBytes (asciiHandoffState env s c v).mem (c.b - 3) 3 = some [0, 0, 0]
  /-- The hand-off block is inside the document. -/
  irow : (v.i + 1).toNat < c.shr.toNat
  /-- Its row address is in range. -/
  i63 : ((v.i + 1).signExtend 64).toNat < 2 ^ 63
  /-- Its shifted row address is in range. -/
  shl63 : (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
    < 2 ^ 63
  /-- The page's first word. -/
  read73 : readBytes (asciiHandoffState env s c v).mem
    (c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
    = some bs73
  /-- The page's second word. -/
  read74 : readBytes (asciiHandoffState env s c v).mem
    ((c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
      + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74
  /-- The first word's four lanes. -/
  len73 : (unpackLanes 64 4 (bytesToNat bs73)).length = 4
  /-- The second word's four lanes. -/
  len74 : (unpackLanes 64 4 (bytesToNat bs74)).length = 4
  /-- The fuse's ASCII word. -/
  asciiLen : (ifThen38Values v.addPtr v.i bs2 bs3
      ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
      ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
      ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
      (((doc ((c.i + 1).toNat)).drop 31).take 32)
      (((doc ((c.i + 1).toNat)).drop 30).take 32)
      (((doc ((c.i + 1).toNat)).drop 29).take 32)).or284.length = 4
  /-- The fuse's byte-mask word. -/
  u8kLen : (ifThen38Values v.addPtr v.i bs2 bs3
      ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
      ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
      ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
      (((doc ((c.i + 1).toNat)).drop 31).take 32)
      (((doc ((c.i + 1).toNat)).drop 30).take 32)
      (((doc ((c.i + 1).toNat)).drop 29).take 32)).or291.length = 4
  /-- The escape selection answers every call. -/
  call : ∀ (args : List Value) (mem : Mem) (next : Nat),
    ∃ r : CallOutcome, esc escapeListCallee args mem next = some r
  /-- The escape selection keeps the document window and the zeroes below it. -/
  keep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
    (r : CallOutcome),
    esc escapeListCallee
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] mem next = some r →
    (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
    readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]

/-! ### The join from the entry to the exit

The phase's terminal is either its own bound, which is already an exit terminal,
or a hand-off, which `handoffPrefix_exit` continues to the bound's exit.  The
witness's carries are the hypothesis: they are model facts, and the only reason
they are not derivable from the seed's is that the witness is the run's. -/

/-- **The entry reaches the exit.**  From `s1BlocksInit`, on a document of at
least one block, the run at the escape selection reaches a terminal at
`for.end101` on one of the two exit arms, carrying the entry's cells. -/
theorem s1BlocksPrefix_exit (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
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
    (hshr57 : (n >>> 6).toNat < 2 ^ 57)
    (hb3 : 3 ≤ b)
    (hready : ∀ (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
      (v : ForBodyValues),
      AsciiInvCells env s c b n (entryGate arm) arm →
      StreamCells env xp nxp xcarry →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 →
      c.i + 1 ≠ c.shr →
      v = asciiValues c bs2 bs3 →
      HandoffCarries esc env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    let args := [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm]
    ∃ (e : State) (N : Nat),
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
          (s1BlocksInit args mem) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      ExitTermCells b n (entryGate arm) arm e := by
  intro args
  obtain ⟨e, N, hpref, hterm⟩ :=
    s1BlocksPrefix_stream esc mem b ent xp nxp xcarry n arm bs doc hlong hread2 hread3
      hgate hfirst hgap hdoc hshr57
  cases hterm with
  | exit env s c hinv hbound =>
      exact ⟨asciiExitState env s c, N, hpref, ExitTermCells.ascii env s c hinv hbound⟩
  | handoff env s c bs2 bs3 v hinv hstream h2 h3 hne hv =>
      have hcar := hready env s c bs2 bs3 v hinv hstream h2 h3 hne hv
      have hshreq : c.shr = n >>> 6 := by
        have h1 := hinv.bound
        rw [hinv.shr_cell] at h1
        simpa using (Option.some.inj h1).symm
      have hshr57' : c.shr.toNat < 2 ^ 57 := by rw [hshreq]; exact hshr57
      have hb3' : 3 ≤ c.b := by rw [hinv.b_eq]; exact hb3
      have hbit : evalICmp .ult (v.i + 1) c.shr = 1 := by
        show BitVec.ofBool (BitVec.ult (v.i + 1) c.shr) = 1
        rw [(BitVec.ult_iff_toNat_lt).2 hcar.irow]
        rfl
      obtain ⟨e', M, hcont, hterm'⟩ :=
        handoffPrefix_exit esc env s c v bs2 bs3 doc b n (entryGate arm) arm xp nxp
          xcarry bs73 bs74 hinv hv h2 h3 hne hbit hshr57' hcar.entGap hcar.docMem hb3'
          hstream.xp_cell hstream.nxp_cell hstream.xcarry_cell hcar.docPage
          hcar.zeroPage hcar.irow hcar.i63 hcar.shl63 hcar.read73 hcar.read74
          hcar.len73 hcar.len74 hcar.asciiLen hcar.u8kLen hcar.call hcar.keep
      exact ⟨e', N + M,
        (fun k => by
          rw [show N + M + k = N + (M + k) from by omega, hpref (M + k)]
          exact hcont k),
        hterm'⟩

/-! ### Axiom footprints

The prefix is the phase's own steps composed by `runFuel`'s prefix rules, the
cells' reads and `handoffPrefix_exit`; it adds no choice beyond the modules' own
scope splits.  No statement carries `sorryAx`. -/
#print axioms lookupName_forBodyOut_xp
#print axioms streamCells_init
#print axioms streamCells_handoffState
#print axioms streamInvCells_seed
#print axioms streamInvCells_step
#print axioms streamInvCells_runFuel
#print axioms AsciiTermStreamCells.toTermCells
#print axioms s1BlocksPrefix_stream
#print axioms s1BlocksPrefix_exit

end LeanLLVM.Refinement.JsonS1BlocksStream
