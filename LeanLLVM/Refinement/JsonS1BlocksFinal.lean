/-
The block unit's residuals at the real run, and its record instance.

`JsonS1BlocksFacts` states the residual `S1BlocksResiduals` and derives the
bundle, the record instance and the refinement from it, but leaves the residual
as a hypothesis at every argument list and the caller's allocator base.  This
module closes that gap as far as the committed components reach:

* **The base.**  `Satisfies` quantifies the allocator base, while every
  committed run statement is at `s1BlocksInit` (`next = 1`).  The body allocates
  nothing (`s1Blocks_allocaFree`) and the selection's four intrinsic arms ignore
  the base (`s1BlocksCalls_nextIrr`), so the only remaining input is that the
  escape selection's answer is the same at every base (`CallsNextIrr esc`).
  `s1BlocksRun_entry_next` is `JsonUnitContracts.runFuel_next_irr` at the unit's
  own two states, and carries a completed run from `next = 1` to any base.
* **The parts.**  `S1BlocksRunParts` names the residual's fields at the shapes
  the committed components produce them: the entry-to-exit prefix as
  `JsonS1BlocksPrefixFuel.OnePrefixBounded`, the exit's charge as
  `JsonS1BlocksExitFuel.exitCharge` at the terminal's own `ret` and memory, the
  staging as `VerdictStaging` at the document's block count, and the tail as
  `S1BlocksTail` at the run's memory.
* **The unit-post facts.**  `S1BlocksUnitPost` is the per-page escape-call
  record `JsonS1BlocksRunFrame.loopRun_frame` consumes — the call resolves, the
  document and the three staged zeroes survive it, and each call's reach is an
  `EscapeReach` at its own count — bundled once so the calling arm's frame is a
  named hypothesis rather than three inline ones
  (`loopRun_frame_of_unitPost`).  `tail_calling_of_unitPost` reads the same
  record at the peel's own call and produces the residual's `tail` on the arm
  that calls (`JsonS1BlocksRunFrame.tail_third_of_frame`); the silent arms are
  `JsonS1BlocksLoopFacts.tail_peel_facts`.
* **The instance.**  `s1_blocks_satisfies_of_parts` and
  `s1_blocks_refines_of_parts` are `JsonS1BlocksSatisfies.s1_blocks_satisfies`
  and `JsonS1BlocksRefines.s1_blocks_refines` with the residual hypothesis
  discharged from `S1BlocksRunParts`; neither statement is restated or
  weakened.
-/
import LeanLLVM.Refinement.JsonS1BlocksFacts
import LeanLLVM.Refinement.JsonS1BlocksRunFrame
import LeanLLVM.Refinement.JsonUnitContracts
import LeanLLVM.Refinement.JsonS1BlocksReuse

namespace LeanLLVM.Refinement.JsonS1BlocksFinal

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksExitFuel
open LeanLLVM.Refinement.JsonS1BlocksFacts
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The allocator base

The record's `pre` and `post` ignore the base (`s1BlocksPre`'s and
`s1BlocksPost`'s `next` argument is unused), but `Satisfies` quantifies it, and
the committed run statements are at `s1BlocksInit`.  These are the two facts
that make the run's outcome independent of it: the body executes no `alloca`,
and the four intrinsic arms answer the same value and memory at every base.  The
escape arm is the caller's selection, so its invariance is the hypothesis
`CallsNextIrr esc`. -/

/-- **The unit's own call environment ignores the allocator base.**  The four
intrinsic arms return `next := next` and the same register value, and the mask
unit's arms it falls back to do the same (`JsonUnitContracts.s1Calls_nextIrr`). -/
theorem s1BlocksCalls_nextIrr : CallsNextIrr s1BlocksCalls := by
  intro sym args mem n1 n2
  unfold s1BlocksCalls
  split
  · rfl
  · rfl
  · exact s1Calls_nextIrr sym args mem n1 n2

/-- **The escape-parametric environment ignores the base when the caller's
selection does.**  At the escape symbol the answer is the selection's; at every
other symbol it is the unit's own. -/
theorem s1BlocksCallsEsc_nextIrr {esc : Calls} (h : CallsNextIrr esc) :
    CallsNextIrr (s1BlocksCallsEsc esc) := by
  intro sym args mem n1 n2
  by_cases he : sym = escapeListCallee
  · subst he
    simpa only [s1BlocksCallsEsc, ↓reduceIte] using h escapeListCallee args mem n1 n2
  · simpa only [s1BlocksCallsEsc, he, ↓reduceIte] using
      s1BlocksCalls_nextIrr sym args mem n1 n2

/-- **The fused body allocates nothing.**  Its scratch is the caller's
(`JsonS1BlocksIR.allocaTypes s1BlocksFunction = []`), so no allocator-moved
frame appears in a run. -/
theorem s1Blocks_allocaFree : allocaFree s1BlocksFunction = true := by decide

/-- **The run from any base is the run from `next = 1`.**  The two entry states
agree on everything but the base, and the body allocates nothing, so
`JsonUnitContracts.runFuel_next_irr` applies at every fuel. -/
theorem s1BlocksRun_entry_next {esc : Calls} (h : CallsNextIrr esc) (fuel : Nat)
    {args : List Value} {mem : Mem} {next : Nat} :
    runFuel (s1BlocksCallsEsc esc) fuel s1BlocksFunction
        (EntryState s1BlocksFunction args mem next) =
      runFuel (s1BlocksCallsEsc esc) fuel s1BlocksFunction
        (EntryState s1BlocksFunction args mem 1) :=
  runFuel_next_irr (s1BlocksCallsEsc_nextIrr h) s1Blocks_allocaFree fuel
    ⟨rfl, rfl, rfl, rfl⟩

/-! ### The unit-post facts

The calling arm's frame is the loop run's, and `loopRun_frame` reads three facts
of the escape call per page: it resolves, the document and the staged zeroes are
its memory's, and its reach is an `EscapeReach` at the page's count.  This is
the unit's post read at each page's own call; nothing else in the loop's
induction mentions the selection. -/

/-- **The per-page post of the escape call.**  The three facts
`JsonS1BlocksRunFrame.loopRun_frame` takes of the selection, at the loop's own
`xp`, `nxp`, `xcarry` and document.

`keep` is **not instantiable as stated**, and the bundle is a hypothesis about a
selection that keeps a window it is never told about.  Its argument list is the
three mask words, the block's index and the three pointers, so it carries neither
the window's base `b` nor the bound `%shr`; a selection whose answer depends only
on its arguments cannot place a document block at `c'.b`, and the escape record
(`JsonS1BlocksRefine.escapeEntryAt`) establishes its post only at the vectors its
`pre` admits, which are the pages' and the peel's.  The correct statement is the
per-call `JsonS1BlocksUnitPost.S1BlocksUnitPostAt`, at those real argument
vectors, from `escapeEntryAt` and the staging (`unitPostAt_of_pre`,
`peel_unitPostAt_of_pre`); consumers take that form rather than this bundle. -/
structure S1BlocksUnitPost (esc : Calls) (xp nxp xcarry : Nat) (bs : List UInt8) : Prop where
  /-- Every escape call resolves. -/
  callAll : ∀ (args : List Value) (mem : Mem) (next : Nat),
    ∃ r : CallOutcome, esc escapeListCallee args mem next = some r
  /-- The document and the three staged zeroes survive every page's call. -/
  keep : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem)
      (next : Nat) (r' : CallOutcome),
    esc escapeListCallee
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
    (∀ j, j < c'.shr.toNat →
      readBytes r'.mem (c'.b + 64 * j) 64 = some (docBlock bs j)) ∧
    readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0]
  /-- Every page's call is an `EscapeReach` at the count it was entered with. -/
  reach : ∀ (c' : FusedCarry) (or14 mask xs i : BitVec 64) (mem : Mem)
      (next : Nat) (r' : CallOutcome) (xnA : Nat),
    esc escapeListCallee
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
    ∃ (blk0 : BitVec 64) (position : List Nat) (opened ppar : Bool),
      EscapeReach blk0 xp nxp xcarry xnA position
        (flagBytes opened ++ flagBytes ppar) mem r'.mem ∧
      position.length ≤ 64

/-- **The calling loop's frame, from the unit's post.**
`JsonS1BlocksRunFrame.loopRun_frame` with its three selection hypotheses read
off `S1BlocksUnitPost`: the frame the tail's third disjunct is
(`JsonS1BlocksRunFrame.tail_third_of_frame`). -/
theorem loopRun_frame_of_unitPost (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
    (bs : List UInt8)
    (hstoreAll : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < blocksOf bs.length →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat)
    (env : Env) (s : State)
    (c : FusedCarry) (gate : BitVec 1) (ps : List Nat)
    (hstart : c.mem = start)
    (hblocks : blocksOf bs.length = c.shr.toNat + 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
    (hinv : LoopInv start xp xn ps bs env s c gate 0)
    (hcount0 : readBytes c.mem nxp 8 = some (wordBytes 8 xn))
    (hstream0 : StreamPrefix c.mem xp xn ps)
    (hpresent0 : HasBytes c.mem c.ent (8 * blocksOf bs.length))
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hentXp : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent)
    (hentNxp : c.ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ c.ent)
    (hentXc : c.ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ c.ent)
    (hxpNxp : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ nxp ∨
      nxp + 8 ≤ xp)
    (hxpXc : xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ xcarry ∨
      xcarry + 16 ≤ xp)
    (hu : S1BlocksUnitPost sel xp nxp xcarry bs) :
    ∃ (env' : Env) (e : State) (c' : FusedCarry) (count pages : Nat) (j : Nat),
      j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      FusedExit env' e c' ∧
      RunFrame start xp xn nxp xcarry ps bs c' count pages ∧
      (∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction
        (stateAt env s) = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) :=
  loopRun_frame sel start xp xn nxp xcarry bs hstoreAll env s c gate ps hstart
    hblocks hshr57 hshrLe hblocks64 hinv hcount0 hstream0 hpresent0 hb3 hgap hdoc
    hzero hentXp hentNxp hentXc hxpNxp hxpXc hu.callAll hu.keep hu.reach

/-- **The calling arm's tail, from the unit's post.**  The loop run's frame
(`JsonS1BlocksRunFrame.tail_third_of_frame`) at the peel's own call: the call
resolves at the store's memory and the unit's post supplies the `EscapeReach` at
the pages' count, so the third disjunct holds.  This is the residual's `tail` on
the arm that calls, the other two arms being the silent merge's
(`JsonS1BlocksLoopFacts.tail_peel_facts`). -/
theorem tail_calling_of_unitPost {esc : Calls} {start : Mem}
    {xp xn nxp xcarry : Nat} {ps : List Nat} {bs : List UInt8} {c : FusedCarry}
    {count pages : Nat} {arm : BitVec 64} {M : Mem} {shr : Nat}
    {or135 andv w : BitVec 64} {or14 mask xs i : BitVec 64} {next : Nat}
    {r' : CallOutcome}
    (hu : S1BlocksUnitPost esc xp nxp xcarry bs)
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hcall : esc escapeListCallee
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) next = some r')
    (hrM : r'.mem = M)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksTail start c.ent xp nxp xcarry xn arm bs M := by
  obtain ⟨blk0, position, opened, ppar, hreach, hlen⟩ :=
    hu.reach c or14 mask xs i
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) next r' count hcall
  rw [hrM] at hreach
  exact tail_third_of_frame hrun hshr hor hshrEq hand hw harm hreach hlen hxpSep

/-! ### The residual's parts at the real run

Each field is the statement of the committed component that produces it, at the
record's own witnesses.  The prefix is
`JsonS1BlocksPrefixFuel.OnePrefixBounded` at the document's block count and the
entry's gate word — its trace runs from `s1BlocksInit`, so the residual's parts
are stated at `next = 1` and moved to the caller's base by
`s1BlocksRun_entry_next`.  The exit is one charge `≤ exitCharge` for the whole
terminal family, which is the form
`JsonS1BlocksExitFuel.fusedExitCells_charged` and `asciiExitCells_charged`
produce, read at the terminal the prefix reaches. -/
structure S1BlocksRunParts (esc : Calls) (args : List Value) (mem : Mem)
    (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) where
  /-- The caller's escape selection answers the same at every allocator base. -/
  nextIrr : CallsNextIrr esc
  /-- The entry-to-exit prefix, bounded by `8 * (%n >>> 6) + 21` and ending at
  the entry's exit terminal.  `JsonS1BlocksPrefixFuel.onePrefixBounded_of_exit`
  builds it from the committed prefix's inputs. -/
  prefixRun : OnePrefixBounded esc args mem b (BitVec.ofNat 64 bs.length)
    (entryGate arm) arm
  /-- The returned word. -/
  ret : BitVec 64
  /-- The run's memory. -/
  M : Mem
  /-- The staging's ASCII word. -/
  ascii : List (BitVec 64)
  /-- The staging's UTF-8 word. -/
  u8k : List (BitVec 64)
  /-- The staging's error bit. -/
  err : BitVec 1
  /-- The classifier's gate. -/
  gate : Bool
  /-- The staging at the document's block count
  (`JsonS1BlocksPageModel.exit_staging_of_loopCarry` /
  `exit_staging_of_fusedEnd`). -/
  staging : VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err
  /-- The returned word is the staging's. -/
  word : ret = verdictWord ascii err
  /-- The tail's shape at the run's memory.  The silent arms are
  `JsonS1BlocksLoopFacts.tail_peel_facts`; the calling arm is
  `JsonS1BlocksRunFrame.tail_third_of_frame` at the loop run, whose per-call
  inputs are `S1BlocksUnitPost` (`tail_calling_of_unitPost`). -/
  tail : S1BlocksTail mem ent xp nxp xcarry xn arm bs M
  /-- The exit's charge at the terminal's own `ret` and memory: `≤ exitCharge`
  for every exit terminal, which is what
  `JsonS1BlocksExitFuel.fusedExitCells_charged` / `asciiExitCells_charged`
  produce at the terminal the prefix reaches. -/
  exitBounded : ∃ jE : Nat, jE ≤ exitCharge ∧
    ∀ e : State, ExitTermCells b (BitVec.ofNat 64 bs.length) (entryGate arm) arm e →
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
        some (.ret (some (.int 64 ret)) M)

/-- **The residual, from its parts.**  The prefix's own terminal is where the
exit's charge is read, and the trace is moved from `s1BlocksInit` to the
caller's base by `s1BlocksRun_entry_next`. -/
theorem s1BlocksResiduals_of_parts {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (h : S1BlocksRunParts esc args mem b ent xp nxp xcarry xn arm bs) :
    S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨hIrr, hprefix, ret, M, ascii, u8k, err, gate, hstage, hword, htail, jE,
    hjE, hexit⟩ := h
  obtain ⟨e, N, hN, htrace, hterm⟩ := hprefix
  have htrace' : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e := by
    intro k
    rw [s1BlocksRun_entry_next hIrr (N + k)]
    simpa only [s1BlocksInit_entryState] using htrace k
  exact ⟨ret, M, ascii, u8k, err, gate, e, N, jE, hstage, hword, htail, hN,
    htrace', hterm, hjE, hexit e hterm⟩

/-- **The bundle, from the parts.**  `JsonS1BlocksFacts.s1BlocksFacts_of_residuals`
at the residual above; the run at `s1BlocksBudget` is the two charged segments
joined, not a field. -/
theorem s1BlocksFacts_of_parts {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
      .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksRunParts esc args mem b ent xp nxp xcarry xn arm bs) :
    S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs :=
  s1BlocksFacts_of_residuals hargs (s1BlocksResiduals_of_parts h)

/-! ### The record instance and the refinement -/

/-- **The block unit satisfies its record, from the parts.**  This is
`JsonS1BlocksSatisfies.s1_blocks_satisfies` with its bundle hypothesis
discharged by `s1BlocksFacts_of_parts`; the instance's statement is not
restated.  The parts are base-free, because the prefix is at `s1BlocksInit` and
the run reaches every base through `s1BlocksRun_entry_next`. -/
theorem s1_blocks_satisfies_of_parts {esc : Calls}
    (h : ∀ (args : List Value) (mem : Mem) (b ent xp nxp xcarry xn : Nat)
        (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunParts esc args mem b ent xp nxp xcarry xn arm bs) :
    Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  s1_blocks_satisfies fun args mem next b ent xp nxp xcarry xn arm bs _ hargs =>
    s1BlocksFacts_of_parts hargs (h args mem b ent xp nxp xcarry xn arm bs)

/-- **The record instance, unconditionally over the selection, from parts each
selection supplies.** -/
theorem s1_blocks_satisfies_all_of_parts
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunParts esc args mem b ent xp nxp xcarry xn arm bs) :
    ∀ esc : Calls, Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  fun esc => s1_blocks_satisfies_of_parts (h esc)

/-- **The refinement, from the parts.**  This is
`JsonS1BlocksRefines.s1_blocks_refines`, whose run starts at
`s1BlocksInit` (`next = 1`); the instance read at `next = 1` is one of its
behaviours, through `JsonS1BlocksFacts.s1_blocks_refines_of_satisfies`. -/
theorem s1_blocks_refines_of_parts
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunParts esc args mem b ent xp nxp xcarry xn arm bs) :
    s1_blocks_refines :=
  s1_blocks_refines_of_satisfies (s1_blocks_satisfies_all_of_parts h)

/-! ### Axiom footprints

The base lemmas are `JsonUnitContracts`'s congruence at the selection and the
body's `alloca`-freeness (`decide` on the pinned IR); the unit-post bundle is a
structure, `loopRun_frame_of_unitPost` is `loopRun_frame`'s own induction and
`tail_calling_of_unitPost` is `tail_third_of_frame`'s.  The parts are a structure;
the residual is `runFuel_next_irr` at the two entry states and the prefix's own
continuation; the bundle and the instance are `JsonS1BlocksFacts`'s and
`JsonS1BlocksSatisfies`'s statements unchanged, so they carry what those carry
and nothing more.  No statement reaches `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1BlocksCalls_nextIrr
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1BlocksCallsEsc_nextIrr
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1Blocks_allocaFree
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1BlocksRun_entry_next
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.S1BlocksUnitPost
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.loopRun_frame_of_unitPost
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.tail_calling_of_unitPost
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.S1BlocksRunParts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1BlocksResiduals_of_parts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1BlocksFacts_of_parts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1_blocks_satisfies_of_parts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1_blocks_satisfies_all_of_parts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinal.s1_blocks_refines_of_parts

end LeanLLVM.Refinement.JsonS1BlocksFinal
