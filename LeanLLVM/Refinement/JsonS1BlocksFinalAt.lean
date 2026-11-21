/-
The final assembly at the escape unit's post, at the real call vectors.

`JsonS1BlocksFinal` states the record instance and the refinement from a
`S1BlocksRunParts` whose `tail` is a hypothesis, and its per-page bundle
`S1BlocksUnitPost` is not instantiable: its `keep` clause quantifies over
argument vectors that carry neither the window's base `b` nor the bound `%shr`,
so no selection whose answer depends only on its arguments can place a document
block (`JsonS1BlocksUnitPost` records that against the record's `pre`).  This
module is the assembly that consumes the instantiable form instead.

`JsonS1BlocksUnitPost` derives, from the caller's escape entry
(`escapeEntryAt`) and the staging, the record's post at the pages' and the
peel's own argument vectors (`unitPostAt_of_pre`, `peel_unitPostAt_of_pre`), and
proves the loop's exit carries the caller's `%ent` (`loopRun_frame_ent`).  Here:

* `exists_of_unitPostAt` — the per-call bundle with its outcome named.  The
  bundle is a `Prop`-valued `∃`; the tail's memory and the exit's are the same
  witness, so a consumer names it once rather than guessing it.
* `tail_calling_at` — the tail's third disjunct from that bundle at the peel's
  vector: `tail_third_at_ent` at the named outcome, with the exit carry's `ent`
  identified with the caller's.  This is `tail_calling_of_unitPost`'s statement
  at the At form, and it is what discharges the calling arm.
* `tail_calling_at_of_pre` — the same from the record's `pre` at the peel's
  vector and the staging (`peel_unitPostAt_of_pre`), so the remaining input is
  the record's `pre` itself rather than a promise about a window the selection
  is never told.
* `S1BlocksRunPartsAt` — `JsonS1BlocksFinal.S1BlocksRunParts` with the tail's
  shape stated at the peel's own call (the `RunFrame` and `c.ent = ent` are
  `loopRun_frame_ent`'s conclusion) instead of assumed.  `s1BlocksResiduals_of_atParts`
  reads it into the residual with `tail_calling_at`'s shape.
* `s1_blocks_satisfies_of_atParts` and `s1_blocks_refines_of_atParts` are
  `JsonS1BlocksFinal.s1_blocks_satisfies_of_parts` and
  `s1_blocks_refines_of_parts` at the At-shaped parts; neither statement is
  restated or weakened.

## What remains

The `pre` at the pages' and the peel's vectors (`escapeEntryAt` plus
`S1BlocksPreAt`) is the one input this assembly still takes; it is the record's
own hypothesis, not the bundle.  The accumulator's fold — the `acc_pack` field of
the `VerdictStaging` the assembly carries — is `JsonS1BlocksAccFold`'s lane and
is not stated here.
-/
import LeanLLVM.Refinement.JsonS1BlocksUnitPost
import LeanLLVM.Refinement.JsonS1BlocksRunCharge

namespace LeanLLVM.Refinement.JsonS1BlocksFinalAt

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksExitFuel
open LeanLLVM.Refinement.JsonS1BlocksFacts
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksFinal
open LeanLLVM.Refinement.JsonS1BlocksUnitPost
open LeanLLVM.Refinement.JsonS1BlocksRunCharge

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The peel's call, with its outcome named

`S1BlocksUnitPostAt` hides the call's outcome behind an `∃`.  The tail and the
exit are stated at that outcome's memory, so the consumer that builds both needs
the witness once, by name. -/

/-- **The unit's post at one call, with the outcome named.**  The bundle's
clauses, read out at the call's own outcome `out`. -/
theorem exists_of_unitPostAt {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {blk0 : BitVec 64} {xp nxp xcarry count : Nat} {mem0 : Mem}
    {b ent xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (hu : S1BlocksUnitPostAt esc args mem next blk0 xp nxp xcarry count
      mem0 b ent xn arm bs) :
    ∃ (out : CallOutcome) (position : List Nat) (opened ppar : Bool),
      esc escapeListCallee args mem next = some out ∧
      EscapeReach blk0 xp nxp xcarry count position
        (flagBytes opened ++ flagBytes ppar) mem out.mem ∧
      position.length ≤ 64 ∧
      (∀ j, j < blocksOf bs.length →
        readBytes out.mem (b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes out.mem (b - 3) 3 = some [0, 0, 0] :=
  hu

/-! ### The tail's third disjunct, at the peel's call

`tail_third_at_ent` states `S1BlocksTail` from a `RunFrame`, the exit carry's
`ent` and the peel's `EscapeReach`.  The At bundle supplies that reach; the
outcome's memory is the tail's `M`. -/

/-- **The calling arm's tail, from the unit's At post.**  The bundle at the
peel's own argument vector, the loop's exit frame and the peel's word: the third
disjunct at the named outcome's memory.  This is
`JsonS1BlocksFinal.tail_calling_of_unitPost` with the instantiable hypothesis in
place of the bundle over arbitrary vectors. -/
theorem tail_calling_at {esc : Calls} {start : Mem}
    {xp xn nxp xcarry : Nat} {ps : List Nat} {bs : List UInt8} {c : FusedCarry}
    {count pages : Nat} {arm : BitVec 64} {shr ent b : Nat}
    {or135 andv w blk0 : BitVec 64} {or14 mask xs i : BitVec 64} {next : Nat}
    {mem0 : Mem}
    (hu : S1BlocksUnitPostAt esc
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry]
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) next
      blk0 xp nxp xcarry count mem0 b ent xn arm bs)
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    ∃ M : Mem, S1BlocksTail start ent xp nxp xcarry xn arm bs M := by
  obtain ⟨out, position, opened, ppar, _hcall, hreach, hlen, _hdoc, _hzero⟩ := hu
  exact ⟨out.mem, tail_third_at_ent hrun hent hshr hor hshrEq hand hw harm
    hreach hlen hxpSep⟩

/-- **The calling arm's tail, from the record's `pre` at the peel's vector.**
`peel_unitPostAt_of_pre` turns the escape entry and the staging into the At
bundle at the peel's stored memory; `tail_calling_at` reads the tail off it.  The
remaining input is the record's own `pre` at that vector, which is what
`escapeEntryAt` establishes a post from — not a promise about a window the
selection is never told. -/
theorem tail_calling_at_of_pre {esc : Calls} {base : Nat}
    (hEsc : escapeEntryAt esc base)
    {or14 mask xs i : BitVec 64} {xp nxp xcarry : Nat} {next : Nat}
    {mem0 memL : Mem} {b ent shr xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    {word : List UInt8}
    {start : Mem} {ps : List Nat} {c : FusedCarry} {count pages : Nat}
    (hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] (writeBytes memL (ent + 8 * shr) word) next)
    (hcountP : readBytes memL nxp 8 = some (wordBytes 8 count))
    (hcountLt : count < 2 ^ 64)
    (hsep : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent)
    (hp : S1BlocksPreAt mem0 b ent xp nxp xcarry xn arm bs)
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry count))
    (hsucc : shr + 1 = blocksOf bs.length)
    (hwlen : word.length = 8)
    (hroom : count + 64 ≤ xn + 64 * blocksOf bs.length)
    {or135 andv w blk0 : BitVec 64}
    (hstore : writeBytes memL (ent + 8 * shr) word =
      writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8))
    (hrun : RunFrame start xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw' : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    ∃ M : Mem, S1BlocksTail start ent xp nxp xcarry xn arm bs M := by
  have hcount := peel_count_read hsep hsucc hwlen hcountP
  have hu := peel_unitPostAt_of_pre hEsc hpre hcount hcountLt hp hframe hsucc
    hwlen hroom
  exact tail_calling_at (hstore ▸ hu) hrun hent hshr hor hshrEq hand hw' harm
    hxpSep

/-! ### The parts at the At form

`JsonS1BlocksFinal.S1BlocksRunParts` leaves the tail as a field.  Here the tail's
shape is stated at the peel's own call: the loop's exit frame (`loopRun_frame_ent`'s
conclusion, with the exit carry's `ent` identified) and the peel's word and
reach.  The run's returned word and memory are the peel's outcome, so they are
named once by the dependent `out` field. -/

/-- **The run's parts at the peel's call.**  The staging, the returned word, the
prefix and the exit as in `S1BlocksRunParts`; the tail's third disjunct is read
from `reach` at the loop's `RunFrame` and the peel's word, and the exit runs to
the same outcome memory. -/
structure S1BlocksRunPartsAt (esc : Calls) (args : List Value) (mem : Mem)
    (next b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) where
  /-- The caller's escape selection answers the same at every allocator base. -/
  nextIrr : CallsNextIrr esc
  /-- The entry-to-exit prefix, bounded by `8 * (%n >>> 6) + 21` and ending at
  the entry's exit terminal. -/
  prefixRun : OnePrefixBounded esc args mem b (BitVec.ofNat 64 bs.length)
    (entryGate arm) arm
  /-- The returned word. -/
  ret : BitVec 64
  /-- The staging's ASCII word. -/
  ascii : List (BitVec 64)
  /-- The staging's UTF-8 word. -/
  u8k : List (BitVec 64)
  /-- The staging's error bit. -/
  err : BitVec 1
  /-- The classifier's gate. -/
  gate : Bool
  /-- The staging at the document's block count. -/
  staging : VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err
  /-- The returned word is the staging's. -/
  word : ret = verdictWord ascii err
  /-- The peel's index. -/
  shr : Nat
  /-- The pages' count. -/
  count : Nat
  /-- The pages' extent. -/
  pages : Nat
  /-- The loop's exit carry. -/
  c : FusedCarry
  /-- The stream's positions. -/
  ps : List Nat
  /-- The peel's classifier words. -/
  or14 : BitVec 64
  /-- The peel's mask word. -/
  mask : BitVec 64
  /-- The peel's shift word. -/
  xs : BitVec 64
  /-- The peel's index argument. -/
  i : BitVec 64
  /-- The peel's `%or135`. -/
  or135 : BitVec 64
  /-- The peel's `%and137`. -/
  andv : BitVec 64
  /-- The peel's stored word. -/
  w : BitVec 64
  /-- The peel's block argument. -/
  blk0 : BitVec 64
  /-- The call's positions. -/
  position : List Nat
  /-- The call's first flag. -/
  opened : Bool
  /-- The call's second flag. -/
  ppar : Bool
  /-- The call's outcome. -/
  out : CallOutcome
  /-- The loop's exit frame (`loopRun_frame_ent`'s `RunFrame`). -/
  runFrame : RunFrame mem xp xn nxp xcarry ps bs c count pages
  /-- The loop's exit carry is at the caller's `%ent`
  (`loopRun_frame_ent`'s added conjunct). -/
  entEq : c.ent = ent
  /-- The peel's index is the exit carry's. -/
  shrEq : shr = c.i.toNat
  /-- The peel's word is the model's at the last block. -/
  hor : PeelWordAtModel or135 bs shr
  /-- The peel's index is the document's block count minus one. -/
  shrEqLen : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat
  /-- The peel's `%and137`. -/
  hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64
  /-- The peel's stored word. -/
  hw : w = or135 &&& limMask andv.toNat
  /-- The page calls. -/
  harm : arm &&& 2 ≠ (0 : BitVec 64)
  /-- The peel's call, at the entry array's stored memory. -/
  hcall : esc escapeListCallee
    [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
     .ptr xp, .ptr nxp, .ptr xcarry]
    (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) next = some out
  /-- The record's reach at the peel's call. -/
  reach : EscapeReach blk0 xp nxp xcarry count position
    (flagBytes opened ++ flagBytes ppar)
    (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) out.mem
  /-- The call's positions are a block's. -/
  reachLen : position.length ≤ 64
  /-- The array's separation at the peel's call. -/
  xpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
    xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent
  /-- The exit's charge at the terminal's own `ret` and the outcome's memory. -/
  exitBounded : ∃ jE : Nat, jE ≤ exitCharge ∧
    ∀ e : State, ExitTermCells b (BitVec.ofNat 64 bs.length) (entryGate arm) arm e →
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
        some (.ret (some (.int 64 ret)) out.mem)

/-- **The residual, from the At-shaped parts.**  The tail is
`tail_third_at_ent` at the loop's exit frame and the peel's reach; the exit runs
to the same outcome memory, so the residual's `∃ ret M` names it once.  The
prefix is moved from `s1BlocksInit` to the caller's base by
`s1BlocksRun_entry_next`, exactly as `s1BlocksResiduals_of_parts` does. -/
theorem s1BlocksResiduals_of_atParts {esc : Calls} {args : List Value} {mem : Mem}
    {next b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (h : S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨hIrr, hprefix, ret, ascii, u8k, err, gate, hstage, hword, shr, count,
    pages, c, ps, or14, mask, xs, i, or135, andv, w, blk0, position, opened, ppar,
    out, hrun, hent, hshr, hor, hshrEq, hand, hw, harm, hcall, hreach, hlen,
    hxpSep, jE, hjE, hexit⟩ := h
  obtain ⟨e, N, hN, htrace, hterm⟩ := hprefix
  have htrace' : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e := by
    intro k
    rw [s1BlocksRun_entry_next hIrr (N + k)]
    simpa only [s1BlocksInit_entryState] using htrace k
  have htail : S1BlocksTail mem ent xp nxp xcarry xn arm bs out.mem :=
    tail_third_at_ent hrun hent hshr hor hshrEq hand hw harm hreach hlen hxpSep
  exact ⟨⟨ret, out.mem, ascii, u8k, err, gate, e, N, jE, hstage, hword, htail,
    hN, htrace', hterm, hjE, hexit e hterm⟩⟩

/-- **The bundle, from the At-shaped parts.**  `s1BlocksFacts_of_residuals` at
the residual above. -/
theorem s1BlocksFacts_of_atParts {esc : Calls} {args : List Value} {mem : Mem}
    {next b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs :=
  s1BlocksFacts_of_residuals hargs (s1BlocksResiduals_of_atParts h)

/-! ### The record instance and the refinement -/

/-- **The block unit satisfies its record, from the At-shaped parts.**  This is
`JsonS1BlocksFinal.s1_blocks_satisfies_of_parts` with the tail's hypothesis read
at the peel's own call; the instance's statement is not restated. -/
theorem s1_blocks_satisfies_of_atParts {esc : Calls}
    (h : ∀ (args : List Value) (mem : Mem) (next b ent xp nxp xcarry xn : Nat)
        (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  s1_blocks_satisfies fun args mem next b ent xp nxp xcarry xn arm bs _ hargs =>
    s1BlocksFacts_of_atParts hargs
      (h args mem next b ent xp nxp xcarry xn arm bs)

/-- **The record instance, unconditionally over the selection, from At-shaped
parts each selection supplies.** -/
theorem s1_blocks_satisfies_all_of_atParts
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem)
        (next b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    ∀ esc : Calls, Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  fun esc => s1_blocks_satisfies_of_atParts (h esc)

/-- **The refinement, from the At-shaped parts.**  This is
`JsonS1BlocksFinal.s1_blocks_refines_of_parts`'s statement, unchanged. -/
theorem s1_blocks_refines_of_atParts
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem)
        (next b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    s1_blocks_refines :=
  s1_blocks_refines_of_satisfies (s1_blocks_satisfies_all_of_atParts h)

/-! ### Axiom footprints

`exists_of_unitPostAt` and `tail_calling_at` are `S1BlocksUnitPostAt`'s
destructuring and `tail_third_at_ent`'s statement; `tail_calling_at_of_pre` adds
`peel_unitPostAt_of_pre`.  The parts are a structure; the residual is
`runFuel_next_irr` at the two entry states and the tail's own composition; the
bundle, the instance and the refinement are
`JsonS1BlocksFinal`'s and `JsonS1BlocksFacts`'s statements unchanged.  No
statement reaches `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.exists_of_unitPostAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.tail_calling_at
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.tail_calling_at_of_pre
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.S1BlocksRunPartsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.s1BlocksResiduals_of_atParts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.s1BlocksFacts_of_atParts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.s1_blocks_satisfies_of_atParts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.s1_blocks_satisfies_all_of_atParts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFinalAt.s1_blocks_refines_of_atParts

end LeanLLVM.Refinement.JsonS1BlocksFinalAt
