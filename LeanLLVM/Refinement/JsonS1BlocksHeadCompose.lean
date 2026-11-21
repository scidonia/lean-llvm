/-
The bounded one-prefix on both of the phase's arms, from the fused loop's head.

`JsonS1BlocksPrefixSplit` states the prefix's charge at the fused loop's head but
stops there: `s1BlocksPrefix_head_of_handoff` ends at `stateAt envL core` with
the latch's `FusedLatch` and the entry's cells, and says nothing about the head's
own step or the loop.  `JsonS1BlocksRunFrame.loopRun_frame` runs the loop's
calling segment from a `LoopInv` — the latch's `FusedInv` plus the model-side
`LoopCarry` — but its terminal is a `FusedExit` with no environment cells, and
`ExitTermCells.fused` needs `EntryCells` at the exit environment, which
`FusedExit` does not carry (`%n`, `%conv`, `%arm` and `%and` are absent, and the
exit environment is existential).  The committed producer of an exit terminal
*with* cells is the register-level loop `fusedInvCells_runFuel`, which yields
`FusedTermCells`.  So the head has two lanes that meet at the same body state and
the same charge:

* the terminal — the latch's step and `fusedInvCells_runFuel`, whose
  `FusedTermCells` is `ExitTermCells.fused`'s payload with
  `entryCells_ifEnd98Env` supplying the cells at the body's environment;
* the run's frame — the latch's step and `loopRun_frame`, over the caller's
  staging and the escape unit's post.

This module states both, joins them to the split, and closes the phase's other
arm from the committed prefix's own exit case.

## What is proved

* `storeAll_of_pageModel` — **`loopRun_frame`'s `hstoreAll`** from the committed
  page identity: `JsonS1BlocksPageModel.pageModel`'s `storeW` at the pages' own
  bound, the windows being the block's halves and the carried state the model's.
  The pages' premise is `c.i.toNat < c.shr.toNat` — where the induction applies
  it — rather than the committed `hstoreAll`'s `c.i.toNat < blocksOf bs.length`.
* `frameCarry_nil` — **the head's staging is the chain's first node**: the
  count's slot, the stream's prefix and the array's presence are
  `JsonS1BlocksRunFrame.FrameCarry`'s clauses at no pages, so the three facts
  `loopRun_frame` takes are the committed producer's own.
* `headExit` — **the head reaches an exit terminal**: the latch's two arms
  (`fused_latch_exit`, `fused_latch_loop`) and the register-level loop reach
  `ExitTermCells` in `5 * %shr + 6`, carrying the entry's cells.
* `headRunFrame` — **the head's calling run**: the latch's back edge, the
  model-side `LoopCarry` and the caller's staging are `loopRun_frame`'s inputs,
  at `5 * (%shr - (%i + 1)) + 5` and the loop's own `RunFrame`.
* `onePrefixBounded_of_head` — **the head's bound inside the prefix's**: the
  head segment `N + (2 + k) ≤ 3 * %shr + 15` and the head's own `≤ 5 * %shr + 6`
  are `OnePrefixBounded`'s `8 * %shr + 21` by `onePrefixBounded_of_split`.
* `onePrefixBounded_of_handoff` — **the hand-off arm**, from the phase's trace to
  the hand-off terminal: `s1BlocksPrefix_head_of_handoff` then
  `onePrefixBounded_of_head`.  Its inputs are that theorem's, so a caller that
  has the phase's bounded terminal applies this directly.
* `onePrefixBounded_of_ascii` — **the phase's exit arm**: the terminal at
  `N ≤ 3 * %shr + 8` is `ExitTermCells.ascii`, inside `8 * %shr + 21`; this is
  `s1BlocksPrefix_exit_bounded`'s exit case at the trace it exposes.
* `onePrefixBounded_of_arms` — **both arms**: `AsciiTermStreamCells`'s two
  constructors, the exit arm above and the hand-off arm above.

## What remains

The hand-off arm's inputs beyond the phase's are `s1BlocksPrefix_head_of_handoff`'s
— the hand-off's window and register carries — so the module invents no model
fact.  `headRunFrame`'s inputs are `loopRun_frame`'s, named at the head it is
applied to:

* `hstoreAll` — produced by `storeAll_of_pageModel` from `pageModel`'s `storeW`,
  the windows and the carried state;
* `hcount0`, `hstream0`, `hpresent0` — the count's slot at `xn`, the stream's
  prefix `ps` and the entry array's presence at the head's own memory, which are
  `JsonS1BlocksRunFrame.FrameCarry`'s three clauses at a loop head
  (`frameCarry_nil`).  They are the caller's staging at the first page's memory,
  and this module does not derive them (the head's memory is the page's, not the
  run's);
* the escape unit's post (`S1BlocksUnitPost`) — the call resolves, the document
  and the three staged zeroes survive it, and each call's reach is an
  `EscapeReach` at its own count; this is
  `JsonS1BlocksFinal.loopRun_frame_of_unitPost`'s shape and
  `JsonS1BlocksUnitPost`'s to produce from the record;
* the separation of the entry array from the stream, the count's slot and the
  carry, and their pairwise separation.

`headRunFrame` needs the latch's back edge (`i + 1 ≠ %shr`); the bound's exit has
no loop page and is `headExit`'s, so a caller that wants both states splits on
`evalICmp .eq (i + 1) %shr` as `handoffPrefix_exit_bounded` does.  The split's
own charge is not an input: `onePrefixBounded_of_head` re-derives
`N + (2 + k) ≤ 3 * %shr + 15` from the phase's `N ≤ 3 * %shr + 8` and `k ≤ 5`.
-/
import LeanLLVM.Refinement.JsonS1BlocksPrefixSplit
import LeanLLVM.Refinement.JsonS1BlocksPageModel
import LeanLLVM.Refinement.JsonS1BlocksFinal

namespace LeanLLVM.Refinement.JsonS1BlocksHeadCompose

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksStream
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksPrefixSplit
open LeanLLVM.Refinement.JsonS1BlocksPageModel
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksFinal
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The loop's staging

`loopRun_frame` takes the page's store identity as `hstoreAll`, quantified over
every carry and every pair of loaded words.  The committed producer is the page
model: at a full block whose windows are the block's halves and whose carried
state is the model's, the stored word is `stage1Word`.  The pages the induction
applies it to are inside the bound (`LoopInv.index_lt`), so the full-block
premise is the carry's own `%shr`. -/

/-- **`loopRun_frame`'s store identity, from the page model.**  `PageModel`'s
`storeW` with its premises read from the run: the block is full because the page
is inside the bound, the carried state is `PageCarry`, and the two loaded windows
are the block's halves. -/
theorem storeAll_of_pageModel {bs : List UInt8}
    (hwin : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < c.shr.toNat →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      bs73 = (docBlock bs c.i.toNat).take 32 ∧
      bs74 = (docBlock bs c.i.toNat).drop 32)
    (hcarry : ∀ (c : FusedCarry), c.i.toNat < c.shr.toNat → PageCarry bs c)
    (hshrBlocks : ∀ (c : FusedCarry), 64 * c.shr.toNat ≤ bs.length) :
    ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < c.shr.toNat →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat := by
  intro c bs73 bs74 hi h73 h74
  obtain ⟨h73', h74'⟩ := hwin c bs73 bs74 hi h73 h74
  refine (pageModel bs).storeW c bs73 bs74 ?_ (hcarry c hi) h73' h74'
  have := hshrBlocks c
  omega

/-! ### The head's starting staging is the chain's first node

`loopRun_frame`'s three staging facts — the count's slot, the stream's prefix and
the array's presence — are `FrameCarry`'s clauses at a loop head with no pages
behind it, `CallChain.nil` being the chain.  So a caller that supplies them at
the head supplies the frame's first node, which is the form the committed
producer (`FrameCarry`) names. -/

/-- **The starting staging is `FrameCarry` at no pages.**  A carry whose memory
is the run's start, the count's slot at `xn`, the stream's prefix `ps` and the
entry array's presence are `JsonS1BlocksRunFrame.FrameCarry`'s fields with the
empty chain. -/
theorem frameCarry_nil {start : Mem} {xp xn nxp xcarry : Nat} {bs : List UInt8}
    {ps : List Nat} {c : FusedCarry}
    (hstart : c.mem = start)
    (hcount : readBytes c.mem nxp 8 = some (wordBytes 8 xn))
    (hstream : StreamPrefix c.mem xp xn ps)
    (hpresent : HasBytes c.mem c.ent (8 * blocksOf bs.length)) :
    FrameCarry start xp xn nxp xcarry bs c xn 0 :=
  { chain := by rw [hstart]; exact CallChain.nil
    countRead := hcount
    stream := ⟨ps, hstream⟩
    present := hpresent }

/-! ### The head's terminal

The latch's two arms and the register-level loop.  The cells travel with
`entryCells_ifEnd98Env` into the body's environment, so the terminal's
`EntryCells` is the head's rather than an assumption. -/

/-- **One register-level terminal is an exit terminal.**  `FusedTermCells` is
`ExitTermCells.fused`'s payload: the cells, the accumulator's four lanes and the
exit's facts at the same environment. -/
theorem exitTermCells_of_fusedTerm {b : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm : BitVec 64} {e : State} (h : FusedTermCells n conv arm e) :
    ExitTermCells b n conv arm e := by
  cases h with
  | exit env s c gate esc hcells hascii hexit =>
      exact ExitTermCells.fused env s c gate esc hcells hascii hexit

/-- **The head reaches an exit terminal.**  From the fused loop's head — the
latch at `stateAt env s` — the latch's step and the register-level loop reach
`for.end101` in at most `5 * %shr + 6`, on either arm: at the bound the latch's
own step is `ExitTermCells.fused`, and inside the bound the loop's
`fusedInvCells_runFuel` is.  The entry's cells at the head are what the terminal
carries, through `entryCells_ifEnd98Env`. -/
theorem headExit {esc : Calls} {b : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm : BitVec 64} {doc : Nat → List UInt8}
    (env : Env) (s : State) (c : FusedCarry) (i0 : BitVec 64)
    (gate escBit : BitVec 1)
    (hl : FusedLatch env s i0 c gate escBit)
    (hcells : EntryCells env n conv arm)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, esc escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      esc escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (e : State) (M : Nat), M ≤ 5 * c.shr.toNat + 6 ∧
      (∀ k, runFuel (s1BlocksCallsEsc esc) (M + k) s1BlocksFunction (stateAt env s) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      ExitTermCells b n conv arm e := by
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (i0 + 1) c.shr) with hbit | hbit
  · -- the back edge and the register-level loop
    obtain ⟨hstep, hinv'⟩ :=
      fused_latch_loop esc env s i0 c gate escBit hl hbit hshr57
    have hcells' : EntryCells (ifEnd98Env env i0 c.shr) n conv arm :=
      entryCells_ifEnd98Env env i0 c.shr hcells
    have hinvCells : FusedInvCells (ifEnd98Env env i0 c.shr)
        (stateAt (ifEnd98Env env i0 c.shr)
          { s with pc := "for.body54", pre := some "if.end98" })
        c gate escBit n conv arm :=
      { toFusedInv := hinv'
        n_cell := hcells'.n_cell
        conv_cell := hcells'.conv_cell
        arm_cell := hcells'.arm_cell
        and_cell := hcells'.and_cell
        shr_cell := hcells'.shr_cell }
    obtain ⟨e', j, hj, hterm, hrun⟩ :=
      fusedInvCells_runFuel esc (ifEnd98Env env i0 c.shr)
        (stateAt (ifEnd98Env env i0 c.shr)
          { s with pc := "for.body54", pre := some "if.end98" })
        c gate escBit n conv arm doc hshr57 hinvCells hb3 hgap hdoc hzero hcall hkeep
    refine ⟨e', 1 + j, by omega, ?_, exitTermCells_of_fusedTerm hterm⟩
    intro k
    rw [show 1 + j + k = 1 + (j + k) from by omega,
      runFuel_jump_prefix hstep (j + k)]
    exact hrun k
  · -- the bound's exit: the latch's one step
    obtain ⟨hstep, hexit⟩ := fused_latch_exit esc env s i0 c gate escBit hl hbit
    refine ⟨stateAt (ifEnd98Env env i0 c.shr)
        { s with pc := "for.end101", pre := some "if.end98" },
      1, by omega, ?_,
      ExitTermCells.fused (ifEnd98Env env i0 c.shr)
        (stateAt (ifEnd98Env env i0 c.shr)
          { s with pc := "for.end101", pre := some "if.end98" }) c gate escBit
        (entryCells_ifEnd98Env env i0 c.shr hcells) hl.ascii_len hexit⟩
    intro k
    rw [runFuel_jump_prefix hstep k]

/-! ### The head's calling run

`loopRun_frame` from the head: the latch's back edge gives the body's `FusedInv`,
the model-side `LoopCarry` completes the `LoopInv`, and the caller's staging and
the escape unit's post are the induction's remaining inputs.  The charge is the
loop's own `5 * (%shr - (%i + 1)) + 5`; the latch's one step is prepended. -/

/-- **The head's calling run, with its frame.**  From the fused loop's head, on
the back edge (`i + 1 ≠ %shr`), the model-side carry, the staging and the unit's
post reach `for.end101` in `1 + j` with `j ≤ 5 * (%shr - (%i + 1)) + 5`,
carrying `FusedExit` and the loop's `RunFrame`.  This is `loopRun_frame` at the
head, with the latch's step and its `FusedInv` in front. -/
theorem headRunFrame (sel : Calls) (start : Mem) (xp xn nxp xcarry : Nat)
    (bs : List UInt8)
    (hstoreAll : ∀ (c : FusedCarry) (bs73 bs74 : List UInt8),
      c.i.toNat < blocksOf bs.length →
      readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73 →
      readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74 →
      (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat)
    (env : Env) (s : State) (c : FusedCarry) (i0 : BitVec 64) (gate : BitVec 1)
    (ps : List Nat)
    (hl : FusedLatch env s i0 c gate 0)
    (hbit : evalICmp .eq (i0 + 1) c.shr = 0)
    (hcarry : LoopCarry start xp xn ps bs c)
    (hstart : c.mem = start)
    (hblocks : blocksOf bs.length = c.shr.toNat + 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hblocks64 : blocksOf bs.length < 2 ^ 64)
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
      (∀ k, runFuel (s1BlocksCallsEsc sel) (1 + j + k) s1BlocksFunction
        (stateAt env s) = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) := by
  obtain ⟨hstep, hinv'⟩ := fused_latch_loop sel env s i0 c gate 0 hl hbit hshr57
  obtain ⟨env', e, c', count, pages, j, hj, hexit, hfr, hrun⟩ :=
    loopRun_frame_of_unitPost sel start xp xn nxp xcarry bs hstoreAll
      (ifEnd98Env env i0 c.shr)
      (stateAt (ifEnd98Env env i0 c.shr)
        { s with pc := "for.body54", pre := some "if.end98" })
      c gate ps hstart hblocks hshr57 hshrLe hblocks64
      { toFusedInv := hinv', model := hcarry }
      hcount0 hstream0 hpresent0 hb3 hgap hdoc hzero hentXp hentNxp hentXc
      hxpNxp hxpXc hu
  refine ⟨env', e, c', count, pages, j, hj, hexit, hfr, ?_⟩
  intro k
  rw [show 1 + j + k = 1 + (j + k) from by omega,
    runFuel_jump_prefix hstep (j + k)]
  exact hrun k

/-! ### The head's bound inside the prefix's

The split's `3 * %shr + 15` and the head's own `5 * %shr + 6` are the prefix's
`8 * %shr + 21`. -/

/-- **The one-prefix from the head.**  The phase's charge `N ≤ 3 * %shr + 8` and
the head segment `2 + k` are the split's `3 * %shr + 15`; the head's own exit
segment is `5 * %shr + 6`; `onePrefixBounded_of_split` puts their sum inside
`8 * %shr + 21`, ending at `ExitTermCells`. -/
theorem onePrefixBounded_of_head {esc : Calls} {args : List Value} {mem : Mem}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    {doc : Nat → List UInt8}
    (env : Env) (s : State) (c : FusedCarry) (i0 : BitVec 64) (k N : Nat)
    (gate escBit : BitVec 1)
    (hhead : ∀ k', runFuel (s1BlocksCallsEsc esc) (N + (2 + k) + k')
      s1BlocksFunction (s1BlocksInit args mem) =
      runFuel (s1BlocksCallsEsc esc) k' s1BlocksFunction (stateAt env s))
    (hN : N ≤ 3 * (n >>> 6).toNat + 8) (hk : k ≤ 5)
    (hl : FusedLatch env s i0 c gate escBit)
    (hcells : EntryCells env n conv arm)
    (hshrEq : c.shr.toNat = (n >>> 6).toNat)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, esc escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r : CallOutcome),
      esc escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    OnePrefixBounded esc args mem b n conv arm := by
  obtain ⟨e, M, hM, hrun, hterm⟩ :=
    headExit env s c i0 gate escBit hl hcells hshr57 hb3 hgap hdoc hzero hcall hkeep
  refine onePrefixBounded_of_split (eH := stateAt env s) (e := e) (N := N) (k := k)
    (M := M) hhead hN hk hrun ?_ hterm
  rw [← hshrEq]
  exact hM

/-! ### The hand-off arm

`s1BlocksPrefix_head_of_handoff` produces the head from the phase's trace; the
head's position is what `onePrefixBounded_of_head` consumes.  The transports are
the head bundle's own identities: the latch's `%shr`, `%b`, `%ent` are the
hand-off terminal's, and its three pointers are the cells' `%xp`, `%nxp` and
`%xcarry`. -/

/-- **The hand-off arm's bounded prefix.**  From the phase's trace at the hand-off
terminal (`N ≤ 3 * %shr + 8`) and the hand-off's carries, the head split and the
head's own exit segment reach `ExitTermCells` inside `OnePrefixBounded`'s
`8 * %shr + 21`. -/
theorem onePrefixBounded_of_handoff (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
    (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
    (v : ForBodyValues) (N : Nat)
    (hphase : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
        .int 64 arm] mem) =
      runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction (asciiHandoffState env s c v))
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hinv : AsciiInvCells env s c b n (entryGate arm) arm)
    (hv : v = asciiValues c bs2 bs3)
    (hread2 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2)
    (hread3 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3)
    (hne : c.i + 1 ≠ c.shr)
    (hbit : evalICmp .ult (v.i + 1) c.shr = 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hcar : HandoffCarries esc env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    OnePrefixBounded esc [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem b n (entryGate arm) arm := by
  obtain ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq0, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', hrun, _hle⟩ :=
    s1BlocksPrefix_head_of_handoff esc mem b ent xp nxp xcarry n arm bs doc bs73 bs74
      env s c bs2 bs3 v N hphase hN hinv hv hread2 hread3 hne hbit hshr57 hb3 hxp
      hnxp hxcarry hcar
  have hshreq : c.shr = n >>> 6 := by
    have h1 := hinv.bound
    rw [hinv.shr_cell] at h1
    simpa using (Option.some.inj h1).symm
  have hshrEq : c'.shr.toNat = (n >>> 6).toNat := by
    rw [hshrEq0, hshreq]
  have hshift57 : c'.shr.toNat < 2 ^ 57 := by
    rw [hshrEq0]
    exact hshr57
  have hb3' : 3 ≤ c'.b := by
    simpa only [hbEq, hinv.b_eq] using hb3
  have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
    rw [hbEq, hentEq, hshrEq0]
    exact hcar.entGap
  have hdocLoop : ∀ j, j < c'.shr.toNat →
      readBytes c'.mem (c'.b + 64 * j) 64 = some (doc j) := by
    intro j hj
    rw [hshrEq0] at hj
    rw [hbEq]
    exact hdoc' j hj
  have hzeroLoop : readBytes c'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
    rw [hbEq]
    exact hzero'
  have hkeep' : ∀ (or14 mask xs i : BitVec 64) (m : Mem) (next : Nat)
      (r : CallOutcome),
      esc escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] m next = some r →
      (∀ j, j < c'.shr.toNat → readBytes r.mem (c'.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c'.b - 3) 3 = some [0, 0, 0] := by
    intro or14 mask xs i m next r hc
    have h := hcar.keep or14 mask xs i m next r
      (by simpa only [hxpEq, hnxpEq, hxcEq] using hc)
    simpa only [hbEq, hshrEq0] using h
  exact onePrefixBounded_of_head (i0 := _) envL core c' k N
    (evalICmp .eq (entryGate arm) 0) (evalICmp .eq (arm &&& 2) 0)
    hrun hN hk hl hcellsL hshrEq hshift57 hb3' hgap' hdocLoop hzeroLoop
    hcar.call hkeep'

/-! ### The phase's exit arm

The phase can also terminate at its own bound (`c.i + 1 = c.shr`), with no fused
page.  That terminal is `ExitTermCells.ascii` already, and its `3 * %shr + 8` is
inside the prefix's `8 * %shr + 21`; this is `s1BlocksPrefix_exit_bounded`'s exit
case read at the trace the phase exposes. -/

/-- **The exit arm's bounded prefix.**  A phase terminal at `asciiExitState` with
`N ≤ 3 * %shr + 8` is `ExitTermCells.ascii` at `N`, inside
`OnePrefixBounded`'s `8 * %shr + 21`. -/
theorem onePrefixBounded_of_ascii {esc : Calls} {args : List Value} {mem : Mem}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    (env : Env) (s : State) (c : AsciiCarry) (N : Nat)
    (hphase : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit args mem) =
      runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction (asciiExitState env s c))
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hinv : AsciiInvCells env s c b n conv arm)
    (hbound : c.i + 1 = c.shr) :
    OnePrefixBounded esc args mem b n conv arm :=
  ⟨asciiExitState env s c, N, by omega, hphase,
    ExitTermCells.ascii env s c hinv hbound⟩

/-! ### Both arms

The phase's bounded terminal carries either arm; the exit arm is above and the
hand-off arm is `onePrefixBounded_of_handoff` at the carries the caller's
`hready` produces.  Nothing at the terminal is a fused head unless the hand-off
constructor is the one the run reached. -/

/-- **The one-prefix on both of the phase's arms.**  From the phase's trace at an
`AsciiTermStreamCells` terminal (`N ≤ 3 * %shr + 8`), the exit arm is
`ExitTermCells.ascii` and the hand-off arm is the head split and the head's exit
segment; both are inside `OnePrefixBounded`'s `8 * %shr + 21`.  The hand-off
carries are the caller's `hready`, at the terminal's own witness. -/
theorem onePrefixBounded_of_arms {esc : Calls} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {n arm : BitVec 64}
    {bs : List UInt8} {doc : Nat → List UInt8} {bs73 bs74 : List UInt8}
    (e : State) (N : Nat)
    (hphase : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
        .int 64 arm] mem) =
      runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hterm : AsciiTermStreamCells b n (entryGate arm) arm xp nxp xcarry e)
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
    OnePrefixBounded esc [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem b n (entryGate arm) arm := by
  cases hterm with
  | exit env s c hinv hbound =>
      exact onePrefixBounded_of_ascii (conv := entryGate arm) env s c N hphase hN
        hinv hbound
  | handoff env s c bs2 bs3 v hinv hstream h2 h3 hne hv =>
      have hcar := hready env s c bs2 bs3 v hinv hstream h2 h3 hne hv
      have hshreq : c.shr = n >>> 6 := by
        have h1 := hinv.bound
        rw [hinv.shr_cell] at h1
        simpa using (Option.some.inj h1).symm
      have hshr57' : c.shr.toNat < 2 ^ 57 := by
        rw [hshreq]
        exact hshr57
      have hb3' : 3 ≤ c.b := by
        rw [hinv.b_eq]
        exact hb3
      have hbit : evalICmp .ult (v.i + 1) c.shr = 1 := by
        show BitVec.ofBool (BitVec.ult (v.i + 1) c.shr) = 1
        rw [(BitVec.ult_iff_toNat_lt).2 hcar.irow]
        rfl
      exact onePrefixBounded_of_handoff esc mem b ent xp nxp xcarry n arm bs doc
        bs73 bs74 env s c bs2 bs3 v N hphase hN hinv hv h2 h3 hne hbit hshr57' hb3'
        hstream.xp_cell hstream.nxp_cell hstream.xcarry_cell hcar

/-! ### Axiom footprints

`storeAll_of_pageModel` is `JsonS1BlocksPageModel.pageModel`'s `storeW` and the
block's fullness; `headExit` is `fused_latch_exit`/`fused_latch_loop` and
`fusedInvCells_runFuel`'s register-level loop; `headRunFrame` is
`JsonS1BlocksFinal.loopRun_frame_of_unitPost`, i.e. `loopRun_frame`'s own
induction; the bound is `JsonS1BlocksPrefixSplit.onePrefixBounded_of_split`;
`onePrefixBounded_of_handoff` is `s1BlocksPrefix_head_of_handoff` and the
transports; the arms are `ExitTermCells.ascii` and the hand-off arm.  No
statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.storeAll_of_pageModel
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.frameCarry_nil
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.exitTermCells_of_fusedTerm
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.headExit
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.headRunFrame
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.onePrefixBounded_of_head
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.onePrefixBounded_of_handoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.onePrefixBounded_of_ascii
#print axioms LeanLLVM.Refinement.JsonS1BlocksHeadCompose.onePrefixBounded_of_arms

end LeanLLVM.Refinement.JsonS1BlocksHeadCompose
