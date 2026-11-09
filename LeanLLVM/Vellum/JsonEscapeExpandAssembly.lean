/-
The expander's bundle, assembled from the three runs it still takes.

`JsonEscapeExpandRun` states the claim with `ExpandFacts` as its hypothesis, and
two of the bundle's five proof fields are already discharged: the exit
continuation (`expandExit_satisfied`, unconditional in the staging its word
carries) and the seed's empty-list arm (`emptySeedRun`).  This module assembles
the bundle from the rest, so a consumer's hypothesis is the staging and exactly
the three body runs:

* `loop` — the iteration arm, `assemblyLatchStep`;
* `refuse` — the refusal arm, `assemblyRefusalArm`;
* the non-empty seed arm — the pre-scan plus one iteration to the latch.

`exit` is **derived** here rather than carried as a hypothesis: `expandExit_satisfied`
proves `ExpandExit` at any staging the exit word admits, so a carried field would be
an obligation nobody has to discharge.  `seed` is derived for the same reason in its
empty arm: the assembly splits on the caller's cursor `k0`, sends `k0 = nps` to
`emptySeedRun`, and takes the latch arm from the hypothesis otherwise.

The bundle is not widened: `ExpandFacts` keeps the fields `JsonEscapeExpandRun`
states, and the three residuals live in `ExpandArms`, beside the consumer rather
than inside the completion condition.
-/
import LeanLLVM.Vellum.JsonEscapeExpandFacts
import LeanLLVM.Vellum.JsonEscapeFinalCopy

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-- **The three runs `ExpandFacts` still takes**, at one staging.

Every witness is the one `ExpandFacts` names, and `staging` is the record's `pre`
at those witnesses, so each run below is a statement about the caller's own
staging.  The exit continuation is absent because it is proved; the empty seed arm
is absent because it is proved. -/
structure ExpandArms (args : List Value) (mem : Mem) (next : Nat) where
  /-- The body the run decodes. -/
  body : List UInt8
  /-- The classifier state the position list is read off. -/
  st : ClassState
  /-- The destination base. -/
  dst : Nat
  /-- The outcome the caller's staging names. -/
  goal : EscapeOutcome
  /-- The caller's position list, as `*xp` holds it. -/
  ps : List Nat
  /-- The document offset of the body's first byte. -/
  pos0 : Nat
  /-- The body base the latch's `%p` reads. -/
  pb : Nat
  /-- The position stream base the latch's `%xp` reads. -/
  xp : Nat
  /-- The escape table's base, which the latch's `%tab` reads. -/
  tab : Nat
  /-- The offset slot's base, which the refusal stores to. -/
  err : Nat
  /-- The cursor slot's base, which the refusal and the success path store to. -/
  xj : Nat
  /-- The caller's staging, named by the record's own `pre` and identified with
  these witnesses. -/
  staging : ExpandStaging args mem next body st dst (expandPosCount args) goal pb xp
    tab pos0 (expandBodyLen args) ps err xj
  /-- **The iteration arm**: the run from the latch back to the latch, crossing
  `while.body6`, `if.end`, the copy at `while.body.i91` and the escape emitter. -/
  loop : assemblyLatchStep args mem next body st dst (expandPosCount args) goal pb xp
    tab pos0 (expandBodyLen args) ps err xj staging
    (decodeIterCost (expandBodyLen args))
  /-- **The refusal arm**: the run from the latch to `cleanup41` at a position that
  refuses, crossing the same blocks as the iteration. -/
  refuse : assemblyRefusalArm args mem next body st dst (expandPosCount args) goal pb
    xp tab pos0 (expandBodyLen args) ps err xj staging
    (decodeIterCost (expandBodyLen args))
  /-- **The entry stage's latch arm**: the pre-scan plus one iteration to the latch.
  The empty-list arm is `emptySeedRun`, so a producer supplies this one only. -/
  seedLatch : ∃ (s : State) (c j : Nat),
    j ≤ preScanFuel (expandPosCount args) + decodeIterCost (expandBodyLen args) ∧
    AssemblyLatchInv body st dst (expandPosCount args) goal pb xp tab pos0
      (expandBodyLen args) ps err xj mem (expandPosCount args) c s ∧
    ∀ k, runFuel escapeCalls (j + k) usDecFunction
        (EntryState usDecFunction args mem next) =
      runFuel escapeCalls k usDecFunction s

/-- **The bundle from the three runs.**  `exit` is `expandExit_satisfied` and the
seed's empty arm is `emptySeedRun`; the latch arm is the hypothesis.  The split on
the caller's cursor is exhaustive because the staging bounds it by the list's
length and the record's `pre` names it at the cursor slot. -/
def expandFacts_of_arms {args : List Value} {mem : Mem} {next : Nat}
    (h : ExpandArms args mem next) : ExpandFacts args mem next := by
  obtain ⟨body, st, dst, goal, ps, pos0, pb, xp, tab, err, xj, hstaging, hloop,
    hrefuse, hseed⟩ := h
  -- the classifier state is the one the staging fixes, so the fields read at it
  have hst : st = (⟨true, false⟩ : ClassState) := hstaging.2.2.1
  subst hst
  refine
    { body := body
      st := ⟨true, false⟩
      dst := dst
      goal := goal
      ps := ps
      pos0 := pos0
      pb := pb
      xp := xp
      tab := tab
      err := err
      xj := xj
      staging := hstaging
      loop := hloop
      refuse := hrefuse
      seed := ?_
      exit := expandExit_satisfied }
  -- the seed is a proposition, so the staging's existentials eliminate here
  have hstage := hstaging
  obtain ⟨-, hargs, -, hbodyE, h32, hdec, hmap, -, -, -, hwalk⟩ := hstage
  obtain ⟨-, -, hpslen, -, -⟩ := hdec
  obtain ⟨k0, hxj, -, hgoalwalk⟩ := hwalk
  have hnpslen : (escAt body ⟨true, false⟩ 0).length = expandPosCount args := by
    show (escapePositionsFrom body ⟨true, false⟩).length = expandPosCount args
    rw [← hmap, List.length_map]
    exact hpslen
  have hn64 : expandBodyLen args < 2 ^ 64 := by omega
  have hnpsle : expandPosCount args ≤ expandBodyLen args := by
    have hble := escAt_length_le body ⟨true, false⟩ 0
    have hblen : body.length = expandBodyLen args :=
      JsonEntrySteps.readBytes_length mem pb (expandBodyLen args) hbodyE
    omega
  have hnps64 : expandPosCount args < 2 ^ 64 := by omega
  by_cases hk : k0 = expandPosCount args
  · have hdrop : (escAt body ⟨true, false⟩ 0).drop (expandPosCount args) = [] := by
      rw [List.drop_eq_nil_of_le]
      omega
    have hgoal : goal = .decoded body (expandPosCount args) := by
      rw [hgoalwalk, hk, hmap, show escapePositionsFrom body ⟨true, false⟩ =
        escAt body ⟨true, false⟩ 0 from rfl, hdrop, escapeDecodeGo_nil,
        List.nil_append, List.drop_zero]
    exact Or.inr (emptySeedRun (mem := mem) (next := next) hargs hxj hnpslen hk hnps64
      goal hgoal hstaging)
  · exact Or.inl hseed

/-- **The bundle from the three runs**, at explicit binders.  A consumer that
carries the witnesses as parameters rather than as a structure uses this form; the
two are the same term. -/
def expandFacts_of_runs (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst : Nat) (goal : EscapeOutcome)
    (ps : List Nat) (pos0 : Nat) (pb xp tab err xj : Nat)
    (hstaging : ExpandStaging args mem next body st dst (expandPosCount args) goal pb
      xp tab pos0 (expandBodyLen args) ps err xj)
    (hloop : assemblyLatchStep args mem next body st dst (expandPosCount args) goal pb
      xp tab pos0 (expandBodyLen args) ps err xj hstaging
      (decodeIterCost (expandBodyLen args)))
    (hrefuse : assemblyRefusalArm args mem next body st dst (expandPosCount args) goal
      pb xp tab pos0 (expandBodyLen args) ps err xj hstaging
      (decodeIterCost (expandBodyLen args)))
    (hseed : ∃ (s : State) (c j : Nat),
      j ≤ preScanFuel (expandPosCount args) + decodeIterCost (expandBodyLen args) ∧
      AssemblyLatchInv body st dst (expandPosCount args) goal pb xp tab pos0
        (expandBodyLen args) ps err xj mem (expandPosCount args) c s ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction
          (EntryState usDecFunction args mem next) =
        runFuel escapeCalls k usDecFunction s) :
    ExpandFacts args mem next :=
  expandFacts_of_arms
    { body := body, st := st, dst := dst, goal := goal, ps := ps, pos0 := pos0,
      pb := pb, xp := xp, tab := tab, err := err, xj := xj, staging := hstaging,
      loop := hloop, refuse := hrefuse, seedLatch := hseed }

/-- **The expander's record, from the three runs.**  The per-run hypothesis is
consumed at the record's own `pre`; `escape_expand_satisfies` then needs nothing
further, because the bundle it takes is built here. -/
theorem escape_expand_satisfies_of_arms
    (h : ∀ (args : List Value) (mem : Mem) (next : Nat),
      (Γ_escape_expand escapeExpandBudget).pre args mem next → ExpandArms args mem next) :
    Satisfies escapeCalls usDecFunction (Γ_escape_expand escapeExpandBudget) :=
  escape_expand_satisfies fun args mem next hpre => expandFacts_of_arms (h args mem next hpre)

/-! ### The emitter's state-level identification with `escapeAt`

Every emitter block step takes its branch value as a hypothesis (`hcond` in
`udIfEndI_step`, `udIfEnd9I_step`, `udIfThen26I_step`, …), and the invariant that
discharges them is `DecodeInv.walk`, whose `step_simple`/`step_six`/`step_pair`
need `escapeAt body q = some …`.  The arithmetic halves are proved — `hex4_hxCode`
and `surrogateTail_none_of_guard`/`_none_of_hex4_none`/`_none_of_lo_out`/
`_some_of_pair` (`JsonEscapeCompose`), `udIfEnd32Word_toNat`,
`udIfEnd3I_highSurrogate_iff`, `udIfThen26I_pairValue`
(`JsonEscapeEmitIdentities`) — but none of them mentions a state: they read the
block's `BitVec` forms.  The lemmas below are the state-level identification.  They
take the record's own table clause (`readBytes M tab 256 = some unescapeTable`) and
the body's byte after the escape position, read the block's `%9` cell out of the
table, and conclude `escapeAt`'s answer at that position.  `emitter_gate_is_escapeAt`
is the two-character escape's gate and its replacement byte;
`emitter_refusal_gate` is the refusal's gate against `IsControlB` and
`escapeAt = none`; the `\u` arm's two outcomes are `escapeAt_of_u_six` and
`escapeAt_of_u_pair`, which the hex and surrogate laws feed. -/

/-- `u` is not a two-character escape, so the table maps it to `0xFF`. -/
theorem simpleEscape_u : simpleEscape (0x75 : UInt8) = none := by decide

/-- A byte the table maps to a two-character escape is that escape at the walk. -/
theorem escapeAt_of_simple {body : List UInt8} {q : Nat} {c e : UInt8}
    (h1 : body[q + 1]? = some c) (hs : simpleEscape c = some e) :
    escapeAt body q = some ([e], 2) := by
  unfold escapeAt
  rw [h1]
  simp [hs]

/-- A byte the table maps nowhere, and which is not `u`, is no escape at the walk. -/
theorem escapeAt_of_none {body : List UInt8} {q : Nat} {c : UInt8}
    (h1 : body[q + 1]? = some c) (hs : simpleEscape c = none) (hc : c ≠ 0x75) :
    escapeAt body q = none := by
  unfold escapeAt
  rw [h1]
  simp [hs, hc]

/-- A `\u` whose four digits are hexadecimal and whose code unit is not the first
half of a pair is the six-byte form. -/
theorem escapeAt_of_u_six {body : List UInt8} {q cp : Nat} {c : UInt8}
    (h1 : body[q + 1]? = some c) (hc : c = 0x75)
    (h4 : hex4 body (q + 2) = some cp) (hst : surrogateTail body q cp = none) :
    escapeAt body q = some (utf8Encode cp, 6) := by
  unfold escapeAt
  rw [h1]
  simp [hc, simpleEscape_u, h4, hst]

/-- A `\u` whose code unit begins a surrogate pair is the pair's code point and
its twelve bytes. -/
theorem escapeAt_of_u_pair {body : List UInt8} {q cp cp' adv : Nat} {c : UInt8}
    (h1 : body[q + 1]? = some c) (hc : c = 0x75)
    (h4 : hex4 body (q + 2) = some cp)
    (hst : surrogateTail body q cp = some (cp', adv)) :
    escapeAt body q = some (utf8Encode cp', adv) := by
  unfold escapeAt
  rw [h1]
  simp [hc, simpleEscape_u, h4, hst]

/-- **The emitter's first gate is the walk's decision.**  From the record's table
clause and the body's byte after the escape position, the block's table read and
its signed gate are the table's answer at that byte, and the walk reads the same
two-character escape.  The `BitVec` value `t` is the block's `%9` cell; `e` is the
replacement byte `escapeAt` returns. -/
theorem emitter_gate_is_escapeAt {M : Mem} {tab : Nat} {body : List UInt8}
    {q : Nat} {c e : UInt8}
    (htab : readBytes M tab 256 = some unescapeTable)
    (h1 : body[q + 1]? = some c) (hs : simpleEscape c = some e) :
    ∃ t : BitVec 8,
      readBytes M (tab + c.toNat) 1 = some (natToBytes t.toNat 1) ∧
      t.toNat = e.toNat ∧
      evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1) ∧
      escapeAt body q = some ([e], 2) := by
  obtain ⟨t, htval, htread, htest⟩ := emitterTest_of_table (M := M) (tab := tab) c htab
  have hs' : simpleEscape c ≠ none := by rw [hs]; exact Option.some_ne_none e
  have hg : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1) := htest.2 hs'
  have hval : (UInt8.ofNat t.toNat) = (simpleEscape c).getD 0xFF := by
    have h := unescapeTable_getElem? c
    rw [h] at htval
    exact (Option.some.inj htval).symm
  have hte : t.toNat = e.toNat := by
    have h' := congrArg UInt8.toNat hval
    rw [hs] at h'
    simpa using h'
  exact ⟨t, htread, hte, hg, escapeAt_of_simple h1 hs⟩

/-- The refusal gate, unfolded: with the head position and its byte pinned, the
body's refusal test is `IsControlB` at the byte or `escapeAt`'s `none` at the
body-relative offset. -/
theorem decodeRefuses_eq_gate {body : List UInt8} {ps : List Nat} {pos0 c q : Nat}
    {b : UInt8} (hp : ps[c]? = some q) (hq : ¬ q < pos0)
    (hb : body[q - pos0]? = some b) :
    decodeRefuses body ps pos0 c =
      (IsControlB b || (escapeAt body (q - pos0)).isNone) := by
  unfold decodeRefuses
  rw [hp]
  simp [hq, hb]

/-- **The refusal's gate is `IsControlB` or `escapeAt = none`.** -/
theorem emitter_refusal_gate {body : List UInt8} {ps : List Nat} {pos0 c q : Nat}
    {b : UInt8} (hp : ps[c]? = some q) (hq : ¬ q < pos0)
    (hb : body[q - pos0]? = some b) :
    decodeRefuses body ps pos0 c = true ↔
      IsControlB b = true ∨ escapeAt body (q - pos0) = none := by
  rw [decodeRefuses_eq_gate hp hq hb, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by simpa using h)

/-- **The record's body and table reads at a state's own memory.**  The iteration's
blocks read the body and the escape table out of the state they start from; the
record promises both at the caller's memory, and the frame is what carries them to
a state that agrees outside the destination extent.  This is the transfer the
emitter bridge and the copy loops need at the latch; it is stated at `ExpandStaging`
because the arm statements that do not carry the staging cannot apply it. -/
theorem ExpandStaging.latch_reads
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (h : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    {s : State} (hframe : UnchangedOutside mem s.mem [(dst, n + 64)]) :
    readBytes s.mem b n = some body ∧ readBytes s.mem tab 256 = some unescapeTable := by
  obtain ⟨hpre, hargs, -, hbody, hpos0n, hrest⟩ := h
  obtain ⟨-, -, -, -, hspB, -⟩ := hrest
  obtain ⟨b', n', dst', err', xp', xj', nps', pos0', tab', body', ps', err0', k0',
    hargs', hbody', -, -, -, -, hwidth', -, -, -, htab, -, -, hspB', -, hspTab, -,
    -, -⟩ := hpre
  obtain ⟨hb', hdst', -, -, -, htab'⟩ := staging_ptr_slots hargs hargs'
  have hnlt : n < 2 ^ 64 := by omega
  have hn'lt : n' < 2 ^ 64 := by omega
  have hn' : n' = n := (staging_len_eq hargs hargs' hnlt hn'lt).symm
  rw [hb', hn'] at hbody'
  have hbody_eq : body' = body := Option.some.inj (hbody'.symm.trans hbody)
  rw [hbody_eq] at hbody'
  rw [hb', hdst', hn'] at hspB'
  rw [htab'] at htab
  rw [htab', hdst', hn'] at hspTab
  refine ⟨?_, ?_⟩
  · exact (readBytes_of_UnchangedOutside hframe (fun x hx1 hx2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rcases hspB with hle | hle
      · omega
      · omega)).trans hbody'
  · exact (readBytes_of_UnchangedOutside hframe (fun x hx1 hx2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rcases hspTab with hle | hle
      · omega
      · omega)).trans htab

/-! ### What the three fields still need

`loop`, `refuse` and `seedLatch` are the bundle's remaining content, and the
obstacle to each is the same composition rather than three separate ones.

**The iteration arm now carries the staging, which is what its proof reads.**
`assemblyLatchStep` takes `ExpandStaging` beside the invariant, because the arm
derives two reads from it and from nothing else: `while.body6` loads the position
`%add28` names out of the caller's list (`readBytes_positionsBytes`, at the entry
the staging's `ps` names and inside the window its range clause bounds), and
`if.end.i` loads the escape table's image of the body's byte
(`emitterTest_of_table`, at `tab + b.toNat`).  `ExpandStaging.latch_reads`
transfers the record's body and table reads across the latch's frame to the memory
the blocks read, so those two facts are available wherever the staging is in scope.
A step stated at `AssemblyLatchInv` alone can reach neither — that invariant
mentions `body` only inside `DecodeInv.walk`, and carries no read of the position
stream or the table — so the staging is part of the statement, not an extra
hypothesis beside it.  `.refuse` and `.seed` take the same staging, and the three
runs are now one shape.

**The chain is not composed.**  The run `loop` and the seed's latch arm need is
`cleanup32 → while.body6 → if.end →` (the copy at `while.body.i91`, or straight to
`us_run_long.exit99` when `if.end`'s test is zero) `→ us_run_long.exit99 →
if.then.i104 → us_run.exit → if.end21 → if.end.i`, and then the emitter's paths:
the simple escape returns to `cleanup32` from `if.then6.i`, and the `\u` arms
(`if.end9.i`, `if.end.i115`, `if.end3.i`, `if.then17.i`, `land.lhs.true22.i`,
`if.then26.i`) return through `if.end32.i`.  The block steps for every one of them
exist — `udWhileBody6_step_one`, `udIfEnd_step` and its zero arm,
`copyBodyLoop_run_at`, `udCopyTail_step`, `udCopyTailIf_step`, `udRunExit_step_one`,
`udIfEnd21_step`, `udIfEndI_step`, `udIfThen6I_step`, `udIfEnd9I_step`,
`udIfEndI115_step`, `udIfEnd3I_step`, `udIfThen17I_step`, `udLandLhsTrue22I_step`,
`udIfThen26I_step`, `udIfEnd32I_step`, with `udIfEnd32I_to_whileBody6` composing
that block and the latch's own step back into the next iteration's first block.
What is missing is the composition itself, and its work is named rather than left
to be discovered:

* a step lemma's witness state is opaque (`decodeLatch_step_enter`'s conclusion
  carries no defining equation for the state it returns), so each intermediate
  state has to be introduced by the composition itself — `let e := …` at the
  block's own environment builder — with the step read off it and its cell
  hypotheses discharged from the builder (`ud_lk`) or from the preceding state's
  cells;
* the arithmetic the blocks compute (`%add28`, `%add24`, `%sub13`, `%conv8`, and
  the encoder at `if.end32.i`) has to be tied to the preceding state's cells and
  the staging's `pos0 + n ≤ 2 ^ 32`;
* `if.end` branches on `%sub13 > 64`, so the copy is present or absent and the two
  arms must reach `us_run_long.exit99` with different fuel;
* each `\u` arm carries its own `DecodeInv` transfer — `step_simple`, `step_six`
  and `step_pair` are the laws, but the branch's `escapeAt` hypothesis has to be
  produced from `emitter_gate_is_escapeAt` and the two `\u` facts, at the byte
  offsets the copy left the cursor at, and the refusing byte takes `if.then22` out
  to `cleanup41`, which is `.refuse`'s branch.

`refuse` additionally needs the prefix from the latch through the same blocks to
`if.then20`/`if.then22`, then `udIfThen20_step`/`udIfThen22_step` and the exit word;
`seedLatch` needs the pre-scan's three blocks (`udEntry_step`, `udLandRhs_step`,
`udWhileBody_step`) composed to the latch, and shares the iteration's first step.
Neither is a statement defect: each quantifies over exactly the run the bound
names.  The fuel primitive for the chain is `runFuel_prefix_trans` /
`runFuel_prefix_some` in `Semantics`.

**A hole with no error is possible here, and a pin is the instrument.**  Elaborating
a candidate composition can succeed with a branch replaced by `sorry` while the
build reports only a warning, so no composition above may be trusted without
`#print axioms` at `[propext, Quot.sound]` or a named carrier.  That is why the
footprints below are pinned. -/

/-! ### Axiom footprints

The assembly adds no principle: `expandExit_satisfied` and `emptySeedRun` carry the
footprints the development already has, and building a structure on top of them
adds nothing.  The named carrier is `expandExit_satisfied`, whose `Classical.choice`
is the exit words' staging destructuring rather than this module's.  The bridge's
one `Classical.choice` is `evalICmp_sgt_negone_one_iff`'s (`JsonEscapeDecodeTrace`)
reading of an eight-bit word's `toInt`; `emitter_gate_is_escapeAt` is the only
lemma here that carries it, and the rest of the bridge stays at `[propext]`. -/

/-- info: 'LeanLLVM.Vellum.expandFacts_of_arms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expandFacts_of_arms

/-- info: 'LeanLLVM.Vellum.expandFacts_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expandFacts_of_runs

/-- info: 'LeanLLVM.Vellum.escape_expand_satisfies_of_arms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms escape_expand_satisfies_of_arms

/-- info: 'LeanLLVM.Vellum.simpleEscape_u' does not depend on any axioms -/
#guard_msgs in
#print axioms simpleEscape_u

/-- info: 'LeanLLVM.Vellum.escapeAt_of_simple' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeAt_of_simple

/-- info: 'LeanLLVM.Vellum.escapeAt_of_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeAt_of_none

/-- info: 'LeanLLVM.Vellum.escapeAt_of_u_six' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeAt_of_u_six

/-- info: 'LeanLLVM.Vellum.escapeAt_of_u_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeAt_of_u_pair

/-- info: 'LeanLLVM.Vellum.decodeRefuses_eq_gate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decodeRefuses_eq_gate

/-- info: 'LeanLLVM.Vellum.emitter_gate_is_escapeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitter_gate_is_escapeAt

/-- info: 'LeanLLVM.Vellum.emitter_refusal_gate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms emitter_refusal_gate

/-- info: 'LeanLLVM.Vellum.ExpandStaging.latch_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ExpandStaging.latch_reads

end LeanLLVM.Vellum
