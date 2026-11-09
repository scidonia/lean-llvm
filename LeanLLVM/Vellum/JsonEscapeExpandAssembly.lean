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
The fuel primitive for the chain is `runFuel_prefix_trans` /
`runFuel_prefix_some` in `Semantics`.

**The chain stops at the copy, and it stops on a statement, not on volume.**
Composing the first two blocks executes (`cleanup32` then `while.body6`, with the
step witnesses introduced as `let`-bound states and their cells discharged from
the environment builders, as the bullets above describe).  The third block's two
arms reach `us_run_long.exit99`; the copy arm is where the hypotheses no longer
assemble, and the reason is the invariant's, not the composition's.

`if.end` forms the copy's destination base as `%add.ptr12 = %dst + %j.0294`, whose
value is `dst + out.length`, and `CopyInv` asks for `copyDisjoint src dst sub` at
that base.  In the staging where the body follows the destination
(`dst + n + 64 ≤ b`), the only disjunct that can hold is
`(dst + out.length) + sub + 64 ≤ b + i`, and it needs `out.length ≤ i`.  Nothing
in `AssemblyLatchInv` states that.  `DecodeInv` carries three fields, and its
`walk` does not constrain the prefix at all when the goal is a refusal: a refusal
outcome drops `out`, so the invariant admits a latch with an arbitrarily long
prefix at any cursor — `escapeDecodeGo_refusal_ignores_prefix` below is that fact
on the pinned body, and `decodeInv_prefix_unbounded` is the existential it yields.
The only prefix bound in the tree is `DecodeInv.out_length_le_cursor`
(`JsonEscapeFinalCopy`), and it is stated at `k = nps` — the exit — which the
iteration's `c < nps` cannot supply.  So the copy's `copyDisjoint`, the emitter's
store extent (`dst + %add15`, needed for the returned state's frame), and the
destination prefix all wait on one clause the invariant does not have:
`out.length ≤ i` at the latch.  That is a statement change, and it reaches
`LatchInv`/`DecodeLatch` in `JsonEscapeDecodeRun`, so it is put to the planner
rather than patched here.  `copyDisjoint_prefix_unbounded` is the arithmetic
witness at the parameters a `n = 200` staging with `q - pos0 = 100` gives, and
`assemblyLatchInv_admits_failing_copy` below is the state: a latch the invariant
admits at `c = 1 < nps = 4`, whose guard is false, at which the copy's
disjointness is false.  The state's walk refuses at `150`, which is why the prefix
is unconstrained there; a conjunct bounding the prefix is therefore needed
unconditionally, not only in the decoded case.

Note that the two claims above about `refuse` and `seedLatch` being volume only
were written before this was executed, and the paragraph `refuse` needs — the
shared prefix — passes through the same copy when the refusing position is past a
long run, so it inherits the same missing clause.

**A hole with no error is possible here, and a pin is the instrument.**  Elaborating
a candidate composition can succeed with a branch replaced by `sorry` while the
build reports only a warning, so no composition above may be trusted without
`#print axioms` at `[propext, Quot.sound]` or a named carrier.  That is why the
footprints below are pinned. -/

/-! ### The copy's obstruction, executed

Two facts, each stated at the strength the argument uses and no further.  The
first is the reason `DecodeInv.walk` cannot bound the prefix: at a refusal the
outcome is produced without reading `out`.  The second is the arithmetic at the
copy's parameters, so the inequality `copyDisjoint` asks for is refuted on numbers
rather than argued in prose. -/

/-- **A refusing walk does not read the prefix.**  The byte at position `2` of this
body is a control byte, so the walk refuses there and returns the same outcome for
every `out` — `DecodeInv.walk` therefore holds of a state carrying any prefix
whatever, at the same cursor and index. -/
theorem escapeDecodeGo_refusal_ignores_prefix (out : List UInt8) :
    escapeDecodeGo [0x41, 0x42, 0x01] 0 1 [2] out = .refused 2 2 := by
  have hb : ([0x41, 0x42, 0x01] : List UInt8)[2]? = some 0x01 := by decide
  have hlt : 2 < ([0x41, 0x42, 0x01] : List UInt8).length := by decide
  have hctl : IsControlB (0x01 : UInt8) = true := by decide
  exact escapeDecodeGo_step_control hb hlt hctl

/-- The existential form: the walk at one cursor and index admits a prefix longer
than that cursor, so no field of `DecodeInv` bounds it. -/
theorem decodeInv_prefix_unbounded :
    ∃ (out : List UInt8),
      escapeDecodeGo [0x41, 0x42, 0x01] 0 1 [2] out = .refused 2 2 ∧ 0 < out.length :=
  ⟨List.replicate 50 0x20, escapeDecodeGo_refusal_ignores_prefix _, by simp⟩

/-- **The copy's disjointness is not free.**  At the copy the destination base is
`dst + out.length`; here `dst = 100`, `out.length = 264` (the `n + 64` extent a
`n = 200` staging names), the residual is `100` and the source base is `364`
(`b = dst + n + 64` with `i = 0`).  Neither disjunct of `copyDisjoint` holds. -/
theorem copyDisjoint_prefix_unbounded :
    ¬ copyDisjoint 364 364 100 := by
  unfold copyDisjoint
  decide

/-! ### The refusal-parameter witness

A latch state the iteration arm's hypotheses admit, at which the copy's
`copyDisjoint` is false.  The body is `\n`, a run of `a`, `\n`, a run of `a`, then
a backslash followed by a control byte and a run of `a`: its escape positions are
`[0, 100, 150, 151]`.  The caller's walk is fresh, so the goal is a refusal at
`150`, and a refusal does not read the prefix — `walk` is therefore satisfied by a
prefix of `264` bytes, the whole destination extent.

At the latch `c = 1` the head position is the valid escape at `100`, so
`decodeRefuses` is false and this is a state the iteration arm quantifies over.
`if.end` then forms `sub13 = 100 - 2 = 98` (above one block, so the copy runs) with
source base `b + i = 466` and destination base `dst + out.length = 464`, where
neither disjunct of `copyDisjoint` holds. -/

/-- The body: `\n`, `a`^98, `\n`, `a`^48, `\` then a control byte, `a`^48.  Length
`200`; positions `[0, 100, 150, 151]`. -/
def refusalBody : List UInt8 :=
  [0x5C, 0x6E] ++ List.replicate 98 0x61 ++ [0x5C, 0x6E] ++ List.replicate 48 0x61 ++
    [0x5C, 0x01] ++ List.replicate 48 0x61

theorem refusalBody_length : refusalBody.length = 200 := by decide

/-- The position stream the staging reads. -/
def refusalStream : List UInt8 := positionsBytes 4 [0, 100, 150, 151]

theorem refusalStream_length : refusalStream.length = 16 := by
  unfold refusalStream
  rw [positionsBytes_length]
  decide

/-- The witness memory: zeros, the table at `1000`, the stream at `700`, the body
at `464`. -/
def refusalMem : Mem :=
  writeBytes (writeBytes (writeBytes (zeroMem 1500) 1000 unescapeTable) 700 refusalStream)
    464 refusalBody

theorem refusalMem_dst : readBytes refusalMem 200 264 = some (List.replicate 264 0) := by
  unfold refusalMem
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 200 + 264 ≤ 464)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 200 + 264 ≤ 700)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 200 + 264 ≤ 1000)]
  exact readBytes_zeroMem 264 1500 200 (by omega)

theorem refusalMem_body : readBytes refusalMem 464 200 = some refusalBody := by
  unfold refusalMem
  rw [show 200 = refusalBody.length from refusalBody_length.symm]
  exact readBytes_writeBytes_same _ _ (addr := 464)

theorem refusalMem_stream : readBytes refusalMem 700 16 = some (positionsBytes 4 [0, 100, 150, 151]) := by
  unfold refusalMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalBody_length]; omega)]
  rw [show 16 = refusalStream.length from refusalStream_length.symm]
  exact readBytes_writeBytes_same _ _ (addr := 700)

theorem refusalMem_table : readBytes refusalMem 1000 256 = some unescapeTable := by
  unfold refusalMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalBody_length]; omega)]
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalStream_length]; omega)]
  rw [show 256 = unescapeTable.length from unescapeTable_length.symm]
  exact readBytes_writeBytes_same _ _ (addr := 1000)

theorem refusalMem_tail : readBytes refusalMem 664 32 = some (List.replicate 32 0) := by
  unfold refusalMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalBody_length]; omega)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 664 + 32 ≤ 700)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 664 + 32 ≤ 1000)]
  exact readBytes_zeroMem 32 1500 664 (by omega)

theorem refusalMem_err : readBytes refusalMem 900 8 = some (wordBytes 8 0) := by
  unfold refusalMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalBody_length]; omega)]
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalStream_length]; omega)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 900 + 8 ≤ 1000)]
  rw [readBytes_zeroMem 8 1500 900 (by omega), wordBytes_rep_eight]

theorem refusalMem_xj : readBytes refusalMem 950 8 = some (wordBytes 8 0) := by
  unfold refusalMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalBody_length]; omega)]
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _
    (by rw [refusalStream_length]; omega)]
  rw [readBytes_writeBytes_below _ _ _ _ _ (by omega : 950 + 8 ≤ 1000)]
  rw [readBytes_zeroMem 8 1500 950 (by omega), wordBytes_rep_eight]

theorem refusalBody_positions :
    escapePositionsFrom refusalBody ⟨true, false⟩ = [0, 100, 150, 151] := by decide

theorem refusalBody_escAt : escAt refusalBody ⟨true, false⟩ 0 = [0, 100, 150, 151] := by
  rw [← escapePositionsFrom_eq_escAt]
  exact refusalBody_positions

theorem refusalBody_escapeAt_100 : escapeAt refusalBody 100 = some ([0x0A], 2) := by decide

theorem refusalBody_escapeAt_150 : escapeAt refusalBody 150 = none := by decide

/-- The caller's fresh walk refuses at `150`. -/
theorem refusalGoal : escapeDecodeGo refusalBody 0 0 [0, 100, 150, 151] [] = .refused 150 3 := by
  decide

/-- The walk from the latch's cursor refuses at the same place for every prefix. -/
theorem refusalWalk (out : List UInt8) :
    escapeDecodeGo refusalBody 2 1 [100, 150, 151] out = .refused 150 3 := by
  have h1 : escapeDecodeGo refusalBody 2 1 [100, 150, 151] out =
      escapeDecodeGo refusalBody 102 2 [150, 151]
        (out ++ (refusalBody.drop 2).take 98 ++ [0x0A]) := by
    refine escapeDecodeGo_step_simple (i := 2) (q := 100) (k := 1) (qs := [150, 151])
      (out := out) (b := 0x5C) (e := 0x0A) ?_ ?_ ?_ refusalBody_escapeAt_100
    · decide
    · decide
    · decide
  rw [h1]
  refine escapeDecodeGo_step_refuse (i := 102) (q := 150) (k := 2) (qs := [151])
    (out := out ++ (refusalBody.drop 2).take 98 ++ [0x0A]) (b := 0x5C) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact refusalBody_escapeAt_150

/-- The latch's cells. -/
def refusalState : State :=
  modelState
    [("%sub", .int 64 0), ("%inc11", .int 64 1), ("%nxp", .int 64 4),
     ("%add8.i", .int 64 264), ("%p", .ptr 464), ("%dst", .ptr 200),
     ("%xp", .ptr 700), ("%tab", .ptr 1000), ("%err", .ptr 900),
     ("%xj", .ptr 950), ("%pos0", .int 64 (BitVec.ofNat 64 0)),
     ("%n", .int 64 (BitVec.ofNat 64 200)),
     ("%add", .int 64 (BitVec.ofNat 64 200))]
    refusalMem "cleanup32" (some "if.then6.i")

theorem refusalState_cursor : latchCursor refusalState = some 2 := by
  simp [latchCursor, refusalState, modelState]

/-- The staging the iteration arm takes. -/
theorem refusalState_staging :
    ExpandStaging [.ptr 464, .int 64 (BitVec.ofNat 64 200), .ptr 200, .ptr 900,
      .ptr 700, .ptr 950, .int 64 (BitVec.ofNat 64 4), .int 64 0, .ptr 1000]
      refusalMem 0 refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 464 700 1000 0 200
      [0, 100, 150, 151] 900 950 := by
  unfold ExpandStaging Γ_escape_expand_at
  refine ⟨?_, rfl, rfl, refusalMem_body, by omega, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · refine ⟨464, 200, 200, 900, 700, 950, 4, 0, 1000, refusalBody, [0, 100, 150, 151],
      0, 0, rfl, refusalMem_body, refusalMem_stream, rfl, ?_, ?_, by omega, refusalMem_xj, by omega,
      refusalMem_err, refusalMem_table, ⟨_, refusalMem_tail⟩, ⟨_, refusalMem_dst⟩, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> omega
    · rw [refusalBody_positions]
      rfl
  · refine ⟨BitVec.ofNat 64 200, refusalMem_stream, rfl, ?_, by decide⟩
    intro j q hq
    rcases Nat.lt_or_ge j 4 with hj | hj
    · have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> simp at hq <;> omega
    · have hnone : ([0, 100, 150, 151] : List Nat)[j]? = none :=
        List.getElem?_eq_none_iff.2 (by simpa using hj)
      rw [hnone] at hq
      cases hq
  · rw [refusalBody_positions]
    rfl
  · unfold DecodeNoAlias
    refine ⟨by omega, by omega, by omega, by omega⟩
  · refine ⟨0, refusalMem_xj, by omega, ?_⟩
    show EscapeOutcome.refused 150 3 =
      escapeDecodeGo refusalBody 0 0 (List.map (fun q => q - 0) [0, 100, 150, 151]) []
    simp only [List.map_cons, List.map_nil, Nat.sub_zero]
    exact refusalGoal.symm

/-- The invariant at the witness state. -/
theorem refusalState_inv :
    AssemblyLatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 464 700 1000 0 200
      [0, 100, 150, 151] 900 950 refusalMem 3 1 refusalState := by
  obtain ⟨addv0, hprop⟩ := refusalState_staging.2.2.2.2.2.1
  have haddv0 : addv0 = BitVec.ofNat 64 200 := by
    apply BitVec.toNat_inj.mp
    rw [hprop.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  have hinv : DecodeInv refusalBody ⟨true, false⟩ refusalMem 200 4 2 1
      (List.replicate 264 0) (.refused 150 3) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [refusalBody_escAt]
      exact refusalWalk _
    · rw [show (List.replicate 264 0 : List UInt8).length = 264 from by simp]
      exact refusalMem_dst
    · rw [refusalBody_escAt]
      rfl
  have hjn : (264 : BitVec 64).toNat = (List.replicate 264 0 : List UInt8).length := by
    simp
  have hcellAdd8 : lookupName refusalState.env "%add8.i" = some (.int 64 264) := by
    simp [refusalState, modelState, lookupName]
  have hncell : lookupName refusalState.env "%n" = some (.int 64 (BitVec.ofNat 64 200)) := by
    simp [refusalState, modelState, lookupName]
  have hphi : ("if.then6.i" = "if.end32.i" ∧
        lookupName refusalState.env "%add.i125" = some (.int 64 264) ∧
        lookupName refusalState.env "%adv.1.i" = some (.int 64 (BitVec.ofInt 64 2))) ∨
      ("if.then6.i" = "if.then6.i" ∧
        lookupName refusalState.env "%add8.i" = some (.int 64 264) ∧
        (BitVec.ofInt 64 2) = BitVec.ofInt 64 2) :=
    Or.inr (And.intro rfl (And.intro hcellAdd8 rfl))
  have hlatch : LatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 3 refusalState 1 := by
    refine ⟨?_, by omega⟩
    refine ⟨2, List.replicate 264 0, "if.then6.i", 0, 1, BitVec.ofInt 64 2, 264, 4,
      464, 700, 1000, 900, 950, BitVec.ofNat 64 0, BitVec.ofNat 64 200,
      BitVec.ofNat 64 200, rfl, hinv, by decide, rfl, rfl, rfl, rfl, by decide,
      hphi, by decide, by decide, hjn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hncell⟩

  have haddcell : lookupName refusalState.env "%add" = some (.int 64 addv0) := by
    rw [haddv0]; simp [refusalState, modelState, lookupName]
  have hex : ∃ addv : BitVec 64,
      DecodeStaging refusalState.mem 4 700 0 200 [0, 100, 150, 151] addv ∧
        lookupName refusalState.env "%add" = some (.int 64 addv) :=
    Exists.intro addv0 (And.intro hprop haddcell)
  have hstaged : StagedLatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 700 0 200
      [0, 100, 150, 151] 3 1 refusalState :=
    And.intro hlatch hex
  refine ⟨hstaged, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · simp [refusalState, modelState, lookupName]
  · intro i hi
    rw [refusalState_cursor] at hi
    injection hi with h
    omega
  · intro a h
    rfl

/-- **The copy's disjointness fails at an invariant state.**  The parameters are
`if.end`'s at this latch: source base `%p + %i.0295 = 464 + 2`, destination base
`%dst + %j.0294 = 200 + 264`, residual `%sub - %i.0295 = 100 - 2`. -/
theorem refusalState_copyDisjoint_false : ¬ copyDisjoint (464 + 2) (200 + 264) 98 := by
  unfold copyDisjoint
  decide

/-- The iteration arm's guard is false at the witness: `1 < 4` and the head
position `100` is a valid escape. -/
theorem refusalState_guard :
    (decide (4 ≤ 1) || decodeRefuses refusalBody [0, 100, 150, 151] 0 1) = false := by
  decide

/-- **The iteration arm's hypotheses hold at a state whose copy cannot run.**  The
state satisfies `AssemblyLatchInv` at budget `3` with `c = 1 < nps = 4`; the arm's
guard is false; and at `if.end`'s copy parameters the disjointness `CopyInv` asks
for is false.  So the copy's hypothesis cannot be discharged from the invariant,
and the clause it needs is the prefix bound `out.length ≤ i`. -/
theorem assemblyLatchInv_admits_failing_copy :
    AssemblyLatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 464 700 1000 0 200
        [0, 100, 150, 151] 900 950 refusalMem 3 1 refusalState ∧
      (decide (4 ≤ 1) || decodeRefuses refusalBody [0, 100, 150, 151] 0 1) = false ∧
      ¬ copyDisjoint (464 + 2) (200 + 264) 98 :=
  ⟨refusalState_inv, refusalState_guard, refusalState_copyDisjoint_false⟩

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

/-- info: 'LeanLLVM.Vellum.escapeDecodeGo_refusal_ignores_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecodeGo_refusal_ignores_prefix

/-- info: 'LeanLLVM.Vellum.decodeInv_prefix_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeInv_prefix_unbounded

/-- info: 'LeanLLVM.Vellum.copyDisjoint_prefix_unbounded' does not depend on any axioms -/
#guard_msgs in
#print axioms copyDisjoint_prefix_unbounded


/-! #### The witness's footprints

A `decide` over the body's bytes and the block steps' own lemmas introduce nothing:
the whole witness is at the module's ceiling, `[propext, Classical.choice,
Quot.sound]`, with `Classical.choice` reaching only the propositions `decide`
evaluates over `EscapeOutcome` and `ClassState` (`refusalState_staging`,
`refusalState_inv`, `assemblyLatchInv_admits_failing_copy`). -/

/-- info: 'LeanLLVM.Vellum.refusalBody' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalBody

/-- info: 'LeanLLVM.Vellum.refusalBody_length' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalBody_length

/-- info: 'LeanLLVM.Vellum.refusalStream' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalStream

/-- info: 'LeanLLVM.Vellum.refusalStream_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalStream_length

/-- info: 'LeanLLVM.Vellum.refusalMem' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalMem

/-- info: 'LeanLLVM.Vellum.refusalMem_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_dst

/-- info: 'LeanLLVM.Vellum.refusalMem_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_body

/-- info: 'LeanLLVM.Vellum.refusalMem_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_stream

/-- info: 'LeanLLVM.Vellum.refusalMem_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_table

/-- info: 'LeanLLVM.Vellum.refusalMem_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_tail

/-- info: 'LeanLLVM.Vellum.refusalMem_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_err

/-- info: 'LeanLLVM.Vellum.refusalMem_xj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalMem_xj

/-- info: 'LeanLLVM.Vellum.refusalBody_positions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalBody_positions

/-- info: 'LeanLLVM.Vellum.refusalBody_escAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalBody_escAt

/-- info: 'LeanLLVM.Vellum.refusalBody_escapeAt_100' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalBody_escapeAt_100

/-- info: 'LeanLLVM.Vellum.refusalBody_escapeAt_150' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalBody_escapeAt_150

/-- info: 'LeanLLVM.Vellum.refusalGoal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalGoal

/-- info: 'LeanLLVM.Vellum.refusalWalk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalWalk

/-- info: 'LeanLLVM.Vellum.refusalState' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalState

/-- info: 'LeanLLVM.Vellum.refusalState_cursor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalState_cursor

/-- info: 'LeanLLVM.Vellum.refusalState_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refusalState_staging

/-- info: 'LeanLLVM.Vellum.refusalState_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refusalState_inv

/-- info: 'LeanLLVM.Vellum.refusalState_copyDisjoint_false' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalState_copyDisjoint_false

/-- info: 'LeanLLVM.Vellum.refusalState_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalState_guard

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_admits_failing_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchInv_admits_failing_copy
end LeanLLVM.Vellum
