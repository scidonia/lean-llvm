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
import LeanLLVM.Vellum.JsonEscapeEmitIdentities

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

/-! ### A surrogate pair's second position

`DecodeInv.step_pair` advances the position cursor by two — the second `\u` is a
position of its own — and returns the walk at `k + 2` without asking the list for
that second entry.  The successor latch's `c ≤ nps` therefore cannot come from the
law; it comes from the encoding.  The pair's first half puts the second `\u`'s
backslash at `q + 6`, that backslash is a lane (`lane_pair_sixth`: its own run
parity is even, because the four digits between the two escapes reset it, and the
string state is unchanged), and nothing between the first escape and it is a
position (`no_lane_twelve`).  So the cursor list read from `q + 1` heads at
`q + 6` (`escAt_cons`), and the list at the caller's cursor carries a second entry.
-/

/-- **The pair's successor cursor is inside the list.**  The cursor advanced past a
surrogate pair is at most the list's length: the pair supplies one further position
at `q + 6`, and the list read at the caller's cursor has that entry behind its own
head. -/
theorem escAt_pair_succ_le {body : List UInt8} {st : ClassState} {c q cp cp' : Nat}
    (hlist : (escAt body st 0)[c]? = some q)
    (hb : body[q]? = some 0x5C) (h1 : body[q + 1]? = some 0x75)
    (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = some (cp', 12)) :
    c + 2 ≤ (escAt body st 0).length := by
  have hlt : c < (escAt body st 0).length := by
    rcases Nat.lt_or_ge c (escAt body st 0).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hlist
      exact absurd hlist (by simp)
  -- the cursor list at `c` is the head and its tail
  have hget : (escAt body st 0)[c]'hlt = q := by
    have h' := hlist
    rw [List.getElem?_eq_getElem hlt] at h'
    exact Option.some.inj h'
  have hhead : (escAt body st 0).drop c = q :: (escAt body st 0).drop (c + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  -- the tail is the cursor list at the next lane, because a drop is one
  obtain ⟨i', hi'⟩ := escAt_drop_exists body st 0 c
  have hcons : escAt body st i' = q :: (escAt body st 0).drop (c + 1) := by
    rw [← hi']
    exact hhead
  have htail : (escAt body st 0).drop (c + 1) = escAt body st (q + 1) :=
    escAt_tail hcons
  -- the head is a run-starting backslash, so the pair's sixth byte is a lane
  have hq : laneAt body st q = true := escAt_head_lane hcons
  have hnb : IsControlB (0x5C : UInt8) = false := by decide
  obtain ⟨-, -, hins⟩ := lane_backslash_of hb hq hnb
  obtain ⟨h6c, -, -, -⟩ := surrogateTail_bytes ht
  have hsix : laneAt body st (q + 6) = true := lane_pair_sixth hb hins h1 hx h6c
  have hpair : escAt body st (q + 1) = (q + 6) :: escAt body st (q + 12) :=
    escAt_cons (by omega) (by omega) hsix (no_lane_twelve h1 hx ht)
  have hlen : 2 ≤ ((escAt body st 0).drop c).length := by
    rw [hhead, htail, hpair]
    simp
  rw [List.length_drop] at hlen
  omega

/-- **The pair's successor cursor is inside the caller's count**, at the list's
length as the staging names it. -/
theorem escAt_pair_succ_le_nps {body : List UInt8} {st : ClassState} {c q cp cp' nps : Nat}
    (hlen : (escAt body st 0).length = nps)
    (hlist : (escAt body st 0)[c]? = some q)
    (hb : body[q]? = some 0x5C) (h1 : body[q + 1]? = some 0x75)
    (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = some (cp', 12)) :
    c + 2 ≤ nps := by
  have h := escAt_pair_succ_le hlist hb h1 hx ht
  omega

/-! ### The emitter's three walk transfers

Each escape form advances the walk by one relation, and `DecodeInv.step_simple`,
`step_six` and `step_pair` (`JsonEscapeExpandContract`) state it.  The iteration arm
needs the *invariant* at the new cursor rather than the outcome equation alone, and
the three laws do not give it: `DecodeInv` also carries the store and the cursor
bound.  The transfers below are one shape at three states — the walk field is the
law read backwards, the store field is the emitter's write (a hypothesis, because the
write belongs to the block and this lemma is not the block), and the cursor bound is
the encoding being no longer than the bytes the escape consumed.

The cursor's monotonicity (`i ≤ q`) is a hypothesis rather than a consequence: the
walk's list is spaced, but spacing is a property of the staging this lemma does not
carry, and the arm supplies it where the list's range is in scope. -/

/-- **The two-character transfer.**  The cursor advances two bytes, the index one,
and the prefix gains the bytes copied plus the escape's own byte. -/
theorem DecodeInv.step_simple_inv {body : List UInt8} {st : ClassState} {M M' : Mem}
    {dst nps i k n : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat}
    {b c1 e : UInt8}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some c1) (hs : simpleEscape c1 = some e)
    (hqi : i ≤ q) (hq2 : q + 2 ≤ n)
    (hstored : readBytes M' dst
      (out ++ (body.drop i).take (q - i) ++ [e]).length =
        some (out ++ (body.drop i).take (q - i) ++ [e])) :
    DecodeInv body st M' dst nps (q + 2) (k + 1)
      (out ++ (body.drop i).take (q - i) ++ [e]) goal := by
  refine ⟨(hinv.step_simple hhead hb hlt hctl h1 hs).symm, hstored, hinv.length, ?_⟩
  rw [List.length_append, List.length_append, List.length_singleton]
  have htake : ((body.drop i).take (q - i)).length ≤ q - i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have hpre := hinv.prefix_le_cursor
  omega

/-- **The six-byte transfer.**  A `\u` whose code unit stands alone advances the
cursor six bytes and the index one; the prefix gains the copied bytes and the
unit's encoding. -/
theorem DecodeInv.step_six_inv {body : List UInt8} {st : ClassState} {M M' : Mem}
    {dst nps i k n : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat}
    {b c1 : UInt8} {cp : Nat}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = none)
    (hqi : i ≤ q) (hq6 : q + 6 ≤ n)
    (hstored : readBytes M' dst
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp).length =
        some (out ++ (body.drop i).take (q - i) ++ utf8Encode cp)) :
    DecodeInv body st M' dst nps (q + 6) (k + 1)
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp) goal := by
  refine ⟨(hinv.step_six hhead hb hlt hctl h1 hx ht).symm, hstored, hinv.length, ?_⟩
  rw [List.length_append, List.length_append]
  have htake : ((body.drop i).take (q - i)).length ≤ q - i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have henc := utf8Encode_length_le_four cp
  have hpre := hinv.prefix_le_cursor
  omega

/-- **The surrogate-pair transfer.**  The pair advances the cursor twelve bytes and
the index by two — the second `\u` is a position of its own — and appends the pair's
code point. -/
theorem DecodeInv.step_pair_inv {body : List UInt8} {st : ClassState} {M M' : Mem}
    {dst nps i k n : Nat} {out : List UInt8} {goal : EscapeOutcome} {q : Nat}
    {b c1 : UInt8} {cp cp' : Nat}
    (hinv : DecodeInv body st M dst nps i k out goal)
    (hhead : (escAt body st 0).drop k = q :: (escAt body st 0).drop (k + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = some (cp', 12))
    (hqi : i ≤ q) (hq12 : q + 12 ≤ n)
    (hstored : readBytes M' dst
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp').length =
        some (out ++ (body.drop i).take (q - i) ++ utf8Encode cp')) :
    DecodeInv body st M' dst nps (q + 12) (k + 2)
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp') goal := by
  refine ⟨(hinv.step_pair hhead hb hlt hctl h1 hx ht).symm, hstored, hinv.length, ?_⟩
  rw [List.length_append, List.length_append]
  have htake : ((body.drop i).take (q - i)).length ≤ q - i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have henc := utf8Encode_length_le_four cp'
  have hpre := hinv.prefix_le_cursor
  omega

/-! ### Axiom footprints: the emitter's three transfers

The transfers consume `DecodeInv.step_*` and the encoding's length bound, and add
no principle: each is an invariant constructor over a law already pinned at the
development's ceiling. -/

/-- info: 'LeanLLVM.Vellum.DecodeInv.step_simple_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_simple_inv

/-- info: 'LeanLLVM.Vellum.DecodeInv.step_six_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_six_inv

/-- info: 'LeanLLVM.Vellum.DecodeInv.step_pair_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.step_pair_inv

/-- info: 'LeanLLVM.Vellum.escAt_pair_succ_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escAt_pair_succ_le

/-- info: 'LeanLLVM.Vellum.escAt_pair_succ_le_nps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escAt_pair_succ_le_nps

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

**The chain stopped at the copy, and it stopped on a statement, not on volume.**
Composing the first two blocks executes (`cleanup32` then `while.body6`, with the
step witnesses introduced as `let`-bound states and their cells discharged from
the environment builders, as the bullets above describe).  The third block's two
arms reach `us_run_long.exit99`; the copy arm is where the hypotheses did not
assemble, and the reason was the invariant's, not the composition's.  The
statement that was missing is now the invariant's, so the copy's hypothesis is
discharged from the state rather than from the composition:

`if.end` forms the copy's destination base as `%add.ptr12 = %dst + %j.0294`, whose
value is `dst + out.length`, and `CopyInv` asks for `copyDisjoint src dst sub` at
that base.  In the staging where the body follows the destination
(`dst + n + 64 ≤ b`), the only disjunct that can hold is
`(dst + out.length) + sub + 64 ≤ b + i`, and it needs `out.length ≤ i`.  That bound
is `DecodeInv.prefix_le_cursor`: the walk's own relation, carried by the invariant
and therefore available to every consumer of it — the copy, the emitter's store
extent (`dst + %add15`, needed for the returned state's frame) and the destination
prefix alike.  With the latch's cursor bound (`%sub + %adv` inside the body,
`AssemblyLatchInv`'s `latchCursor` clause) it reads as the capacity form
`out.length + (n - i) ≤ n`, which is `DecodeInv.capacity`.

The clause is unconditional, and the reason is executed below.  `escapeDecodeGo`
returns the same refused outcome for every `out` at a refusing position, so
`DecodeInv.walk` alone holds at a latch with an arbitrarily long prefix at any
cursor — `escapeDecodeGo_refusal_ignores_prefix` is that fact on the pinned body,
and `decodeInv_prefix_unbounded` is the existential it yields.  A bound stated only
for the decoded case would leave exactly the refusing state unconstrained, and a
refusal is the *walk's* outcome, not the iteration's exit: the state can still be
the one the copy runs at.  `copyDisjoint_prefix_unbounded` is the arithmetic at the
parameters a `n = 200` staging with `q - pos0 = 100` gives, and the
refusal-parameter witness below is a state that satisfied the invariant at exactly
those parameters before the clause; it is now outside the invariant, and
`assemblyLatchInv_excludes_failing_copy` is that exclusion.

Note that the two claims above about `refuse` and `seedLatch` being volume only
were written before this was executed, and the paragraph `refuse` needs — the
shared prefix — passes through the same copy when the refusing position is past a
long run, so it reads the same clause.

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
whatever, at the same cursor and index.  That is what the record's
`prefix_le_cursor` is for: the walk cannot exclude such a state, so the invariant
states the bound itself. -/
theorem escapeDecodeGo_refusal_ignores_prefix (out : List UInt8) :
    escapeDecodeGo [0x41, 0x42, 0x01] 0 1 [2] out = .refused 2 2 := by
  have hb : ([0x41, 0x42, 0x01] : List UInt8)[2]? = some 0x01 := by decide
  have hlt : 2 < ([0x41, 0x42, 0x01] : List UInt8).length := by decide
  have hctl : IsControlB (0x01 : UInt8) = true := by decide
  exact escapeDecodeGo_step_control hb hlt hctl

/-- The existential form: the walk at one cursor and index admits a prefix longer
than that cursor, so `walk` alone bounds nothing.  The bound is the record's
`prefix_le_cursor`, which is why that clause is a field of `DecodeInv` and not a
theorem about the walk. -/
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

A latch state at which the copy's `copyDisjoint` is false, and which the prefix
bound excludes.  The body is `\n`, a run of `a`, `\n`, a run of `a`, then a
backslash followed by a control byte and a run of `a`: its escape positions are
`[0, 100, 150, 151]`.  The caller's walk is fresh, so the goal is a refusal at
`150`, and a refusal does not read the prefix — `walk` is satisfied by a prefix of
`264` bytes, the whole destination extent, which is exactly why `walk` alone does
not bound it.

At the latch `c = 1` the head position is the valid escape at `100`, so
`decodeRefuses` is false and this is a state the iteration arm quantifies over.
`if.end` then forms `sub13 = 100 - 2 = 98` (above one block, so the copy runs) with
source base `b + i = 466` and destination base `dst + out.length = 464`, where
neither disjunct of `copyDisjoint` holds.

This is the state the invariant admitted before `prefix_le_cursor`; the exclusion
below is the clause's own test.  The staging, the guard and the copy parameters are
kept, because they are what makes the exclusion a statement about this state rather
than about an arbitrary one. -/

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

/-- **The witness state is not a walk state.**  The store holds a prefix of the
whole destination extent — `264` bytes — while the cursor sits at byte two, the
end of the body's first escape, so `prefix_le_cursor` is false there. -/
theorem refusalState_not_decodeInv :
    ¬ DecodeInv refusalBody ⟨true, false⟩ refusalMem 200 4 2 1
        (List.replicate 264 0) (.refused 150 3) := by
  intro h
  have hpre := h.prefix_le_cursor
  rw [show (List.replicate 264 0 : List UInt8).length = 264 from by simp] at hpre
  omega

/-- **The witness state is not a latch state.**  A `DecodeLatch` pins the cursor at
`%sub + %adv = 2` and the prefix's length at `%add8.i = 264`, so every `DecodeInv`
its existential names fails `prefix_le_cursor`, and the state is outside `LatchInv`
whatever budget its second conjunct names. -/
theorem refusalState_not_latchInv :
    ¬ LatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 3 refusalState 1 := by
  intro h
  obtain ⟨i, out, prev, sub, inc11, adv, j, nxp, paddr, xpaddr, tabaddr, err,
    xjaddr, pos0v, addv, nv, hpc, hwalk, hcle, hpre, hsub, hinc11, hnxp, hnps,
    hphi, hnext, hi, hjlen, hpcell, hdstcell, hxpcell, htabcell, herrcell,
    hxjcell, hpos0cell, haddcall, hncell⟩ := h.1
  have hsub0 : sub = 0 := by
    have h1 : lookupName refusalState.env "%sub" = some (.int 64 (0 : BitVec 64)) := by
      simp [refusalState, modelState, lookupName]
    rw [h1] at hsub
    have h2 := Option.some.inj hsub
    cases h2
    rfl
  have hadv : adv = BitVec.ofInt 64 2 := by
    rcases hphi with ⟨_, ha, _⟩ | ⟨_, _, ha⟩
    · simp [refusalState, modelState, lookupName] at ha
    · exact ha
  have hi2 : i = 2 := by
    rw [← hi, hadv, hsub0]
    decide
  have hj264 : j = 264 := by
    rcases hphi with ⟨_, hj, _⟩ | ⟨_, hj, _⟩
    · simp [refusalState, modelState, lookupName] at hj
    · have hcell : lookupName refusalState.env "%add8.i" =
          some (.int 64 (264 : BitVec 64)) := by
        simp [refusalState, modelState, lookupName]
      rw [hcell] at hj
      have h2 := Option.some.inj hj
      cases h2
      rfl
  have hlen264 : out.length = 264 := by
    rw [← hjlen, hj264]
    decide
  have hbound := hwalk.prefix_le_cursor
  omega

/-- **The witness state is outside the assembly's latch invariant**, which carries
the walk's bound through `LatchInv`/`DecodeLatch`. -/
theorem refusalState_not_assemblyLatchInv :
    ¬ AssemblyLatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 464 700 1000 0 200
        [0, 100, 150, 151] 900 950 refusalMem 3 1 refusalState :=
  fun h => refusalState_not_latchInv (assemblyLatchInv_latch h)

/-- **The copy's disjointness fails at the witness's parameters.**  They are
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

/-- **The state that forced the clause is excluded by it.**  `AssemblyLatchInv` no
longer holds at the witness, while its guard and its copy parameters are unchanged:
the iteration arm's guard is false there, and at `if.end`'s copy parameters the
disjointness `CopyInv` asks for is false.  The exclusion is the repair's own test —
a state good enough to break the old statement is the state the new one must
exclude. -/
theorem assemblyLatchInv_excludes_failing_copy :
    ¬ AssemblyLatchInv refusalBody ⟨true, false⟩ 200 4 (.refused 150 3) 464 700 1000 0 200
        [0, 100, 150, 151] 900 950 refusalMem 3 1 refusalState ∧
      (decide (4 ≤ 1) || decodeRefuses refusalBody [0, 100, 150, 151] 0 1) = false ∧
      ¬ copyDisjoint (464 + 2) (200 + 264) 98 :=
  ⟨refusalState_not_assemblyLatchInv, refusalState_guard, refusalState_copyDisjoint_false⟩

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
evaluates over `EscapeOutcome` and `ClassState` (`refusalState_staging`). -/

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

/-- info: 'LeanLLVM.Vellum.refusalState_not_decodeInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalState_not_decodeInv

/-- info: 'LeanLLVM.Vellum.refusalState_not_latchInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refusalState_not_latchInv

/-- info: 'LeanLLVM.Vellum.refusalState_not_assemblyLatchInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refusalState_not_assemblyLatchInv

/-- info: 'LeanLLVM.Vellum.refusalState_copyDisjoint_false' does not depend on any axioms -/
#guard_msgs in
#print axioms refusalState_copyDisjoint_false

/-- info: 'LeanLLVM.Vellum.refusalState_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refusalState_guard

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_excludes_failing_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchInv_excludes_failing_copy

/-- **The latch's first two blocks, composed.**  From the latch at a live guard —
the index is below the list's length and the head position does not refuse —
`cleanup32` and `while.body6` run in two control steps and leave the state at
`if.end` with the block's own cells: the next index `%k.1296 = %inc11 + %adv == 12`,
the byte cursor `%i.0295 = %adv + %sub`, the prefix length `%j.0294`, and the
position read `%conv8`, whose value is the list entry at the index.  The staging is
what makes the read a value rather than a hypothesis, and the spacing clause is what
puts the cursor at or behind that entry's body-relative position `q`.

**The hypothesis is the index's liveness, not the loop's exit test.**  Both blocks
read only `¬ nps ≤ c`: `cleanup32`'s `%cmp4` is the liveness test, and `while.body6`
loads the position at the index.  The exit test's second disjunct — the head does
not refuse — is no premise of either step, so the theorem takes `¬ nps ≤ c` and the
two-arm consumers both supply it: the iteration's the loop's `= false` arm, the
refusal's its `¬ nps ≤ c`.  A compound hypothesis would have made the refusal arm
uninstantiable while saying nothing more about these blocks.

**The list's length is exported beside it.**  The successor latch's `DecodeLatch`
names `%nxp` and its own `Nat` value, so the bound `nxp.toNat = nps` is stated here
where the cell is read rather than re-derived by each consumer.

**The index's `Nat` reading is exported.**  `%k.1296` names the next index as a
`BitVec`, and the successor it equals is `decodeNextIdx inc11 adv`, whose `Nat`
reading `= c` is the walk's own cursor relation.  The refusal exit's index clause is
`goal = .refused off.toNat k.toNat` at a state that carries this cell as its
`%inc11`, so its consumer has to relate the two numbers rather than the words; the
conjunct is `DecodeLatch`'s, carried here once instead of re-derived per consumer. -/
theorem latch_to_ifEnd
    {args : List Value} {mem : Mem} {next : Nat}
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b xp tab : Nat} {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    {r c : Nat} {s : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem (r + 1) c s)
    (hnle : ¬ nps ≤ c) :
    ∃ (e : State) (i q : Nat) (out : List UInt8) (sub adv inc11 nxp jv : BitVec 64)
      (v : BitVec 32) (addv : BitVec 64),
      e.pc = "if.end" ∧ e.pre = some "while.body6" ∧ e.mem = s.mem ∧
      (escAt body st 0)[c]? = some q ∧ i ≤ q ∧ (adv + sub).toNat = i ∧
      lookupName e.env "%k.1296" = some (.int 64 (decodeNextIdx inc11 adv)) ∧
      lookupName e.env "%i.0295" = some (.int 64 (adv + sub)) ∧
      lookupName e.env "%j.0294" = some (.int 64 jv) ∧
      lookupName e.env "%conv8" = some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
      v.toNat = pos0 + q ∧
      lookupName e.env "%sub" = some (.int 64 sub) ∧
      lookupName e.env "%inc11" = some (.int 64 inc11) ∧
      lookupName e.env "%nxp" = some (.int 64 nxp) ∧
      lookupName e.env "%p" = some (.ptr b) ∧
      lookupName e.env "%dst" = some (.ptr dst) ∧
      lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%xp" = some (.ptr xp) ∧
      lookupName e.env "%tab" = some (.ptr tab) ∧
      lookupName e.env "%err" = some (.ptr err) ∧
      lookupName e.env "%xj" = some (.ptr xj) ∧
      lookupName e.env "%add" = some (.int 64 addv) ∧ addv.toNat = pos0 + n ∧
      jv.toNat = out.length ∧
      readBytes e.mem dst out.length = some out ∧
      out.length ≤ i ∧
      DecodeInv body st e.mem dst nps i c out goal ∧
      nxp.toNat = nps ∧
      (decodeNextIdx inc11 adv).toNat = c ∧
      ∀ k, runFuel escapeCalls (2 + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e := by
  -- the invariant, at the latch
  have hkeep := h
  obtain ⟨hstaged, hp_b, hxp_b, htab_b, hpos0_b, hn_b, herr_b, hxj_b, hcur, hspaced,
    hframe⟩ := hkeep
  obtain ⟨hlatch, ⟨addv, hds, haddcell⟩⟩ := hstaged
  obtain ⟨hdec, hbudget⟩ := hlatch
  obtain ⟨i, out, prev, sub, inc11, adv, jv, nxp, paddr, xpaddr, tabaddr, erraddr,
    xjaddr, pos0v, addv', nv, hpc, hwalk, hcle, hpre, hsubc, hinc11c, hnxpc, hnxpnat,
    hphi, hnext, hi, hjlen, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell,
    hpos0cell, haddcall, hncell⟩ := hdec
  -- the hypothesis says the index is live
  have hclt : c < nps := by omega
  -- the staging's facts at the caller's binders
  obtain ⟨hstream, hpslen, hrange, haddnat⟩ := hds
  obtain ⟨-, -, -, hbody0, h32, -, hmap, -, -, -, -⟩ := hstaging
  have hinlen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbody0
  have hnpsn : nps ≤ n := by
    have hlen := hwalk.length
    have hle := escAt_length_le body st 0
    omega
  -- the pinnings force the latch's existentials
  have hxpaddr : xpaddr = xp := by
    rw [hxp_b] at hxpcell
    exact (Value.ptr.inj (Option.some.inj hxpcell)).symm
  have htabaddr : tabaddr = tab := by
    rw [htab_b] at htabcell
    exact (Value.ptr.inj (Option.some.inj htabcell)).symm
  have herraddr : erraddr = err := by
    rw [herr_b] at herrcell
    exact (Value.ptr.inj (Option.some.inj herrcell)).symm
  have hxjaddr : xjaddr = xj := by
    rw [hxj_b] at hxjcell
    exact (Value.ptr.inj (Option.some.inj hxjcell)).symm
  -- the stream's entry at `c` is the load `while.body6` makes
  have hlenps : nps = ps.length := hpslen.symm
  have hcps : c < ps.length := by omega
  have hread := readBytes_positionsBytes hstream hlenps hcps
  have hqbound := hrange c (ps[c]'hcps) (List.getElem?_eq_getElem hcps)
  have hq32 : ps[c]'hcps < 2 ^ 32 := by omega
  let v : BitVec 32 := BitVec.ofNat 32 (ps[c]'hcps)
  have hvnat : v.toNat = ps[c]'hcps := by
    show (BitVec.ofNat 32 (ps[c]'hcps)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hload : readBytes s.mem (xp + 4 * c) 4 = some (natToBytes v.toNat 4) := by
    rw [hvnat]
    exact hread
  -- the head position, body-relative
  have hhead : (escAt body st 0)[c]? = some (ps[c]'hcps - pos0) := by
    rw [← escapePositionsFrom_eq_escAt, ← hmap, List.getElem?_map,
      List.getElem?_eq_getElem hcps]
    rfl
  have hcurval : latchCursor s = some (adv + sub).toNat := by
    rcases hphi with ⟨hprev, _, ha⟩ | ⟨hprev, _, hadv⟩
    · simp only [latchCursor, hpre, hprev, hsubc, ha]
    · rw [hadv]
      simp only [latchCursor, hpre, hprev, hsubc]
  have hile : (adv + sub).toNat ≤ ps[c]'hcps - pos0 :=
    assemblyLatchInv_cursor_le_head h hcurval hhead
  have hkval : (decodeNextIdx inc11 adv).toNat = c := hnext
  have hk63 : (decodeNextIdx inc11 adv).toNat < 2 ^ 63 := by omega
  have hcond : evalICmp .ugt addv (BitVec.ofNat 64 v.toNat) = (1 : BitVec 1) := by
    refine (evalICmp_ugt_one_iff_toNat _ _).2 ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hvnat, haddnat]
    omega
  -- the two steps
  let e1 : State :=
    { (withEnv (udCleanup32Env s.env jv adv sub inc11 nxp) s) with
        pc := "while.body6", pre := some "cleanup32" }
  have hstep1 : step escapeCalls usDecFunction s = .jump e1 := by
    rcases hphi with ⟨hprev, hj, ha⟩ | ⟨hprev, hj, hadv⟩
    · subst hprev
      have h1 := udCleanup32_step s.env s "if.end32.i" (.reg "%add.i125")
        (.reg "%adv.1.i") jv adv sub inc11 nxp hpc hpre
        latch_phi_operand_emitter latch_phi_operand_emitter_adv
        (evalOperand_reg_eq s.env s "%add.i125" (.int 64 jv) hj)
        (by
          rw [evalOperand_reg_eq (("%j.3", .int 64 jv) :: s.env) s "%adv.1.i"
            (.int 64 adv) (by rw [lookupName_cons_ne _ _ (by decide)]; exact ha)])
        hsubc hinc11c hnxpc (by
          refine (evalICmp_ult_one_iff _ _).2 ?_
          change (decodeNextIdx inc11 adv).toNat < nxp.toNat
          rw [hnext, hnxpnat]
          exact hclt)
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    · subst hprev
      have h1 := udCleanup32_step s.env s "if.then6.i" (.reg "%add8.i")
        (.imm (.int 64 (BitVec.ofInt 64 2))) jv adv sub inc11 nxp hpc hpre
        latch_phi_operand_simple latch_phi_operand_simple_adv
        (evalOperand_reg_eq s.env s "%add8.i" (.int 64 jv) hj)
        (by rw [hadv]; rfl)
        hsubc hinc11c hnxpc (by
          refine (evalICmp_ult_one_iff _ _).2 ?_
          change (decodeNextIdx inc11 adv).toNat < nxp.toNat
          rw [hnext, hnxpnat]
          exact hclt)
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
  let e2 : State :=
    { (withEnv (udWhileBody6Env (udCleanup32Env s.env jv adv sub inc11 nxp) xp
        (decodeNextIdx inc11 adv) (adv + sub) jv v addv) s) with
        pc := "if.end", pre := some "while.body6" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udWhileBody6_step_one (udCleanup32Env s.env jv adv sub inc11 nxp)
      { s with pc := "while.body6", pre := some "cleanup32" }
      "cleanup32" (.reg "%add28") (.reg "%add24") (.reg "%j.3") xp
      (decodeNextIdx inc11 adv) (adv + sub) jv v addv
      rfl rfl
      (by decide)
      (by
        exact evalOperand_reg_eq (udCleanup32Env s.env jv adv sub inc11 nxp) s
          "%add28" (.int 64 (decodeNextIdx inc11 adv)) (by
            show lookupName (udCleanup32Env s.env jv adv sub inc11 nxp) "%add28" =
              some (.int 64 (decodeNextIdx inc11 adv))
            simp only [decodeNextIdx, decodePairBit, udCleanup32Env]; ud_lk))
      (by decide)
      (by
        exact evalOperand_reg_eq (udCleanup32Env s.env jv adv sub inc11 nxp) s
          "%add24" (.int 64 (adv + sub)) (by
            simp only [udCleanup32Env]; ud_lk))
      (by decide)
      (by
        exact evalOperand_reg_eq (udCleanup32Env s.env jv adv sub inc11 nxp) s
          "%j.3" (.int 64 jv) (by
            simp only [udCleanup32Env]; ud_lk))
      (by simp only [withEnv, udCleanup32Env]; ud_lk_h hxp_b)
      (by simp only [withEnv, udCleanup32Env]; ud_lk_h haddcell)
      hk63 (signExtend_self_toNat (decodeNextIdx inc11 adv))
      (by
        show readBytes s.mem (xp + (decodeNextIdx inc11 adv).toNat * 4) 4 = _
        rw [hkval, Nat.mul_comm]
        exact hload)
      hcond
    exact h1
  refine ⟨e2, i, ps[c]'hcps - pos0, out, sub, adv, inc11, nxp, jv, v, addv, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact hhead
  · exact hi ▸ hile
  · exact hi
  · simp only [e2, withEnv, udWhileBody6Env]; ud_lk
  · simp only [e2, withEnv, udWhileBody6Env]; ud_lk
  · simp only [e2, withEnv, udWhileBody6Env]; ud_lk
  · simp only [e2, withEnv, udWhileBody6Env]; ud_lk
  · rw [hvnat]
    omega
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hsubc
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hinc11c
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hnxpc
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hp_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hdstcell
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hpos0_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hn_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hxp_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h htab_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h herr_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h hxj_b
  · simp only [e2, withEnv, udWhileBody6Env, udCleanup32Env]; ud_lk_h haddcell
  · exact haddnat
  · exact hjlen
  · rw [show e2.mem = s.mem from rfl]; exact hwalk.stored
  · exact hwalk.prefix_le_cursor
  · rw [show e2.mem = s.mem from rfl]; exact hwalk
  · exact hnxpnat
  · exact hkval
  · intro k
    rw [show 2 + k = (1 + k) + 1 from by omega, udRun_jump hstep1]
    rw [show 1 + k = k + 1 from by omega, udRun_jump hstep2]

/-! ### The wrap state: a cursor past the head position

`if.end` forms `%sub13 = %sub - %i.0295` in 64-bit arithmetic, with `%sub` the
head position (`%conv8 - %pos0`) and `%i.0295` the walk's byte cursor.  At a cursor
past the head the subtraction wraps to `2 ^ 64 - 1`, so the copy that follows is
given a residual no bound inside `decodeIterCost` can exhaust; every other clause
of the latch invariant holds at such a state, because the walk is defined at any
cursor (`escapeDecodeGo` copies `take (q - i)`, empty for `q < i`) and
`DecodeInv.prefix_le_cursor` bounds only the decoded prefix by the cursor.

The state below is that state, on a six-byte body with one position: at
`cleanup32`, `%sub = 3` and `%adv.1.i = 2` put the cursor at `5` while the head
position is `4`.  `AssemblyLatchInvUnspaced` is the invariant before the spacing
clause, and `wrapState_unspaced` shows the state satisfied all of it, so the
exclusion below is a statement about a state that was admitted rather than about an
arbitrary one.  The arithmetic facts beside it are what the copy then cannot meet:
the block's residual is `2 ^ 64 - 1`, no `Nat` residual below `2 ^ 63` is that
word, and `copyDisjoint` fails at it. -/

/-- The latch invariant before the spacing clause: `AssemblyLatchInv`'s conjuncts
up to the cursor-behind-head relation.  Kept so the state that forced the clause is
a checkable statement rather than a paragraph. -/
def AssemblyLatchInvUnspaced (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (r c : Nat) (s : State) : Prop :=
  StagedLatchInv body st dst nps goal xp pos0 n ps r c s ∧
  lookupName s.env "%p" = some (.ptr b) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%tab" = some (.ptr tab) ∧
  lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName s.env "%err" = some (.ptr err) ∧
  lookupName s.env "%xj" = some (.ptr xj) ∧
  (∀ i : Nat, latchCursor s = some i → i ≤ n) ∧
  UnchangedOutside mem s.mem [(dst, n + 64)]

/-- The body: four `a`, then `\ n`.  Its own position list is `[4]`. -/
def wrapBody : List UInt8 := [0x61, 0x61, 0x61, 0x61, 0x5C, 0x6E]

theorem wrapBody_positions : escAt wrapBody ⟨true, false⟩ 0 = [4] := by decide

/-- The witness memory: zeros, the table at `1000`, the stream at `700`, the body
at `464`. -/
def wrapMem : Mem :=
  writeBytes
    (writeBytes (writeBytes (zeroMem 1600) 1000 unescapeTable)
      700 (positionsBytes 4 [4]))
    464 wrapBody

theorem wrapMem_body : readBytes wrapMem 464 6 = some wrapBody := by
  unfold wrapMem
  exact readBytes_writeBytes_same _ _

theorem wrapMem_stream : readBytes wrapMem 700 4 = some (positionsBytes 4 [4]) := by
  unfold wrapMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _ (by decide)]
  exact readBytes_writeBytes_same _ _

theorem wrapMem_table : readBytes wrapMem 1000 256 = some unescapeTable := by
  unfold wrapMem
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _ (by decide)]
  rw [JsonEntrySteps.readBytes_writeBytes_above _ _ _ _ _ (by decide)]
  rw [show 256 = unescapeTable.length from unescapeTable_length.symm]
  exact readBytes_writeBytes_same _ _

/-- The latch's cells: `%sub = 3`, `%adv.1.i = 2`, so the cursor is `5`. -/
def wrapState : State :=
  modelState
    [("%sub", .int 64 3), ("%inc11", .int 64 0), ("%nxp", .int 64 1),
     ("%add.i125", .int 64 0), ("%adv.1.i", .int 64 2), ("%p", .ptr 464),
     ("%dst", .ptr 200), ("%xp", .ptr 700), ("%tab", .ptr 1000),
     ("%err", .ptr 900), ("%xj", .ptr 950), ("%pos0", .int 64 0),
     ("%add", .int 64 6), ("%n", .int 64 6)]
    wrapMem "cleanup32" (some "if.end32.i")

theorem wrapState_cursor : latchCursor wrapState = some 5 := by
  decide

theorem wrapState_walk : escapeDecodeGo wrapBody 5 0 [4] [] = .decoded [0x0A] 1 := by
  decide

theorem wrapState_decodeInv :
    DecodeInv wrapBody ⟨true, false⟩ wrapMem 200 1 5 0 [] (.decoded [0x0A] 1) where
  walk := wrapState_walk
  stored := rfl
  length := by rw [wrapBody_positions]; rfl
  prefix_le_cursor := by decide

theorem wrapState_staging :
    DecodeStaging wrapMem 1 700 0 6 [4] (6 : BitVec 64) := by
  refine ⟨wrapMem_stream, rfl, ?_, by decide⟩
  intro j q hq
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq
      omega
  | succ k =>
      simp only [List.getElem?_cons_succ] at hq
      cases hq

/-- **The state satisfied the invariant before the spacing clause.**  The walk at
cursor `5` on the one-position list is the decode of the empty remainder, the
stored prefix is empty, the staging reads, the cells hold, the cursor is inside the
body, and the frame is the identity. -/
theorem wrapState_unspaced :
    AssemblyLatchInvUnspaced wrapBody ⟨true, false⟩ 200 1 (.decoded [0x0A] 1) 464 700
      1000 0 6 [4] 900 950 wrapMem 1 0 wrapState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ⟨6, wrapState_staging, ?_⟩⟩
    · refine ⟨?_, by omega⟩
      refine ⟨5, [], "if.end32.i", 3, 0, 2, 0, 1, 464, 700, 1000, 900, 950, 0, 6, 6,
        rfl, wrapState_decodeInv, by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · decide
      · left
        exact ⟨rfl, by simp [wrapState, modelState, lookupName],
          by simp [wrapState, modelState, lookupName]⟩
      · decide
      · simp [wrapState, modelState, lookupName]
      · rfl
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
      · simp [wrapState, modelState, lookupName]
    · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · simp [wrapState, modelState, lookupName]
  · intro i hi
    rw [wrapState_cursor] at hi
    have h : i = 5 := (Option.some.inj hi).symm
    subst h
    omega
  · intro a _
    rfl

/-- **The cursor is past the head position.**  The invariant's cursor is `5`; the
walk's one position is `4`. -/
theorem wrapState_cursor_past_head :
    latchCursor wrapState = some 5 ∧ (escAt wrapBody ⟨true, false⟩ 0)[0]? = some 4 :=
  ⟨wrapState_cursor, by rw [wrapBody_positions]; rfl⟩

/-- **The state is outside the invariant that carries the spacing.**  `Spaced`'s
head premise is `i ≤ q`, and here `5 ≤ 4` is false. -/
theorem wrapState_not_assemblyLatchInv :
    ¬ AssemblyLatchInv wrapBody ⟨true, false⟩ 200 1 (.decoded [0x0A] 1) 464 700 1000
        0 6 [4] 900 950 wrapMem 1 0 wrapState := by
  intro h
  have hsp := assemblyLatchInv_spaced h 5 wrapState_cursor
  simp only [List.drop_zero, wrapBody_positions] at hsp
  have := Spaced.head_le hsp
  omega

/-- **The copy's residual cannot be the block's cell.**  `if.end` forms
`%sub13 = %sub - %i.0295` in 64-bit arithmetic; here that is `4 - 5 = 2 ^ 64 - 1`.
`CopyInv`'s residual is a `Nat` carried as `BitVec.ofNat 64 sub` with `sub < 2 ^ 63`,
and no such `sub` is that word. -/
theorem wrapState_copy_residual_wraps :
    ∀ sub : Nat, sub < 2 ^ 63 → BitVec.ofNat 64 sub ≠ (4 : BitVec 64) - (5 : BitVec 64) := by
  intro sub hlt h
  have h1 : (BitVec.ofNat 64 sub).toNat = ((4 : BitVec 64) - (5 : BitVec 64)).toNat := by
    rw [h]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sub < 2 ^ 64)] at h1
  have h2 : ((4 : BitVec 64) - (5 : BitVec 64)).toNat = 2 ^ 64 - 1 := by decide
  rw [h2] at h1
  omega

/-- **The copy's disjointness fails at the wrapped residual.**  At the parameters
`if.end` would form — source base `%p + %i.0295 = 464 + 5`, destination base
`%dst + %j.0294 = 200`, residual `2 ^ 64 - 1` — neither disjunct holds. -/
theorem wrapState_disjoint_false :
    ¬ copyDisjoint (464 + 5) (200 + 0) (2 ^ 64 - 1) := by
  unfold copyDisjoint
  decide

/-- **The iteration arm's guard is false at the wrap state**: the index is below
the list's length and the head position is a valid escape. -/
theorem wrapState_guard :
    (decide (1 ≤ 0) || decodeRefuses wrapBody [4] 0 0) = false := by
  decide

/-- **The state the spacing clause excludes.**  It satisfied the invariant's other
conjuncts, its guard is false — so the iteration arm quantifies over it — and the
copy's residual at its parameters is `2 ^ 64 - 1`, which is not a `Nat` residual
below the sign-extension bound. -/
theorem assemblyLatchInv_excludes_wrap_state :
    AssemblyLatchInvUnspaced wrapBody ⟨true, false⟩ 200 1 (.decoded [0x0A] 1) 464 700
        1000 0 6 [4] 900 950 wrapMem 1 0 wrapState ∧
      latchCursor wrapState = some 5 ∧
      (escAt wrapBody ⟨true, false⟩ 0)[0]? = some 4 ∧
      (decide (1 ≤ 0) || decodeRefuses wrapBody [4] 0 0) = false ∧
      ¬ AssemblyLatchInv wrapBody ⟨true, false⟩ 200 1 (.decoded [0x0A] 1) 464 700
        1000 0 6 [4] 900 950 wrapMem 1 0 wrapState ∧
      ¬ copyDisjoint (464 + 5) (200 + 0) (2 ^ 64 - 1) :=
  ⟨wrapState_unspaced, wrapState_cursor_past_head.1, wrapState_cursor_past_head.2,
    wrapState_guard, wrapState_not_assemblyLatchInv, wrapState_disjoint_false⟩

/-! #### The wrap state's footprints -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchInvUnspaced' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchInvUnspaced

/-- info: 'LeanLLVM.Vellum.wrapBody' does not depend on any axioms -/
#guard_msgs in
#print axioms wrapBody

/-- info: 'LeanLLVM.Vellum.wrapBody_positions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapBody_positions

/-- info: 'LeanLLVM.Vellum.wrapMem' does not depend on any axioms -/
#guard_msgs in
#print axioms wrapMem

/-- info: 'LeanLLVM.Vellum.wrapMem_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrapMem_body

/-- info: 'LeanLLVM.Vellum.wrapMem_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrapMem_stream

/-- info: 'LeanLLVM.Vellum.wrapMem_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrapMem_table

/-- info: 'LeanLLVM.Vellum.wrapState' does not depend on any axioms -/
#guard_msgs in
#print axioms wrapState

/-- info: 'LeanLLVM.Vellum.wrapState_cursor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapState_cursor

/-- info: 'LeanLLVM.Vellum.wrapState_walk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapState_walk

/-- info: 'LeanLLVM.Vellum.wrapState_decodeInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapState_decodeInv

/-- info: 'LeanLLVM.Vellum.wrapState_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrapState_staging

/-- info: 'LeanLLVM.Vellum.wrapState_unspaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrapState_unspaced

/-- info: 'LeanLLVM.Vellum.wrapState_cursor_past_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapState_cursor_past_head

/-- info: 'LeanLLVM.Vellum.wrapState_not_assemblyLatchInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrapState_not_assemblyLatchInv

/-- info: 'LeanLLVM.Vellum.wrapState_copy_residual_wraps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrapState_copy_residual_wraps

/-- info: 'LeanLLVM.Vellum.wrapState_disjoint_false' does not depend on any axioms -/
#guard_msgs in
#print axioms wrapState_disjoint_false

/-- info: 'LeanLLVM.Vellum.wrapState_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wrapState_guard

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_excludes_wrap_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchInv_excludes_wrap_state

/-- info: 'LeanLLVM.Vellum.latch_to_ifEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms latch_to_ifEnd
/-! ### The iteration's middle: the copy's exit, and the two facts it does not carry

`if.end`'s two arms and the copy after a position compose as far as the copy's exit
state — the copy's invariant is built from the state's own cells
(`ifEnd_copyArm`'s substance, below in `ifEnd_sub13`/`source_read_slice`/`take_take_source`)
— and the tail and the escape emitter's blocks then read cells the copy's own exit
word does not name.

**The cells the emitter reads, and the frame that carries them.**  `copyBodyPrefixLoop`'s
`ExitWord` names the counters it writes (`%add.ptr`, `%add.ptr12`, `%sub13` and the two
copy counters) and the copy's destination and prefix reads beside them, but the blocks
after it read cells the copy only passes over: `us_run.exit` loads the body at
`%p + %sub` and forms `%add15 = %sub13 + %j.0294`, `if.end.i` reads `%tab`, and the
refusal stores at `%err` and `%xj`.  The exit environment is opaque, so a cell the word
does not name cannot be recovered at the exit; the loop therefore takes the caller's
register frame as a parameter (`Cells` beside its persistence lemma), and the frame is
`CellFrame` — the nine cells the tail, the emitter and the refusal read — with
`CellFrame.copyBodyEnv` and the two tail lemmas as the persistence facts, one per
environment builder.  Both `if.end` arms take the same frame and hand it back at their
exit, so the middle's chain carries it without naming each cell at each block.

**And `us_run.exit` reads two different values out of the register pair its step fact
identifies.**  `%add15 = %sub13 + %j.0294` takes the residual and
`%arrayidx16 = %p + %sub` takes the head position; at the iteration's exit those are
`q - i` and `q`, which are equal only at cursor zero.  `udRunExit_denote`,
`udRunExit_step` and `udRunExit_step_one` (`JsonEscapeDecodeTrace`) bind both `%sub13`
and `%sub` to one `subv`, so they state the block only where the cursor is zero.
`udRunExit_stepS_zero` below is the block's step at both values, with the two
hypotheses kept apart, which is the form every iteration but the first needs.

The arithmetic and the source reads the middle needs are proved here: the residual
`if.end` forms as `%conv8 - %pos0 - %i.0295` at `q - i` (`ifEnd_sub13`), the source
range's sub-range at an offset (`source_read_slice`), the copy's byte list cut at its
residual (`take_take_source`), and the per-byte read of a range that reads back
(`readBytes_one_getD`).
-/

/-! ### The middle's arithmetic and its reads -/

theorem natToBytes_one_eq (b : UInt8) : natToBytes b.toNat 1 = [b] := by
  simp [natToBytes]

/-! ### The transfers attached to their compositions

The three laws above take the store field as a hypothesis.  The blocks are what
supply it: the simple escape's one-byte store and the `\u` arm's four-byte word
store, each written *after* the prefix the copy put at `%dst`.  The lemmas here are
the attachments — the block's write read back as the prefix extended by the
escape's bytes — together with the head equation and the two cursor bounds the laws
ask for.

The prefix is `out ++ (body.drop i).take (q - i)`: the walk's decoded prefix and
the bytes the copy moved from the body up to the head position.  A caller supplies
it as `hcover`, which is what the copy arms' `readBytes` conjunct is.
-/

/-- **The cursor list's head, as the drop equation the laws read.**  A position at
index `c` splits the list there. -/
theorem escAt_head_drop {body : List UInt8} {st : ClassState} {c q : Nat}
    (hlist : (escAt body st 0)[c]? = some q) :
    (escAt body st 0).drop c = q :: (escAt body st 0).drop (c + 1) := by
  have hlt : c < (escAt body st 0).length := by
    rcases Nat.lt_or_ge c (escAt body st 0).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hlist
      exact absurd hlist (by simp)
  have hget : (escAt body st 0)[c]'hlt = q := by
    have h' := hlist
    rw [List.getElem?_eq_getElem hlt] at h'
    exact Option.some.inj h'
  rw [List.drop_eq_getElem_cons hlt, hget]

/-- **A one-byte store extends the prefix the caller already holds.** -/
theorem readBytes_writeBytes_one_extend {m : Mem} {dst k : Nat} {out : List UInt8}
    {b : UInt8} (hout : readBytes m dst k = some out) :
    readBytes (writeBytes m (dst + k) [b]) dst (k + 1) = some (out ++ [b]) := by
  have hbelow : readBytes (writeBytes m (dst + k) [b]) dst k = some out := by
    rw [readBytes_writeBytes_below m [b] k dst (dst + k) (by omega)]
    exact hout
  have hsame := readBytes_writeBytes_same m [b] (addr := dst + k)
  have hsplit := JsonEntrySteps.readBytes_append (m := writeBytes m (dst + k) [b])
    k dst out 1 [b] hbelow hsame
  simpa using hsplit

/-- **The two-character arm's successor invariant.**  `if.then6.i` writes the
replacement byte at `%dst + %add15` — the prefix's own end — and the walk continues
two bytes on with the index advanced by one. -/
theorem DecodeInv.simple_succ {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i c n : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {q : Nat} {b c1 e t : UInt8}
    (hinv : DecodeInv body st M dst nps i c out goal)
    (hhead : (escAt body st 0).drop c = q :: (escAt body st 0).drop (c + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some c1) (hs : simpleEscape c1 = some e)
    (hiq : i ≤ q) (hq2 : q + 2 ≤ n)
    (hcover : readBytes M dst (out ++ (body.drop i).take (q - i)).length =
      some (out ++ (body.drop i).take (q - i)))
    (ht : t = e) :
    DecodeInv body st
      (writeBytes M (dst + (out ++ (body.drop i).take (q - i)).length)
        (natToBytes t.toNat 1)) dst nps (q + 2) (c + 1)
      (out ++ (body.drop i).take (q - i) ++ [e]) goal := by
  have hbyte : natToBytes t.toNat 1 = [e] := by rw [natToBytes_one_eq, ht]
  refine DecodeInv.step_simple_inv hinv hhead hb hlt hctl h1 hs hiq hq2 ?_
  have hlen : (out ++ (body.drop i).take (q - i) ++ [e]).length =
      (out ++ (body.drop i).take (q - i)).length + 1 := by
    rw [List.length_append]
    rfl
  rw [hbyte, hlen]
  exact readBytes_writeBytes_one_extend (b := e) hcover

/-- **The six-byte `\u` arm's successor invariant.**  `if.end32.i` writes the unit's
own UTF-8 encoding as one four-byte word at `%dst + %add15`, so the store field is
the block's `udIfEnd32I_decode` read; the index advances by one. -/
theorem DecodeInv.six_succ {body : List UInt8} {st : ClassState} {M M' : Mem}
    {dst nps i c n : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {q cp : Nat} {b : UInt8}
    (hinv : DecodeInv body st M dst nps i c out goal)
    (hhead : (escAt body st 0).drop c = q :: (escAt body st 0).drop (c + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = none)
    (hiq : i ≤ q) (hq6 : q + 6 ≤ n)
    (hstore : readBytes M' dst
      ((out ++ (body.drop i).take (q - i)).length + (utf8Encode cp).length) =
        some ((out ++ (body.drop i).take (q - i)) ++ utf8Encode cp)) :
    DecodeInv body st M' dst nps (q + 6) (c + 1)
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp) goal := by
  have hstored : readBytes M' dst
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp).length =
        some (out ++ (body.drop i).take (q - i) ++ utf8Encode cp) := by
    rw [List.length_append]
    exact hstore
  exact DecodeInv.step_six_inv (c1 := 0x75) hinv hhead hb hlt hctl h1 hx ht hiq hq6
    hstored

/-- **The pair arm's successor invariant.**  The pair's code point is one word too,
and the index advances by two: the second `\u` is a position of its own.  The cursor
bound `c + 2 ≤ nps` is *not* the law's: `escAt_pair_succ_le` derives it from the
encoding, and the caller supplies it as `hcle`. -/
theorem DecodeInv.pair_succ {body : List UInt8} {st : ClassState} {M M' : Mem}
    {dst nps i c n : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {q cp cp' : Nat} {b : UInt8}
    (hinv : DecodeInv body st M dst nps i c out goal)
    (hhead : (escAt body st 0).drop c = q :: (escAt body st 0).drop (c + 1))
    (hb : body[q]? = some b) (hlt : q < body.length)
    (hctl : IsControlB b = false)
    (h1 : body[q + 1]? = some 0x75) (hx : hex4 body (q + 2) = some cp)
    (ht : surrogateTail body q cp = some (cp', 12))
    (hiq : i ≤ q) (hq12 : q + 12 ≤ n)
    (hstore : readBytes M' dst
      ((out ++ (body.drop i).take (q - i)).length + (utf8Encode cp').length) =
        some ((out ++ (body.drop i).take (q - i)) ++ utf8Encode cp')) :
    DecodeInv body st M' dst nps (q + 12) (c + 2)
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp') goal := by
  have hstored : readBytes M' dst
      (out ++ (body.drop i).take (q - i) ++ utf8Encode cp').length =
        some (out ++ (body.drop i).take (q - i) ++ utf8Encode cp') := by
    rw [List.length_append]
    exact hstore
  exact DecodeInv.step_pair_inv (c1 := 0x75) hinv hhead hb hlt hctl h1 hx ht hiq hq12
    hstored

/-- info: 'LeanLLVM.Vellum.DecodeInv.six_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.six_succ

/-- info: 'LeanLLVM.Vellum.DecodeInv.pair_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.pair_succ



theorem readBytes_one_of_readByte {m : Mem} {a : Nat} {b : UInt8}
    (h : readByte m a = some b) : readBytes m a 1 = some (natToBytes b.toNat 1) := by
  rw [LeanLLVM.Vellum.JsonEntrySteps.readBytes_one, h, natToBytes_one_eq]
  rfl

theorem readBytes_one_getD {m : Mem} {a n : Nat} {bs : List UInt8}
    (h : readBytes m a n = some bs) {k : Nat} (hk : k < n) :
    readBytes m (a + k) 1 = some (natToBytes (bs.getD k 0).toNat 1) :=
  readBytes_one_of_readByte (readByte_of_readBytes h hk)

theorem ofNat64_toNat {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ifEnd_sub13 {pos0 q i : Nat} (hiq : i ≤ q) (hpos0n : pos0 + q < 2 ^ 64) :
    BitVec.ofNat 64 (pos0 + q) - BitVec.ofNat 64 pos0 - BitVec.ofNat 64 i =
      BitVec.ofNat 64 (q - i) := by
  rw [ofNat_sub_ofNat (by omega) hpos0n, show pos0 + q - pos0 = q from by omega,
    ofNat_sub_ofNat hiq (by omega)]

theorem take_take_source {body extra : List UInt8} {i n sub : Nat}
    (hb : body.length = n) (hs : sub ≤ n - i) :
    ((body.drop i ++ extra).take (sub + 32)).take sub = (body.drop i).take sub := by
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_append, List.length_drop, hb,
    show sub - (n - i) = 0 from by omega, List.take_zero, List.append_nil]

/-- A sub-range of the source: the body from `off`, followed by the record's trailing
bytes as far as the range reaches. -/
theorem source_read_slice {m : Mem} {b n i : Nat} {body extra : List UInt8}
    (hb : body.length = n)
    (hsrc : readBytes m (b + i) ((n - i) + 32) = some (body.drop i ++ extra))
    {off len : Nat} (hioff : i ≤ off) (hon : off ≤ n) (hlen : off + len ≤ n + 32) :
    readBytes m (b + off) len = some ((body.drop off ++ extra).take len) := by
  have hfull : readBytes m (b + i) ((off - i) + ((n - i) + 32 - (off - i))) =
      some (body.drop i ++ extra) := by
    rw [show (off - i) + ((n - i) + 32 - (off - i)) = (n - i) + 32 from by omega]
    exact hsrc
  obtain ⟨-, h2⟩ := readBytes_split m (b + i) (off - i) ((n - i) + 32 - (off - i)) hfull
  have h2' : readBytes m (b + off) ((n - i) + 32 - (off - i)) =
      some ((body.drop i ++ extra).drop (off - i)) := by
    rwa [show b + i + (off - i) = b + off from by omega] at h2
  obtain ⟨h3, -⟩ := readBytes_split m (b + off) len
    ((n - i) + 32 - (off - i) - len) (bs := (body.drop i ++ extra).drop (off - i))
    (by
      rw [show len + ((n - i) + 32 - (off - i) - len) = (n - i) + 32 - (off - i) from by omega]
      exact h2')
  have hdrop : (body.drop i ++ extra).drop (off - i) = body.drop off ++ extra := by
    rw [List.drop_append_of_le_length (by rw [List.length_drop, hb]; omega), List.drop_drop,
      show i + (off - i) = off from by omega]
  rw [hdrop] at h3
  exact h3

/-! ### `us_run.exit` with its two different operands

The trace's `udRunExit_denote` binds `%sub13` and `%sub` to one value `subv`, but the
block reads both: `%add15 = %sub13 + %j.0294` takes the residual and
`%arrayidx16 = %p + %sub` takes the head position.  They are different registers with
different values at the iteration's exit (`q - i` and `q`), so this is the block's
step at both, stated once. -/

/-- `us_run.exit`'s environment at two operand values. -/
def udRunExitEnvS (env : Env) (paddr : Nat) (sub13v subv j : BitVec 64)
    (b : BitVec 8) : Env :=
  ("%cmp18", .int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) ::
    ("%7", .int 8 b) ::
    ("%arrayidx16", .ptr (paddr + subv.toNat)) ::
    ("%add15", .int 64 (sub13v + j)) :: env

theorem udRunExit_denoteS (env : Env) (s : State) (paddr : Nat)
    (sub13v subv j : BitVec 64) (b : BitVec 8)
    (hsub13 : lookupName env "%sub13" = some (.int 64 sub13v))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode escapeCalls udRunExit.instrs (withEnv env s) =
      some (withEnv (udRunExitEnvS env paddr sub13v subv j b) s) := by
  rw [udRunExit_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64 _ _ "%add15" "%sub13" "%j.0294" sub13v j
    (by ud_lk_h hsub13) (by ud_lk_h hj))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ _ "%arrayidx16" "%p" "%sub" paddr subv
    subv.toNat (by ud_lk_h hp) (by ud_lk_h hsub) hsw hs63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load8 _ _ "%7" "%arrayidx16" (paddr + subv.toNat) b
    (by ud_lk) hr)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult8_imm _ _ "%cmp18" "%7" b
    (BitVec.ofInt 8 32) (by ud_lk))]
  simp only [denoteCode, withEnv, udRunExitEnvS]

/-- `us_run.exit`'s step into `if.end21`: the body's byte at the head is not a control
byte. -/
theorem udRunExit_stepS_zero (env : Env) (s : State) (paddr : Nat)
    (sub13v subv j : BitVec 64) (b : BitVec 8)
    (hpc : s.pc = "us_run.exit")
    (hsub13 : lookupName env "%sub13" = some (.int 64 sub13v))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1))
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udRunExitEnvS env paddr sub13v subv j b) s) with
              pc := "if.end21", pre := some "us_run.exit" } := by
  rw [udStep_of (withEnv env s) "us_run.exit" udRunExit _
    (by rw [withEnv]; exact hpc) findBlock_udRunExit
    (udRunExit_denoteS env s paddr sub13v subv j b hsub13 hj hp hsub hsw hs63 hr),
    udRunExit_term]
  have hcmp : evalOperand (withEnv (udRunExitEnvS env paddr sub13v subv j b) s)
      (.reg "%cmp18") =
      some (.int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) :=
    evalOperand_reg_of _ s "%cmp18" _ (by simp only [udRunExitEnvS]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- `us_run.exit`'s step into `if.then20`: the body's byte at the head is a control
byte, so the refusal's first store block is reached from the same two-value
environment `udRunExit_stepS_zero` uses.

**Both arms need the two-value form.**  The trace's `udRunExit_step_one` and
`udRunExit_step` bind `%sub13` and `%sub` to one value, which holds only at cursor
zero (the residual is `q - i` and the head position `q`), so neither can serve the
iteration's cursor: the decoded exit composes the zero arm here
(`udRunExit_to_ifEndI`), and the refusal composed from `us_run.exit` needs this one.
The two arms are the block's whole branch, and they are stated at the same
environment so a consumer chooses by the block's `%cmp18` alone. -/
theorem udRunExit_stepS_one (env : Env) (s : State) (paddr : Nat)
    (sub13v subv j : BitVec 64) (b : BitVec 8)
    (hpc : s.pc = "us_run.exit")
    (hsub13 : lookupName env "%sub13" = some (.int 64 sub13v))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1))
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udRunExitEnvS env paddr sub13v subv j b) s) with
              pc := "if.then20", pre := some "us_run.exit" } := by
  rw [udStep_of (withEnv env s) "us_run.exit" udRunExit _
    (by rw [withEnv]; exact hpc) findBlock_udRunExit
    (udRunExit_denoteS env s paddr sub13v subv j b hsub13 hj hp hsub hsw hs63 hr),
    udRunExit_term]
  have hcmp : evalOperand (withEnv (udRunExitEnvS env paddr sub13v subv j b) s)
      (.reg "%cmp18") =
      some (.int 1 (evalICmp .ult b (BitVec.ofInt 8 32))) :=
    evalOperand_reg_of _ s "%cmp18" _ (by simp only [udRunExitEnvS]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### The tail's continuation through the middle

`us_run.exit` is the join of the tail's two edges.  It loads the body's byte at the
head position `%sub` and tests it against the control range, and `if.end21` then tests
that the byte after the escape is inside the body.  The two steps are one run here, at
the two operands `us_run.exit` keeps apart — the residual `%sub13` and the head
position `%sub` — which is why this composes `udRunExit_stepS_zero` and not the
trace's one-value form.

The cells are stated as the blocks' own arithmetic writes them: `%add15` is the
residual plus the prefix length and `%add.i100` is the head position plus one, so a
caller that instantiates those at the canonical `ofNat` values reads them back in the
same vocabulary.  `%cmp.not.i` carries `if.end21`'s own test, which is the predicate a
caller proves from the body's length and the head's bound. -/
theorem udRunExit_to_ifEndI (env : Env) (s : State) (paddr : Nat)
    (sub13v subv j nv : BitVec 64) (b : BitVec 8)
    (hpc : s.pc = "us_run.exit")
    (hsub13 : lookupName env "%sub13" = some (.int 64 sub13v))
    (hj : lookupName env "%j.0294" = some (.int 64 j))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hsw : (subv.signExtend 64).toNat = subv.toNat)
    (hs63 : subv.toNat < 2 ^ 63)
    (hr : readBytes s.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1))
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (1 : BitVec 1)) :
    ∃ (e : State) (k : Nat),
      k ≤ 2 ∧ e.pc = "if.end.i" ∧ e.pre = some "if.end21" ∧ e.mem = s.mem ∧
      lookupName e.env "%add15" = some (.int 64 (sub13v + j)) ∧
      lookupName e.env "%arrayidx16" = some (.ptr (paddr + subv.toNat)) ∧
      lookupName e.env "%7" = some (.int 8 b) ∧
      lookupName e.env "%add.i100" = some (.int 64 (subv + BitVec.ofInt 64 1)) ∧
      lookupName e.env "%cmp.not.i" =
        some (.int 1 (evalICmp .ult (subv + BitVec.ofInt 64 1) nv)) ∧
      lookupName e.env "%sub" = some (.int 64 subv) ∧
      lookupName e.env "%n" = some (.int 64 nv) ∧
      lookupName e.env "%p" = some (.ptr paddr) ∧
      lookupName e.env "%sub13" = some (.int 64 sub13v) ∧
      lookupName e.env "%j.0294" = some (.int 64 j) ∧
      (∀ z, runFuel escapeCalls (2 + z) usDecFunction (withEnv env s) =
        runFuel escapeCalls z usDecFunction e) := by
  let e1 : State :=
    { (withEnv (udRunExitEnvS env paddr sub13v subv j b) s) with
        pc := "if.end21", pre := some "us_run.exit" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udRunExit_stepS_zero env s paddr sub13v subv j b hpc hsub13 hj hp hsub hsw hs63 hr
      hcond
  let e2 : State :=
    { (withEnv (udIfEnd21Env (udRunExitEnvS env paddr sub13v subv j b) subv nv) s) with
        pc := "if.end.i", pre := some "if.end21" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 :=
    udIfEnd21_step (udRunExitEnvS env paddr sub13v subv j b)
      { s with pc := "if.end21", pre := some "us_run.exit" } subv nv rfl
      (by simp only [udRunExitEnvS]; ud_lk_h hsub)
      (by simp only [udRunExitEnvS]; ud_lk_h hn)
      hcond2
  refine ⟨e2, 2, by omega, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hsub
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hn
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hp
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hsub13
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hj
  · intro z
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep2]

/-! #### Axiom footprints: the tail's continuation -/

/-- info: 'LeanLLVM.Vellum.udRunExit_to_ifEndI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_to_ifEndI

/-! ### The middle's second block and the simple escape's arm

`if.end.i` reads the byte after the escape and the table's image of it, and when the
table answers a two-character escape the arm runs `if.then6.i`, which stores the
replacement byte at the destination cursor and advances it by one.  Both steps are
here, and the state they leave is `cleanup32` with its two `phi`s taken from the
simple-escape edge: `%j.3` is `%add8.i` and `%adv.2` is the literal two, which is what
`cleanup32`'s own step reads.

The store's address is `%dst + %add15`, and `%add15` is the block's own residual-plus-
prefix cell, so the memory is the statement's, not a new vocabulary. -/
theorem ifEndI_to_simple (env : Env) (s : State) (paddr tab daddr : Nat)
    (off outv sub inc11 nxp : BitVec 64) (c t : BitVec 8)
    (hpc : s.pc = "if.end.i")
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hout : lookupName env "%add15" = some (.int 64 outv))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hoffw : (off.signExtend 64).toNat = off.toNat) (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes c.toNat 1))
    (ht : readBytes s.mem (tab + c.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 c.toNat).signExtend 64).toNat = c.toNat)
    (hcond4 : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1))
    (how : (outv.signExtend 64).toNat = outv.toNat) (ho63 : outv.toNat < 2 ^ 63) :
    ∃ (e : State) (k : Nat),
      k ≤ 2 ∧ e.pc = "cleanup32" ∧ e.pre = some "if.then6.i" ∧
      e.mem = writeBytes s.mem (daddr + outv.toNat) (natToBytes t.toNat 1) ∧
      lookupName e.env "%add8.i" = some (.int 64 (outv + BitVec.ofInt 64 1)) ∧
      lookupName e.env "%9" = some (.int 8 t) ∧
      lookupName e.env "%8" = some (.int 8 c) ∧
      lookupName e.env "%add.i100" = some (.int 64 off) ∧
      lookupName e.env "%sub" = some (.int 64 sub) ∧
      lookupName e.env "%inc11" = some (.int 64 inc11) ∧
      lookupName e.env "%nxp" = some (.int 64 nxp) ∧
      lookupName e.env "%dst" = some (.ptr daddr) ∧
      (∀ z, runFuel escapeCalls (2 + z) usDecFunction (withEnv env s) =
        runFuel escapeCalls z usDecFunction e) := by
  let e1 : State :=
    { (withEnv (udIfEndIEnv env paddr tab off c t) s) with
        pc := "if.then6.i", pre := some "if.end.i" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udIfEndI_step env s paddr tab off c t hpc hp hoff htab hoffw hoff63 hb ht hgw hcond4
  let e2 : State :=
    { (withEnv (udIfThen6IEnv (udIfEndIEnv env paddr tab off c t) daddr outv)
        { s with mem := writeBytes s.mem (daddr + outv.toNat) (natToBytes t.toNat 1) }) with
        pc := "cleanup32", pre := some "if.then6.i" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udIfThen6I_step (udIfEndIEnv env paddr tab off c t)
      { s with pc := "if.then6.i", pre := some "if.end.i" } daddr outv t rfl
      (by simp only [udIfEndIEnv]; ud_lk_h hdst)
      (by simp only [udIfEndIEnv]; ud_lk_h hout)
      (by simp only [udIfEndIEnv]; ud_lk)
      how ho63
    exact h1
  refine ⟨e2, 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rfl
  · rfl
  · rfl
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk_h hoff
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk_h hsub
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk_h hinc11
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk_h hnxp
  · simp only [e2, withEnv, udIfThen6IEnv, udIfEndIEnv]; ud_lk_h hdst
  · intro z
    have h1 := runFuel_jump_prefix hstep1 (1 + z)
    have h2 := runFuel_jump_prefix hstep2 z
    rw [show 2 + z = 1 + (1 + z) from by omega]
    exact h1.trans h2

/-- info: 'LeanLLVM.Vellum.ifEndI_to_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEndI_to_simple

/-- **The `\u` entry of the emitter's chain.**  When the table maps the byte after the
escape to no two-character escape, `if.end.i` takes `if.end9.i`, which reads the byte
again: not `u`, or six bytes past the escape do not fit, is the refusal's edge, and
the other answer sends the run to the hex reader.  The two steps are here, at the
cells the hex reader reads: `%8` is the byte itself, `%add.i113` is the head position
plus six, and `%or.cond335` is the guard the branch took.

The arithmetic the `u` byte and the fit bound supply is the caller's: `%8`'s value and
`%or.cond335`'s zero are hypotheses, because they are the emitter's gate decision and
not a property of these two blocks' steps. -/
theorem ifEndI_to_u_entry (env : Env) (s : State) (paddr tab : Nat)
    (off sub nv : BitVec 64) (c t : BitVec 8)
    (hpc : s.pc = "if.end.i")
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hoff : lookupName env "%add.i100" = some (.int 64 off))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hoffw : (off.signExtend 64).toNat = off.toNat) (hoff63 : off.toNat < 2 ^ 63)
    (hb : readBytes s.mem (paddr + off.toNat) 1 = some (natToBytes c.toNat 1))
    (ht : readBytes s.mem (tab + c.toNat) 1 = some (natToBytes t.toNat 1))
    (hgw : ((BitVec.ofNat 64 c.toNat).signExtend 64).toNat = c.toNat)
    (hcond4 : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1))
    (hcond9 : (evalICmp .ne c (BitVec.ofInt 8 117) |||
      evalICmp .ugt (sub + BitVec.ofInt 64 6) nv) = (0 : BitVec 1)) :
    ∃ (e : State) (k : Nat),
      k ≤ 2 ∧ e.pc = "if.end.i115" ∧ e.pre = some "if.end9.i" ∧ e.mem = s.mem ∧
      lookupName e.env "%8" = some (.int 8 c) ∧
      lookupName e.env "%add.i113" = some (.int 64 (sub + BitVec.ofInt 64 6)) ∧
      lookupName e.env "%add.i100" = some (.int 64 off) ∧
      lookupName e.env "%9" = some (.int 8 t) ∧
      lookupName e.env "%sub" = some (.int 64 sub) ∧
      lookupName e.env "%n" = some (.int 64 nv) ∧
      (∀ z, runFuel escapeCalls (2 + z) usDecFunction (withEnv env s) =
        runFuel escapeCalls z usDecFunction e) := by
  let e1 : State :=
    { (withEnv (udIfEndIEnv env paddr tab off c t) s) with
        pc := "if.end9.i", pre := some "if.end.i" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udIfEndI_step_zero env s paddr tab off c t hpc hp hoff htab hoffw hoff63 hb ht hgw
      hcond4
  let e2 : State :=
    { (withEnv (udIfEnd9IEnv (udIfEndIEnv env paddr tab off c t) (sub + BitVec.ofInt 64 6)
        (evalICmp .ne c (BitVec.ofInt 8 117))
        (evalICmp .ugt (sub + BitVec.ofInt 64 6) nv)) s) with
        pc := "if.end.i115", pre := some "if.end9.i" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udIfEnd9I_step_zero (udIfEndIEnv env paddr tab off c t)
      { s with pc := "if.end9.i", pre := some "if.end.i" } sub nv c rfl
      (by simp only [udIfEndIEnv]; ud_lk)
      (by simp only [udIfEndIEnv]; ud_lk_h hsub)
      (by simp only [udIfEndIEnv]; ud_lk_h hn) hcond9
    exact h1
  refine ⟨e2, 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rfl
  · rfl
  · rfl
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk_h hoff
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk_h hsub
  · simp only [e2, withEnv, udIfEnd9IEnv, udIfEndIEnv]; ud_lk_h hn
  · intro z
    have h1 := runFuel_jump_prefix hstep1 (1 + z)
    have h2 := runFuel_jump_prefix hstep2 z
    rw [show 2 + z = 1 + (1 + z) from by omega]
    exact h1.trans h2

/-- info: 'LeanLLVM.Vellum.ifEndI_to_u_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEndI_to_u_entry

/-- **`if.end3.i`'s zero arm.**  The guard false is the six-byte form: the code unit
did not open a surrogate pair (or the twelve bytes do not fit, or the next two bytes
are not `\` `u`), so the run goes straight to the block that packs and stores the
word.  The trace states the guard's one-arm only, and this is its sibling at the same
environment builder, which is the shape `udIfEnd21_step_zero` supplies for the middle. -/
theorem udIfEnd3I_step_zero (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (c : List (BitVec 1)) (sub n : BitVec 64)
    (hpc : s.pc = "if.end3.i")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (h10 : lookupName env "%10" = some (.vec 2 64 (unpackLanes 64 2 (bytesToNat bs))))
    (h11 : lookupName env "%11" = some (.vec 16 8 (byteLanes bs)))
    (hc190 : lookupName env "%cmp.i190" = some (.vec 16 1 c))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hlen : bs.length = 16) (hc16 : c.length = 16)
    (hcond : udIfEnd3IGuard bs c sub n = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd3IEnv env bs c sub n) s) with
              pc := "if.end32.i", pre := some "if.end3.i" } := by
  rw [udStep_of (withEnv env s) "if.end3.i" udIfEnd3I _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd3I
    (udIfEnd3I_denote env s addr bs c sub n haddr h10 h11 hc190 hsub hn hlen hc16),
    udIfEnd3I_term]
  have hcmp : evalOperand (withEnv (udIfEnd3IEnv env bs c sub n) s)
      (.reg "%or.cond334") =
      some (.int 1 (udIfEnd3IGuard bs c sub n)) :=
    evalOperand_reg_of _ s "%or.cond334" _ (by simp only [udIfEnd3IEnv]; hex_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- info: 'LeanLLVM.Vellum.udIfEnd3I_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd3I_step_zero

/-- **The hex reader's guard and the store, composed.**  From `if.end.i115` — the
sixteen bytes after the escape already in hand — `if.end3.i` tests the code unit's
high bits, the twelve bytes of room and the two trailing bytes, and `if.end32.i`
packs the unit's bytes into a word and stores them at `%dst + %add15`.  The
six-byte form is the guard's zero arm; the pair's twelve-byte arm runs
`if.then17.i`/`land.lhs.true22.i`/`if.then26.i` instead, which is a separate
statement.

The block's own cells are as their builders write them: `%and27.i` is the code unit's
low sixteen bits, `%adv.1.i` is the advance the phi supplied (`6` on this edge), and
`%add.i125` is the published length arithmetic at the packed word's width. -/
theorem hex_to_ifEnd32 (env : Env) (s : State) (addr : Nat) (bs : List UInt8)
    (sub nv add15 : BitVec 64) (daddr k : Nat)
    (c db : List (BitVec 1))
    (hpc : s.pc = "if.end.i115")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hadd15 : lookupName env "%add15" = some (.int 64 add15))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hinc11 : lookupName env "%inc11" = some (.int 64 (0 : BitVec 64)))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs)
    (hdb : db = hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
      (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))
    (hcond115 : evalICmp .eq
      (BitVec.ofNat 16 (lanesToNat (hexZipOr
        (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
        BitVec.ofInt 16 15) (BitVec.ofInt 16 15) = (1 : BitVec 1))
    (hcond3 : udIfEnd3IGuard bs db sub nv = (0 : BitVec 1))
    (hk : (add15.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    ∃ (e : State), e.pc = "cleanup32" ∧ e.pre = some "if.end32.i" ∧
      e.mem = writeBytes s.mem (daddr + k)
        (natToBytes (udIfEnd32Word (hxCode (byteLanes bs) db &&&
          BitVec.ofInt 32 65535)).toNat 4) ∧
      lookupName e.env "%add.i125" = some (.int 64
        (add15 + BitVec.ofNat 64 (evalICmp .ugt (hxCode (byteLanes bs) db &&&
          BitVec.ofInt 32 65535) (BitVec.ofInt 32 2047)).toNat +
          udIfEnd32Adv (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535) +
          BitVec.ofNat 64 (evalICmp .ugt (hxCode (byteLanes bs) db &&&
            BitVec.ofInt 32 65535) (BitVec.ofInt 32 65535)).toNat)) ∧
      lookupName e.env "%adv.1.i" = some (.int 64 (BitVec.ofInt 64 6)) ∧
      lookupName e.env "%sub" = some (.int 64 sub) ∧
      lookupName e.env "%dst" = some (.ptr daddr) := by
  have hc16 : db.length = 16 := by
    rw [hdb]
    simp only [hexUltL_length, hexAddL_length, hexOrL_length, byteLanes_length, hlen]
  let e1 : State :=
    { (withEnv (udIfEndI115Env env addr bs) s) with
        pc := "if.end3.i", pre := some "if.end.i115" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udIfEndI115_step env s addr bs hpc haddr hlen hload hcond115
  let e2 : State :=
    { (withEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) s) with
        pc := "if.end32.i", pre := some "if.end3.i" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udIfEnd3I_step_zero (udIfEndI115Env env addr bs)
      { s with pc := "if.end3.i", pre := some "if.end.i115" } addr bs db sub nv rfl
      (by simp only [udIfEndI115Env]; ud_lk_h haddr)
      (by simp only [udIfEndI115Env]; ud_lk)
      (by simp only [udIfEndI115Env]; ud_lk)
      (by simp only [udIfEndI115Env]; rw [hdb]; ud_lk)
      (by simp only [udIfEndI115Env]; ud_lk_h hsub)
      (by simp only [udIfEndI115Env]; ud_lk_h hn)
      hlen hc16 hcond3
    exact h1
  let e3 : State :=
    { (withEnv (udIfEnd32IEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv)
        (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535)
        (BitVec.ofInt 64 6) add15 daddr k)
        (udIfEnd32IWritten s daddr k (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535))) with
        pc := "cleanup32", pre := some "if.end32.i" }
  have hstep3 : step escapeCalls usDecFunction e2 = .jump e3 := by
    have h1 := udIfEnd32I_step
      (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv)
      { s with pc := "if.end32.i", pre := some "if.end3.i" } "if.end3.i"
      (.reg "%and27.i") (.imm (.int 64 (BitVec.ofInt 64 6)))
      (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535) (BitVec.ofInt 64 6) add15
      daddr k rfl rfl (by decide)
      (by
        show phiIncoming "if.end3.i" udIfEnd32IIncomingAdv =
          some (.imm (.int 64 (BitVec.ofInt 64 6)))
        decide)
      (by
        show evalOperand (withEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) s)
          (.reg "%and27.i") = some (.int 32 (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535))
        simp only [udIfEnd3IEnv, udIfEndI115Env]; hex_lk)
      (by
        show evalOperand (withEnv (("%cp.i.3", .int 32 (hxCode (byteLanes bs) db &&&
          BitVec.ofInt 32 65535)) :: udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) s)
          (.imm (.int 64 (BitVec.ofInt 64 6))) = some (.int 64 (BitVec.ofInt 64 6))
        simp [evalOperand, Const.toValue])
      (by simp only [udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hdst)
      (by simp only [udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hadd15)
      hk hpos
    exact h1
  refine ⟨e3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp only [e3, withEnv, udIfEnd32IEnv, udIfEnd3IEnv, udIfEndI115Env]; hex_lk
  · simp only [e3, withEnv, udIfEnd32IEnv, udIfEnd3IEnv, udIfEndI115Env]; hex_lk
  · simp only [e3, withEnv, udIfEnd32IEnv, udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hsub
  · simp only [e3, withEnv, udIfEnd32IEnv, udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hdst

/-- info: 'LeanLLVM.Vellum.hex_to_ifEnd32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hex_to_ifEnd32

/-- **The pair's word value**, as the four blocks form it: the second unit's low ten
bits below the first unit's, shifted up and offset, the two lanes disjoint.

`%and27.i` is the first unit's low sixteen bits (from `if.end3.i`), `%sub23.i` is
the second unit's offset from `DC00` (from `land.lhs.true22.i`), and `%add30.i`
combines them.  The expression is the phi's operand on the `if.then26.i` edge. -/
def pairArmValue (bs bs2 : List UInt8) (db : List (BitVec 1)) : BitVec 32 :=
  let cl2 := hexUltL (hexAddL (hexOrL (byteLanes bs2) (BitVec.ofInt 8 32))
    (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)
  let hi := hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535
  let lo := hxCode (byteLanes bs2) cl2 &&& BitVec.ofInt 32 65535
  (lo + BitVec.ofInt 32 (-56320)) |||
    ((hi <<< (BitVec.ofInt 32 10)) + BitVec.ofInt 32 (-56557568))

/-- **The pair arm.**  `if.end3.i`'s one-arm sends the run into the surrogate pair's
four blocks and out at the latch: `if.then17.i` reads the second `\u`'s digits,
`land.lhs.true22.i` folds them to the low ten bits and tests the low-surrogate
range, `if.then26.i` combines the two units, and `if.end32.i` stores the pair's
packed word at `%dst + %add15` with the twelve-byte advance the phi supplies.

The composition is the *run*: the state's cells are the builders' own, and the
memory is the one store `if.end32.i` makes.  `%cp.i.3` is the pair's code point
`udIfThen26I_pairValue` names, which is what the walk transfer below it reads.

The four gates are hypotheses, because they are the branch decisions and not a
property of these blocks' steps: `hcond3` is the high-surrogate range and the twelve
bytes' room, `hcond17` is the four digits being hexadecimal, `hcond22` is the second
unit's low-surrogate range. -/
theorem pairArm_to_cleanup32 (env : Env) (s : State) (addr : Nat)
    (bs bs2 : List UInt8) (sub nv add15 : BitVec 64) (daddr k : Nat)
    (db : List (BitVec 1))
    (hpc : s.pc = "if.end.i115")
    (haddr : lookupName env "%arrayidx16" = some (.ptr addr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hadd15 : lookupName env "%add15" = some (.int 64 add15))
    (hsub : lookupName env "%sub" = some (.int 64 sub))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hlen : bs.length = 16)
    (hload : readBytes s.mem (addr + 2) 16 = some bs)
    (hdb : db = hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
      (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))
    (hcond115 : evalICmp .eq
      (BitVec.ofNat 16 (lanesToNat (hexZipOr
        (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
        BitVec.ofInt 16 15) (BitVec.ofInt 16 15) = (1 : BitVec 1))
    (hcond3 : udIfEnd3IGuard bs db sub nv = (1 : BitVec 1))
    (hlen2 : bs2.length = 16)
    (hload2 : readBytes s.mem (addr + 8) 16 = some bs2)
    (hcond17 : evalICmp .eq
      (BitVec.ofNat 16 (lanesToNat (hexZipOr
        (hexUltL (hexAddL (byteLanes bs2) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs2) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)))) &&&
        BitVec.ofInt 16 15) (BitVec.ofInt 16 15) = (1 : BitVec 1))
    (hcond22 : evalICmp .ult
      ((hxCode (byteLanes bs2) (hexUltL (hexAddL (hexOrL (byteLanes bs2)
          (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)) &&&
        BitVec.ofInt 32 65535) + BitVec.ofInt 32 (-56320))
      (BitVec.ofInt 32 1024) = (1 : BitVec 1))
    (hk : (add15.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    ∃ (e : State),
      e.pc = "cleanup32" ∧ e.pre = some "if.end32.i" ∧
      e.mem = writeBytes s.mem (daddr + k)
        (natToBytes (udIfEnd32Word (pairArmValue bs bs2 db)).toNat 4) ∧
      lookupName e.env "%cp.i.3" = some (.int 32 (pairArmValue bs bs2 db)) ∧
      lookupName e.env "%adv.1.i" = some (.int 64 (BitVec.ofInt 64 12)) ∧
      lookupName e.env "%sub" = some (.int 64 sub) ∧
      lookupName e.env "%dst" = some (.ptr daddr) ∧
      (∀ z, runFuel escapeCalls (6 + z) usDecFunction (withEnv env s) =
        runFuel escapeCalls z usDecFunction e) := by
  have hc16 : db.length = 16 := by
    rw [hdb]
    simp only [hexUltL_length, hexAddL_length, hexOrL_length, byteLanes_length, hlen]
  have hdl2 : (hexUltL (hexAddL (hexOrL (byteLanes bs2) (BitVec.ofInt 8 32))
      (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)).length = 16 := by
    simp only [hexUltL_length, hexAddL_length, hexOrL_length, byteLanes_length, hlen2]
  let e1 : State :=
    { (withEnv (udIfEndI115Env env addr bs) s) with
        pc := "if.end3.i", pre := some "if.end.i115" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udIfEndI115_step env s addr bs hpc haddr hlen hload hcond115
  let e2 : State :=
    { (withEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) s) with
        pc := "if.then17.i", pre := some "if.end3.i" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udIfEnd3I_step (udIfEndI115Env env addr bs)
      { s with pc := "if.end3.i", pre := some "if.end.i115" } addr bs db sub nv rfl
      (by simp only [udIfEndI115Env]; ud_lk_h haddr)
      (by simp only [udIfEndI115Env]; ud_lk)
      (by simp only [udIfEndI115Env]; ud_lk)
      (by simp only [udIfEndI115Env]; rw [hdb]; ud_lk)
      (by simp only [udIfEndI115Env]; ud_lk_h hsub)
      (by simp only [udIfEndI115Env]; ud_lk_h hn)
      hlen hc16 hcond3
    exact h1
  let e3 : State :=
    { (withEnv (udIfThen17IEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv)
        addr bs2) s) with
        pc := "land.lhs.true22.i", pre := some "if.then17.i" }
  have hstep3 : step escapeCalls usDecFunction e2 = .jump e3 := by
    have h1 := udIfThen17I_step
      (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv)
      { s with pc := "if.then17.i", pre := some "if.end3.i" } addr bs2 rfl
      (by simp only [udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h haddr)
      hlen2 hload2 hcond17
    exact h1
  let cl2 : List (BitVec 1) :=
    hexUltL (hexAddL (hexOrL (byteLanes bs2) (BitVec.ofInt 8 32))
      (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)
  let e4 : State :=
    { (withEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
        (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2) s) with
        pc := "if.then26.i", pre := some "land.lhs.true22.i" }
  have hstep4 : step escapeCalls usDecFunction e3 = .jump e4 := by
    have h1 := udLandLhsTrue22I_step
      (udIfThen17IEnv (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2)
      { s with pc := "land.lhs.true22.i", pre := some "if.then17.i" } bs2 cl2 rfl
      (by simp only [udIfThen17IEnv]; hex_lk)
      (by simp only [udIfThen17IEnv]; hex_lk)
      hlen2 hdl2 hcond22
    exact h1
  let hi : BitVec 32 := hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535
  let lo : BitVec 32 := hxCode (byteLanes bs2) cl2 &&& BitVec.ofInt 32 65535
  let s23 : BitVec 32 := lo + BitVec.ofInt 32 (-56320)
  let cp : BitVec 32 := pairArmValue bs bs2 db
  have hcpv : cp = s23 ||| ((hi <<< (BitVec.ofInt 32 10)) +
      BitVec.ofInt 32 (-56557568)) := rfl
  let e5 : State :=
    { (withEnv (udIfThen26IEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
        (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
        hi s23) s) with
        pc := "if.end32.i", pre := some "if.then26.i" }
  have hstep5 : step escapeCalls usDecFunction e4 = .jump e5 := by
    have h1 := udIfThen26I_step
      (udLandLhsTrue22IEnv (udIfThen17IEnv
        (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
      { s with pc := "if.then26.i", pre := some "land.lhs.true22.i" } hi s23 rfl
      (by simp only [udLandLhsTrue22IEnv]; hex_lk)
      (by simp only [udLandLhsTrue22IEnv]; hex_lk)
    exact h1
  let e6 : State :=
    { (withEnv (udIfEnd32IEnv (udIfThen26IEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
        (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
        hi s23) cp (BitVec.ofInt 64 12) add15 daddr k)
        (udIfEnd32IWritten s daddr k cp)) with
        pc := "cleanup32", pre := some "if.end32.i" }
  have hstep6 : step escapeCalls usDecFunction e5 = .jump e6 := by
    have h1 := udIfEnd32I_step
      (udIfThen26IEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
        (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
        hi s23)
      { s with pc := "if.end32.i", pre := some "if.then26.i" } "if.then26.i"
      (.reg "%add30.i") (.imm (.int 64 (BitVec.ofInt 64 12))) cp
      (BitVec.ofInt 64 12) add15 daddr k rfl rfl (by decide) (by decide)
      (by
        show evalOperand (withEnv (udIfThen26IEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
          (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
          hi s23) s) (.reg "%add30.i") = some (.int 32 cp)
        simp only [hcpv, s23, lo, hi, udIfThen26IEnv]; hex_lk)
      (by
        show evalOperand (withEnv (("%cp.i.3", .int 32 cp) ::
          udIfThen26IEnv (udLandLhsTrue22IEnv (udIfThen17IEnv
            (udIfEnd3IEnv (udIfEndI115Env env addr bs) bs db sub nv) addr bs2) bs2 cl2)
            hi s23) s) (.imm (.int 64 (BitVec.ofInt 64 12))) =
          some (.int 64 (BitVec.ofInt 64 12))
        simp [evalOperand, Const.toValue])
      (by simp only [udIfThen26IEnv, udLandLhsTrue22IEnv, udIfThen17IEnv, udIfEnd3IEnv,
        udIfEndI115Env]; ud_lk_h hdst)
      (by simp only [udIfThen26IEnv, udLandLhsTrue22IEnv, udIfThen17IEnv, udIfEnd3IEnv,
        udIfEndI115Env]; ud_lk_h hadd15)
      hk hpos
    exact h1
  have hmem : e6.mem = writeBytes s.mem (daddr + k)
      (natToBytes (udIfEnd32Word (pairArmValue bs bs2 db)).toNat 4) := by
    simp only [e6, udIfEnd32IWritten]
    rfl
  have hcpcell : lookupName e6.env "%cp.i.3" =
      some (.int 32 (pairArmValue bs bs2 db)) := by
    simp only [e6, withEnv, udIfEnd32IEnv, udIfThen26IEnv]; ud_lk
  have hadvcell : lookupName e6.env "%adv.1.i" =
      some (.int 64 (BitVec.ofInt 64 12)) := by
    simp only [e6, withEnv, udIfEnd32IEnv, udIfThen26IEnv]; ud_lk
  have hsubcell : lookupName e6.env "%sub" = some (.int 64 sub) := by
    simp only [e6, withEnv, udIfEnd32IEnv, udIfThen26IEnv, udLandLhsTrue22IEnv,
      udIfThen17IEnv, udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hsub
  have hdstcell : lookupName e6.env "%dst" = some (.ptr daddr) := by
    simp only [e6, withEnv, udIfEnd32IEnv, udIfThen26IEnv, udLandLhsTrue22IEnv,
      udIfThen17IEnv, udIfEnd3IEnv, udIfEndI115Env]; ud_lk_h hdst
  exact ⟨e6, rfl, rfl, hmem, hcpcell, hadvcell, hsubcell, hdstcell, fun z => by
    rw [show 6 + z = (5 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 5 + z = (4 + z) + 1 from by omega, udRun_jump hstep2]
    rw [show 4 + z = (3 + z) + 1 from by omega, udRun_jump hstep3]
    rw [show 3 + z = (2 + z) + 1 from by omega, udRun_jump hstep4]
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep5]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep6]⟩

/-- info: 'LeanLLVM.Vellum.pairArmValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairArmValue

/-- **The pair's stored word is the specification's encoding of its code point.**

The pair arm packs the two code units into one word (`pairArmValue`) and stores the
four bytes `udIfEnd32Word` selects out of it; the walk writes the bytes
`utf8Encode cp'` of the same code point.  This is the composition of the two
halves already proved: `udIfThen26I_pairValue` reads the pair's `Nat` value off the
masked units, and `udIfEnd32Word_toNat` reads the store's bytes off that value.

The two hypotheses are the units' **hex identifications**, which is the form
`hex4_hxCode` concludes at each of the two `\u` digit runs (`if.end.i115` for the
high unit, `if.then17.i` for the low one): the block's masked `hxCode` word is the
unit `hex4` found.  The masked word is what the blocks' own `%and27.i` holds, so a
consumer applies this lemma with `hex4_hxCode`'s result rather than re-deriving the
lane arithmetic. -/
theorem pairArmValue_word {bs bs2 : List UInt8} {db : List (BitVec 1)}
    {hi lo cp' : Nat}
    (hhi : (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535).toNat = hi)
    (hlo : (hxCode (byteLanes bs2) (hexUltL (hexAddL (hexOrL (byteLanes bs2)
      (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)) &&&
      BitVec.ofInt 32 65535).toNat = lo)
    (hrhi : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF)
    (hrlo : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)
    (hcp : cp' = 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :
    (udIfEnd32Word (pairArmValue bs bs2 db)).toNat = bytesToNat (utf8Encode cp') := by
  have hdouble : ∀ x : BitVec 32,
      x &&& BitVec.ofInt 32 65535 &&& BitVec.ofInt 32 65535 =
        x &&& BitVec.ofInt 32 65535 := by
    intro x
    rw [BitVec.and_assoc, BitVec.and_self]
  have hval : (pairArmValue bs bs2 db).toNat = cp' := by
    have h := udIfThen26I_pairValue
      (hxCode (byteLanes bs) db &&& BitVec.ofInt 32 65535)
      (hxCode (byteLanes bs2) (hexUltL (hexAddL (hexOrL (byteLanes bs2)
        (BitVec.ofInt 8 32)) (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6)) &&&
        BitVec.ofInt 32 65535)
      (by rw [hhi]; exact hrhi) (by rw [hlo]; exact hrlo)
    rw [hhi, hlo] at h
    rw [hcp]
    simpa only [pairArmValue, hdouble] using h
  calc (udIfEnd32Word (pairArmValue bs bs2 db)).toNat
      = bytesToNat (utf8Encode (pairArmValue bs bs2 db).toNat) :=
        udIfEnd32Word_toNat _ (by rw [hval]; omega)
    _ = bytesToNat (utf8Encode cp') := by rw [hval]

/-- info: 'LeanLLVM.Vellum.pairArmValue_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairArmValue_word

/-- info: 'LeanLLVM.Vellum.pairArm_to_cleanup32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairArm_to_cleanup32

/-- **The middle's refusal branch.**  `if.end21`'s zero arm sends the run to
`if.then22`, which performs the refusal's two stores — the offset at `%err` and the
index at `%xj` — and then reaches `cleanup41`.  The two steps are here with the
memory they leave, which is the word the exit's refusal branch reads: the caller's
staging supplies the two slot bases, and this lemma names the writes it made. -/
theorem ifEnd21_to_refusal (env : Env) (s : State) (subv nv inc11 : BitVec 64)
    (err xj : Nat)
    (hpc : s.pc = "if.end21")
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hinc11 : lookupName env "%inc11" = some (.int 64 inc11))
    (herr : lookupName env "%err" = some (.ptr err))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hcond : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (0 : BitVec 1)) :
    ∃ (e : State) (k : Nat),
      k ≤ 2 ∧ e.pc = "cleanup41" ∧ e.pre = some "if.then22" ∧
      e.mem = udRefusalMem s.mem subv.toNat err inc11.toNat xj ∧
      lookupName e.env "%sub" = some (.int 64 subv) ∧
      lookupName e.env "%inc11" = some (.int 64 inc11) ∧
      lookupName e.env "%err" = some (.ptr err) ∧
      lookupName e.env "%xj" = some (.ptr xj) ∧
      (∀ z, runFuel escapeCalls (2 + z) usDecFunction (withEnv env s) =
        runFuel escapeCalls z usDecFunction e) := by
  let e1 : State :=
    { (withEnv (udIfEnd21Env env subv nv) s) with
        pc := "if.then22", pre := some "if.end21" }
  have hstep1 : step escapeCalls usDecFunction (withEnv env s) = .jump e1 :=
    udIfEnd21_step_zero env s subv nv hpc hsub hn hcond
  let e2 : State :=
    { (withEnv (udIfEnd21Env env subv nv)
        { s with mem := udRefusalMem s.mem subv.toNat err inc11.toNat xj }) with
        pc := "cleanup41", pre := some "if.then22" }
  have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
    have h1 := udIfThen22_step (udIfEnd21Env env subv nv)
      { s with pc := "if.then22", pre := some "if.end21" } subv inc11 err xj rfl
      (by simp only [udIfEnd21Env]; ud_lk_h hsub)
      (by simp only [udIfEnd21Env]; ud_lk_h hinc11)
      (by simp only [udIfEnd21Env]; ud_lk_h herr)
      (by simp only [udIfEnd21Env]; ud_lk_h hxj)
    exact h1
  refine ⟨e2, 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rfl
  · rfl
  · rfl
  · simp only [e2, withEnv, udIfEnd21Env]; ud_lk_h hsub
  · simp only [e2, withEnv, udIfEnd21Env]; ud_lk_h hinc11
  · simp only [e2, withEnv, udIfEnd21Env]; ud_lk_h herr
  · simp only [e2, withEnv, udIfEnd21Env]; ud_lk_h hxj
  · intro z
    have h1 := runFuel_jump_prefix hstep1 (1 + z)
    have h2 := runFuel_jump_prefix hstep2 z
    rw [show 2 + z = 1 + (1 + z) from by omega]
    exact h1.trans h2

/-- info: 'LeanLLVM.Vellum.ifEnd21_to_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd21_to_refusal

/-- **The successor latch's staging is the current one.**  The emitter writes inside
the destination extent, so every byte the position stream occupies is the caller's:
the stream read, its length, each entry's window and the body's end offset all survive
the iteration.  The disjointness is the staging's own (the record excludes the stream
from the destination extent), stated here in the two-disjunct form the clauses use.

This is the staging half of the successor `AssemblyLatchInv`, and the reason the
invariant's non-memory conjuncts — the pinnings and the walk — are the only ones an
iteration changes. -/
theorem successor_staging {M m : Mem} {nps xp pos0 n : Nat} {ps : List Nat}
    {addv : BitVec 64} {dst : Nat}
    (hstage : DecodeStaging M nps xp pos0 n ps addv)
    (hframe : UnchangedOutside M m [(dst, n + 64)])
    (hdisj : xp + 4 * nps ≤ dst ∨ dst + (n + 64) ≤ xp) :
    DecodeStaging m nps xp pos0 n ps addv := by
  obtain ⟨hstream, hlen, hrange, hadd⟩ := hstage
  refine ⟨?_, hlen, hrange, hadd⟩
  rw [readBytes_of_UnchangedOutside hframe]
  · exact hstream
  · intro x hx1 hx2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rcases hdisj with hd | hd
    · omega
    · omega

/-- info: 'LeanLLVM.Vellum.successor_staging' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms successor_staging

/-- **The successor latch's invariant.**  One iteration's outputs are the next
latch's premisses: the emitter's `DecodeInv` transfer is the walk, the cells the
phi and the middle's blocks leave are the `DecodeLatch` fields, the staging survives
the emitter's write (`successor_staging`), the spacing is inherited
(`assemblyLatchInv_spaced_succ`), and the budget closes because the cursor advanced.

This is the assembly the iteration arm consumes: `P`-side hypotheses are the run's
own cells and the transfer's results, and everything `AssemblyLatchInv` states is
derived here rather than restated.  In particular the *cursor bound* `c' ≤ nps` is a
hypothesis, not a consequence of `DecodeInv.step_pair`; the surrogate pair's is
`escAt_pair_succ_le_nps`, and a two-character or six-byte escape's is `c < nps`.

The pinnings are the run's, not the caller's invention: the emitter blocks read the
same `%p`, `%xp`, `%tab`, `%pos0`, `%n`, `%err` and `%xj` cells and write none of
them, so the successor's are the predecessor's, carried by the ``hpin`` hypotheses
against the successor state. -/
theorem assemblyLatchInv_succ {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab : Nat} {pos0 n : Nat} {ps : List Nat}
    {err xj : Nat} {mem : Mem} {r c : Nat} {s e : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem (r + 1) c s)
    {i q adv i' c' : Nat} {bytes : List UInt8} {b' : UInt8} {out' : List UInt8}
    {prev : String} {sub inc11 nxp advv j addv : BitVec 64}
    (hpc : e.pc = "cleanup32")
    (hpre : e.pre = some prev)
    (hphi : (prev = "if.end32.i" ∧ lookupName e.env "%add.i125" = some (.int 64 j) ∧
        lookupName e.env "%adv.1.i" = some (.int 64 advv)) ∨
      (prev = "if.then6.i" ∧ lookupName e.env "%add8.i" = some (.int 64 j) ∧
        advv = BitVec.ofInt 64 2))
    (hsubc : lookupName e.env "%sub" = some (.int 64 sub))
    (hinc11c : lookupName e.env "%inc11" = some (.int 64 inc11))
    (hnxpc : lookupName e.env "%nxp" = some (.int 64 nxp)) (hnxpv : nxp.toNat = nps)
    (hnext : (decodeNextIdx inc11 advv).toNat = c')
    (hadvsub : (advv + sub).toNat = i') (hi' : q + adv = i')
    (hjlen : j.toNat = out'.length)
    (hwalk : DecodeInv body st e.mem dst nps i' c' out' goal)
    (hcle : c' ≤ nps) (hcgt : c < c')
    (hcurE : ∀ k : Nat, latchCursor e = some k → k ≤ n)
    (hi : latchCursor s = some i) (hq : (escAt body st 0)[c]? = some q)
    (hb : body[q]? = some b') (hctl : IsControlB b' = false)
    (hesc : escapeAt body q = some (bytes, adv))
    (hc'eq : c' = c + 1 + (if adv = 12 then 1 else 0))
    (hstage : DecodeStaging e.mem nps xp pos0 n ps addv)
    (haddcell : lookupName e.env "%add" = some (.int 64 addv))
    (hp_b : lookupName e.env "%p" = some (.ptr b))
    (hxp_b : lookupName e.env "%xp" = some (.ptr xp))
    (htab_b : lookupName e.env "%tab" = some (.ptr tab))
    (hpos0_b : lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hn_b : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (herr_b : lookupName e.env "%err" = some (.ptr err))
    (hxj_b : lookupName e.env "%xj" = some (.ptr xj))
    (hdst_b : lookupName e.env "%dst" = some (.ptr dst))
    (hframe : UnchangedOutside mem e.mem [(dst, n + 64)]) :
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c' e := by
  -- the budget: the cursor moved on, so one step of it is spent
  have hbudget : nps ≤ c' + r := by
    have hb := assemblyLatchInv_budget h
    omega
  -- the spacing is inherited at the emitter's own escape
  have hspd : Spaced body (q + adv) ((escAt body st 0).drop c') := by
    have hs := assemblyLatchInv_spaced_succ h hi hq hb hctl hesc
    rw [hc'eq]
    exact hs
  -- the successor's cursor is the walk's, so the spacing clause reads at either
  have hcurV : ∀ k : Nat, latchCursor e = some k → k = i' := by
    intro k hk
    rcases hphi with ⟨rfl, _, ha⟩ | ⟨rfl, _, ha⟩
    · simp only [latchCursor, hpre, hsubc, ha] at hk
      have h1 : k = (advv + sub).toNat := (Option.some.inj hk).symm
      rw [h1]
      exact hadvsub
    · simp only [latchCursor, hpre, hsubc] at hk
      have h1 : k = (BitVec.ofInt 64 2 + sub).toNat := (Option.some.inj hk).symm
      rw [h1, ← ha]
      exact hadvsub
  refine ⟨⟨⟨⟨i', out', prev, sub, inc11, advv, j, nxp, b, xp, tab, err, xj,
      BitVec.ofNat 64 pos0, addv, BitVec.ofNat 64 n,
      hpc, hwalk, hcle, hpre, hsubc, hinc11c, hnxpc, hnxpv, hphi, hnext, hadvsub,
      hjlen, hp_b, hdst_b, hxp_b, htab_b, herr_b, hxj_b, hpos0_b, haddcell, hn_b⟩,
      hbudget⟩, addv, hstage, haddcell⟩, hp_b, hxp_b, htab_b, hpos0_b, hn_b, herr_b,
    hxj_b, hcurE, ?_, hframe⟩
  intro k hk
  rw [hcurV k hk, ← hi']
  exact hspd

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchInv_succ

/-! ### `if.end`'s two arms, composed to the copy's exit word

The block's residual test sends the run round the sixty-four-byte copy when it is
one and straight to the copy's exit block when it is zero.  Each arm is stated
separately because the exit block's two `phi`s take different operands from the two
edges — `%add.i98`/`%sub.i87` on the copy's, the zero constant and `%sub13` on
`if.end`'s. -/

/-- **The copy arm.**  The test being one puts the run in `while.body.i91` with the
copy's invariant at its whole bound, and the loop's induction leaves the copy's exit
word.  The source range is the body from the walk's cursor plus the record's trailing
bytes, the destination base is the decoded prefix's end, and the two ranges are
disjoint — which is what makes the source read survive the copy's own stores. -/
theorem ifEnd_copyArm
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b pos0 n : Nat} {s : State} {i q c : Nat} {out extra : List UInt8}
    {inc11 adv : BitVec 64} {mem : Mem}
    (hpc : s.pc = "if.end") (hpre : s.pre = some "while.body6")
    (hinv : DecodeInv body st s.mem dst nps i c out goal)
    (hiq : i ≤ q) (hqn : q < n) (hnn : pos0 + n ≤ 2 ^ 32)
    (hdisjS : b + n + 32 ≤ dst ∨ dst + n + 64 ≤ b)
    (hframe : UnchangedOutside mem s.mem [(dst, n + 64)])
    (hbody : readBytes s.mem b n = some body)
    (hextra : readBytes s.mem (b + n) 32 = some extra)
    (hk : lookupName s.env "%k.1296" = some (.int 64 (decodeNextIdx inc11 adv)))
    (hc8 : lookupName s.env "%conv8" = some (.int 64 (BitVec.ofNat 64 (pos0 + q))))
    (hp0 : lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hp : lookupName s.env "%p" = some (.ptr b))
    (hi5 : lookupName s.env "%i.0295" = some (.int 64 (BitVec.ofNat 64 i)))
    (hdstc : lookupName s.env "%dst" = some (.ptr dst))
    (hj4 : lookupName s.env "%j.0294" = some (.int 64 (BitVec.ofNat 64 out.length)))
    (hgt : 64 < q - i)
    (Cells : Env → Prop)
    (hCellsC : ∀ (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64), Cells env → Cells (udCopyBodyEnv env src dst k bs1 bs2 subv))
    (hcells3 : Cells (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0))) :
    ∃ (e : State) (j : Nat),
      j ≤ copyIterBound (q - i) + 2 ∧
      CopyExitWord copyBodyNames (b + i) (dst + out.length) (q - i)
        ((body.drop i ++ extra).take ((q - i) + 32)) e ∧
      readBytes e.mem dst out.length = some out ∧
      UnchangedOutside mem e.mem [(dst, n + 64)] ∧
      lookupName e.env "%p" = some (.ptr b) ∧
      lookupName e.env "%dst" = some (.ptr dst) ∧
      lookupName e.env "%j.0294" = some (.int 64 (BitVec.ofNat 64 out.length)) ∧
      Cells e.env ∧
      (∀ k, runFuel escapeCalls (j + k) usDecFunction s = runFuel escapeCalls k usDecFunction e) := by
  have hbodyL : body.length = n := JsonEntrySteps.readBytes_length s.mem b n hbody
  have hextralen : extra.length = 32 :=
    JsonEntrySteps.readBytes_length s.mem (b + n) 32 hextra
  have houtle : out.length ≤ i := hinv.prefix_le_cursor
  have hsub64 : q - i < 2 ^ 64 := by omega
  have hsrcfull : readBytes s.mem (b + i) ((n - i) + 32) = some (body.drop i ++ extra) :=
    (finalSource_read hbody (by omega) hextra).1
  have hwhole : readBytes s.mem (b + i) ((q - i) + 32) =
      some ((body.drop i ++ extra).take ((q - i) + 32)) :=
    source_read_slice hbodyL hsrcfull (Nat.le_refl _) (by omega) (by omega)
  have hBlen : ((body.drop i ++ extra).take ((q - i) + 32)).length = (q - i) + 32 := by
    rw [List.length_take,
      Nat.min_eq_left (by rw [List.length_append, List.length_drop, hbodyL, hextralen]; omega)]
  have hdisj : copyDisjoint (b + i) (dst + out.length) (q - i) := by
    rcases hdisjS with hd | hd
    · right; omega
    · left; omega
  have hcond1 : evalICmp .ugt
      (BitVec.ofNat 64 (pos0 + q) - BitVec.ofNat 64 pos0 - BitVec.ofNat 64 i)
      (BitVec.ofInt 64 64) = (1 : BitVec 1) := by
    rw [ifEnd_sub13 hiq (by omega)]
    exact (evalICmp_ugt_one_iff_toNat _ _).2 (by
      rw [ofNat64_toNat hsub64, show (BitVec.ofInt 64 64).toNat = 64 from by decide]
      exact hgt)
  let e3 : State :=
    { (withEnv (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
        (BitVec.ofNat 64 pos0)) s) with
        pc := "while.body.i91", pre := some "if.end" }
  have hstep3 : step escapeCalls usDecFunction s = .jump e3 := by
    have h1 := udIfEnd_step s.env s b dst (decodeNextIdx inc11 adv) (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q)) (BitVec.ofNat 64 pos0)
      hpc hk hc8 hp0 hp hi5 hdstc hj4
      (by rw [ofNat64_toNat (by omega)]; omega)
      (by rw [ofNat64_toNat (by omega)]; omega)
      (signExtend_self_toNat _) (signExtend_self_toNat _) hcond1
    rw [show withEnv s.env s = s from rfl] at h1
    exact h1
  have hinvC : CopyInv copyBodyNames (b + i) (dst + out.length) (q - i)
      ((body.drop i ++ extra).take ((q - i) + 32)) (copyIterBound (q - i)) 0 e3 := by
    refine ⟨"if.end", .imm (.int 64 (BitVec.ofInt 64 0)), (0 : BitVec 64), rfl, rfl,
      by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
        (BitVec.ofNat 64 pos0)) "%add.ptr" = some (.ptr (b + i))
      simp only [udIfEndEnv]
      rw [ofNat64_toNat (x := i) (by omega)]
      ud_lk
    · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
        (BitVec.ofNat 64 pos0)) "%add.ptr12" = some (.ptr (dst + out.length))
      simp only [udIfEndEnv]
      rw [ofNat64_toNat (x := out.length) (by omega)]
      ud_lk
    · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
        (BitVec.ofNat 64 pos0)) "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i)))
      simp only [udIfEndEnv]
      rw [ifEnd_sub13 hiq (by omega)]
      ud_lk
    · rw [show e3.mem = s.mem from rfl]; exact hwhole
    · exact hBlen
    · rw [show e3.mem = s.mem from rfl]
      rfl
    · exact hdisj
    · omega
    · exact hgt
    · exact Nat.zero_le _
    · show copyIterBound (q - i) ≤ 0 + copyIterBound (q - i)
      omega
  have hcells3' : Cells e3.env := hcells3
  obtain ⟨eL, jL, hrest⟩ :=
    (copyBodyPrefixLoop (b + i) (dst + out.length) (q - i)
      ((body.drop i ++ extra).take ((q - i) + 32)) b dst out.length out s.mem (n + 64)
      (by omega) (by omega) Cells hCellsC).run_from (copyIterBound (q - i)) e3 0
      ⟨hinvC, hinv.stored, fun a _ => rfl, hp, hdstc, hj4, hcells3'⟩
  obtain ⟨hjL, hpcL, hwL, hrunL⟩ := hrest
  obtain ⟨hw1, hprefL, hframeL, hpL, hdL, hjcellL, hcellsL⟩ := hwL
  obtain ⟨hpcL', hpreL, hknext, hsnext, hsrcLb, hdstLb, hsubLb, hdstreadL, hsrcLb2⟩ := hw1
  have hjL' : jL ≤ copyIterBound (q - i) + 1 := by
    have := hjL; simpa [copyBodyPrefixLoop, Nat.mul_one] using this
  exact ⟨eL, 1 + jL, by omega,
    ⟨hpcL', hpreL, hknext, hsnext, hsrcLb, hdstLb, hsubLb, hdstreadL, hsrcLb2⟩,
    hprefL, UnchangedOutside.comp hframe hframeL (fun r hr => hr), hpL, hdL, hjcellL,
    hcellsL,
    fun k => by
      rw [show 1 + jL + k = 1 + (jL + k) from by omega]
      exact (runFuel_jump_prefix hstep3 (jL + k)).trans (hrunL k)⟩

/-- **The zero arm.**  The test being zero is one control step to the copy's exit
block on `if.end`'s own edge, where the exit block's counter is the zero constant and
its residual is `%sub13` itself. -/
theorem ifEnd_zeroArm
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b pos0 n : Nat} {s : State} {i q c : Nat} {out extra : List UInt8}
    {inc11 adv : BitVec 64} {mem : Mem}
    (hpc : s.pc = "if.end") (hpre : s.pre = some "while.body6")
    (hiq : i ≤ q) (hqn : q < n) (hnn : pos0 + n ≤ 2 ^ 32)
    (hframe : UnchangedOutside mem s.mem [(dst, n + 64)])
    (hbody : readBytes s.mem b n = some body)
    (hk : lookupName s.env "%k.1296" = some (.int 64 (decodeNextIdx inc11 adv)))
    (hc8 : lookupName s.env "%conv8" = some (.int 64 (BitVec.ofNat 64 (pos0 + q))))
    (hp0 : lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hp : lookupName s.env "%p" = some (.ptr b))
    (hi5 : lookupName s.env "%i.0295" = some (.int 64 (BitVec.ofNat 64 i)))
    (hdstc : lookupName s.env "%dst" = some (.ptr dst))
    (hj4 : lookupName s.env "%j.0294" = some (.int 64 (BitVec.ofNat 64 out.length)))
    (houtle : out.length ≤ i) (hle : q - i ≤ 64)
    (hprefix : readBytes s.mem dst out.length = some out)
    (Cells : Env → Prop)
    (hcells0 : Cells (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0))) :
    ∃ (e : State) (j : Nat),
      j ≤ 1 ∧ e.pc = "us_run_long.exit99" ∧ e.pre = some "if.end" ∧
      phiIncoming "if.end" udCopyTailIncomingK =
        some (.imm (.int 64 (BitVec.ofInt 64 0))) ∧
      phiIncoming "if.end" udCopyTailIncomingS = some (.reg "%sub13") ∧
      lookupName e.env "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i))) ∧
      lookupName e.env "%add.ptr" = some (.ptr (b + i)) ∧
      lookupName e.env "%add.ptr12" = some (.ptr (dst + out.length)) ∧
      readBytes e.mem dst out.length = some out ∧
      UnchangedOutside mem e.mem [(dst, n + 64)] ∧
      Cells e.env ∧
      (∀ k, runFuel escapeCalls (j + k) usDecFunction s = runFuel escapeCalls k usDecFunction e) := by
  have hsub64 : q - i < 2 ^ 64 := by omega
  have hcond0 : evalICmp .ugt
      (BitVec.ofNat 64 (pos0 + q) - BitVec.ofNat 64 pos0 - BitVec.ofNat 64 i)
      (BitVec.ofInt 64 64) = (0 : BitVec 1) := by
    rw [ifEnd_sub13 hiq (by omega)]
    exact (evalICmp_ugt_zero_iff _ _).2 (by
      rw [ofNat64_toNat hsub64, show (BitVec.ofInt 64 64).toNat = 64 from by decide]
      omega)
  let e0 : State :=
    { (withEnv (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
        (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
        (BitVec.ofNat 64 pos0)) s) with
        pc := "us_run_long.exit99", pre := some "if.end" }
  have hstep : step escapeCalls usDecFunction s = .jump e0 := by
    have h1 := udIfEnd_step_zero s.env s b dst (decodeNextIdx inc11 adv) (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q)) (BitVec.ofNat 64 pos0)
      hpc hk hc8 hp0 hp hi5 hdstc hj4
      (by rw [ofNat64_toNat (by omega)]; omega)
      (by rw [ofNat64_toNat (by omega)]; omega)
      (signExtend_self_toNat _) (signExtend_self_toNat _) hcond0
    rw [show withEnv s.env s = s from rfl] at h1
    exact h1
  refine ⟨e0, 1, by omega, rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_,
    fun k => runFuel_jump_prefix hstep k⟩
  · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0)) "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i)))
    simp only [udIfEndEnv]
    rw [ifEnd_sub13 hiq (by omega)]
    ud_lk
  · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0)) "%add.ptr" = some (.ptr (b + i))
    simp only [udIfEndEnv]
    rw [ofNat64_toNat (x := i) (by omega)]
    ud_lk
  · show lookupName (udIfEndEnv s.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0)) "%add.ptr12" = some (.ptr (dst + out.length))
    simp only [udIfEndEnv]
    rw [ofNat64_toNat (x := out.length) (by omega)]
    ud_lk
  · rw [show e0.mem = s.mem from rfl]; exact hprefix
  · rw [show e0.mem = s.mem from rfl]; exact hframe
  · exact hcells0

/-! #### Axiom footprints: the middle's arithmetic and the split step -/

/-- info: 'LeanLLVM.Vellum.natToBytes_one_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms natToBytes_one_eq

/-- info: 'LeanLLVM.Vellum.readBytes_one_of_readByte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readBytes_one_of_readByte

/-- info: 'LeanLLVM.Vellum.readBytes_one_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_one_getD

/-- info: 'LeanLLVM.Vellum.ofNat64_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofNat64_toNat

/-- info: 'LeanLLVM.Vellum.ifEnd_sub13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_sub13

/-- info: 'LeanLLVM.Vellum.take_take_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take_take_source

/-- info: 'LeanLLVM.Vellum.source_read_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_read_slice

/-- info: 'LeanLLVM.Vellum.udRunExitEnvS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms udRunExitEnvS

/-- info: 'LeanLLVM.Vellum.udRunExit_denoteS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_denoteS

/-- info: 'LeanLLVM.Vellum.udRunExit_stepS_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_stepS_zero

/-- info: 'LeanLLVM.Vellum.udRunExit_stepS_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udRunExit_stepS_one

/-- info: 'LeanLLVM.Vellum.ifEnd_copyArm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_copyArm

/-- info: 'LeanLLVM.Vellum.ifEnd_zeroArm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_zeroArm


/-! ### The frame the middle's blocks carry

The iteration's middle — the latch, the position block, `if.end`, one of its two
arms, the copy and the tail — copies bytes and writes only its own counters.  Every
cell the blocks *after* it read therefore survives an iteration unchanged, but the
copy loop's exit word names only the counters it writes, and its exit environment is
opaque: a consumer holding the exit state alone cannot recover a cell the word does
not name.  `CellFrame` is that frame, carried as one conjunct rather than as a list
of cells the loop would have to enumerate, and the persistence lemmas are what a
loop instance needs to keep it: the copy's body block and the tail's two blocks
prepend only their own names, so the frame passes over them.

Three of the cells are the successor latch's rather than the run's own: `%nxp`, the
list's length the next `DecodeLatch` names; `%add`, the window's end offset the
position block reads and the staging names; and `%inc11`, the position index, which
`if.end` rewrites once per iteration and which the next latch's test reads.  Carrying
them in the frame is what lets an iteration's result be the next iteration's
premisses without re-reading the middle's blocks.

`ExpandStaging.latch_tail` is the same transfer for the record's trailing thirty-two
bytes, which `if.end`'s copy arm reads past the body.  The two arithmetic facts are
`if.end`'s own `%sub = %conv8 - %pos0` and `%inc11 = %k.1296 + 1`, at the values the
phi supplies from the position the block loaded.  `dest_cover` is the destination
read the escape's store extends — the decoded prefix at `%dst` and the bytes the copy
moved after it — and `srcBlen`/`srcBtake` are the source list's length and the cut
the copy's residual makes of it. -/

structure CellFrame (env : Env) (pb xp tab err xj dst : Nat) (pos0v n jv : BitVec 64)
    (nxpv addv incv : BitVec 64) : Prop where
  pcell : lookupName env "%p" = some (.ptr pb)
  xpcell : lookupName env "%xp" = some (.ptr xp)
  tabcell : lookupName env "%tab" = some (.ptr tab)
  errcell : lookupName env "%err" = some (.ptr err)
  xjcell : lookupName env "%xj" = some (.ptr xj)
  dstcell : lookupName env "%dst" = some (.ptr dst)
  pos0cell : lookupName env "%pos0" = some (.int 64 pos0v)
  ncell : lookupName env "%n" = some (.int 64 n)
  jcell : lookupName env "%j.0294" = some (.int 64 jv)
  /-- The list's length as the caller's `%nxp` slot carries it.  The successor
  latch's `DecodeLatch` reads it, and no block of an iteration writes it. -/
  nxpcell : lookupName env "%nxp" = some (.int 64 nxpv)
  /-- The window's end offset `%add = %pos0 + %n`, which the position block reads
  and the staging names. -/
  addcell : lookupName env "%add" = some (.int 64 addv)
  /-- The position index the next latch's test reads.  `if.end` writes it once per
  iteration, so it is part of the frame from that block on. -/
  incell : lookupName env "%inc11" = some (.int 64 incv)

/-- The frame passes the copy's body block, which prepends only its own names. -/
theorem CellFrame.copyBodyEnv (env : Env) (src dst : Nat) (k : BitVec 64)
    (bs1 bs2 : List UInt8) (subv : BitVec 64) {pb xp tab err xj dst0 : Nat}
    {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udCopyBodyEnv env src dst k bs1 bs2 subv) pb xp tab err xj dst0 pos0v n jv
      nxpv addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udCopyBodyEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `us_run_long.exit99`. -/
theorem CellFrame.tailEnv (env : Env) (src dst : Nat) (k : BitVec 64)
    (bs1 : List UInt8) (sub13 : BitVec 64) {pb xp tab err xj dst0 : Nat}
    {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udCopyTailEnv env src dst k bs1 sub13) pb xp tab err xj dst0 pos0v n jv
      nxpv addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udCopyTailEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.then.i104`. -/
theorem CellFrame.tailIfEnv (env : Env) (src dst : Nat) (k : BitVec 64)
    (bs2 : List UInt8) {pb xp tab err xj dst0 : Nat}
    {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udCopyTailIfEnv env src dst k bs2) pb xp tab err xj dst0 pos0v n jv
      nxpv addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udCopyTailIfEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `us_run.exit`, whose builder prepends the two operand cells and
the loaded byte. -/
theorem CellFrame.runExitEnv (env : Env) (paddr : Nat) (sub13v subv j : BitVec 64)
    (b : BitVec 8) {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udRunExitEnvS env paddr sub13v subv j b) pb xp tab err xj dst0 pos0v n jv
      nxpv addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udRunExitEnvS] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end21`. -/
theorem CellFrame.ifEnd21Env (env : Env) (subv nv : BitVec 64) {pb xp tab err xj dst0 : Nat}
    {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfEnd21Env env subv nv) pb xp tab err xj dst0 pos0v n jv nxpv addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEnd21Env] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end.i`. -/
theorem CellFrame.ifEndIEnv (env : Env) (paddr tab : Nat) (off : BitVec 64)
    (b t : BitVec 8) {pb xp err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfEndIEnv env paddr tab off b t) pb xp tab err xj dst0 pos0v n jv nxpv
      addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEndIEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.then6.i`. -/
theorem CellFrame.ifThen6IEnv (env : Env) (daddr : Nat) (out : BitVec 64)
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfThen6IEnv env daddr out) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfThen6IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end9.i`. -/
theorem CellFrame.ifEnd9IEnv (env : Env) (off : BitVec 64) (c1 c2 : BitVec 1)
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfEnd9IEnv env off c1 c2) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEnd9IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end.i115`. -/
theorem CellFrame.ifEndI115Env (env : Env) (addr : Nat) (bs : List UInt8)
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfEndI115Env env addr bs) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEndI115Env] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end3.i`. -/
theorem CellFrame.ifEnd3IEnv (env : Env) (bs : List UInt8) (c : List (BitVec 1))
    (sub n : BitVec 64) {pb xp tab err xj dst0 : Nat}
    {pos0v n0 jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n0 jv nxpv addv incv) :
    CellFrame (udIfEnd3IEnv env bs c sub n) pb xp tab err xj dst0 pos0v n0 jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEnd3IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.then17.i`. -/
theorem CellFrame.ifThen17IEnv (env : Env) (addr : Nat) (bs : List UInt8)
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfThen17IEnv env addr bs) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfThen17IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `land.lhs.true22.i`. -/
theorem CellFrame.landLhsTrue22IEnv (env : Env) (bs : List UInt8) (cl : List (BitVec 1))
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udLandLhsTrue22IEnv env bs cl) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udLandLhsTrue22IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.then26.i`. -/
theorem CellFrame.ifThen26IEnv (env : Env) (cp s23 : BitVec 32)
    {pb xp tab err xj dst0 : Nat} {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfThen26IEnv env cp s23) pb xp tab err xj dst0 pos0v n jv nxpv addv
      incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfThen26IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

/-- The frame passes `if.end32.i`. -/
theorem CellFrame.ifEnd32IEnv (env : Env) (cp : BitVec 32) (adv x : BitVec 64)
    (dsta k : Nat) {pb xp tab err xj dst0 : Nat}
    {pos0v n jv nxpv addv incv : BitVec 64}
    (h : CellFrame env pb xp tab err xj dst0 pos0v n jv nxpv addv incv) :
    CellFrame (udIfEnd32IEnv env cp adv x dsta k) pb xp tab err xj dst0 pos0v n jv nxpv
      addv incv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [udIfEnd32IEnv] <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]
  all_goals first
    | exact h.pcell | exact h.xpcell | exact h.tabcell | exact h.errcell
    | exact h.xjcell | exact h.dstcell | exact h.pos0cell | exact h.ncell
    | exact h.jcell | exact h.nxpcell | exact h.addcell | exact h.incell

theorem bv64_eq_ofNat_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 64) :
    x = BitVec.ofNat 64 x.toNat := by
  refine BitVec.toNat_inj.1 ?_
  rw [ofNat64_toNat h]

theorem ExpandStaging.latch_tail
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (h : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    {s : State} (hframe : UnchangedOutside mem s.mem [(dst, n + 64)]) :
    ∃ extra : List UInt8, readBytes s.mem (b + n) 32 = some extra ∧ extra.length = 32 := by
  obtain ⟨hpre, hargs, -, -, hpos0n, -, -, -, hspB, -, -⟩ := h
  obtain ⟨b', n', dst', err', xp', xj', nps', pos0', tab', body', ps', err0', k0',
    hargs', hbody', -, -, -, -, hwidth', -, -, -, htab, htail, -, -, -, -, -, -, -⟩ := hpre
  obtain ⟨hb', hdst', -, -, -, -⟩ := staging_ptr_slots hargs hargs'
  have hnlt : n < 2 ^ 64 := by omega
  have hn'lt : n' < 2 ^ 64 := by omega
  have hn' : n' = n := (staging_len_eq hargs hargs' hnlt hn'lt).symm
  rw [hb', hn'] at htail
  obtain ⟨extra, hextra⟩ := htail
  have hextraS : readBytes s.mem (b + n) 32 = some extra :=
    (readBytes_of_UnchangedOutside hframe (fun x hx1 hx2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rcases hspB with hle | hle
      · omega
      · omega)).trans hextra
  exact ⟨extra, hextraS, JsonEntrySteps.readBytes_length s.mem (b + n) 32 hextraS⟩

theorem ifEnd_env_sub_eq {pos0 q : Nat} (hq : pos0 + q < 2 ^ 64) :
    BitVec.ofNat 64 (pos0 + q) - BitVec.ofNat 64 pos0 = BitVec.ofNat 64 q := by
  rw [ofNat_sub_ofNat (by omega) hq, Nat.add_sub_cancel_left]

theorem ifEnd_env_inc_eq (c : Nat) :
    BitVec.ofNat 64 c + BitVec.ofInt 64 1 = BitVec.ofNat 64 (c + 1) := by
  rw [show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from BitVec.ofInt_ofNat 64 1,
    ← BitVec.ofNat_add]

/-- A list's prefix at one cut and its next chunk concatenate into the longer
prefix: this is how the tail's second write extends the copy's own read-back. -/
theorem take_append_drop_take {α : Type} (B : List α) (k n : Nat) :
    B.take k ++ (B.drop k).take n = B.take (k + n) := by
  induction B generalizing k with
  | nil => simp
  | cons b rest ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [List.take_succ_cons, List.drop_succ_cons, List.cons_append, ih k,
            show k + 1 + n = (k + n) + 1 from by omega, List.take_succ_cons]

/-- The escape's byte read, from the body's range read. -/
theorem byte_read_of_body {M : Mem} {b n q : Nat} {body : List UInt8}
    (hbody : readBytes M b n = some body) (hq : q < n) :
    readBytes M (b + q) 1 = some (natToBytes (body.getD q 0).toNat 1) := by
  have hblen : body.length = n := JsonEntrySteps.readBytes_length M b n hbody
  exact readBytes_one_getD hbody (by omega)

/-- The byte's index names the body's own element. -/
theorem body_getElem?_getD {body : List UInt8} {q : Nat} (h : q < body.length) :
    body[q]? = some (body.getD q 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
/-- **The destination cover**: the decoded prefix plus the bytes the escape test is
about to read, both at the state's own memory. -/
theorem dest_cover {M : Mem} {dst : Nat} {out copy : List UInt8}
    (hpref : readBytes M dst out.length = some out)
    (hcopy : readBytes M (dst + out.length) copy.length = some copy) :
    readBytes M dst (out ++ copy).length = some (out ++ copy) := by
  rw [List.length_append]
  exact JsonEntrySteps.readBytes_append M out.length dst out copy.length copy hpref hcopy

/-- The copy's destination cover's list length. -/
theorem srcBlen {body extra : List UInt8} {i n q : Nat} (hblen : body.length = n)
    (hextra : extra.length = 32) (hiq : i ≤ q) (hqn : q < n) :
    ((body.drop i ++ extra).take ((q - i) + 32)).length = (q - i) + 32 := by
  have h : (q - i) + 32 ≤ (body.drop i ++ extra).length := by
    rw [List.length_append, List.length_drop, hblen, hextra]
    omega
  rw [List.length_take, Nat.min_eq_left h]

theorem srcBtake {body extra : List UInt8} {i n q : Nat} (hblen : body.length = n)
    (hiq : i ≤ q) (hqn : q < n) :
    ((body.drop i ++ extra).take ((q - i) + 32)).take (q - i) = (body.drop i).take (q - i) :=
  take_take_source hblen (by omega)

/-! ### The tail's two blocks, composed at the exit's own operands

`if.end`'s two arms both leave the run at `us_run_long.exit99`, and they leave
*different* values in the block's two `phi`s: the copy's next counter and its
residual on the copy edge, the zero constant and `%sub13` on `if.end`'s.  The tail
therefore takes its two operands as parameters — `k` and `sub13` — and each arm
instantiates them, which is why this is one lemma at the block rather than one per
edge.  `udCopyTail_run_zero`/`_one` are the two steps; what this adds is the state
they leave read as the cells the next block reads: the caller's prefix, the frame
over the destination extent, and the register frame (`CellFrame` plus `%sub`,
`%inc11` and `%sub13`, which the tail's environment builders prepend nothing to).

**The destination's read at the gap's length.**  The tail's writes complete the
copy: `us_run_long.exit99` always moves thirty-two bytes, and `if.then.i104` moves
thirty-two more when the residual asked for it, so after the tail the destination
holds the whole gap and not only the decoded prefix.  The lemma states that read at
`q - i`, which is what the escape's store extends.  Its `sub13.toNat ≤ 64`
hypothesis is the copy loop's exit bound (`copyIterBound_exit`), not a promise
beside the caller's: the residual the loop leaves is at most one block.

**Carrier.**  The footprint is `[propext, Classical.choice, Quot.sound]`; the choice
enters through the two blocks' `%add.ptr` steps at `hkw`, which is
`BitVec.signExtend_eq` — the carrier the copy's own steps already name. -/
theorem copyTail_to_usRunExit
    {mem : Mem} {body extra B out : List UInt8} {b dst n i q pos0 : Nat}
    {s : State} {prev : String} (opk ops : Operand) (k sub13 : BitVec 64)
    {pb xp tab err xj : Nat} {incv nxpv addv : BitVec 64}
    (hblen : body.length = n) (hBlen : B.length = (q - i) + 32)
    (hpc : s.pc = "us_run_long.exit99") (hprev : s.pre = some prev)
    (hinck : phiIncoming prev udCopyTailIncomingK = some opk)
    (hopk : evalOperand (withEnv s.env s) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i86.lcssa", .int 64 k) :: s.env) s) ops =
      some (.int 64 sub13))
    (hsrcb : lookupName s.env "%add.ptr" = some (.ptr (b + i)))
    (hdstb : lookupName s.env "%add.ptr12" = some (.ptr (dst + out.length)))
    (hkN : k.toNat ≤ q - i) (hk63 : k.toNat < 2 ^ 63)
    (hsubN : sub13.toNat = (q - i) - k.toNat) (hres64 : sub13.toNat ≤ 64)
    (hpref : readBytes s.mem dst out.length = some out)
    (hdstread : readBytes s.mem (dst + out.length) k.toNat = some (List.take k.toNat B))
    (hsrcfull : readBytes s.mem (b + i) ((q - i) + 32) = some B)
    (hcf : CellFrame s.env pb xp tab err xj dst (BitVec.ofNat 64 pos0)
      (BitVec.ofNat 64 n) (BitVec.ofNat 64 out.length) nxpv addv incv)
    (hsubc : lookupName s.env "%sub" = some (.int 64 (BitVec.ofNat 64 q)))
    (hincell : lookupName s.env "%inc11" = some (.int 64 incv))
    (hsub13c : lookupName s.env "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i))))
    (hframe : UnchangedOutside mem s.mem [(dst, n + 64)])
    (hdisj : copyDisjoint (b + i) (dst + out.length) (q - i))
    (houtle : out.length ≤ i) (hiq : i ≤ q) (hqn : q < n) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = "us_run.exit" ∧
      readBytes e.mem dst out.length = some out ∧
      UnchangedOutside mem e.mem [(dst, n + 64)] ∧
      CellFrame e.env pb xp tab err xj dst (BitVec.ofNat 64 pos0)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 out.length) nxpv addv incv ∧
      lookupName e.env "%sub" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lookupName e.env "%inc11" = some (.int 64 incv) ∧
      lookupName e.env "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i))) ∧
      (∀ k', runFuel escapeCalls (j + k') usDecFunction s =
        runFuel escapeCalls k' usDecFunction e) ∧
      readBytes e.mem (dst + out.length) (q - i) = some (List.take (q - i) B) := by
  let bs1 : List UInt8 := (B.drop k.toNat).take 32
  have href1 : readBytes s.mem (b + i + k.toNat) 32 = some bs1 :=
    copySrc_read hsrcfull hkN
  have hlen1 : bs1.length = 32 := by
    refine copyChunk_length ?_
    rw [hBlen]; omega
  have hkw : (k.signExtend 64).toNat = k.toNat := signExtend_self_toNat k
  have hdstk : out.length + k.toNat ≤ n := by omega
  -- the first write lies inside the destination extent, so the frame passes it
  have hinside : UnchangedOutside mem
      (writeBytes s.mem (dst + out.length + k.toNat) bs1) [(dst, n + 64)] :=
    UnchangedOutside.writeBytes_inside hframe (by omega) (by omega)
  by_cases hgt : 32 < sub13.toNat
  · -- the residual reaches the second block: two steps to `us_run.exit`
    let bs2 : List UInt8 := (B.drop (k.toNat + 32)).take 32
    have hk32 : k.toNat + 32 ≤ q - i := by omega
    have hlen2 : bs2.length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hfr : (b + i + k.toNat + 32) + 32 ≤ dst + out.length + k.toNat ∨
        (dst + out.length + k.toNat) + bs1.length ≤ b + i + k.toNat + 32 := by
      rw [hlen1]
      rcases hdisj with hd | hd
      · right; omega
      · left; omega
    have hr2 : readBytes (writeBytes s.mem (dst + out.length + k.toNat) bs1)
        (b + i + k.toNat + 32) 32 = some bs2 := by
      rw [JsonEntrySteps.readBytes_writeBytes_frame _ _ _ _ _ hfr]
      exact copySrc_read_mid (B := B) hsrcfull hk32
    have hcond : evalICmp .ugt sub13 (BitVec.ofInt 64 32) = (1 : BitVec 1) :=
      (evalICmp_ugt_one_iff_toNat _ _).2 (by
        rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide]; exact hgt)
    let mF : Mem := udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2
    let Fin : State :=
      { (withEnv (udCopyTailIfEnv
          (udCopyTailEnv s.env (b + i) (dst + out.length) k bs1 sub13)
          (b + i) (dst + out.length) k bs2) { s with mem := mF }) with
          pc := "us_run.exit", pre := some "if.then.i104" }
    have hrun := udCopyTail_run_one s.env s prev opk ops (b + i) (dst + out.length) k
      bs1 bs2 sub13 hpc hprev hinck hopk hincs hops hsrcb hdstb hk63 hkw href1 hlen1
      hr2 hlen2 hcond
    refine ⟨Fin, 2, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun k' => hrun k', ?_⟩
    · show readBytes (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2)
        dst out.length = some out
      simp only [udCopy2Mem]
      rw [readBytes_writeBytes_below _ _ _ _ _ (by omega)]
      rw [readBytes_writeBytes_below _ _ _ _ _ (by omega)]
      exact hpref
    · show UnchangedOutside mem
        (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2) [(dst, n + 64)]
      simp only [udCopy2Mem]
      exact UnchangedOutside.writeBytes_inside hinside (by omega) (by omega)
    · exact CellFrame.tailIfEnv _ _ _ _ _ (CellFrame.tailEnv s.env (b + i)
        (dst + out.length) k bs1 sub13 hcf)
    · show lookupName (udCopyTailIfEnv (udCopyTailEnv s.env (b + i) (dst + out.length) k
        bs1 sub13) (b + i) (dst + out.length) k bs2) "%sub" =
        some (.int 64 (BitVec.ofNat 64 q))
      simp only [udCopyTailIfEnv, udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hsubc
    · show lookupName (udCopyTailIfEnv (udCopyTailEnv s.env (b + i) (dst + out.length) k
        bs1 sub13) (b + i) (dst + out.length) k bs2) "%inc11" = some (.int 64 incv)
      simp only [udCopyTailIfEnv, udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hincell
    · show lookupName (udCopyTailIfEnv (udCopyTailEnv s.env (b + i) (dst + out.length) k
        bs1 sub13) (b + i) (dst + out.length) k bs2) "%sub13" =
        some (.int 64 (BitVec.ofNat 64 (q - i)))
      simp only [udCopyTailIfEnv, udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hsub13c
    · have hres : (q - i) - k.toNat ≤ 64 := by
        have h := hres64; rw [hsubN] at h; exact h
      have hle64 : q - i ≤ k.toNat + 64 := by omega
      show readBytes (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2)
        (dst + out.length) (q - i) = some (List.take (q - i) B)
      have hbelow : readBytes (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2)
          (dst + out.length) k.toNat = some (List.take k.toNat B) := by
        simp only [udCopy2Mem]
        rw [readBytes_writeBytes_below _ bs2 k.toNat (dst + out.length)
          (dst + out.length + k.toNat + 32) (by omega)]
        rw [readBytes_writeBytes_below _ bs1 k.toNat (dst + out.length)
          (dst + out.length + k.toNat) (by omega)]
        exact hdstread
      have hsame1 : readBytes (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2)
          (dst + out.length + k.toNat) 32 = some bs1 := by
        simp only [udCopy2Mem]
        rw [readBytes_writeBytes_below _ bs2 32 (dst + out.length + k.toNat)
          (dst + out.length + k.toNat + 32) (by omega)]
        have h := readBytes_writeBytes_same s.mem bs1
          (addr := dst + out.length + k.toNat)
        rwa [hlen1] at h
      have hsame2 : readBytes (udCopy2Mem s.mem (dst + out.length + k.toNat) bs1 bs2)
          (dst + out.length + k.toNat + 32) 32 = some bs2 := by
        simp only [udCopy2Mem]
        have h := readBytes_writeBytes_same
          (writeBytes s.mem (dst + out.length + k.toNat) bs1) bs2
          (addr := dst + out.length + k.toNat + 32)
        rwa [hlen2] at h
      have hcat1 := JsonEntrySteps.readBytes_append _ k.toNat (dst + out.length)
        _ 32 bs1 hbelow hsame1
      have hcat2 := JsonEntrySteps.readBytes_append _ (k.toNat + 32)
        (dst + out.length) _ 32 bs2 hcat1 hsame2
      rw [show k.toNat + 32 + 32 = k.toNat + 64 from by omega] at hcat2
      rw [show List.take k.toNat B ++ bs1 ++ bs2 = List.take (k.toNat + 64) B from by
        rw [show bs1 = (B.drop k.toNat).take 32 from rfl,
          show bs2 = (B.drop (k.toNat + 32)).take 32 from rfl,
          take_append_drop_take B k.toNat 32,
          take_append_drop_take B (k.toNat + 32) 32,
          show k.toNat + 32 + 32 = k.toNat + 64 from by omega]] at hcat2
      obtain ⟨hpref', -⟩ := readBytes_split _ (dst + out.length) (q - i)
        (k.toNat + 64 - (q - i))
        (by rw [show q - i + (k.toNat + 64 - (q - i)) = k.toNat + 64 from by omega]
            exact hcat2)
      rwa [List.take_take, Nat.min_eq_left hle64] at hpref'
  · -- the residual fits: one step to `us_run.exit`
    have hcond : evalICmp .ugt sub13 (BitVec.ofInt 64 32) = (0 : BitVec 1) :=
      (evalICmp_ugt_zero_iff _ _).2 (by
        rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide]; omega)
    let mO : Mem := writeBytes s.mem (dst + out.length + k.toNat) bs1
    let One : State :=
      { (withEnv (udCopyTailEnv s.env (b + i) (dst + out.length) k bs1 sub13)
          { s with mem := mO }) with
          pc := "us_run.exit", pre := some "us_run_long.exit99" }
    have hrun := udCopyTail_run_zero s.env s prev opk ops (b + i) (dst + out.length) k
      bs1 sub13 hpc hprev hinck hopk hincs hops hsrcb hdstb hk63 hkw href1 hlen1 hcond
    refine ⟨One, 1, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun k' => hrun k', ?_⟩
    · show readBytes (writeBytes s.mem (dst + out.length + k.toNat) bs1)
        dst out.length = some out
      rw [readBytes_writeBytes_below _ _ _ _ _ (by omega)]
      exact hpref
    · show UnchangedOutside mem
        (writeBytes s.mem (dst + out.length + k.toNat) bs1) [(dst, n + 64)]
      exact hinside
    · exact CellFrame.tailEnv s.env (b + i) (dst + out.length) k bs1 sub13 hcf
    · show lookupName (udCopyTailEnv s.env (b + i) (dst + out.length) k bs1 sub13)
        "%sub" = some (.int 64 (BitVec.ofNat 64 q))
      simp only [udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hsubc
    · show lookupName (udCopyTailEnv s.env (b + i) (dst + out.length) k bs1 sub13)
        "%inc11" = some (.int 64 incv)
      simp only [udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hincell
    · show lookupName (udCopyTailEnv s.env (b + i) (dst + out.length) k bs1 sub13)
        "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i)))
      simp only [udCopyTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hsub13c
    · have hle32 : q - i ≤ k.toNat + 32 := by
        have h : sub13.toNat ≤ 32 := by omega
        rw [hsubN] at h
        omega
      show readBytes (writeBytes s.mem (dst + out.length + k.toNat) bs1)
        (dst + out.length) (q - i) = some (List.take (q - i) B)
      have hbelow : readBytes (writeBytes s.mem (dst + out.length + k.toNat) bs1)
          (dst + out.length) k.toNat = some (List.take k.toNat B) := by
        rw [readBytes_writeBytes_below _ bs1 k.toNat (dst + out.length)
          (dst + out.length + k.toNat) (by omega)]
        exact hdstread
      have hsame1 : readBytes (writeBytes s.mem (dst + out.length + k.toNat) bs1)
          (dst + out.length + k.toNat) 32 = some bs1 := by
        have h := readBytes_writeBytes_same s.mem bs1
          (addr := dst + out.length + k.toNat)
        rwa [hlen1] at h
      have hcat1 := JsonEntrySteps.readBytes_append _ k.toNat (dst + out.length)
        _ 32 bs1 hbelow hsame1
      rw [show List.take k.toNat B ++ bs1 = List.take (k.toNat + 32) B from by
        rw [show bs1 = (B.drop k.toNat).take 32 from rfl]
        exact take_append_drop_take B k.toNat 32] at hcat1
      obtain ⟨hpref', -⟩ := readBytes_split _ (dst + out.length) (q - i)
        (k.toNat + 32 - (q - i))
        (by rw [show q - i + (k.toNat + 32 - (q - i)) = k.toNat + 32 from by omega]
            exact hcat1)
      rwa [List.take_take, Nat.min_eq_left hle32] at hpref'

/-- info: 'LeanLLVM.Vellum.copyTail_to_usRunExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyTail_to_usRunExit

/-! ### The middle: the latch to `us_run.exit`

The iteration arm and the refusal arm share their first half: the latch's two
blocks (`latch_to_ifEnd`), one of `if.end`'s arms, and the tail.  This is that half
composed once, ending at the block the two continuations start from:
`us_run.exit`'s own step (`udRunExit_stepS_zero`) reads `%sub13`, `%j.0294`, `%p`
and `%sub` and the body's byte at the head, and `if.end21`'s refusal arm reads
`%sub`, `%n`, `%inc11`, `%err` and `%xj` — all of them stated here, at the values
the blocks compute.

**The two arms leave different operands at the same block.**  `if.end`'s copy edge
supplies the copy's residual and its next counter, its zero edge the constant and
`%sub13`; the tail's `phi`s read them, which is why the tail is instantiated twice
rather than given one value.  The fuel bound is the copy arm's, and it bounds both:
the zero edge's single control step is less than the copy's.

The destination prefix read and the frame are carried because the exit word the
records compare is about the caller's memory, not the state's.

**What the iteration's continuation reads.**  Besides the exit state's cells, the
result carries the decoded prefix and the whole gap as one destination read, the
walk's invariant at that memory, the list's length cell `%nxp` and the window's end
offset `%add`.  Those are the cells the successor latch's `DecodeLatch` and
`StagedLatchInv` name, and the read is the one the emitter's store extends; stated
here they are read off the middle's blocks once rather than re-derived by every
consumer of the run.

**Carrier.**  The footprint is `[propext, Classical.choice, Quot.sound]`: the two
`if.end` arms and `latch_to_ifEnd` carry it, through the copy's `%add.ptr` steps at
`BitVec.signExtend_eq`. -/
theorem latch_to_runExit
    {args : List Value} {mem : Mem} {next : Nat}
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b xp tab : Nat} {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    {r c : Nat} {s : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem (r + 1) c s)
    (hnle : ¬ nps ≤ c) :
    ∃ (e : State) (i q : Nat) (out : List UInt8) (inc11 adv : BitVec 64) (j : Nat),
      j ≤ 2 + (copyIterBound (q - i) + 2) + 2 ∧
      e.pc = "us_run.exit" ∧ (escAt body st 0)[c]? = some q ∧ i ≤ q ∧ q < n ∧
      readBytes e.mem (b + q) 1 = some (natToBytes (body.getD q 0).toNat 1) ∧
      body[q]? = some (body.getD q 0) ∧
      lookupName e.env "%sub" = some (.int 64 (BitVec.ofNat 64 q)) ∧
      lookupName e.env "%sub13" = some (.int 64 (BitVec.ofNat 64 (q - i))) ∧
      lookupName e.env "%j.0294" = some (.int 64 (BitVec.ofNat 64 out.length)) ∧
      lookupName e.env "%p" = some (.ptr b) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      lookupName e.env "%inc11" =
        some (.int 64 (decodeNextIdx inc11 adv + BitVec.ofInt 64 1)) ∧
      lookupName e.env "%err" = some (.ptr err) ∧
      lookupName e.env "%xj" = some (.ptr xj) ∧
      lookupName e.env "%tab" = some (.ptr tab) ∧
      lookupName e.env "%xp" = some (.ptr xp) ∧
      lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName e.env "%dst" = some (.ptr dst) ∧
      UnchangedOutside mem e.mem [(dst, n + 64)] ∧
      readBytes e.mem dst out.length = some out ∧
      (decodeNextIdx inc11 adv).toNat = c ∧
      (∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e) ∧
      readBytes e.mem dst (out ++ (body.drop i).take (q - i)).length =
        some (out ++ (body.drop i).take (q - i)) ∧
      DecodeInv body st e.mem dst nps i c out goal ∧
      lookupName e.env "%nxp" = some (.int 64 (BitVec.ofNat 64 nps)) ∧
      (∃ addv : BitVec 64, lookupName e.env "%add" = some (.int 64 addv) ∧
        addv.toNat = pos0 + n) := by
  -- the record's clauses, at the caller's binders
  have hstg := hstaging
  obtain ⟨-, -, -, hbodyS, hpos0n, -, -, -, hdisjB, -, -⟩ := hstg
  have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbodyS
  -- the latch's two blocks
  obtain ⟨e2, i, q, out, sub, adv, inc11, nxp, jv, v, addv,
    hpc2, hpre2, hmem2, hq, hiq, hadvsub, hk2, hi5, hj4, hconv, hvpos, hsub2,
    hinc112, hnxp2, hp2, hdst2, hpos02, hn2, hxp2, htab2, herr2, hxj2, hadd2,
    haddnat, hjv, hprefix2, houtle, hwalk2, hnxpnat, hkidx, hrun2⟩ :=
    latch_to_ifEnd hstaging h hnle
  have hqbody : q < body.length := (mem_escAt.mp (List.mem_of_getElem? hq)).2.1
  have hqn : q < n := by rw [← hblen]; exact hqbody
  -- the frame at the latch, and the reads the arms take
  have hframe0 := assemblyLatchInv_frame h
  have hframe2 : UnchangedOutside mem e2.mem [(dst, n + 64)] := by
    rw [hmem2]; exact hframe0
  obtain ⟨hbodyL, -⟩ := ExpandStaging.latch_reads hstaging hframe0
  obtain ⟨extra, hextraL, hextralen⟩ := ExpandStaging.latch_tail hstaging hframe0
  have hbodyE2 : readBytes e2.mem b n = some body := by rw [hmem2]; exact hbodyL
  have hextraE2 : readBytes e2.mem (b + n) 32 = some extra := by rw [hmem2]; exact hextraL
  have hextraOut : ∀ x, b + n ≤ x → x < b + n + 32 →
      ∀ r ∈ [(dst, n + 64)], ¬ (r.1 ≤ x ∧ x < r.1 + r.2) := by
    intro x hx1 hx2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rcases hdisjB with hd | hd <;> omega
  have hextraMem : readBytes mem (b + n) 32 = some extra := by
    rw [← readBytes_of_UnchangedOutside hframe0 hextraOut]
    exact hextraL
  have hprefixE2 : readBytes e2.mem dst out.length = some out := hwalk2.stored
  have hsubv : adv + sub = BitVec.ofNat 64 i := by
    rw [bv64_eq_ofNat_toNat (x := adv + sub) (by omega), hadvsub]
  have hi5' : lookupName e2.env "%i.0295" = some (.int 64 (BitVec.ofNat 64 i)) := by
    rw [hi5, hsubv]
  have hc8' : lookupName e2.env "%conv8" =
      some (.int 64 (BitVec.ofNat 64 (pos0 + q))) := by
    rw [hconv, hvpos]
  have hjcell : jv = BitVec.ofNat 64 out.length := by
    rw [bv64_eq_ofNat_toNat (x := jv) (by omega), hjv]
  have hjcell2 : lookupName e2.env "%j.0294" =
      some (.int 64 (BitVec.ofNat 64 out.length)) := by
    rw [hj4, hjcell]
  -- the register frame the copy's exit word does not name
  let Cells : Env → Prop := fun env =>
    CellFrame env b xp tab err xj dst (BitVec.ofNat 64 pos0) (BitVec.ofNat 64 n)
      (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 nps) addv
      (decodeNextIdx inc11 adv + BitVec.ofInt 64 1) ∧
    lookupName env "%sub" = some (.int 64 (BitVec.ofNat 64 q)) ∧
    lookupName env "%inc11" =
      some (.int 64 (decodeNextIdx inc11 adv + BitVec.ofInt 64 1))
  have hCellsC : ∀ (env : Env) (src dst' : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64), Cells env → Cells (udCopyBodyEnv env src dst' k bs1 bs2 subv) := by
    intro env src dst' k bs1 bs2 subv hc
    obtain ⟨hcf, hsubc, hincc⟩ := hc
    refine ⟨CellFrame.copyBodyEnv env src dst' k bs1 bs2 subv hcf, ?_, ?_⟩
    · simp only [udCopyBodyEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hsubc
    · simp only [udCopyBodyEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hincc
  have hcells3 : Cells (udIfEndEnv e2.env b dst (decodeNextIdx inc11 adv)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (pos0 + q))
      (BitVec.ofNat 64 pos0)) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [udIfEndEnv]; ud_lk_h hp2
    · simp only [udIfEndEnv]; ud_lk_h hxp2
    · simp only [udIfEndEnv]; ud_lk_h htab2
    · simp only [udIfEndEnv]; ud_lk_h herr2
    · simp only [udIfEndEnv]; ud_lk_h hxj2
    · simp only [udIfEndEnv]; ud_lk_h hdst2
    · simp only [udIfEndEnv]; ud_lk_h hpos02
    · simp only [udIfEndEnv]; ud_lk_h hn2
    · simp only [udIfEndEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [hj4, hjcell]
    · simp only [udIfEndEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [hnxp2, bv64_eq_ofNat_toNat (x := nxp) (by omega), hnxpnat]
    · simp only [udIfEndEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hadd2
    · simp only [udIfEndEnv]
      ud_lk
    · simp only [udIfEndEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rw [ifEnd_env_sub_eq (by omega)]
      rw [lookupName_cons_self]
    · simp only [udIfEndEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rfl
  -- the copy's disjointness is the record's, at the copy's own bases
  have hdisjC : copyDisjoint (b + i) (dst + out.length) (q - i) := by
    unfold copyDisjoint
    omega
  -- the body's range is outside the destination extent, so the frame carries reads
  have houtside : ∀ x, b + i ≤ x → x < b + i + ((q - i) + 32) →
      ∀ r ∈ [(dst, n + 64)], ¬ (r.1 ≤ x ∧ x < r.1 + r.2) := by
    intro x hx1 hx2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rcases hdisjB with hd | hd <;> omega
  have hbyteOut : ∀ x, b + q ≤ x → x < b + q + 1 →
      ∀ r ∈ [(dst, n + 64)], ¬ (r.1 ≤ x ∧ x < r.1 + r.2) := by
    intro x hx1 hx2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rcases hdisjB with hd | hd <;> omega
  -- the source range from the cursor, at the caller's own memory
  have hsrcfullMem : readBytes mem (b + i) ((q - i) + 32) =
      some ((body.drop i ++ extra).take ((q - i) + 32)) := by
    have hin : i ≤ n := Nat.le_trans hiq (Nat.le_of_lt hqn)
    have hfull := (finalSource_read (i := i) hbodyS hin hextraMem).1
    exact source_read_slice hblen hfull (Nat.le_refl i) (by omega) (by omega)
  by_cases hgt : 64 < q - i
  · -- the copy arm
    obtain ⟨eL, jL, hjL, hcw, hprefL, hfrL, hpL, hdL, hjcellL, hcellsL, hrunL⟩ :=
      ifEnd_copyArm (q := q) (extra := extra) hpc2 hpre2 hwalk2 hiq hqn hpos0n hdisjB
        hframe2 hbodyE2 hextraE2 hk2 hc8' hpos02 hp2 hi5' hdst2 hjcell2 hgt Cells
        hCellsC hcells3
    obtain ⟨hpcLw, hpreLw, hknext, hsnext, hsrcbL, hdstbL, hsubcL, hdstreadL,
      hsrcfullL⟩ := hcw
    have hBlen : ((body.drop i ++ extra).take ((q - i) + 32)).length = (q - i) + 32 :=
      srcBlen hblen hextralen hiq hqn
    have hkNat : (BitVec.ofNat 64 (64 * copyIterBound (q - i) + 64)).toNat =
        64 * copyIterBound (q - i) + 64 :=
      ofNat64_toNat (by have := copyIterBound_mul_le (sub := q - i); omega)
    -- the copy's exit counter is at or below the residual: `q - i ≥ 128` puts the
    -- loop's ceiling below `q - i - 64`, and below it the residual is under 128
    have hkexit : 64 * copyIterBound (q - i) + 64 ≤ q - i := by
      have hle : 64 * copyIterBound (q - i) ≤ q - i - 64 := by
        rw [copyIterBound]
        rcases Nat.lt_or_ge (q - i) 128 with hlt | hge
        · have hz : q - i - 128 = 0 := by omega
          rw [hz]
          simp
        · have hd : q - i - 128 + 63 = q - i - 65 := by omega
          rw [hd]
          have := Nat.div_mul_le_self (q - i - 65) 64
          omega
      omega
    have hsubNat : (BitVec.ofNat 64
        ((q - i) - (64 * copyIterBound (q - i) + 64))).toNat =
        (q - i) - (64 * copyIterBound (q - i) + 64) :=
      ofNat64_toNat (by have := copyIterBound_mul_le (sub := q - i); omega)
    obtain ⟨eT, jT, hjT, hpcT, hprefT, hfrT, hcfT, hsubT, hincT, hsub13T, hrunT,
      hcovT⟩ :=
      copyTail_to_usRunExit (mem := mem) (extra := extra)
        (.reg "%add.i98") (.reg "%sub.i87")
        (BitVec.ofNat 64 (64 * copyIterBound (q - i) + 64))
        (BitVec.ofNat 64 ((q - i) - (64 * copyIterBound (q - i) + 64)))
        (pb := b) (xp := xp) (tab := tab) (err := err) (xj := xj)
        (incv := decodeNextIdx inc11 adv + BitVec.ofInt 64 1)
        hblen hBlen hpcLw hpreLw (by decide)
        (evalOperand_reg_eq eL.env eL "%add.i98" _ hknext) (by decide)
        (by
          show evalOperand (withEnv (("%k.0.i86.lcssa",
            .int 64 (BitVec.ofNat 64 (64 * copyIterBound (q - i) + 64))) :: eL.env) eL)
            (.reg "%sub.i87") = some (.int 64 (BitVec.ofNat 64
              ((q - i) - (64 * copyIterBound (q - i) + 64))))
          rw [evalOperand_reg_eq (("%k.0.i86.lcssa", .int 64 (BitVec.ofNat 64
            (64 * copyIterBound (q - i) + 64))) :: eL.env) eL "%sub.i87" _ (by
              rw [lookupName_cons_ne _ _ (by decide)]; exact hsnext)])
        hsrcbL hdstbL
        (by rw [hkNat]; exact hkexit)
        (by rw [hkNat]; omega)
        (by rw [hsubNat, hkNat])
        (by rw [hsubNat]
            exact copyIterBound_exit (sub := q - i) (c := copyIterBound (q - i))
              (by omega) (by omega) hgt)
        hprefL
        (by rw [hkNat]; exact hdstreadL)
        hsrcfullL hcellsL.1 hcellsL.2.1 hcellsL.2.2 hsubcL hfrL hdisjC houtle hiq hqn
    refine ⟨eT, i, q, out, inc11, adv, 2 + jL + jT, ?_, hpcT, hq, hiq, hqn, ?_,
      body_getElem?_getD hqbody, hsubT, hsub13T, hcfT.jcell, hcfT.pcell, hcfT.ncell,
      hincT, hcfT.errcell, hcfT.xjcell, hcfT.tabcell, hcfT.xpcell, hcfT.pos0cell,
      hcfT.dstcell, hfrT, hprefT, hkidx, ?_, ?_, ?_, hcfT.nxpcell, ⟨addv, hcfT.addcell,
      haddnat⟩⟩
    · omega
    · rw [readBytes_of_UnchangedOutside hfrT hbyteOut]
      exact byte_read_of_body hbodyS hqn
    · intro k
      exact runFuel_prefix_trans (runFuel_prefix_trans hrun2 hrunL) hrunT k
    · -- the destination holds the decoded prefix and the whole gap
      rw [srcBtake hblen hiq hqn] at hcovT
      rw [List.length_append, List.length_take,
        Nat.min_eq_left (by rw [List.length_drop, hblen]; omega)]
      exact JsonEntrySteps.readBytes_append _ out.length dst out (q - i)
        (List.take (q - i) (List.drop i body)) hprefT hcovT
    · exact ⟨hwalk2.walk, hprefT, hwalk2.length, hwalk2.prefix_le_cursor⟩
  · -- `if.end`'s zero arm: one control step to the same block
    obtain ⟨e0L, j0L, hj0L, hpc0, hpre0, hk0, hs0, hsub13c0, hsrcb0, hdstb0,
      hpref0, hfr0, hcells0, hrun0⟩ :=
      ifEnd_zeroArm (body := body) (st := st) (dst := dst) (nps := nps) (goal := goal)
        (b := b) (pos0 := pos0) (n := n) (s := e2) (i := i) (q := q) (c := c)
        (out := out) (extra := extra) (inc11 := inc11) (adv := adv) (mem := mem) hpc2 hpre2 hiq hqn hpos0n hframe2 hbodyE2 hk2 hc8' hpos02
        hp2 hi5' hdst2 hjcell2 houtle (by omega) hprefixE2 Cells hcells3
    have hBlen : ((body.drop i ++ extra).take ((q - i) + 32)).length = (q - i) + 32 :=
      srcBlen hblen hextralen hiq hqn
    have hsrcfull0 : readBytes e0L.mem (b + i) ((q - i) + 32) =
        some ((body.drop i ++ extra).take ((q - i) + 32)) := by
      rw [readBytes_of_UnchangedOutside hfr0 houtside]
      exact hsrcfullMem
    obtain ⟨eT, jT, hjT, hpcT, hprefT, hfrT, hcfT, hsubT, hincT, hsub13T, hrunT,
      hcovT⟩ :=
      copyTail_to_usRunExit (mem := mem) (extra := extra)
        (.imm (.int 64 (BitVec.ofInt 64 0))) (.reg "%sub13")
        (BitVec.ofInt 64 0) (BitVec.ofNat 64 (q - i))
        (pb := b) (xp := xp) (tab := tab) (err := err) (xj := xj)
        (incv := decodeNextIdx inc11 adv + BitVec.ofInt 64 1)
        hblen hBlen hpc0 hpre0 hk0
        (by simp [evalOperand, Const.toValue]) hs0
        (by
          show evalOperand (withEnv (("%k.0.i86.lcssa", .int 64 (BitVec.ofInt 64 0)) ::
            e0L.env) e0L) (.reg "%sub13") = some (.int 64 (BitVec.ofNat 64 (q - i)))
          rw [evalOperand_reg_eq (("%k.0.i86.lcssa", .int 64 (BitVec.ofInt 64 0)) ::
            e0L.env) e0L "%sub13" _ (by
              rw [lookupName_cons_ne _ _ (by decide)]; exact hsub13c0)])
        hsrcb0 hdstb0
        (by rw [show (BitVec.ofInt 64 0).toNat = 0 from by decide]; omega)
        (by rw [show (BitVec.ofInt 64 0).toNat = 0 from by decide]; omega)
        (by rw [ofNat64_toNat (by omega),
          show (BitVec.ofInt 64 0).toNat = 0 from by decide]; omega)
        (by rw [ofNat64_toNat (by omega)]; omega)
        hpref0
        (by rw [show (BitVec.ofInt 64 0).toNat = 0 from by decide]; rfl)
        hsrcfull0 hcells0.1 hcells0.2.1 hcells0.2.2 hsub13c0 hfr0 hdisjC houtle hiq hqn
    refine ⟨eT, i, q, out, inc11, adv, 2 + j0L + jT, ?_, hpcT, hq, hiq, hqn, ?_,
      body_getElem?_getD hqbody, hsubT, hsub13T, hcfT.jcell, hcfT.pcell, hcfT.ncell,
      hincT, hcfT.errcell, hcfT.xjcell, hcfT.tabcell, hcfT.xpcell, hcfT.pos0cell,
      hcfT.dstcell, hfrT, hprefT, hkidx, ?_, ?_, ?_, hcfT.nxpcell, ⟨addv, hcfT.addcell,
      haddnat⟩⟩
    · omega
    · rw [readBytes_of_UnchangedOutside hfrT hbyteOut]
      exact byte_read_of_body hbodyS hqn
    · intro k
      exact runFuel_prefix_trans (runFuel_prefix_trans hrun2 hrun0) hrunT k
    · -- the destination holds the decoded prefix and the whole gap
      rw [srcBtake hblen hiq hqn] at hcovT
      rw [List.length_append, List.length_take,
        Nat.min_eq_left (by rw [List.length_drop, hblen]; omega)]
      exact JsonEntrySteps.readBytes_append _ out.length dst out (q - i)
        (List.take (q - i) (List.drop i body)) hprefT hcovT
    · exact ⟨hwalk2.walk, hprefT, hwalk2.length, hwalk2.prefix_le_cursor⟩

/-- info: 'LeanLLVM.Vellum.latch_to_runExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms latch_to_runExit

/-! #### Axiom footprints: the carried frame -/

/-- info: 'LeanLLVM.Vellum.CellFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms CellFrame

/-- info: 'LeanLLVM.Vellum.CellFrame.copyBodyEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.copyBodyEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.tailEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.tailEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.tailIfEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.tailIfEnv

/-- info: 'LeanLLVM.Vellum.take_append_drop_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take_append_drop_take

/-- info: 'LeanLLVM.Vellum.CellFrame.runExitEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.runExitEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEnd21Env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.ifEnd21Env

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEndIEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.ifEndIEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifThen6IEnv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CellFrame.ifThen6IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEnd9IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifEnd9IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEndI115Env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifEndI115Env

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEnd3IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifEnd3IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifThen17IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifThen17IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.landLhsTrue22IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.landLhsTrue22IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifThen26IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifThen26IEnv

/-- info: 'LeanLLVM.Vellum.CellFrame.ifEnd32IEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CellFrame.ifEnd32IEnv

/-- info: 'LeanLLVM.Vellum.bv64_eq_ofNat_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bv64_eq_ofNat_toNat

/-- info: 'LeanLLVM.Vellum.ExpandStaging.latch_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ExpandStaging.latch_tail

/-- info: 'LeanLLVM.Vellum.ifEnd_env_sub_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_env_sub_eq

/-- info: 'LeanLLVM.Vellum.ifEnd_env_inc_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ifEnd_env_inc_eq

/-- info: 'LeanLLVM.Vellum.dest_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dest_cover

/-- info: 'LeanLLVM.Vellum.srcBlen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms srcBlen

/-- info: 'LeanLLVM.Vellum.srcBtake' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms srcBtake

/-! ### The refusal arm's four routes -/

/-- Sign extension at equal width on a byte's `ofNat 64` form, which is the
`%idxprom` hypothesis of the emitter's byte loads. -/
theorem signExtend_ofNat64_byte (c : BitVec 8) :
    ((BitVec.ofNat 64 c.toNat).signExtend 64).toNat = c.toNat := by
  rw [signExtend_self_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := c.isLt; omega)]

/-- A width-one word that is not one is zero, which is the form a block's branch
value takes when its guard is refuted. -/
theorem bv1_eq_zero_of_ne_one {v : BitVec 1} (h : v ≠ 1) : v = 0 := by
  have hv := v.isLt
  have htoNat : v.toNat ≠ 1 := fun h1 => h (BitVec.eq_of_toNat_eq (by simp [h1]))
  have : v.toNat = 0 := by omega
  exact BitVec.eq_of_toNat_eq (by simp [this])

theorem bv1_eq_one_of_ne_zero {v : BitVec 1} (h : v ≠ 0) : v = 1 := by
  have hv := v.isLt
  have htoNat : v.toNat ≠ 0 := fun h1 => h (BitVec.eq_of_toNat_eq (by simp [h1]))
  have : v.toNat = 1 := by omega
  exact BitVec.eq_of_toNat_eq (by simp [this])

/-- A width-one word's `= 0` reading, as the negation of its `= 1` reading. -/
theorem bv1_eq_zero_iff_ne_one (v : BitVec 1) : v = 0 ↔ v ≠ 1 := by
  constructor
  · intro h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
  · exact bv1_eq_zero_of_ne_one

/-- A disjunction at width one is one when either summand is. -/
theorem or1_eq_one_iff (x y : BitVec 1) : (x ||| y) = 1 ↔ x = 1 ∨ y = 1 := by
  constructor
  · intro h
    by_cases hx : x = 1
    · exact Or.inl hx
    · refine Or.inr (bv1_eq_one_of_ne_zero ?_)
      intro hy
      have hx0 : x = 0 := bv1_eq_zero_of_ne_one hx
      rw [hx0, hy] at h
      exact absurd h (by decide)
  · rintro (h | h)
    · rw [h]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or, show (1 : BitVec 1).toNat = 1 from rfl]
      have hy := y.isLt
      have : y.toNat = 0 ∨ y.toNat = 1 := by omega
      rcases this with h' | h' <;> rw [h'] <;> decide
    · rw [h, BitVec.or_comm]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or, show (1 : BitVec 1).toNat = 1 from rfl]
      have hx := x.isLt
      have : x.toNat = 0 ∨ x.toNat = 1 := by omega
      rcases this with h' | h' <;> rw [h'] <;> decide

/-- The inequality test at width one, as its proposition. -/
theorem evalICmp_ne_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ne x y = (1 : BitVec 1) ↔ x ≠ y := by
  rw [show evalICmp .ne x y = BitVec.ofBool (decide (x ≠ y)) from rfl]
  exact ofBool_decide_one_iff _

theorem evalICmp_ne_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ne x y = (0 : BitVec 1) ↔ x = y := by
  rw [show evalICmp .ne x y = BitVec.ofBool (decide (x ≠ y)) from rfl,
    ofBool_decide_zero_iff (x ≠ y)]
  constructor
  · intro h
    by_cases hx : x = y
    · exact hx
    · exact absurd hx h
  · intro h hx
    exact hx h

/-- The signed compare against `-1` at zero: the byte's high bit is set. -/
theorem evalICmp_sgt_negone_zero_iff (t : BitVec 8) :
    evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1) ↔ 128 ≤ t.toNat := by
  have h := evalICmp_sgt_negone_one_iff t
  have hz : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1) ↔
      ¬ (evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1)) :=
    bv1_eq_zero_iff_ne_one _
  rw [hz]
  constructor
  · intro hne
    apply Nat.le_of_not_lt
    intro hlt
    exact hne (h.2 hlt)
  · intro hge h1
    exact absurd (h.1 h1) (by omega)

/-- The low nibble of a sixteen-bit word, as the mask the hex reader applies. -/
theorem and15_ofNat (v : Nat) :
    (BitVec.ofNat 16 v) &&& (BitVec.ofInt 16 15) = BitVec.ofNat 16 (v % 16) := by
  rw [show (BitVec.ofInt 16 15) = (BitVec.ofNat 16 15) from BitVec.ofInt_ofNat 16 15]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (15 : Nat) % 2 ^ 16 = 15 from by decide]
  rw [show (15 : Nat) = 2 ^ 4 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (show 2 ^ 4 ∣ 2 ^ 16 from by decide)]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ### The refusal's exit, as the arm's word reads it -/

/-- **The refusal's exit state**, and the run prefix that reaches it: the block,
the predecessor edge, the two stores at the values the walk names, and the fuel.

The offset and the index are parameters rather than existentials inside the
predicate, because the consumer has to match them against the walk's refusal out-
come: an existential here would leave the two numbers unrelated. -/
def RefusalExitAt (s e : State) (err xj : Nat) (off k : BitVec 64) (fuel : Nat) : Prop :=
  e.pc = "cleanup41" ∧
  (e.pre = some "if.then20" ∨ e.pre = some "if.then22") ∧
  lookupName e.env "%sub" = some (.int 64 off) ∧
  lookupName e.env "%inc11" = some (.int 64 k) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  e.mem = udRefusalMem s.mem off.toNat err k.toNat xj ∧
  (∀ z, runFuel escapeCalls (fuel + z) usDecFunction s =
    runFuel escapeCalls z usDecFunction e)

/-- **The cells `us_run.exit` leaves**, as every block after it reads them: the head
position and its residual, the prefix length, the caller's registers, the two
destination slots, the index cell, and the byte the control test loads. -/
structure RunExitCells (e : State) (paddr : Nat) (sub13v subv j inc11v nv : BitVec 64)
    (b : BitVec 8) (dst tab err xj : Nat) : Prop where
  pc : e.pc = "us_run.exit"
  sub13 : lookupName e.env "%sub13" = some (.int 64 sub13v)
  jc : lookupName e.env "%j.0294" = some (.int 64 j)
  pc_p : lookupName e.env "%p" = some (.ptr paddr)
  sub : lookupName e.env "%sub" = some (.int 64 subv)
  nc : lookupName e.env "%n" = some (.int 64 nv)
  inc : lookupName e.env "%inc11" = some (.int 64 inc11v)
  errc : lookupName e.env "%err" = some (.ptr err)
  xjc : lookupName e.env "%xj" = some (.ptr xj)
  dstc : lookupName e.env "%dst" = some (.ptr dst)
  tabc : lookupName e.env "%tab" = some (.ptr tab)
  byte : readBytes e.mem (paddr + subv.toNat) 1 = some (natToBytes b.toNat 1)

/-- **Route (a): a control byte at the head.**  `us_run.exit`'s control test takes
`if.then20`, which performs the two stores and leaves for `cleanup41`. -/
theorem usRunExit_control_to_refusal {e : State} {paddr err xj dst tab : Nat}
    {sub13v subv j inc11v nv : BitVec 64} {b : BitVec 8}
    (hc : RunExitCells e paddr sub13v subv j inc11v nv b dst tab err xj)
    (h63 : subv.toNat < 2 ^ 63)
    (hcond : evalICmp .ult b (BitVec.ofInt 8 32) = (1 : BitVec 1)) :
    ∃ e' : State, RefusalExitAt e e' err xj subv inc11v 2 := by
  let e2 : State :=
    { (withEnv (udRunExitEnvS e.env paddr sub13v subv j b)
        { e with mem := udRefusalMem e.mem subv.toNat err inc11v.toNat xj }) with
        pc := "cleanup41", pre := some "if.then20" }
  have hstep1 : step escapeCalls usDecFunction e = .jump
      { (withEnv (udRunExitEnvS e.env paddr sub13v subv j b) e) with
          pc := "if.then20", pre := some "us_run.exit" } := by
    have h := udRunExit_stepS_one e.env e paddr sub13v subv j b hc.pc hc.sub13 hc.jc
      hc.pc_p hc.sub (signExtend_self_toNat subv) h63 hc.byte hcond
    rwa [show withEnv e.env e = e from rfl] at h
  have hstep2 : step escapeCalls usDecFunction
      { (withEnv (udRunExitEnvS e.env paddr sub13v subv j b) e) with
          pc := "if.then20", pre := some "us_run.exit" } = .jump e2 :=
    udIfThen20_step (udRunExitEnvS e.env paddr sub13v subv j b)
      { e with pc := "if.then20", pre := some "us_run.exit" } subv inc11v err xj rfl
      (by simp only [udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [udRunExitEnvS]; ud_lk_h hc.inc)
      (by simp only [udRunExitEnvS]; ud_lk_h hc.errc)
      (by simp only [udRunExitEnvS]; ud_lk_h hc.xjc)
  refine ⟨e2, rfl, Or.inl rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [e2, withEnv, udRunExitEnvS]; ud_lk_h hc.sub
  · simp only [e2, withEnv, udRunExitEnvS]; ud_lk_h hc.inc
  · simp only [e2, withEnv, udRunExitEnvS]; ud_lk_h hc.errc
  · simp only [e2, withEnv, udRunExitEnvS]; ud_lk_h hc.xjc
  · intro z
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep2]

/-- **Route (c2): the escape is the last byte of the body.**  `us_run.exit` takes
`if.end21` on the backslash and `if.end21` refuses, because the byte after it is at or
past the body's end; `if.then22` stores and leaves for `cleanup41`. -/
theorem usRunExit_alone_to_refusal {e : State} {paddr err xj dst tab : Nat}
    {sub13v subv j inc11v nv : BitVec 64} {b : BitVec 8}
    (hc : RunExitCells e paddr sub13v subv j inc11v nv b dst tab err xj)
    (h63 : subv.toNat < 2 ^ 63)
    (hcond0 : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1))
    (hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (0 : BitVec 1)) :
    ∃ e' : State, RefusalExitAt e e' err xj subv inc11v 3 := by
  let e2 : State :=
    { (withEnv (udIfEnd21Env (udRunExitEnvS e.env paddr sub13v subv j b) subv nv)
        { e with mem := udRefusalMem e.mem subv.toNat err inc11v.toNat xj }) with
        pc := "cleanup41", pre := some "if.then22" }
  have hstep1 : step escapeCalls usDecFunction e = .jump
      { (withEnv (udRunExitEnvS e.env paddr sub13v subv j b) e) with
          pc := "if.end21", pre := some "us_run.exit" } := by
    have h := udRunExit_stepS_zero e.env e paddr sub13v subv j b hc.pc hc.sub13 hc.jc
      hc.pc_p hc.sub (signExtend_self_toNat subv) h63 hc.byte hcond0
    rwa [show withEnv e.env e = e from rfl] at h
  have hstep2 : step escapeCalls usDecFunction
      { (withEnv (udRunExitEnvS e.env paddr sub13v subv j b) e) with
          pc := "if.end21", pre := some "us_run.exit" } = .jump
      { (withEnv (udIfEnd21Env (udRunExitEnvS e.env paddr sub13v subv j b) subv nv) e)
        with pc := "if.then22", pre := some "if.end21" } :=
    udIfEnd21_step_zero (udRunExitEnvS e.env paddr sub13v subv j b)
      { e with pc := "if.end21", pre := some "us_run.exit" } subv nv rfl
      (by simp only [udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [udRunExitEnvS]; ud_lk_h hc.nc) hcond2
  have hstep3 : step escapeCalls usDecFunction
      { (withEnv (udIfEnd21Env (udRunExitEnvS e.env paddr sub13v subv j b) subv nv) e)
        with pc := "if.then22", pre := some "if.end21" } = .jump e2 :=
    udIfThen22_step (udIfEnd21Env (udRunExitEnvS e.env paddr sub13v subv j b) subv nv)
      { e with pc := "if.then22", pre := some "if.end21" } subv inc11v err xj rfl
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.inc)
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.errc)
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.xjc)
  refine ⟨e2, rfl, Or.inr rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.sub
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.inc
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.errc
  · simp only [e2, withEnv, udIfEnd21Env, udRunExitEnvS]; ud_lk_h hc.xjc
  · intro z
    rw [show 3 + z = (2 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep2]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep3]

/-- **Route (c1): the escape is not one the emitter can read.**  `us_run.exit` takes
`if.end21` on the backslash, `if.end21` finds the second byte inside the body, and
`if.end.i` finds no two-character escape at it — so `if.end9.i` reads the byte again
and refuses: it is not `u`, or six bytes past the escape do not fit.  `if.then22`
stores and leaves for `cleanup41`.

The two branch values are the caller's, because they are the emitter's decisions and
not these blocks' arithmetic: the table's answer at the second byte (`hcond4`) and
`if.end9.i`'s own guard (`hcond9`). -/
theorem usRunExit_second_to_refusal {e : State} {paddr err xj dst tab : Nat}
    {sub13v subv j inc11v nv : BitVec 64} {b : BitVec 8} {c1 : UInt8} {t : BitVec 8}
    (hc : RunExitCells e paddr sub13v subv j inc11v nv b dst tab err xj)
    (h63 : subv.toNat < 2 ^ 63)
    (hoff63 : (subv + BitVec.ofInt 64 1).toNat < 2 ^ 63)
    (hcond0 : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1))
    (hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (1 : BitVec 1))
    (h2 : readBytes e.mem (paddr + (subv + BitVec.ofInt 64 1).toNat) 1 =
      some (natToBytes c1.toNat 1))
    (ht : readBytes e.mem (tab + c1.toNat) 1 = some (natToBytes t.toNat 1))
    (hcond4 : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1))
    (hcond9 : (evalICmp .ne (BitVec.ofNat 8 c1.toNat) (BitVec.ofInt 8 117) |||
      evalICmp .ugt (subv + BitVec.ofInt 64 6) nv) = (1 : BitVec 1)) :
    ∃ e' : State, RefusalExitAt e e' err xj subv inc11v 5 := by
  let E1 := udRunExitEnvS e.env paddr sub13v subv j b
  let off := subv + BitVec.ofInt 64 1
  let c1v : BitVec 8 := BitVec.ofNat 8 c1.toNat
  have hc1vn : c1v.toNat = c1.toNat := by
    show (BitVec.ofNat 8 c1.toNat).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c1.toNat_lt; omega)]
  let E2 := udIfEndIEnv (udIfEnd21Env E1 subv nv) paddr tab off c1v t
  let E3 := udIfEnd9IEnv E2 (subv + BitVec.ofInt 64 6)
    (evalICmp .ne c1v (BitVec.ofInt 8 117)) (evalICmp .ugt (subv + BitVec.ofInt 64 6) nv)
  let e5 : State :=
    { (withEnv E3 { e with mem := udRefusalMem e.mem subv.toNat err inc11v.toNat xj })
        with pc := "cleanup41", pre := some "if.then22" }
  have hstep1 : step escapeCalls usDecFunction e = .jump
      { (withEnv E1 e) with pc := "if.end21", pre := some "us_run.exit" } := by
    have h := udRunExit_stepS_zero e.env e paddr sub13v subv j b hc.pc hc.sub13 hc.jc
      hc.pc_p hc.sub (signExtend_self_toNat subv) h63 hc.byte hcond0
    rwa [show withEnv e.env e = e from rfl] at h
  have hstep2 : step escapeCalls usDecFunction
      { (withEnv E1 e) with pc := "if.end21", pre := some "us_run.exit" } = .jump
      { (withEnv (udIfEnd21Env E1 subv nv) e) with
          pc := "if.end.i", pre := some "if.end21" } :=
    udIfEnd21_step E1 { e with pc := "if.end21", pre := some "us_run.exit" } subv nv rfl
      (by simp only [E1, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E1, udRunExitEnvS]; ud_lk_h hc.nc) hcond2
  have hstep3 : step escapeCalls usDecFunction
      { (withEnv (udIfEnd21Env E1 subv nv) e) with
          pc := "if.end.i", pre := some "if.end21" } = .jump
      { (withEnv E2 e) with pc := "if.end9.i", pre := some "if.end.i" } :=
    udIfEndI_step_zero (udIfEnd21Env E1 subv nv)
      { e with pc := "if.end.i", pre := some "if.end21" } paddr tab off c1v t rfl
      (by simp only [udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.pc_p)
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk)
      (by simp only [udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.tabc)
      (signExtend_self_toNat off) hoff63 (by rw [hc1vn]; exact h2)
      (by rw [hc1vn]; exact ht) (signExtend_ofNat64_byte c1v) hcond4
  have hstep4 : step escapeCalls usDecFunction
      { (withEnv E2 e) with pc := "if.end9.i", pre := some "if.end.i" } = .jump
      { (withEnv E3 e) with pc := "if.then22", pre := some "if.end9.i" } :=
    udIfEnd9I_step E2
      { e with pc := "if.end9.i", pre := some "if.end.i" } subv nv c1v rfl
      (by simp only [E2, udIfEndIEnv]; ud_lk)
      (by simp only [E2, udIfEndIEnv, udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E2, udIfEndIEnv, udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.nc)
      hcond9
  have hstep5 : step escapeCalls usDecFunction
      { (withEnv E3 e) with pc := "if.then22", pre := some "if.end9.i" } = .jump e5 :=
    udIfThen22_step E3 { e with pc := "if.then22", pre := some "if.end9.i" } subv inc11v
      err xj rfl
      (by simp only [E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
        udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
        udRunExitEnvS]; ud_lk_h hc.inc)
      (by simp only [E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
        udRunExitEnvS]; ud_lk_h hc.errc)
      (by simp only [E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
        udRunExitEnvS]; ud_lk_h hc.xjc)
  refine ⟨e5, rfl, Or.inr rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [e5, withEnv, E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
      udRunExitEnvS]; ud_lk_h hc.sub
  · simp only [e5, withEnv, E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
      udRunExitEnvS]; ud_lk_h hc.inc
  · simp only [e5, withEnv, E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
      udRunExitEnvS]; ud_lk_h hc.errc
  · simp only [e5, withEnv, E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
      udRunExitEnvS]; ud_lk_h hc.xjc
  · intro z
    rw [show 5 + z = (4 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 4 + z = (3 + z) + 1 from by omega, udRun_jump hstep2]
    rw [show 3 + z = (2 + z) + 1 from by omega, udRun_jump hstep3]
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep4]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep5]

/-! ### The hex reader's refusal gate

The emitter's `\u` reader refuses when one of the four digits is not hexadecimal,
and the walk refuses at the same position because `hex4` answers `none` there.  The
bridge below is the negative direction of `hex4_of_lane_test`: the block's guard
reads the four lanes' tests out of its mask word, so a `hex4 = none` forces the
guard's zero arm.  The positive direction is `hex4_hxCode`'s, which the accepted
`\u` path consumes. -/

/-- `hex4`'s value from the four lane tests alone, which is the window the block
reads: the emitter's mask covers sixteen bytes and the digits are the first four. -/
theorem hex4_of_lane_test_four {bs : List UInt8} {q : Nat} {l : List (BitVec 8)}
    (hbytes : ∀ i, i < 4 → bs[q + i]? = some (UInt8.ofBitVec (l.getD i 0)))
    (h0 : hexLaneTest (l.getD 0 0) = true) (h1 : hexLaneTest (l.getD 1 0) = true)
    (h2 : hexLaneTest (l.getD 2 0) = true) (h3 : hexLaneTest (l.getD 3 0) = true) :
    hex4 bs q = some (hexFour (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)) := by
  unfold hex4
  rw [show bs[q]? = some (UInt8.ofBitVec (l.getD 0 0)) from hbytes 0 (by decide),
      show bs[q+1]? = some (UInt8.ofBitVec (l.getD 1 0)) from hbytes 1 (by decide),
      show bs[q+2]? = some (UInt8.ofBitVec (l.getD 2 0)) from hbytes 2 (by decide),
      show bs[q+3]? = some (UInt8.ofBitVec (l.getD 3 0)) from hbytes 3 (by decide)]
  simp only [hexDigit_lane, h0, h1, h2, h3]
  rfl

/-- The loaded byte's lane is the byte again, so the lane list and the sixteen-byte
window name the same four bytes. -/
theorem ofBitVec_byteLanes_getD (bs : List UInt8) (i : Nat) :
    UInt8.ofBitVec ((byteLanes bs).getD i 0) = bs.getD i 0 := by
  induction bs generalizing i with
  | nil => simp [byteLanes]
  | cons b rest ih =>
      cases i with
      | zero => simp [byteLanes]
      | succ j =>
          show UInt8.ofBitVec ((byteLanes rest).getD j 0) = rest.getD j 0
          exact ih j

/-- Four lanes' worth of a byte list, as the four-and-rest shape the mask's low
nibble is stated at. -/
theorem byteLanes_four {bs : List UInt8} (hlen : 4 ≤ bs.length) :
    ∃ (x0 x1 x2 x3 : BitVec 8) (rest : List (BitVec 8)),
      byteLanes bs = x0 :: x1 :: x2 :: x3 :: rest := by
  cases bs with
  | nil => simp at hlen
  | cons b0 bs1 =>
    cases bs1 with
    | nil => simp at hlen
    | cons b1 bs2 =>
      cases bs2 with
      | nil => simp at hlen
      | cons b2 bs3 =>
        cases bs3 with
        | nil => simp at hlen
        | cons b3 rest =>
            exact ⟨BitVec.ofNat 8 b0.toNat, BitVec.ofNat 8 b1.toNat,
              BitVec.ofNat 8 b2.toNat, BitVec.ofNat 8 b3.toNat, byteLanes rest,
              by simp [byteLanes]⟩

/-- **A non-hexadecimal digit is the emitter's refusal.**  The block's guard is
`(%13 &&& 15) = 15` over the mask word the four loaded bytes build, so the guard's
one arm says all four digits are hexadecimal and `hex4` answers `some`: with
`hex4 … = none` the block takes its zero arm, which is `if.then22`. -/
theorem hexReaderGuard_zero_of_hex4_none {body : List UInt8} {k0 : Nat}
    {bs : List UInt8}
    (hlen : 4 ≤ bs.length)
    (hbytes : ∀ i, i < 4 → body[k0 + i]? = some (bs.getD i 0))
    (hnone : hex4 body k0 = none) :
    evalICmp .eq
      ((BitVec.ofNat 16 (lanesToNat (hexZipOr
        (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))))) &&&
        (BitVec.ofInt 16 15)) (BitVec.ofInt 16 15) = (0 : BitVec 1) := by
  refine bv1_eq_zero_of_ne_one ?_
  intro h1
  obtain ⟨x0, x1, x2, x3, rest, hsl⟩ := byteLanes_four hlen
  have heq : (BitVec.ofNat 16 (lanesToNat (hexZipOr
      (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
      (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
        (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))))) &&&
      (BitVec.ofInt 16 15) = BitVec.ofInt 16 15 := (evalICmp_eq_one_iff _ _).1 h1
  have hmod : lanesToNat (hexZipOr
      (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
      (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
        (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))) % 16 = 15 := by
    have h := congrArg BitVec.toNat heq
    rw [and15_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 16 15).toNat = 15 from by decide] at h
    rwa [Nat.mod_eq_of_lt (by omega)] at h
  have hfour := hexLanes_low_four (bs := bs) (x0 := x0) (x1 := x1) (x2 := x2)
    (x3 := x3) (rest := rest) hsl
  rw [hmod] at hfour
  have hall := (hexTest_four_eq_fifteen (hexLaneTest x0) (hexLaneTest x1)
    (hexLaneTest x2) (hexLaneTest x3)).1 hfour.symm
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hall
  have hbytes' : ∀ i, i < 4 → body[k0 + i]? =
      some (UInt8.ofBitVec ((byteLanes bs).getD i 0)) := by
    intro i hi
    rw [ofBitVec_byteLanes_getD]
    exact hbytes i hi
  have hsome := hex4_of_lane_test_four (bs := body) (q := k0) (l := byteLanes bs)
    hbytes' (by rw [hsl]; exact hx0) (by rw [hsl]; exact hx1)
    (by rw [hsl]; exact hx2) (by rw [hsl]; exact hx3)
  rw [hsome] at hnone
  exact absurd hnone (by simp)

/-- **Route (b): a `\u` whose digits are not hexadecimal.**  The run reaches the hex
reader through `if.end9.i`'s zero arm — the second byte is `u` and six bytes past the
escape fit — and the reader's guard is the four loaded digits' tests.  A non-hex
digit is `hex4`'s `none`, so the guard's zero arm takes `if.then22`, which stores and
leaves for `cleanup41`.

The window is the sixteen bytes at the escape plus two, and `hbytes` names the four
digits inside it: the guard is a statement about those four lanes, and `hex4`'s
refusal at the same position is what makes the arm necessary. -/
theorem usRunExit_hex_to_refusal {e : State} {paddr err xj dst tab : Nat}
    {sub13v subv j inc11v nv : BitVec 64} {b : BitVec 8} {c1 : UInt8} {t : BitVec 8}
    (hc : RunExitCells e paddr sub13v subv j inc11v nv b dst tab err xj)
    (h63 : subv.toNat < 2 ^ 63)
    (hoff63 : (subv + BitVec.ofInt 64 1).toNat < 2 ^ 63)
    (hcond0 : evalICmp .ult b (BitVec.ofInt 8 32) = (0 : BitVec 1))
    (hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (1 : BitVec 1))
    (h2 : readBytes e.mem (paddr + (subv + BitVec.ofInt 64 1).toNat) 1 =
      some (natToBytes c1.toNat 1))
    (ht : readBytes e.mem (tab + c1.toNat) 1 = some (natToBytes t.toNat 1))
    (hcond4 : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1))
    (hcond9 : (evalICmp .ne (BitVec.ofNat 8 c1.toNat) (BitVec.ofInt 8 117) |||
      evalICmp .ugt (subv + BitVec.ofInt 64 6) nv) = (0 : BitVec 1))
    {body : List UInt8} {k0 : Nat} {bs : List UInt8}
    (hlen : bs.length = 16)
    (hbs : readBytes e.mem (paddr + subv.toNat + 2) 16 = some bs)
    (hbytes : ∀ i, i < 4 → body[k0 + i]? = some (bs.getD i 0))
    (hnone : hex4 body k0 = none) :
    ∃ e' : State, RefusalExitAt e e' err xj subv inc11v 6 := by
  let E1 := udRunExitEnvS e.env paddr sub13v subv j b
  let off := subv + BitVec.ofInt 64 1
  let c1v : BitVec 8 := BitVec.ofNat 8 c1.toNat
  have hc1vn : c1v.toNat = c1.toNat := by
    show (BitVec.ofNat 8 c1.toNat).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := c1.toNat_lt; omega)]
  let E2 := udIfEndIEnv (udIfEnd21Env E1 subv nv) paddr tab off c1v t
  let E3 := udIfEnd9IEnv E2 (subv + BitVec.ofInt 64 6)
    (evalICmp .ne c1v (BitVec.ofInt 8 117)) (evalICmp .ugt (subv + BitVec.ofInt 64 6) nv)
  let E4 := udIfEndI115Env E3 (paddr + subv.toNat) bs
  let e6 : State :=
    { (withEnv E4 { e with mem := udRefusalMem e.mem subv.toNat err inc11v.toNat xj })
        with pc := "cleanup41", pre := some "if.then22" }
  have hguard : evalICmp .eq
      ((BitVec.ofNat 16 (lanesToNat (hexZipOr
        (hexUltL (hexAddL (byteLanes bs) (BitVec.ofInt 8 (-48))) (BitVec.ofInt 8 10))
        (hexUltL (hexAddL (hexOrL (byteLanes bs) (BitVec.ofInt 8 32))
          (BitVec.ofInt 8 (-97))) (BitVec.ofInt 8 6))))) &&&
        (BitVec.ofInt 16 15)) (BitVec.ofInt 16 15) = (0 : BitVec 1) :=
    hexReaderGuard_zero_of_hex4_none (by rw [hlen]; decide) hbytes hnone
  have hstep1 : step escapeCalls usDecFunction e = .jump
      { (withEnv E1 e) with pc := "if.end21", pre := some "us_run.exit" } := by
    have h := udRunExit_stepS_zero e.env e paddr sub13v subv j b hc.pc hc.sub13 hc.jc
      hc.pc_p hc.sub (signExtend_self_toNat subv) h63 hc.byte hcond0
    rwa [show withEnv e.env e = e from rfl] at h
  have hstep2 : step escapeCalls usDecFunction
      { (withEnv E1 e) with pc := "if.end21", pre := some "us_run.exit" } = .jump
      { (withEnv (udIfEnd21Env E1 subv nv) e) with
          pc := "if.end.i", pre := some "if.end21" } :=
    udIfEnd21_step E1 { e with pc := "if.end21", pre := some "us_run.exit" } subv nv rfl
      (by simp only [E1, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E1, udRunExitEnvS]; ud_lk_h hc.nc) hcond2
  have hstep3 : step escapeCalls usDecFunction
      { (withEnv (udIfEnd21Env E1 subv nv) e) with
          pc := "if.end.i", pre := some "if.end21" } = .jump
      { (withEnv E2 e) with pc := "if.end9.i", pre := some "if.end.i" } :=
    udIfEndI_step_zero (udIfEnd21Env E1 subv nv)
      { e with pc := "if.end.i", pre := some "if.end21" } paddr tab off c1v t rfl
      (by simp only [udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.pc_p)
      (by simp only [udIfEnd21Env, udRunExitEnvS]; ud_lk)
      (by simp only [udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.tabc)
      (signExtend_self_toNat off) hoff63 (by rw [hc1vn]; exact h2)
      (by rw [hc1vn]; exact ht) (signExtend_ofNat64_byte c1v) hcond4
  have hstep4 : step escapeCalls usDecFunction
      { (withEnv E2 e) with pc := "if.end9.i", pre := some "if.end.i" } = .jump
      { (withEnv E3 e) with pc := "if.end.i115", pre := some "if.end9.i" } :=
    udIfEnd9I_step_zero E2
      { e with pc := "if.end9.i", pre := some "if.end.i" } subv nv c1v rfl
      (by simp only [E2, udIfEndIEnv]; ud_lk)
      (by simp only [E2, udIfEndIEnv, udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E2, udIfEndIEnv, udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.nc)
      hcond9
  have hstep5 : step escapeCalls usDecFunction
      { (withEnv E3 e) with pc := "if.end.i115", pre := some "if.end9.i" } = .jump
      { (withEnv E4 e) with pc := "if.then22", pre := some "if.end.i115" } :=
    udIfEndI115_step_zero E3
      { e with pc := "if.end.i115", pre := some "if.end9.i" } (paddr + subv.toNat) bs rfl
      (by simp only [E3, udIfEnd9IEnv, E2, udIfEndIEnv, udIfEnd21Env, E1,
        udRunExitEnvS]; ud_lk_h hc.pc_p)
      hlen hbs hguard
  have hstep6 : step escapeCalls usDecFunction
      { (withEnv E4 e) with pc := "if.then22", pre := some "if.end.i115" } = .jump e6 :=
    udIfThen22_step E4 { e with pc := "if.then22", pre := some "if.end.i115" } subv inc11v
      err xj rfl
      (by simp only [E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
        udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.sub)
      (by simp only [E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
        udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.inc)
      (by simp only [E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
        udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.errc)
      (by simp only [E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
        udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.xjc)
  refine ⟨e6, rfl, Or.inr rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [e6, withEnv, E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
      udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.sub
  · simp only [e6, withEnv, E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
      udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.inc
  · simp only [e6, withEnv, E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
      udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.errc
  · simp only [e6, withEnv, E4, udIfEndI115Env, E3, udIfEnd9IEnv, E2, udIfEndIEnv,
      udIfEnd21Env, E1, udRunExitEnvS]; ud_lk_h hc.xjc
  · intro z
    rw [show 6 + z = (5 + z) + 1 from by omega, udRun_jump hstep1]
    rw [show 5 + z = (4 + z) + 1 from by omega, udRun_jump hstep2]
    rw [show 4 + z = (3 + z) + 1 from by omega, udRun_jump hstep3]
    rw [show 3 + z = (2 + z) + 1 from by omega, udRun_jump hstep4]
    rw [show 2 + z = (1 + z) + 1 from by omega, udRun_jump hstep5]
    rw [show 1 + z = z + 1 from by omega, udRun_jump hstep6]

/-! ### The refusal arm, composed from the four routes

`assemblyRefusalArm` is the bundle's `.refuse` field, and it is one statement about
four paths rather than one path: `decodeRefuses` is true exactly when the head byte
is a control byte or `escapeAt` names no escape there, and the emitter reaches
`cleanup41` by four different blocks for those two reasons.  The dispatch is on the
body's bytes, not on the run, and each leaf is one of the four tails above:

* a control byte — `us_run.exit`'s `if.then20`;
* `\` with no byte after it — `if.end21`'s zero arm;
* `\` whose second byte is not `u`, or whose six bytes do not fit — `if.end9.i`'s;
* `\u` whose four digits are not hexadecimal — `if.end.i115`'s.

The emitter's two decoding leaves — the two-character escape and the two `\u` forms —
are `escapeAt = some …` at the head, which the walk's own refusal excludes.

The proof is cut at the two seams the exit word has, and the cut is load-bearing
rather than stylistic: the arm's own statement is a five-conjunct word whose
disjunction mentions `ExpandStaging`, and elaborating the dispatch against it
re-unfolds that term at every branch.  `refusalArm_routes` needs none of it, and
`assemblyRefusalExit_of_reached` is the one step that does. -/

/-- `hex4` answers `none` wherever `escapeAt` does at a `\u` whose digits run from
`q + 2`.  The arm has the walk's refusal rather than the digits', so this is the
direction the hex reader's guard needs. -/
theorem hex4_none_of_escapeAt_none {body : List UInt8} {q : Nat}
    (h1 : body[q+1]? = some (0x75 : UInt8)) (h : escapeAt body q = none) :
    hex4 body (q + 2) = none := by
  cases hx : hex4 body (q + 2) with
  | none => rfl
  | some cp =>
      exfalso
      have h' : escapeAt body q ≠ none := by
        unfold escapeAt
        rw [h1]
        dsimp only
        rw [simpleEscape_u]
        simp only [ite_true]
        rw [hx]
        dsimp only
        cases hst : surrogateTail body q cp <;> simp
      exact h' h

/-- A sixteen-byte window of the body and its tail reads the body's own bytes back
inside the body's extent. -/
theorem take_append_getD {body extra : List UInt8} {k i : Nat}
    (hk : k + i < body.length) (hi : i < 16) :
    (((body.drop k ++ extra)).take 16).getD i 0 = body[k + i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi,
    List.getElem?_append_left (by rw [List.length_drop]; omega),
    List.getElem?_drop, List.getElem?_eq_getElem hk, Option.getD_some]

/-- A control byte is below thirty-two, at the block's own width. -/
theorem isControlB_true_toNat {b : UInt8} (h : IsControlB b = true) : b.toNat < 32 := by
  have h31 : ((0x1F : UInt8)).toNat = 31 := by decide
  have hb : b ≤ 0x1F := of_decide_eq_true h
  rw [UInt8.le_iff_toNat_le, h31] at hb
  omega

/-- A byte the control test rejects is at least thirty-two. -/
theorem isControlB_false_toNat {b : UInt8} (h : IsControlB b = false) : 32 ≤ b.toNat := by
  have h31 : ((0x1F : UInt8)).toNat = 31 := by decide
  by_cases hlt : b.toNat < 32
  · have hb : b ≤ 0x1F := by
      rw [UInt8.le_iff_toNat_le, h31]
      omega
    have htrue : IsControlB b = true := by
      rw [IsControlB]
      exact decide_eq_true hb
    rw [htrue] at h
    exact absurd h (by decide)
  · omega

/-- **The four routes, dispatched on the body's bytes.**  From the `us_run.exit`
cells, the record's body and table reads at that state's memory, and the head's
refusal, the run reaches `cleanup41` within six steps — one tail's allowance — at the
word's refusal branch. -/
theorem refusalArm_routes
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8} {st : ClassState}
    {dst nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat} {pos0 n : Nat}
    {ps : List Nat} {err xj : Nat} {e : State} {q : Nat}
    {sub13v subv jb inc11v nv : BitVec 64} {bv : BitVec 8}
    (hstg : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    (hframeE : UnchangedOutside mem e.mem [(dst, n + 64)])
    (hblen : body.length = n)
    (hbodyLatch : readBytes e.mem b n = some body)
    (htabRead : readBytes e.mem tab 256 = some unescapeTable)
    (hcells : RunExitCells e b sub13v subv jb inc11v nv bv dst tab err xj)
    (hsubvn : subv.toNat = q) (hnvn : nv.toNat = n)
    (hoff1n : (subv + BitVec.ofInt 64 1).toNat = q + 1)
    (hoff6n : (subv + BitVec.ofInt 64 6).toNat = q + 6)
    (hbvn : bv.toNat = (body.getD q 0).toNat)
    (hoff163 : (subv + BitVec.ofInt 64 1).toNat < 2 ^ 63)
    (hgateQ : IsControlB (body.getD q 0) = true ∨ (escapeAt body q).isNone = true) :
    ∃ (e' : State) (fuel : Nat),
      RefusalExitAt e e' err xj subv inc11v fuel ∧ fuel ≤ 6 := by
  by_cases hctl : IsControlB (body.getD q 0) = true
  · -- (a) the head byte is a control byte
    have hcond : evalICmp .ult bv (BitVec.ofInt 8 32) = (1 : BitVec 1) := by
      refine (evalICmp_ult_one_iff _ _).2 ?_
      rw [hbvn, show ((BitVec.ofInt 8 32)).toNat = 32 from by decide]
      exact isControlB_true_toNat hctl
    obtain ⟨e', hR⟩ := usRunExit_control_to_refusal hcells
      (by rw [hsubvn]; omega) hcond
    exact ⟨e', 2, hR, by omega⟩
  · have hctl' : IsControlB (body.getD q 0) = false := by
      cases hv : IsControlB (body.getD q 0) with
      | false => rfl
      | true => exact absurd hv hctl
    have hb0nat : 32 ≤ (body.getD q 0).toNat := isControlB_false_toNat hctl'
    have hcond0 : evalICmp .ult bv (BitVec.ofInt 8 32) = (0 : BitVec 1) := by
      refine (evalICmp_ult_zero_iff _ _).2 ?_
      rw [hbvn, show ((BitVec.ofInt 8 32)).toNat = 32 from by decide]
      omega
    have hesc : escapeAt body q = none := by
      rcases hgateQ with hc1 | hc1
      · exact absurd hc1 hctl
      · cases hv : escapeAt body q with
        | none => rfl
        | some p => rw [hv] at hc1; exact absurd hc1 (by simp)
    by_cases hq1 : q + 1 < n
    · -- the second byte is inside the body
      let c1b : UInt8 := body.getD (q + 1) 0
      have hq1lt : q + 1 < body.length := by rw [hblen]; exact hq1
      have hc1 : body[q + 1]? = some c1b := body_getElem?_getD hq1lt
      have hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (1 : BitVec 1) := by
        refine (evalICmp_ult_one_iff _ _).2 ?_
        rw [hoff1n, hnvn]; omega
      have h2 : readBytes e.mem (b + (subv + BitVec.ofInt 64 1).toNat) 1 =
          some (natToBytes c1b.toNat 1) := by
        rw [hoff1n]
        exact readBytes_one_getD hbodyLatch hq1
      obtain ⟨t, _, ht, hiff⟩ := emitterTest_of_table (M := e.mem) (tab := tab) c1b
        htabRead
      by_cases hsimple : simpleEscape c1b = none
      · -- `if.end9.i` is reached, and its guard decides the route
        have hcond4 : evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (0 : BitVec 1) :=
          bv1_eq_zero_of_ne_one (fun h1 => hiff.1 h1 hsimple)
        by_cases hcu : c1b = 0x75
        · by_cases hq6 : q + 6 ≤ n
          · -- (b) the digits are not hexadecimal
            have h1u : body[q + 1]? = some (0x75 : UInt8) := by rw [← hcu]; exact hc1
            have hnone : hex4 body (q + 2) = none :=
              hex4_none_of_escapeAt_none h1u hesc
            have hcond9 : (evalICmp .ne (BitVec.ofNat 8 c1b.toNat)
                  (BitVec.ofInt 8 117) |||
                evalICmp .ugt (subv + BitVec.ofInt 64 6) nv) = (0 : BitVec 1) := by
              have h1 : evalICmp .ne (BitVec.ofNat 8 c1b.toNat)
                  (BitVec.ofInt 8 117) = (0 : BitVec 1) :=
                (evalICmp_ne_zero_iff _ _).2 (by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := c1b.toNat_lt; omega), hcu]
                  decide)
              have h2' : evalICmp .ugt (subv + BitVec.ofInt 64 6) nv = (0 : BitVec 1) :=
                (evalICmp_ugt_zero_iff _ _).2 (by rw [hoff6n, hnvn]; omega)
              rw [h1, h2']
              decide
            obtain ⟨extra, hextraE, hextralen⟩ := ExpandStaging.latch_tail hstg hframeE
            have hfull := (finalSource_read (mem := e.mem) (b := b) (n := n)
              (i := q + 2) hbodyLatch (by omega) hextraE).1
            have hfull16 : readBytes e.mem (b + (q + 2))
                (16 + ((n - (q + 2)) + 32 - 16)) =
                some (body.drop (q + 2) ++ extra) := by
              rw [show 16 + ((n - (q + 2)) + 32 - 16) = (n - (q + 2)) + 32
                from by omega]
              exact hfull
            obtain ⟨h16, _⟩ := readBytes_split e.mem (b + (q + 2)) 16
              ((n - (q + 2)) + 32 - 16) hfull16
            let win := ((body.drop (q + 2) ++ extra)).take 16
            have h16' : readBytes e.mem (b + subv.toNat + 2) 16 = some win := by
              rw [hsubvn, Nat.add_assoc]
              exact h16
            have hlen16 : win.length = 16 := by
              rw [List.length_take, Nat.min_eq_left (by
                rw [List.length_append, List.length_drop, hblen, hextralen]; omega)]
            obtain ⟨e', hR⟩ := usRunExit_hex_to_refusal
              (bs := win) (body := body) (k0 := q + 2)
              hcells (by rw [hsubvn]; omega) hoff163 hcond0 hcond2 h2 ht hcond4 hcond9
              hlen16 h16'
              (by
                intro i hi
                have hlt : q + 2 + i < body.length := by rw [hblen]; omega
                have htake : win.getD i 0 = body[q + 2 + i] := by
                  show ((body.drop (q + 2) ++ extra).take 16).getD i 0 =
                    body[q + 2 + i]
                  exact take_append_getD (by omega) (by omega)
                rw [htake]
                exact List.getElem?_eq_getElem hlt)
              hnone
            exact ⟨e', 6, hR, by omega⟩
          · -- (c1) six bytes past the escape do not fit
            have hcond9 : (evalICmp .ne (BitVec.ofNat 8 c1b.toNat)
                  (BitVec.ofInt 8 117) |||
                evalICmp .ugt (subv + BitVec.ofInt 64 6) nv) = (1 : BitVec 1) := by
              have h2' : evalICmp .ugt (subv + BitVec.ofInt 64 6) nv = (1 : BitVec 1) :=
                (evalICmp_ugt_one_iff_toNat _ _).2 (by rw [hoff6n, hnvn]; omega)
              exact (or1_eq_one_iff _ _).2 (Or.inr h2')
            obtain ⟨e', hR⟩ := usRunExit_second_to_refusal hcells
              (by rw [hsubvn]; omega) hoff163 hcond0 hcond2 h2 ht hcond4 hcond9
            exact ⟨e', 5, hR, by omega⟩
        · -- (c1) the second byte is not `u`
          have hcond9 : (evalICmp .ne (BitVec.ofNat 8 c1b.toNat)
                (BitVec.ofInt 8 117) |||
              evalICmp .ugt (subv + BitVec.ofInt 64 6) nv) = (1 : BitVec 1) := by
            have h1 : evalICmp .ne (BitVec.ofNat 8 c1b.toNat)
                (BitVec.ofInt 8 117) = (1 : BitVec 1) :=
              (evalICmp_ne_one_iff _ _).2 (fun hc => hcu (by
                have hv := congrArg BitVec.toNat hc
                rw [BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by have := c1b.toNat_lt; omega),
                  show ((BitVec.ofInt 8 117)).toNat = 117 from by decide] at hv
                apply UInt8.toNat_inj.mp
                rw [show (0x75 : UInt8).toNat = 117 from by decide]
                exact hv))
            exact (or1_eq_one_iff _ _).2 (Or.inl h1)
          obtain ⟨e', hR⟩ := usRunExit_second_to_refusal hcells
            (by rw [hsubvn]; omega) hoff163 hcond0 hcond2 h2 ht hcond4 hcond9
          exact ⟨e', 5, hR, by omega⟩
      · -- a two-character escape: the walk decodes, so this is no refusal
        have hs : ∃ e0 : UInt8, simpleEscape c1b = some e0 := by
          cases hv : simpleEscape c1b with
          | none => exact absurd hv hsimple
          | some e0 => exact ⟨e0, rfl⟩
        obtain ⟨e0, hs⟩ := hs
        exact absurd (escapeAt_of_simple hc1 hs) (by rw [hesc]; simp)
    · -- (c2) the escape is the body's last byte
      have hcond2 : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (0 : BitVec 1) := by
        refine (evalICmp_ult_zero_iff _ _).2 ?_
        rw [hoff1n, hnvn]; omega
      obtain ⟨e', hR⟩ := usRunExit_alone_to_refusal hcells
        (by rw [hsubvn]; omega) hcond0 hcond2
      exact ⟨e', 3, hR, by omega⟩

/-- **The word's refusal branch, from the reached state.**  The two stores at the
walk's offset and index, the destinations the record names, and the frame: the
latch's extent widened to the record's four regions and then carried through the
stores, which are inside two of them. -/
theorem assemblyRefusalExit_of_reached
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8} {st : ClassState}
    {dst nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat} {pos0 n : Nat}
    {ps : List Nat} {err xj : Nat} {s e : State} {off k : BitVec 64} {j : Nat}
    (hstg : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    (hnoalias : DecodeNoAlias n dst err xj tab)
    (hframe : UnchangedOutside mem s.mem [(dst, n + 64)])
    (hR : RefusalExitAt s e err xj off k j)
    (hgoal : goal = .refused off.toNat k.toNat) :
    assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj e := by
  obtain ⟨hEpc, hEpre, hEsub, hEinc, hEerr, hExj, hEmem, hErun⟩ := hR
  -- the two stores' bytes, at the destinations the record names
  have hreadErr : readBytes e.mem err 8 = some (wordBytes 8 off.toNat) := by
    rw [hEmem]
    show readBytes (writeBytes (writeBytes s.mem err (natToBytes off.toNat 8))
      xj (natToBytes k.toNat 8)) err 8 = some (wordBytes 8 off.toNat)
    rcases hnoalias.2.2.1 with hd | hd
    · rw [readBytes_writeBytes_below _ _ 8 err xj (by omega)]
      simpa [wordBytes, natToBytes_length] using
        readBytes_writeBytes_same s.mem (natToBytes off.toNat 8)
    · rw [JsonEntrySteps.readBytes_writeBytes_above _ (natToBytes k.toNat 8) 8 err xj
        (by rw [natToBytes_length]; omega)]
      simpa [wordBytes, natToBytes_length] using
        readBytes_writeBytes_same s.mem (natToBytes off.toNat 8)
  have hreadXj : readBytes e.mem xj 8 = some (wordBytes 8 k.toNat) := by
    rw [hEmem]
    show readBytes (writeBytes (writeBytes s.mem err (natToBytes off.toNat 8))
      xj (natToBytes k.toNat 8)) xj 8 = some (wordBytes 8 k.toNat)
    simpa [wordBytes, natToBytes_length] using
      readBytes_writeBytes_same _ (natToBytes k.toNat 8)
  -- the frame: the latch's extent, widened, then carried through the two stores
  have hframeW : UnchangedOutside mem s.mem
      [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] :=
    UnchangedOutside.mono hframe (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp)
  have hstore1 : UnchangedOutside s.mem (writeBytes s.mem err (natToBytes off.toNat 8))
      [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] :=
    UnchangedOutside.writeBytes_in (m0 := s.mem) (m := s.mem) (fun _ _ => rfl)
      ⟨(err, 8), by simp, by simp, by simp [natToBytes_length]⟩
  have hstore2 : UnchangedOutside (writeBytes s.mem err (natToBytes off.toNat 8))
      (writeBytes (writeBytes s.mem err (natToBytes off.toNat 8))
        xj (natToBytes k.toNat 8))
      [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] :=
    UnchangedOutside.writeBytes_in (m0 := _) (m := _) (fun _ _ => rfl)
      ⟨(xj, 8), by simp, by simp, by simp [natToBytes_length]⟩
  have hframeAll : UnchangedOutside mem e.mem
      [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] := by
    rw [hEmem]
    exact UnchangedOutside.comp hframeW (UnchangedOutside.comp hstore1 hstore2
      (fun _ hr => hr)) (fun _ hr => hr)
  have hdr : DecodeRefusalExit e :=
    ⟨hEpc, off, k, err, xj, hEsub, hEinc, hEerr, hExj, hreadErr, hreadXj⟩
  have hword : AssemblyRefusalExit body st dst nps goal b xp tab pos0 n ps err xj
      mem e :=
    ⟨hdr, hEpre, hEerr, hExj, ⟨off, k, hEsub, hEinc, hgoal⟩, hframeAll⟩
  exact ⟨hstg, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hword))))⟩

/-- **The refusal arm is discharged.**  At the caller's staging, from any latch state
whose head refuses, the run reaches `cleanup41` within one iteration's allowance, at
the exit word's refusal branch. -/
theorem assemblyRefusalArm_satisfied
    {args : List Value} {mem : Mem} {next : Nat}
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b xp tab : Nat} {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj) :
    assemblyRefusalArm args mem next body st dst nps goal b xp tab pos0 n ps err xj
      hstaging (decodeIterCost n) := by
  intro r s c h href hnle
  -- `obtain` replaces the hypothesis it destructs, so the staging is kept beside it
  have hstg := hstaging
  -- the staging, the walk and the frame at the latch
  obtain ⟨_, _, _, hbodyS, hwidth, _, hmap, hnoalias, hdisjB, _, _⟩ := hstaging
  have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbodyS
  -- the middle is stated one iteration in, and the arm's exit test makes `r` positive
  obtain ⟨hcle0, hbudget0⟩ := assemblyLatchInv_budget h
  have hclt : c < nps := by omega
  have hrpos : r ≠ 0 := by omega
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero hrpos
  rw [hr'] at h
  obtain ⟨_, hds, _⟩ := assemblyLatchInv_staging h
  obtain ⟨_, hpslen, hrange, _⟩ := hds
  obtain ⟨i0, out0, hwalk⟩ := stagedLatchInv_decodeInv (assemblyLatchInv_staged h)
  have hcur := assemblyLatchInv_frame h
  -- the head position, its byte, and the record's refusal test at them
  have hcps : c < ps.length := by omega
  have hp : ps[c]? = some (ps[c]'hcps) := List.getElem?_eq_getElem hcps
  obtain ⟨_, hpn⟩ := hrange c (ps[c]'hcps) hp
  have hpge : ¬ ps[c]'hcps < pos0 := by omega
  have hb0lt : ps[c]'hcps - pos0 < body.length := by rw [hblen]; omega
  have hb0 : body[ps[c]'hcps - pos0]? = some (body.getD (ps[c]'hcps - pos0) 0) :=
    body_getElem?_getD hb0lt
  have hgate : decodeRefuses body ps pos0 c =
      (IsControlB (body.getD (ps[c]'hcps - pos0) 0) ||
        (escapeAt body (ps[c]'hcps - pos0)).isNone) :=
    decodeRefuses_eq_gate hp hpge hb0
  rw [hgate] at href
  -- the middle, from the latch to `us_run.exit`
  obtain ⟨e, i, q, out, inc11, adv, j0, hj0, hepc, hqE, hiq, hqn, hbyteE, hqbody,
    hsubE, hsub13E, hjE, hpE, hnE, hincE, herrE, hxjE, htabE, _, _, hdstE,
    hframeE, _, hinc, hrunE, _, _, _, _⟩ := latch_to_runExit hstg h hnle
  -- the entry at the cursor is the head, so `q` is its body-relative position
  have hheadP : (escAt body st 0)[c]? = some (ps[c]'hcps - pos0) := by
    rw [← escapePositionsFrom_eq_escAt, ← hmap, List.getElem?_map,
      List.getElem?_eq_getElem hcps]
    rfl
  have hqeq : ps[c]'hcps - pos0 = q := by
    rw [hheadP] at hqE
    exact Option.some.inj hqE
  have hlt : q < body.length := by rw [hblen]; omega
  have hgateQ : IsControlB (body.getD q 0) = true ∨
      (escapeAt body q).isNone = true := by
    have h := href
    rw [decide_eq_false hnle] at h
    have h' : IsControlB (body.getD q 0) = true ∨ escapeAt body q = none := by
      simpa [hgate, hqeq] using h
    rcases h' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1]; rfl)
  -- the walk's own refusal: which offset, and which index
  have hrw : goal = .refused q (c + 1) := by
    by_cases hctl : IsControlB (body.getD q 0) = true
    · exact DecodeInv.step_control hwalk (escAt_head_drop hqE) hqbody hlt hctl
    · have hctl' : IsControlB (body.getD q 0) = false := by
        cases hv : IsControlB (body.getD q 0) with
        | false => rfl
        | true => exact absurd hv hctl
      have hesc : escapeAt body q = none := by
        rcases hgateQ with hc1 | hc1
        · exact absurd hc1 hctl
        · cases hv : escapeAt body q with
          | none => rfl
          | some p => rw [hv] at hc1; exact absurd hc1 (by simp)
      exact DecodeInv.step_refuse hwalk (escAt_head_drop hqE) hqbody hlt hctl' hesc
  -- the arithmetic the tails' operands are stated at
  have hn32 : n ≤ 2 ^ 32 := by omega
  have hq64 : q < 2 ^ 64 := by omega
  have hq63 : q < 2 ^ 63 := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hsubvn : (BitVec.ofNat 64 q).toNat = q := ofNat64_toNat hq64
  have hnvn : (BitVec.ofNat 64 n).toNat = n := ofNat64_toNat hn64
  have hoff1n : ((BitVec.ofNat 64 q + BitVec.ofInt 64 1)).toNat = q + 1 := by
    rw [BitVec.toNat_add, hsubvn, show (BitVec.ofInt 64 1).toNat = 1 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hoff6n : ((BitVec.ofNat 64 q + BitVec.ofInt 64 6)).toNat = q + 6 := by
    rw [BitVec.toNat_add, hsubvn, show (BitVec.ofInt 64 6).toNat = 6 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hoff163 : ((BitVec.ofNat 64 q + BitVec.ofInt 64 1)).toNat < 2 ^ 63 := by
    rw [hoff1n]; omega
  -- the byte `us_run.exit` loads is the head byte
  let bv : BitVec 8 := BitVec.ofNat 8 (body.getD q 0).toNat
  have hbvn : bv.toNat = (body.getD q 0).toNat := by
    show (BitVec.ofNat 8 (body.getD q 0).toNat).toNat = _
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := (body.getD q 0).toNat_lt; omega)]
  have hcells : RunExitCells e b (BitVec.ofNat 64 (q - i)) (BitVec.ofNat 64 q)
      (BitVec.ofNat 64 out.length)
      (decodeNextIdx inc11 adv + BitVec.ofInt 64 1) (BitVec.ofNat 64 n) bv dst tab
      err xj :=
    { pc := hepc, sub13 := hsub13E, jc := hjE, pc_p := hpE, sub := hsubE, nc := hnE,
      inc := hincE, errc := herrE, xjc := hxjE, dstc := hdstE, tabc := htabE,
      byte := by rw [hsubvn, hbvn]; exact hbyteE }
  -- the body and the escape table at the exit state's memory
  obtain ⟨hbodyLatch, htabRead⟩ := ExpandStaging.latch_reads hstg hframeE
  -- the four routes
  obtain ⟨e', fuel, hR, hfuel⟩ := refusalArm_routes (q := q) hstg hframeE hblen
    hbodyLatch htabRead hcells hsubvn hnvn hoff1n hoff6n hbvn hoff163 hgateQ
  -- the word's refusal branch, at the walk's own offset and index
  have hcbound : c < 2 ^ 64 := by
    rw [← hinc]
    exact (decodeNextIdx inc11 adv).isLt
  have hnpsle : nps ≤ n := by
    have h1 : nps = (escapePositionsFrom body st).length := by
      rw [← hpslen, ← hmap, List.length_map]
    rw [h1, show escapePositionsFrom body st = escAt body st 0 from rfl, ← hblen]
    exact escAt_length_le body st 0
  have hc1 : c + 1 < 2 ^ 64 := by omega
  have hmod : (c + 1) % 2 ^ 64 = c + 1 := Nat.mod_eq_of_lt hc1
  have hkN : (decodeNextIdx inc11 adv + BitVec.ofInt 64 1).toNat = c + 1 := by
    rw [BitVec.toNat_add, hinc, show (BitVec.ofInt 64 1).toNat = 1 from by decide, hmod]
  have hgoal' : goal = .refused (BitVec.ofNat 64 q).toNat
      (decodeNextIdx inc11 adv + BitVec.ofInt 64 1).toNat := by
    rw [hsubvn, hkN]; exact hrw
  have hword := assemblyRefusalExit_of_reached hstg hnoalias hframeE hR hgoal'
  -- the exit, and the cost one iteration's allowance
  refine ⟨e', j0 + fuel, ?_, Or.inr hR.1, hword, ?_⟩
  · have hb := copyIterBound_le_div (sub := q - i) (n := n) (by omega)
    unfold copyIterBound at hj0 hb
    unfold decodeIterCost
    omega
  · intro z
    rw [show j0 + fuel + z = j0 + (fuel + z) from by omega]
    exact (hrunE (fuel + z)).trans (hR.2.2.2.2.2.2.2 z)

/-! #### Axiom footprints: the refusal routes -/

/-- info: 'LeanLLVM.Vellum.signExtend_ofNat64_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signExtend_ofNat64_byte

/-- info: 'LeanLLVM.Vellum.bv1_eq_zero_of_ne_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv1_eq_zero_of_ne_one

/-- info: 'LeanLLVM.Vellum.bv1_eq_one_of_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv1_eq_one_of_ne_zero

/-- info: 'LeanLLVM.Vellum.bv1_eq_zero_iff_ne_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv1_eq_zero_iff_ne_one

/-- info: 'LeanLLVM.Vellum.or1_eq_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms or1_eq_one_iff

/-- info: 'LeanLLVM.Vellum.evalICmp_ne_one_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms evalICmp_ne_one_iff

/-- info: 'LeanLLVM.Vellum.evalICmp_ne_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evalICmp_ne_zero_iff

/-- info: 'LeanLLVM.Vellum.evalICmp_sgt_negone_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_sgt_negone_zero_iff

/-- info: 'LeanLLVM.Vellum.and15_ofNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms and15_ofNat

/-- info: 'LeanLLVM.Vellum.RefusalExitAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RefusalExitAt

/-- info: 'LeanLLVM.Vellum.RunExitCells' does not depend on any axioms -/
#guard_msgs in
#print axioms RunExitCells

/-- info: 'LeanLLVM.Vellum.usRunExit_control_to_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usRunExit_control_to_refusal

/-- info: 'LeanLLVM.Vellum.usRunExit_alone_to_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usRunExit_alone_to_refusal

/-- info: 'LeanLLVM.Vellum.usRunExit_second_to_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usRunExit_second_to_refusal

/-- info: 'LeanLLVM.Vellum.hex4_of_lane_test_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hex4_of_lane_test_four

/-- info: 'LeanLLVM.Vellum.ofBitVec_byteLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofBitVec_byteLanes_getD

/-- info: 'LeanLLVM.Vellum.byteLanes_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms byteLanes_four

/-- info: 'LeanLLVM.Vellum.hexReaderGuard_zero_of_hex4_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hexReaderGuard_zero_of_hex4_none

/-- info: 'LeanLLVM.Vellum.usRunExit_hex_to_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usRunExit_hex_to_refusal

/-- info: 'LeanLLVM.Vellum.hex4_none_of_escapeAt_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hex4_none_of_escapeAt_none

/-- info: 'LeanLLVM.Vellum.take_append_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take_append_getD

/-- info: 'LeanLLVM.Vellum.isControlB_true_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isControlB_true_toNat

/-- info: 'LeanLLVM.Vellum.isControlB_false_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isControlB_false_toNat

/-- info: 'LeanLLVM.Vellum.refusalArm_routes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refusalArm_routes

/-- info: 'LeanLLVM.Vellum.assemblyRefusalExit_of_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyRefusalExit_of_reached

/-- info: 'LeanLLVM.Vellum.assemblyRefusalArm_satisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyRefusalArm_satisfied

end LeanLLVM.Vellum
