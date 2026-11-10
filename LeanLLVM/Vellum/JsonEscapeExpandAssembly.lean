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
puts the cursor at or behind that entry's body-relative position `q`. -/
theorem latch_to_ifEnd
    {args : List Value} {mem : Mem} {next : Nat}
    {body : List UInt8} {st : ClassState} {dst nps : Nat} {goal : EscapeOutcome}
    {b xp tab : Nat} {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj)
    {r c : Nat} {s : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem (r + 1) c s)
    (hguard : (decide (nps ≤ c) || decodeRefuses body ps pos0 c) = false) :
    ∃ (e : State) (i q : Nat) (out : List UInt8) (sub adv inc11 nxp jv : BitVec 64)
      (v : BitVec 32) (addv : BitVec 64),
      e.pc = "if.end" ∧ e.pre = some "while.body6" ∧ e.mem = s.mem ∧
      (escAt body st 0)[c]? = some q ∧ i ≤ q ∧ (adv + sub).toNat = i ∧
      lookupName e.env "%k.1296" = some (.int 64 (decodeNextIdx inc11 adv)) ∧
      lookupName e.env "%i.0295" = some (.int 64 (adv + sub)) ∧
      lookupName e.env "%j.0294" = some (.int 64 jv) ∧
      lookupName e.env "%conv8" = some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
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
  -- the guard says the index is live
  have hnle : ¬ nps ≤ c := by
    intro hle
    rw [decide_eq_true hle] at hguard
    exact absurd hguard (by simp)
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
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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

**The cells the emitter reads and the exit word omits.**  `copyBodyPrefixLoop`'s
`ExitWord` carries `%add.ptr`, `%add.ptr12`, `%sub13` and the two counters
(`copyBodyEnv_src`, `copyBodyEnv_dst`, `copyBodyEnv_sub`, `copyBodyEnv_knext`,
`copyBodyEnv_snext`), and the copy's destination and prefix reads beside them.
`%p`, `%dst` and `%j.0294` are inherited from the latch's environment and survive the
loop unchanged, but the word does not name them, so a consumer holding the exit state
alone cannot recover them: `us_run.exit` loads the body at `%p + %sub` and forms
`%add15 = %sub13 + %j.0294`, and `if.then6.i` stores at `%dst + %add15`.  Two forms
close this, and both are statements rather than proof work: an instance of the copy
whose `ExitWord` conjoins the three cells — the form `copyPreLoop` already takes for
`%j.0.lcssa`, `%k.1.lcssa` and `%xj` — or a `Carries` relation between the exit
environment and the caller's, carried as a conjunct of the loop's invariant, which is
the general form of the first and the one a second copy would reuse.  The second needs
a `lookupName` frame across a prepended environment, one lemma per block constructor.

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
    (hgt : 64 < q - i) :
    ∃ (e : State) (j : Nat),
      j ≤ copyIterBound (q - i) + 2 ∧
      CopyExitWord copyBodyNames (b + i) (dst + out.length) (q - i)
        ((body.drop i ++ extra).take ((q - i) + 32)) e ∧
      readBytes e.mem dst out.length = some out ∧
      UnchangedOutside mem e.mem [(dst, n + 64)] ∧
      lookupName e.env "%p" = some (.ptr b) ∧
      lookupName e.env "%dst" = some (.ptr dst) ∧
      lookupName e.env "%j.0294" = some (.int 64 (BitVec.ofNat 64 out.length)) ∧
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
  obtain ⟨eL, jL, hrest⟩ :=
    (copyBodyPrefixLoop (b + i) (dst + out.length) (q - i)
      ((body.drop i ++ extra).take ((q - i) + 32)) b dst out.length out s.mem (n + 64)
      (by omega) (by omega)).run_from (copyIterBound (q - i)) e3 0
      ⟨hinvC, hinv.stored, fun a _ => rfl, hp, hdstc, hj4⟩
  obtain ⟨hjL, hpcL, hwL, hrunL⟩ := hrest
  obtain ⟨hw1, hprefL, hframeL, hpL, hdL, hjcellL⟩ := hwL
  obtain ⟨hpcL', hpreL, hknext, hsnext, hsrcLb, hdstLb, hsubLb, hdstreadL, hsrcLb2⟩ := hw1
  have hjL' : jL ≤ copyIterBound (q - i) + 1 := by
    have := hjL; simpa [copyBodyPrefixLoop, Nat.mul_one] using this
  exact ⟨eL, 1 + jL, by omega,
    ⟨hpcL', hpreL, hknext, hsnext, hsrcLb, hdstLb, hsubLb, hdstreadL, hsrcLb2⟩,
    hprefL, UnchangedOutside.comp hframe hframeL (fun r hr => hr), hpL, hdL, hjcellL,
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
    (hprefix : readBytes s.mem dst out.length = some out) :
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
  refine ⟨e0, 1, by omega, rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_,
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

/-- info: 'LeanLLVM.Vellum.ifEnd_copyArm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_copyArm

/-- info: 'LeanLLVM.Vellum.ifEnd_zeroArm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_zeroArm


end LeanLLVM.Vellum
