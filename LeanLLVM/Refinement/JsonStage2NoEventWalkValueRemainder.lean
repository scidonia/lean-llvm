/-
The no-event walk's value class, the remainder arm: what the value dispatch does
with a byte that is neither a number start nor a literal start.

`Stage2NoEventValueClass` (`JsonStage2NoEventWalkHead`) is the dispatch at
`%.lcssa` below `if.end457`: `.ws` (9, 10, 13, 32), `.numberOrMinus` (`-` or a
decimal digit), `.literal` (`f`, `n`, `t`) and `.other`.  The four rows in
`JsonStage2NoEventWalkRowsValue` cover `.numberOrMinus` and `.literal`;
`hvalue`'s slot (`Stage2NoEventWalkValueReady`) still needs the remaining two
constructors, and this module is that arm's account.

**The route the body takes.**  For a head whose value-class byte is whitespace or
any other non-token byte, `NodeBlock5`'s value leaf enters `scalar`,
`cond.end` computes `%cond` and `land.lhs.true` probes the byte at it, the
scan to the token's end being `land.rhs`/`while.body`; `if.end457`'s guard
`%or.cond901` is `0`; the run leaves on `if.else495` and the
literal leaves `LeafBlock64`/`LeafBlock66`/`LeafBlock68` each fail, so the run
arrives at `if.else510`'s entry in at most four steps and then goes
`if.else510`'s eight instructions to `cleanup580`, whose `%retval.14` is `0`.  So
the arm is **not** a continuing one: it does not end at the next head or a
closing element, it ends in a refusal with the index's word at `%err`.  The row
it can build is `Stage2NoEventWalkRow.terminal` of a `Stage2NoEventWalkExit.refuse`
with the `gapElse` evidence (`%eoff = %idxprom.lcssa`).

**What this module proves, and what it does not.**  It proves the class's
dispatch arithmetic (`%or.cond901` is `0` at a byte that is not a number start,
kernel `decide` over `Fin 256`, and the three literal tests are `0` by their own
zero lemmas), the three literal leaves' steps
landing at `if.else510` from the committed denotations, the head predicate's
embedding into `Stage2NoEventWalkHeadValueClass`, the route's price
`23 + 5·(q − lane) ≤ Φ K k`, and the refusal row from the route's tail.  It does
**not** produce the row: `if.else510`'s own `denoteCode` chain is absent from the
tree.  `JsonStage2NoEventWalkTerminalA` pins the block
(`stage2NoEventIfElse510Block_find`) but derives neither its `denoteCode` nor the
`gapElse` evidence — its header says so ("their evidence is the route's to
supply") — so `step510` and `evidence` below are the missing premises, not
consequences of anything committed.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsValue
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminalA
import LeanLLVM.Refinement.JsonStage2NoEventWalkDispatchValueArmsB

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The value table's remainder

Two constructors of `Stage2NoEventValueClass` are left after the four rows: the
whitespace one and the catch-all.  Their common surface, at the byte's `Nat`
value, is exactly the negation of the number-or-minus guard and of the three
literal tests. -/

/-- **The value table's remainder**: not a number or a leading minus, and not a
literal start.  At a byte the guard's `45`/`48..57` test and the three literal
tests are both false, which is what the dispatch below reads. -/
def Stage2NoEventValueRemainder (x : Nat) : Prop :=
  ¬ (x = 45 ∨ (48 ≤ x ∧ x ≤ 57)) ∧ ¬ (x = 102 ∨ x = 110 ∨ x = 116)

/-- **The remainder is not a number start**, its first conjunct. -/
def Stage2NoEventValueNotNumber (x : Nat) : Prop :=
  ¬ (x = 45 ∨ (48 ≤ x ∧ x ≤ 57))

/-- The not-a-number test's decision procedure. -/
instance stage2NoEventValueNotNumberDecidable (x : Nat) :
    Decidable (Stage2NoEventValueNotNumber x) := by
  unfold Stage2NoEventValueNotNumber
  infer_instance

/-- **A remainder byte is not a number start.** -/
theorem Stage2NoEventValueRemainder.notNumber {x : Nat}
    (h : Stage2NoEventValueRemainder x) : Stage2NoEventValueNotNumber x := h.1

/-- The remainder's decision procedure, registered so `decide` can read the
predicate without unfolding it at instance search. -/
instance stage2NoEventValueRemainderDecidable (x : Nat) :
    Decidable (Stage2NoEventValueRemainder x) := by
  unfold Stage2NoEventValueRemainder
  infer_instance

/-- **The number-or-minus guard** `%or.cond901`, as `stage2SkipJoinRun` writes it
at `%.lcssa = lc`: `lc = '-'` or `lc - 48 < 10`. -/
def Stage2NoEventValueNumGuard (lc : BitVec 8) : BitVec 1 :=
  evalICmp .eq lc (BitVec.ofNat 8 45) |||
    evalICmp .ult (lc + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)

/-- **The guard's zero test is the not-a-number test**, byte by byte.  Kernel
`decide` over the 256 values, as the class tables in
`JsonStage2NoEventWalkScalar` are checked. -/
theorem stage2NoEventValueNumGuard_decide_fin (i : Fin 256) :
    decide (Stage2NoEventValueNumGuard (BitVec.ofNat 8 i.val) = 0) =
      decide (Stage2NoEventValueNotNumber i.val) := by
  revert i
  decide

/-- **The guard is zero at a byte that is not a number start.**  Kernel `decide`
over the 256 bytes, not a case split per value. -/
theorem stage2NoEventValueNumGuard_zero_fin (i : Fin 256)
    (h : Stage2NoEventValueNotNumber i.val) :
    Stage2NoEventValueNumGuard (BitVec.ofNat 8 i.val) = 0 := by
  have he := stage2NoEventValueNumGuard_decide_fin i
  have htrue : decide
      (Stage2NoEventValueNumGuard (BitVec.ofNat 8 i.val) = 0) = true := by
    rw [he, decide_eq_true h]
  exact of_decide_eq_true htrue

/-- **The guard is zero at a byte that is not a number start.** -/
theorem stage2NoEventValueNumGuard_zero {x : Nat} (hx : x < 256)
    (h : Stage2NoEventValueNotNumber x) :
    Stage2NoEventValueNumGuard (BitVec.ofNat 8 x) = 0 :=
  stage2NoEventValueNumGuard_zero_fin ⟨x, hx⟩ h

/-- **The guard is zero at a remainder byte**, as `UInt8` carries it. -/
theorem stage2NoEventValueNumGuard_zero_byte {byte : UInt8}
    (h : Stage2NoEventValueRemainder byte.toNat) :
    Stage2NoEventValueNumGuard (BitVec.ofNat 8 byte.toNat) = 0 :=
  stage2NoEventValueNumGuard_zero (UInt8.toNat_lt byte) h.notNumber

/-! ### The literal leaves' tests

Each leaf tests `%.lcssa` against its literal's first byte; at a remainder byte
none of the three holds, so each leaf's false edge is the one taken. -/

/-- **`icmp eq` is zero off the diagonal**, at the literal dispatch's width. -/
theorem stage2NoEventValueEq_zero {x c : Nat} (hx : x < 256) (hc : c < 256)
    (h : x ≠ c) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 c) = 0 := by
  refine valueArms_icmp_eq_zero ?_
  intro heq
  have hto := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hto
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hc] at hto
  exact h hto

/-- **The `f` leaf's test is zero at a remainder byte.** -/
theorem stage2NoEventValueLeafF_zero {x : Nat} (hx : x < 256)
    (h : ¬ (x = 102 ∨ x = 110 ∨ x = 116)) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 102) = 0 :=
  stage2NoEventValueEq_zero hx (by decide) (by
    intro hc; exact h (Or.inl hc))

/-- **The `n` leaf's test is zero at a remainder byte.** -/
theorem stage2NoEventValueLeafN_zero {x : Nat} (hx : x < 256)
    (h : ¬ (x = 102 ∨ x = 110 ∨ x = 116)) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 110) = 0 :=
  stage2NoEventValueEq_zero hx (by decide) (by
    intro hc; exact h (Or.inr (Or.inl hc)))

/-- **The `t` leaf's test is zero at a remainder byte.** -/
theorem stage2NoEventValueLeafT_zero {x : Nat} (hx : x < 256)
    (h : ¬ (x = 102 ∨ x = 110 ∨ x = 116)) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 116) = 0 :=
  stage2NoEventValueEq_zero hx (by decide) (by
    intro hc; exact h (Or.inr (Or.inr hc)))

/-! ### The head's remainder class

The head's value class (`Stage2NoEventWalkHeadValueClass`) cuts the remaining
bytes to those that are not `"`, `[`, `{`.  Its remainder subclass is the same
staging with the byte in the value table's remainder. -/

/-- **The head's value-class remainder.**  The head's lane, the document's byte
there, its `%3` cell, the three head-class exclusions, and the value table's
remainder at the byte. -/
def Stage2NoEventWalkHeadValueRemainder (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop :=
  ∃ (lane : Nat) (byte : UInt8),
    K.ent[k]? = some lane ∧ K.bs[lane]? = some byte ∧
    readBytes s.mem (K.b + lane) 1 = some [byte] ∧
    lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) ∧
    byte.toNat ≠ 34 ∧ byte.toNat ≠ 91 ∧ byte.toNat ≠ 123 ∧
    Stage2NoEventValueRemainder byte.toNat

/-- **The remainder is a head value class.**  The subclass is the predicate's
staging plus the value table's remainder; the class predicate drops the
remainder. -/
theorem Stage2NoEventWalkHeadValueRemainder.toValueClass {K : Stage2NoEventWalkCarry}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHeadValueRemainder K k s) :
    Stage2NoEventWalkHeadValueClass K k s := by
  obtain ⟨lane, byte, hent, hbs, hread, h3, h34, h91, h123, -⟩ := h
  exact ⟨lane, byte, hent, hbs, hread, h3, h34, h91, h123⟩

/-- **The head's remainder byte has the guard zero.**  The staging names the
byte; `%3` is its `8`-bit value and the guard reads that value. -/
theorem Stage2NoEventWalkHeadValueRemainder.numGuard_zero
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHeadValueRemainder K k s) :
    ∃ (lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ K.bs[lane]? = some byte ∧
      Stage2NoEventValueNumGuard (BitVec.ofNat 8 byte.toNat) = 0 := by
  obtain ⟨lane, byte, hent, hbs, -, -, -, -, -, hrem⟩ := h
  exact ⟨lane, byte, hent, hbs, stage2NoEventValueNumGuard_zero_byte hrem⟩

/-! ### The literal leaves reach `if.else510`

Each leaf's false edge is the refusal entry.  These are the committed
`DispatchValueArmsB` steps at the test the two lemmas above evaluate. -/

/-- **`LeafBlock64`'s step at a failed `f` test lands at `if.else510`.** -/
theorem valueRemainder_step_leaf64 {calls : Calls} {env : Env} {s : State}
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock64")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc))
    (h102 : evalICmp .eq lc (BitVec.ofNat 8 102) = 0) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (("%SwitchLeaf65", .int 1 0) :: env)
        { s with pc := "if.else510", pre := some "LeafBlock64" }) := by
  rw [valueArms_step_leafBlock64 calls env s hpc hlc, h102,
    if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]

/-- **`LeafBlock66`'s step at a failed `n` test lands at `if.else510`.** -/
theorem valueRemainder_step_leaf66 {calls : Calls} {env : Env} {s : State}
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock66")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc))
    (h110 : evalICmp .eq lc (BitVec.ofNat 8 110) = 0) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (("%SwitchLeaf67", .int 1 0) :: env)
        { s with pc := "if.else510", pre := some "LeafBlock66" }) := by
  rw [valueArms_step_leafBlock66 calls env s hpc hlc, h110,
    if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]

/-- **`LeafBlock68`'s step at a failed `t` test lands at `if.else510`.** -/
theorem valueRemainder_step_leaf68 {calls : Calls} {env : Env} {s : State}
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock68")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc))
    (h116 : evalICmp .eq lc (BitVec.ofNat 8 116) = 0) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (("%SwitchLeaf69", .int 1 0) :: env)
        { s with pc := "if.else510", pre := some "LeafBlock68" }) := by
  rw [valueArms_step_leafBlock68 calls env s hpc hlc, h116,
    if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]

/-! ### The route's price

The provider's route costs at most `18 + 5·(q − lane)` (`JsonStage2NoEventWalkValue`),
and the literal dispatch below `if.else495` adds at most four steps
(`if.else495`, `NodeBlock72`, `NodeBlock70`, one leaf), so the route to
`if.else510`'s entry costs at most `22 + 5·(q − lane)`, and the refusal seam's
`j + 1` at most `23 + 5·(q − lane)`.  The potential at the head is at least that
much with no budget: its entry term is at least `32`, and its document term at
least `8·(q − lane)`. -/

/-- **The remainder route's price is inside the potential.**  With one entry
left, the next entry's position (or the document's end) at `cond` and the scan's
stop `q` inside `[lane, cond]`, the seam's `23 + 5·(q − lane)` is at most
`Φ K k`. -/
theorem stage2NoEventWalkValueRemainder_price {K : Stage2NoEventWalkCarry}
    {k lane q cond : Nat}
    (hent : K.ent[k]? = some lane)
    (hk : k + 1 ≤ K.nep) (hlaneq : lane ≤ q) (hq : q ≤ cond) (hcondn : cond ≤ K.n) :
    23 + 5 * (q - lane) ≤ stage2NoEventWalkPotential K k := by
  unfold stage2NoEventWalkPotential
  have hget : K.ent.getD k 0 = lane := by
    rw [List.getD_eq_getElem?_getD, hent]; rfl
  rw [hget]
  have h1 : 1 ≤ K.nep - k := by omega
  have h2 : q - lane ≤ K.n - lane := by omega
  have hm1 : 32 ≤ 32 * (K.nep - k) := by
    simpa using Nat.mul_le_mul_left 32 h1
  have hm2 : 8 * (q - lane) ≤ 8 * (K.n - lane) := Nat.mul_le_mul_left 8 h2
  omega

/-! ### The route, the price, and each premise's status

**The route**, verbatim: `NodeBlock5`'s value leaf → `scalar` (the head's seven
`phi` cells) → `cond.end` (`%cond` = the next entry's lane or `%n`) →
`land.lhs.true`/`land.rhs` scan to `%ee.1` → `if.end457` (the `%k219` store and
`%or.cond901` = 0) → `if.else495` → `NodeBlock72` → `NodeBlock70` or one of
`LeafBlock64`/`LeafBlock66`/`LeafBlock68` → `if.else510` (four stores, the
`od_gap_recover` call, the `%off` reload, the `%err` store) → `cleanup580`
(`%retval.14` = 0) → `ret`.  It ends at a **refusal**, not at the next head and
not at a closing element.

**The price**: the scan's route is at most `18 + 5·(q − lane)`
(`stage2NoEventWalkValue`); the literal dispatch below `if.else495` adds at most
four steps (`if.else495`, `NodeBlock72`, `NodeBlock70`, one leaf); the refusal
seam's `j + 1` is therefore at most `23 + 5·(q − lane)`, and
`23 + 5·(q − lane) ≤ Φ K k` (`stage2NoEventWalkValueRemainder_price`), with no
budget spent.  `%idxprom.lcssa` becomes `%err`'s word.

**Status of each premise.**

* `proved here`: the guard `%or.cond901 = 0` at a byte that is not a number start
  (`…NumGuard_zero*`), the three literal tests `= 0` at a remainder byte
  (`…LeafF/N/T_zero`), the three leaf steps' false edges (`valueRemainder_step_leaf*`),
  the head remainder's embedding into the head value class
  (`…toValueClass`), and the price (`…price`).
* `an existing denotation`: the head-to-`if.else495` route with its
  `18 + 5·(q − lane)` bound (`JsonStage2NoEventWalkValue`'s `stage2NoEventWalkValue`,
  with `stage2NoEventWalkValueProv_of_head` in `JsonStage2NoEventWalkRowsValue`),
  the `if.else495`/`NodeBlock72`/leaf steps
  (`JsonStage2NoEventWalkDispatchValueArmsB`), `cleanup580`'s returning step
  (`JsonStage2NoEventWalkTerminal`'s `stage2NoEventCleanup_step`), and the refusal
  boundary (`JsonStage2NoEventWalkTerminal`'s `stage2NoEventBoundary_refusal`).
* `not in this tree`: `if.else510`'s eight-instruction `denoteCode` chain.  The
  block is pinned as data (`stage2NoEventIfElse510Block_find`) but no `step` binds
  its five stores, the `od_gap_recover` call, the `%off` load and the `%err`
  store, so its output
  environment and memory are not available; and the `gapElse` evidence
  (`Stage2NoEventWalkRefusalEvidence.gapElse`, `%eoff = %idxprom.lcssa`, the
  `%off` slot at `K.e + 8` read at the call's memory) has no producer — the
  terminal module's header says the two gap entries' evidence is the route's to
  supply.  These two are the `step510` and `evidence` fields of
  `Stage2NoEventWalkValueRemainderTail`; nothing else of the arm is missing.

The four arm wrappers in `JsonStage2NoEventWalkRowsValue` also take the
separator loop's whitespace run (`hws : ∀ i, q ≤ i → i < cond → …`) as a
caller premise; that run is the separator loop's whitespace run, taken as a
caller premise and distinct from this module's dispatch remainder — it is not a
block.

-/

/-! ### The arm's tail and the refusal row

The route is `NodeBlock5`'s value leaf, `scalar`, `cond.end`/`land.lhs.true`, the
merge, `if.else495`, the literal leaves, `if.else510`, `cleanup580`.  The first
segments are committed (`JsonStage2NoEventWalkValue`, and the leaves above), and
so is `cleanup580`'s (`JsonStage2NoEventWalkTerminal`'s `stage2NoEventCleanup_step`);
only `if.else510`'s denotation is absent, so the tail is stated as data: the run to
`if.else510`'s entry, the block's step, `cleanup580`'s return, and the `gapElse`
evidence.  The row is then the committed refusal seam
(`stage2NoEventRefuse_exit`) under `Stage2NoEventWalkRow.terminal`. -/

/-- **The remainder arm's tail.**  `run` is the route from the head to
`if.else510`'s entry (`scalar` through the literal leaves), `step510` that
block's own step to `cleanup580`, `clean` the return block's step, and
`evidence` the `gapElse` shape.  `step510` and `evidence` are the two pieces the
tree does not supply. -/
structure Stage2NoEventWalkValueRemainderTail (gap : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The route's count to `if.else510`'s entry. -/
  j : Nat
  /-- `if.else510`'s entry. -/
  sE : State
  /-- `cleanup580`'s entry. -/
  sT : State
  /-- The return block's post-state. -/
  sR : State
  /-- The returned memory. -/
  m : Mem
  /-- The entry is the refusal block. -/
  entry : sE.pc = "if.else510"
  /-- The route from the head to the refusal block's entry. -/
  run : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
    runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE
  /-- The route plus the block's step is inside the potential. -/
  cost : j + 1 ≤ stage2NoEventWalkPotential K k + F
  /-- **Not in this tree**: `if.else510`'s eight-instruction step. -/
  step510 : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT
  /-- `cleanup580`'s returning step, verdict zero. -/
  clean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
    .ret (some (.int 64 0)) sR
  memR : sR.mem = m
  /-- **Not in this tree**: the `gapElse` evidence at `cleanup580`'s entry. -/
  evidence : Stage2NoEventWalkRefusalEvidence K sT
  report : Stage2NoEventRun K.a12 mem m
  trace : Stage2NoEventWalkTrace K
  data : Stage2NoEventWalkReferenceRefuse K
  bound : stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)

/-- **The remainder arm's row**: the refusal seam's exit, as a terminal row.  The
row is `terminal` by construction — the body refuses these bytes, it does not
continue to the next head. -/
noncomputable def Stage2NoEventWalkValueRemainderTail.row {gap : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (t : Stage2NoEventWalkValueRemainderTail gap mem F K k s) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s :=
  .terminal
    (stage2NoEventRefuse_exit t.run t.step510 t.clean t.memR t.cost t.report
      t.trace t.evidence t.data t.bound)

/-- **The route's endpoint is the refusal block.** -/
theorem Stage2NoEventWalkValueRemainderTail.entryPc {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (t : Stage2NoEventWalkValueRemainderTail gap mem F K k s) :
    t.sE.pc = "if.else510" := t.entry

/-! ### Axiom footprints -/

#print axioms stage2NoEventValueNumGuard_decide_fin
#print axioms stage2NoEventValueNumGuard_zero
#print axioms stage2NoEventValueNumGuard_zero_byte
#print axioms stage2NoEventValueEq_zero
#print axioms stage2NoEventValueLeafF_zero
#print axioms stage2NoEventValueLeafN_zero
#print axioms stage2NoEventValueLeafT_zero
#print axioms Stage2NoEventWalkHeadValueRemainder.toValueClass
#print axioms Stage2NoEventWalkHeadValueRemainder.numGuard_zero
#print axioms valueRemainder_step_leaf64
#print axioms valueRemainder_step_leaf66
#print axioms valueRemainder_step_leaf68
#print axioms stage2NoEventWalkValueRemainder_price
#print axioms Stage2NoEventWalkValueRemainderTail.row
#print axioms Stage2NoEventWalkValueRemainderTail.entryPc

end LeanLLVM.Refinement
