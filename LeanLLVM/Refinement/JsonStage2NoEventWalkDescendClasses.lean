/-
The no-event walk's bracket descend, indexed by the continuation dispatch's class.

`JsonStage2NoEventWalkRowsDescend`'s descend arm hands `NodeBlock15` the entry at
`k + 1` and its document byte, and `Stage2NoEventWalkBracketInner` names what must
happen next: at every state on the dispatch's window, the class the byte selects
runs its route to the `after_value` endpoint and the shared cycle returns.  The
committed producer `JsonStage2NoEventWalkBracketInner` supplies that obligation at
the `[` class only: its window's `byte91 : nextByte.toNat = 91` pins the entry's
byte, so the committed window is uninhabited at `{`, `"`, a digit or `t`/`f`/`n`.
This module states the window once, **indexed by the dispatch's class**, and says
for each class where its inner route comes from.

**The classes.**  `Stage2NoEventWalkDescendClass` is the dispatch's own table:
`bracket` (`91`), `brace` (`123`), `string` (`34`) and `scalar` (every other
byte).  `Selects` is the class's byte predicate and `entryPc` the block the
class's dispatch chain lands in — `if.then35`, `if.then9.loopexit`,
`string_value.loopexit`, `scalar.loopexit`, the dispatch's four leaf targets
`JsonStage2NoEventWalkClose` proves out of `NodeBlock15`;
`stage2NoEventWalkDescendClass_exists_selects` and
`…_selects_unique` say the table is total and deterministic: every byte selects
exactly one class, so the four classes partition the dispatch's byte space and no
row is stated at a byte no class owns.

**The window, indexed.**  `Stage2NoEventWalkDescendWindow cls` is the readings
every class's inner route starts from: the dispatch's own window
(`Stage2NoEventWalkBracketDispatch`: the class byte `%7`, its lane `%8`, the
index, the guard's index, the two counts and the base lookups), the class's
selection of the entry's byte (`sel`), the entry at `k + 1` (`bs1`), the
invariant, the consumed-count bound, the report's base and the trace.  The class
enters through `sel` alone, and `Stage2NoEventWalkDescendWindow.entry` runs the
dispatch's chain from the window to `cls.entryPc`, returning the class's entry
state with the invariant.  The four instances are the committed chains at the
window's own byte: `stage2NoEventWalkDescendEntry_bracket` is
`stage2NoEventRow_loopExitBracket`, `…_brace` is `stage2NoEventRow_loopExitBrace`,
`…_string` is `stage2NoEventRow_loopExitString` and `…_scalar` is
`stage2NoEventRow_loopScalar` (three leaves, all at `scalar.loopexit`).

**`[` is the committed window.**  At `91` the window's remaining fields — the
outer opener's lane and byte, the array stack's cursor cells and their relation,
the stack base, the head's two arena `phi`s and the advance's room — are the
class's own staging, `Stage2NoEventWalkBracketClassStaging`.
`Stage2NoEventWalkDescendWindow.toBracket` rebuilds the committed
`Stage2NoEventWalkBracketInnerWindow` from the indexed window plus that staging;
`…toDescend` and `…BracketInnerWindow.staging` are the projections; and both
roundtrips hold.  The indexed window at `91` therefore *is* the committed window,
with no new staging for the array, and
`stage2NoEventWalkDescendBracketAt327` hands the rebuilt window to the committed
first half (`stage2NoEventWalkBracketInnerTo327`), so the `[` class's route
begins at `if.end327`'s entry with the arms `JsonStage2NoEventWalkBracketInner`
proves.

**The consequence, at `[`.**  `…BracketInner_of_windowSupply` turns the committed
`Stage2NoEventWalkBracketInnerAll` plus the per-dispatch window supply into
`Stage2NoEventWalkBracketInner` (the supply is the same `hstage`
`…BracketInnerOutElement` threads), and
`…BracketDescendRow_of_windowSupply` composes it with
`stage2NoEventWalkBracketDescendRow_of_inner`: at a `[` head carrying the
descend's staging and an entry at `k + 1` whose byte is not `]`, the head's row
exists.  That is the descend arm's row at `[`, unchanged from the committed
module but stated at the class.

**The other three classes: named, not produced.**  Their producers are in the
tree, but rooted at a `NodeBlock5` head, not at the `.loopexit` entry:

* `{` — `JsonStage2NoEventWalkRowsBrace`'s `stage2NoEventWalkBracePrologue` (the
  eight prologue links: the dispatch, `if.then9`'s seven `phi`s and depth test,
  the push, `if.end74`'s read) and `JsonStage2NoEventWalkKeyRoute`'s
  `stage2NoEventWalkKeyRoute_of_head` (the quote arm, `LeafBlock17` and the key's
  eighteen blocks), with the pair cycle `stage2NoEventWalkCycle_of_pair_price`.
  What is missing at this shape is the prologue *from* `if.then9.loopexit`: both
  stated pieces begin at the head and run their own three-block dispatch.
* `"` — `JsonStage2NoEventWalkRowsString`'s builders `…StringRoute_arena`/`…StringRoute_plain` over the committed `Stage2NoEventWalkStringRoute` (its
  `segHead` is the call's own eight-block slice, the dispatch included),
  `…StringRoute_arena`/`…StringRoute_plain` and the rows `…StringRow_arena`/
  `…StringRow_plainArm`.  The route builder is segment-driven; the row's
  head-dependence is only the consumed-count bound, which
  `JsonStage2NoEventWalkEntryRooted`'s `…StringRow_cont_of_route_count` replaces
  by a supply, so the remaining obstacle at `string_value.loopexit` is the call
  leg, not the row.
* scalar — `JsonStage2NoEventWalkRowsValue`'s `…ValueRoute_of_head` and
  `…ValueRow_of_head`, over the four arms `…ValueArmRoute_number`/`_True`/`_Null`/
  `_False`.  The row is head-rooted, and the residue table's whitespace/remainder
  arm has no producer at all.

`stage2NoEventWalkDescendEntry_notHead` proves why that matters: at `cls.entryPc`
no `Stage2NoEventWalkHead` holds (the head's `pc` is `NodeBlock5`), so each of
those producers is inapplicable at the entry its class's chain reaches.
`Stage2NoEventWalkDescendClass.routeAtDispatch` records the split in the class
vocabulary: `[` alone has a route stated at the dispatch.  Closing the other three
means stating their route from the class's entry — the prologue's links from
`if.then9.loopexit`, the string call's remaining slice from
`string_value.loopexit`, and the value arm from `scalar.loopexit` — and no module
in the tree does.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkBracketInner
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The dispatch's classes

`NodeBlock15`'s table compares the entry's byte with `34`, `91` and `123` and
falls to the scalar leaf otherwise.  The four classes below are that table; the
two facts this section proves are that it is total (every byte selects a class)
and deterministic (no byte selects two), so a row stated at a class is stated at
exactly the bytes that class owns. -/

/-- **The continuation dispatch's classes**: the array's `[`, the object's `{`,
the string's `"`, and the scalar class (every other byte). -/
inductive Stage2NoEventWalkDescendClass : Type
  | bracket
  | brace
  | string
  | scalar
  deriving DecidableEq, Repr

namespace Stage2NoEventWalkDescendClass

/-- **The class's byte predicate.**  The three openers are equalities; the scalar
class is their complement. -/
def Selects : Stage2NoEventWalkDescendClass → Nat → Prop
  | .bracket, b => b = 91
  | .brace, b => b = 123
  | .string, b => b = 34
  | .scalar, b => b ≠ 34 ∧ b ≠ 91 ∧ b ≠ 123

/-- **The block the class's dispatch chain lands in**, one of `NodeBlock15`'s
four `.loopexit` leaves (`JsonStage2NoEventWalkClose`'s `stage2NoEventRow_loopExit*`). -/
def entryPc : Stage2NoEventWalkDescendClass → String
  | .bracket => "if.then35"
  | .brace => "if.then9.loopexit"
  | .string => "string_value.loopexit"
  | .scalar => "scalar.loopexit"

/-- **The class's inner producer, by committed module.**  The `[` class's route is
stated at the continuation dispatch (`JsonStage2NoEventWalkBracketInner`); the
other three only at a `NodeBlock5` head (see `routeAtDispatch`). -/
def producer : Stage2NoEventWalkDescendClass → String
  | .bracket =>
      "JsonStage2NoEventWalkBracketInner (…BracketInnerOutCloser, …BracketInnerOutElement)"
  | .brace =>
      "JsonStage2NoEventWalkRowsBrace + JsonStage2NoEventWalkKeyRoute (…BracePrologue, …KeyRoute_of_head)"
  | .string =>
      "JsonStage2NoEventWalkRowsString (…StringRoute_arena, …StringRow_arena/_plainArm)"
  | .scalar =>
      "JsonStage2NoEventWalkRowsValue (…ValueRoute_of_head, …ValueRow_of_head)"

/-- **Whether the class's producer runs from the continuation dispatch.**  Only
the `[` class's does; the other three begin at a `NodeBlock5` head. -/
def routeAtDispatch : Stage2NoEventWalkDescendClass → Bool
  | .bracket => true
  | .brace => false
  | .string => false
  | .scalar => false

/-- The three openers' predicates are their byte equalities, and the scalar
class's is the complement, verbatim. -/
theorem selects_bracket {b : Nat} : Selects .bracket b ↔ b = 91 := Iff.rfl

theorem selects_brace {b : Nat} : Selects .brace b ↔ b = 123 := Iff.rfl

theorem selects_string {b : Nat} : Selects .string b ↔ b = 34 := Iff.rfl

theorem selects_scalar {b : Nat} :
    Selects .scalar b ↔ b ≠ 34 ∧ b ≠ 91 ∧ b ≠ 123 := Iff.rfl

/-- **The table is total**: every byte falls in a class. -/
theorem exists_selects (b : Nat) : ∃ cls : Stage2NoEventWalkDescendClass, cls.Selects b := by
  by_cases h91 : b = 91
  · exact ⟨.bracket, h91⟩
  by_cases h123 : b = 123
  · exact ⟨.brace, h123⟩
  by_cases h34 : b = 34
  · exact ⟨.string, h34⟩
  exact ⟨.scalar, h34, h91, h123⟩

/-- **The table is deterministic**: a byte selects at most one class. -/
theorem selects_unique {cls cls' : Stage2NoEventWalkDescendClass} {b : Nat}
    (h : cls.Selects b) (h' : cls'.Selects b) : cls' = cls := by
  cases cls with
  | bracket =>
      have hb : b = 91 := selects_bracket.mp h
      cases cls' with
      | bracket => rfl
      | brace => exact absurd (hb.symm.trans (selects_brace.mp h')) (by decide)
      | string => exact absurd (hb.symm.trans (selects_string.mp h')) (by decide)
      | scalar => exact absurd hb (selects_scalar.mp h').2.1
  | brace =>
      have hb : b = 123 := selects_brace.mp h
      cases cls' with
      | bracket => exact absurd ((selects_bracket.mp h').symm.trans hb) (by decide)
      | brace => rfl
      | string => exact absurd ((selects_string.mp h').symm.trans hb) (by decide)
      | scalar => exact absurd hb (selects_scalar.mp h').2.2
  | string =>
      have hb : b = 34 := selects_string.mp h
      cases cls' with
      | bracket => exact absurd ((selects_bracket.mp h').symm.trans hb) (by decide)
      | brace => exact absurd ((selects_brace.mp h').symm.trans hb) (by decide)
      | string => rfl
      | scalar => exact absurd hb (selects_scalar.mp h').1
  | scalar =>
      have hb := selects_scalar.mp h
      cases cls' with
      | bracket => exact absurd (selects_bracket.mp h') hb.2.1
      | brace => exact absurd (selects_brace.mp h') hb.2.2
      | string => exact absurd (selects_string.mp h') hb.1
      | scalar => rfl

/-- **The table partitions the byte space**: exactly one class per byte. -/
theorem exists_unique_selects (b : Nat) :
    ∃ cls : Stage2NoEventWalkDescendClass,
      cls.Selects b ∧ ∀ cls', cls'.Selects b → cls' = cls := by
  obtain ⟨cls, h⟩ := exists_selects b
  exact ⟨cls, h, fun cls' h' => selects_unique h h'⟩

/-- No class's entry is the head block. -/
theorem entryPc_ne_nodeBlock5 (cls : Stage2NoEventWalkDescendClass) :
    cls.entryPc ≠ "NodeBlock5" := by
  cases cls <;> decide

/-- **`[` alone has a route at the continuation dispatch.** -/
theorem routeAtDispatch_iff (cls : Stage2NoEventWalkDescendClass) :
    cls.routeAtDispatch = true ↔ cls = .bracket := by
  cases cls <;> simp [routeAtDispatch]

end Stage2NoEventWalkDescendClass

/-! ### The window, indexed by the class

One window for the four classes: the dispatch's readings, the class's selection
of the entry's byte, the entry, the invariant, the consumed-count bound, the
report's base and the trace.  The class enters through `sel`; the staging its
route needs beyond these readings is the class's own (below, for `[`). -/

/-- **The descend inner window, indexed by the dispatch's class.** -/
structure Stage2NoEventWalkDescendWindow (cls : Stage2NoEventWalkDescendClass)
    (K : Stage2NoEventWalkCarry) (mem : Mem) (k : Nat) (s : State)
    (next : Nat) (nextByte : UInt8) : Type where
  /-- The continuation dispatch's own readings. -/
  disp : Stage2NoEventWalkBracketDispatch K k s next nextByte
  /-- The dispatch's byte selects this window's class. -/
  sel : cls.Selects nextByte.toNat
  /-- The entry at `k + 1` is the byte the dispatch read. -/
  bs1 : K.bs[next]? = some nextByte
  /-- The invariant at the dispatch. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The consumed-count bound at the head's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The report's base. -/
  bPos : 1 ≤ K.b
  /-- The trace at the dispatch's carry. -/
  trace : Stage2NoEventWalkTrace K

/-! ### A byte bridge

The chains take the class byte as a `BitVec 8` equality; the window's selection is
a `Nat` equality (or complement).  The byte's `toNat` is already reduced, so the
two are the same fact. -/

/-- A `BitVec 8` inequality from the `Nat` inequality the selection states. -/
private theorem stage2NoEventByte_ne_of_toNat_ne {b c : Nat} (hb : b < 2 ^ 8)
    (hc : c < 2 ^ 8) (h : b ≠ c) :
    BitVec.ofNat 8 b ≠ BitVec.ofNat 8 c := by
  intro he
  apply h
  have h' := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc] at h'
  exact h'

/-! ### The class's entry, for all four classes

Each is the committed `.loopexit` chain at the window's own byte, so the class's
producer's entry point is reached from the dispatch with no new route. -/

/-- **The `[` class's entry**: the dispatch's chain to `if.then35`. -/
theorem stage2NoEventWalkDescendEntry_bracket {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .bracket K mem k s next nextByte) :
    ∃ sE : State,
      Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "if.then35" ∧ Stage2NoEventWalkInv K mem sE := by
  have hsel : nextByte.toNat = 91 := W.sel
  have hb : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 91)) := by
    have h := W.disp.byte
    rw [hsel] at h
    exact h
  have hc := stage2NoEventRow_loopExitBracket (calls := calls) W.inv W.disp.pc hb
  exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩

/-- **The `{` class's entry**: the dispatch's chain to `if.then9.loopexit`. -/
theorem stage2NoEventWalkDescendEntry_brace {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .brace K mem k s next nextByte) :
    ∃ sE : State,
      Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "if.then9.loopexit" ∧ Stage2NoEventWalkInv K mem sE := by
  have hsel : nextByte.toNat = 123 := W.sel
  have hb : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 123)) := by
    have h := W.disp.byte
    rw [hsel] at h
    exact h
  have hc := stage2NoEventRow_loopExitBrace (calls := calls) W.inv W.disp.pc hb
  exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩

/-- **The `"` class's entry**: the dispatch's chain to `string_value.loopexit`. -/
theorem stage2NoEventWalkDescendEntry_string {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .string K mem k s next nextByte) :
    ∃ sE : State,
      Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "string_value.loopexit" ∧ Stage2NoEventWalkInv K mem sE := by
  have hsel : nextByte.toNat = 34 := W.sel
  have hb : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 34)) := by
    have h := W.disp.byte
    rw [hsel] at h
    exact h
  have hc := stage2NoEventRow_loopExitString (calls := calls) W.inv W.disp.pc hb
  exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩

/-- **The scalar class's entry**: the dispatch's chain to `scalar.loopexit`,
through the leaf its pivot range selects. -/
theorem stage2NoEventWalkDescendEntry_scalar {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .scalar K mem k s next nextByte) :
    ∃ sE : State,
      Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = "scalar.loopexit" ∧ Stage2NoEventWalkInv K mem sE := by
  obtain ⟨h34, h91, h123⟩ := W.sel
  have hy34 : BitVec.ofNat 8 nextByte.toNat ≠ BitVec.ofNat 8 34 :=
    stage2NoEventByte_ne_of_toNat_ne (UInt8.toNat_lt nextByte) (by decide) h34
  have hy91 : BitVec.ofNat 8 nextByte.toNat ≠ BitVec.ofNat 8 91 :=
    stage2NoEventByte_ne_of_toNat_ne (UInt8.toNat_lt nextByte) (by decide) h91
  have hy123 : BitVec.ofNat 8 nextByte.toNat ≠ BitVec.ofNat 8 123 :=
    stage2NoEventByte_ne_of_toNat_ne (UInt8.toNat_lt nextByte) (by decide) h123
  obtain ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ :=
    stage2NoEventRow_loopScalar (calls := calls) W.inv W.disp.pc W.disp.byte hy34 hy91 hy123
  · exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩
  · exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩
  · exact ⟨_, hc, rfl, Stage2NoEventWalkChain.inv hc⟩

/-- **The class's entry is reached, at every class.**  The chain is the dispatch's
own `.loopexit` route at the window's byte; the invariant at the entry is the
chain's. -/
theorem Stage2NoEventWalkDescendWindow.entry {calls : Calls} {cls : Stage2NoEventWalkDescendClass}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow cls K mem k s next nextByte) :
    ∃ sE : State,
      Stage2NoEventWalkChain calls mem K s K sE ∧
      sE.pc = cls.entryPc ∧ Stage2NoEventWalkInv K mem sE := by
  cases cls with
  | bracket => exact stage2NoEventWalkDescendEntry_bracket W
  | brace => exact stage2NoEventWalkDescendEntry_brace W
  | string => exact stage2NoEventWalkDescendEntry_string W
  | scalar => exact stage2NoEventWalkDescendEntry_scalar W

/-- **No head holds at a class's entry**: the head's `pc` is `NodeBlock5`, and no
class's `entryPc` is.  This is why the three head-rooted class producers do not
apply at the entry the dispatch's chain reaches. -/
theorem stage2NoEventWalkDescendEntry_notHead {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {sE : State} {cls : Stage2NoEventWalkDescendClass}
    (hpc : sE.pc = cls.entryPc) : ¬ Stage2NoEventWalkHead K mem k sE := by
  intro h
  exact Stage2NoEventWalkDescendClass.entryPc_ne_nodeBlock5 cls (hpc.symm.trans h.pc)

/-! ### The `[` class's staging and the committed window

At `91` the indexed window plus the class's own staging is the committed
`Stage2NoEventWalkBracketInnerWindow`, in both directions.  The staging is exactly
the fields the committed window carries beyond the shared readings: the outer
opener (the token the descend's `if.end` already moved in the registers), the
array stack's cursor cells and their relation, the stack base, the head's two
arena `phi`s, and the advance's room. -/

/-- **The `[` class's own staging**, the committed window's remaining fields. -/
structure Stage2NoEventWalkBracketClassStaging (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Type where
  /-- The outer opener at `k`, whose token and terms the descend's `if.end`
  already moved in the registers. -/
  outerLane : Nat
  outerByte : UInt8
  outerBs : K.bs[outerLane]? = some outerByte
  outerOpen : outerByte.toNat = 91
  /-- The array stack's cursor cell and its bound. -/
  ivIn : BitVec 64
  iv : BitVec 64
  cnt : BitVec 64
  hIVIn : lookupName s.env "%indvars.iv.in" = some (.int 64 ivIn)
  hIV : lookupName s.env "%indvars.iv" = some (.int 64 iv)
  hCnt : lookupName s.env "%wide.trip.count1409" = some (.int 64 cnt)
  ivInLt : (ivIn.signExtend 64).toNat < 520
  ivVal : iv.toNat = (ivIn.signExtend 64).toNat + 1
  ivNe : iv ≠ cnt
  /-- The stack's base. -/
  hStk : lookupName s.env "%stk" = some (.ptr K.stk)
  /-- The head's arena-length and arena-word `phi`s, carried through the descend. -/
  alenPhi : lookupName s.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arenaPhi : lookupName s.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The four-entry advance's room. -/
  live : k + 4 < K.nep

/-- **The committed window from the indexed window at `[`**: the shared readings
and the class's staging. -/
def Stage2NoEventWalkDescendWindow.toBracket {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .bracket K mem k s next nextByte)
    (G : Stage2NoEventWalkBracketClassStaging K k s) :
    Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte where
  disp := W.disp
  byte91 := W.sel
  bs1 := W.bs1
  inv := W.inv
  outerLane := G.outerLane
  outerByte := G.outerByte
  outerBs := G.outerBs
  outerOpen := G.outerOpen
  ivIn := G.ivIn
  iv := G.iv
  cnt := G.cnt
  hIVIn := G.hIVIn
  hIV := G.hIV
  hCnt := G.hCnt
  ivInLt := G.ivInLt
  ivVal := G.ivVal
  ivNe := G.ivNe
  hStk := G.hStk
  alenPhi := G.alenPhi
  arenaPhi := G.arenaPhi
  count := W.count
  live := G.live
  bPos := W.bPos
  trace := W.trace

/-- **The indexed window at `[` from the committed window.** -/
def Stage2NoEventWalkBracketInnerWindow.toDescend {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte) :
    Stage2NoEventWalkDescendWindow .bracket K mem k s next nextByte where
  disp := W.disp
  sel := W.byte91
  bs1 := W.bs1
  inv := W.inv
  count := W.count
  bPos := W.bPos
  trace := W.trace

/-- **The class's staging, from the committed window.** -/
def Stage2NoEventWalkBracketInnerWindow.staging {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte) :
    Stage2NoEventWalkBracketClassStaging K k s where
  outerLane := W.outerLane
  outerByte := W.outerByte
  outerBs := W.outerBs
  outerOpen := W.outerOpen
  ivIn := W.ivIn
  iv := W.iv
  cnt := W.cnt
  hIVIn := W.hIVIn
  hIV := W.hIV
  hCnt := W.hCnt
  ivInLt := W.ivInLt
  ivVal := W.ivVal
  ivNe := W.ivNe
  hStk := W.hStk
  alenPhi := W.alenPhi
  arenaPhi := W.arenaPhi
  live := W.live

/-- **Both roundtrips**: the indexed window at `91` and the committed window carry
the same data.  The staging is not part of the shared window, so the second
roundtrip does not read it. -/
theorem Stage2NoEventWalkBracketInnerWindow.toDescend_toBracket
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte) :
    W.toDescend.toBracket W.staging = W := by
  cases W
  rfl

theorem Stage2NoEventWalkDescendWindow.toBracket_toDescend
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .bracket K mem k s next nextByte)
    (_G : Stage2NoEventWalkBracketClassStaging K k s) :
    (W.toBracket _G).toDescend = W := by
  cases W
  rfl

/-- **The `[` class's route begins at the committed entry**: the rebuilt window
hands the committed first half its entry at `if.end327`. -/
theorem stage2NoEventWalkDescendBracketAt327 {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkDescendWindow .bracket K mem k s next nextByte)
    (G : Stage2NoEventWalkBracketClassStaging K k s) :
    Nonempty (Stage2NoEventWalkBracketInnerAt327 calls K mem k s) :=
  ⟨stage2NoEventWalkBracketInnerTo327 (W.toBracket G)⟩

/-! ### The consequence at `[`

The committed recursion `Stage2NoEventWalkBracketInnerAll` is stated over the
window; the per-dispatch window supply turns it into
`Stage2NoEventWalkBracketInner`, and the committed descend row consumes that. -/

/-- **The `[` class's obligation from the committed recursion**: the window supply
is `…BracketInnerOutElement`'s `hstage` — the caller's staging at every dispatch of
the element's class.  The prefix count is the recursion's own `∀ j`, so the
segment is not read. -/
theorem stage2NoEventWalkBracketInner_of_windowSupply {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (hall : Stage2NoEventWalkBracketInnerAll calls mem K k next nextByte)
    (hstage : ∀ (s₁ : State), Stage2NoEventWalkBracketDispatch K k s₁ next nextByte →
      Nonempty (Stage2NoEventWalkBracketInnerWindow K mem k s₁ next nextByte)) :
    Stage2NoEventWalkBracketInner calls mem K k s next nextByte := by
  intro j0 s₁ hdisp _
  obtain ⟨W⟩ := hstage s₁ hdisp
  exact hall s₁ W j0

/-- **The descend arm's row at `[`**: the head's own segment to the continuation
dispatch, the class's obligation from the committed recursion and window supply,
and the shared cycle's return. -/
noncomputable def stage2NoEventWalkBracketDescendRow_of_windowSupply {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    (hbranch : Stage2NoEventWalkDescendBranch K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hne : nextByte.toNat ≠ 93)
    (hall : Stage2NoEventWalkBracketInnerAll calls mem K k next nextByte)
    (hstage : ∀ (s₁ : State), Stage2NoEventWalkBracketDispatch K k s₁ next nextByte →
      Nonempty (Stage2NoEventWalkBracketInnerWindow K mem k s₁ next nextByte)) :
    Stage2NoEventWalkRow calls mem F K k s :=
  stage2NoEventWalkBracketDescendRow_of_inner h hclass hbranch hk1 hbs1 hne
    (stage2NoEventWalkBracketInner_of_windowSupply hall hstage)

#print axioms Stage2NoEventWalkDescendClass.exists_selects
#print axioms Stage2NoEventWalkDescendClass.selects_unique
#print axioms Stage2NoEventWalkDescendClass.exists_unique_selects
#print axioms Stage2NoEventWalkDescendClass.entryPc_ne_nodeBlock5
#print axioms Stage2NoEventWalkDescendClass.routeAtDispatch_iff
#print axioms stage2NoEventWalkDescendEntry_bracket
#print axioms stage2NoEventWalkDescendEntry_brace
#print axioms stage2NoEventWalkDescendEntry_string
#print axioms stage2NoEventWalkDescendEntry_scalar
#print axioms Stage2NoEventWalkDescendWindow.entry
#print axioms stage2NoEventWalkDescendEntry_notHead
#print axioms Stage2NoEventWalkBracketInnerWindow.toDescend_toBracket
#print axioms Stage2NoEventWalkDescendWindow.toBracket_toDescend
#print axioms stage2NoEventWalkDescendBracketAt327
#print axioms stage2NoEventWalkBracketInner_of_windowSupply
#print axioms stage2NoEventWalkBracketDescendRow_of_windowSupply

end LeanLLVM.Refinement
