/-
The no-event walk's `after_value` decision: the depth-zero terminal lane and the
continuation's stated interface.

`after_value` ends at `%cmp355 = icmp eq %sp.4, 0`.  At depth zero there is no
continuation to take — `Stage2NoEventWalkCycleSrc` requires `sp ≠ 0` — so the row
is terminal, and the "which row" question is the class's: each depth-zero route in
`JsonStage2NoEventWalkRowsContainerZero` leaves the endpoint with `%sp.3 = 0`,
`%frame.4`, `%k.5`, `%alen.7`, `%arena.9`, `%terms.7`, `%tokens.7` and `%nep`
(the bracket pair) or `%dec`, `%k.4`, `%alen.6`, `%arena.8`, `%terms.6`,
`%tokens.6` and `%nep` (the brace pair), at the counts `+7`/`+2` and `+3`/`+2`.
Those are the cells this module takes as the depth-zero arm's entry.

**What is proved.**  Two reductions, one per class (each a `noncomputable def`:
the row is data, so the depth-zero arm is not a proposition):

* `stage2NoEventWalkBracketZeroRow` — the `[]` endpoint cells at the zero depth,
  the head's staging and the caller's acceptance/refusal evidence give the
  bracket terminal row (through `stage2NoEventWalkBracketZeroTerminal`);
* `stage2NoEventWalkBraceZeroRow` — the same for `{}`, through
  `stage2NoEventWalkBraceZeroTerminal`.

Both are reductions: the row's run, credit, exit and boundary are the committed
producers', and the caller's `hreportAcc`/`hboundAcc`/`hreportRef` are the only
evidence the route cannot supply.  The cell bundles are the case-split witness —
they are what places the endpoint on the depth-zero lane rather than the
continuation's — not premises of the producers' own runs, which re-derive the
same cells from the head.

**What is stated, not proved.**  `Stage2NoEventWalkAfterValueCont` is the other
side of `%cmp355`: from a `Stage2NoEventWalkCycleSrc` at the endpoint — the
structure the shared cycle already takes, whose `spNe` is `1 ≤ sp` beside its
`spLt` — the step is one `Stage2NoEventWalkCycle` of index delta one, the shape
`stage2NoEventWalkCycle_of_pair` states at the pair endpoint.  It is a `def`, not
a goal: the committed proof is `stage2NoEventWalkCycle_of_afterValue`, and this
module does not restate it.  An assembly lane cases `%cmp355` and takes either a
reduction above or this interface, rather than improvising the continuation.

Nothing here is wired into `JsonStage2NoEventWalkRowsAssemble`.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerZero
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The endpoint cells the depth-zero routes conclude

Each bundle is exactly the `∃ sE, …` tail of the matching `…ZeroRoute` lemma at
`Stage2NoEventWalkCarry`'s `{ K with tok := K.tok + 2, terms := … }`: the cells
`after_value`'s `phi` run reads, the `%nep` param, and the block's predecessor. -/

/-- **The `[]` endpoint's `after_value` cells at the zero depth.**  These are
`stage2NoEventWalkBracketZeroRoute`'s conclusions at the endpoint state, with the
head's index `k` and the route's carry `K`. -/
structure Stage2NoEventWalkAfterValueBracketCells (K : Stage2NoEventWalkCarry)
    (k : Nat) (sE : State) : Type where
  /-- The endpoint is `after_value`'s entry. -/
  pc : sE.pc = "after_value"
  /-- The edge is `close_arr`'s zero-depth arm. -/
  pre : sE.pre = some "close_arr"
  /-- The frame word (the `[]` tag). -/
  frame4 : lookupName sE.env "%frame.4" = some (.int 8 (BitVec.ofNat 8 1))
  /-- The depth word: zero, so `%cmp355` holds. -/
  sp3 : lookupName sE.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 0))
  /-- The closer's index, `k + 2`. -/
  k5 : lookupName sE.env "%k.5" = some (.int 64 (BitVec.ofNat 64 (k + 2)))
  /-- The arena's length word. -/
  alen7 : lookupName sE.env "%alen.7" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  /-- The arena's running sum. -/
  arena9 : lookupName sE.env "%arena.9" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The terms count, after the pair's seven. -/
  terms7 : lookupName sE.env "%terms.7" =
    some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
  /-- The token count, after the pair's two. -/
  tokens7 : lookupName sE.env "%tokens.7" =
    some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
  /-- The entry count's param. -/
  nep : lookupName sE.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep))

/-- **The `{}` endpoint's `after_value` cells at the zero depth.**  These are
`stage2NoEventWalkBraceZeroRoute`'s conclusions; the brace edge's frame is the
constant zero and its depth word is `%dec`. -/
structure Stage2NoEventWalkAfterValueBraceCells (K : Stage2NoEventWalkCarry)
    (k : Nat) (sE : State) : Type where
  /-- The endpoint is `after_value`'s entry. -/
  pc : sE.pc = "after_value"
  /-- The edge is `close_obj`'s zero-depth arm. -/
  pre : sE.pre = some "close_obj"
  /-- The depth word after the decrement: zero, so `%cmp355` holds. -/
  dec : lookupName sE.env "%dec" = some (.int 32
    (BitVec.ofNat 32 0 + BitVec.ofNat 32 1 + BitVec.ofNat 32 4294967295))
  /-- The closer's index, `k + 2`. -/
  k4 : lookupName sE.env "%k.4" = some (.int 64 (BitVec.ofNat 64 (k + 2)))
  /-- The arena's length word. -/
  alen6 : lookupName sE.env "%alen.6" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  /-- The arena's running sum. -/
  arena8 : lookupName sE.env "%arena.8" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The terms count, after the pair's three. -/
  terms6 : lookupName sE.env "%terms.6" =
    some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3))
  /-- The token count, after the pair's two. -/
  tokens6 : lookupName sE.env "%tokens.6" =
    some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
  /-- The entry count's param. -/
  nep : lookupName sE.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep))

/-! ### The depth-zero arm's two rows

Both reductions take the endpoint's cells, the head's own staging (the opener's
lane and byte, the closer's entry, the head's depth read and the invariant's
bounds) and the caller's two post words plus the refusal's run.  The row is the
committed depth-zero producer's. -/

/-- **The `[]` depth-zero row from the endpoint's cells.**  The `[]` head at
`k`, its depth-zero route's `after_value` cells, and the caller's
`hreportAcc`/`hboundAcc`/`hreportRef` give the terminal row: acceptance when
`k + 2 = K.nep`, refusal otherwise. -/
noncomputable def stage2NoEventWalkBracketZeroRow {gap : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (_hz : Stage2NoEventWalkAfterValueBracketCells K k sE)
    (hreportAcc : Stage2NoEventRun K.a12 mem
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 7) + BitVec.ofNat 64 K.arenaWord)))
    (hboundAcc : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 7) + BitVec.ofNat 64 K.arenaWord))
      (.int 64 1))
    (hreportRef : ∀ q : Nat, K.ent[k + 2]? = some q →
      Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q))) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  -- The endpoint's cells place the walk at `%sp.4 = 0` (`%sp.3` is zero there),
  -- so `%cmp355` holds and the continuation is unavailable (`spNe : sp ≠ 0`).
  -- The row is the depth-zero route's own terminal one, which re-derives these
  -- cells from the head.
  exact stage2NoEventWalkBracketZeroTerminal (gap := gap) (F := F)
    h htrace hk hbs hb hbs1 hb1 hspZ hkbound hk63 hlane hval4lt hbyte1
    hreportAcc hboundAcc hreportRef

/-- **The `{}` depth-zero row from the endpoint's cells.**  The `{}` head at
`k`, its depth-zero route's `after_value` cells, and the caller's
`hreportAcc`/`hboundAcc`/`hreportRef` give the terminal row: acceptance when
`k + 2 = K.nep`, refusal otherwise. -/
noncomputable def stage2NoEventWalkBraceZeroRow {gap : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (_hz : Stage2NoEventWalkAfterValueBraceCells K k sE)
    (hreportAcc : Stage2NoEventRun K.a12 mem
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 K.arenaWord)))
    (hboundAcc : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 K.arenaWord))
      (.int 64 1))
    (hreportRef : ∀ q : Nat, K.ent[k + 2]? = some q →
      Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q))) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  -- The brace endpoint's `%dec` is the zero word, so `%cmp355` holds there too
  -- and the continuation (`Stage2NoEventWalkCycleSrc.spNe`) is not available.
  exact stage2NoEventWalkBraceZeroTerminal (gap := gap) (F := F)
    h htrace hk hbs hb hbs1 hb1 hspZ hkbound hk63 hlane hval4lt hbyte1
    hreportAcc hboundAcc hreportRef

/-! ### The continuation arm's interface

At `1 ≤ sp` — `Stage2NoEventWalkCycleSrc.spNe` beside its `spLt` — the walk is on
the cycle, not the terminal lane.  The interface is stated here so the assembly
cases `%cmp355` against a fixed shape: a `Stage2NoEventWalkCycle` of index delta
one (the after-value path's `%inc379 = %k.6 + 1`), which is
`stage2NoEventWalkCycle_of_pair`'s shape at the pair endpoint and
`stage2NoEventWalkCycle_of_afterValue`'s at this one. -/

/-- **The continuation's interface at the after-value cells.**  Given the
endpoint's `Stage2NoEventWalkCycleSrc` — the invariant at `after_value`, the
dispatch `phi` run, the depth and frame words with `sp ≠ 0`, the index bounds,
the consumed-count bound, the base lookups and the continuation's comma — the
step is one cycle of delta one to the next head.  Stated as a `def`, not a goal:
the committed inhabitant is `stage2NoEventWalkCycle_of_afterValue`. -/
def Stage2NoEventWalkAfterValueCont (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Prop :=
  ∀ (_src : Stage2NoEventWalkCycleSrc calls mem K k s),
    ∃ (s' : State) (p : Nat), Stage2NoEventWalkCycle calls mem K k s 1 s' p

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracketZeroRow
#print axioms stage2NoEventWalkBraceZeroRow

end LeanLLVM.Refinement
