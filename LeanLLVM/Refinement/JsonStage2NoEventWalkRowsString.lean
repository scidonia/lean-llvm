/-
The no-event walk's string class row: the class's route to `after_value`'s entry
and the shared cycle.

A string head is one entry whose document byte is `"` (34).  The class route
consumes it — the dispatch `NodeBlock5 → LeafBlock → string_value` and the
closing entry's test (`if.end216`), the body's extent (`if.end230`), the
`s2_string_body` call and its result's dispatch (`NodeBlock29`, `LeafBlock27`),
and then one of two arms:

* **the arena arm** (`%call243` above one, `for.cond266.preheader`): the walk's
  own byte-sum loop over the decoded body, `JsonStage2NoEventWalkDispatchStringArenaB`'s
  `stage2NoEventWalkStringArenaB_short` (`len < 8`) and `_long` (`8 ≤ len`), whose
  count is `3 + (len + 1) + 2` and `len / 8 + len % 8 + 8` respectively, and whose
  handoff (`cleanup287`) stores one token and the record's `tag + len + payload`;
* **the empty string** (`%call243 = 1`, `do.body254`): the one `strPlain`
  `len = 0` step (`doBody254`'s `%add260`, the plain record's contribution) and
  `cleanup287`'s handoff, two blocks.

Both arms end at `after_value` at index `k + 2` with the class's carry
(`stage2NoEventWalkStringCarry` / `stage2NoEventWalkStringCarryPlain`), and both
record's event and token step the head's trace (`Stage2NoEventWalkTrace.stringStep`
and `stringPlainStep`).  The depth-0 string is not this row: at `%sp.4 = 0`
`after_value` takes the terminal arm, so this row's `CycleSrc` requires a nested
value (`sp ≠ 0`, `frame ≠ 0`), exactly as the container row does.

**What this module owns.**  The composition: given the class's route as one
counted segment from the head to `after_value`'s entry, split into the call's own
slice (`head → the arm's entry`) and the arm's slice (the arm's entry →
`after_value`), this module builds the endpoint's `Stage2NoEventWalkCycleSrc`,
runs the shared cycle `stage2NoEventWalkCycle_of_afterValue`, and concludes
`Stage2NoEventWalkRow.cont` through `stage2NoEventWalkRow_cont_of_afterValue`.
The price is proved from the two slices' measured counts against the potential's
fall over the two consumed entries, `32·2 + 8·(q − lane)`.

**What the committed slices do not expose (named, not faked).**  Two bridges
stand between the class's slices and the endpoint the cycle starts at:

* `JsonStage2NoEventWalkString`'s call row (`ifEnd239_step`) deliberately claims
  no invariant: the block stores at `%outn205` and hands the callee a memory
  outside the invariant's run regions, so the endpoint's invariant is the
  class route's fact, carried by the segment (`Stage2NoEventWalkSegment.inv'`),
  not a projection of the head.  The helper's own frame
  (`s2StringBodyBody_contract`'s `UnchangedOutside`) is what a caller uses to
  rebuild it;
* `stage2NoEventWalkStringArenaB_short`/`_long` state the endpoint's four
  acceptance cells (`%alen.4`, `%arena.6`, `%tokens.4`, `%terms.4`) existentially,
  not the three registers `after_value`'s `phi` run also selects at the
  `cleanup287` edge (`%frame.0.lcssa1099`, `%sp.0.lcssa1093.wide`, `%inc217`).
  A producer from a bare `Head` needs them; they are the route's dispatch window
  (`Stage2NoEventWalkStringAfter`) here.

The price and the credit are still proved: the route's own count is what is
priced, so the row does not depend on the advertised bounds of the slices.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerB
import LeanLLVM.Refinement.JsonStage2NoEventWalkDispatchStringArenaB
import LeanLLVM.Refinement.JsonStage2NoEventWalkString
import LeanLLVM.Refinement.JsonStage2NoEventWalkValue

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The endpoint's dispatch window

`after_value`'s `phi` run at the `cleanup287` edge selects seven registers: the
class route's three survivors (`%frame.0.lcssa1099`, `%sp.0.lcssa1093.wide`,
`%inc217`) and the handoff's four (`%alen.4`, `%arena.6`, `%terms.4`,
`%tokens.4`).  The window states the selection at the class's own values; it is
the cycle source's `phiRun`, not a second dispatch. -/

/-- **`after_value`'s `phi` window at the string class's endpoint**: the
`cleanup287` edge, at the class's frame, depth, index and carry. -/
def Stage2NoEventWalkStringAfter (Kc : Stage2NoEventWalkCarry) (kc : Nat) (fr sp : Nat)
    (s : State) : Prop :=
  ∃ p, s.pre = some p ∧
    PhiSelects (stateAt s.env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 kc)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 Kc.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 Kc.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 Kc.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 Kc.tok))]

/-! ### The class route's data

The route is two counted segments: the call's own slice (the head to the arm's
entry, at the head's carry) and the arm's slice (the arm's entry to
`after_value`, at the class's carry).  The two counts are kept apart so the
composed price is the sum of the measured pieces, not a class advert. -/

/-- **The string class's route to the after-value endpoint.**  `segHead` is the
call's slice (dispatch, `string_value`, `if.end216`, `if.end230`, the call and
the result dispatch to the arm's entry) at `jHead`; `segTail` is the arm's slice
to `after_value` at `jTail`.  `lane` is the entry's lane and `q` the next-next
entry (the comma the cycle reads), so the two consumed entries are
`[lane, q)`.  The endpoint's invariant rides in `segTail`. -/
structure Stage2NoEventWalkStringRoute (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The carry the string class builds. -/
  Kc : Stage2NoEventWalkCarry
  /-- The arm's entry: `for.cond266.preheader` on the arena arm, `do.body254` on
  the empty string's. -/
  sMid : State
  /-- The state at `after_value`'s entry. -/
  sA : State
  /-- The call's own slice's count. -/
  jHead : Nat
  /-- The arm's slice's count. -/
  jTail : Nat
  /-- The entry's lane. -/
  lane : Nat
  /-- The decoded body's length. -/
  len : Nat
  /-- The next-next entry: the comma the cycle reads. -/
  q : Nat
  /-- The call's own slice is eight blocks: the two-link dispatch, the
  `string_value` merge, the three routing blocks and the two-block result
  dispatch. -/
  headBound : jHead ≤ 8
  /-- The two consumed entries span at least the body's `len + 2` bytes. -/
  deltaLe : len + 2 ≤ q - lane
  /-- The frame word at the endpoint. -/
  frame : Nat
  /-- The depth word at the endpoint. -/
  sp : Nat
  /-- The call's own slice, at the head's carry. -/
  segHead : Stage2NoEventWalkSegment calls mem K s K sMid jHead
  /-- The arm's slice, to the class's carry. -/
  segTail : Stage2NoEventWalkSegment calls mem K sMid Kc sA jTail
  /-- `after_value` is the next block. -/
  pc : sA.pc = "after_value"
  /-- The endpoint's dispatch window. -/
  after : Stage2NoEventWalkStringAfter Kc (k + 2) frame sp sA
  frameLt : frame < 2 ^ 8
  frameNe : frame ≠ 0
  spLt : sp < 2 ^ 32
  spNe : sp ≠ 0
  /-- The next head's index fits the address arithmetic. -/
  kAddr : k + 3 < 2 ^ 63
  /-- The next head exists. -/
  klt : k + 3 < Kc.nep
  /-- The head's entry and the comma's. -/
  laneEq : K.ent[k]? = some lane
  qEq : K.ent[k + 2]? = some q
  laneLeQ : lane ≤ q
  qLeN : q ≤ K.n
  /-- The class consumes exactly one token. -/
  tokEq : Kc.tok = K.tok + 1
  /-- The class's three static numbers do not move. -/
  nepEq : Kc.nep = K.nep
  nEq : Kc.n = K.n
  entEq : Kc.ent = K.ent
  a12Eq : Kc.a12 = K.a12
  next0Eq : Kc.next0 = K.next0
  /-- The entry chain's stable live-ins survived the route. -/
  base : Stage2NoEventWalkBaseLookups Kc sA
  bPos : 1 ≤ Kc.b
  /-- The route's output evidence. -/
  trace : Stage2NoEventWalkTrace Kc
  /-- The byte at the endpoint's index is the comma the cycle reads. -/
  comma : ∀ m, Kc.ent[k + 2]? = some m → Kc.bs.getD m 0 = 44

/-! ### The potential across the string pair

The route advances two entries and consumes the two quote positions, so the
credit is `32·2 + 8·(q − lane)`: two entries' allowance plus the byte term the
body's extent accounts for. -/

/-- **The potential's string-pair fall.**  `Φ K k − Φ Kc (k + 2)` is exactly
`32·2 + 8·(q − lane)` when the entries are `lane` at `k` and `q` at `k + 2`. -/
theorem stage2NoEventWalkStringPotential {K Kc : Stage2NoEventWalkCarry}
    {k lane q : Nat}
    (hk : k + 2 ≤ K.nep) (hlane : K.ent[k]? = some lane)
    (hq : K.ent[k + 2]? = some q) (hlq : lane ≤ q) (hqN : q ≤ K.n)
    (hnep : Kc.nep = K.nep) (hn : Kc.n = K.n) (hent : Kc.ent = K.ent) :
    stage2NoEventWalkPotential K k =
      stage2NoEventWalkPotential Kc (k + 2) + (32 * 2 + 8 * (q - lane)) := by
  have hlane' : K.ent.getD k 0 = lane := by
    rw [List.getD_eq_getElem?_getD, hlane]; rfl
  have hq' : K.ent.getD (k + 2) 0 = q := by
    rw [List.getD_eq_getElem?_getD, hq]; rfl
  unfold stage2NoEventWalkPotential
  rw [hnep, hn, hent, hlane', hq']
  omega

/-! ### The row

The endpoint's `CycleSrc`, the shared cycle, and the generic seam. -/

/-- **The string class's continuing row from its route.**  The route's segment
is the head-to-`after_value` run with the endpoint's invariant; this builds the
endpoint's `CycleSrc` from the dispatch window and the continuation facts, runs
the shared cycle, and concludes the row.  The price is the route's own count
against the potential's fall (`hcredit`); the two arms below discharge it from
their measured slice counts. -/
noncomputable def stage2NoEventWalkStringRow_cont_of_route {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (_htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkStringRoute calls mem K k s)
    (hcredit : route.jHead + route.jTail +
      stage2NoEventWalkPotential route.Kc (k + 2) ≤
        stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  -- the endpoint's liveness and the consumed count
  have hklt : k + 2 + 1 < route.Kc.nep := by
    have := route.klt
    omega
  have hkaddr : k + 2 + 1 < 2 ^ 63 := by
    have := route.kAddr
    omega
  have hcount : Stage2NoEventWalkCount route.Kc (k + 2) := by
    have hc := h.count
    unfold Stage2NoEventWalkCount at hc ⊢
    rw [route.tokEq]
    omega
  -- the endpoint's `CycleSrc`
  have hsrc : Stage2NoEventWalkCycleSrc calls mem route.Kc (k + 2) route.sA :=
    { inv := route.segTail.inv'
      pc := route.pc
      frame := route.frame
      frameLt := route.frameLt
      frameNe := route.frameNe
      sp := route.sp
      spLt := route.spLt
      spNe := route.spNe
      kAddr := hkaddr
      klt := hklt
      count := hcount
      phiRun := route.after
      baseLookups := route.base
      bPos := route.bPos
      trace := route.trace
      comma := route.comma }
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' : State := Classical.choose cw
  let p : Nat := Classical.choose (Classical.choose_spec cw)
  have hcyc : Stage2NoEventWalkCycle calls mem route.Kc (k + 2) route.sA 1 s' p :=
    Classical.choose_spec (Classical.choose_spec cw)
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F)
    (route.segHead.trans route.segTail) hsrc hcyc
    route.nepEq route.a12Eq route.next0Eq (by omega) ?_
  exact hcredit

/-! ### The two arms' prices

The call's own slice is eight blocks on both arms (the two-link dispatch, the
`string_value` merge, the three routing blocks, the two-block result dispatch).  The arena arm's tail is
the arena slice's published count; the empty string's is the two-block plain
handoff.  In both, the two consumed entries leave at least `len + 2` bytes at
the endpoint, so the credit is far above the price. -/

/-- **The arena arm at a body shorter than eight bytes.**  The tail is the committed arena
slice's `_short` count, `3 + (len + 1) + 2`; the price is inside the two entries'
allowance. -/
noncomputable def stage2NoEventWalkStringRow_short {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkStringRoute calls mem K k s)
    (hj : route.jTail ≤ 3 + (route.len + 1) + 2) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hhead := route.headBound
  have hdelta := route.deltaLe
  refine stage2NoEventWalkStringRow_cont_of_route h htrace route ?_
  have hpot := stage2NoEventWalkStringPotential (K := K) (Kc := route.Kc)
    (k := k) (lane := route.lane) (q := route.q)
    (by have := route.klt; rw [route.nepEq] at this; omega)
    route.laneEq route.qEq route.laneLeQ route.qLeN
    route.nepEq route.nEq route.entEq
  omega

/-- **The arena arm at a body of at least eight bytes.**  The tail is the committed arena
slice's `_long` count, `len / 8 + len % 8 + 8`; `len / 8 + len % 8 ≤ len`, so the
price is still inside the two entries' allowance. -/
noncomputable def stage2NoEventWalkStringRow_long {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkStringRoute calls mem K k s)
    (hj : route.jTail ≤ route.len / 8 + route.len % 8 + 8) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hdm := Nat.div_add_mod route.len 8
  have hle : route.len / 8 + route.len % 8 ≤ route.len := by omega
  have hhead := route.headBound
  have hdelta := route.deltaLe
  refine stage2NoEventWalkStringRow_cont_of_route h htrace route ?_
  have hpot := stage2NoEventWalkStringPotential (K := K) (Kc := route.Kc)
    (k := k) (lane := route.lane) (q := route.q)
    (by have := route.klt; rw [route.nepEq] at this; omega)
    route.laneEq route.qEq route.laneLeQ route.qLeN
    route.nepEq route.nEq route.entEq
  omega

/-- **The empty string.**  The tail is `do.body254`'s `strPlain` step and the
`cleanup287` handoff, two blocks; the credit's two entries' allowance (`64`) is
far above `8 + 2`. -/
noncomputable def stage2NoEventWalkStringRow_plain {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkStringRoute calls mem K k s)
    (hj : route.jTail ≤ 2) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hhead := route.headBound
  have hdelta := route.deltaLe
  refine stage2NoEventWalkStringRow_cont_of_route h htrace route ?_
  have hpot := stage2NoEventWalkStringPotential (K := K) (Kc := route.Kc)
    (k := k) (lane := route.lane) (q := route.q)
    (by have := route.klt; rw [route.nepEq] at this; omega)
    route.laneEq route.qEq route.laneLeQ route.qLeN
    route.nepEq route.nEq route.entEq
  omega

/-! ### The class's carry and the trace

Both arms build the same carry vocabulary: the arena arm appends the decoded body
to the logical arena (and its byte sum to the arena word), the empty string
leaves both where they were.  The target trace is the source's stepped by the
class's own record and token. -/

/-- **The arena arm's route bundle**: the class route with the target carry and
the trace built from the head's prefix, the class's decode facts and the class's
token.  The caller's hypotheses are the slices and the endpoint. -/
noncomputable def stage2NoEventWalkStringRoute_arena {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (htrace : Stage2NoEventWalkTrace K)
    {sMid sA : State} {jHead jTail lane len q frame sp : Nat}
    {body : List UInt8} {cs : List Nat} {nextLane : Nat}
    (hsegHead : Stage2NoEventWalkSegment calls mem K s K sMid jHead)
    (hsegTail : Stage2NoEventWalkSegment calls mem K sMid
      (stage2NoEventWalkStringCarry K len body) sA jTail)
    (hpc : sA.pc = "after_value")
    (hafter : Stage2NoEventWalkStringAfter
      (stage2NoEventWalkStringCarry K len body) (k + 2) frame sp sA)
    (hframeLt : frame < 2 ^ 8) (hframeNe : frame ≠ 0)
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkAddr : k + 3 < 2 ^ 63)
    (hklt : k + 3 < (stage2NoEventWalkStringCarry K len body).nep)
    (hlane : K.ent[k]? = some lane) (hq : K.ent[k + 2]? = some q)
    (hlq : lane ≤ q) (hqN : q ≤ K.n)
    (hheadBound : jHead ≤ 8) (hdelta : len + 2 ≤ q - lane)
    (hbase : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkStringCarry K len body) sA)
    (hbPos : 1 ≤ (stage2NoEventWalkStringCarry K len body).b)
    (hcomma : ∀ m, (stage2NoEventWalkStringCarry K len body).ent[k + 2]? = some m →
      (stage2NoEventWalkStringCarry K len body).bs.getD m 0 = 44)
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbodyLen : body.length = len)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs) :
    Stage2NoEventWalkStringRoute calls mem K k s :=
  { Kc := stage2NoEventWalkStringCarry K len body
    sMid := sMid
    sA := sA
    jHead := jHead
    jTail := jTail
    lane := lane
    len := len
    q := q
    frame := frame
    sp := sp
    segHead := hsegHead
    segTail := hsegTail
    pc := hpc
    after := hafter
    frameLt := hframeLt
    frameNe := hframeNe
    spLt := hspLt
    spNe := hspNe
    kAddr := hkAddr
    klt := hklt
    laneEq := hlane
    qEq := hq
    laneLeQ := hlq
    qLeN := hqN
    headBound := hheadBound
    deltaLe := hdelta
    tokEq := rfl
    nepEq := rfl
    nEq := rfl
    entEq := rfl
    a12Eq := rfl
    next0Eq := rfl
    base := hbase
    bPos := hbPos
    trace := Stage2NoEventWalkTrace.stringStep htrace hquote hspan hcode hbelow
      hbodyLen hdecode
    comma := hcomma }

/-- **The empty string's route bundle.**  The target carry is the plain record's
(the arena and its word unchanged); the trace is the source's with the
`strPlain len = 0` record appended. -/
noncomputable def stage2NoEventWalkStringRoute_plain {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (htrace : Stage2NoEventWalkTrace K)
    {sMid sA : State} {jHead jTail lane q frame sp : Nat}
    (hsegHead : Stage2NoEventWalkSegment calls mem K s K sMid jHead)
    (hsegTail : Stage2NoEventWalkSegment calls mem K sMid
      (stage2NoEventWalkStringCarryPlain K lane) sA jTail)
    (hpc : sA.pc = "after_value")
    (hafter : Stage2NoEventWalkStringAfter
      (stage2NoEventWalkStringCarryPlain K lane) (k + 2) frame sp sA)
    (hframeLt : frame < 2 ^ 8) (hframeNe : frame ≠ 0)
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkAddr : k + 3 < 2 ^ 63)
    (hklt : k + 3 < (stage2NoEventWalkStringCarryPlain K lane).nep)
    (hlane : K.ent[k]? = some lane) (hq : K.ent[k + 2]? = some q)
    (hlq : lane ≤ q) (hqN : q ≤ K.n)
    (hheadBound : jHead ≤ 8) (hdelta : 0 + 2 ≤ q - lane)
    (hbase : Stage2NoEventWalkBaseLookups
      (stage2NoEventWalkStringCarryPlain K lane) sA)
    (hbPos : 1 ≤ (stage2NoEventWalkStringCarryPlain K lane).b)
    (hcomma : ∀ m, (stage2NoEventWalkStringCarryPlain K lane).ent[k + 2]? = some m →
      (stage2NoEventWalkStringCarryPlain K lane).bs.getD m 0 = 44)
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hcode : bodyCodePoints K.bs ⟨lane, lane + 2⟩ = some []) :
    Stage2NoEventWalkStringRoute calls mem K k s :=
  { Kc := stage2NoEventWalkStringCarryPlain K lane
    sMid := sMid
    sA := sA
    jHead := jHead
    jTail := jTail
    lane := lane
    len := 0
    q := q
    frame := frame
    sp := sp
    segHead := hsegHead
    segTail := hsegTail
    pc := hpc
    after := hafter
    frameLt := hframeLt
    frameNe := hframeNe
    spLt := hspLt
    spNe := hspNe
    kAddr := hkAddr
    klt := hklt
    laneEq := hlane
    qEq := hq
    laneLeQ := hlq
    qLeN := hqN
    headBound := hheadBound
    deltaLe := hdelta
    tokEq := rfl
    nepEq := rfl
    nEq := rfl
    entEq := rfl
    a12Eq := rfl
    next0Eq := rfl
    base := hbase
    bPos := hbPos
    trace := Stage2NoEventWalkTrace.stringPlainStep htrace hquote hcode
    comma := hcomma }


/-! ### The empty string's handoff

`do.body254` (`strPlain`, `len = 0`) branches to `cleanup287`, whose `phi` run at
that edge selects the arena's length and word (unchanged) and `%add260` (the plain
record's contribution), then stores one token and adds the contribution to
`%terms`.  The loop-exit edge is the committed `arenaBCleanup287_step`; the plain
edge is proved here, and it is what makes the empty string's arm the two blocks
`do.body254` + `cleanup287`, not the byte-sum loop. -/

/-- **`cleanup287` at the `do.body254` edge**: the plain record's three `phi`
operands, the token's increment, the terms' addition and the `lifetime.end`
marker, to `after_value`. -/
theorem stage2NoEventWalkCleanup287Plain_denote {gap : Calls} (env : Env) (s : State)
    {alen arena pn tokens terms outn : Nat}
    (hpre : s.pre = some "do.body254")
    (halen : lookupName env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.0.ph1406" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hpn : lookupName env "%add260" = some (.int 64 (BitVec.ofNat 64 pn)))
    (htok : lookupName env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName env "%outn205" = some (.ptr outn)) :
    denoteCode (stage2NoEventCalls gap) arenaBCleanup287Instrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup287TailCells pn tokens terms)
        (cells (arenaBCleanup287PhiCells alen arena pn) env)) s) := by
  have hsel : ArenaBPhiSelects (stateAt env s) "do.body254"
      arenaBCleanup287PhiSpecs (arenaBCleanup287PhiCells alen arena pn).reverse := by
    refine ArenaBPhiSelects.cons (op := .reg "%alen.0.ph1405") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
        (ArenaBPhiSelects.cons (op := .reg "%add260") (by decide) ?_
          ArenaBPhiSelects.nil))
    · exact arenaB_phiSel_reg hpre (by decide) halen
    · exact arenaB_phiSel_reg hpre (by decide) harena
    · exact arenaB_phiSel_reg hpre (by decide) hpn
  simp only [arenaBCleanup287Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s) (p := "do.body254")
    hpre hsel (by decide)]
  change denoteCode (stage2NoEventCalls gap) arenaBCleanup287TailInstrs
      (stateAt (cells (arenaBCleanup287PhiCells alen arena pn) env) s) = _
  simp only [arenaBCleanup287TailInstrs]
  rw [denoteCode_add_imm (calls := stage2NoEventCalls gap) (env := _) (s := s)
    (d := "%tokens.4") (a := "%tokens.0.lcssa1075")
    (x := BitVec.ofNat 64 tokens) (c := BitVec.ofNat 64 1) (by block_lk)]
  rw [denoteCode_add_reg (calls := stage2NoEventCalls gap) (env := _) (s := s)
    (d := "%terms.4") (a := "%add260.pn") (b := "%terms.0.lcssa1081")
    (x := BitVec.ofNat 64 pn) (y := BitVec.ofNat 64 terms)
    (by block_lk) (by block_lk)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap) (env := _) (s := s)
    (p := "%outn205") (sz := 8) (a := outn) (by block_lk)]
  simp only [arenaBCleanup287TailCells, cells, arenaB_ofNat_add, denoteCode,
    denoteRun, State.bindAll]

/-- **`cleanup287`'s step at the `do.body254` edge.** -/
theorem stage2NoEventWalkCleanup287Plain_step {gap : Calls} {s : State}
    {alen arena pn tokens terms outn : Nat}
    (hpc : s.pc = "cleanup287") (hpre : s.pre = some "do.body254")
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hpn : lookupName s.env "%add260" = some (.int 64 (BitVec.ofNat 64 pn)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn)) :
    step (stage2NoEventCalls gap) stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBCleanup287TailCells pn tokens terms)
          (cells (arenaBCleanup287PhiCells alen arena pn) s.env)) s "after_value") := by
  have hcode := stage2NoEventWalkCleanup287Plain_denote (gap := gap) (env := s.env)
    (s := s) hpre halen harena hpn htok hterms houtn
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBCleanup287Block_find)
    (by simpa only [stateAt, arenaBCleanup287Block] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **The empty-string carry's invariant.**  The plain record changes only the
token count and the terms; every other invariant field is the source's, and the
arena's word is where it was. -/
theorem Stage2NoEventWalkInv.stringPlain {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {lane : Nat} (h : Stage2NoEventWalkInv K mem s)
    (htok : K.tok + 1 ≤ K.n) :
    Stage2NoEventWalkInv (stage2NoEventWalkStringCarryPlain K lane) mem s := by
  unfold stage2NoEventWalkStringCarryPlain
  exact { h with tokLe := htok, arenaEq := h.arenaEq }

/-- **The plain record's terms word.**  `%add260` is `tag + 0 + plainSpan`, the
plain record's contribution, up to the addition's order. -/
theorem stage2NoEventWalkStringPlainTerms (lane terms : Nat) :
    ((lane + 1) + 9223372036854775814) + terms =
      terms + (EventRecord.tagStr + 0 + plainSpan (lane + 1)) := by
  simp only [plainSpan, EventRecord.tagStr]
  omega

/-- **The empty string's arm end to end.**  From the state at `do.body254`'s
entry, the `strPlain len = 0` step and the `cleanup287` handoff are two blocks to
`after_value`'s entry, at the plain carry; the endpoint's invariant is the source's
(the route writes no memory), the `phi` window is the plain handoff's, and the
segment carries the endpoint's invariant. -/
theorem stage2NoEventWalkStringPlainTail {gap : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {lane fr sp outn : Nat}
    (hinv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "do.body254")
    (hlc : lookupName s.env "%.lcssa1125" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hsub : lookupName s.env "%sub234" = some (.int 64 (BitVec.ofNat 64 0)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hframe : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hinc217 : lookupName s.env "%inc217" = some (.int 64 (BitVec.ofNat 64 (k + 2))))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hlaneLt : lane < 2 ^ 32) (hlane1 : lane + 1 < 2 ^ 32)
    (htokN : K.tok + 1 ≤ K.n) :
    ∃ (sA : State) (j : Nat), j ≤ 2 ∧
      Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s
        (stage2NoEventWalkStringCarryPlain K lane) sA j ∧
      sA.pc = "after_value" ∧
      Stage2NoEventWalkStringAfter (stage2NoEventWalkStringCarryPlain K lane) (k + 2)
        fr sp sA ∧
      Stage2NoEventWalkInv (stage2NoEventWalkStringCarryPlain K lane) mem sA ∧
      Stage2NoEventWalkBaseLookups K sA := by
  -- the `strPlain` step
  let s1 : State := stage2NoEventWalkNext
    (("%add260", .int 64
        (((BitVec.ofNat 64
            ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat +
            BitVec.ofNat 64 9223372036854775814) + BitVec.ofNat 64 0))) ::
      ("%or259", .int 64
        (BitVec.ofNat 64 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat +
          BitVec.ofNat 64 9223372036854775814)) ::
      ("%conv258", .int 64
        (BitVec.ofNat 64 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat)) ::
      ("%add257", .int 32 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1)) :: s.env)
    s "cleanup287"
  have hstep1 : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump s1 := by
    simpa only [s1] using
      doBody254_step (calls := stage2NoEventCalls gap) (s := s) hpc hlc hsub
  have h1pc : s1.pc = "cleanup287" := by simp only [s1, stage2NoEventWalkNext]
  have h1pre : s1.pre = some "do.body254" := by
    simp only [s1, stage2NoEventWalkNext, hpc]
  -- the plain contribution's value and the survivors' lookups
  have hlcToNat : ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat = lane + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlaneLt, Nat.mod_eq_of_lt (by decide : (1 : Nat) < 2 ^ 32),
      Nat.mod_eq_of_lt hlane1]
  have hadd260 : (((BitVec.ofNat 64
        ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat +
        BitVec.ofNat 64 9223372036854775814) + BitVec.ofNat 64 0)) =
      BitVec.ofNat 64 ((lane + 1) + 9223372036854775814) := by
    rw [hlcToNat, arenaB_ofNat_add, arenaB_ofNat_add]
  have h1add260 : lookupName s1.env "%add260" =
      some (.int 64 (BitVec.ofNat 64 ((lane + 1) + 9223372036854775814))) := by
    simp only [s1, stage2NoEventWalkNext]
    rw [lookupName_cons_self]
    rw [hadd260]
  have h1alen : lookupName s1.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [s1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have h1arena : lookupName s1.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [s1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have h1tok : lookupName s1.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [s1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have h1terms : lookupName s1.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [s1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have h1outn : lookupName s1.env "%outn205" = some (.ptr outn) := by
    simp only [s1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  -- the handoff
  have hstep2 := stage2NoEventWalkCleanup287Plain_step (gap := gap) (s := s1)
    (alen := K.arena.length) (arena := K.arenaWord)
    (pn := (lane + 1) + 9223372036854775814)
    (tokens := K.tok) (terms := K.terms) (outn := outn)
    h1pc h1pre h1alen h1arena h1add260 h1tok h1terms h1outn
  let sA : State := stage2NoEventWalkNext
    (cells (arenaBCleanup287TailCells ((lane + 1) + 9223372036854775814) K.tok K.terms)
      (cells (arenaBCleanup287PhiCells K.arena.length K.arenaWord
        ((lane + 1) + 9223372036854775814)) s1.env))
    s1 "after_value"
  have hstep2' : step (stage2NoEventCalls gap) stage2NoEventBody s1 = .jump sA := by
    simpa only [sA] using hstep2
  have hpcA : sA.pc = "after_value" := by simp only [sA, stage2NoEventWalkNext]
  have hmemA : sA.mem = s.mem := by
    simp only [sA, s1, stage2NoEventWalkNext]
  -- the endpoint's four handoff cells and the three survivors
  have hAalen : lookupName sA.env "%alen.4" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [sA, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hAarena : lookupName sA.env "%arena.6" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [sA, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hAtok : lookupName sA.env "%tokens.4" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [sA, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hAterms : lookupName sA.env "%terms.4" =
      some (.int 64 (BitVec.ofNat 64
        (((lane + 1) + 9223372036854775814) + K.terms))) := by
    simp only [sA, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_self]
  have hAterms' : lookupName sA.env "%terms.4" =
      some (.int 64 (BitVec.ofNat 64
        (stage2NoEventWalkStringCarryPlain K lane).terms)) := by
    rw [hAterms]
    have hnat : ((lane + 1) + 9223372036854775814) + K.terms =
        (stage2NoEventWalkStringCarryPlain K lane).terms := by
      rw [show (stage2NoEventWalkStringCarryPlain K lane).terms =
        K.terms + (EventRecord.tagStr + 0 + plainSpan (lane + 1)) from rfl]
      exact stage2NoEventWalkStringPlainTerms lane K.terms
    rw [hnat]
  have hAalen' : lookupName sA.env "%alen.4" =
      some (.int 64 (BitVec.ofNat 64
        (stage2NoEventWalkStringCarryPlain K lane).arena.length)) := by
    rw [hAalen]; rfl
  have hAarena' : lookupName sA.env "%arena.6" =
      some (.int 64 (BitVec.ofNat 64
        (stage2NoEventWalkStringCarryPlain K lane).arenaWord)) := by
    rw [hAarena]; rfl
  have hAtok' : lookupName sA.env "%tokens.4" =
      some (.int 64 (BitVec.ofNat 64
        (stage2NoEventWalkStringCarryPlain K lane).tok)) := by
    rw [hAtok]; rfl
  have hAframe : lookupName sA.env "%frame.0.lcssa1099" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    simp only [sA, s1, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hframe
  have hAsp : lookupName sA.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [sA, s1, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hAinc217 : lookupName sA.env "%inc217" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [sA, s1, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc217
  -- the endpoint's `phi` window
  have hAafter : Stage2NoEventWalkStringAfter
      (stage2NoEventWalkStringCarryPlain K lane) (k + 2) fr sp sA := by
    refine ⟨"cleanup287", rfl, ?_⟩
    refine PhiSelects.cons (op := .reg "%frame.0.lcssa1099") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.0.lcssa1093.wide") (by decide) ?_
        (PhiSelects.cons (op := .reg "%inc217") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.4") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.6") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.4") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.4") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hAframe, hAsp, hAinc217, hAalen', hAarena',
        hAterms', hAtok']
  -- the endpoint's invariant: the route writes no memory
  have hinvA : Stage2NoEventWalkInv (stage2NoEventWalkStringCarryPlain K lane) mem sA :=
    (Stage2NoEventWalkInv.stringPlain hinv htokN).mem_congr hmemA
  -- the two-block run
  have hrun : ∀ n, runFuel (stage2NoEventCalls gap) (2 + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sA := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      arenaB_runFuel_jump hstep1 (1 + n), arenaB_runFuel_jump hstep2' n]
  -- the base lookups through the two handoff blocks' cell layers
  have hbaseA : Stage2NoEventWalkBaseLookups K sA := by
    have hb1 := stage2NoEventCycleBase (K := K) hbase
      (cs := [("%add260", .int 64
          (((BitVec.ofNat 64
              ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat +
              BitVec.ofNat 64 9223372036854775814) + BitVec.ofNat 64 0))),
        ("%or259", .int 64
          (BitVec.ofNat 64 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat +
            BitVec.ofNat 64 9223372036854775814)),
        ("%conv258", .int 64
          (BitVec.ofNat 64 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1).toNat)),
        ("%add257", .int 32 ((BitVec.ofNat 32 lane) + BitVec.ofNat 32 1))])
      (names := ["%add260", "%or259", "%conv258", "%add257"]) rfl (by decide)
    have hb2 := stage2NoEventCycleBase (K := K) hb1
      (cs := arenaBCleanup287PhiCells K.arena.length K.arenaWord
        ((lane + 1) + 9223372036854775814))
      (names := (arenaBCleanup287PhiCells K.arena.length K.arenaWord
        ((lane + 1) + 9223372036854775814)).map (·.1)) rfl
      (by simp only [arenaBCleanup287PhiCells, List.map_cons, List.map_nil]; decide)
    have hb3 := stage2NoEventCycleBase (K := K) hb2
      (cs := arenaBCleanup287TailCells ((lane + 1) + 9223372036854775814) K.tok
        K.terms)
      (names := (arenaBCleanup287TailCells ((lane + 1) + 9223372036854775814) K.tok
        K.terms).map (·.1)) rfl
      (by simp only [arenaBCleanup287TailCells, List.map_cons, List.map_nil]; decide)
    simpa only [sA, s1, stage2NoEventWalkNext, cells, Stage2NoEventWalkBaseLookups] using hb3
  exact ⟨sA, 2, le_rfl, ⟨hrun, hinvA⟩, hpcA, hAafter, hinvA, hbaseA⟩


/-! ### The run's memory inside its own regions

A step of the walk writes only inside the run's regions (`stage2NoEventRunRegions`
plus the bootstrap interval), so an invariant stated at a fixed memory survives a
run whose writes stay there and whose regions stay present.  This is the bridge a
class route uses after a call: the callee's frame covers its footprint, the
footprint is inside the regions, and presence is the caller's staging. -/

/-- **Presence after a write**: a byte is present if it was, or if the write
reached it. -/
theorem stage2NoEventWalkPresent_writeBytes {mem : Mem} {a : Nat} {bs : List UInt8}
    {x : Nat} :
    present (writeBytes mem a bs) x ↔
      present mem x ∨ (a ≤ x ∧ x < a + bs.length) := by
  constructor
  · intro hp
    by_cases hin : a ≤ x ∧ x < a + bs.length
    · exact Or.inr hin
    · left
      have hout : x < a ∨ a + bs.length ≤ x := by omega
      obtain ⟨b, hb⟩ := hp
      refine ⟨b, ?_⟩
      rw [readByte_writeBytes_outside mem bs (start := a) (addr := x) hout] at hb
      exact hb
  · rintro (hp | ⟨hle, hlt⟩)
    · exact present_writeBytes mem a bs hp
    · refine ⟨bs.getD (x - a) 0, ?_⟩
      have hx : x = a + (x - a) := (Nat.add_sub_of_le hle).symm
      rw [hx, readByte_writeBytes_at mem bs a (x - a) (by omega),
        Nat.add_sub_cancel_left]

/-- **The invariant across a run inside its own regions.**  The invariant's
static memory facts are stated at `mem`, so only its two state-memory clauses
move: the run keeps the regions present and changes nothing outside them. -/
theorem Stage2NoEventWalkInv.of_frame {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s s' : State} (h : Stage2NoEventWalkInv K mem s)
    (hpres : ∀ a,
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present s'.mem a)
    (hframe : UnchangedOutside mem s'.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)])) :
    Stage2NoEventWalkInv K mem s' :=
  { h with walkPresent := hpres, walkFrame := hframe }

/-- **The empty-string arm's invariant after the route's writes**: the plain
handoff writes no memory, so the target's invariant is the source's at the same
carry, transported to the target's state. -/
theorem Stage2NoEventWalkInv.stringPlain_mem_congr {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s s' : State} {lane : Nat} (h : Stage2NoEventWalkInv K mem s)
    (htok : K.tok + 1 ≤ K.n) (hm : s'.mem = s.mem) :
    Stage2NoEventWalkInv (stage2NoEventWalkStringCarryPlain K lane) mem s' :=
  (Stage2NoEventWalkInv.stringPlain h htok).mem_congr hm


/-- **The base table is the same at the string carries**: the class's carry moves
only the token count, the terms, the logical arena and its word, and the base
cells read the parameters and the entry chain's own bindings. -/
theorem stage2NoEventWalkBaseValues_stringCarry (K : Stage2NoEventWalkCarry)
    (len : Nat) (body : List UInt8) :
    stage2NoEventWalkBaseValues (stage2NoEventWalkStringCarry K len body) =
      stage2NoEventWalkBaseValues K := rfl

theorem stage2NoEventWalkBaseValues_stringCarryPlain (K : Stage2NoEventWalkCarry)
    (lane : Nat) :
    stage2NoEventWalkBaseValues (stage2NoEventWalkStringCarryPlain K lane) =
      stage2NoEventWalkBaseValues K := rfl


/-- **The arena carry's invariant.**  The class appends the decoded body to the
logical arena and its byte sum to the arena word; every other invariant field is
the source's, and the word's equation is the source's by the append's sum. -/
theorem Stage2NoEventWalkInv.stringArena {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {len : Nat} {body : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (htok : K.tok + 1 ≤ K.n) :
    Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem s := by
  have hW' : K.arenaWord % 2 ^ 64 = K.arenaWord := by
    rw [← h.arenaEq]
    exact Nat.mod_mod _ _
  unfold stage2NoEventWalkStringCarry
  refine { h with tokLe := htok, arenaEq := ?_ }
  rw [byteSum_append, Nat.add_mod (byteSum K.arena) (byteSum body) (2 ^ 64),
    Nat.add_mod K.arenaWord (byteSum body) (2 ^ 64), h.arenaEq, hW']


/-- The `string_value` merge's cell list at the head's edge, over the head's
environment: the test's bit, the eight `phi` cells, and the two dispatch cells the
merge's edge names. -/
def stage2NoEventWalkStringEntryCells (inc lane fr sp k terms tok nep : Nat) :
    List (String × Value) :=
  [("%cmp207.not", .int 1 (evalICmp .ult (BitVec.ofNat 64 inc) (BitVec.ofNat 64 nep))),
   ("%tokens.0.lcssa1075", .int 64 (BitVec.ofNat 64 tok)),
   ("%terms.0.lcssa1081", .int 64 (BitVec.ofNat 64 terms)),
   ("%k.0.lcssa1087", .int 64 (BitVec.ofNat 64 k)),
   ("%sp.0.lcssa1093.wide", .int 32 (BitVec.ofNat 32 sp)),
   ("%frame.0.lcssa1099", .int 8 (BitVec.ofNat 8 fr)),
   ("%idxprom.lcssa1109", .int 64 (BitVec.ofNat 64 lane)),
   ("%.lcssa1125", .int 32 (BitVec.ofNat 32 lane)),
   ("%inc.lcssa1130", .int 64 (BitVec.ofNat 64 inc)),
   ("%SwitchLeaf", .int 1 1), ("%Pivot6", .int 1 1)]

/-- **The head's entry to `if.end216`**: the dispatch row's two links (the byte's
class and the `LeafBlock` arm) and `string_value`'s merge, three steps, ending at
`if.end216`'s entry with the class's `phi` cells and the base table carried
through the merge's cell layers. -/
theorem stage2NoEventWalkStringEntrySegment {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {lane : Nat} {byte : UInt8} {fr sp : Nat}
    (h : Stage2NoEventWalkHead K mem k s) (hent : K.ent[k]? = some lane)
    (hbs : K.bs[lane]? = some byte) (h34 : byte.toNat = 34) (hk1 : k + 1 < K.nep)
    (hfrPhi : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPhi : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp))) :
    ∃ (s216 : State), s216.pc = "if.end216" ∧
      s216.pre = some "string_value" ∧
      s216.mem = s.mem ∧
      s216.next = s.next ∧
      Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s216 3 ∧
      lookupName s216.env "%k.0.lcssa1087" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName s216.env "%inc.lcssa1130" =
        some (.int 64 (BitVec.ofNat 64 (k + 1))) ∧
      lookupName s216.env "%.lcssa1125" = some (.int 32 (BitVec.ofNat 32 lane)) ∧
      lookupName s216.env "%idxprom.lcssa1109" =
        some (.int 64 (BitVec.ofNat 64 lane)) ∧
      lookupName s216.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s216.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s216.env "%tokens.0.lcssa1075" =
        some (.int 64 (BitVec.ofNat 64 K.tok)) ∧
      lookupName s216.env "%terms.0.lcssa1081" =
        some (.int 64 (BitVec.ofNat 64 K.terms)) ∧
      lookupName s216.env "%alen.0.ph1405" =
        some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName s216.env "%arena.0.ph1406" =
        some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      Stage2NoEventWalkBaseLookups K s216 := by
  have hstage := stage2NoEventWalkStringB_headStaging h hent hbs
  obtain ⟨-, h3, h2, hidx, hinc, -, -, -⟩ := hstage
  have hk := h.kEq
  have hterms := h.termsPhi
  have htok := h.tokensPhi
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    h.baseLookup (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have houtn : lookupName s.env "%outn205" = some (.ptr (K.next0 + 16)) :=
    h.baseLookup (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
        entryCells2, entryCells3, entryCells4, preHeaderCells])
  have h3' : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 34)) := by
    rw [h3, h34]
  -- the dispatch row's two links
  let S0 : State := stage2NoEventWalkNext (("%Pivot6", .int 1 1) :: s.env) s "LeafBlock"
  have L1 : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem s K S0 := by
    simpa only [S0] using link_nodeBlock5_true h.inv h.pc h3' (by decide)
  have h3₁ : lookupName S0.env "%3" = some (.int 8 (BitVec.ofNat 8 34)) :=
    lookupName_cons_other _ _ _ (by decide) h3'
  let envL : Env := ("%SwitchLeaf", .int 1 1) :: ("%Pivot6", .int 1 1) :: s.env
  let S1 : State := stage2NoEventWalkNext envL S0 "string_value"
  have L2 : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem S0 K S1 := by
    simpa only [S1, envL, S0, stage2NoEventWalkNext] using
      link_leafBlock_true L1.inv' rfl h3₁ (by decide)
  have hpc1 : S1.pc = "string_value" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "LeafBlock" := by
    simp only [S1, S0, stage2NoEventWalkNext]
  -- the merge's link
  have hlink : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem S1 K
      (stage2NoEventWalkNext
        (stringValueHeadEnv envL (k + 1) lane fr sp k K.terms K.tok K.nep) S1
        "if.end216") :=
    link_string_valueHead (gap := gap) L2.inv' hpc1 hpre1
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hinc)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) h2)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hidx)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hfrPhi)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hspPhi)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hk)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hterms)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) htok)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) houtn)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hnep)
      (stage2NoEventWalkStringB_ult (Nat.lt_trans hk1 h.inv.nepLt) h.inv.nepLt hk1)
  let s216 : State := stage2NoEventWalkNext
    (stringValueHeadEnv envL (k + 1) lane fr sp k K.terms K.tok K.nep) S1 "if.end216"
  have hrun : ∀ n, runFuel (stage2NoEventCalls gap) (3 + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody s216 := by
    intro n
    rw [show 3 + n = 1 + (1 + (1 + n)) from by omega,
      arenaB_runFuel_jump L1.step (1 + (1 + n)),
      arenaB_runFuel_jump L2.step (1 + n), arenaB_runFuel_jump hlink.step n]
  have hinv216 : Stage2NoEventWalkInv K mem s216 :=
    h.inv.mem_congr (by
      simp only [s216, S1, S0, stage2NoEventWalkNext])
  -- the cell layers over the head's environment
  let cs : List (String × Value) :=
    stage2NoEventWalkStringEntryCells (k + 1) lane fr sp k K.terms K.tok K.nep
  have henv216 : s216.env = cells cs s.env := by
    simp only [s216, S1, S0, envL, cs, stage2NoEventWalkNext, stringValueHeadEnv,
      stringValueHeadCells, stage2NoEventWalkStringEntryCells, cells]
  have hbase216 : Stage2NoEventWalkBaseLookups K s216 :=
    (h.baseLookups.consCells (cs := cs) (by rfl)).congr_env henv216
  have hnd : (cs.map (·.1)).Nodup := by
    simp only [cs, stage2NoEventWalkStringEntryCells, List.map_cons, List.map_nil]
    decide
  have hphi : ∀ (n : String) (v : Value), (n, v) ∈ cs → lookupName s216.env n = some v := by
    intro n v hv
    rw [henv216]
    exact cells_lookup_of_mem cs s.env hv hnd
  have hnotin : ∀ (n : String), n ∉ (cs.map (·.1)) →
      lookupName s216.env n = lookupName s.env n := by
    intro n hn
    rw [henv216]
    exact cells_lookup_of_notin cs s.env hn
  have hcsnames : ∀ (n : String), n = "%alen.0.ph1405" ∨ n = "%arena.0.ph1406" →
      n ∉ (cs.map (·.1)) := by
    rintro n (rfl | rfl) <;>
      (simp only [cs, stage2NoEventWalkStringEntryCells, List.map_cons, List.map_nil]
       decide)
  have halen216 : lookupName s216.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [hnotin _ (hcsnames _ (Or.inl rfl))]
    exact h.alenPhi
  have harena216 : lookupName s216.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [hnotin _ (hcsnames _ (Or.inr rfl))]
    exact h.arenaPhi
  refine ⟨s216, ?_, ?_, ?_, ?_, ⟨hrun, hinv216⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hbase216⟩
  · simp only [s216, stage2NoEventWalkNext]
  · simp only [s216, S1, stage2NoEventWalkNext]
  · simp only [s216, S1, S0, stage2NoEventWalkNext]
  · simp only [s216, S1, S0, stage2NoEventWalkNext]
  all_goals
    first
      | exact halen216
      | exact harena216
      | exact hphi _ _ (by simp [cs, stage2NoEventWalkStringEntryCells])


/-- **A lane-stream read across a frame.**  A `readLanes32` whose whole byte range
lies outside the run's regions reads the same at a memory the frame says is
unchanged there.  The invariant's entry stream is stated at its fixed `mem`; the
dispatch blocks read the state's memory, so this is how the closing lane's read
reaches the block. -/
theorem stage2NoEventWalkReadLanes32_of_frame {m m' : Mem} {R : List (Nat × Nat)}
    {a n : Nat} {l : List Nat} (h : UnchangedOutside m m' R)
    (hout : ∀ k, k < 4 * n → ¬ inRegions R (a + k))
    (hl : readLanes32 m a n = some l) :
    readLanes32 m' a n = some l := by
  have hm' : UnchangedOn (inRegions R) m m' := unchangedOutside_iff_inRegions.mp h
  induction n generalizing a l with
  | zero =>
      simp only [readLanes32, Option.some.injEq] at hl ⊢
      exact hl
  | succ n ih =>
      simp only [readLanes32] at hl ⊢
      cases hb : readBytes m a 4 with
      | none => rw [hb] at hl; cases hl
      | some bs =>
          rw [hb] at hl
          have hb' : readBytes m' a 4 = some bs := by
            rw [readBytes_eq_of_UnchangedOn hm' (a := a) (n := 4)
              (fun k hk => hout k (by omega)), hb]
          rw [hb']
          cases hr : readLanes32 m (a + 4) n with
          | none => rw [hr] at hl; cases hl
          | some tl =>
              rw [hr] at hl
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hl
              subst hl
              rw [ih (a := a + 4) (l := tl) (fun k hk => by
                have hk' := hout (k + 4) (by omega)
                simpa only [show a + (k + 4) = a + 4 + k from by omega] using hk') hr]
              simp

/-! ### The class's call leg

The head's read hands off to `if.end216` (`stage2NoEventWalkStringEntrySegment`,
three blocks).  The call's own slice is the five blocks after it: the extent test
(`if.end216`), the length and scratch guard (`if.end230`), the call
(`if.end239`), and the result's two-way dispatch (`NodeBlock29`, `LeafBlock27`).
The class's tail after that is the arm's own.  This section proves the five
blocks and the invariant they leave, so the two arms can consume them.

The guard's numbers: the closing entry is at index `k+1` and the entry after it
(the comma) at `k+2`.  `if.end216` reads the closing entry's lane word and
requires it inside the document (`next < K.n`); `if.end230` forms the length
`next - lane - 1`, adds the 64-byte reserve and requires it inside the scratch
capacity.  Both are the class's own facts and are taken as such.

The invariant crosses the call once: `%k219`'s store at `K.c + 32` and the
`%outn205` zero store at `K.next0 + 16` are inside the run's regions
(`stage2NoEventWalkInv.stack_write`), and the callee's frame over its footprint,
widened by `UnchangedOutside.of_covered` to the run's regions, is the rest.
Presence at the returned memory is the class's staging fact. -/

/-- **The string body call's argument list**, at the class's cursor, scratch
buffer, output slot and index cells. -/
def stage2NoEventWalkStringArgs (K : Stage2NoEventWalkCarry) (lane : Nat)
    (sub : BitVec 64) : List Value :=
  [.ptr K.c, .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat), .int 64 sub,
   .ptr K.scratch, .ptr (K.next0 + 16), .ptr K.xp, .ptr K.next0,
   .int 64 (BitVec.ofNat 64 K.nxp)]

/-- **A base lookup survives a cons of a name outside the table.** -/
theorem Stage2NoEventWalkBaseLookups.consOne {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) {n : String} {v : Value}
    (hn : n ∉ stage2NoEventWalkBaseNames) :
    Stage2NoEventWalkBaseLookups K { s with env := (n, v) :: s.env } := by
  intro m w hmw
  have hm : m ∈ stage2NoEventWalkBaseNames := by
    have h2 := List.mem_map_of_mem (f := Prod.fst) hmw
    rwa [stage2NoEventWalkBaseValues_names] at h2
  show lookupName ((n, v) :: s.env) m = some w
  have hnm : n ≠ m := by
    rintro rfl
    exact hn hm
  rw [lookupName_cons_ne _ _ hnm]
  exact h m w hmw

/-- **A lookup outside a cell list reaches the list's environment.** -/
theorem stage2NoEventWalkStringRowCellsNotin {env : Env} {n : String}
    {cs : List (String × Value)} (h : n ∉ cs.map (·.1)) :
    lookupName (cells cs env) n = lookupName env n :=
  cells_lookup_of_notin cs env h

/-- The cell names the call leg conses, outermost first. -/
def stage2NoEventWalkStringRowLegNames : List String :=
  ["%Pivot30", "%call243", "%gep", "%cmp236", "%add235", "%sub234", "%30",
   "%cmp221.not", "%conv220", "%29", "%arrayidx218", "%inc217"]

/-- **The invariant's frame composes over the same region list.** -/
theorem stage2NoEventWalkStringRowFrameTrans {m0 m1 m2 : Mem} {R : List (Nat × Nat)}
    (h1 : UnchangedOutside m0 m1 R) (h2 : UnchangedOutside m1 m2 R) :
    UnchangedOutside m0 m2 R :=
  fun a ha => (h2 a ha).trans (h1 a ha)

/-- **A link is a one-step segment.** -/
theorem stage2NoEventWalkStringRowLinkSegment {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {s s' : State}
    (hl : Stage2NoEventWalkLink calls K mem s K' s') :
    Stage2NoEventWalkSegment calls mem K s K' s' 1 :=
  ⟨fun n => stage2NoEventWalkLink_runFuel hl n, hl.inv'⟩

/-- **A step is a one-step segment**, at the invariant its target carries. -/
theorem stage2NoEventWalkStringRowStepSegment {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {s s' : State}
    (hs : step calls stage2NoEventBody s = .jump s')
    (hinv : Stage2NoEventWalkInv K mem s') :
    Stage2NoEventWalkSegment calls mem K s K s' 1 :=
  ⟨fun n => arenaB_runFuel_jump hs n, hinv⟩

/-- **The inverted lane word.** -/
theorem stage2NoEventWalkStringRowXor (lane : Nat) (hlane : lane < 2 ^ 64) :
    BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615 =
      BitVec.ofNat 64 (2 ^ 64 - 1 - lane) := by
  have hall : BitVec.ofNat 64 18446744073709551615 = BitVec.allOnes 64 := by decide
  rw [hall, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlane,
    Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 1 - lane < 2 ^ 64)]

/-- **The call's length argument**: the closing position less the opening one
less one. -/
theorem stage2NoEventWalkStringRowSubToNat {lane nextLane : Nat} (hlt : lane < nextLane)
    (hnext : nextLane < 2 ^ 64) :
    (BitVec.ofNat 64 nextLane +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)).toNat =
      nextLane - lane - 1 := by
  have hlane : lane < 2 ^ 64 := by omega
  rw [stage2NoEventWalkStringRowXor lane hlane, stage2NoEventWalkOfNat_add,
    BitVec.toNat_ofNat,
    show nextLane + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (nextLane - lane - 1) from by omega,
    Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- A `ugt` at one, from the `Nat` order. -/
theorem stage2NoEventWalkStringRowUgt_one {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : b < a) : evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  have hbit : BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true := by
    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha]
    exact decide_eq_true h
  simp [evalICmp, hbit]

/-- A `ugt` at zero, from the `Nat` order. -/
theorem stage2NoEventWalkStringRowUgt_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a ≤ b) : evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  have hbit : BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = false := by
    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha]
    simp only [decide_eq_false_iff_not, not_lt]
    exact h
  simp [evalICmp, hbit]

/-- **`if.end230`'s guard at zero**: the length and reserve inside the scratch
capacity. -/
theorem stage2NoEventWalkStringRowGuard230 {lane next cap : Nat}
    (hln : lane < next) (hnext : next < 2 ^ 64)
    (hcap : next - lane - 1 + 64 ≤ cap) (hcapLt : cap < 2 ^ 64) :
    evalICmp .ugt
      ((BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) +
        BitVec.ofNat 64 64) (BitVec.ofNat 64 cap) = 0 := by
  have hX : BitVec.ofNat 64 next +
      (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615) =
      BitVec.ofNat 64 (next - lane - 1) := by
    rw [stage2NoEventWalkStringRowXor lane (by omega), stage2NoEventWalkOfNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show next + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (next - lane - 1) from by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hX, stage2NoEventWalkOfNat_add]
  exact stage2NoEventWalkStringRowUgt_zero (by omega) hcapLt hcap

/-- **`NodeBlock29`'s guard at zero**: a form of at least one is not below one. -/
theorem stage2NoEventWalkStringRowSlt_one_zero {form : Nat}
    (h : form = 1 ∨ form = 2) :
    evalICmp .slt (BitVec.ofNat 32 form) (BitVec.ofNat 32 1) = 0 := by
  rcases h with rfl | rfl <;> decide

/-- **`LeafBlock27`'s guard at one.** -/
theorem stage2NoEventWalkStringRowEq_one {form : Nat} (h : form = 1) :
    evalICmp .eq (BitVec.ofNat 32 form) (BitVec.ofNat 32 1) = 1 := by
  subst h
  exact arenaB_icmp_eq_one rfl

/-- **`LeafBlock27`'s guard at zero**, off the form's being other than one. -/
theorem stage2NoEventWalkStringRowEq_zero {form : Nat} (h : form ≠ 1)
    (hlt : form < 2 ^ 32) :
    evalICmp .eq (BitVec.ofNat 32 form) (BitVec.ofNat 32 1) = 0 := by
  have hne : BitVec.ofNat 32 form ≠ BitVec.ofNat 32 1 := by
    intro hc
    apply h
    have h2 := congrArg BitVec.toNat hc
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (by decide : (1 : Nat) < 2 ^ 32)] using h2
  exact arenaB_icmp_eq_zero hne

/-- **The class's call leg**: the head to `LeafBlock27`'s entry, seven blocks.
The endpoint carries the source invariant at the fixed memory, the base table,
and the register facts the two arms read. -/
theorem stage2NoEventWalkStringHeadToLeaf27 {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {fr sp : Nat}
    (h : Stage2NoEventWalkHead K mem k s)
    (hfrPhi : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPhi : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    {lane next : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 34)
    (hk1 : K.ent[k + 1]? = some next)
    (hklt : k + 3 < K.nep)
    {form : Nat} {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 form))
    (hforms : form = 1 ∨ form = 2) (hformLt : form < 2 ^ 32)
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a) :
    ∃ s27, Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s27 7 ∧
      Stage2NoEventWalkInv K mem s27 ∧
      Stage2NoEventWalkBaseLookups K s27 ∧
      s27.pc = "LeafBlock27" ∧ s27.mem = r.mem ∧
      lookupName s27.env "%call243" = some (.int 32 (BitVec.ofNat 32 form)) ∧
      lookupName s27.env "%alen.0.ph1405" =
        some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName s27.env "%arena.0.ph1406" =
        some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      lookupName s27.env "%tokens.0.lcssa1075" =
        some (.int 64 (BitVec.ofNat 64 K.tok)) ∧
      lookupName s27.env "%terms.0.lcssa1081" =
        some (.int 64 (BitVec.ofNat 64 K.terms)) ∧
      lookupName s27.env "%inc217" = some (.int 64 (BitVec.ofNat 64 (k + 2))) ∧
      lookupName s27.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s27.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s27.env "%sub234" = some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) ∧
      lookupName s27.env "%.lcssa1125" = some (.int 32 (BitVec.ofNat 32 lane)) := by
  classical
  -- the entry segment and the head's frame/depth readings
  have hk1lt : k + 1 < K.nep := by omega
  obtain ⟨s216, hpc216, hpre216, hmem216, hnext216, hseg3, hk216, hinc216, hlc216, hidx216,
    hfr216, hsp216, htok216, hterms216, halen216, harena216, hbase216⟩ :=
    stage2NoEventWalkStringEntrySegment (gap := gap) h hk hbs hb hk1lt hfrPhi hspPhi
  -- the closing entry's lane word
  obtain ⟨q, bs4, hentq, hq32, hread4, hval⟩ := h.laneAt (i := k + 1) hk1lt
  have hqnext : q = next := Option.some.inj (by rw [← hentq, hk1])
  have hbs4next : bytesToNat bs4 = next := by rw [hval, hqnext]
  -- the head's numbers
  have hlane32 : lane < 2 ^ 32 := by
    have h1 := h.inv.inside lane (List.mem_of_getElem? hk)
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnext32 : next < 2 ^ 32 := by
    have h1 := h.inv.inside next (List.mem_of_getElem? hk1)
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp h.inv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextN : next < K.n := h.inv.inside next (List.mem_of_getElem? hk1)
  have hk2lt : k + 2 < 2 ^ 64 := by
    have h1 := h.inv.nepLe
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    have h3 := h.inv.nLt
    omega
  -- the `if.end216` instance
  let kv : BitVec 64 := BitVec.ofNat 64 k
  let incv : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let nv : BitVec 64 := BitVec.ofNat 64 K.n
  have hincpos : (incv.signExtend 64).toNat = k + 1 := by
    show ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat = k + 1
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpos216 : (incv.signExtend 64).toNat < 2 ^ 63 := by
    rw [hincpos]
    have h1 := h.inv.nepLe
    have h2 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hread216 : readBytes s216.mem (K.ep + (incv.signExtend 64).toNat * 4) 4 = some bs4 := by
    simpa only [hmem216, hincpos, Nat.mul_comm] using hread4
  have hlanelt : bytesToNat bs4 < 2 ^ 32 := by rw [hbs4next]; exact hnext32
  have hk219216 : lookupName s216.env "%k219" = some (.ptr (K.c + 32)) :=
    hbase216 "%k219" (.ptr (K.c + 32)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])
  have hn216 : lookupName s216.env "%n" =
      some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase216 "%n" (.int 64 (BitVec.ofNat 64 K.n)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hy216 : evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)) = 1 := by
    rw [hbs4next]
    exact stage2NoEventWalkStringRowUgt_one h.inv.nLt (by
      have h2 := h.inv.maxDoc
      simp only [stage2MaxDocument] at h2
      omega) hnextN
  have hw219 : ∀ j, j < (natToBytes (kv + BitVec.ofNat 64 2).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 32 + j) := by
    intro j hj
    rw [natToBytes_length] at hj
    refine ⟨(K.c, stage2NoEventCursorExtent), ?_, ?_, ?_⟩
    · simp [stage2NoEventRunRegions, stage2NoEventStagedRegions]
    · simp only [stage2NoEventCursorExtent]; omega
    · simp only [stage2NoEventCursorExtent]; omega
  have L216 := link_ifEnd216_true (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s216) (k := kv) (ep := K.ep) (inc := incv) (a := K.c + 32) (bs4 := bs4)
    (n := nv) hseg3.inv' hpc216 hk216 (by
      rw [show lookupName s216.env "%ep" = some (.ptr K.ep) from
        hbase216 "%ep" (.ptr K.ep) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])]) hinc216
    hpos216 hread216 hlanelt hk219216 hn216 hw219 hy216
  let s217 : State := stage2NoEventWalkStored
    (ifEnd216Cells s216.env kv K.ep incv bs4 nv) s216
    (writeBytes s216.mem (K.c + 32) (natToBytes (kv + BitVec.ofNat 64 2).toNat 8))
    "if.end230"
  have hstep217 : step (stage2NoEventCalls gap) stage2NoEventBody s216 = .jump s217 := by
    simpa only [s217] using L216.step
  have hpc217 : s217.pc = "if.end230" := by
    simp only [s217, stage2NoEventWalkStored]
  -- the `if.end230` instance
  have hidx217 : lookupName s217.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx216
  have hv217 : lookupName s217.env "%conv220" = some (.int 64 (BitVec.ofNat 64 next)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    rw [hbs4next]
  have hcap217 : lookupName s217.env "%scratchcap" =
      some (.int 64 (BitVec.ofNat 64 K.scratchcap)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbase216 "%scratchcap" (.int 64 (BitVec.ofNat 64 K.scratchcap)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hcapLt : K.scratchcap < 2 ^ 64 := h.inv.scratchcapLt
  have hy230 : evalICmp .ugt
      ((BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) +
        BitVec.ofNat 64 64) (BitVec.ofNat 64 K.scratchcap) = 0 :=
    stage2NoEventWalkStringRowGuard230 hlaneNext (by omega) hscratch hcapLt
  have L230 := link_ifEnd230_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s217) (idx := BitVec.ofNat 64 lane) (v := BitVec.ofNat 64 next)
    (cap := BitVec.ofNat 64 K.scratchcap) L216.inv' hpc217 hidx217 hv217 hcap217 hy230
  let s218 : State := stage2NoEventWalkNext
    (ifEnd230Cells s217.env (BitVec.ofNat 64 lane) (BitVec.ofNat 64 next)
      (BitVec.ofNat 64 K.scratchcap)) s217 "if.end239"
  have hstep218 : step (stage2NoEventCalls gap) stage2NoEventBody s217 = .jump s218 := by
    simpa only [s218] using L230.step
  have hpc218 : s218.pc = "if.end239" := by
    simp only [s218, stage2NoEventWalkNext]
  have hs218env : s218.env = cells
      [("%cmp236", .int 1 (evalICmp .ugt
          ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
          (BitVec.ofNat 64 K.scratchcap))),
        ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
        ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615))),
        ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615)),
        ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
        ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
        ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))] s216.env := by
    simp only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd230Cells, ifEnd216Cells, cells]
  -- the base table at the two links' targets
  have hb218 : Stage2NoEventWalkBaseLookups K s218 := by
    have hh := stage2NoEventCycleBase (K := K) (env := s216.env) hbase216
      (cs := [("%cmp236", .int 1 (evalICmp .ugt
          ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
          (BitVec.ofNat 64 K.scratchcap))),
        ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
        ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615))),
        ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615)),
        ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
        ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
        ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))])
      (names := ["%cmp236", "%add235", "%sub234", "%30", "%cmp221.not", "%conv220",
        "%29", "%arrayidx218", "%inc217"]) rfl (by decide)
    intro n v hv
    have h2 := hh n v hv
    rw [hs218env]
    exact h2
  -- the call
  have hmem218 : s218.mem =
      writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8) := by
    have hkv : (kv + BitVec.ofNat 64 2).toNat = k + 2 := by
      show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2).toNat = k + 2
      rw [stage2NoEventWalkOfNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored, hmem216, hkv]
  have hidx218 : lookupName s218.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [s218, stage2NoEventWalkNext, ifEnd230Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx217
  have hnext218 : s218.next = s.next := by
    simpa only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored] using hnext216
  have hsub218 : lookupName s218.env "%sub234" =
      some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) := by
    simp only [s218, stage2NoEventWalkNext, ifEnd230Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
    rw [show (BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) =
        BitVec.ofNat 64 (next - lane - 1) from by
      rw [stage2NoEventWalkStringRowXor lane (by omega), stage2NoEventWalkOfNat_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show next + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (next - lane - 1) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]]
  have hcall' : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes s218.mem (K.next0 + 16) (natToBytes 0 8)) s218.next = some r := by
    rw [hmem218, hnext218]
    exact hcall
  have hpos239 : ((BitVec.ofNat 64 lane).signExtend 64).toNat < 2 ^ 63 :=
    stage2NoEventLane_signExtend_lt hlane32
  have hstepCall : step (stage2NoEventCalls gap) stage2NoEventBody s218 = .jump
      { env := ifEnd239Cells s218.env (K.b + 1) (BitVec.ofNat 64 lane) r,
        mem := r.mem, next := r.next, pc := "NodeBlock29", pre := some s218.pc } :=
    ifEnd239_step (calls := stage2NoEventCalls gap) (s := s218) hpc218
      (hb218 "%outn205" (.ptr (K.next0 + 16)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hb218 "%invariant.gep" (.ptr (K.b + 1)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4]))
      hidx218 hpos239
      (hb218 "%c" (.ptr K.c) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      hsub218
      (hb218 "%scratch" (.ptr K.scratch) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      (hb218 "%xp" (.ptr K.xp) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      (hb218 "%xj" (.ptr K.next0) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hb218 "%nxp" (.int 64 (BitVec.ofNat 64 K.nxp)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      hcall'
  let sCall : State :=
    { env := ifEnd239Cells s218.env (K.b + 1) (BitVec.ofNat 64 lane) r,
      mem := r.mem, next := r.next, pc := "NodeBlock29", pre := some s218.pc }
  -- the invariant across the two stores and the call
  let R : List (Nat × Nat) :=
    stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
      [(K.next0, K.nextEnd - K.next0)]
  have hkvN : (kv + BitVec.ofNat 64 2).toNat = k + 2 := by
    show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2).toNat = k + 2
    rw [stage2NoEventWalkOfNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hwrite217 : writeBytes s216.mem (K.c + 32)
      (natToBytes (kv + BitVec.ofNat 64 2).toNat 8) =
      writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8) := by
    rw [hkvN, hmem216]
  have hf0 : UnchangedOutside s.mem s.mem R := fun a _ => rfl
  have hf1 : UnchangedOutside s.mem
      (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8)) R := by
    have hh := UnchangedOutside.write_inside (m := s.mem) hf0
      (a := K.c + 32) (bs := natToBytes (kv + BitVec.ofNat 64 2).toNat 8) hw219
    simpa only [hkvN] using hh
  have hwOut : ∀ j, j < (natToBytes 0 8).length →
      inRegions R (K.next0 + 16 + j) := by
    intro j hj
    rw [natToBytes_length] at hj
    refine ⟨(K.next0, K.nextEnd - K.next0), ?_, ?_, ?_⟩
    · exact List.mem_append_right _ (by simp)
    · omega
    · have h1 := h.inv.nextEnd_static
      simp only [stage2BootstrapExtent] at h1
      omega
  have hf2 : UnchangedOutside
      (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) R :=
    UnchangedOutside.write_inside (m := writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
      (fun a _ => rfl) (a := K.next0 + 16) (bs := natToBytes 0 8) hwOut
  have hfCall : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem R :=
    UnchangedOutside.of_covered hframe hfoot
  have hf012 : UnchangedOutside s.mem
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) R :=
    stage2NoEventWalkStringRowFrameTrans hf1 hf2
  have hf : UnchangedOutside s.mem r.mem R :=
    stage2NoEventWalkStringRowFrameTrans hf012 hfCall
  have hfm : UnchangedOutside mem r.mem R :=
    stage2NoEventWalkStringRowFrameTrans h.inv.walkFrame hf
  have hinvCall : Stage2NoEventWalkInv K mem sCall :=
    Stage2NoEventWalkInv.of_frame (K := K) (mem := mem) (s := s216) (s' := sCall)
      hseg3.inv' hpresent hfm
  -- the result's dispatch
  have hcall243 : lookupName sCall.env "%call243" =
      some (.int 32 (BitVec.ofNat 32 form)) := by
    simp only [sCall, ifEnd239Cells]
    rw [lookupName_cons_self, hret]
  have hpcCall : sCall.pc = "NodeBlock29" := rfl
  have hy29 : evalICmp .slt (BitVec.ofNat 32 form) (BitVec.ofNat 32 1) = 0 :=
    stage2NoEventWalkStringRowSlt_one_zero hforms
  have L29 := link_nodeBlock29_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := sCall) (v := BitVec.ofNat 32 form) hinvCall hpcCall hcall243 hy29
  let s29 : State := stage2NoEventWalkNext
    (("%Pivot30", .int 1 0) :: sCall.env) sCall "LeafBlock27"
  have hstep29 : step (stage2NoEventCalls gap) stage2NoEventBody sCall = .jump s29 := by
    simpa only [s29] using L29.step
  have hseg29 := stage2NoEventWalkStringRowLinkSegment L29
  have hsegCall := stage2NoEventWalkStringRowStepSegment
    (K := K) (mem := mem) (s := s218) (s' := sCall) hstepCall hinvCall
  have hseg217 := stage2NoEventWalkStringRowLinkSegment L216
  have hseg218 := stage2NoEventWalkStringRowLinkSegment L230
  have hseg7 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s29 7 := by
    have h34 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s217 4 :=
      hseg3.trans hseg217
    have h5 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s218 5 :=
      h34.trans hseg218
    have h6 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sCall 6 :=
      h5.trans hsegCall
    have h7 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s29 7 :=
      h6.trans hseg29
    exact h7
  have hb29 : Stage2NoEventWalkBaseLookups K s29 := by
    have hbCall : Stage2NoEventWalkBaseLookups K sCall := by
      have h1 : Stage2NoEventWalkBaseLookups K
          { s218 with env := ("%gep", .ptr ((K.b + 1) +
            ((BitVec.ofNat 64 lane).signExtend 64).toNat)) :: s218.env } :=
        hb218.consOne (n := "%gep")
          (v := .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat)) (by decide)
      have h2 : Stage2NoEventWalkBaseLookups K
          { { s218 with env := ("%gep", .ptr ((K.b + 1) +
              ((BitVec.ofNat 64 lane).signExtend 64).toNat)) :: s218.env } with
            env := ("%call243", r.ret)
              :: ("%gep", .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat))
              :: s218.env } :=
        h1.consOne (n := "%call243") (v := r.ret) (by decide)
      exact h2.congr_env (by simp only [sCall, ifEnd239Cells, cells])
    have hh : Stage2NoEventWalkBaseLookups K
        { sCall with env := ("%Pivot30", .int 1 0) :: sCall.env } :=
      hbCall.consOne (n := "%Pivot30") (v := .int 1 0) (by decide)
    exact hh.congr_env (by simp only [s29, stage2NoEventWalkNext, cells])
  -- the surviving readings
  have hs29env : s29.env = ("%Pivot30", .int 1 0) :: ("%call243", r.ret) ::
      ("%gep", .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat)) ::
      cells
        [("%cmp236", .int 1 (evalICmp .ugt
            ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
            (BitVec.ofNat 64 K.scratchcap))),
          ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
          ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615))),
          ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)),
          ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
          ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
          ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
          ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
          ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))] s216.env := by
    simp only [s29, sCall, stage2NoEventWalkNext, ifEnd239Cells, hs218env]
  have hsurv (n : String) (hn1 : n ∉ ["%Pivot30", "%call243", "%gep"])
      (hn2 : n ∉ ["%cmp236", "%add235", "%sub234", "%30", "%cmp221.not", "%conv220",
        "%29", "%arrayidx218", "%inc217"]) (v : Value)
      (hv : lookupName s216.env n = some v) :
      lookupName s29.env n = some v := by
    rw [hs29env]
    rw [lookupName_cons_ne _ _ (fun e => hn1 (by simp [e])),
        lookupName_cons_ne _ _ (fun e => hn1 (by simp [e])),
        lookupName_cons_ne _ _ (fun e => hn1 (by simp [e]))]
    rw [stage2NoEventWalkStringRowCellsNotin
      (cs := [("%cmp236", .int 1 (evalICmp .ugt
            ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
            (BitVec.ofNat 64 K.scratchcap))),
          ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
          ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615))),
          ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)),
          ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
          ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
          ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
          ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
          ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))]) (n := n) (fun hc => hn2 (by
      simpa using hc))]
    exact hv
  have hcall29 : lookupName s29.env "%call243" =
      some (.int 32 (BitVec.ofNat 32 form)) := by
    simp only [s29, sCall, stage2NoEventWalkNext, ifEnd239Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hret]
  have hpc29 : s29.pc = "LeafBlock27" := by simp only [s29, stage2NoEventWalkNext]
  have hmem29 : s29.mem = r.mem := by
    simp only [s29, sCall, stage2NoEventWalkNext]
  have hinc29 : lookupName s29.env "%inc217" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [s29, sCall, s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd239Cells, ifEnd230Cells, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    rw [show (kv + BitVec.ofNat 64 2) = BitVec.ofNat 64 (k + 2) from by
      show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2) = BitVec.ofNat 64 (k + 2)
      exact stage2NoEventWalkOfNat_add 64 k 2]
  have hsub29 : lookupName s29.env "%sub234" =
      some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) := by
    simp only [s29, sCall, s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd239Cells, ifEnd230Cells, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    rw [show (BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) =
        BitVec.ofNat 64 (next - lane - 1) from by
      rw [stage2NoEventWalkStringRowXor lane (by omega), stage2NoEventWalkOfNat_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show next + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (next - lane - 1) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]]
  exact ⟨s29, hseg7, hseg29.inv', hb29, hpc29, hmem29, hcall29,
    hsurv _ (by decide) (by decide) _ halen216, hsurv _ (by decide) (by decide) _ harena216,
    hsurv _ (by decide) (by decide) _ htok216, hsurv _ (by decide) (by decide) _ hterms216,
    hinc29, hsurv _ (by decide) (by decide) _ hfr216, hsurv _ (by decide) (by decide) _ hsp216,
    hsub29, hsurv _ (by decide) (by decide) _ hlc216⟩

/-! ### The arena arm's endpoint at either length case

`_short` and `_long` state the same ten endpoint cells and differ only in the
count.  This is one existential over either count, so the row's own price can
case on the length with the endpoint facts in hand. -/

theorem stage2NoEventWalkStringArenaArm {gap : Calls} {K : Stage2NoEventWalkCarry}
    {s : State} {mem : Mem} {sc arenaWord alen len tokens terms outn spv : Nat}
    {body : List UInt8} {inc217 : BitVec 64} {fr : BitVec 8}
    (hpc : s.pc = "for.cond266.preheader")
    (hmem : s.mem = mem)
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hread : readBytes mem outn 8 = some (natToBytes len 8))
    (hlenLt64 : len < 2 ^ 64) (hlen0 : len ≠ 0) (hlen63 : len < 2 ^ 63)
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv)))
    (hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (harenaPhi : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (hbody : readBytes mem sc len = some body) (hbodyLen : body.length = len)
    (hcase : len < 8 ∨ 8 ≤ len) :
    ∃ (sA : State) (jA : Nat),
      (jA ≤ 3 + (len + 1) + 2 ∨ jA ≤ len / 8 + len % 8 + 8) ∧
      (∀ n, runFuel (stage2NoEventCalls gap) (jA + n) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sA) ∧
      sA.pc = "after_value" ∧ sA.pre = some "cleanup287" ∧ sA.mem = mem ∧
      lookupName sA.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName sA.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) ∧
      lookupName sA.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName sA.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName sA.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName sA.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName sA.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K sA := by
  rcases hcase with h8 | h8
  · obtain ⟨sA, jA, hjA, hrun, hpcA, hpreA, hmemA, h1, h2, h3, h4, h5, h6, h7, hb⟩ :=
      stage2NoEventWalkStringArenaB_short (gap := gap) (K := K) (s := s) (mem := mem)
        (xt := BitVec.ofNat 64 0)
        hpc hmem houtn hread hlenLt64 hlen0 h8 hsc halen htok hterms hinc217 hsp hfr
        hbase harenaPhi hbody hbodyLen
    exact ⟨sA, jA, Or.inl hjA, hrun, hpcA, hpreA, hmemA, h1, h2, h3, h4, h5, h6, h7, hb⟩
  · obtain ⟨sA, jA, hjA, hrun, hpcA, hpreA, hmemA, h1, h2, h3, h4, h5, h6, h7, hb⟩ :=
      stage2NoEventWalkStringArenaB_long (gap := gap) (K := K) (s := s) (mem := mem)
        (xt := BitVec.ofNat 64 0)
        hpc hmem houtn hread hlen63 h8 hsc hg1 hg2 hg3 hg4 hg5 hg6 hg7 halen htok hterms
        hinc217 hsp hfr hbase harenaPhi hbody hbodyLen
    exact ⟨sA, jA, Or.inr hjA, hrun, hpcA, hpreA, hmemA, h1, h2, h3, h4, h5, h6, h7, hb⟩


/-- **The `after_value` window at the class's carried readings.**  The seven
`phi`s select the frame, the depth, the index and the handoff's four cells; the
edge is `cleanup287`. -/
theorem stage2NoEventWalkStringAfter_of_lookups {Kc : Stage2NoEventWalkCarry}
    {kc fr sp : Nat} {s : State}
    (hpre : s.pre = some "cleanup287")
    (hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hinc : lookupName s.env "%inc217" = some (.int 64 (BitVec.ofNat 64 kc)))
    (halen : lookupName s.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 Kc.arena.length)))
    (harena : lookupName s.env "%arena.6" = some (.int 64 (BitVec.ofNat 64 Kc.arenaWord)))
    (hterms : lookupName s.env "%terms.4" = some (.int 64 (BitVec.ofNat 64 Kc.terms)))
    (htok : lookupName s.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 Kc.tok))) :
    Stage2NoEventWalkStringAfter Kc kc fr sp s := by
  refine ⟨"cleanup287", hpre, ?_⟩
  refine PhiSelects.cons (op := .reg "%frame.0.lcssa1099") (by decide) ?_
    (PhiSelects.cons (op := .reg "%sp.0.lcssa1093.wide") (by decide) ?_
      (PhiSelects.cons (op := .reg "%inc217") (by decide) ?_
        (PhiSelects.cons (op := .reg "%alen.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%arena.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%terms.4") (by decide) ?_
              (PhiSelects.cons (op := .reg "%tokens.4") (by decide) ?_
                PhiSelects.nil))))))
  all_goals
    simp only [stateAt, evalOperand, hfr, hsp, hinc, halen, harena, hterms, htok]

/-- **The string class's continuing row, arena arm.**  The head at `"` to
`LeafBlock27`, that block's staged-word arm at either length case, the arena's
slice and the shared cycle. -/
noncomputable def stage2NoEventWalkStringRow_arena {gap : Calls} {F : Nat}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State} {fr sp : Nat}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hfrPhi : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPhi : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    {lane next comma : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 34)
    (hk1 : K.ent[k + 1]? = some next)
    (hcommaEnt : K.ent[k + 2]? = some comma)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hklt : k + 3 < K.nep)
    (hfrLt : fr < 2 ^ 8) (hfrNe : fr ≠ 0) (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    {len : Nat} {body : List UInt8} {cs : List Nat}
    {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 2))
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a)
    (hcode : bodyCodePoints K.bs ⟨lane, next + 1⟩ = some cs)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs)
    (hbodyLen : body.length = len)
    (hreadOutn : readBytes r.mem (K.next0 + 16) 8 = some (natToBytes len 8))
    (hbodyRead : readBytes r.mem K.scratch len = some body)
    (hlen0 : len ≠ 0) (hlenSpan : len + 1 ≤ next - lane)
    (hbelow : K.arena.length < 2 ^ 63) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  refine Classical.choice (show Nonempty
    (Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s) from ?_)
  let w := stage2NoEventWalkStringHeadToLeaf27 (gap := gap) h hfrPhi hspPhi hk hbs hb hk1 hklt
    (form := 2) hret (Or.inr rfl) (by decide) hscratch hcall hframe hfoot hpresent
  let s27 : State := Classical.choose w
  obtain ⟨hseg7, hinv27, hbase27, hpc27, hmem27, hcall243, halen27, harena27, htok27,
    hterms27, hinc27, hfr27, hsp27, hsub27, hlc27⟩ := Classical.choose_spec w
  have hy27 : evalICmp .eq (BitVec.ofNat 32 2) (BitVec.ofNat 32 1) = 0 := by decide
  have L27 := link_leafBlock27_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s27) (v := BitVec.ofNat 32 2) hinv27 hpc27 hcall243 hy27
  let sMid : State := stage2NoEventWalkNext
    (("%SwitchLeaf28", .int 1 0) :: s27.env) s27 "for.cond266.preheader"
  have hpcMid : sMid.pc = "for.cond266.preheader" := rfl
  have hmemMid : sMid.mem = r.mem := by
    show s27.mem = r.mem
    exact hmem27
  have hseg8 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sMid 8 :=
    hseg7.trans (stage2NoEventWalkStringRowLinkSegment L27)
  have hbaseMid : Stage2NoEventWalkBaseLookups K sMid := by
    have hh : Stage2NoEventWalkBaseLookups K
        { s27 with env := ("%SwitchLeaf28", .int 1 0) :: s27.env } :=
      hbase27.consOne (n := "%SwitchLeaf28") (v := .int 1 0) (by decide)
    exact hh.congr_env rfl
  have hlift : ∀ (n : String) (v : Value), "%SwitchLeaf28" ≠ n →
      lookupName s27.env n = some v → lookupName sMid.env n = some v := by
    intro n v hne hv
    simp only [sMid, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ hne]
    exact hv
  have hbL (n : String) (v : Value) (hv : (n, v) ∈ stage2NoEventWalkBaseValues K) :
      lookupName sMid.env n = some v := hbaseMid n v hv
  have htokN : K.tok + 1 ≤ K.n := by
    have hc : K.tok ≤ k := h.count
    have h1 : K.nep ≤ K.n := h.inv.nepLe
    have h2 := hklt
    omega
  have hinvMidKc : Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem sMid :=
    Stage2NoEventWalkInv.stringArena L27.inv' htokN
  have hlen63 : len < 2 ^ 63 := by
    have h0 := h.inv.inside next (List.mem_of_getElem? hk1)
    have h1 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hlenLt64 : len < 2 ^ 64 := by omega
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp h.inv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextComma : next < comma := by
    obtain ⟨h1, h1v⟩ := List.getElem?_eq_some_iff.mp hk1
    obtain ⟨h2, h2v⟩ := List.getElem?_eq_some_iff.mp hcommaEnt
    have hh := (List.pairwise_iff_getElem.mp h.inv.order) (k + 1) (k + 2) h1 h2 (by omega)
    rw [h1v, h2v] at hh
    exact hh
  have hlq : lane ≤ comma := by omega
  have hqN : comma ≤ K.n := le_of_lt (h.inv.inside comma (List.mem_of_getElem? hcommaEnt))
  have hdelta : len + 2 ≤ comma - lane := by omega
  have hspan : lane + 2 ≤ next + 1 := by omega
  have hkAddr : k + 3 < 2 ^ 63 := by
    have h1 := h.inv.maxDoc
    have h2 := h.inv.nepLe
    simp only [stage2MaxDocument] at h1
    omega
  have hquote : K.bs[lane]? = some (34 : UInt8) := by
    have hbyte34 : byte = (34 : UInt8) := by
      apply UInt8.toNat_inj.mp
      simpa using hb
    rw [hbs, hbyte34]
  by_cases h8 : len < 8
  · obtain ⟨sA, jA, hjA, hrunA, hpcA, hpreA, hmemA, hAalen, hAarena, hAtok, hAterms, hAfr,
      hAsp, hAinc, hbaseA⟩ :=
      stage2NoEventWalkStringArenaB_short (gap := gap) (K := K) (s := sMid) (mem := r.mem)
        (sc := K.scratch) (arenaWord := K.arenaWord) (alen := K.arena.length) (len := len)
        (tokens := K.tok) (terms := K.terms) (outn := K.next0 + 16) (spv := sp)
        (body := body) (inc217 := BitVec.ofNat 64 (k + 2)) (fr := BitVec.ofNat 8 fr)
        (xt := BitVec.ofNat 64 0) hpcMid hmemMid
        (hbL "%outn205" (.ptr (K.next0 + 16)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
            entryCells2, entryCells3, entryCells4, preHeaderCells]))
        hreadOutn hlenLt64 hlen0 h8
        (hbL "%scratch" (.ptr K.scratch) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
        (hlift "%alen.0.ph1405" _ (by decide) halen27)
        (hlift "%tokens.0.lcssa1075" _ (by decide) htok27)
        (hlift "%terms.0.lcssa1081" _ (by decide) hterms27)
        (hlift "%inc217" _ (by decide) hinc27)
        (hlift "%sp.0.lcssa1093.wide" _ (by decide) hsp27)
        (hlift "%frame.0.lcssa1099" _ (by decide) hfr27) hbaseMid
        (hlift "%arena.0.ph1406" _ (by decide) harena27) hbodyRead hbodyLen
    have hlenEq : len + K.arena.length =
        (stage2NoEventWalkStringCarry K len body).arena.length := by
      rw [stage2NoEventWalkStringCarry_arena, List.length_append, hbodyLen]
      omega
    have htermsEq : ((K.arena.length + 6) + len) + K.terms =
        (stage2NoEventWalkStringCarry K len body).terms := by
      show ((K.arena.length + 6) + len) + K.terms =
        K.terms + (EventRecord.tagStr + len + K.arena.length)
      rw [EventRecord.tagStr]
      omega
    have hInvA : Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem sA :=
      hinvMidKc.mem_congr (by rw [hmemA, hmemMid])
    have hafter : Stage2NoEventWalkStringAfter
        (stage2NoEventWalkStringCarry K len body) (k + 2) fr sp sA :=
      stage2NoEventWalkStringAfter_of_lookups (Kc := stage2NoEventWalkStringCarry K len body)
        (kc := k + 2) hpreA hAfr hAsp
        (by rw [hAinc]) (by rw [hAalen, hlenEq]) hAarena
        (by rw [hAterms, htermsEq]) hAtok
    let route : Stage2NoEventWalkStringRoute (stage2NoEventCalls gap) mem K k s :=
     stage2NoEventWalkStringRoute_arena (calls := stage2NoEventCalls gap) (mem := mem)
      (K := K) (k := k) (s := s) htrace
      (sMid := sMid) (sA := sA) (jHead := 8) (jTail := jA) (lane := lane) (len := len)
      (q := comma) (frame := fr) (sp := sp) (body := body) (cs := cs) (nextLane := next)
      hseg8 ⟨hrunA, hInvA⟩ hpcA hafter hfrLt hfrNe hspLt hspNe hkAddr
      (by rw [stage2NoEventWalkStringCarry]; exact hklt)
      hk hcommaEnt hlq hqN (le_rfl) hdelta (by
        show Stage2NoEventWalkBaseLookups (stage2NoEventWalkStringCarry K len body) sA
        exact hbaseA) h.bPos hcomma hquote hspan hcode hbelow hbodyLen hdecode
    exact ⟨stage2NoEventWalkStringRow_short h htrace route hjA⟩
  · have h8' : 8 ≤ len := by omega
    obtain ⟨sA, jA, hjA, hrunA, hpcA, hpreA, hmemA, hAalen, hAarena, hAtok, hAterms, hAfr,
      hAsp, hAinc, hbaseA⟩ :=
      stage2NoEventWalkStringArenaB_long (gap := gap) (K := K) (s := sMid) (mem := r.mem)
        (sc := K.scratch) (arenaWord := K.arenaWord) (alen := K.arena.length) (len := len)
        (tokens := K.tok) (terms := K.terms) (outn := K.next0 + 16) (spv := sp)
        (body := body) (inc217 := BitVec.ofNat 64 (k + 2)) (fr := BitVec.ofNat 8 fr)
        (xt := BitVec.ofNat 64 0) hpcMid hmemMid
        (hbL "%outn205" (.ptr (K.next0 + 16)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
            entryCells2, entryCells3, entryCells4, preHeaderCells]))
        hreadOutn hlen63 h8'
        (hbL "%scratch" (.ptr K.scratch) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
        (hbL "%invariant.gep1650" (.ptr (K.scratch + 1)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1652" (.ptr (K.scratch + 2)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1654" (.ptr (K.scratch + 3)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1656" (.ptr (K.scratch + 4)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1658" (.ptr (K.scratch + 5)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1660" (.ptr (K.scratch + 6)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hbL "%invariant.gep1662" (.ptr (K.scratch + 7)) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
        (hlift "%alen.0.ph1405" _ (by decide) halen27)
        (hlift "%tokens.0.lcssa1075" _ (by decide) htok27)
        (hlift "%terms.0.lcssa1081" _ (by decide) hterms27)
        (hlift "%inc217" _ (by decide) hinc27)
        (hlift "%sp.0.lcssa1093.wide" _ (by decide) hsp27)
        (hlift "%frame.0.lcssa1099" _ (by decide) hfr27) hbaseMid
        (hlift "%arena.0.ph1406" _ (by decide) harena27) hbodyRead hbodyLen
    have hlenEq : len + K.arena.length =
        (stage2NoEventWalkStringCarry K len body).arena.length := by
      rw [stage2NoEventWalkStringCarry_arena, List.length_append, hbodyLen]
      omega
    have htermsEq : ((K.arena.length + 6) + len) + K.terms =
        (stage2NoEventWalkStringCarry K len body).terms := by
      show ((K.arena.length + 6) + len) + K.terms =
        K.terms + (EventRecord.tagStr + len + K.arena.length)
      rw [EventRecord.tagStr]
      omega
    have hInvA : Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem sA :=
      hinvMidKc.mem_congr (by rw [hmemA, hmemMid])
    have hafter : Stage2NoEventWalkStringAfter
        (stage2NoEventWalkStringCarry K len body) (k + 2) fr sp sA :=
      stage2NoEventWalkStringAfter_of_lookups (Kc := stage2NoEventWalkStringCarry K len body)
        (kc := k + 2) hpreA hAfr hAsp
        (by rw [hAinc]) (by rw [hAalen, hlenEq]) hAarena
        (by rw [hAterms, htermsEq]) hAtok
    let route : Stage2NoEventWalkStringRoute (stage2NoEventCalls gap) mem K k s :=
     stage2NoEventWalkStringRoute_arena (calls := stage2NoEventCalls gap) (mem := mem)
      (K := K) (k := k) (s := s) htrace
      (sMid := sMid) (sA := sA) (jHead := 8) (jTail := jA) (lane := lane) (len := len)
      (q := comma) (frame := fr) (sp := sp) (body := body) (cs := cs) (nextLane := next)
      hseg8 ⟨hrunA, hInvA⟩ hpcA hafter hfrLt hfrNe hspLt hspNe hkAddr
      (by rw [stage2NoEventWalkStringCarry]; exact hklt)
      hk hcommaEnt hlq hqN (le_rfl) hdelta (by
        show Stage2NoEventWalkBaseLookups (stage2NoEventWalkStringCarry K len body) sA
        exact hbaseA) h.bPos hcomma hquote hspan hcode hbelow hbodyLen hdecode
    exact ⟨stage2NoEventWalkStringRow_long h htrace route hjA⟩

/-- **The string class's continuing row, empty-string arm.** -/
noncomputable def stage2NoEventWalkStringRow_plainArm {gap : Calls} {F : Nat}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State} {fr sp : Nat}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hfrPhi : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPhi : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    {lane next comma : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 34)
    (hk1 : K.ent[k + 1]? = some next)
    (hcommaEnt : K.ent[k + 2]? = some comma)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hklt : k + 3 < K.nep)
    (hfrLt : fr < 2 ^ 8) (hfrNe : fr ≠ 0) (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a)
    (hcodeEmpty : bodyCodePoints K.bs ⟨lane, lane + 2⟩ = some [])
    (hsubZero : next - lane - 1 = 0) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  classical
  refine Classical.choice (show Nonempty
    (Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s) from ?_)
  let w := stage2NoEventWalkStringHeadToLeaf27 (gap := gap) h hfrPhi hspPhi hk hbs hb hk1 hklt
    (form := 1) hret (Or.inl rfl) (by decide) hscratch hcall hframe hfoot hpresent
  let s27 : State := Classical.choose w
  obtain ⟨hseg7, hinv27, hbase27, hpc27, hmem27, hcall243, halen27, harena27, htok27,
    hterms27, hinc27, hfr27, hsp27, hsub27, hlc27⟩ := Classical.choose_spec w
  have hy27 : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 1) = 1 :=
    stage2NoEventWalkStringRowEq_one rfl
  have L27 := link_leafBlock27_true (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s27) (v := BitVec.ofNat 32 1) hinv27 hpc27 hcall243 hy27
  let sMid : State := stage2NoEventWalkNext
    (("%SwitchLeaf28", .int 1 1) :: s27.env) s27 "do.body254"
  have hpcMid : sMid.pc = "do.body254" := rfl
  have hseg8 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sMid 8 :=
    hseg7.trans (stage2NoEventWalkStringRowLinkSegment L27)
  have hbaseMid : Stage2NoEventWalkBaseLookups K sMid := by
    have hh : Stage2NoEventWalkBaseLookups K
        { s27 with env := ("%SwitchLeaf28", .int 1 1) :: s27.env } :=
      hbase27.consOne (n := "%SwitchLeaf28") (v := .int 1 1) (by decide)
    exact hh.congr_env rfl
  have hlift : ∀ (n : String) (v : Value), "%SwitchLeaf28" ≠ n →
      lookupName s27.env n = some v → lookupName sMid.env n = some v := by
    intro n v hne hv
    simp only [sMid, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ hne]
    exact hv
  have hbL (n : String) (v : Value) (hv : (n, v) ∈ stage2NoEventWalkBaseValues K) :
      lookupName sMid.env n = some v := hbaseMid n v hv
  have htokN : K.tok + 1 ≤ K.n := by
    have hc : K.tok ≤ k := h.count
    have h1 : K.nep ≤ K.n := h.inv.nepLe
    have h2 := hklt
    omega
  have hsubMid : lookupName sMid.env "%sub234" = some (.int 64 (BitVec.ofNat 64 0)) := by
    rw [← hsubZero]
    exact hlift "%sub234" _ (by decide) hsub27
  have hspLt32 : lane < 2 ^ 32 := by
    have h0 := h.inv.inside lane (List.mem_of_getElem? hk)
    have h1 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hlane1 : lane + 1 < 2 ^ 32 := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp h.inv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    have h0 := h.inv.inside next (List.mem_of_getElem? hk1)
    have h1 := h.inv.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  obtain ⟨sA, jA, hjA, hsegTail, hpcA, hafter, hInvA, hbaseA⟩ :=
    stage2NoEventWalkStringPlainTail (gap := gap) (K := K) (mem := mem) (k := k)
      (s := sMid) (lane := lane) (fr := fr) (sp := sp) (outn := K.next0 + 16)
      L27.inv' hpcMid (hlift "%.lcssa1125" _ (by decide) hlc27) hsubMid
      (hlift "%tokens.0.lcssa1075" _ (by decide) htok27)
      (hlift "%terms.0.lcssa1081" _ (by decide) hterms27)
      (hlift "%alen.0.ph1405" _ (by decide) halen27)
      (hlift "%arena.0.ph1406" _ (by decide) harena27)
      (hbL "%outn205" (.ptr (K.next0 + 16)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hlift "%frame.0.lcssa1099" _ (by decide) hfr27)
      (hlift "%sp.0.lcssa1093.wide" _ (by decide) hsp27)
      (hlift "%inc217" _ (by decide) hinc27) hbaseMid hspLt32 hlane1 htokN
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp h.inv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextComma : next < comma := by
    obtain ⟨h1, h1v⟩ := List.getElem?_eq_some_iff.mp hk1
    obtain ⟨h2, h2v⟩ := List.getElem?_eq_some_iff.mp hcommaEnt
    have hh := (List.pairwise_iff_getElem.mp h.inv.order) (k + 1) (k + 2) h1 h2 (by omega)
    rw [h1v, h2v] at hh
    exact hh
  have hlq : lane ≤ comma := by omega
  have hqN : comma ≤ K.n := le_of_lt (h.inv.inside comma (List.mem_of_getElem? hcommaEnt))
  have hdelta : 0 + 2 ≤ comma - lane := by omega
  have hspan : lane + 2 ≤ next + 1 := by omega
  have hkAddr : k + 3 < 2 ^ 63 := by
    have h1 := h.inv.maxDoc
    have h2 := h.inv.nepLe
    simp only [stage2MaxDocument] at h1
    omega
  have hquote : K.bs[lane]? = some (34 : UInt8) := by
    have hbyte34 : byte = (34 : UInt8) := by
      apply UInt8.toNat_inj.mp
      simpa using hb
    rw [hbs, hbyte34]
  let route : Stage2NoEventWalkStringRoute (stage2NoEventCalls gap) mem K k s :=
   stage2NoEventWalkStringRoute_plain (calls := stage2NoEventCalls gap) (mem := mem)
    (K := K) (k := k) (s := s) htrace
    (sMid := sMid) (sA := sA) (jHead := 8) (jTail := jA) (lane := lane) (q := comma)
    (frame := fr) (sp := sp)
    hseg8 hsegTail hpcA hafter hfrLt hfrNe hspLt hspNe hkAddr hklt hk hcommaEnt hlq hqN
    (le_rfl) hdelta (by
      show Stage2NoEventWalkBaseLookups (stage2NoEventWalkStringCarryPlain K lane) sA
      exact hbaseA) h.bPos hcomma hquote hcodeEmpty
  exact ⟨stage2NoEventWalkStringRow_plain h htrace route hjA⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkStringPotential
#print axioms stage2NoEventWalkStringRow_cont_of_route
#print axioms stage2NoEventWalkStringRow_short
#print axioms stage2NoEventWalkStringRow_long
#print axioms stage2NoEventWalkStringRow_plain
#print axioms stage2NoEventWalkStringRoute_arena
#print axioms stage2NoEventWalkStringRoute_plain
#print axioms stage2NoEventWalkCleanup287Plain_step
#print axioms Stage2NoEventWalkInv.stringPlain
#print axioms stage2NoEventWalkStringPlainTerms
#print axioms stage2NoEventWalkStringPlainTail
#print axioms stage2NoEventWalkPresent_writeBytes
#print axioms Stage2NoEventWalkInv.of_frame
#print axioms Stage2NoEventWalkInv.stringPlain_mem_congr
#print axioms stage2NoEventWalkBaseValues_stringCarry
#print axioms stage2NoEventWalkBaseValues_stringCarryPlain
#print axioms Stage2NoEventWalkInv.stringArena
#print axioms stage2NoEventWalkStringEntrySegment
#print axioms stage2NoEventWalkStringAfter_of_lookups
#print axioms stage2NoEventWalkStringRow_arena
#print axioms stage2NoEventWalkStringRow_plainArm
#print axioms stage2NoEventWalkReadLanes32_of_frame
#print axioms stage2NoEventWalkStringHeadToLeaf27
#print axioms stage2NoEventWalkStringArenaArm

end LeanLLVM.Refinement
