/-
The no-event walk's value class row: the scalar route, the value arms, and the
shared cycle.

A scalar head consumes one entry: `NodeBlock5`'s value arm sends it to `scalar`,
the skip loop stops at the token's extent, and the number-or-literal arms below
`if.end457` build the event, store the counts at `if.end545`, and stop at
`after_value`'s entry.  The shared cycle then reads the following comma and
returns to the next head.

This module owns the **composition**: given the class route's two measured
slices — the provider's route to the arm's entry and the arm's own route to
`after_value` — it assembles the after-value endpoint's `Stage2NoEventWalkCycleSrc`,
runs the shared cycle, and concludes `Stage2NoEventWalkRow.cont` through
`stage2NoEventWalkRow_cont_of_afterValue`.  The price is proved from the two
slice counts, not from an advertised class bound: the provider's measured count
is relative to the scan's stop `q`, and the arm's is relative to `q` and the
skip bound `cond`.

**The measured price.**  Let `d = cond − lane` be the distance from the entry's
lane to the scan's bound (the next entry, or the document's end) and `g = cond − q`
the separator run.  The provider's route costs at most `18 + 5·(q − lane)` and the
arm's own count is

* number: `3 + 5·g`,
* `true`/`false`: `18 + 5·g` (a 4- or 5-byte literal and the chain's thirteen),
* `null`: `19 + 5·g`.

The composed route is at most `21 + 5·d` (number) and `36/37 + 5·d` (the
literals, whose stops put `d ≥ 4`), each against the credit
`32 + 8·d`.  At the worst measured instance (`d = 20`, a 4-byte `true`, sixteen
trailing blanks) the measured total is `38 + 98 = 136`, inside `192`.

**What this module takes from its callers.**  The two slice segments are the
class's own route facts, supplied as `Stage2NoEventWalkValueRoute`: the head-to-
`after_value` counted segment, the endpoint's dispatch window, the carry's
static equalities, the base lookups, the trace, the continuation's comma, and the
two measured slice counts.  The route's `seg` carries the invariant at the
endpoint, exactly as `Stage2NoEventWalkSegment.trans` would.  This is the same
class-fact surface the container row's staging facts occupy; the module's job is
the value class's endpoint and price, and the row itself.

**What this module contributes, and what it does not.**  The endpoint state, its
carry, the invariant, the registers, the base lookups and the two slice counts
come from `JsonStage2NoEventWalkValue`, `JsonStage2NoEventWalkScalar` and
`JsonStage2NoEventWalkDispatchValueArmsB`.  This module contributes the four
per-arm rows (`stage2NoEventWalkValueRow_number/_literalTrue/_literalFalse/
_literalNull`) and the generic `stage2NoEventWalkValueRow_of_head`.

It does **not** fill the value class's `hvalue` slot: that slot demands a `Row`
at every head of the class, each wrapper is instantiable only at its own arm's
state, and no producer exists for the whitespace/remainder arm.  The per-arm
facts are the wrappers' premises, and deriving them is the class producer's
job: the number's `Decimal` decomposition has no slice→`Decimal` function in this
tree (`Decimal` is the parsed `neg/ip/fr/ex`), and the scan exports only the first
whitespace of `[q, cond)`, not the run the separator loop needs.  The slot stays a
parameter; `JsonStage2NoEventWalkRowsAssemble`'s `Stage2NoEventWalkValueReady`
names it.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerB
import LeanLLVM.Refinement.JsonStage2NoEventWalkDispatchValueArmsB
import LeanLLVM.Refinement.JsonStage2NoEventWalkValue
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDispatch

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The class route's data

The value class's route to `after_value`'s entry, at the carry the route builds
(`tok + 1`, and the arm's `terms` delta), with the endpoint's dispatch window and
the continuation's facts.  The two slice counts are kept apart so the composed
price is proved from them. -/

/-- **The value class's route to the after-value endpoint.**  `seg` is the
provider's route composed with the arm's, at price `jprov + jarm`; `after` is the
endpoint's seven `phi` inputs; the rest are the static and staging facts the
cycle's source needs.  `provBound` is the provider slice's measured count
relative to the scan's stop `q`. -/
structure Stage2NoEventWalkValueRoute (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The provider slice's endpoint: the arm's entry. -/
  e : State
  /-- The carry the value route builds. -/
  K' : Stage2NoEventWalkCarry
  /-- The state at `after_value`'s entry. -/
  sA : State
  /-- The provider slice's count, from the head to the arm's entry. -/
  jprov : Nat
  /-- The arm slice's count, from the arm's entry to `after_value`. -/
  jarm : Nat
  /-- The entry's lane (the head's). -/
  lane : Nat
  /-- The scan's stop, inside `[lane, cond]`. -/
  q : Nat
  /-- The scan's bound: the next entry's position or the document's length. -/
  cond : Nat
  /-- The frame word at the endpoint. -/
  fr : Nat
  /-- The depth word at the endpoint. -/
  sp : Nat
  /-- The endpoint's index cell `%inc.lcssa`. -/
  knext : Nat
  /-- The provider slice's counted route, from the head to the arm's entry. -/
  provSeg : Stage2NoEventWalkSegment calls mem K s K e jprov
  /-- The arm slice's counted route, from its entry to `after_value`. -/
  armSeg : Stage2NoEventWalkSegment calls mem K e K' sA jarm
  /-- The endpoint's dispatch window, at the carry's counts. -/
  after : valueArmsAfter K' fr sp knext
    (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) sA
  frameLt : fr < 2 ^ 8
  frameNe : fr ≠ 0
  spLt : sp < 2 ^ 32
  spNe : sp ≠ 0
  /-- The endpoint's index is the head's successor. -/
  knextEq : knext = k + 1
  /-- The continuation has a following entry and a following head. -/
  klt : k + 2 < K'.nep
  /-- The route consumes one event. -/
  tokEq : K'.tok = K.tok + 1
  nepEq : K'.nep = K.nep
  nEq : K'.n = K.n
  entEq : K'.ent = K.ent
  a12Eq : K'.a12 = K.a12
  next0Eq : K'.next0 = K.next0
  /-- The entry chain's stable live-ins survived the route. -/
  base : Stage2NoEventWalkBaseLookups K' sA
  bPos : 1 ≤ K'.b
  /-- The route's output evidence. -/
  trace : Stage2NoEventWalkTrace K'
  /-- The byte at the endpoint's index is the comma the cycle reads. -/
  comma : ∀ lane, K'.ent[knext]? = some lane → K'.bs.getD lane 0 = 44
  /-- The head's lane. -/
  laneEq : K.ent[k]? = some lane
  /-- Every entry starts inside the document. -/
  condLeN : cond ≤ K.n
  laneLeQ : lane ≤ q
  qLeCond : q ≤ cond
  /-- The provider slice's measured count, relative to the scan's stop. -/
  provBound : jprov ≤ 18 + 5 * (q - lane)

/-- **The route's counted segment is the two slices composed.**  `Segment.trans`
adds the counts and keeps the second slice's target invariant. -/
theorem Stage2NoEventWalkValueRoute.seg {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (r : Stage2NoEventWalkValueRoute calls mem K k s) :
    Stage2NoEventWalkSegment calls mem K s r.K' r.sA (r.jprov + r.jarm) :=
  r.provSeg.trans r.armSeg

/-! ### The provider half

The strengthened provider export carries the arm-entry register bundle and the
scan's `q`-relative count.  This section packs its conclusion as the route's
first segment and the facts the arm half consumes. -/

/-- **The provider slice's export**: the head-to-arm-entry segment, the
arm-entry registers, and the scan's measured stop. -/
structure Stage2NoEventWalkValueProv (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The arm's entry. -/
  e : State
  /-- The provider's count. -/
  j : Nat
  /-- The scan's stop and bound, and the entry's lane. -/
  (q cond lane : Nat)
  /-- The value's byte. -/
  byte : UInt8
  /-- The frame and depth words carried to the arm. -/
  (sp fr : Nat)
  /-- The head-to-arm-entry segment. -/
  seg : Stage2NoEventWalkSegment calls mem K s K e j
  /-- The arm-entry registers. -/
  regs : Stage2NoEventWalkValueArmsRegs K k lane sp fr
    (BitVec.ofNat 8 byte.toNat) q cond e
  laneLt : lane < 2 ^ 32
  laneEq : K.ent[k]? = some lane
  byteEq : K.bs[lane]? = some byte
  read : readBytes s.mem (K.b + lane) 1 = some [byte]
  /-- The scan's stop is inside the entry's extent. -/
  laneLeQ : lane ≤ q
  qLeCond : q ≤ cond
  condLeN : cond ≤ K.n
  qLt64 : q < 2 ^ 64
  condLt63 : cond < 2 ^ 63
  /-- The provider's measured count, relative to the scan's stop. -/
  provBound : j ≤ 18 + 5 * (q - lane)
  /-- The entry chain's stable live-ins at the arm's entry. -/
  base : Stage2NoEventWalkBaseLookups K e

/-- **The provider slice, from a head.**  The value class supplies the byte's
three inequalities; the strengthened export supplies the run, the invariant, the
registers, and the `q`-relative count. -/
noncomputable def stage2NoEventWalkValueProv_of_head {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadValueClass K k s) :
    Stage2NoEventWalkValueProv calls mem K k s := by
  classical
  let lane := Classical.choose hclass
  let byte := Classical.choose (Classical.choose_spec hclass)
  have hspec := Classical.choose_spec (Classical.choose_spec hclass)
  have hent : K.ent[k]? = some lane := hspec.1
  have hbs : K.bs[lane]? = some byte := hspec.2.1
  have hread : readBytes s.mem (K.b + lane) 1 = some [byte] := hspec.2.2.1
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) :=
    hspec.2.2.2.1
  have h34 : byte.toNat ≠ 34 := by
    intro hc; exact hspec.2.2.2.2.1 hc
  have h91 : byte.toNat ≠ 91 := by
    intro hc; exact hspec.2.2.2.2.2.1 hc
  have h123 : byte.toNat ≠ 123 := by
    intro hc; exact hspec.2.2.2.2.2.2 hc
  have hy34 : (BitVec.ofNat 8 byte.toNat) ≠ BitVec.ofNat 8 34 := by
    intro hc
    have h := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (UInt8.toNat_lt byte), Nat.mod_eq_of_lt (by decide : 34 < 2 ^ 8)] at h
    exact h34 h
  have hy91 : (BitVec.ofNat 8 byte.toNat) ≠ BitVec.ofNat 8 91 := by
    intro hc
    have h := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (UInt8.toNat_lt byte), Nat.mod_eq_of_lt (by decide : 91 < 2 ^ 8)] at h
    exact h91 h
  have hy123 : (BitVec.ofNat 8 byte.toNat) ≠ BitVec.ofNat 8 123 := by
    intro hc
    have h := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (UInt8.toNat_lt byte), Nat.mod_eq_of_lt (by decide : 123 < 2 ^ 8)] at h
    exact h123 h
  choose e' j q cond lane' byte' sp fr hbody using
    stage2NoEventWalkValue (calls := calls) (K := K) (mem := mem) (k := k) (s := s)
      (y := BitVec.ofNat 8 byte.toNat) h h3 hy34 hy91 hy123
  have hent' : K.ent[k]? = some lane' := hbody.1
  have hlane32 : lane' < 2 ^ 32 := hbody.2.1
  have hbs' : K.bs[lane']? = some byte' := hbody.2.2.1
  have hread' : readBytes s.mem (K.b + lane') 1 = some [byte'] := hbody.2.2.2.1
  have hjQ : j ≤ 18 + 5 * (q - lane') :=
    hbody.2.2.2.2.2.1
  have hlaneq : lane' ≤ q :=
    hbody.2.2.2.2.2.2.2.2.1
  have hqcond : q ≤ cond :=
    hbody.2.2.2.2.2.2.2.2.2.1
  have hcondn : cond ≤ K.n :=
    hbody.2.2.2.2.2.2.2.2.2.2.1
  have hinv : Stage2NoEventWalkInv K mem e' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hregs : Stage2NoEventWalkValueArmsRegs K k lane' sp fr
      (BitVec.ofNat 8 byte'.toNat) q cond e' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrun : ∀ n, runFuel calls (j + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody e' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbaseE : Stage2NoEventWalkBaseLookups K e' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlaneEq : lane = lane' := Option.some.inj (by rw [← hent, hent'])
  subst hlaneEq
  have hbyteEq : byte = byte' := Option.some.inj (by rw [← hbs, hbs'])
  subst hbyteEq
  have hq64 : q < 2 ^ 64 := by have := hinv.nLt; omega
  have hc63 : cond < 2 ^ 63 := by
    have hmax := hinv.maxDoc
    simp only [stage2MaxDocument] at hmax
    omega
  exact
    { e := e'
      j := j
      q := q
      cond := cond
      lane := lane
      byte := byte
      sp := sp
      fr := fr
      seg := ⟨hrun, hinv⟩
      regs := hregs
      laneLt := hlane32
      laneEq := hent
      byteEq := hbs
      read := hread
      laneLeQ := hlaneq
      qLeCond := hqcond
      condLeN := hcondn
      qLt64 := hq64
      condLt63 := hc63
      provBound := hjQ
      base := hbaseE }

/-- **The arm half of the route**: the strengthened arm export's endpoint, its
invariant, the dispatch window, and the continuation facts.  It is the arm
export's conclusion, indexed by the provider's entry state. -/
structure Stage2NoEventWalkValueArmRoute (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (e : State) where
  /-- The carry the arm builds. -/
  K' : Stage2NoEventWalkCarry
  /-- The arm's endpoint (`after_value`'s entry). -/
  sA : State
  /-- The arm's count, its scan window, and its measured price. -/
  (jarm armCount : Nat)
  (q cond : Nat)
  (fr sp knext : Nat)
  /-- The arm's counted segment. -/
  armSeg : Stage2NoEventWalkSegment calls mem K e K' sA jarm
  /-- The endpoint's dispatch window at the carry's counts. -/
  after : valueArmsAfter K' fr sp knext
    (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) sA
  frameLt : fr < 2 ^ 8
  frameNe : fr ≠ 0
  spLt : sp < 2 ^ 32
  spNe : sp ≠ 0
  knextEq : knext = k + 1
  klt : k + 2 < K'.nep
  tokEq : K'.tok = K.tok + 1
  nepEq : K'.nep = K.nep
  nEq : K'.n = K.n
  entEq : K'.ent = K.ent
  a12Eq : K'.a12 = K.a12
  next0Eq : K'.next0 = K.next0
  base : Stage2NoEventWalkBaseLookups K' sA
  bPos : 1 ≤ K'.b
  trace : Stage2NoEventWalkTrace K'
  comma : ∀ lane, K'.ent[knext]? = some lane → K'.bs.getD lane 0 = 44
  /-- The arm slice's own measured count. -/
  armBound : jarm ≤ armCount + 5 * (cond - q)

/-! ### The document slice

The raw read at `[lane, q)` is derivable from `Inv.docAt` and `readBytes_split`;
it is the document's slice, not yet the arm's `d.lexeme` (see the module header). -/

/-- **The document's bytes at `[lane, q)`.** -/
theorem Stage2NoEventWalkInv.readBytes_slice {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {lane q : Nat}
    (hlane : lane < K.n) (hlaneq : lane ≤ q) (hq : q ≤ K.n) :
    readBytes s.mem (K.b + lane) (q - lane) =
      some ((K.bs.drop lane).take (q - lane)) := by
  have hdoc := h.docAt
  obtain ⟨-, hrest⟩ := readBytes_split s.mem K.b lane (K.n - lane) (by
    simpa only [Nat.add_sub_of_le (le_of_lt hlane)] using hdoc)
  have h2 : (q - lane) + (K.n - q) = K.n - lane := by omega
  obtain ⟨hlex, -⟩ := readBytes_split s.mem (K.b + lane) (q - lane) (K.n - q) (by
    simpa only [h2] using hrest)
  exact hlex

/-- **The potential's one-entry fall at the scan's bound.** -/
theorem stage2NoEventWalkPotential_succ {K K' : Stage2NoEventWalkCarry} {k lane cond : Nat}
    (hklt : k < K.nep) (hlane : K.ent[k]? = some lane)
    (hcond : K.ent[k + 1]? = some cond) (hlaneCond : lane ≤ cond)
    (hcondn : cond ≤ K.n)
    (hnep : K'.nep = K.nep) (hn : K'.n = K.n) (hent : K'.ent = K.ent) :
    stage2NoEventWalkPotential K k =
      stage2NoEventWalkPotential K' (k + 1) + (32 + 8 * (cond - lane)) := by
  unfold stage2NoEventWalkPotential
  have hlane' : K.ent.getD k 0 = lane := by
    rw [List.getD_eq_getElem?_getD, hlane]; rfl
  have hcond' : K.ent.getD (k + 1) 0 = cond := by
    rw [List.getD_eq_getElem?_getD, hcond]; rfl
  rw [hnep, hn, hent, hlane', hcond']
  have hne : K.nep - k = (K.nep - (k + 1)) + 1 := by omega
  have hsub : K.n - lane = (K.n - cond) + (cond - lane) := by omega
  rw [hne, hsub]
  omega

/-- **The route from its two halves.** -/
noncomputable def stage2NoEventWalkValueRoute_of_parts {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (prov : Stage2NoEventWalkValueProv calls mem K k s)
    (a : Stage2NoEventWalkValueArmRoute calls mem K k prov.e) :
    Stage2NoEventWalkValueRoute calls mem K k s :=
  { e := prov.e
    K' := a.K'
    sA := a.sA
    jprov := prov.j
    jarm := a.jarm
    lane := prov.lane
    q := prov.q
    cond := prov.cond
    fr := a.fr
    sp := a.sp
    knext := a.knext
    provSeg := prov.seg
    armSeg := a.armSeg
    after := a.after
    frameLt := a.frameLt
    frameNe := a.frameNe
    spLt := a.spLt
    spNe := a.spNe
    knextEq := a.knextEq
    klt := a.klt
    tokEq := a.tokEq
    nepEq := a.nepEq
    nEq := a.nEq
    entEq := a.entEq
    a12Eq := a.a12Eq
    next0Eq := a.next0Eq
    base := a.base
    bPos := a.bPos
    trace := a.trace
    comma := a.comma
    laneEq := prov.laneEq
    condLeN := prov.condLeN
    laneLeQ := prov.laneLeQ
    qLeCond := prov.qLeCond
    provBound := prov.provBound }

/-- **The value class's route, from the head and the arm half.**  The provider
half is the strengthened `stage2NoEventWalkValue`; the arm half is its export
once the endpoint invariant lands.  The route is their two segments side by side,
with the endpoint's fields from the two halves. -/
noncomputable def stage2NoEventWalkValueRoute_of_head {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (arm : ∀ (e : State) (q cond lane sp fr : Nat) (byte : UInt8),
      Stage2NoEventWalkValueArmsRegs K k lane sp fr
        (BitVec.ofNat 8 byte.toNat) q cond e →
      Stage2NoEventWalkValueArmRoute calls mem K k e) :
    Stage2NoEventWalkValueRoute calls mem K k s := by
  classical
  let prov := stage2NoEventWalkValueProv_of_head (calls := calls) h hclass
  let a := arm prov.e prov.q prov.cond prov.lane prov.sp prov.fr prov.byte prov.regs
  exact stage2NoEventWalkValueRoute_of_parts prov a

/-- **The endpoint's after-value `phi` run.**  Every arm leaves `after_value`
from `while.body557` or `if.end545`, and both edges select the same seven
registers the arm's `valueArmsAfter` binds. -/
theorem valueArmsAfter_phiSelects {K : Stage2NoEventWalkCarry} {s : State}
    {fr sp knext : Nat} {tk tm : BitVec 64}
    (h : valueArmsAfter K fr sp knext tk tm s) :
    ∀ p, s.pre = some p → (p = "while.body557" ∨ p = "if.end545") →
      PhiSelects (stateAt s.env s) p afterValuePhiSpecs
        [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
         ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
         ("%k.6", .int 64 (BitVec.ofNat 64 knext)),
         ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
         ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
         ("%terms.8", .int 64 tm),
         ("%tokens.8", .int 64 tk)] := by
  intro p hp hpd
  rcases hpd with rfl | rfl <;>
    refine PhiSelects.cons (op := .reg "%frame.0.lcssa1097") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.0.lcssa1091.wide") (by decide) ?_
        (PhiSelects.cons (op := .reg "%inc.lcssa") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.0.ph1405") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.12") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.12") (by decide) ?_
                  PhiSelects.nil)))))) <;>
    simp only [stateAt, evalOperand, h.frame, h.spLk, h.kLk, h.alen, h.arena,
      h.terms, h.tokens]

/-- **The route's after-value cycle source.**  The endpoint's invariant is the
arm slice's (`armSeg.inv'`), the dispatch window supplies the `phi` run, and the
continuation facts (`count`, `comma`, the base lookups, the target trace) are the
route's. -/
noncomputable def Stage2NoEventWalkValueRoute.cycleSrc {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (route : Stage2NoEventWalkValueRoute calls mem K k s) :
    Stage2NoEventWalkCycleSrc calls mem route.K' route.knext route.sA := by
  have hklt : route.knext + 1 < route.K'.nep := by
    simpa only [route.knextEq] using route.klt
  have hkaddr : route.knext + 1 < 2 ^ 63 := by
    have h1 : route.knext + 1 = k + 2 := by rw [route.knextEq]
    have h2 : k + 2 < route.K'.nep := route.klt
    have h3 : route.K'.nep ≤ route.K'.n := route.armSeg.inv'.nepLe
    have h4 : route.K'.n ≤ 2 ^ 32 := by
      simpa only [stage2MaxDocument] using route.armSeg.inv'.maxDoc
    have h5 : route.K'.nep ≤ 2 ^ 32 := le_trans h3 h4
    have h6 : route.K'.nep < 2 ^ 63 := by omega
    exact lt_of_lt_of_le hklt (le_of_lt h6)
  have hcount : Stage2NoEventWalkCount route.K' route.knext :=
    Stage2NoEventWalkCount.step (a := 1) (b := 1) h.count route.tokEq
      route.knextEq (by omega)
  have hphi : ∃ p, route.sA.pre = some p ∧
      PhiSelects (stateAt route.sA.env route.sA) p afterValuePhiSpecs
        [("%frame.6", .int 8 (BitVec.ofNat 8 route.fr)),
         ("%sp.4", .int 32 (BitVec.ofNat 32 route.sp)),
         ("%k.6", .int 64 (BitVec.ofNat 64 route.knext)),
         ("%alen.8", .int 64 (BitVec.ofNat 64 route.K'.arena.length)),
         ("%arena.10", .int 64 (BitVec.ofNat 64 route.K'.arenaWord)),
         ("%terms.8", .int 64 (BitVec.ofNat 64 route.K'.terms)),
         ("%tokens.8", .int 64 (BitVec.ofNat 64 route.K'.tok))] := by
    rcases route.after.pre with hp | hp
    · exact ⟨"while.body557", hp,
        valueArmsAfter_phiSelects route.after "while.body557" hp (Or.inl rfl)⟩
    · exact ⟨"if.end545", hp,
        valueArmsAfter_phiSelects route.after "if.end545" hp (Or.inr rfl)⟩
  exact
    { inv := route.armSeg.inv'
      pc := route.after.pc
      frame := route.fr
      frameLt := route.frameLt
      frameNe := route.frameNe
      sp := route.sp
      spLt := route.spLt
      spNe := route.spNe
      kAddr := hkaddr
      klt := hklt
      count := hcount
      phiRun := hphi
      baseLookups := route.base
      bPos := route.bPos
      trace := route.trace
      comma := route.comma }

/-- **The value class's continuing row from its route.** -/
noncomputable def stage2NoEventWalkValueRow_cont_of_route {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (_htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcredit : route.jprov + route.jarm +
      stage2NoEventWalkPotential route.K' route.knext ≤
        stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  have hsrc := route.cycleSrc h
  have hknext : route.knext = k + 1 := route.knextEq
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' := Classical.choose cw
  have hcwspec := Classical.choose_spec cw
  let p := Classical.choose hcwspec
  have hcyc : Stage2NoEventWalkCycle calls mem route.K' route.knext route.sA 1 s' p :=
    Classical.choose_spec hcwspec
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F) route.seg hsrc hcyc
    route.nepEq route.a12Eq route.next0Eq (by omega) ?_
  exact hcredit

/-- **The value class's continuing row, from the head and the arm half.**  The
price is the route's own (`hcredit`); the arm wrappers below prove it from the
provider's `q`-relative count and the arm's measured count. -/
noncomputable def stage2NoEventWalkValueRow_of_head {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (arm : ∀ (e : State) (q cond lane sp fr : Nat) (byte : UInt8),
      Stage2NoEventWalkValueArmsRegs K k lane sp fr
        (BitVec.ofNat 8 byte.toNat) q cond e →
      Stage2NoEventWalkValueArmRoute calls mem K k e)
    (hcredit : (stage2NoEventWalkValueRoute_of_head h hclass arm).jprov +
        (stage2NoEventWalkValueRoute_of_head h hclass arm).jarm +
        stage2NoEventWalkPotential
          (stage2NoEventWalkValueRoute_of_head h hclass arm).K'
          (stage2NoEventWalkValueRoute_of_head h hclass arm).knext ≤
      stage2NoEventWalkPotential K k) :
    Stage2NoEventWalkRow calls mem F K k s :=
  stage2NoEventWalkValueRow_cont_of_route h htrace
    (stage2NoEventWalkValueRoute_of_head h hclass arm) hcredit


/-! ### The four arm callbacks

Each callback consumes the strengthened arm export at the provider's entry `e`
and fills `Stage2NoEventWalkValueArmRoute`.  `hbase` is the provider's new
`Stage2NoEventWalkBaseLookups K e`; the arm export carries it to `s'`. -/

/-- **The number arm's route half.** -/
noncomputable def stage2NoEventWalkValueArmRoute_number {calls gap : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {e : State} {σ : Nat → UInt8}
    {lane q cond knext : Nat} {frb : BitVec 8} {spb : BitVec 32} {d : Decimal}
    (hpc : e.pc = "if.then471")
    (hInv : Stage2NoEventWalkInv K mem e)
    (hd : lookupName e.env "%d" = some (.ptr K.d))
    (hei : lookupName e.env "%ei" = some (.ptr (K.next0 + 24)))
    (hee : lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName e.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName e.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hqleK : q ≤ K.n)
    (hlex : readBytes e.mem (K.b + lane) (q - lane) = some d.lexeme.data.toList)
    (hwf : d.wellFormed) (hscan : (numLexScan d.lexeme.data.toList).2 = true)
    (hframe : lookupName e.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName e.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName e.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName e.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName e.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbk : lookupName e.env "%b" = some (.ptr K.b))
    (htk0 : lookupName e.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName e.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hcond : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond →
      readByte
        (writeBytes (writeBytes e.mem (K.next0 + 24) (natToBytes 0 8)) K.d
          (wordBytes 8 (strtodSpec d).toBits)) (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + d.lexeme.length)
    (hslice : (K.bs.drop lane).take (q - lane) = d.lexeme.data.toList)
    (htrace : Stage2NoEventWalkTrace K)
    (hknext : knext = k + 1) (hklt : k + 2 < K.nep)
    (hcount : Stage2NoEventWalkCount K k)
    (hbase : Stage2NoEventWalkBaseLookups K e)
    (hbPos : 1 ≤ K.b)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0)
    (hcomma : ∀ lane, K.ent[knext]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap) :
    Stage2NoEventWalkValueArmRoute calls mem K k e := by
  classical
  have htokn : K.tok < K.n := by
    have h1 : K.tok ≤ k := hcount
    have h2 : K.nep ≤ K.n := hInv.nepLe
    omega
  choose s' j K' hbody using
    stage2NoEventWalkValueNumber (gap := gap) (K := K) (mem := mem) (σ := σ)
      (lane := lane) (q := q) (cond := cond) (knext := knext) (frb := frb)
      (spb := spb) (d := d) hInv hpc hd hei hee hidx harr hlaneq hq64 hqleK
      hlex hwf hscan hframe hsp hk halen harena hbk htk0 htm0 hcond hqle hcond63
      hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  have hrun : ∀ n, runFuel calls (j + n) stage2NoEventBody e =
      runFuel calls n stage2NoEventBody s' := by
    intro n; rw [hcalls]; exact hbody.2.1 n
  have hafter : valueArmsAfter K' frb.toNat spb.toNat knext
      (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) s' := by
    have hkq : BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1 = BitVec.ofNat 64 K'.tok := by
      rw [hbody.2.2.2.2.1]
      exact stage2NoEventWalkOfNat_add 64 K.tok 1
    have htmq : (BitVec.ofNat 64 (strtodSpec d).toBits + BitVec.ofNat 64 7) +
        BitVec.ofNat 64 K.terms = BitVec.ofNat 64 K'.terms := by
      rw [hbody.2.2.2.2.2.1]
      rw [stage2NoEventWalkOfNat_add, stage2NoEventWalkOfNat_add]
      congr 1; omega
    simpa only [hkq, htmq] using hbody.2.2.1
  have hinv' : Stage2NoEventWalkInv K' mem s' := hbody.2.2.2.1
  have htok' : K'.tok = K.tok + 1 := hbody.2.2.2.2.1
  have hterms' : K'.terms = K.terms + (7 + (strtodSpec d).toBits) :=
    hbody.2.2.2.2.2.1
  have hbs' : K'.bs = K.bs := hbody.2.2.2.2.2.2.1
  have harena' : K'.arena = K.arena := hbody.2.2.2.2.2.2.2.1
  have hnep' : K'.nep = K.nep := hbody.2.2.2.2.2.2.2.2.1
  have hn' : K'.n = K.n := hbody.2.2.2.2.2.2.2.2.2.1
  have hent' : K'.ent = K.ent := hbody.2.2.2.2.2.2.2.2.2.2.1
  have ha12' : K'.a12 = K.a12 := hbody.2.2.2.2.2.2.2.2.2.2.2.1
  have hn0' : K'.next0 = K.next0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htrace' : Stage2NoEventWalkTrace K' := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrLt : frb.toNat < 2 ^ 8 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrNe' : frb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspLt : spb.toNat < 2 ^ 32 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspNe' : spb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbase' : Stage2NoEventWalkBaseLookups K' s' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hbEq : K'.b = K.b := by
    have h1 : K'.a12 = [.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] := hinv'.args_eq
    have h2 : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := hInv.args_eq
    have hl : ([.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] : List Value) =
      [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := by
      rw [← h1, ha12', h2]
    have hh := hl
    simp only [List.cons.injEq, Value.ptr.injEq] at hh
    exact hh.1
  have hbPos' : 1 ≤ K'.b := by rw [hbEq]; exact hbPos
  exact
    { K' := K'
      sA := s'
      jarm := j
      armCount := 3
      q := q
      cond := cond
      fr := frb.toNat
      sp := spb.toNat
      knext := knext
      armSeg := ⟨hrun, hinv'⟩
      after := hafter
      frameLt := hfrLt
      frameNe := hfrNe'
      spLt := hspLt
      spNe := hspNe'
      knextEq := hknext
      klt := by rw [hnep']; exact hklt
      tokEq := htok'
      nepEq := hnep'
      nEq := hn'
      entEq := hent'
      a12Eq := ha12'
      next0Eq := hn0'
      base := hbase'
      bPos := hbPos'
      trace := htrace'
      comma := by
        intro lane hlane
        have hkK : K.ent[knext]? = some lane := by rw [← hent']; exact hlane
        rw [hbs']
        exact hcomma lane hkK
      armBound := hbody.1 }

noncomputable def stage2NoEventWalkValueArmRoute_True {calls gap : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {e : State} {σ : Nat → UInt8}
    {lane q cond knext : Nat} {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8}
    (hpc : e.pc = "if.else495")
    (hlc : lookupName e.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 116)))
    (hInv : Stage2NoEventWalkInv K mem e)
    (hee : lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName e.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName e.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hbk : lookupName e.env "%b" = some (.ptr K.b))
    (hcond : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName e.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName e.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName e.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName e.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName e.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName e.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName e.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes e.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1702195828) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte e.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x74, 0x72, 0x75, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (hknext : knext = k + 1) (hklt : k + 2 < K.nep)
    (hcount : Stage2NoEventWalkCount K k)
    (hbase : Stage2NoEventWalkBaseLookups K e)
    (hbPos : 1 ≤ K.b)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0)
    (hcomma : ∀ lane, K.ent[knext]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap) :
    Stage2NoEventWalkValueArmRoute calls mem K k e := by
  classical
  have htokn : K.tok < K.n := by
    have h1 : K.tok ≤ k := hcount
    have h2 : K.nep ≤ K.n := hInv.nepLe
    omega
  choose s' j K' hbody using
    stage2NoEventWalkValueLiteralTrue (gap := gap) (K := K) (mem := mem) (σ := σ)
      (lane := lane) (q := q) (cond := cond) (knext := knext) (frb := frb)
      (spb := spb) (qbytes := qbytes) hInv hpc hlc hee hidx harr hbk hcond htk0 htm0
      hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63
      hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  have hrun : ∀ n, runFuel calls (j + n) stage2NoEventBody e =
      runFuel calls n stage2NoEventBody s' := by
    intro n; rw [hcalls]; exact hbody.2.1 n
  have hafter : valueArmsAfter K' frb.toNat spb.toNat knext
      (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) s' := by
    have hkq : BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1 = BitVec.ofNat 64 K'.tok := by
      rw [hbody.2.2.2.2.1]
      exact stage2NoEventWalkOfNat_add 64 K.tok 1
    have htmq : (BitVec.ofNat 64 8 + BitVec.ofNat 64 K.terms) =
        BitVec.ofNat 64 K'.terms := by
      rw [hbody.2.2.2.2.2.1]
      rw [stage2NoEventWalkOfNat_add]
      congr 1; omega
    simpa only [hkq, htmq] using hbody.2.2.1
  have hinv' : Stage2NoEventWalkInv K' mem s' := hbody.2.2.2.1
  have htok' : K'.tok = K.tok + 1 := hbody.2.2.2.2.1
  have hterms' : K'.terms = K.terms + 8 :=
    hbody.2.2.2.2.2.1
  have hbs' : K'.bs = K.bs := hbody.2.2.2.2.2.2.1
  have harena' : K'.arena = K.arena := hbody.2.2.2.2.2.2.2.1
  have hnep' : K'.nep = K.nep := hbody.2.2.2.2.2.2.2.2.1
  have hn' : K'.n = K.n := hbody.2.2.2.2.2.2.2.2.2.1
  have hent' : K'.ent = K.ent := hbody.2.2.2.2.2.2.2.2.2.2.1
  have ha12' : K'.a12 = K.a12 := hbody.2.2.2.2.2.2.2.2.2.2.2.1
  have hn0' : K'.next0 = K.next0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htrace' : Stage2NoEventWalkTrace K' := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrLt : frb.toNat < 2 ^ 8 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrNe' : frb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspLt : spb.toNat < 2 ^ 32 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspNe' : spb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbase' : Stage2NoEventWalkBaseLookups K' s' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hbEq : K'.b = K.b := by
    have h1 : K'.a12 = [.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] := hinv'.args_eq
    have h2 : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := hInv.args_eq
    have hl : ([.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] : List Value) =
      [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := by
      rw [← h1, ha12', h2]
    have hh := hl
    simp only [List.cons.injEq, Value.ptr.injEq] at hh
    exact hh.1
  have hbPos' : 1 ≤ K'.b := by rw [hbEq]; exact hbPos
  exact
    { K' := K'
      sA := s'
      jarm := j
      armCount := 18
      q := q
      cond := cond
      fr := frb.toNat
      sp := spb.toNat
      knext := knext
      armSeg := ⟨hrun, hinv'⟩
      after := hafter
      frameLt := hfrLt
      frameNe := hfrNe'
      spLt := hspLt
      spNe := hspNe'
      knextEq := hknext
      klt := by rw [hnep']; exact hklt
      tokEq := htok'
      nepEq := hnep'
      nEq := hn'
      entEq := hent'
      a12Eq := ha12'
      next0Eq := hn0'
      base := hbase'
      bPos := hbPos'
      trace := htrace'
      comma := by
        intro lane hlane
        have hkK : K.ent[knext]? = some lane := by rw [← hent']; exact hlane
        rw [hbs']
        exact hcomma lane hkK
      armBound := hbody.1 }


noncomputable def stage2NoEventWalkValueArmRoute_Null {calls gap : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {e : State} {σ : Nat → UInt8}
    {lane q cond knext : Nat} {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8}
    (hpc : e.pc = "if.else495")
    (hlc : lookupName e.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 110)))
    (hInv : Stage2NoEventWalkInv K mem e)
    (hee : lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName e.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName e.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hbk : lookupName e.env "%b" = some (.ptr K.b))
    (hcond : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName e.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName e.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName e.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName e.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName e.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName e.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName e.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes e.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1819047278) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte e.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
    (htrace : Stage2NoEventWalkTrace K)
    (hknext : knext = k + 1) (hklt : k + 2 < K.nep)
    (hcount : Stage2NoEventWalkCount K k)
    (hbase : Stage2NoEventWalkBaseLookups K e)
    (hbPos : 1 ≤ K.b)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0)
    (hcomma : ∀ lane, K.ent[knext]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap) :
    Stage2NoEventWalkValueArmRoute calls mem K k e := by
  classical
  have htokn : K.tok < K.n := by
    have h1 : K.tok ≤ k := hcount
    have h2 : K.nep ≤ K.n := hInv.nepLe
    omega
  choose s' j K' hbody using
    stage2NoEventWalkValueLiteralNull (gap := gap) (K := K) (mem := mem) (σ := σ)
      (lane := lane) (q := q) (cond := cond) (knext := knext) (frb := frb)
      (spb := spb) (qbytes := qbytes) hInv hpc hlc hee hidx harr hbk hcond htk0 htm0
      hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63
      hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  have hrun : ∀ n, runFuel calls (j + n) stage2NoEventBody e =
      runFuel calls n stage2NoEventBody s' := by
    intro n; rw [hcalls]; exact hbody.2.1 n
  have hafter : valueArmsAfter K' frb.toNat spb.toNat knext
      (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) s' := by
    have hkq : BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1 = BitVec.ofNat 64 K'.tok := by
      rw [hbody.2.2.2.2.1]
      exact stage2NoEventWalkOfNat_add 64 K.tok 1
    have htmq : (BitVec.ofNat 64 10 + BitVec.ofNat 64 K.terms) =
        BitVec.ofNat 64 K'.terms := by
      rw [hbody.2.2.2.2.2.1]
      rw [stage2NoEventWalkOfNat_add]
      congr 1; omega
    simpa only [hkq, htmq] using hbody.2.2.1
  have hinv' : Stage2NoEventWalkInv K' mem s' := hbody.2.2.2.1
  have htok' : K'.tok = K.tok + 1 := hbody.2.2.2.2.1
  have hterms' : K'.terms = K.terms + 10 :=
    hbody.2.2.2.2.2.1
  have hbs' : K'.bs = K.bs := hbody.2.2.2.2.2.2.1
  have harena' : K'.arena = K.arena := hbody.2.2.2.2.2.2.2.1
  have hnep' : K'.nep = K.nep := hbody.2.2.2.2.2.2.2.2.1
  have hn' : K'.n = K.n := hbody.2.2.2.2.2.2.2.2.2.1
  have hent' : K'.ent = K.ent := hbody.2.2.2.2.2.2.2.2.2.2.1
  have ha12' : K'.a12 = K.a12 := hbody.2.2.2.2.2.2.2.2.2.2.2.1
  have hn0' : K'.next0 = K.next0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htrace' : Stage2NoEventWalkTrace K' := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrLt : frb.toNat < 2 ^ 8 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrNe' : frb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspLt : spb.toNat < 2 ^ 32 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspNe' : spb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbase' : Stage2NoEventWalkBaseLookups K' s' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hbEq : K'.b = K.b := by
    have h1 : K'.a12 = [.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] := hinv'.args_eq
    have h2 : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := hInv.args_eq
    have hl : ([.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] : List Value) =
      [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := by
      rw [← h1, ha12', h2]
    have hh := hl
    simp only [List.cons.injEq, Value.ptr.injEq] at hh
    exact hh.1
  have hbPos' : 1 ≤ K'.b := by rw [hbEq]; exact hbPos
  exact
    { K' := K'
      sA := s'
      jarm := j
      armCount := 19
      q := q
      cond := cond
      fr := frb.toNat
      sp := spb.toNat
      knext := knext
      armSeg := ⟨hrun, hinv'⟩
      after := hafter
      frameLt := hfrLt
      frameNe := hfrNe'
      spLt := hspLt
      spNe := hspNe'
      knextEq := hknext
      klt := by rw [hnep']; exact hklt
      tokEq := htok'
      nepEq := hnep'
      nEq := hn'
      entEq := hent'
      a12Eq := ha12'
      next0Eq := hn0'
      base := hbase'
      bPos := hbPos'
      trace := htrace'
      comma := by
        intro lane hlane
        have hkK : K.ent[knext]? = some lane := by rw [← hent']; exact hlane
        rw [hbs']
        exact hcomma lane hkK
      armBound := hbody.1 }


noncomputable def stage2NoEventWalkValueArmRoute_False {calls gap : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {e : State} {σ : Nat → UInt8}
    {lane q cond knext : Nat} {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8}
    (hpc : e.pc = "if.else495")
    (hlc : lookupName e.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 102)))
    (hInv : Stage2NoEventWalkInv K mem e)
    (hee : lookupName e.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName e.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName e.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hbk : lookupName e.env "%b" = some (.ptr K.b))
    (hcond : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName e.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName e.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName e.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName e.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName e.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName e.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName e.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes e.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 435728179558) 5) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte e.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 5)
    (hslice : (K.bs.drop lane).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (hknext : knext = k + 1) (hklt : k + 2 < K.nep)
    (hcount : Stage2NoEventWalkCount K k)
    (hbase : Stage2NoEventWalkBaseLookups K e)
    (hbPos : 1 ≤ K.b)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0)
    (hcomma : ∀ lane, K.ent[knext]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap) :
    Stage2NoEventWalkValueArmRoute calls mem K k e := by
  classical
  have htokn : K.tok < K.n := by
    have h1 : K.tok ≤ k := hcount
    have h2 : K.nep ≤ K.n := hInv.nepLe
    omega
  choose s' j K' hbody using
    stage2NoEventWalkValueLiteralFalse (gap := gap) (K := K) (mem := mem) (σ := σ)
      (lane := lane) (q := q) (cond := cond) (knext := knext) (frb := frb)
      (spb := spb) (qbytes := qbytes) hInv hpc hlc hee hidx harr hbk hcond htk0 htm0
      hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63
      hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  have hrun : ∀ n, runFuel calls (j + n) stage2NoEventBody e =
      runFuel calls n stage2NoEventBody s' := by
    intro n; rw [hcalls]; exact hbody.2.1 n
  have hafter : valueArmsAfter K' frb.toNat spb.toNat knext
      (BitVec.ofNat 64 K'.tok) (BitVec.ofNat 64 K'.terms) s' := by
    have hkq : BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1 = BitVec.ofNat 64 K'.tok := by
      rw [hbody.2.2.2.2.1]
      exact stage2NoEventWalkOfNat_add 64 K.tok 1
    have htmq : (BitVec.ofNat 64 9 + BitVec.ofNat 64 K.terms) =
        BitVec.ofNat 64 K'.terms := by
      rw [hbody.2.2.2.2.2.1]
      rw [stage2NoEventWalkOfNat_add]
      congr 1; omega
    simpa only [hkq, htmq] using hbody.2.2.1
  have hinv' : Stage2NoEventWalkInv K' mem s' := hbody.2.2.2.1
  have htok' : K'.tok = K.tok + 1 := hbody.2.2.2.2.1
  have hterms' : K'.terms = K.terms + 9 :=
    hbody.2.2.2.2.2.1
  have hbs' : K'.bs = K.bs := hbody.2.2.2.2.2.2.1
  have harena' : K'.arena = K.arena := hbody.2.2.2.2.2.2.2.1
  have hnep' : K'.nep = K.nep := hbody.2.2.2.2.2.2.2.2.1
  have hn' : K'.n = K.n := hbody.2.2.2.2.2.2.2.2.2.1
  have hent' : K'.ent = K.ent := hbody.2.2.2.2.2.2.2.2.2.2.1
  have ha12' : K'.a12 = K.a12 := hbody.2.2.2.2.2.2.2.2.2.2.2.1
  have hn0' : K'.next0 = K.next0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htrace' : Stage2NoEventWalkTrace K' := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrLt : frb.toNat < 2 ^ 8 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfrNe' : frb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspLt : spb.toNat < 2 ^ 32 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hspNe' : spb.toNat ≠ 0 := hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbase' : Stage2NoEventWalkBaseLookups K' s' :=
    hbody.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hbEq : K'.b = K.b := by
    have h1 : K'.a12 = [.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] := hinv'.args_eq
    have h2 : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := hInv.args_eq
    have hl : ([.ptr K'.b, .int 64 (BitVec.ofNat 64 K'.n), .ptr K'.ep,
      .int 64 (BitVec.ofNat 64 K'.nep), .ptr K'.xp, .int 64 (BitVec.ofNat 64 K'.nxp),
      .ptr K'.scratch, .int 64 (BitVec.ofNat 64 K'.scratchcap), .ptr K'.tokensOut,
      .ptr K'.valuesOut, .ptr K'.sumOut, .ptr K'.err] : List Value) =
      [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err] := by
      rw [← h1, ha12', h2]
    have hh := hl
    simp only [List.cons.injEq, Value.ptr.injEq] at hh
    exact hh.1
  have hbPos' : 1 ≤ K'.b := by rw [hbEq]; exact hbPos
  exact
    { K' := K'
      sA := s'
      jarm := j
      armCount := 18
      q := q
      cond := cond
      fr := frb.toNat
      sp := spb.toNat
      knext := knext
      armSeg := ⟨hrun, hinv'⟩
      after := hafter
      frameLt := hfrLt
      frameNe := hfrNe'
      spLt := hspLt
      spNe := hspNe'
      knextEq := hknext
      klt := by rw [hnep']; exact hklt
      tokEq := htok'
      nepEq := hnep'
      nEq := hn'
      entEq := hent'
      a12Eq := ha12'
      next0Eq := hn0'
      base := hbase'
      bPos := hbPos'
      trace := htrace'
      comma := by
        intro lane hlane
        have hkK : K.ent[knext]? = some lane := by rw [← hent']; exact hlane
        rw [hbs']
        exact hcomma lane hkK
      armBound := hbody.1 }


/-! ### The four arms' prices

Each arm supplies its own measured count; the arithmetic below is the composition
against `32 + 8·(cond − lane)`.  The scan's stop `q` is the arm's entry, so the
two counts add along one extent. -/

/-- **The number arm's composition.**  `18 + 5·(q − lane)` plus `3 + 5·(cond − q)`
is `21 + 5·(cond − lane)`, inside `32 + 8·(cond − lane)`. -/
noncomputable def stage2NoEventWalkValueRow_cont_number {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcondEq : K.ent[k + 1]? = some route.cond)
    (harm : route.jarm ≤ 3 + 5 * (route.cond - route.q)) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hup : route.jprov + route.jarm ≤ 32 + 8 * (route.cond - route.lane) := by
    have hp := route.provBound
    have hl := route.laneLeQ
    have hq := route.qLeCond
    have hsplit : route.cond - route.lane =
        (route.cond - route.q) + (route.q - route.lane) := by omega
    rw [hsplit]
    omega
  have hpot := stage2NoEventWalkPotential_succ (K := K) (K' := route.K')
    (k := k) (lane := route.lane) (cond := route.cond)
    h.klt route.laneEq hcondEq
      (le_trans route.laneLeQ route.qLeCond) route.condLeN route.nepEq route.nEq route.entEq
  refine stage2NoEventWalkValueRow_cont_of_route h htrace route ?_
  rw [route.knextEq]
  omega

/-- **The `true` arm's composition.**  The literal's chain is thirteen steps plus
the four dispatch blocks and the merge; its stop is `q = lane + 4`, so
`d = cond − lane ≥ 4` and `36 + 5·d ≤ 32 + 8·d`. -/
noncomputable def stage2NoEventWalkValueRow_cont_literalTrue {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcondEq : K.ent[k + 1]? = some route.cond)
    (hstop : route.q = route.lane + 4)
    (harm : route.jarm ≤ 18 + 5 * (route.cond - route.q)) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hup : route.jprov + route.jarm ≤ 32 + 8 * (route.cond - route.lane) := by
    have hp := route.provBound
    have hl := route.laneLeQ
    have hq := route.qLeCond
    have hsplit : route.cond - route.lane =
        (route.cond - route.q) + (route.q - route.lane) := by omega
    have hql : route.q - route.lane = 4 := by omega
    rw [hsplit, hql]
    omega
  have hpot := stage2NoEventWalkPotential_succ (K := K) (K' := route.K')
    (k := k) (lane := route.lane) (cond := route.cond)
    h.klt route.laneEq hcondEq
      (le_trans route.laneLeQ route.qLeCond) route.condLeN route.nepEq route.nEq route.entEq
  refine stage2NoEventWalkValueRow_cont_of_route h htrace route ?_
  rw [route.knextEq]
  omega

/-- **The `false` arm's composition.**  A five-byte literal: its stop is
`q = lane + 5` and `36 + 5·d ≤ 32 + 8·d` follows from `d ≥ 5`. -/
noncomputable def stage2NoEventWalkValueRow_cont_literalFalse {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcondEq : K.ent[k + 1]? = some route.cond)
    (hstop : route.q = route.lane + 5)
    (harm : route.jarm ≤ 18 + 5 * (route.cond - route.q)) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hup : route.jprov + route.jarm ≤ 32 + 8 * (route.cond - route.lane) := by
    have hp := route.provBound
    have hl := route.laneLeQ
    have hq := route.qLeCond
    have hsplit : route.cond - route.lane =
        (route.cond - route.q) + (route.q - route.lane) := by omega
    have hql : route.q - route.lane = 5 := by omega
    rw [hsplit, hql]
    omega
  have hpot := stage2NoEventWalkPotential_succ (K := K) (K' := route.K')
    (k := k) (lane := route.lane) (cond := route.cond)
    h.klt route.laneEq hcondEq
      (le_trans route.laneLeQ route.qLeCond) route.condLeN route.nepEq route.nEq route.entEq
  refine stage2NoEventWalkValueRow_cont_of_route h htrace route ?_
  rw [route.knextEq]
  omega

/-- **The `null` arm's composition.**  `19 + 5·(cond − q)` at `q = lane + 4`;
`37 + 5·d ≤ 32 + 8·d` needs only `d ≥ 2`. -/
noncomputable def stage2NoEventWalkValueRow_cont_literalNull {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (route : Stage2NoEventWalkValueRoute calls mem K k s)
    (hcondEq : K.ent[k + 1]? = some route.cond)
    (hstop : route.q = route.lane + 4)
    (harm : route.jarm ≤ 19 + 5 * (route.cond - route.q)) :
    Stage2NoEventWalkRow calls mem F K k s := by
  have hup : route.jprov + route.jarm ≤ 32 + 8 * (route.cond - route.lane) := by
    have hp := route.provBound
    have hl := route.laneLeQ
    have hq := route.qLeCond
    have hsplit : route.cond - route.lane =
        (route.cond - route.q) + (route.q - route.lane) := by omega
    have hql : route.q - route.lane = 4 := by omega
    rw [hsplit, hql]
    omega
  have hpot := stage2NoEventWalkPotential_succ (K := K) (K' := route.K')
    (k := k) (lane := route.lane) (cond := route.cond)
    h.klt route.laneEq hcondEq
      (le_trans route.laneLeQ route.qLeCond) route.condLeN route.nepEq route.nEq route.entEq
  refine stage2NoEventWalkValueRow_cont_of_route h htrace route ?_
  rw [route.knextEq]
  omega

/-- **The number arm's row**, from the head and the class facts. -/
noncomputable def stage2NoEventWalkValueRow_number {calls gap : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {σ : Nat → UInt8} {d : Decimal}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (hpc : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.pc =
      "if.then471")
    (hcondEq : K.ent[k + 1]? =
      some (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond)
    (hk2 : k + 2 < K.nep)
    (hfrNe : BitVec.ofNat 8
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).fr ≠ 0)
    (hspNe : BitVec.ofNat 32
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).sp ≠ 0)
    (hcomma : ∀ lane, K.ent[k + 1]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap)
    (hlex : readBytes
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
      (K.b + (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
      ((stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane) =
      some d.lexeme.data.toList)
    (hwf : d.wellFormed)
    (hscan : (numLexScan d.lexeme.data.toList).2 = true)
    (hstop : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q =
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane +
        d.lexeme.length)
    (hslice : (K.bs.drop
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane).take
      ((stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane) =
      d.lexeme.data.toList)
    (hbytes : ∀ i, i <
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      readByte
        (writeBytes
          (writeBytes
            (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
            (K.next0 + 24) (natToBytes 0 8))
          K.d (wordBytes 8 (strtodSpec d).toBits))
        (K.b + i) = some (σ i))
    (hws : ∀ i,
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q ≤ i → i <
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let prov := stage2NoEventWalkValueProv_of_head (calls := calls) h hclass
  have hlaneq : prov.lane ≤ prov.q := prov.laneLeQ
  have hq64 : prov.q < 2 ^ 64 := prov.qLt64
  have hqleK : prov.q ≤ K.n := by have h1 := prov.qLeCond; have h2 := prov.condLeN; omega
  let arm := stage2NoEventWalkValueArmRoute_number (calls := calls) (gap := gap)
    (mem := mem) (K := K) (k := k) (e := prov.e) (σ := σ) (lane := prov.lane)
    (q := prov.q) (cond := prov.cond) (knext := k + 1)
    (frb := BitVec.ofNat 8 prov.fr) (spb := BitVec.ofNat 32 prov.sp) (d := d)
    hpc prov.seg.inv' prov.regs.d prov.regs.ei prov.regs.ee prov.regs.idx
    prov.regs.arr hlaneq hq64 hqleK hlex hwf hscan prov.regs.frame prov.regs.sp
    prov.regs.inc prov.regs.alen prov.regs.arena prov.regs.b prov.regs.tokens
    prov.regs.terms prov.regs.cond prov.qLeCond prov.condLt63 hbytes hws hstop
    hslice htrace rfl hk2 h.count prov.base h.bPos hfrNe hspNe hcomma hcalls
  let route := stage2NoEventWalkValueRoute_of_parts prov arm
  have hcondEq' : K.ent[k + 1]? = some route.cond := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hcondEq
  have harm : route.jarm ≤ 3 + 5 * (route.cond - route.q) := by
    have h := arm.armBound
    have hc : arm.armCount = 3 := rfl
    have hq : arm.q = prov.q := rfl
    have hcd : arm.cond = prov.cond := rfl
    rw [hc, hq, hcd] at h
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using h
  exact stage2NoEventWalkValueRow_cont_number h htrace route hcondEq' harm

noncomputable def stage2NoEventWalkValueRow_literalTrue {calls gap : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {σ : Nat → UInt8}
    {qbytes : List UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (hpc : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.pc =
      "if.else495")
    (hlc : lookupName
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.env "%.lcssa" =
      some (.int 8 (BitVec.ofNat 8 116)))
    (hcondEq : K.ent[k + 1]? =
      some (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond)
    (hk2 : k + 2 < K.nep)
    (hfrNe : BitVec.ofNat 8
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).fr ≠ 0)
    (hspNe : BitVec.ofNat 32
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).sp ≠ 0)
    (hcomma : ∀ lane, K.ent[k + 1]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap)
    (hq4 : 4 ≤
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
    (hlex : readBytes
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
      (K.b + (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
      ((stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane) =
      some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1702195828) 4) = none)
    (hstop : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q =
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane + 4)
    (hslice : (K.bs.drop
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane).take
      4 = [0x74, 0x72, 0x75, 0x65])
    (hbytes : ∀ i, i <
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      readByte
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
        (K.b + i) = some (σ i))
    (hws : ∀ i,
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q ≤ i → i <
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let prov := stage2NoEventWalkValueProv_of_head (calls := calls) h hclass
  have hlaneq : prov.lane ≤ prov.q := prov.laneLeQ
  have hq64 : prov.q < 2 ^ 64 := prov.qLt64
  have hqleK : prov.q ≤ K.n := by have h1 := prov.qLeCond; have h2 := prov.condLeN; omega
  let arm := stage2NoEventWalkValueArmRoute_True (calls := calls) (gap := gap)
    (mem := mem) (K := K) (k := k) (e := prov.e) (σ := σ) (lane := prov.lane)
    (q := prov.q) (cond := prov.cond) (knext := k + 1)
    (frb := BitVec.ofNat 8 prov.fr) (spb := BitVec.ofNat 32 prov.sp)
    hpc hlc prov.seg.inv' prov.regs.ee prov.regs.idx prov.regs.arr prov.regs.b
    prov.regs.cond prov.regs.tokens prov.regs.terms prov.regs.frame prov.regs.sp
    prov.regs.inc prov.regs.alen prov.regs.arena hlaneq hq64 hq4 hlex hval
    prov.qLeCond prov.condLt63 hbytes hws hstop hslice htrace rfl hk2 h.count
    prov.base h.bPos hfrNe hspNe hcomma hcalls
  let route := stage2NoEventWalkValueRoute_of_parts prov arm
  have hcondEq' : K.ent[k + 1]? = some route.cond := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hcondEq
  have harm : route.jarm ≤ 18 + 5 * (route.cond - route.q) := by
    have h := arm.armBound
    have hc : arm.armCount = 18 := rfl
    have hq : arm.q = prov.q := rfl
    have hcd : arm.cond = prov.cond := rfl
    rw [hc, hq, hcd] at h
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using h
  have hstop' : route.q = route.lane + 4 := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hstop
  exact stage2NoEventWalkValueRow_cont_literalTrue h htrace route hcondEq' hstop' harm


noncomputable def stage2NoEventWalkValueRow_literalFalse {calls gap : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {σ : Nat → UInt8}
    {qbytes : List UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (hpc : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.pc =
      "if.else495")
    (hlc : lookupName
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.env "%.lcssa" =
      some (.int 8 (BitVec.ofNat 8 102)))
    (hcondEq : K.ent[k + 1]? =
      some (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond)
    (hk2 : k + 2 < K.nep)
    (hfrNe : BitVec.ofNat 8
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).fr ≠ 0)
    (hspNe : BitVec.ofNat 32
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).sp ≠ 0)
    (hcomma : ∀ lane, K.ent[k + 1]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap)
    (hq4 : 4 ≤
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
    (hlex : readBytes
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
      (K.b + (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
      ((stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane) =
      some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 435728179558) 5) = none)
    (hstop : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q =
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane + 5)
    (hslice : (K.bs.drop
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane).take
      5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (hbytes : ∀ i, i <
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      readByte
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
        (K.b + i) = some (σ i))
    (hws : ∀ i,
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q ≤ i → i <
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let prov := stage2NoEventWalkValueProv_of_head (calls := calls) h hclass
  have hlaneq : prov.lane ≤ prov.q := prov.laneLeQ
  have hq64 : prov.q < 2 ^ 64 := prov.qLt64
  have hqleK : prov.q ≤ K.n := by have h1 := prov.qLeCond; have h2 := prov.condLeN; omega
  let arm := stage2NoEventWalkValueArmRoute_False (calls := calls) (gap := gap)
    (mem := mem) (K := K) (k := k) (e := prov.e) (σ := σ) (lane := prov.lane)
    (q := prov.q) (cond := prov.cond) (knext := k + 1)
    (frb := BitVec.ofNat 8 prov.fr) (spb := BitVec.ofNat 32 prov.sp)
    hpc hlc prov.seg.inv' prov.regs.ee prov.regs.idx prov.regs.arr prov.regs.b
    prov.regs.cond prov.regs.tokens prov.regs.terms prov.regs.frame prov.regs.sp
    prov.regs.inc prov.regs.alen prov.regs.arena hlaneq hq64 hq4 hlex hval
    prov.qLeCond prov.condLt63 hbytes hws hstop hslice htrace rfl hk2 h.count
    prov.base h.bPos hfrNe hspNe hcomma hcalls
  let route := stage2NoEventWalkValueRoute_of_parts prov arm
  have hcondEq' : K.ent[k + 1]? = some route.cond := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hcondEq
  have harm : route.jarm ≤ 18 + 5 * (route.cond - route.q) := by
    have h := arm.armBound
    have hc : arm.armCount = 18 := rfl
    have hq : arm.q = prov.q := rfl
    have hcd : arm.cond = prov.cond := rfl
    rw [hc, hq, hcd] at h
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using h
  have hstop' : route.q = route.lane + 5 := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hstop
  exact stage2NoEventWalkValueRow_cont_literalFalse h htrace route hcondEq' hstop' harm


noncomputable def stage2NoEventWalkValueRow_literalNull {calls gap : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {σ : Nat → UInt8}
    {qbytes : List UInt8}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadValueClass K k s)
    (hpc : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.pc =
      "if.else495")
    (hlc : lookupName
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.env "%.lcssa" =
      some (.int 8 (BitVec.ofNat 8 110)))
    (hcondEq : K.ent[k + 1]? =
      some (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond)
    (hk2 : k + 2 < K.nep)
    (hfrNe : BitVec.ofNat 8
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).fr ≠ 0)
    (hspNe : BitVec.ofNat 32
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).sp ≠ 0)
    (hcomma : ∀ lane, K.ent[k + 1]? = some lane → K.bs.getD lane 0 = 44)
    (hcalls : calls = stage2NoEventCalls gap)
    (hq4 : 4 ≤
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
    (hlex : readBytes
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
      (K.b + (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane)
      ((stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q -
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane) =
      some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1819047278) 4) = none)
    (hstop : (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q =
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane + 4)
    (hslice : (K.bs.drop
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).lane).take
      4 = [0x6E, 0x75, 0x6C, 0x6C])
    (hbytes : ∀ i, i <
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      readByte
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).e.mem
        (K.b + i) = some (σ i))
    (hws : ∀ i,
      (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).q ≤ i → i <
        (stage2NoEventWalkValueProv_of_head (calls := calls) h hclass).cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let prov := stage2NoEventWalkValueProv_of_head (calls := calls) h hclass
  have hlaneq : prov.lane ≤ prov.q := prov.laneLeQ
  have hq64 : prov.q < 2 ^ 64 := prov.qLt64
  have hqleK : prov.q ≤ K.n := by have h1 := prov.qLeCond; have h2 := prov.condLeN; omega
  let arm := stage2NoEventWalkValueArmRoute_Null (calls := calls) (gap := gap)
    (mem := mem) (K := K) (k := k) (e := prov.e) (σ := σ) (lane := prov.lane)
    (q := prov.q) (cond := prov.cond) (knext := k + 1)
    (frb := BitVec.ofNat 8 prov.fr) (spb := BitVec.ofNat 32 prov.sp)
    hpc hlc prov.seg.inv' prov.regs.ee prov.regs.idx prov.regs.arr prov.regs.b
    prov.regs.cond prov.regs.tokens prov.regs.terms prov.regs.frame prov.regs.sp
    prov.regs.inc prov.regs.alen prov.regs.arena hlaneq hq64 hq4 hlex hval
    prov.qLeCond prov.condLt63 hbytes hws hstop hslice htrace rfl hk2 h.count
    prov.base h.bPos hfrNe hspNe hcomma hcalls
  let route := stage2NoEventWalkValueRoute_of_parts prov arm
  have hcondEq' : K.ent[k + 1]? = some route.cond := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hcondEq
  have harm : route.jarm ≤ 19 + 5 * (route.cond - route.q) := by
    have h := arm.armBound
    have hc : arm.armCount = 19 := rfl
    have hq : arm.q = prov.q := rfl
    have hcd : arm.cond = prov.cond := rfl
    rw [hc, hq, hcd] at h
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using h
  have hstop' : route.q = route.lane + 4 := by
    simpa only [route, stage2NoEventWalkValueRoute_of_parts] using hstop
  exact stage2NoEventWalkValueRow_cont_literalNull h htrace route hcondEq' hstop' harm


/-! ### The wrappers' premises

The four wrappers above take the arm's lexical facts — `hlex`/`hval`/`hstop`/
`hslice`, the skip run's `hbytes`/`hws`, and the arm's exit pin — as premises,
because each is a slice the arm's own route supplies.  They build `prov`, apply
the matching arm callback, `route_of_parts`, and the matching price wrapper.  The
number arm is `%ee.1`/`scalar`/`cond.end`; the literal arms are `if.else495`'s
`LeafBlock68` (`t`), `LeafBlock64` (`f`) and `LeafBlock66` (`n`).

The per-arm fact derivation is not written: the number's `Decimal` decomposition
`d` has no slice→`Decimal` function in this tree, and the scan exports only the
first whitespace of `[q, cond)`, not the run.  So no term here fills the value
class's `hvalue` slot; that slot stays a parameter and is named in
`JsonStage2NoEventWalkRowsAssemble`'s `Stage2NoEventWalkValueReady`.
-/

/-! ### The price at the worst measured instance

`d = 20`, a four-byte `true` and sixteen trailing blanks: the provider is
`18 + 5·4 = 38`, the arm `18 + 5·16 = 98`, the composed total `136`, against the
credit `32 + 8·20 = 192`. -/

/-- **The measured composition at the worst instance.** -/
theorem stage2NoEventWalkValueRow_price_check :
    (18 + 5 * 4) + (18 + 5 * 16) ≤ 32 + 8 * 20 := by decide

/-- **The composed price is the two measured counts.** -/
theorem stage2NoEventWalkValueRow_price_check_eq :
    (18 + 5 * 4) + (18 + 5 * 16) = 136 := by decide

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkValueRoute_of_parts
#print axioms stage2NoEventWalkValueRow_number
#print axioms stage2NoEventWalkValueRow_literalTrue
#print axioms stage2NoEventWalkValueRow_literalFalse
#print axioms stage2NoEventWalkValueRow_literalNull
#print axioms stage2NoEventWalkValueArmRoute_number
#print axioms stage2NoEventWalkValueArmRoute_True
#print axioms stage2NoEventWalkValueArmRoute_False
#print axioms stage2NoEventWalkValueArmRoute_Null
#print axioms stage2NoEventWalkValueProv_of_head
#print axioms stage2NoEventWalkValueRoute_of_head
#print axioms stage2NoEventWalkValueRow_of_head
#print axioms valueArmsAfter_phiSelects
#print axioms Stage2NoEventWalkValueRoute.seg
#print axioms Stage2NoEventWalkValueRoute.cycleSrc
#print axioms Stage2NoEventWalkInv.readBytes_slice
#print axioms stage2NoEventWalkPotential_succ
#print axioms stage2NoEventWalkValueRow_cont_of_route
#print axioms stage2NoEventWalkValueRow_cont_number
#print axioms stage2NoEventWalkValueRow_cont_literalTrue
#print axioms stage2NoEventWalkValueRow_cont_literalFalse
#print axioms stage2NoEventWalkValueRow_cont_literalNull
#print axioms stage2NoEventWalkValueRow_price_check

end LeanLLVM.Refinement
