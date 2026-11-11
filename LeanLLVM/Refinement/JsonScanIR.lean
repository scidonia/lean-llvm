/-
The JSON window scanner, at the LLVM level.

`probes/install/ir/json-scan-body.ll` is the rendering of the AST in
`LeanLLVM/Refinement/JsonScanBody.lean`, emitted by `lake exe
leanllvm-json-scan-emit` through `LeanLLVM.Function.render`.  This module pins
the fixture to that AST, and defines and proves the three prefix objects the
body's loop tracks:

* `maskPref` is the structural mask over a window's first `k` lanes, and
  `maskPref_eq_maskOfList` identifies it with the model's `maskOfList` at the
  end of the window;
* `firstStop` is the first stop among the first `k` lanes, and
  `firstStop_eq_stopOf` identifies it with the model's `stopOf` — through
  `windowOf_stop_spec`, whose readback is the public form of the fold's stop;
* `carriedAt` is the carry the body's slot holds after `k` lanes — the model's
  prefix carry, held still once a lane stops — with its per-lane step lemmas
  and `carriedAt_eq_carryAt`, which is the model's `carryAt` at
  `stopLaneOrLength`.

**The statement, and the step that remains.**  `scanWindowStatement` below is the
refinement statement `JsonScanLane`'s header writes, with the band hypothesis that
prose leaves as an ellipsis supplied: the body returns the model's status word,
writes the model's mask at `%out`, leaves the model's carry in the slot, changes no
byte outside its own allocation band and the caller's state region, and leaves the
window it read unchanged.  It is a proposition and not a theorem; the name a
certificate would carry (`scanWindowLLVM_refines`) is left free for the theorem that
proves it.

The prose's ellipsis is one hypothesis short of the statement, and the shortfall
is load-bearing.  The body allocates six cells at the allocator base — `%k` (8
bytes), `%maskp` (4), `%stopp` (4) and the three lane mask words (4 each) — and
stores through them on every lane, so the band it owns is
`[base, base + scanBandBytes)`, and `scanBandDisjoint` states it clear of the
caller's three regions.  `bandOverlap_clobbers_window` lays the band's counter cell
across the window's second byte and reads the caller's window back as the counter's
bytes; `bandClear_preserves_window`, the same read with the band clear, reads it
back intact.

The frame's second boundary is the caller's state region, which the unit writes
and the caller reads back as a carry.  The slot's *bytes* are the rule's own and
not the encoding's: a lane that completes a UTF-8 requirement leaves the bounds it
last used (`[0x80, 0xBF]`) in the slot where `encodeState` writes zero, and the
entry slot may carry anything above the bits `decodeState` reads.
`completionLeavesBounds` measures the first on `[0xC2, 0x80]` — at a caller whose
slot *is* the encoding, so it is not an input-canonicality question — and shows the
readback `slotAt` agrees there; `scanWindowStatementPinningSlotBytes_false` refutes
the statement that pins the slot's bytes inside the frame.  The frame therefore
stops at the band and at the state region, which is the granularity
`JsonScanABI.scanFootprint` states: a difference anywhere in `%state` is the
unit's, and its caller-visible content is the readback clause.

The stop word is where the statement met the body rather than a proof step.  The
body reports one word per refusal reason its lane rule can raise — `%wcl` for a
closing lane, `%wct` for a control byte and `%wbd` for a `badUtf8` — and the select
chain that chose the `badUtf8` word tested `%lbad`, a bad *lead* byte.  A byte that
violates a pending requirement is a bad *continuation*, a different condition, so
`%wbd` was unreachable on that path: on `[0xE0, 0x80]` the model refuses at lane 1
with `badUtf8` (`0x382`) where the body answered `%wct`, `0x282`, `refuse lane 1
control`.  `scanWindowBody` now chooses `%wbd` on `%ubad ||| %lbad`, and
`scanWindowStatement_false` keeps the record: it refutes the statement about
`scanWindowBodyBeforeStopWordFix`, the body as it stood before that change, at that
witness.  `badContinuation_reason_agrees`, `badContinuation_rest_agrees` and
`probeWindows_agree` state the agreement the change produces — at the witness, and
on seven windows including a 32-byte one whose bad continuation sits at lane 31,
where both paths share the lane body.

What remains is the instruction-level step `scanWindowStatement` needs: the effect
of the `body` block's instruction list on the five memory cells it touches, the
loop induction over `valid ≤ 32`, and the theorem's footprint clause.  The prefix
lemmas above are the model-side half of that step and are proved here, so that the
outstanding half has a fixed statement to meet.  `JsonScanLane` now proves the
chain's head there: the 23 instructions before the rule on the full-window path
and the 8 on the scalar path, as `denoteCode` equations at the lane's own
environment.  What that leaves outstanding is `ruleInstrs`'s 120 instructions, the
arithmetic bridge from the four words they leave to `bodyStep`, the loop
induction over `valid ≤ 32` and the footprint clause.

Two properties of the body are measured rather than promised, and are what a
reviewer of the fixture can check independently: it contains no `phi`, no
`switch`, no vector `store`, no vector `alloca` and no intrinsic
(`probes/install/ir/capture-json-scan.sh`'s stop condition is the same detector
for the captured C), and `probes/install/ir/json-scan-body.ll` assembles and
compiles with the pinned `llvm-as`, `opt -passes=verify` and `clang`.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Memory
import LeanLLVM.Frames
import LeanLLVM.Refinement.JsonScanABI
import LeanLLVM.Refinement.JsonScanModel
import LeanLLVM.Refinement.JsonScanBody

namespace LeanLLVM.Refinement.JsonScanIR

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanABI
open LeanLLVM.Refinement.JsonScanModel
open LeanLLVM.Refinement.JsonScanBody (scanWindowBody scanWindowBaselineBody)

/-! ### The fixture

The committed rendering, and the pin that it is the AST's own text. -/

def scanWindowBodySrc : String := include_str "../../probes/install/ir/json-scan-body.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

#guard decide (firstFunction scanWindowBodySrc = some scanWindowBody)

/-! ### The mask prefix

The structural mask over the first `k` lanes, at the word level: the same fold
`maskOfList` runs, truncated.  It is a `BitVec 32` recursion rather than a `Nat`
fold so the per-lane step is the emitted `or` of a shifted one, and so no
magnitude side condition is carried through the loop.
-/

/-- The structural-or-space mask over the first `k` lanes.  Bit `j` is set
exactly when lane `j < k` holds a structural or whitespace byte. -/
def maskPref (bs : List UInt8) : Nat → BitVec 32
  | 0 => 0
  | k + 1 =>
      match bs[k]? with
      | some b =>
          if IsStructOrSpaceB b then maskPref bs k ||| ((1 : BitVec 32) <<< k)
          else maskPref bs k
      | none => maskPref bs k

/-- The lane the fold's list has at `k`, for `k` inside a window: the byte and
its own index.  `ScanWindow.lean`'s form of this is private, so it is restated
here; it is the fact that lets a prefix fold be split at its last lane. -/
theorem zipIdx_take_getElem? (bs : List UInt8) {k : Nat} (hk : k < 32) :
    (bs.zipIdx.take 32)[k]? = (bs[k]?).map (fun b => (b, k)) := by
  rw [List.getElem?_take, ite_eq_left hk, List.getElem?_zipIdx]
  simp

/-- Bit `k` of the emitted one, as a `BitVec 32` shifted by a lane index. -/
theorem ofNat_one_shiftLeft (k : Nat) (hk : k < 32) :
    BitVec.ofNat 32 (1 <<< k) = ((1 : BitVec 32) <<< k) := by
  have hlt : 1 <<< k < 2 ^ 32 := by
    rw [Nat.one_shiftLeft]
    -- `Nat.pow_lt_pow_right` carries `Classical.choice`; monotonicity to the
    -- lane's own bound and a decided constant step do not.
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : k ≤ 31))
      (by decide : 2 ^ 31 < 2 ^ 32)
  have hone : (1 : BitVec 32).toNat = 1 := by decide
  apply BitVec.eq_of_toNat_eq
  show (1 <<< k) % 2 ^ 32 = ((1 : BitVec 32) <<< k).toNat
  rw [Nat.mod_eq_of_lt hlt, BitVec.toNat_shiftLeft, hone, Nat.mod_eq_of_lt hlt]

/-- One lane of the prefix fold, as the recursion's own equation. -/
theorem maskPref_succ (bs : List UInt8) (k : Nat) :
    maskPref bs (k + 1) =
      (match bs[k]? with
       | some b =>
           if IsStructOrSpaceB b then maskPref bs k ||| ((1 : BitVec 32) <<< k)
           else maskPref bs k
       | none => maskPref bs k) := rfl

/-- The prefix's own fold: the lanes before `k` of the window list. -/
def laneFold (bs : List UInt8) (k : Nat) : Nat :=
  ((bs.zipIdx.take 32).take k).foldl
    (fun acc (p : UInt8 × Nat) => if IsStructOrSpaceB p.1 then acc ||| (1 <<< p.2) else acc) 0

/-- `maskPref` read at the `Nat` fold's own value, for a prefix inside a window. -/
theorem maskPref_eq_laneFold (bs : List UInt8) :
    ∀ k ≤ 32, maskPref bs k = BitVec.ofNat 32 (laneFold bs k) := by
  intro k
  induction k with
  | zero => intro _; simp [maskPref, laneFold]
  | succ n ih =>
      intro hn
      have hn32 : n < 32 := by omega
      rw [maskPref_succ]
      cases hb : bs[n]? with
      | none =>
          have hlist : (bs.zipIdx.take 32).take (n + 1) = (bs.zipIdx.take 32).take n := by
            rw [List.take_add_one, zipIdx_take_getElem? bs hn32, hb]
            simp
          simp only [hb]
          rw [ih (by omega)]
          simp only [laneFold, hlist]
      | some b =>
          have hpair : (bs.zipIdx.take 32)[n]? = some (b, n) := by
            rw [zipIdx_take_getElem? bs hn32, hb]
            rfl
          have hlist : (bs.zipIdx.take 32).take (n + 1) =
              (bs.zipIdx.take 32).take n ++ [(b, n)] := by
            rw [List.take_add_one, hpair]
            rfl
          simp only [hb]
          by_cases hs : IsStructOrSpaceB b = true
          · rw [if_pos hs, ih (by omega)]
            simp only [laneFold, hlist, List.foldl_append, List.foldl]
            rw [if_pos hs, BitVec.ofNat_or, ofNat_one_shiftLeft n hn32]
          · rw [if_neg hs, ih (by omega)]
            simp only [laneFold, hlist, List.foldl_append, List.foldl]
            rw [if_neg hs]

/-- **The mask clause of the theorem, at the model's own object.**  At the end of
a window the accumulator's word is `maskOfList`, whose own fold is this one. -/
theorem maskPref_eq_maskOfList (bs : List UInt8) (h : bs.length ≤ 32) :
    maskPref bs bs.length = maskOfList bs := by
  rw [maskPref_eq_laneFold bs bs.length h]
  have htake : (bs.zipIdx.take 32).take bs.length = bs.zipIdx.take 32 := by
    apply List.take_of_length_le
    rw [List.length_take, List.length_zipIdx]
    omega
  simp only [laneFold, htake, maskOfList]

/-! ### The stop prefix, and the carry it clamps

The body freezes at the first stop, so the slot holds the model's prefix carry
*clamped* at the first stop's lane.  `carriedAt` is that object; `firstStop` is
the stop the first `k` lanes raise.  `lastStop_eq_stopOf` at the end of the
window is what turns them into the model's own `carryAt` and `stopOf`.
-/

/-- The stop lane `k` raises, if the byte rule stops there. -/
def laneStop (bs : List UInt8) (st : BodyState) (k : Nat) : Option Stop :=
  match bs[k]? with
  | none => none
  | some b =>
      match bodyStep (carryAt bs st k) b with
      | .cont _ => none
      | .closed => some (.close k)
      | .refused s => some (.refuse k s)

/-- The first stop among the first `k` lanes, which is what the emitted body's
stop word holds after `k` lanes. -/
def firstStop (bs : List UInt8) (st : BodyState) : Nat → Option Stop
  | 0 => none
  | k + 1 =>
      match firstStop bs st k with
      | some s => some s
      | none => laneStop bs st k

/-- The carry the slot holds after `k` lanes: the model's prefix carry, clamped
at the first stop's lane — the state the fold held when the scan stopped. -/
def carriedAt (bs : List UInt8) (st : BodyState) (k : Nat) : BodyState :=
  match firstStop bs st k with
  | some (.close j) => carryAt bs st j
  | some (.refuse j _) => carryAt bs st j
  | none => carryAt bs st k

/-- One lane of the stop prefix, as the recursion's own equation. -/
theorem firstStop_succ (bs : List UInt8) (st : BodyState) (k : Nat) :
    firstStop bs st (k + 1) =
      (match firstStop bs st k with
       | some s => some s
       | none => laneStop bs st k) := rfl

/-- While every lane before `n` continues, no stop is recorded. -/
theorem firstStop_eq_none {bs : List UInt8} {st : BodyState} :
    ∀ {k : Nat}, (∀ j, j < k → ∀ (b : UInt8), bs[j]? = some b →
        ∃ st', bodyStep (carryAt bs st j) b = .cont st') → firstStop bs st k = none
  | 0, _ => rfl
  | k + 1, h => by
      have hpre : firstStop bs st k = none :=
        firstStop_eq_none (k := k) (fun j hj b hb => h j (by omega) b hb)
      have hlane : laneStop bs st k = none := by
        unfold laneStop
        cases hb : bs[k]? with
        | none => rfl
        | some b =>
            obtain ⟨st', hstep⟩ := h k (by omega) b hb
            simp only [hb, hstep]
      rw [firstStop_succ, hpre]
      exact hlane

/-- The first stop is at the lane that raises it, and stays there. -/
theorem firstStop_eq_some {bs : List UInt8} {st : BodyState} {k : Nat}
    (hcont : ∀ j, j < k → ∀ (b : UInt8), bs[j]? = some b →
      ∃ st', bodyStep (carryAt bs st j) b = .cont st')
    {stop : Stop} (hlane : laneStop bs st k = some stop) :
    ∀ {n : Nat}, k < n → firstStop bs st n = some stop
  | 0, hn => absurd hn (by omega)
  | n + 1, hn => by
      rcases Nat.lt_or_ge k n with h | h
      · have := firstStop_eq_some hcont hlane (n := n) h
        rw [firstStop_succ, this]
      · have hkn : k = n := by omega
        subst hkn
        rw [firstStop_succ, firstStop_eq_none (k := k) hcont]
        exact hlane

/-- **The stop word's value at the end of the window**, at the model's own
object: the first stop among the window's own lanes. -/
theorem firstStop_eq_stopOf {bs : List UInt8} {st : BodyState} (hlen : bs.length ≤ 32) :
    firstStop bs st bs.length = stopOf bs st := by
  have hspec := windowOf_stop_spec (bs := bs) (st := st)
  cases hstop : (windowOf bs st).stop with
  | none =>
      simp only [stopOf, hstop]
      rw [hstop] at hspec
      exact firstStop_eq_none (fun j hj (b : UInt8) hb => hspec j (by omega) hb)
  | some stop =>
      simp only [stopOf, hstop]
      rw [hstop] at hspec
      cases stop with
      | close j =>
          obtain ⟨-, ⟨b0, hb0⟩, hcb, hstep⟩ := hspec
          have hjlen : j < bs.length := (List.getElem?_eq_some_iff.mp hb0).1
          have hlane : laneStop bs st j = some (.close j) := by
            unfold laneStop
            simp only [hb0, hstep (b := b0) hb0]
          exact firstStop_eq_some (k := j) (fun i hi (b : UInt8) hbi => hcb i hi hbi) hlane
            (n := bs.length) (by omega)
      | refuse j s =>
          obtain ⟨-, ⟨b0, hb0⟩, hcb, hstep⟩ := hspec
          have hjlen : j < bs.length := (List.getElem?_eq_some_iff.mp hb0).1
          have hlane : laneStop bs st j = some (.refuse j s) := by
            unfold laneStop
            simp only [hb0, hstep (b := b0) hb0]
          exact firstStop_eq_some (k := j) (fun i hi (b : UInt8) hbi => hcb i hi hbi) hlane
            (n := bs.length) (by omega)

/-- A lane that continues leaves the clamp alone and advances the prefix carry. -/
theorem carriedAt_succ_cont {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    {st' : BodyState} (hstop : firstStop bs st k = none) (hb : bs[k]? = some b)
    (hstep : bodyStep (carryAt bs st k) b = .cont st') :
    carriedAt bs st (k + 1) = st' := by
  have hnext : firstStop bs st (k + 1) = none := by
    rw [firstStop_succ, hstop]
    unfold laneStop
    simp only [hb, hstep]
  have hpre : carryAt bs st (k + 1) = st' := by
    simp only [carryAt_succ, hb, hstep]
  unfold carriedAt
  rw [hnext, hpre]

/-- A lane that stops leaves the clamp where it was: the body's freeze is the
model's prefix carry at the stop's lane. -/
theorem carriedAt_succ_stop {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    (hstop : firstStop bs st k = none) (hb : bs[k]? = some b)
    (hne : ∀ st', bodyStep (carryAt bs st k) b ≠ .cont st') :
    carriedAt bs st (k + 1) = carriedAt bs st k := by
  have hclamp : carriedAt bs st k = carryAt bs st k := by
    unfold carriedAt
    rw [hstop]
  rw [hclamp]
  unfold carriedAt
  rw [firstStop_succ, hstop]
  unfold laneStop
  simp only [hb]
  cases hb' : bodyStep (carryAt bs st k) b with
  | cont st' => exact absurd hb' (hne st')
  | closed => rfl
  | refused s => rfl

/-- **The carry clause of the theorem, at the model's own object.**  At the end of
the window the slot holds the prefix carry at the stop's lane, or the window's
length when nothing stopped — `JsonScanModel`'s `stopLaneOrLength`. -/
theorem carriedAt_eq_carryAt {bs : List UInt8} {st : BodyState} (hlen : bs.length ≤ 32) :
    carriedAt bs st bs.length = carryAt bs st (stopLaneOrLength bs st) := by
  unfold carriedAt
  rw [firstStop_eq_stopOf hlen]
  unfold stopLaneOrLength stopLane
  cases h : stopOf bs st with
  | none => rfl
  | some s => cases s <;> rfl

/-! ### The refinement statement

`JsonScanLane`'s header writes the statement as prose, and this section is that
prose as one object, so that a pin, a certificate and a reader all name the same
proposition: the body returns the model's status word, writes the model's mask at
`%out`, leaves the model's carry in the slot, changes no byte outside its own
allocation band and the caller's state region, and leaves the window it read
unchanged.  It is a proposition and not a theorem; the name a certificate would
carry (`scanWindowLLVM_refines`) is left free for the theorem that proves it.

The prose's hypothesis list ends with `(hband : … base disjoint …)`, an ellipsis
where a hypothesis belongs, and the shortfall is not decoration.  The body
allocates six cells at the allocator base — `%k` (8 bytes), `%maskp` (4), `%stopp`
(4) and the three lane mask words (4 each) — and stores through them on every
lane, so the band it owns is `[base, base + scanBandBytes)`, and
`scanBandDisjoint` states it clear of the caller's three regions.
`bandOverlap_clobbers_window` lays the band's counter cell across the window's
second byte and reads the caller's window back as the counter's bytes, while
`bandClear_preserves_window` — the same read, same detector, band clear of the
window — reads it back intact.

The frame's other boundary is the caller's state region.  The body stores the
rule's four words there on every lane, and a lane that completes a UTF-8
requirement leaves the bounds it last used in the slot's bounds words where
`encodeState` writes zero; the entry slot's upper bits likewise come back out
unchanged.  `completionLeavesBounds` measures the bounds on `[0xC2, 0x80]` at a
caller whose slot holds the encoding, and the readback `slotAt` is the model's
carry there, so the difference is the frame's rather than the readback's.
`scanWindowStatementPinningSlotBytes_false` refutes the statement that pins the
slot's bytes inside the frame; the frame here stops at the band and at the state
region, which is `JsonScanABI.scanFootprint`'s granularity, and the state region's
caller-visible content is the readback clause.

The stop word is where the statement met the body rather than a proof step.  The
body reports one word per refusal reason its lane rule can raise — `%wcl` for a
closing lane, `%wct` for a control byte and `%wbd` for a `badUtf8` — and the
select chain that chose the `badUtf8` word tested `%lbad`, a bad *lead* byte.  A
byte that violates a pending requirement is a bad *continuation*, a different
condition, so `%wbd` was unreachable on that path: on `[0xE0, 0x80]` the model
refuses at lane 1 with `badUtf8` (`0x382`) where the body answered `%wct`,
`0x282`, `refuse lane 1 control`.

`scanWindowBody` now chooses `%wbd` on `%ubad ||| %lbad`, and
`scanWindowStatement_false` keeps the record: it refutes the statement about
`scanWindowBodyBeforeStopWordFix`, the body as it stood before that change, at
that witness.  `badContinuation_reason_agrees`, `badContinuation_rest_agrees` and
`probeWindows_agree` state the agreement the change produces — at the witness, and
on seven windows including a 32-byte one whose bad continuation sits at lane 31,
where both paths share the lane body.

What remains is the instruction-level step `scanWindowStatement` needs: the effect
of the `body` block's instruction list on the five memory cells it touches, the
loop induction over `valid ≤ 32`, and the theorem's footprint clause.  The prefix
lemmas above are the model-side half of that step and are proved here, so that the
outstanding half has a fixed statement to meet.  `JsonScanLane` now proves the
chain's head there: the 23 instructions before the rule on the full-window path
and the 8 on the scalar path, as `denoteCode` equations at the lane's own
environment.  What that leaves outstanding is `ruleInstrs`'s 120 instructions, the
arithmetic bridge from the four words they leave to `bodyStep`, the loop
induction over `valid ≤ 32` and the footprint clause.
-/

/-- The bytes the body's own allocations occupy, from the allocator base: `%k`
(8), `%maskp` (4), `%stopp` (4) and the three lane-mask words (4 each). -/
def scanBandBytes : Nat := 28

/-- The band the body allocates, disjoint from the caller's three regions: the
hypothesis the prose leaves as `(hband : … base disjoint …)`. -/
def scanBandDisjoint (base pIn pOut pState valid : Nat) : Prop :=
  (base + scanBandBytes ≤ pIn ∨ pIn + valid ≤ base) ∧
  (base + scanBandBytes ≤ pOut ∨ pOut + outBytes ≤ base) ∧
  (base + scanBandBytes ≤ pState ∨ pState + stateBytes ≤ base)

/-- **The refinement statement about a body**, with the prose's elided band
hypothesis supplied, the frame tied to `scanBandBytes`, and the state region left
to the unit at the ABI's granularity.

The frame stops at the band and at the caller's state region, and the state
region's caller-visible content is the readback clause `slotAt`.  It is not byte
equality with the encoding: the body writes the rule's own four words into the
slot on every lane, so a lane that completes a UTF-8 requirement leaves the bounds
it last used in the slot where `encodeState` writes zero.
`completionLeavesBounds` measures that at a caller whose slot holds the encoding,
and `scanWindowStatementPinningSlotBytes_false` refutes the statement that pins
those bytes inside the frame.  `JsonScanABI.scanFootprint` allows the same
difference anywhere in `%state`, which is the granularity this clause keeps. -/
def scanWindowStatementOf (f : Function) : Prop :=
  ∀ (bs : List UInt8) (st : BodyState) (mem : Mem)
    (pIn pOut pState base valid : Nat),
    valid ≤ 32 →
    bs.length = valid →
    readBytes mem pIn valid = some bs →
    slotAt mem pState = some st →
    st.WellFormed →
    scanSlotDisjoint pIn pOut pState valid →
    scanBandDisjoint base pIn pOut pState valid →
    ∃ mem', runFuel noCalls 10000 f
        { (initState f [.ptr pIn, .ptr pOut, .ptr pState,
                        .int 32 (BitVec.ofNat 32 valid)]) with
          mem := mem, next := base } =
        some (.ret (some (.int 32 (encodeStatus (Status.ok (stopOf bs st))))) mem') ∧
      readWord mem' pOut = some (maskOfList bs) ∧
      slotAt mem' pState = some (carryAt bs st (stopLaneOrLength bs st)) ∧
      AgreesOutsideMem mem' (writeMask mem pOut (maskOfList bs))
        (fun a => Band base (base + scanBandBytes) a ∨
          (pState ≤ a ∧ a < pState + stateBytes)) ∧
      readBytes mem' pIn valid = some bs

/-- **The refinement statement about the emitted body**: the proposition the
scanner's certificate would name, and the one `scanWindowLLVM_refines` is to
prove. -/
def scanWindowStatement : Prop := scanWindowStatementOf scanWindowBody

/-! #### The statement before the frame left the state region to the unit

The frame clause cannot pin the slot's bytes.  The body stores the rule's four
words and not the encoding's: on a lane that completes a UTF-8 requirement it
leaves the bounds it last used (`[0x80, 0xBF]`) where `encodeState` writes zero,
and the entry slot it read may carry anything above the bits `decodeState` reads.
`completionLeavesBounds` measures the first at a caller whose slot *is* the
encoding, so the disagreement is not an input-canonicality question; the readback
`slotAt` is the model's carry in both cases.  The definition below is the statement
as it stood with the slot's bytes inside the frame, and
`scanWindowStatementPinningSlotBytes_false` refutes it about the emitted body.
-/

/-- The statement as it stood before the frame left the state region to the unit:
byte equality with the model's canonical slot write, outside the band.  It is the
pre-correction shape, the subject of `scanWindowStatementPinningSlotBytes_false`
and of nothing else: no certificate names it. -/
def scanWindowStatementOfPinningSlotBytes (f : Function) : Prop :=
  ∀ (bs : List UInt8) (st : BodyState) (mem : Mem)
    (pIn pOut pState base valid : Nat),
    valid ≤ 32 →
    bs.length = valid →
    readBytes mem pIn valid = some bs →
    slotAt mem pState = some st →
    st.WellFormed →
    scanSlotDisjoint pIn pOut pState valid →
    scanBandDisjoint base pIn pOut pState valid →
    ∃ mem', runFuel noCalls 10000 f
        { (initState f [.ptr pIn, .ptr pOut, .ptr pState,
                        .int 32 (BitVec.ofNat 32 valid)]) with
          mem := mem, next := base } =
        some (.ret (some (.int 32 (encodeStatus (Status.ok (stopOf bs st))))) mem') ∧
      readWord mem' pOut = some (maskOfList bs) ∧
      slotAt mem' pState = some (carryAt bs st (stopLaneOrLength bs st)) ∧
      AgreesOutsideMem mem' (writeSlot (writeMask mem pOut (maskOfList bs)) pState
          (encodeState (carryAt bs st (stopLaneOrLength bs st))))
        (Band base (base + scanBandBytes)) ∧
      readBytes mem' pIn valid = some bs

/-! #### The body's stop word before it tested `%ubad`

The defect `scanWindowStatement_false` records belongs to the text the body
carried before its select chain tested `%ubad`, so the record is a theorem about
that text rather than a claim about the current one.  The text is derived from the
current `body` block by the inverse of the change — `%bad8` dropped, `%sw0` back
on `%lbad` — so the two cannot drift apart silently: if the current chain stops
matching the pattern, the record theorem stops proving rather than describing a
body that no longer exists.
-/

/-- One block's instructions with the stop word's chain as it stood before it
tested `%ubad`: no `%bad8`, and `%sw0` on `%lbad` alone. -/
def stopWordChainBeforeUBad (instrs : List Instr) : List Instr :=
  instrs.flatMap fun i =>
    match i with
    | .binop "%bad8" _ _ _ _ => []
    | .select "%sw0" ty _ wbd wct => [.select "%sw0" ty (.reg "%lbad") wbd wct]
    | i => [i]

/-- The body with that chain: `scanWindowBody`'s blocks with its `body` block
rewritten.  It is the pre-fix text, the subject of `scanWindowStatement_false` and
of nothing else: it is not emitted, not parsed, not certified, and no manifest or
certificate names it. -/
def scanWindowBodyBeforeStopWordFix : Function :=
  { scanWindowBody with
    blocks := scanWindowBody.blocks.map fun b =>
      if b.name = "body" then { b with instrs := stopWordChainBeforeUBad b.instrs }
      else b }

-- The substitution is the change the record describes: it bites on the current
-- text, and it removes exactly one instruction.
#guard (stopWordChainBeforeUBad JsonScanBody.ruleInstrs) ≠ JsonScanBody.ruleInstrs
#guard (stopWordChainBeforeUBad JsonScanBody.ruleInstrs).length + 1 =
  JsonScanBody.ruleInstrs.length

/-! #### The witness harness

A run over a caller's memory laid out the way the unit's ABI describes it: the
window at 100, the carry slot at 200 holding `st`'s encoding, and the mask's word
at 300.  Nothing is present inside the band, which is what a fresh allocation
finds, so the only bytes a run writes outside the band are the ones the unit
owns.
-/

/-- The carry's encoding as the slot's 16 bytes at `p`: `flags`, `count`, `lo`
and `hi`, each little-endian. -/
def slotBytes (p : Nat) (st : BodyState) : Mem :=
  let s := encodeState st
  (natToBytes s.flags.toNat 4 ++ natToBytes s.count.toNat 4 ++
    natToBytes s.lo.toNat 4 ++ natToBytes s.hi.toNat 4).zipIdx.map
    fun q => (p + q.2, q.1)

/-- The caller's memory a witness run starts from. -/
def witnessMem (bs : List UInt8) (st : BodyState) : Mem :=
  bs.zipIdx.map (fun p => (100 + p.2, p.1)) ++ slotBytes 200 st ++
    (List.range 4).map (fun i => (300 + i, 0))

/-- The state a witness run of `f` starts in: the caller's memory, the window's
length as the request's `%valid`, and the allocator base the request names. -/
def witnessStart (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    State :=
  { (initState f [.ptr 100, .ptr 300, .ptr 200,
      .int 32 (BitVec.ofNat 32 valid)]) with
    mem := witnessMem bs st, next := base }

/-- The value a completed run of `f` returns; `none` when it is undefined or runs
out of fuel. -/
def runValue (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    Option Value :=
  (runFuel noCalls 10000 f (witnessStart f bs st base valid)).bind fun
    | .ret v _ => v
    | .ub => none

/-- The status word a completed run of `f` returns. -/
def runWord (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    Option (BitVec 32) :=
  (runValue f bs st base valid).bind fun
    | .int 32 w => some w
    | _ => none

/-- The window a completed run of `f` leaves at the caller's address. -/
def runWindow (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    Option (List UInt8) :=
  (runFuel noCalls 10000 f (witnessStart f bs st base valid)).bind fun
    | .ret _ m => readBytes m 100 valid
    | .ub => none

/-- The memory a completed run of `f` leaves; the empty memory when it is
undefined or runs out of fuel. -/
def runMem (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    Mem :=
  ((runFuel noCalls 10000 f (witnessStart f bs st base valid)).bind fun
    | .ret _ m => some m
    | .ub => none).getD []

/-- What a run leaves, as the statement's four clauses. -/
structure Summary where
  /-- The value the unit returns. -/
  value : Option Value
  /-- The mask's word, read at the caller's `%out`. -/
  mask : Option (BitVec 32)
  /-- The carry, read as the caller's slot. -/
  carry : Option BodyState
  /-- The window, read at the caller's `%in`. -/
  window : Option (List UInt8)
deriving DecidableEq, Repr

/-- What a completed run of `f` leaves, as those four clauses. -/
def runSummary (f : Function) (bs : List UInt8) (st : BodyState) (base valid : Nat) :
    Option Summary :=
  (runFuel noCalls 10000 f (witnessStart f bs st base valid)).bind fun
    | .ret v m => some ⟨v, readWord m 300, slotAt m 200, readBytes m 100 valid⟩
    | .ub => none

/-- What the model says those four clauses are for `bs` and `st`. -/
def modelSummary (bs : List UInt8) (st : BodyState) : Summary :=
  ⟨some (.int 32 (encodeStatus (Status.ok (stopOf bs st)))),
    some (maskOfList bs),
    some (carryAt bs st (stopLaneOrLength bs st)),
    some bs⟩

/-! #### The witnesses

The runs below reduce the body through the semantics, which is deeper than the
default recursion limit, so the block raises it once.
-/

set_option maxRecDepth 100000 in
section

/-- **The prose's elided hypothesis is load-bearing.**  With the band's counter
cell laid across the window's second byte, the run's own stores replace the
caller's bytes, so the conclusion's `readBytes mem' pIn valid = some bs` clause is
false. -/
theorem bandOverlap_clobbers_window :
    runWindow scanWindowBody [0x61, 0x61] BodyState.body 99 2 = some [0, 0] := by
  decide

/-- The control for `bandOverlap_clobbers_window`: the same read, with the band
clear of the caller's regions, returns the window.  Only the band's placement
changed. -/
theorem bandClear_preserves_window :
    runWindow scanWindowBody [0x61, 0x61] BodyState.body 64 2 = some [0x61, 0x61] := by
  decide

/-- **The record: the stop word's select chain, before it tested `%ubad`, carries
the wrong refusal reason.**  On `[0xE0, 0x80]` the model refuses at lane 1 with
`badUtf8` — the requirement `0xE0` leaves is `[0xA0, 0xBF]` and `0x80` is outside
it — while the pre-fix body returns the control word.  Both words name lane 1 and
kind `refuse`; the two-bit reason field is `control` where the model says
`badUtf8`.  The body change that answers this — `%sw0` testing `%ubad ||| %lbad`
instead of `%lbad` — is what makes the body in `scanWindowBody` agree, and what
makes this theorem false of that body. -/
theorem badContinuation_reason_differs :
    runValue scanWindowBodyBeforeStopWordFix [0xE0, 0x80] BodyState.body 64 2 =
        some (.int 32 0x282) ∧
      (0x282 : BitVec 32) ≠
        encodeStatus (Status.ok (stopOf [0xE0, 0x80] BodyState.body)) := by
  refine ⟨by decide, by decide⟩

/-- **The emitted body reports the model's refusal at the same witness.**  On
`[0xE0, 0x80]` it returns `0x382`, `refuse lane 1 badUtf8`, where the pre-fix
chain returned `0x282`. -/
theorem badContinuation_reason_agrees :
    runValue scanWindowBody [0xE0, 0x80] BodyState.body 64 2 =
      some (.int 32 (encodeStatus (Status.ok (stopOf [0xE0, 0x80] BodyState.body)))) := by
  decide

/-- The control for the two theorems above: on a window whose refusal is a bad
*lead* byte the words agree in both bodies, so the disagreement recorded above is
the select chain and not the comparison. -/
theorem badLead_reason_agrees :
    runValue scanWindowBody [0xC0] BodyState.body 64 1 =
      some (.int 32 (encodeStatus (Status.ok (stopOf [0xC0] BodyState.body)))) := by
  decide

/-- At the corrected witness all four clauses agree: the status word, the mask the
run writes at `%out`, the carry it leaves in the slot and the window the caller
reads back. -/
theorem badContinuation_rest_agrees :
    runSummary scanWindowBody [0xE0, 0x80] BodyState.body 64 2 =
      some (modelSummary [0xE0, 0x80] BodyState.body) := by
  decide

/-- **The windows the stop word's chain is measured on**: a bad continuation
under a three-byte lead and under a two-byte lead, a bad lead byte, a control
byte, a closing quote, a full window with no stop, and a 32-byte window whose bad
continuation sits at lane 31. -/
def probeWindows : List (List UInt8) :=
  [[0xE0, 0x80], [0xC2, 0x41], [0xC0], [0x61, 0x01], [0x61, 0x22],
   List.replicate 32 0x61, List.replicate 30 0x61 ++ [0xE0, 0x80]]

set_option maxHeartbeats 8000000 in
/-- **Every probe window agrees with the model on all four clauses.**  The two
32-byte windows take the vector-mask path and the rest the scalar one; the two
paths share the lane body, so the correction reaches lane 31 with nothing else
changed. -/
theorem probeWindows_agree :
    probeWindows.map (fun bs =>
        runSummary scanWindowBody bs BodyState.body 64 bs.length) =
      probeWindows.map (fun bs => some (modelSummary bs BodyState.body)) := by
  decide

/-- Two byte reads agree: both absent, or both present with the same value.  The
comparison is on the bytes' `Nat` values, which keeps the checker's axiom
footprint the constructive one the pins below record. -/
def sameByte : Option UInt8 → Option UInt8 → Bool
  | none, none => true
  | some x, some y => x.toNat == y.toNat
  | _, _ => false

/-- Whether two memories agree at every address either of them mentions, outside
the band and the state region: the frame clause of `scanWindowStatementOf` as a
computation.  The band and the state region are the unit's; everywhere else the
run's memory must be the model's mask write, byte for byte.  Addresses either
memory mentions are checked as they come — a repeated address is checked twice and
answers the same way — so no deduplication is needed. -/
def frameAgrees (m m' : Mem) (base pState : Nat) : Bool :=
  (m.map (fun p => p.1) ++ m'.map (fun p => p.1)).all fun a =>
    (base ≤ a && a < base + scanBandBytes) ||
      (pState ≤ a && a < pState + stateBytes) ||
      sameByte (readByte m a) (readByte m' a)

set_option maxHeartbeats 16000000 in
/-- **Every probe window meets the frame clause too.**  Outside the band and the
state region the run's memory is the model's mask write at `%out`; the state
region's content is the readback `probeWindows_agree` compares, and the band is the
unit's own.  This is the clause the pinned-slot statement got wrong, checked on the
same seven windows rather than read off one. -/
theorem probeWindows_frame :
    probeWindows.all (fun bs =>
        frameAgrees (runMem scanWindowBody bs BodyState.body 64 bs.length)
          (writeMask (witnessMem bs BodyState.body) 300 (maskOfList bs)) 64 200) = true := by
  decide

/-- **The statement was false of the body before the stop word's chain tested
`%ubad`.**  Every hypothesis of `scanWindowStatementOf scanWindowBodyBeforeStopWordFix`
holds at the bad-continuation witness — the window is readable, the slot holds a
well-formed carry, the three regions are disjoint and the band is clear of them —
and the conclusion demands the model's `badUtf8` word where that body returns the
control word.  It is the record of the defect the chain carried, and it is the
value clause it refutes: the frame's own clause is refuted separately, about the
emitted body, by `scanWindowStatementPinningSlotBytes_false`. -/
theorem scanWindowStatement_false :
    ¬ scanWindowStatementOf scanWindowBodyBeforeStopWordFix := by
  intro h
  have hconcl :=
    h [0xE0, 0x80] BodyState.body (witnessMem [0xE0, 0x80] BodyState.body)
      100 300 200 64 2 (by decide) (by decide) (by decide) (by decide)
      (by simp [BodyState.WellFormed, BodyState.body, Utf8Need.WellFormed])
      (by unfold scanSlotDisjoint outBytes stateBytes; decide)
      (by unfold scanBandDisjoint scanBandBytes outBytes stateBytes; decide)
  obtain ⟨mem', hrun, -⟩ := hconcl
  have hvalue := badContinuation_reason_differs.1
  rw [runValue, witnessStart, hrun] at hvalue
  simp only [Option.bind, Option.some.injEq, Value.int.injEq] at hvalue
  exact badContinuation_reason_differs.2 ((eq_of_heq hvalue.2).symm)

/-- **The slot the run leaves after a requirement completes.**  On `[0xC2, 0x80]`
the caller's slot holds the encoding of the entry carry; lane 0 leaves the
requirement `more 1 [0x80, 0xBF]` and lane 1 completes it.  The run leaves the
bounds it last used in the slot's two bounds words — `0x80` and `0xBF` — where the
encoding writes zero for a completed requirement.  The readback is the model's
carry in both cases, because `slotAt` ignores the bounds when the count is zero,
so the disagreement is the frame's and not the readback's, and it survives every
hypothesis of the statement including the slot holding the encoding. -/
theorem completionLeavesBounds :
    readBytes (runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2) 200 16 =
        some [1, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 191, 0, 0, 0] ∧
      slotAt (runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2) 200 =
        some (carryAt [0xC2, 0x80] BodyState.body
          (stopLaneOrLength [0xC2, 0x80] BodyState.body)) ∧
      readBytes (writeSlot (writeMask (witnessMem [0xC2, 0x80] BodyState.body) 300
            (maskOfList [0xC2, 0x80])) 200
          (encodeState (carryAt [0xC2, 0x80] BodyState.body
            (stopLaneOrLength [0xC2, 0x80] BodyState.body)))) 200 16 =
        some [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The frame cannot pin the slot's bytes.**  Every hypothesis of
`scanWindowStatementOfPinningSlotBytes scanWindowBody` holds at the completion
witness — the window is readable, the slot holds a well-formed carry *and* its
encoding, the three regions are disjoint and the band is clear of them — and the
conclusion demands the slot's bytes be `encodeState`'s outside the band, where the
run's are the rule's own (`completionLeavesBounds`, first and third clauses).  The
statement is therefore refuted rather than unproved.  It is the record of the shape
the frame had; `scanWindowStatementOf` leaves the state region to the unit and pins
its caller-visible content by `slotAt`. -/
theorem scanWindowStatementPinningSlotBytes_false :
    ¬ scanWindowStatementOfPinningSlotBytes scanWindowBody := by
  intro h
  have hconcl :=
    h [0xC2, 0x80] BodyState.body (witnessMem [0xC2, 0x80] BodyState.body)
      100 300 200 64 2 (by decide) (by decide) (by decide) (by decide)
      (by simp [BodyState.WellFormed, BodyState.body, Utf8Need.WellFormed])
      (by unfold scanSlotDisjoint outBytes stateBytes; decide)
      (by unfold scanBandDisjoint scanBandBytes outBytes stateBytes; decide)
  obtain ⟨mem', hrun, -, -, hframe, -⟩ := hconcl
  have hrun0 : runFuel noCalls 10000 scanWindowBody
      (witnessStart scanWindowBody [0xC2, 0x80] BodyState.body 64 2) =
      some (.ret (some (.int 32
        (encodeStatus (Status.ok (stopOf [0xC2, 0x80] BodyState.body)))))
        (runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2)) := by
    decide
  have hsame : some (Outcome.ret (some (.int 32
        (encodeStatus (Status.ok (stopOf [0xC2, 0x80] BodyState.body))))) mem') =
      some (Outcome.ret (some (.int 32
        (encodeStatus (Status.ok (stopOf [0xC2, 0x80] BodyState.body)))))
        (runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2)) :=
    hrun.symm.trans hrun0
  have hmem : mem' = runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2 := by
    have h3 := Option.some.inj hsame
    have hm := congrArg (fun o : Outcome => match o with
      | .ret _ m => m
      | .ub => ([] : Mem)) h3
    simpa using hm
  have hframeAt := hframe 208 (by unfold Band scanBandBytes; decide)
  rw [hmem] at hframeAt
  have hl : readByte (runMem scanWindowBody [0xC2, 0x80] BodyState.body 64 2) 208 =
      some 128 := by decide
  have hr : readByte (writeSlot (writeMask (witnessMem [0xC2, 0x80] BodyState.body) 300
      (maskOfList [0xC2, 0x80])) 200
      (encodeState (carryAt [0xC2, 0x80] BodyState.body
        (stopLaneOrLength [0xC2, 0x80] BodyState.body)))) 208 = some 0 := by decide
  rw [hl, hr] at hframeAt
  exact absurd hframeAt (by decide)

end

end LeanLLVM.Refinement.JsonScanIR
