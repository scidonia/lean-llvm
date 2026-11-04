/-
The JSON window scanner, at the LLVM level.

`probes/install/ir/json-scan-body.ll` is the rendering of the AST in
`LeanLLVM/Vellum/JsonScanBody.lean`, emitted by `lake exe
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

**What is not here.**  The refinement theorem itself — that
`runFuel noCalls 10000 scanWindowBody` returns the model's status word, writes
the model's mask and leaves the model's carry in the slot, changing no other
byte outside the band its own allocations cover — together with its instantiation
at `scanWindowBaselineBody` and the negative control, is **not yet proved**, and
nothing in this repository certifies the body until it is.  What remains is the
lane-level step the plan calls P4's instruction-level obligation: the effect of
the `body` block's instruction list on the five memory cells it touches, the loop
induction over `valid ≤ 32`, and the theorem's footprint clause.  The prefix
lemmas above are the model-side half of that step, and they are proved here so
that the outstanding half has a fixed statement to meet.

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
import LeanLLVM.Vellum.JsonScanABI
import LeanLLVM.Vellum.JsonScanModel
import LeanLLVM.Vellum.JsonScanBody

namespace LeanLLVM.Vellum.JsonScanIR

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonScanABI
open LeanLLVM.Vellum.JsonScanModel
open LeanLLVM.Vellum.JsonScanBody (scanWindowBody scanWindowBaselineBody)

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
