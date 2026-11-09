/-
The bit intrinsics of the JSON kernels, in lane vocabulary.

`tests/v16/ci2.ll`, the stage-1 index kernel, forms its masks with three
intrinsics: `llvm.x86.bmi.pext.64` twice, `llvm.x86.bmi.pdep.64` and
`llvm.ctlz.i64`.  The entry kernels add three more — `llvm.ctpop.i32`,
`llvm.ctpop.i64` and `llvm.cttz.i64` — the UTF-8 stage adds two,
`llvm.usub.sat.v32i8` and `llvm.x86.avx.ptestz.256`, and the escape unit adds
three, `llvm.umin.i32`, `llvm.x86.sse2.pmadd.wd` and
`llvm.x86.ssse3.pmadd.ub.sw.128`, so eleven spellings have a modelled reading
here, as ten lane definitions (the two `ctpop` widths share one) and no semantics
case.  They are modelled as calls — the parser checks the shape of the spellings
it has a rule for, and an environment supplies every meaning, so the semantics
needs no special case — and this module is that meaning: `pext`, `pdep` and
`ctlz` lane by lane, which `s1Calls` (`LeanLLVM/Vellum/JsonS1MasksIR.lean`)
binds for the extracted mask unit; `ctpop`/`cttz`, which `entryCalls`
(`LeanLLVM/Vellum/JsonEntryIR.lean`) binds for the entry kernels; `subsSat`/
`ptestz`, which `utf8Calls` (`LeanLLVM/Vellum/JsonUtf8IR.lean`) binds for the
UTF-8 stage; and `umin`/`pmaddUbSw`/`pmaddWd`, which `escapeCalls`
(`LeanLLVM/Vellum/JsonEscapeIntrinsics.lean`) binds for the escape unit.
`Pclmul` gives the fourth (`llvm.x86.pclmulqdq`) its algebra.

A word is read lane by lane with `BitVec.getLsbD`, and `ofLanes` packs a lane
function back into a word, so every definition below is a statement about lanes
rather than about a bit-twiddling sequence:

* `pext a m` gathers: lane `j` of the result is `a`'s lane at the `j`-th set
  lane of `m`, and clear at or past `m`'s population count.
* `pdep a m` scatters: lane `i` is `a`'s lane at `i`'s **rank** among `m`'s set
  lanes, and clear where `m` is clear.
* `ctlz x` is the number of clear lanes above `x`'s highest set lane — `w` for
  the zero word — and `trailingRun m` is the length of `m`'s maximal suffix of
  set lanes; `ctlz_not_eq_trailingRun` is `ctlz (~~~m) = trailingRun m`.
* `ctpop x` is the number of set lanes, and `cttz x` is the least set lane —
  `w` at the zero word.
* `subsSat a b` subtracts one byte lane from another and saturates at zero, so
  it is `a - b` when the subtrahend fits and `0` when it does not; the UTF-8
  stage's `usub.sat.v32i8` applies it byte by byte.
* `ptestz a b` is the 256-bit zero test: `1` when no lane is set in both
  operands, `0` otherwise.
* `umin a b` is the unsigned minimum of two words; `pmaddWd x y` is the signed
  word multiply-add — adjacent word lanes of each operand multiplied pairwise,
  the two products summed at `i32` and wrapping; and `pmaddUbSw x y` is the
  unsigned-by-signed byte multiply-add, its pair sums saturated to a signed word.
  The last two read an operand as adjacent lane pairs (`pairsOf`), which is the
  granularity both instructions read.

**The poison flag, stated once.** `cttz` has an `i1` flag in LLVM.  At `false`
the zero word yields `w`, which is exact.  At `true` LLVM makes the zero operand
poison, and this model has no poison: it returns the determined `w` where LLVM
allows anything.  That is admissible because no clause of the claims that read
`cttz` reads where those values land — they reach only lanes past the emitted
count, outside the written region the frame clause confines and the read region
the words clause reads — and it is why `cttz`'s `i1 true` is the one poison-carrying
flag the parser admits.  `ctlz`'s `i1 true` is refused by the same rule applied
the other way: not observed, and no clause bounds where its poison would land.
`usub.sat.v32i8`, `ptestz.256` and the escape unit's three carry no flag at all,
so the rule has nothing to bound for them.

## The rank machinery

`setLanes m` is `m`'s set lanes in increasing order, and `rank m i` counts those
below `i`.  The facts a gather/scatter argument needs are all here:

* `setLanes_pairwise` — the lane list is strictly increasing, and
  `setLanes_length_le` — it has at most `w` entries;
* `rank_mono` — the rank does not decrease as the lane rises, and `rank_le` — it
  is bounded by the population count;
* `rank_setLanes_getElem` and `setLanes_getElem?_rank` — the two alignment facts,
  that the `j`-th set lane has rank exactly `j`, and that the rank of a set lane
  indexes that lane.  These are the whole of the correspondence between a mask's
  set lanes and their positions, and both come from the same `List` fact: in a
  strictly increasing list, the entries below the `j`-th entry are exactly its
  predecessors.

The Galois connection is therefore two statements, and only one of them is
unconditional: `pdep_pext` (`pdep (pext a m) m = a &&& m`) holds for every `a`,
because scattering a gather puts back exactly the lanes `m` selects; the round
trip `pext_pdep` (`pext (pdep a m) m = a`) holds when `a` is clear above `m`'s
population count, which is the side condition the gather necessarily has — its
lanes past the count are zero whatever was scattered into `m`.

Nothing here is an axiom, and nothing reaches `BitVec.allOnes` through a core
lemma that carries `Classical.choice` — the module's own lane lemma and
`BitVec.toNat_allOnes` are the two routes it takes; the module's footprint is
`[propext, Quot.sound]`.  The lane algebra that a body and its specification share
— the packing's distribution, a fold's lane, the lane list's zero test, the `i8`
bound, and the disjoint-lane sum — is stated in the section at the end, and it
depends on nothing in this repository below `LeanLLVM.Semantics` and
`LeanLLVM.Memory`.
-/
import LeanLLVM.Semantics
import LeanLLVM.Memory

namespace LeanLLVM.Vellum.BitLanes

open LeanLLVM

/-! ### Packing lanes

`ofLanes` is the inverse of the lane read: `lanesToNat` packs boolean lanes
little-endian, and `lanesToNat_testBit` reads a packed natural back lane by
lane.  The two together are what makes a definition below a lane statement. -/

/-- Pack a lane function into a word: lane `k` is `f k`. -/
def ofLanes {w : Nat} (f : Fin w → Bool) : BitVec w :=
  BitVec.ofNat w (lanesToNat (List.ofFn (fun i : Fin w => BitVec.ofBool (f i))))

/-- Lane `k` of a packed word is the function's value at `k`. -/
theorem ofLanes_getLsbD {w : Nat} (f : Fin w → Bool) {k : Nat} (hk : k < w) :
    (ofLanes f).getLsbD k = f ⟨k, hk⟩ := by
  unfold ofLanes
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [lanesToNat_testBit, List.getElem?_ofFn, dite_eq_left hk]
  cases h : f ⟨k, hk⟩ <;> simp [BitVec.ofBool]

/-- Two lane functions that agree give the same word. -/
theorem ofLanes_congr {w : Nat} {f g : Fin w → Bool} (h : ∀ i, f i = g i) :
    ofLanes f = ofLanes g := by
  unfold ofLanes
  have hf : (fun i : Fin w => BitVec.ofBool (f i)) = (fun i : Fin w => BitVec.ofBool (g i)) := by
    ext i
    rw [h i]
  rw [hf]

/-- A word whose every lane is clear is zero. -/
theorem ofLanes_false {w : Nat} : ofLanes (fun _ => false) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [ofLanes_getLsbD _ hk, BitVec.getLsbD_zero]

/-- The lanes below a bound, as a mask. -/
def lowLanes (w n : Nat) : BitVec w := ofLanes (fun i => decide (i.val < n))

/-- Bit `k` of the lanes below `n` is the test `k < n`. -/
theorem lowLanes_getLsbD {w n : Nat} {k : Nat} (hk : k < w) :
    (lowLanes w n).getLsbD k = decide (k < n) :=
  ofLanes_getLsbD (fun i => decide (i.val < n)) hk

/-! ### The all-ones word and complement, lane by lane

`BitVec.getLsbD_allOnes` and `BitVec.getLsbD_not` both carry `Classical.choice` in
their proof terms.  The two lane facts are elementary, so they are proved here
instead, through `BitVec.xor_allOnes` (`x ^^^ allOnes w = ~~~x`) and the numeral
`2 ^ w - 1`; every theorem below then stays at the module's own footprint. -/

/-- Halving an all-ones word drops one lane. -/
private theorem two_pow_sub_one_div_two (n : Nat) : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
  have hval : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
    rw [Nat.two_pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hval, Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2)]
  omega

/-- A positive-length all-ones word is odd. -/
private theorem two_pow_sub_one_odd (n : Nat) : (2 ^ (n + 1) - 1) % 2 = 1 := by
  have hval : 2 ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by
    rw [Nat.two_pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide : 1 < 2)]

/-- Lane `i` of the numeral `2 ^ w - 1` is set while `i < w`. -/
private theorem testBit_two_pow_sub_one_of_lt :
    ∀ {w i : Nat}, i < w → (2 ^ w - 1).testBit i = true
  | 0, _, h => by omega
  | _ + 1, 0, _ => by rw [Nat.testBit_zero, two_pow_sub_one_odd, decide_eq_true rfl]
  | w + 1, i + 1, h => by
    rw [Nat.testBit_succ, two_pow_sub_one_div_two]
    exact testBit_two_pow_sub_one_of_lt (by omega)

/-- Lane `i` of the numeral `2 ^ w - 1` is the test `i < w`, without the choice
that `Nat.testBit_two_pow_sub_one` carries. -/
theorem testBit_two_pow_sub_one (w i : Nat) :
    (2 ^ w - 1).testBit i = decide (i < w) := by
  by_cases h : i < w
  · rw [testBit_two_pow_sub_one_of_lt h, decide_eq_true h]
  · have hpos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have hle : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : 2 ^ w - 1 < 2 ^ i := by omega
    rw [Nat.testBit_lt_two_pow hlt, decide_eq_false h]

/-- Lane `i` of an all-ones word is set while `i < w`, without the choice that
`BitVec.getLsbD_allOnes` carries. -/
theorem allOnes_getLsbD_of_lt {w i : Nat} (h : i < w) :
    (BitVec.allOnes w).getLsbD i = true := by
  have key : (BitVec.allOnes w).getLsbD i = (2 ^ w - 1).testBit i :=
    BitVec.getLsbD_ofNatLT (n := w) (2 ^ w - 1)
      (by have := Nat.two_pow_pos w; omega) i
  rw [key, testBit_two_pow_sub_one_of_lt h]

/-- Lane `i` of a complement is the complement of the lane, without the choice
that `BitVec.getLsbD_not` carries. -/
theorem getLsbD_not_of_lt {w : Nat} (x : BitVec w) {i : Nat} (hi : i < w) :
    (~~~x).getLsbD i = !x.getLsbD i := by
  have h : (~~~x) = (BitVec.allOnes w ^^^ x) := rfl
  rw [h, BitVec.getLsbD_xor, allOnes_getLsbD_of_lt hi]
  cases x.getLsbD i <;> rfl

/-! ### The set lanes and their rank -/

/-- A mask's set lanes, in increasing order. -/
def setLanes {w : Nat} (m : BitVec w) : List Nat :=
  (List.range w).filter (fun i => m.getLsbD i)

/-- A mask's set lanes are exactly the lanes it sets. -/
theorem mem_setLanes {w : Nat} {m : BitVec w} {i : Nat} :
    i ∈ setLanes m ↔ i < w ∧ m.getLsbD i = true := by
  rw [setLanes, List.mem_filter, List.mem_range]

/-- The natural numbers in order are strictly increasing. -/
theorem range_pairwise (n : Nat) : (List.range n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j _ _ hij
  simpa using hij

/-- A mask's set lanes are strictly increasing. -/
theorem setLanes_pairwise {w : Nat} (m : BitVec w) : (setLanes m).Pairwise (· < ·) :=
  List.Pairwise.filter (fun i => m.getLsbD i) (range_pairwise w)

/-- A mask has no more set lanes than it has lanes. -/
theorem setLanes_length_le {w : Nat} (m : BitVec w) : (setLanes m).length ≤ w := by
  have h := List.length_filter_le (fun i => m.getLsbD i) (List.range w)
  simpa [setLanes] using h

/-- Lane `j` of the set-lane list is a set lane. -/
theorem setLanes_getElem_true {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : m.getLsbD (setLanes m)[j] = true :=
  (mem_setLanes.mp (List.getElem_mem hj)).2

/-- Lane `j` of the set-lane list is inside the word. -/
theorem setLanes_getElem_lt {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : (setLanes m)[j] < w :=
  (mem_setLanes.mp (List.getElem_mem hj)).1

/-- The set-lane list read as a lookup. -/
theorem setLanes_getElem?_eq {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : (setLanes m)[j]? = some ((setLanes m)[j]'hj) :=
  List.getElem?_eq_getElem hj

/-- The rank of a lane: how many of the mask's set lanes lie below it. -/
def rank {w : Nat} (m : BitVec w) (i : Nat) : Nat :=
  ((setLanes m).filter (fun k => decide (k < i))).length

/-- The rank never exceeds the population count. -/
theorem rank_le {w : Nat} (m : BitVec w) (i : Nat) : rank m i ≤ (setLanes m).length :=
  List.length_filter_le (fun k => decide (k < i)) (setLanes m)

/-- Filtering by a weaker test is filtering again, so lengths compare. -/
theorem filter_implies_filter {l : List Nat} {p q : Nat → Bool}
    (h : ∀ a, p a = true → q a = true) : l.filter p = (l.filter q).filter p := by
  rw [List.filter_filter]
  exact List.filter_congr (fun a _ => by
    by_cases hp : p a = true
    · rw [hp, h a hp, Bool.and_self]
    · have hp' : p a = false := by simpa using hp
      rw [hp', Bool.false_and])

/-- **The rank is monotone in the lane.** -/
theorem rank_mono {w : Nat} (m : BitVec w) {i j : Nat} (h : i ≤ j) : rank m i ≤ rank m j := by
  have heq : (setLanes m).filter (fun k => decide (k < i))
      = ((setLanes m).filter (fun k => decide (k < j))).filter (fun k => decide (k < i)) :=
    filter_implies_filter (fun a ha => by
      rw [decide_eq_true_eq] at ha ⊢
      omega)
  unfold rank
  rw [heq]
  exact List.length_filter_le _ _

/-- A list all of whose entries fail a test filters to nothing, without the
choice that `List.filter_eq_nil_iff` carries. -/
theorem filter_eq_nil_of_all_false {l : List Nat} {p : Nat → Bool}
    (h : ∀ a, a ∈ l → p a = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hpa : ¬ p a = true := by rw [h a (List.mem_cons_self ..)]; simp
    rw [List.filter_cons, ite_eq_right hpa]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- In a strictly increasing list, the entries below the `j`-th entry are its
first `j` entries. -/
theorem filter_lt_getElem_eq_take {l : List Nat} (hs : l.Pairwise (· < ·)) {j : Nat}
    (hj : j < l.length) : l.filter (fun k => decide (k < l[j])) = l.take j := by
  induction l generalizing j with
  | nil => exact absurd hj (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hall, hst⟩ := hs
    cases j with
    | zero =>
      rw [List.take_zero]
      refine filter_eq_nil_of_all_false (fun k hk => ?_)
      rw [List.mem_cons] at hk
      have hka : ¬ k < a := by
        rcases hk with hk | hk
        · rw [hk]; omega
        · have := hall k hk; omega
      rw [show (a :: t)[0] = a from rfl]
      simpa using hka
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have ha : decide (a < t[j]) = true := decide_eq_true (hall _ (List.getElem_mem hj'))
      rw [show (a :: t)[j + 1] = t[j] from List.getElem_cons_succ .., List.filter_cons,
        ite_eq_left ha, ih hst hj', List.take_succ_cons]

/-- In a strictly increasing list, the number of entries below the `j`-th entry
is `j`. -/
theorem filter_lt_getElem_eq_take_length {l : List Nat} (hs : l.Pairwise (· < ·))
    {j : Nat} (hj : j < l.length) :
    (l.filter (fun k => decide (k < l[j]))).length = j := by
  rw [filter_lt_getElem_eq_take hs hj, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hj)]

/-- In a strictly increasing list, an entry's own rank indexes it again. -/
theorem filter_lt_getElem?_mem {l : List Nat} (hs : l.Pairwise (· < ·)) {k : Nat}
    (hk : k ∈ l) : l[(l.filter (fun x => decide (x < k))).length]? = some k := by
  induction l with
  | nil => exact absurd hk (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hall, hst⟩ := hs
    rw [List.mem_cons] at hk
    rcases hk with hk | hk
    · have hnil : (k :: t).filter (fun x => decide (x < k)) = [] := by
        refine filter_eq_nil_of_all_false (fun x hx => ?_)
        rw [List.mem_cons] at hx
        have hxk : ¬ x < k := by
          rcases hx with hx | hx
          · rw [hx]; omega
          · have hlt := hall x hx
            rw [← hk] at hlt
            omega
        simpa using hxk
      rw [← hk, hnil]
      rfl
    · have hlt : a < k := hall k hk
      rw [List.filter_cons, ite_eq_left (decide_eq_true hlt)]
      have hidx : (a :: t.filter (fun x => decide (x < k))).length
          = (t.filter (fun x => decide (x < k))).length + 1 := rfl
      rw [hidx, List.getElem?_cons_succ]
      exact ih hst hk

/-- **A set lane's rank is its own index.** -/
theorem rank_setLanes_getElem {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : rank m (setLanes m)[j] = j :=
  filter_lt_getElem_eq_take_length (setLanes_pairwise m) hj

/-- **A set lane's rank indexes that lane.** -/
theorem setLanes_getElem?_rank {w : Nat} (m : BitVec w) {i : Nat} (hi : i < w)
    (hm : m.getLsbD i = true) : (setLanes m)[rank m i]? = some i :=
  filter_lt_getElem?_mem (setLanes_pairwise m) (mem_setLanes.mpr ⟨hi, hm⟩)

/-! ### Gather and scatter -/

/-- `pext a m`: lane `j` is `a`'s lane at the `j`-th set lane of `m`, and clear
at or past `m`'s population count.  This is `llvm.x86.bmi.pext.64`. -/
def pext {w : Nat} (a m : BitVec w) : BitVec w :=
  ofLanes (fun j => ((setLanes m)[j.val]?).map a.getLsbD |>.getD false)

/-- The gathered lane, read as a lookup past the mask's population count. -/
theorem pext_getLsbD {w : Nat} (a m : BitVec w) {j : Nat} (hj : j < w) :
    (pext a m).getLsbD j = (((setLanes m)[j]?).map a.getLsbD).getD false := by
  rw [pext, ofLanes_getLsbD _ hj]

/-- The gathered lane, as `a`'s lane at the `j`-th set lane. -/
theorem pext_getLsbD_of_lt {w : Nat} (a m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) :
    (pext a m).getLsbD j = a.getLsbD ((setLanes m)[j]'hj) := by
  rw [pext_getLsbD (a := a) (m := m) (j := j)
      (hj := Nat.lt_of_lt_of_le hj (setLanes_length_le m)),
    List.getElem?_eq_getElem hj]
  rfl

/-- A gathered lane past the population count is clear. -/
theorem pext_getLsbD_of_ge {w : Nat} (a m : BitVec w) {j : Nat}
    (hj : (setLanes m).length ≤ j) (hjw : j < w) : (pext a m).getLsbD j = false := by
  rw [pext_getLsbD (a := a) (m := m) (j := j) (hj := hjw), List.getElem?_eq_none hj]
  rfl

/-- `pdep a m`: lane `i` is `a`'s lane at `i`'s rank among `m`'s set lanes, and
clear where `m` is clear.  This is `llvm.x86.bmi.pdep.64`. -/
def pdep {w : Nat} (a m : BitVec w) : BitVec w :=
  ofLanes (fun i => m.getLsbD i.val && a.getLsbD (rank m i.val))

/-- Lane `i` of a scatter. -/
theorem pdep_getLsbD {w : Nat} (a m : BitVec w) {i : Nat} (hi : i < w) :
    (pdep a m).getLsbD i = (m.getLsbD i && a.getLsbD (rank m i)) :=
  ofLanes_getLsbD _ hi

/-- **The Galois connection, unconditional side.**  Scattering a gather into `m`
puts back exactly the lanes `m` selects: `pdep (pext a m) m = a &&& m`. -/
theorem pdep_pext {w : Nat} (a m : BitVec w) : pdep (pext a m) m = a &&& m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [pdep_getLsbD (a := pext a m) (m := m) (i := i) (hi := hi), BitVec.getLsbD_and]
  cases hm : m.getLsbD i with
  | false => simp
  | true =>
    have hrank := setLanes_getElem?_rank m hi hm
    have hlt : rank m i < (setLanes m).length := by
      rcases List.getElem?_eq_some_iff.mp hrank with ⟨h, _⟩
      exact h
    rw [pext_getLsbD_of_lt (a := a) (m := m) (j := rank m i) (hj := hlt)]
    have hidx : (setLanes m)[rank m i]'hlt = i := by
      have := hrank
      rw [List.getElem?_eq_getElem hlt] at this
      exact Option.some.inj this
    rw [hidx]
    simp

/-- **The Galois connection, the round trip.**  Gathering a scatter returns `a`
on the lanes below `m`'s population count, and clears the lanes above it. -/
theorem pext_pdep {w : Nat} (a m : BitVec w) :
    pext (pdep a m) m = a &&& lowLanes w (setLanes m).length := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [pext_getLsbD (a := pdep a m) (m := m) (j := j) (hj := hj), BitVec.getLsbD_and,
    lowLanes_getLsbD hj]
  by_cases hlen : j < (setLanes m).length
  · rw [List.getElem?_eq_getElem hlen, decide_eq_true hlen]
    have hrank := rank_setLanes_getElem m hlen
    have hlt := setLanes_getElem_lt m hlen
    rw [Option.map_some, Option.getD_some,
      pdep_getLsbD (a := a) (m := m) (i := (setLanes m)[j]'hlen) (hi := hlt),
      setLanes_getElem_true m hlen, hrank]
    simp
  · rw [List.getElem?_eq_none (by omega), decide_eq_false (by omega)]
    simp

/-- **The Galois connection, stated as a round trip.**  When `a` is clear above
`m`'s population count, gathering a scatter returns `a` itself. -/
theorem pext_pdep_of_clear {w : Nat} (a m : BitVec w)
    (hclear : ∀ j, (setLanes m).length ≤ j → j < w → a.getLsbD j = false) :
    pext (pdep a m) m = a := by
  rw [pext_pdep]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, lowLanes_getLsbD hj]
  by_cases hlen : j < (setLanes m).length
  · rw [decide_eq_true hlen]; simp
  · rw [decide_eq_false (by omega), Bool.and_false, hclear j (by omega) hj]

/-! ### `ctlz` and the trailing run -/

/-- The leading-zero count above lane `i`: walk down from `i`, counting one for
each clear lane and stopping at the first set one. -/
def leadZerosAux {w : Nat} (x : BitVec w) : Nat → Nat
  | 0 => if x.getLsbD 0 then 0 else 1
  | i + 1 => if x.getLsbD (i + 1) then 0 else 1 + leadZerosAux x i

/-- `llvm.ctlz.i64`: the number of clear lanes above the highest set lane, and
the width for the zero word. -/
def ctlz {w : Nat} (x : BitVec w) : Nat :=
  match w with
  | 0 => 0
  | n + 1 => leadZerosAux x n

/-- A word's suffix run of set lanes: lane `n - 1` counted down while set. -/
def suffixRun {w : Nat} (m : BitVec w) : Nat → Nat
  | 0 => 0
  | n + 1 => if m.getLsbD n then suffixRun m n + 1 else 0

/-- The length of the maximal suffix of set lanes. -/
def trailingRun {w : Nat} (m : BitVec w) : Nat := suffixRun m w

/-- A suffix run is no longer than the lanes it counts. -/
theorem suffixRun_le {w : Nat} (m : BitVec w) : ∀ n, suffixRun m n ≤ n
  | 0 => by rw [suffixRun]; omega
  | n + 1 => by
    rw [suffixRun]
    split
    · have := suffixRun_le m n; omega
    · omega

/-- The trailing run is no longer than the word. -/
theorem trailingRun_le {w : Nat} (m : BitVec w) : trailingRun m ≤ w :=
  suffixRun_le m w

/-- The step shared by the two recursions: a clear lane stops the count, a set one
extends it. -/
theorem ite_not_add (b : Bool) (s : Nat) :
    (if (!b) = true then 0 else 1 + s) = (if b = true then s + 1 else 0) := by
  cases b <;> simp <;> omega

/-- **`ctlz` of the complement is the trailing run.**  The clear lanes of `~~~m`
above the highest set lane are exactly `m`'s suffix of set lanes. -/
theorem ctlz_not_eq_trailingRun {w : Nat} (m : BitVec w) : ctlz (~~~m) = trailingRun m := by
  cases w with
  | zero => simp [ctlz, trailingRun, suffixRun]
  | succ w' =>
    have key : ∀ i, i < w' + 1 → leadZerosAux (~~~m) i = suffixRun m (i + 1) := by
      intro i
      induction i with
      | zero =>
        intro _
        rw [leadZerosAux, suffixRun, getLsbD_not_of_lt m (by omega)]
        cases m.getLsbD 0 <;> rfl
      | succ i ih =>
        intro h
        have hnot : (~~~m).getLsbD (i + 1) = !m.getLsbD (i + 1) :=
          getLsbD_not_of_lt m h
        rw [leadZerosAux, suffixRun, hnot, ih (by omega)]
        exact ite_not_add (m.getLsbD (i + 1)) (suffixRun m (i + 1))
    rw [ctlz, trailingRun]
    exact key w' (by omega)

/-- The zero word has no set lane, so every lane is leading. -/
theorem ctlz_zero {w : Nat} : ctlz (0#w) = w := by
  cases w with
  | zero => rfl
  | succ w' =>
    have haux : ∀ i, leadZerosAux (0#(w' + 1)) i = i + 1 := by
      intro i
      induction i with
      | zero => rw [leadZerosAux, BitVec.getLsbD_zero]; rfl
      | succ i ih =>
        rw [leadZerosAux, BitVec.getLsbD_zero, ih]
        show 1 + (i + 1) = i + 1 + 1
        omega
    rw [ctlz, haux]

/-! ### `ctpop` and `cttz`

Both are counts over the set lanes, and both are determined at the zero word.
`ctpop` is exact there and needs no bound.  `cttz` at the flag `i1 false` is
exact there too (it is `w`); at `i1 true` it is the value LLVM leaves poison,
admitted under the bound the module docstring states once. -/

/-- `llvm.ctpop`: the population count, as the sum of the word's lanes read one
at a time — lane `k` contributes one when it is set.  `ctpop.i32` and
`ctpop.i64` share this definition, each at its own width. -/
def ctpop {w : Nat} (x : BitVec w) : Nat :=
  ((List.range w).map (fun k => if x.getLsbD k then 1 else 0)).sum

/-- A list's lane indicators sum to the length of its set lanes. -/
private theorem sum_map_ite_eq_length_filter (l : List Nat) (p : Nat → Bool) :
    (l.map (fun k => if p k then 1 else 0)).sum = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    split
    · rw [ih, List.length_cons]
      omega
    · simpa using ih

/-- **The population count is the number of set lanes.** -/
theorem ctpop_eq_setLanes_length {w : Nat} (x : BitVec w) :
    ctpop x = (setLanes x).length :=
  sum_map_ite_eq_length_filter (List.range w) (fun k => x.getLsbD k)

/-- `llvm.cttz`: the least set lane, and the word's width when no lane is set —
LLVM's `i1 false` flag is exactly this.  At `i1 true` LLVM makes the zero word
poison instead; this model has no poison, so `w` is the determined value it gives
there, admissible only under the bound the module docstring states. -/
def cttz {w : Nat} (x : BitVec w) : Nat :=
  ((List.range w).find? (fun k => x.getLsbD k)).getD w

/-- Finding the first set lane is taking the head of the set-lane list. -/
private theorem find?_eq_head_filter (l : List Nat) (p : Nat → Bool) :
    l.find? p = (l.filter p).head? := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons]
    split
    · rename_i hp
      rw [List.find?_cons]
      rw [show p a = true from hp]
      rfl
    · rename_i hp
      rw [List.find?_cons]
      rw [show p a = false from by cases hv : p a <;> simp_all]
      exact ih

/-- **The trailing count is the least set lane**, and the width at the zero
word. -/
theorem cttz_eq_head {w : Nat} (x : BitVec w) :
    cttz x = ((setLanes x).head?).getD w := by
  unfold cttz setLanes
  rw [find?_eq_head_filter]

/-! ### The UTF-8 stage's two instructions

The UTF-8 stage's `llvm.usub.sat.v32i8` and `llvm.x86.avx.ptestz.256` are exact:
neither has a flag, and the parser admits only their written shapes.  They are
stated here at the byte lane and at the word rather than at the bit, because
that is the granularity the instructions read: the subtract saturates each byte,
and the test reads all 256 bits of the and-word at once. -/

/-- `llvm.usub.sat.v32i8`'s lane: unsigned saturating subtraction at one byte,
`a - b` when the subtrahend fits and `0` otherwise.  A vector call applies it
lane by lane. -/
def subsSat (a b : BitVec 8) : BitVec 8 :=
  if b.toNat ≤ a.toNat then a - b else 0

/-- A lane whose subtrahend fits is the plain difference. -/
theorem subsSat_of_le {a b : BitVec 8} (h : b.toNat ≤ a.toNat) :
    subsSat a b = a - b := by
  simp [subsSat, h]

/-- A lane whose subtrahend is larger saturates at zero. -/
theorem subsSat_of_gt {a b : BitVec 8} (h : a.toNat < b.toNat) :
    subsSat a b = 0 := by
  have h' : ¬ b.toNat ≤ a.toNat := by omega
  simp [subsSat, h']

/-- `llvm.x86.avx.ptestz.256`'s word test: `1` when no bit is set in both
operands, `0` otherwise.  The result type is the instruction's `i32`. -/
def ptestz {w : Nat} (a b : BitVec w) : BitVec 32 :=
  if a &&& b = 0 then 1 else 0

/-- The test answers one exactly on a cleared and-word. -/
theorem ptestz_eq_one_iff {w : Nat} (a b : BitVec w) :
    ptestz a b = 1 ↔ a &&& b = 0 := by
  by_cases h : a &&& b = 0 <;> simp [ptestz, h]

/-- The test answers zero exactly when some lane is set in both operands. -/
theorem ptestz_eq_zero_iff {w : Nat} (a b : BitVec w) :
    ptestz a b = 0 ↔ a &&& b ≠ 0 := by
  by_cases h : a &&& b = 0 <;> simp [ptestz, h]

/-! ### The escape unit's three instructions

`json-escape.candidate.ll` calls three intrinsic spellings the entry, mask and
UTF-8 units do not: `llvm.umin.i32` in `xl_batch`, and the pair
`llvm.x86.ssse3.pmadd.ub.sw.128` then `llvm.x86.sse2.pmadd.wd` in
`us_hex4_pshufb`, whose four hexadecimal digits are read as lane 0 of the
`pmadd.wd` result.  Each model below is the instruction, at the granularity the
instruction reads: the scalar minimum at the word, and the two multiply-adds at
the adjacent lane pair.

Three facts in them are the ones a plausible lookalike would get wrong, and each
has a control rather than only a sentence:

* `umin` compares **unsigned**, so `umin 0x80000000 1 = 1` at `i32`
  (`umin_highBit_control`); a signed comparison would answer `0x80000000`.
* `pmadd.ub.sw` is **not symmetric**.  Its first operand's byte lanes are read
  unsigned and its second's signed — that is `_mm_maddubs_epi16`'s reading — and
  its result is a signed word, which the spelling's `ub`/`sw` abbreviates.
  `pmaddUbSw_operand_order_control` is the pair at which the swapped reading is
  `0x4000` and the instruction's is `0xC000`.  Its pair sum is then
  **saturated** to a signed word rather than wrapped:
  `pmaddUbSw_saturate_control` gives `0x7FFF` where the modular sum of the same
  17-bit value is `0xFD02`.  The individual products fit a signed word
  (`255 * -128 = -32640`), so the pair sum is the only place saturation occurs.
* `pmadd.wd` **wraps**.  It multiplies signed word lanes and adds the two
  adjacent products at `i32` with no saturation and no trap; with both products
  at `2 ^ 30` the sum is `2 ^ 31`, which the instruction writes as `-2 ^ 31`
  (`pmaddWd_wrap_control`), so the model's `BitVec` arithmetic is the
  instruction's and not exact arithmetic's.

None of the three carries a flag, so the poison note above has nothing to bound
here: `umin` is total at every operand pair and both multiply-adds are total at
every lane pair, which is why no clause of the escape unit's records has to bound
where a poison value would land. -/

/-- The adjacent pairs of a lane list, in order: pair `j` is lanes `2j` and
`2j + 1`.  A list of fewer than two remaining lanes contributes no pair, which
the multiply-adds' eight- and sixteen-lane operands make unreachable. -/
def pairsOf {α : Type} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: pairsOf rest
  | _ => []

/-- A lane list of `n` lanes has `n / 2` adjacent pairs. -/
theorem pairsOf_length {α : Type} (l : List α) : (pairsOf l).length = l.length / 2 := by
  induction l using pairsOf.induct with
  | case1 a b rest ih =>
      simp only [pairsOf, List.length_cons]
      rw [ih, show rest.length + 1 + 1 = 2 * 1 + rest.length from by omega,
        Nat.mul_add_div (by decide)]
      omega
  | case2 t h =>
      cases t with
      | nil => simp [pairsOf]
      | cons a t' =>
        cases t' with
        | nil => simp [pairsOf]
        | cons b rest => exact (h a b rest rfl).elim

/-- `llvm.umin`: the unsigned minimum of two words.  The order is `toNat`'s, so
at `i32` a high bit does not make an operand the larger one; the escape emission
calls the spelling at `i32` only, and the definition is the two-operand order at
whatever width a call spells. -/
def umin {w : Nat} (a b : BitVec w) : BitVec w :=
  if a.toNat ≤ b.toNat then a else b

/-- The minimum is the first operand exactly when it is the smaller. -/
theorem umin_eq_left {w : Nat} {a b : BitVec w} (h : a.toNat ≤ b.toNat) :
    umin a b = a := by
  simp [umin, h]

/-- The minimum is the second operand exactly when the first is not the smaller. -/
theorem umin_eq_right {w : Nat} {a b : BitVec w} (h : ¬ a.toNat ≤ b.toNat) :
    umin a b = b := by
  simp [umin, h]

/-- The comparison is unsigned: a set top bit does not make an operand larger. -/
theorem umin_highBit_control : umin (0x80000000 : BitVec 32) 1 = 1 := by decide

/-- One `pmadd.wd` lane: the two products of a pair of adjacent signed word lanes,
summed at `i32`.  The parameters are the **first** operand's pair and then the
**second's**, in the order the call spells them. -/
def pmaddWdLane (x₀ x₁ y₀ y₁ : BitVec 16) : BitVec 32 :=
  BitVec.ofInt 32 (x₀.toInt * y₀.toInt + x₁.toInt * y₁.toInt)

/-- `llvm.x86.sse2.pmadd.wd`: signed word multiply-add.  Word lanes `2j` and
`2j + 1` of each operand are multiplied pairwise, the two products are summed, and
the sum is `i32` lane `j` — wrapping, because the instruction neither saturates
nor traps.  The emission calls it at `<8 x i16>` → `<4 x i32>`, which is the
shape `checkIntrinsicShape` admits; a call at another arity, operand type or
result type is refused by name. -/
def pmaddWd (x y : List (BitVec 16)) : List (BitVec 32) :=
  List.zipWith (fun (x₀, x₁) (y₀, y₁) => pmaddWdLane x₀ x₁ y₀ y₁) (pairsOf x) (pairsOf y)

/-- One result lane consumes one adjacent pair of each operand. -/
theorem pmaddWd_cons (x₀ x₁ : BitVec 16) (xs : List (BitVec 16)) (y₀ y₁ : BitVec 16)
    (ys : List (BitVec 16)) :
    pmaddWd (x₀ :: x₁ :: xs) (y₀ :: y₁ :: ys)
      = pmaddWdLane x₀ x₁ y₀ y₁ :: pmaddWd xs ys := rfl

/-- The multiply-add halves the lane count, so the pairing is exhaustive on the
measured shape. -/
theorem pmaddWd_length (x y : List (BitVec 16)) :
    (pmaddWd x y).length = min (x.length / 2) (y.length / 2) := by
  rw [pmaddWd, List.length_zipWith, pairsOf_length, pairsOf_length]

/-- At the emission's shape the result is the `<4 x i32>` the call declares. -/
theorem pmaddWd_length_eight {x y : List (BitVec 16)} (hx : x.length = 8)
    (hy : y.length = 8) : (pmaddWd x y).length = 4 := by
  rw [pmaddWd_length, hx, hy]
  rfl

/-- The wrap case: two products of `2 ^ 30` sum to `2 ^ 31`, which `i32` writes
as `-2 ^ 31`.  An exact-arithmetic reading of the instruction would answer
`0x100000000` and have no `i32` lane to put it in. -/
theorem pmaddWd_wrap_control :
    pmaddWd [0x8000, 0x8000] [0x8000, 0x8000] = [0x80000000] := by decide

/-- A signed lane pair: `-1 * 1` is `-1`, and `i32` writes it all ones. -/
theorem pmaddWd_signed_control :
    pmaddWd [0xFFFF, 0x0000] [0x0001, 0x0000] = [0xFFFFFFFF] := by decide

/-- A signed word saturated from exact arithmetic: PMADDUBSW's pack step, which
clamps a pair sum (which can need seventeen bits) into `[-2 ^ 15, 2 ^ 15 - 1]`. -/
def satI16 (k : Int) : BitVec 16 :=
  if 32767 < k then BitVec.ofInt 16 32767
  else if k < -32768 then BitVec.ofInt 16 (-32768)
  else BitVec.ofInt 16 k

/-- A sum already inside the signed word's range is itself. -/
theorem satI16_of_range {k : Int} (h₁ : k ≤ 32767) (h₂ : -32768 ≤ k) :
    satI16 k = BitVec.ofInt 16 k := by
  simp [satI16, show ¬ 32767 < k from by omega, show ¬ k < -32768 from by omega]

/-- A sum above the range saturates at the largest signed word. -/
theorem satI16_of_high {k : Int} (h : 32767 < k) : satI16 k = BitVec.ofInt 16 32767 := by
  simp [satI16, h]

/-- A sum below the range saturates at the smallest signed word. -/
theorem satI16_of_low {k : Int} (h : k < -32768) :
    satI16 k = BitVec.ofInt 16 (-32768) := by
  simp [satI16, show ¬ 32767 < k from by omega, h]

/-- One `pmadd.ub.sw` lane: the first operand's byte lanes read **unsigned**, the
second's read **signed**, the two products summed exactly and saturated to a signed
word.  The parameters are the first operand's pair and then the second's, in the
order the call spells them. -/
def pmaddUbSwLane (x₀ x₁ y₀ y₁ : BitVec 8) : BitVec 16 :=
  satI16 ((x₀.toNat : Int) * y₀.toInt + (x₁.toNat : Int) * y₁.toInt)

/-- `llvm.x86.ssse3.pmadd.ub.sw.128`: unsigned-byte times signed-byte multiply-add
with a saturated signed-word result.  Byte lanes `2j` and `2j + 1` of each operand
are multiplied pairwise — the first operand's read unsigned, the second's signed —
the two products are summed, and the sum saturates into signed word lane `j`.  The
emission calls it at `<16 x i8>` → `<8 x i16>`, which is the shape
`checkIntrinsicShape` admits; a call at another arity, operand type or result
type is refused by name. -/
def pmaddUbSw (x y : List (BitVec 8)) : List (BitVec 16) :=
  List.zipWith (fun (x₀, x₁) (y₀, y₁) => pmaddUbSwLane x₀ x₁ y₀ y₁) (pairsOf x) (pairsOf y)

/-- One result lane consumes one adjacent pair of each operand. -/
theorem pmaddUbSw_cons (x₀ x₁ : BitVec 8) (xs : List (BitVec 8)) (y₀ y₁ : BitVec 8)
    (ys : List (BitVec 8)) :
    pmaddUbSw (x₀ :: x₁ :: xs) (y₀ :: y₁ :: ys)
      = pmaddUbSwLane x₀ x₁ y₀ y₁ :: pmaddUbSw xs ys := rfl

/-- The multiply-add halves the lane count. -/
theorem pmaddUbSw_length (x y : List (BitVec 8)) :
    (pmaddUbSw x y).length = min (x.length / 2) (y.length / 2) := by
  rw [pmaddUbSw, List.length_zipWith, pairsOf_length, pairsOf_length]

/-- At the emission's shape the result is the `<8 x i16>` the call declares. -/
theorem pmaddUbSw_length_sixteen {x y : List (BitVec 8)} (hx : x.length = 16)
    (hy : y.length = 16) : (pmaddUbSw x y).length = 8 := by
  rw [pmaddUbSw_length, hx, hy]
  rfl

/-- The operand order: `0x80` read unsigned times `0x80` read signed is `-16384`,
which is `0xC000`; the signed-by-signed reading would answer `0x4000`. -/
theorem pmaddUbSw_operand_order_control :
    pmaddUbSw [0x80, 0x00] [0x80, 0x00] = [0xC000] := by decide

/-- The saturation: two products of `255 * 127` sum to `64770`, which the
instruction packs as `0x7FFF`; the modular sum of the same value is `0xFD02`. -/
theorem pmaddUbSw_saturate_control :
    pmaddUbSw [0xFF, 0xFF] [0x7F, 0x7F] = [0x7FFF] := by decide

/-- A negative lane: `2 * -1` is `-2`, and the signed word writes it `0xFFFE`. -/
theorem pmaddUbSw_signed_control :
    pmaddUbSw [0x02, 0x00] [0xFF, 0x00] = [0xFFFE] := by decide

/-! #### Axiom footprints

The three models' own terms: `umin` is axiom-free, and the two multiply-adds reach
`propext` through `BitVec.ofInt`'s definition and nothing else.  Both are inside
the module's ceiling, and no declaration here introduces a carrier. -/

/-- info: 'LeanLLVM.Vellum.BitLanes.umin' does not depend on any axioms -/
#guard_msgs in
#print axioms umin

/-- info: 'LeanLLVM.Vellum.BitLanes.pmaddWd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pmaddWd

/-- info: 'LeanLLVM.Vellum.BitLanes.pmaddUbSw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pmaddUbSw

/-- info: 'LeanLLVM.Vellum.BitLanes.pairsOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pairsOf

/-- info: 'LeanLLVM.Vellum.BitLanes.satI16' depends on axioms: [propext] -/
#guard_msgs in
#print axioms satI16

/-! ### The lane algebra: packing, distributing, folding, and the lane list

`packLanes` (`LeanLLVM/Semantics.lean`) lays a lane list out little-endian —
lane `k` at bits `[k * w, (k + 1) * w)` of the natural — and `unpackLanes` reads
a word back at a lane width.  That pair is what a vector `bitcast` is
(`bitcastVecLanes wOut nOut lanes = unpackLanes wOut nOut (packLanes lanes)`), so
the facts below are what lets an emitted body's lane list stand for a list-shaped
specification, and a specification's lane list for the body's words.  They are
stated over the packing and the lane read, and over nothing else: no fixture, no
unit, no call environment, no route.

**Distribution.**  A lane-wise bitwise operation is the same operation on the
packed word, in both directions: `unpackLanes_or`/`_and`/`_xor`/`_not` cut the
word at a lane, and `packLanes_zipWith_or`/`_and`/`_xor`/`_map_not` read the list
back from the word.  The cutting direction is `Nat.or_div_two_pow` and
`BitVec.ofNat_or`: lane `k` is the quotient by `2 ^ (k * w)`, and cutting commutes
with `|||` because no lane carries into another.  The packing direction is the
same statement read backwards through `unpackLanes_packLanes` and
`packLanes_unpackLanes`, so the two directions cannot disagree — which is what a
body and its specification need, since each crosses the bitcast once.  Two facts
about the all-ones word are proved here for the complement's sake
(`unpackLanes_allOnes`, and `allOnes_xor_eq_not` in the private step), because
the core lemma that states the complement's lane carries `Classical.choice`.

**The fold's lane.**  `foldl_or_getLsbD` and its `&&&` and `^^^` siblings say a
fold's lane is a function of its operands' lanes: `|||` reads as `any`, `&&&` as
`all`, and `^^^` as the fold of the bits.  `getLsbD_or_eq_false_iff` and its
siblings give the same step at one operation.  They are proved from
`BitVec.getLsbD_or`/`_and`/`_xor` and a case split on the lane values, never by
`decide`: a symbolic `BitVec 8 × BitVec 8` product is 256 × 256 = 65,536 cases
and crosses the default heartbeat budget, while the bitwise identity closes in
one split.

**The lane list.**  `packLanes_eq_zero_iff` reads a packed word as its lanes, in
`∀` form, and `packLanes_eq_zero_iff_all` as a `List.all` — the decidable form a
verdict reads, because `List.all` on a list of lanes is a computation while
`decide` over a `∀` on a symbolic product type has no `Decidable` instance at
all.  `zipWith_zero_right` is the zero lane as an `|||` identity, stated for an
arbitrary operation and zero because the two sides of a comparison need not share
a lane type: a specification's accumulator is a byte list (`UInt8`) where an
emitted body's is a word's lane list (`BitVec w`), and both are read by the same
`zipWith`.  It is what makes "this block contributed nothing" a statement about
the accumulator rather than about a copy of it.

**The `i8` facts.**  `getLsbD_seven_iff` and `getLsbD_seven_false_iff` read bit 7
as the bound `0x80`, `getLsbD_highBit` reads the mask word's own lane, and
`and80_eq_zero_iff`/`and80_eq_zero_iff_lt` turn a cleared high-bit mask into
"every byte is below `0x80`" — the form an ASCII gate's `ptestz` test is read at.

**The controls.**  Each family carries a decided witness that a near-miss does
not satisfy the statement it sits beside, so a reader can see which clause is
load-bearing.  `packLanes_zipWith_or_control`: the length hypothesis is not
decoration, because `zipWith` stops at the shorter list.
`foldl_or_getLsbD_control`: a `|||` fold's lane is not a `&&&` fold's.
`packLanes_eq_zero_iff_control`: the zero characterization is not a gate's ASCII
predicate, which a near-miss that reused `all` for it would confuse.
`and80_eq_zero_iff_control`: the mask reading is the `i8` bound and not a wider
one, because at sixteen bits the mask misses the bit the bound sees.

Nothing in this section is an axiom, and nothing reaches a core lemma carrying
`Classical.choice`: the all-ones word enters only through
`BitVec.toNat_allOnes` and this module's own `allOnes_getLsbD_of_lt`, and the
complement's lane through `getLsbD_not_of_lt`.  `decide` appears only on closed
facts, never over a symbolic word. -/

private theorem map_zipWith_map {α β γ δ : Type} (l : List α) (f : α → β)
    (g : β → γ → δ) (h : α → γ) :
    List.zipWith g (l.map f) (l.map h) = l.map (fun x => g (f x) (h x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, ih, List.map_cons]

theorem unpackLanes_or {w n : Nat} (u v : Nat) :
    unpackLanes w n (u ||| v) =
      List.zipWith (· ||| ·) (unpackLanes w n u) (unpackLanes w n v) := by
  have h : (fun k => BitVec.ofNat w ((u ||| v) / 2 ^ (k * w)))
      = fun k => BitVec.ofNat w (u / 2 ^ (k * w)) ||| BitVec.ofNat w (v / 2 ^ (k * w)) := by
    funext k
    rw [Nat.or_div_two_pow, BitVec.ofNat_or]
  simp only [unpackLanes, h]
  exact (map_zipWith_map (List.range n) _ _ _).symm

theorem unpackLanes_and {w n : Nat} (u v : Nat) :
    unpackLanes w n (u &&& v) =
      List.zipWith (· &&& ·) (unpackLanes w n u) (unpackLanes w n v) := by
  have h : (fun k => BitVec.ofNat w ((u &&& v) / 2 ^ (k * w)))
      = fun k => BitVec.ofNat w (u / 2 ^ (k * w)) &&& BitVec.ofNat w (v / 2 ^ (k * w)) := by
    funext k
    rw [Nat.and_div_two_pow, BitVec.ofNat_and]
  simp only [unpackLanes, h]
  exact (map_zipWith_map (List.range n) _ _ _).symm

theorem unpackLanes_xor {w n : Nat} (u v : Nat) :
    unpackLanes w n (u ^^^ v) =
      List.zipWith (· ^^^ ·) (unpackLanes w n u) (unpackLanes w n v) := by
  have h : (fun k => BitVec.ofNat w ((u ^^^ v) / 2 ^ (k * w)))
      = fun k => BitVec.ofNat w (u / 2 ^ (k * w)) ^^^ BitVec.ofNat w (v / 2 ^ (k * w)) := by
    funext k
    rw [Nat.xor_div_two_pow, BitVec.ofNat_xor]
  simp only [unpackLanes, h]
  exact (map_zipWith_map (List.range n) _ _ _).symm

private theorem two_pow_sub_one_div {m k : Nat} (hk : k ≤ m) :
    (2 ^ m - 1) / 2 ^ k = 2 ^ (m - k) - 1 := by
  have hAB : 2 ^ (m - k) * 2 ^ k = 2 ^ m := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmul : (2 ^ (m - k) - 1) * 2 ^ k = 2 ^ m - 2 ^ k := by
    rw [Nat.sub_mul, hAB, Nat.one_mul]
  have hle : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hk
  have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [show 2 ^ m - 1 = (2 ^ k - 1) + (2 ^ (m - k) - 1) * 2 ^ k by rw [hmul]; omega]
  rw [Nat.mul_comm (2 ^ (m - k) - 1) (2 ^ k),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (by omega)]
  omega

private theorem two_pow_mul_sub_one_mod {w q : Nat} (hq : 1 ≤ q) :
    (2 ^ (w * q) - 1) % 2 ^ w = 2 ^ w - 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, q = d + 1 := ⟨q - 1, by omega⟩
  have hexp : 2 ^ (w * (d + 1)) = 2 ^ w * 2 ^ (w * d) := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * d)) (2 ^ w)]
  have hmul : 2 ^ w * (2 ^ (w * d) - 1) = 2 ^ w * 2 ^ (w * d) - 2 ^ w := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hshape : 2 ^ (w * (d + 1)) - 1 = (2 ^ w - 1) + 2 ^ w * (2 ^ (w * d) - 1) := by
    rw [hexp, hmul]
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (w * d) := Nat.one_le_two_pow (n := w * d)
    have h4 : 2 ^ w ≤ 2 ^ w * 2 ^ (w * d) := by
      simpa using Nat.mul_le_mul_left (2 ^ w) h2
    omega
  rw [hshape, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos w; omega)

private theorem ofNat_two_pow_mul_sub_one_eq_allOnes {w q : Nat} (hq : 1 ≤ q) :
    BitVec.ofNat w (2 ^ (w * q) - 1) = BitVec.allOnes w := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes, two_pow_mul_sub_one_mod hq]

theorem unpackLanes_allOnes {w n : Nat} :
    unpackLanes w n (2 ^ (n * w) - 1) = List.replicate n (BitVec.allOnes w) := by
  apply List.ext_getElem
  · rw [unpackLanes_length, List.length_replicate]
  · intro k h1 h2
    have hk : k < n := by simpa [unpackLanes_length] using h1
    rw [show (unpackLanes w n (2 ^ (n * w) - 1))[k]'h1
          = BitVec.ofNat w ((2 ^ (n * w) - 1) / 2 ^ (k * w)) from by
        simp [unpackLanes, List.getElem_range]]
    rw [show (List.replicate n (BitVec.allOnes w))[k]'h2 = BitVec.allOnes w from by simp]
    rw [two_pow_sub_one_div (Nat.mul_le_mul_right w (Nat.le_of_lt hk)),
      ← Nat.sub_mul, Nat.mul_comm (n - k) w]
    exact ofNat_two_pow_mul_sub_one_eq_allOnes (by omega)

private theorem zipWith_replicate_left {α β γ : Type} (f : α → β → γ) (l : List β)
    {n : Nat} {a : α} (h : l.length = n) :
    List.zipWith f (List.replicate n a) l = l.map (fun x => f a x) := by
  induction l generalizing n with
  | nil =>
      have hn : n = 0 := by simpa using h.symm
      subst hn
      rfl
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ m =>
          rw [List.replicate_succ, List.zipWith_cons_cons, ih (by simpa using h),
            List.map_cons]

private theorem allOnes_xor_eq_not {w : Nat} (x : BitVec w) :
    BitVec.allOnes w ^^^ x = ~~~x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_xor, allOnes_getLsbD_of_lt hj, Bool.true_xor, getLsbD_not_of_lt _ hj]

private theorem map_allOnes_xor {w : Nat} (l : List (BitVec w)) :
    l.map (fun x => BitVec.allOnes w ^^^ x) = l.map (fun x => ~~~x) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.map_cons, ih, allOnes_xor_eq_not]

theorem unpackLanes_not {w n : Nat} (u : Nat) :
    unpackLanes w n ((2 ^ (n * w) - 1) ^^^ u) =
      (unpackLanes w n u).map (fun x => ~~~x) := by
  rw [unpackLanes_xor, unpackLanes_allOnes,
    zipWith_replicate_left (· ^^^ ·) (unpackLanes w n u) (unpackLanes_length w n u),
    map_allOnes_xor]

/-! #### The packing side, through the round trip -/

theorem packLanes_zipWith_or {w : Nat} {a b : List (BitVec w)} (h : a.length = b.length) :
    packLanes (List.zipWith (· ||| ·) a b) = packLanes a ||| packLanes b := by
  have ha : a = unpackLanes w a.length (packLanes a) := (unpackLanes_packLanes a).symm
  have hb : b = unpackLanes w b.length (packLanes b) := (unpackLanes_packLanes b).symm
  have hL : packLanes (List.zipWith (· ||| ·) a b)
      = (packLanes a ||| packLanes b) % 2 ^ (a.length * w) := by
    conv => lhs; rw [ha, hb, ← h]
    rw [← unpackLanes_or, packLanes_unpackLanes]
  rw [hL, Nat.mod_eq_of_lt (Nat.or_lt_two_pow (packLanes_lt a) (by rw [h]; exact packLanes_lt b))]

theorem packLanes_zipWith_and {w : Nat} {a b : List (BitVec w)} (h : a.length = b.length) :
    packLanes (List.zipWith (· &&& ·) a b) = packLanes a &&& packLanes b := by
  have ha : a = unpackLanes w a.length (packLanes a) := (unpackLanes_packLanes a).symm
  have hb : b = unpackLanes w b.length (packLanes b) := (unpackLanes_packLanes b).symm
  have hL : packLanes (List.zipWith (· &&& ·) a b)
      = (packLanes a &&& packLanes b) % 2 ^ (a.length * w) := by
    conv => lhs; rw [ha, hb, ← h]
    rw [← unpackLanes_and, packLanes_unpackLanes]
  rw [hL, Nat.mod_eq_of_lt (Nat.and_lt_two_pow (packLanes a) (by rw [h]; exact packLanes_lt b))]

theorem packLanes_zipWith_xor {w : Nat} {a b : List (BitVec w)} (h : a.length = b.length) :
    packLanes (List.zipWith (· ^^^ ·) a b) = packLanes a ^^^ packLanes b := by
  have ha : a = unpackLanes w a.length (packLanes a) := (unpackLanes_packLanes a).symm
  have hb : b = unpackLanes w b.length (packLanes b) := (unpackLanes_packLanes b).symm
  have hL : packLanes (List.zipWith (· ^^^ ·) a b)
      = (packLanes a ^^^ packLanes b) % 2 ^ (a.length * w) := by
    conv => lhs; rw [ha, hb, ← h]
    rw [← unpackLanes_xor, packLanes_unpackLanes]
  rw [hL, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (packLanes_lt a) (by rw [h]; exact packLanes_lt b))]

theorem packLanes_map_not {w : Nat} (a : List (BitVec w)) :
    packLanes (a.map (fun x => ~~~x)) = (2 ^ (a.length * w) - 1) ^^^ packLanes a := by
  have ha : a = unpackLanes w a.length (packLanes a) := (unpackLanes_packLanes a).symm
  have h : a.map (fun x => ~~~x)
      = unpackLanes w a.length ((2 ^ (a.length * w) - 1) ^^^ packLanes a) := by
    conv => lhs; rw [ha]
    exact (unpackLanes_not (w := w) (n := a.length) (u := packLanes a)).symm
  rw [h, packLanes_unpackLanes]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow
    (by have := Nat.two_pow_pos (a.length * w); omega) (packLanes_lt a))

/-! #### The lane ops and the folds -/

theorem getLsbD_or_eq_false_iff {w : Nat} (x y : BitVec w) (i : Nat) :
    (x ||| y).getLsbD i = false ↔ x.getLsbD i = false ∧ y.getLsbD i = false := by
  rw [BitVec.getLsbD_or]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp

theorem getLsbD_and_eq_true_iff {w : Nat} (x y : BitVec w) (i : Nat) :
    (x &&& y).getLsbD i = true ↔ x.getLsbD i = true ∧ y.getLsbD i = true := by
  rw [BitVec.getLsbD_and]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp

theorem getLsbD_xor_eq_false_iff {w : Nat} (x y : BitVec w) (i : Nat) :
    (x ^^^ y).getLsbD i = false ↔ x.getLsbD i = y.getLsbD i := by
  rw [BitVec.getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp

theorem foldl_or_getLsbD {w : Nat} (l : List (BitVec w)) (init : BitVec w) (i : Nat) :
    (l.foldl (· ||| ·) init).getLsbD i =
      (init.getLsbD i || l.any (fun x => x.getLsbD i)) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, List.any_cons, ih (init := init ||| x), BitVec.getLsbD_or,
        Bool.or_assoc]

theorem foldl_and_getLsbD {w : Nat} (l : List (BitVec w)) (init : BitVec w) (i : Nat) :
    (l.foldl (· &&& ·) init).getLsbD i =
      (init.getLsbD i && l.all (fun x => x.getLsbD i)) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, List.all_cons, ih (init := init &&& x), BitVec.getLsbD_and,
        Bool.and_assoc]

theorem foldl_xor_getLsbD {w : Nat} (l : List (BitVec w)) (init : BitVec w) (i : Nat) :
    (l.foldl (· ^^^ ·) init).getLsbD i =
      l.foldl (fun acc x => acc ^^ x.getLsbD i) (init.getLsbD i) := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (init := init ^^^ x), BitVec.getLsbD_xor]

/-! #### The lane list: zero, `all`, and the `|||` identity -/

theorem packLanes_eq_zero_iff {w : Nat} (l : List (BitVec w)) :
    packLanes l = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil =>
      rw [packLanes]
      constructor
      · intro _ x hx
        cases hx
      · intro _
        rfl
  | cons x xs ih =>
      have hmul : 2 ^ w * packLanes xs = 0 ↔ packLanes xs = 0 := by
        rw [Nat.mul_eq_zero]
        constructor
        · rintro (h2 | h0)
          · exact absurd h2 (by have := Nat.two_pow_pos w; omega)
          · exact h0
        · intro h0
          exact Or.inr h0
      rw [packLanes, Nat.add_eq_zero_iff, hmul, ih, List.forall_mem_cons]
      constructor
      · rintro ⟨hx, hxs⟩
        refine ⟨?_, hxs⟩
        apply BitVec.toNat_inj.mp
        rw [hx]
        simp
      · rintro ⟨hx, hxs⟩
        exact ⟨by rw [hx]; simp, hxs⟩

theorem packLanes_eq_zero_iff_all {w : Nat} (l : List (BitVec w)) :
    packLanes l = 0 ↔ l.all (fun x => decide (x = 0)) = true := by
  rw [packLanes_eq_zero_iff, List.all_eq_true]
  exact ⟨fun hh x hx => decide_eq_true (hh x hx), fun hh x hx => of_decide_eq_true (hh x hx)⟩

theorem zipWith_zero_right {α : Type} (op : α → α → α) (z : α) (l : List α) {n : Nat}
    (hz : ∀ x, op x z = x) (h : l.length = n) :
    List.zipWith op l (List.replicate n z) = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ m =>
          rw [List.replicate_succ, List.zipWith_cons_cons, hz x,
            ih (n := m) (by simpa using h)]

/-! #### The `i8` facts -/

theorem getLsbD_seven_iff (b : BitVec 8) : b.getLsbD 7 = true ↔ 0x80 ≤ b.toNat := by
  have hbit : b.getLsbD 7 = decide (b.toNat / 2 ^ 7 % 2 = 1) := by
    show b.toNat.testBit 7 = _
    exact Nat.testBit_eq_decide_div_mod_eq
  have hq : b.toNat / 2 ^ 7 < 2 := by
    have h255le : b.toNat ≤ 255 := by have := b.isLt; omega
    have hle : b.toNat / 2 ^ 7 ≤ 255 / 2 ^ 7 := Nat.div_le_div_right h255le
    have h255 : 255 / 2 ^ 7 = 1 := by decide
    omega
  rw [hbit, decide_eq_true_iff, Nat.mod_eq_of_lt hq]
  constructor
  · intro hh
    have hx : 128 * (b.toNat / 128) + b.toNat % 128 = b.toNat :=
      Nat.div_add_mod b.toNat 128
    omega
  · intro hh
    have hdiv : 1 ≤ b.toNat / 2 ^ 7 := by
      have := Nat.div_le_div_right (c := 2 ^ 7) hh
      have h1 : 0x80 / 2 ^ 7 = 1 := by decide
      omega
    omega

theorem getLsbD_seven_false_iff (b : BitVec 8) : b.getLsbD 7 = false ↔ b.toNat < 0x80 := by
  have h := getLsbD_seven_iff b
  constructor
  · intro hf
    have hnt : ¬ 0x80 ≤ b.toNat := by
      intro hge
      have ht : b.getLsbD 7 = true := h.mpr hge
      rw [hf] at ht
      exact absurd ht (by simp)
    omega
  · intro hlt
    have : ¬ 0x80 ≤ b.toNat := by omega
    cases hv : b.getLsbD 7 with
    | false => rfl
    | true => exact absurd (h.mp hv) this

theorem getLsbD_highBit (i : Nat) : (0x80 : BitVec 8).getLsbD i = decide (i = 7) := by
  have htoNat : (0x80 : BitVec 8).toNat = 128 := by decide
  have h128 : (128 : Nat) = 2 ^ 7 := by decide
  by_cases hi : i = 7
  · subst hi
    rw [BitVec.getLsbD, htoNat, h128, Nat.testBit_two_pow_self]
    rfl
  · rw [BitVec.getLsbD, htoNat, h128, Nat.testBit_two_pow, decide_eq_false (by omega),
      decide_eq_false hi]

theorem and80_eq_zero_iff (b : BitVec 8) : (b &&& 0x80 = 0) ↔ b.getLsbD 7 = false := by
  constructor
  · intro hh
    have hb := congrArg (fun y => y.getLsbD 7) hh
    simpa [BitVec.getLsbD_and, getLsbD_highBit] using hb
  · intro hh
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    by_cases hi : i = 7
    · subst hi
      rw [BitVec.getLsbD_and, getLsbD_highBit, decide_eq_true rfl, hh]
      simp
    · rw [BitVec.getLsbD_and, getLsbD_highBit, decide_eq_false hi]
      simp

theorem and80_eq_zero_iff_lt (b : BitVec 8) : (b &&& 0x80 = 0) ↔ b.toNat < 0x80 := by
  rw [and80_eq_zero_iff, getLsbD_seven_false_iff]

/-! #### Controls -/

theorem packLanes_zipWith_or_control :
    packLanes (List.zipWith (· ||| ·) [(0xFF : BitVec 8)] [(0xFF : BitVec 8), (0xFF : BitVec 8)])
      ≠ packLanes [(0xFF : BitVec 8)] ||| packLanes [(0xFF : BitVec 8), (0xFF : BitVec 8)] := by
  decide

theorem foldl_or_getLsbD_control :
    ([(0x00 : BitVec 8), (0xFF : BitVec 8)].foldl (· ||| ·) 0x00).getLsbD 0
      ≠ ([(0x00 : BitVec 8), (0xFF : BitVec 8)].foldl (· &&& ·) 0xFF).getLsbD 0 := by
  decide

theorem packLanes_eq_zero_iff_control :
    ¬ (packLanes [(0x01 : BitVec 8)] = 0 ↔
        [(0x01 : BitVec 8)].all (fun x => decide (x.getLsbD 7 = false)) = true) := by
  decide

theorem and80_eq_zero_iff_control :
    ¬ ((0x100 : BitVec 16) &&& 0x80 = 0 ↔ (0x100 : BitVec 16).toNat < 0x80) := by
  decide

/-! #### The disjoint-lane sum

A body's packed word is a sum of bit fields, and a specification's bytes are the
same fields read back, so the step that crosses between them is "a lane set in
exactly one operand contributes itself to the sum".  The toolchain has the
bitwise operations but no lemma relating `|||` to `+` on disjoint operands — the
names a consumer reaches for, `Nat.lor_eq_add_of_and_eq_zero` and its
neighbours, are undeclared.  So the fact is proved here, in `Nat`'s own namespace
under the name the consumer asks for, because it is lane arithmetic: the or of
disjoint fields is their sum, which is what a packed word and a lane list both
need, and which is why it belongs beside the packing distribution above rather
than in the one consumer that first needs it.  Enumeration is not an alternative
at the widths involved: the width-by-width `decide` is exponential — measured at
2m42s for sixteen bits and past this repository's probe bound at twenty-four — so
the bitwise recursion below is the route. -/
end LeanLLVM.Vellum.BitLanes

namespace Nat

/-- Set bits in disjoint masks add: when `a` and `b` share no set bit, `a ||| b`
is `a + b`.  The toolchain declares neither this lemma nor a neighbour of it, and
a consumer cannot enumerate its way to it, so it is proved once here for every
width.  The proof peels the low bit of each operand — `Nat.and_div_two` and
`Nat.or_div_two` carry the halves, the strong induction adds them, and
`Nat.and_mod_two_eq_one`/`Nat.or_mod_two_eq_one` read the low bit — so it carries
only `[propext, Quot.sound]`, the module's ceiling. -/
theorem lor_eq_add_of_and_eq_zero (a b : Nat) (h : a &&& b = 0) : a ||| b = a + b := by
  suffices ∀ n, ∀ a b : Nat, a + b = n → a &&& b = 0 → a ||| b = a + b by
    exact this (a + b) a b rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b hn h
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · simp
    · simp
    · have hlt : (a + 1) / 2 + (b + 1) / 2 < n := by
        have h1 : (a + 1) / 2 < a + 1 := Nat.div_lt_self (Nat.succ_pos a) (by decide)
        have h2 : (b + 1) / 2 < b + 1 := Nat.div_lt_self (Nat.succ_pos b) (by decide)
        omega
      have hland : (a + 1) / 2 &&& (b + 1) / 2 = 0 := by
        have hd := Nat.and_div_two (a := a + 1) (b := b + 1)
        rw [h] at hd
        simpa using hd.symm
      have hsum : (a + 1) / 2 ||| (b + 1) / 2 = (a + 1) / 2 + (b + 1) / 2 :=
        ih ((a + 1) / 2 + (b + 1) / 2) hlt ((a + 1) / 2) ((b + 1) / 2) rfl hland
      have hordiv : ((a + 1) ||| (b + 1)) / 2 = (a + 1) / 2 + (b + 1) / 2 := by
        rw [Nat.or_div_two, hsum]
      have hne : ¬ ((a + 1) % 2 = 1 ∧ (b + 1) % 2 = 1) := by
        intro hc
        have hm : ((a + 1) &&& (b + 1)) % 2 = 1 := Nat.and_mod_two_eq_one.mpr hc
        rw [h] at hm
        simp at hm
      have hr : ((a + 1) ||| (b + 1)) % 2 = (a + 1) % 2 + (b + 1) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one (a + 1) with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one (b + 1) with hb | hb
        · have hzero : ¬ (((a + 1) ||| (b + 1)) % 2 = 1) := by
            rw [Nat.or_mod_two_eq_one]
            omega
          rcases Nat.mod_two_eq_zero_or_one ((a + 1) ||| (b + 1)) with hz | ho
          · omega
          · exact absurd ho hzero
        · have hone : ((a + 1) ||| (b + 1)) % 2 = 1 :=
            Nat.or_mod_two_eq_one.mpr (Or.inr hb)
          omega
        · have hone : ((a + 1) ||| (b + 1)) % 2 = 1 :=
            Nat.or_mod_two_eq_one.mpr (Or.inl ha)
          omega
        · exact absurd ⟨ha, hb⟩ hne
      have hx : 2 * (((a + 1) ||| (b + 1)) / 2) + ((a + 1) ||| (b + 1)) % 2 =
          (a + 1) ||| (b + 1) := Nat.div_add_mod _ _
      rw [hordiv, hr] at hx
      have h1 : 2 * ((a + 1) / 2) + (a + 1) % 2 = a + 1 := Nat.div_add_mod _ _
      have h2 : 2 * ((b + 1) / 2) + (b + 1) % 2 = b + 1 := Nat.div_add_mod _ _
      omega

/-- info: 'Nat.lor_eq_add_of_and_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lor_eq_add_of_and_eq_zero

/-- The disjointness hypothesis is load-bearing: overlapping masks do not add. -/
theorem lor_eq_add_of_and_eq_zero_control :
    (0xFF : Nat) ||| 0xFF ≠ 0xFF + 0xFF := by decide

end Nat
