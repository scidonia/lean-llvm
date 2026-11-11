/-
The index kernel's escape arithmetic, in the specification's own masks.

`JsonScanSpec` writes the classifier's interface down in lane vocabulary: the raw
quote lanes, the escape mask, the delimiter lanes, and the unescaped-quote mask
`quoteMask` — the raw quote lanes whose escape-run parity is even.  It records as
owed that nothing there relates those definitions to the `pext`/`pdep` lane moves
the kernel emits for them (`tests/v16/ci2.ll`).  This module closes that gap *for
the arithmetic*: the sequence those instructions form is transcribed here, lane by
lane, and proved equal to the specification's masks.  For the extracted stage-1
mask unit the transcribed arithmetic is also tied to emitted text: the body
`LeanLLVM/Refinement/JsonS1MasksIR.lean` pins stores `kernelEscape`'s word and feeds
`kernelQuote64` and `ppn64`, and `s1_masks_refines`
(`LeanLLVM/Refinement/JsonS1MasksSteps.lean`) turns that into the mask the body
leaves.  For `@ci2` itself it is a transcription and not a model of the file — the
body it names is not parsed anywhere in the library, and nothing here reaches
`@ci2`; both limits are in "What is not proved" below, next to the lane
conventions the transcription reads.

## The kernel's escape arithmetic

The kernel never asks whether a lane holds a quote while it computes escapes.  It
asks about **backslash runs**, and it produces the escape mask from lane moves
alone:

    starts = (bs & ~((bs << 1) | o)) | (bs & o)         -- one lane per run, at its first
    last   = bs & ~(bs >> 1)                            -- one lane per run, at its last
    after  = last << 1                                  -- the lane after each run
    alt    = 0x5555… ^ (o & ppar)                       -- even lanes, flipped if the
                                                         -- incoming run is odd
    sec    = pext alt starts                            -- each run's start parity
    lec    = pext 0x5555… last                          -- each run's end parity
    nr     = ~(sec ^ lec)                               -- each run's length parity
    esc    = pdep nr after | (o & ~bs0 & ppar)          -- scatter onto the lanes
                                                         -- after the runs
    qm     = qraw & ~esc                                -- the unescaped quote lanes

`startPara`/`endPara`/`oddRuns`/`escapedRuns`/`kernelEscape` are those
expressions, and `kernelQuote` is the last line.  `evenLanes` is the kernel's
`0x5555555555555555` and `oneLane` its one-bit words `%open` and `%ppar`.

## What is proved

* `runStarts_getLsbD` and `runEnds_getLsbD` — the two masks' lanes: a run starts
  at a backslash whose predecessor in the cell is not one (or at lane zero), and
  ends at a backslash whose successor is not one.  `runStarts`'s lane does not
  depend on the run-open bit, which is why the kernel's `| (bs & o)` is invisible
  here.
* `startsUpTo_end` — **the run count invariant**: up to a lane, the number of run
  starts equals the number of run ends plus one exactly when that lane is a
  backslash.  This is the fact that pairs a run's start with its end, and every
  gather/scatter index below rests on it.
* `kernelEscape_eq` — **the escape mask is the parity mask on the lanes that are
  not backslashes**: `kernelEscape bs o p = escapeLanes bs o p &&& ~~~bs`.  The
  kernel's mask is narrower than the parity mask — it leaves a run's interior
  lanes clear, where the parity mask is set — and the identity says exactly which
  narrowing it is.
* `kernelQuote_eq` — **the mask algebra**: `qraw & ~esc` is `qraw & ~parity`,
  because no byte is both a quote and a backslash.
* `kernelQuote64` — **the derivation**: over a sixty-four-lane block, the kernel's
  `%qmc2 = %qrawc2 & ~%escc2` *is* `JsonScanSpec`'s `specQuote64`.
* `oddRun_lo` and `oddRun_hi` — the bridges the last two need: the `classStep`
  fold's `oddRun` at a lane of either half is this module's `runParityBefore`.
* `lzParity_eq_suffixRun`, `parity_top`, `nextParity_eq` and `ppn64` — the kernel's
  outgoing parity `%ppnc2`, which it takes from `ctlz(~bs) & 1` and the
  all-ones/run-open correction, is the `oddRun` the specification's `classStep` fold
  leaves after the block.
* `nextParity_and_not_top`, `nextParity_ne_zero_imp_open`, `specCarry_hypothesis`
  and `classState_self_open` — the hypothesis the derivation carries is an
  invariant of **both** sides, not a restriction on the specification; see below.

## What is not proved (owed)

* **The transcription.**  Every mask this module defines is a hand transcription of
  `tests/v16/ci2.ll`'s `@ci2` body — the `%qc20s` … `%qmc2` instructions, in the
  order the file writes them.  Nothing in the library parses that file into an AST:
  `tests/v16/ci2.ll` is exercised only as *text*, by the refusal census
  (`probes/census/repo-corpus.manifest` lists it `parsed`), and — unlike
  `JsonClassifyIR` and `DepthCountRefine`, whose fixtures are `include_str`'d and
  whose parsed ASTs are pinned by a `#guard` — no fixture is read here and no AST is
  pinned.  Nothing below therefore relates `kernelEscape`, `kernelQuote` or
  `nextParity`, or the registers they are named after, to the emitted body: a
  diverging transcription would leave every statement below true and would leave
  what they say about `@ci2` unchanged, which is nothing.
* **The lane conventions the transcription reads.**  Two conventions are what the
  definitions *mean* by the registers, not theorems about the instructions: that
  `bitcast <32 x i1> %… to i32` puts lane 0 in bit 0 — inherited from
  `JsonScanSpec.pack32_eq_bitcast`, which proves the packing used here *is* that
  bitcast, so it is assumed once and not twice — and that
  `%qhic2 = shl i64 %qhi0c2, 32` with `or` joins the halves low-then-high, which is
  `JsonScanSpec.mask64`'s definition.  A different bit order in the emitted code
  would make them false about it and change nothing here.
* **Any relation to the emitted IR**, for `@ci2`.  `Pclmul`, which states the same
  of the in-string identity: no theorem in either module mentions *that* body's
  registers, or states a refinement about it.  The extracted stage-1 mask unit is
  the exception and is proved elsewhere: `escapedWord_eq_kernelEscape`,
  `s1_backslash_eq` and `s1_inString`
  (`LeanLLVM/Refinement/JsonS1MasksSteps.lean`) read these definitions at the emitted
  body's own words, and `s1_masks_refines` turns them into the masks that body
  stores — so the arithmetic here is tied to text for that unit, and remains
  arithmetic alone for `@ci2`.

## The hypothesis, and why it restricts nothing

The kernel's `open` (its previous block ended in a backslash) is not a field of
`ClassState`, and its escape arithmetic reads it in three places: the run-open term
of `%startsc2`, `alt`'s lane-zero flip and the boundary lane of `esc`.  The two sides
agree under

    st.oddRun = (o && ppar)

— the parity is nonzero only if a run is open.  That is not an extra assumption on
either side's states, and each side says so in its own terms:

* **The kernel keeps it.**  `nextParity_and_not_top` confines `%ppnc2` to `%topc2`,
  and `nextParity_ne_zero_imp_open` reads the consequence: a nonzero outgoing parity
  implies the block's last lane is a backslash — which is what `%openn = %topc2`
  hands the next block as its run-open bit.  Every state the loop enters therefore
  satisfies the equation, by the body's own arithmetic.
* **The specification keeps it.**  `classStep_oddRun_gated` gates the fold's parity
  on the byte it reads, so `specCarry_hypothesis` gives the equation — with the
  run-open bit read from the window's bytes as `byteOpen` — for every state the fold
  reaches from a parity-false seed: a nonzero parity *is* an open run there.
  `classState_self_open` is the degenerate instance `(o, ppar) = (oddRun, oddRun)`,
  which any `ClassState` satisfies.

What differs between the two sides is the *seed*: `runParityBefore` starts from
`o && ppar` and the fold starts from `st.oddRun`, and the equation is what makes them
the same.  A state with `st.oddRun = true` reached without a run open would be read
differently at the seed — which is what the module's negative witness executes — and
neither side can be in one.
-/
import LeanLLVM.Refinement.BitLanes
import LeanLLVM.Refinement.JsonScanSpec

namespace LeanLLVM.Refinement.QuoteDerive

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonScanSpec

/-! ### One-bit words and the even lanes -/

/-- A one-bit word: lane zero carries `b` when the word has a lane zero.  This is
the kernel's `%open`, `%ppar`, `%flipc2` and `%b0bitc2`. -/
def oneLane (w : Nat) (b : Bool) : BitVec w :=
  if b then 1#w else 0#w

/-- Lane `k` of a one-bit word. -/
theorem oneLane_getLsbD {w : Nat} (b : Bool) {k : Nat} (hk : k < w) :
    (oneLane w b).getLsbD k = (decide (k = 0) && b) := by
  cases b
  · rw [oneLane, ite_eq_right (by simp), BitVec.getLsbD_zero]
    simp
  · rw [oneLane, ite_eq_left rfl, BitVec.getLsbD_one,
      show decide (0 < w) = true from decide_eq_true (by omega), Bool.true_and,
      Bool.and_true]

/-- The even lanes: the kernel's `0x5555555555555555`. -/
def evenLanes (w : Nat) : BitVec w := ofLanes (fun i => i.val % 2 == 0)

/-- Lane `k` of the even lanes is the test that `k` is even. -/
theorem evenLanes_getLsbD {w : Nat} {k : Nat} (hk : k < w) :
    (evenLanes w).getLsbD k = (k % 2 == 0) :=
  ofLanes_getLsbD (fun i => i.val % 2 == 0) hk

/-! ### The kernel's mask expressions

Each definition below is one instruction of the kernel's escape arithmetic, named
after the register it fills. -/

/-- `%opbc2`: the backslash mask shifted up, with the incoming run-open bit in
lane zero. -/
def openedBackslashes {w : Nat} (bs : BitVec w) (runOpen : Bool) : BitVec w :=
  (bs <<< 1) ||| oneLane w runOpen

/-- `%startsc2`: one lane per backslash run, at the run's first lane.  The
`& open` term is `%fakec2`: it keeps lane zero a run start when the previous block
ends in a backslash, so that every run has exactly one start lane. -/
def runStarts {w : Nat} (bs : BitVec w) (runOpen : Bool) : BitVec w :=
  (bs &&& ~~~(openedBackslashes bs runOpen)) ||| (bs &&& oneLane w runOpen)

/-- `%lastsc2`: one lane per backslash run, at the run's last lane. -/
def runEnds {w : Nat} (bs : BitVec w) : BitVec w :=
  bs &&& ~~~(bs >>> 1)

/-- `%afterc2`: one lane per backslash run, at the lane after its last. -/
def afterRuns {w : Nat} (bs : BitVec w) : BitVec w :=
  runEnds bs <<< 1

/-- `%altc2`: the even lanes, flipped at lane zero when the incoming run is odd. -/
def altLanes (w : Nat) (runOpen ppar : Bool) : BitVec w :=
  evenLanes w ^^^ oneLane w (runOpen && ppar)

/-- `%sec2`: each run's start parity, gathered onto the run index. -/
def startPara {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  pext (altLanes w runOpen ppar) (runStarts bs runOpen)

/-- `%lec2`: each run's end parity, gathered onto the run index. -/
def endPara {w : Nat} (bs : BitVec w) : BitVec w :=
  pext (evenLanes w) (runEnds bs)

/-- `%nrc2`: the runs whose backslash count is odd. -/
def oddRuns {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  ~~~(startPara bs runOpen ppar ^^^ endPara bs)

/-- `%escmc2`: that run parity, scattered back onto the lanes after the runs. -/
def escapedRuns {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  pdep (oddRuns bs runOpen ppar) (afterRuns bs)

/-- `%b0bitc2`: lane zero is escaped when the previous block left an odd run. -/
def boundaryEscape {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  oneLane w (runOpen && !(bs.getLsbD 0) && ppar)

/-- `%escc2`: the kernel's escape mask. -/
def kernelEscape {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  escapedRuns bs runOpen ppar ||| boundaryEscape bs runOpen ppar

/-- `%qmc2`: the kernel's unescaped-quote mask, `%qrawc2 & ~%escc2`. -/
def kernelQuote {w : Nat} (qraw bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  qraw &&& ~~~(kernelEscape bs runOpen ppar)

/-! ### The specification's parity, lane by lane

The classification rule `classStep` toggles its run parity on every backslash and
clears it otherwise; `runParityBefore` is that rule read at one lane, and
`escapeLanes` is the mask of lanes whose preceding run is odd. -/

/-- The parity of the backslash run immediately before a lane, with the incoming
run's parity as the seed. -/
def runParityBefore {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : Nat → Bool
  | 0 => runOpen && ppar
  | k + 1 => if bs.getLsbD k then !(runParityBefore bs runOpen ppar k) else false

/-- The lanes immediately preceded by an odd backslash run. -/
def escapeLanes {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  ofLanes (fun i => runParityBefore bs runOpen ppar i.val)

/-- Lane `k` of the parity mask. -/
theorem escapeLanes_getLsbD {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {k : Nat}
    (hk : k < w) :
    (escapeLanes bs runOpen ppar).getLsbD k = runParityBefore bs runOpen ppar k :=
  ofLanes_getLsbD (fun i => runParityBefore bs runOpen ppar i.val) hk

/-! ### The run-start and run-end lanes

The two masks decide a lane from that lane and one neighbour, and the start
decision does not read `open`: lane zero is a start exactly when it is a
backslash, because `%fakec2` supplies what `%opbc2` took away. -/

/-- The run-start decision at a lane. -/
def startLane {w : Nat} (bs : BitVec w) (s : Nat) : Bool :=
  bs.getLsbD s && (decide (s = 0) || !bs.getLsbD (s - 1))

/-- The run-end decision at a lane. -/
def endLane {w : Nat} (bs : BitVec w) (e : Nat) : Bool :=
  bs.getLsbD e && !bs.getLsbD (e + 1)

/-- Lane `k` of `%startsc2`. -/
theorem runStarts_getLsbD {w : Nat} (bs : BitVec w) (runOpen : Bool) {k : Nat}
    (hk : k < w) :
    (runStarts bs runOpen).getLsbD k = startLane bs k := by
  have hlt : decide (k < w) = true := decide_eq_true hk
  unfold runStarts openedBackslashes startLane
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and, getLsbD_not_of_lt _ hk,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, oneLane_getLsbD runOpen hk, hlt]
  cases k with
  | zero => cases hb : bs.getLsbD 0 <;> cases hg : runOpen <;> simp
  | succ k => simp

/-- Lane `k` of `%lastsc2`. -/
theorem runEnds_getLsbD {w : Nat} (bs : BitVec w) {k : Nat} (hk : k < w) :
    (runEnds bs).getLsbD k = endLane bs k := by
  unfold runEnds endLane
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hk, BitVec.getLsbD_ushiftRight,
    show 1 + k = k + 1 from by omega]

/-- Lane `k` of `%afterc2`: a run ends one lane below. -/
theorem afterRuns_getLsbD {w : Nat} (bs : BitVec w) {k : Nat} (hk : k < w) :
    (afterRuns bs).getLsbD k = (decide (1 ≤ k) && endLane bs (k - 1)) := by
  unfold afterRuns
  rw [BitVec.getLsbD_shiftLeft, show decide (k < w) = true from decide_eq_true hk,
    Bool.true_and]
  cases k with
  | zero => simp
  | succ k =>
    have hk1 : decide (k + 1 < 1) = false := decide_eq_false (by omega)
    rw [hk1, Bool.not_false, Bool.true_and, show k + 1 - 1 = k from by omega]
    rw [show decide (1 ≤ k + 1) = true from decide_eq_true (by omega), Bool.true_and]
    exact runEnds_getLsbD bs (k := k) (by omega)

/-! ### Counting set lanes below a bound

`BitLanes.rank` counts a mask's set lanes below a lane, as a filter over the
mask's own lane list.  Every induction below instead runs over `List.range`, so
the counts here are written that way and `countBelow_eq_rank` is the bridge: the
two agree below the word's width, and the range form's boundary step is
`List.range_succ`. -/

/-- The mask's set lanes below a bound, counted. -/
def countBelow {w : Nat} (m : BitVec w) (n : Nat) : Nat :=
  ((List.range n).filter (fun e => m.getLsbD e)).length

/-- One lane added at the top of the bound. -/
theorem countBelow_succ {w : Nat} (m : BitVec w) (n : Nat) :
    countBelow m (n + 1) = countBelow m n + (if m.getLsbD n then 1 else 0) := by
  unfold countBelow
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  cases h : m.getLsbD n <;> simp [h]

/-- The count does not decrease as the bound rises. -/
theorem countBelow_mono {w : Nat} (m : BitVec w) {a b : Nat} (h : a ≤ b) :
    countBelow m a ≤ countBelow m b := by
  induction b with
  | zero =>
    have haz : a = 0 := by omega
    subst haz
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · have hrec := ih hab
      rw [countBelow_succ]
      split <;> omega
    · have haz : a = b + 1 := by omega
      subst haz
      exact Nat.le_refl _

/-- A one-element list filters to one element or to none. -/
theorem filter_singleton_length (n : Nat) (p : Nat → Bool) :
    ([n].filter p).length = (if p n then 1 else 0) := by
  cases h : p n <;> simp [h]

/-- Filtering by an always-true test changes nothing. -/
theorem filter_true_eq (l : List Nat) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.filter_cons, ite_eq_left rfl, ih]

/-- The lanes below `n` are the first `n` lanes. -/
theorem range_filter_lt {w n : Nat} (hn : n ≤ w) :
    (List.range w).filter (fun s => decide (s < n)) = List.range n := by
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [List.range_add, List.filter_append]
  have h1 : (List.range n).filter (fun s => decide (s < n)) = List.range n := by
    rw [show (List.range n).filter (fun s => decide (s < n))
        = (List.range n).filter (fun _ => true) from
      List.filter_congr (fun a ha => by
        rw [decide_eq_true_eq]
        exact List.mem_range.mp ha)]
    exact filter_true_eq _
  have h2 : ((List.range k).map (n + ·)).filter (fun s => decide (s < n)) = [] := by
    refine filter_eq_nil_of_all_false (fun a ha => ?_)
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [decide_eq_false_iff_not]
    omega
  rw [h1, h2, List.append_nil]

/-- The mask's lanes below a bound, read over the mask's own lane list. -/
theorem range_filter_and_lt {w n : Nat} (p : Nat → Bool) (hn : n ≤ w) :
    (List.range w).filter (fun s => p s && decide (s < n)) = (List.range n).filter p := by
  rw [← List.filter_filter (p := p) (q := fun s => decide (s < n)), range_filter_lt hn]

/-- **The count below a bound is the mask's rank.** -/
theorem countBelow_eq_rank {w : Nat} (m : BitVec w) {n : Nat} (hn : n ≤ w) :
    countBelow m n = rank m n := by
  unfold countBelow rank setLanes
  rw [List.filter_filter (p := fun a => decide (a < n)) (q := fun a => m.getLsbD a),
    List.filter_congr (p := fun a => decide (a < n) && m.getLsbD a)
      (q := fun a => m.getLsbD a && decide (a < n)) (fun a _ => Bool.and_comm ..),
    range_filter_and_lt (fun a => m.getLsbD a) hn]

/-- Filtering a mapped list maps the filtered preimage. -/
theorem filter_map_eq {α : Type} (l : List Nat) (f : Nat → α) (p : α → Bool) :
    (l.map f).filter p = (l.filter (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons]
    by_cases h : p (f a) = true
    · rw [List.filter_cons, ite_eq_left h, List.filter_cons, ite_eq_left h, List.map_cons, ih]
    · rw [List.filter_cons, ite_eq_right h, List.filter_cons, ite_eq_right h, ih]

/-- **The after-run mask's rank is the run-end count one lane lower**: shifting a
mask up moves every lane up by one, so the lanes below `i` are the lanes below
`i - 1` of the unshifted mask. -/
theorem countBelow_shift {w : Nat} (m : BitVec w) :
    ∀ i, i ≤ w → countBelow (m <<< 1) i = countBelow m (i - 1)
  | 0, _ => by simp [countBelow]
  | i + 1, h => by
    unfold countBelow
    rw [List.range_succ_eq_map, List.filter_cons]
    have h0 : ¬ ((m <<< 1).getLsbD 0 = true) := by
      rw [BitVec.getLsbD_shiftLeft]
      simp
    rw [ite_eq_right h0]
    have hpred : (List.map Nat.succ (List.range i)).filter (fun a => (m <<< 1).getLsbD a)
        = (List.map Nat.succ (List.range i)).filter (fun a => m.getLsbD (a - 1)) := by
      refine List.filter_congr (fun a ha => ?_)
      rw [List.mem_map] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      have hkw : k + 1 < w := by
        have := List.mem_range.mp hk
        omega
      rw [BitVec.getLsbD_shiftLeft,
        show decide (k + 1 < w) = true from decide_eq_true hkw,
        show decide (k + 1 < 1) = false from decide_eq_false (by omega),
        Bool.not_false, Bool.true_and, show k + 1 - 1 = k from by omega, Bool.true_and]
    rw [hpred, filter_map_eq (List.range i) Nat.succ (fun a => m.getLsbD (a - 1)),
      List.filter_congr (p := fun k => m.getLsbD (k + 1 - 1)) (q := fun k => m.getLsbD k)
        (fun k _ => by rw [show k + 1 - 1 = k from by omega]),
      List.length_map]
    rw [show i + 1 - 1 = i from by omega]

/-! ### The run counts

`startsBelow` and `endsBelow` are the two counts the pairing rests on, each a
`countBelow` of one of the kernel's masks, so `countBelow_eq_rank` makes them
`rank`s of those masks. -/

/-- How many run starts lie below a lane. -/
def startsBelow {w : Nat} (bs : BitVec w) (runOpen : Bool) (n : Nat) : Nat :=
  countBelow (runStarts bs runOpen) n

/-- How many run ends lie below a lane. -/
def endsBelow {w : Nat} (bs : BitVec w) (n : Nat) : Nat :=
  countBelow (runEnds bs) n

/-- The run starts below a lane, counted through the mask's lane decision. -/
theorem startsBelow_succ {w : Nat} (bs : BitVec w) (runOpen : Bool) {n : Nat} (hn : n < w) :
    startsBelow bs runOpen (n + 1)
      = startsBelow bs runOpen n + (if startLane bs n then 1 else 0) := by
  unfold startsBelow
  rw [countBelow_succ, runStarts_getLsbD bs runOpen hn]

/-- The run ends below a lane, counted through the mask's lane decision. -/
theorem endsBelow_succ {w : Nat} (bs : BitVec w) {n : Nat} (hn : n < w) :
    endsBelow bs (n + 1) = endsBelow bs n + (if endLane bs n then 1 else 0) := by
  unfold endsBelow
  rw [countBelow_succ, runEnds_getLsbD bs hn]

/-- **The run count invariant.**  Up to a lane, a backslash mask has one more run
start than run ends exactly at the lanes that are backslashes: every run is
entered once and left once, and a lane inside a run has been entered but not yet
left.  This is the correspondence a gather/scatter pairing needs. -/
theorem startsUpTo_end {w : Nat} (bs : BitVec w) (runOpen : Bool) :
    ∀ K, K < w →
      startsBelow bs runOpen (K + 1) = endsBelow bs K + (if bs.getLsbD K then 1 else 0)
  | 0, h => by
    rw [startsBelow_succ bs runOpen (Nat.zero_lt_of_lt h), endsBelow]
    have hzero : countBelow (runEnds bs) 0 = 0 := by simp [countBelow]
    rw [hzero, Nat.zero_add]
    have hstart : startLane bs 0 = bs.getLsbD 0 := by
      unfold startLane
      rw [show decide ((0 : Nat) = 0) = true from rfl, Bool.true_or]
      simp
    rw [hstart]
    have hbase : startsBelow bs runOpen 0 = 0 := by simp [startsBelow, countBelow]
    rw [hbase, Nat.zero_add]
  | K + 1, h => by
    rw [startsBelow_succ bs runOpen (by omega), endsBelow_succ bs (by omega),
      startsUpTo_end bs runOpen K (by omega)]
    unfold startLane endLane
    rw [show decide ((K : Nat) + 1 = 0) = false from decide_eq_false (by omega)]
    cases hk : bs.getLsbD K <;> cases hk1 : bs.getLsbD (K + 1) <;>
      simp [hk, show K + 1 - 1 = K from by omega]

/-- The starts counted to the end of the word. -/
theorem startsBelow_top {w : Nat} (bs : BitVec w) (runOpen : Bool) :
    startsBelow bs runOpen w = countBelow (runStarts bs runOpen) w := rfl

/-! ### Rank forms of the run counts -/

/-- The run starts below a lane, as the start mask's rank. -/
theorem rank_runStarts {w : Nat} (bs : BitVec w) (runOpen : Bool) {n : Nat} (hn : n ≤ w) :
    rank (runStarts bs runOpen) n = startsBelow bs runOpen n :=
  (countBelow_eq_rank _ hn).symm

/-- The run ends below a lane, as the end mask's rank. -/
theorem rank_runEnds {w : Nat} (bs : BitVec w) {n : Nat} (hn : n ≤ w) :
    rank (runEnds bs) n = endsBelow bs n :=
  (countBelow_eq_rank _ hn).symm

/-- **The after-run mask's rank is the run-end count one lane lower.** -/
theorem rank_afterRuns {w : Nat} (bs : BitVec w) {i : Nat} (hi : i ≤ w) :
    rank (afterRuns bs) i = endsBelow bs (i - 1) := by
  rw [show afterRuns bs = runEnds bs <<< 1 from rfl,
    ← countBelow_eq_rank (runEnds bs <<< 1) hi, countBelow_shift (runEnds bs) i hi,
    countBelow_eq_rank (runEnds bs) (by omega), rank_runEnds bs (by omega)]

/-! ### The parity of a run

The kernel gathers a run's start and end *lane numbers* and reads the even-lane
word at both: the run's length parity is the difference of the two, and the
incoming run's parity flips the start when the run touches lane zero. -/

/-- The even-lane word read through a complement: a lane is even or odd. -/
theorem mod_two_eq_zero_or_one (d : Nat) : (d % 2 == 0) = !(d % 2 == 1) := by
  have h : d % 2 = 0 ∨ d % 2 = 1 := by
    have := Nat.mod_lt d (by decide : 0 < 2)
    omega
  rcases h with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

/-- The parity of a lane number alternates with the lane. -/
theorem mod_two_succ_eq_one (d : Nat) : ((d + 1) % 2 == 1) = !(d % 2 == 1) := by
  have hmod : (d + 1) % 2 = (d % 2 + 1) % 2 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by decide : 1 < 2)]
  rw [hmod]
  have h : d % 2 = 0 ∨ d % 2 = 1 := by
    have := Nat.mod_lt d (by decide : 0 < 2)
    omega
  rcases h with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

/-- The even test alternates with the lane. -/
theorem mod_two_succ_eq_zero (d : Nat) : ((d + 1) % 2 == 0) = !(d % 2 == 0) := by
  rw [mod_two_eq_zero_or_one (d + 1), mod_two_succ_eq_one, mod_two_eq_zero_or_one (d)]


/-- A negated right summand is a negated sum. -/
theorem xor_not_right (p q : Bool) : (p ^^ !q) = !(p ^^ q) := by
  cases p <;> cases q <;> rfl

/-- **A run's length parity is the difference of its endpoint parities.** -/
theorem evenXor_add (s : Nat) : ∀ d, ((s % 2 == 0) ^^ ((s + d) % 2 == 0)) = (d % 2 == 1)
  | 0 => by
    rw [Nat.add_zero, Bool.xor_self]
    rfl
  | d + 1 => by
    have hstep : (((s + (d + 1)) % 2 == 0) = !((s + d) % 2 == 0)) := by
      rw [show s + (d + 1) = (s + d) + 1 from by omega, mod_two_succ_eq_zero]
    rw [hstep, xor_not_right, evenXor_add s d, mod_two_succ_eq_one]

/-- Lane `k` of the alternation word. -/
theorem altLanes_getLsbD {w : Nat} (runOpen ppar : Bool) {k : Nat} (hk : k < w) :
    (altLanes w runOpen ppar).getLsbD k
      = ((k % 2 == 0) ^^ (decide (k = 0) && (runOpen && ppar))) := by
  unfold altLanes
  rw [BitVec.getLsbD_xor, evenLanes_getLsbD hk, oneLane_getLsbD _ hk]

/-- Lane `j` of the start-parity gather. -/
theorem startPara_getLsbD {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {j : Nat}
    (hj : j < (setLanes (runStarts bs runOpen)).length) :
    (startPara bs runOpen ppar).getLsbD j
      = (((setLanes (runStarts bs runOpen))[j] % 2 == 0)
          ^^ (decide ((setLanes (runStarts bs runOpen))[j] = 0) && (runOpen && ppar))) := by
  unfold startPara
  rw [pext_getLsbD_of_lt (a := altLanes w runOpen ppar) (m := runStarts bs runOpen) (j := j)
      (hj := hj),
    altLanes_getLsbD runOpen ppar (setLanes_getElem_lt (runStarts bs runOpen) hj)]

/-- Lane `j` of the end-parity gather. -/
theorem endPara_getLsbD {w : Nat} (bs : BitVec w) {j : Nat}
    (hj : j < (setLanes (runEnds bs)).length) :
    (endPara bs).getLsbD j = ((setLanes (runEnds bs))[j] % 2 == 0) := by
  unfold endPara
  rw [pext_getLsbD_of_lt (a := evenLanes w) (m := runEnds bs) (j := j) (hj := hj),
    evenLanes_getLsbD (setLanes_getElem_lt (runEnds bs) hj)]

/-- Lane `j` of the odd-run word. -/
theorem oddRuns_getLsbD {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {j : Nat}
    (hj : j < w) :
    (oddRuns bs runOpen ppar).getLsbD j
      = !((startPara bs runOpen ppar).getLsbD j ^^ (endPara bs).getLsbD j) := by
  unfold oddRuns
  rw [getLsbD_not_of_lt _ hj, BitVec.getLsbD_xor]

/-- Lane `i` of the scatter onto the after-run lanes. -/
theorem escapedRuns_getLsbD {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {i : Nat}
    (hi : i < w) :
    (escapedRuns bs runOpen ppar).getLsbD i
      = ((afterRuns bs).getLsbD i
          && (oddRuns bs runOpen ppar).getLsbD (rank (afterRuns bs) i)) := by
  unfold escapedRuns
  rw [pdep_getLsbD _ _ hi]

/-- Lane `k` of the boundary escape bit. -/
theorem boundaryEscape_getLsbD {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {k : Nat}
    (hk : k < w) :
    (boundaryEscape bs runOpen ppar).getLsbD k
      = (decide (k = 0) && (runOpen && !(bs.getLsbD 0) && ppar)) :=
  oneLane_getLsbD _ hk

/-! ### The parity at the start of a run

The seed `runParityBefore` reads at a run's first lane is the incoming run's
parity at lane zero and `false` anywhere else, because the lane below a start is
not a backslash. -/

theorem runParityBefore_start {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {s : Nat}
    (hstart : startLane bs s = true) :
    runParityBefore bs runOpen ppar s = (decide (s = 0) && (runOpen && ppar)) := by
  unfold startLane at hstart
  rw [Bool.and_eq_true] at hstart
  obtain ⟨hbs, hprev⟩ := hstart
  cases s with
  | zero => rfl
  | succ k =>
    have hk0 : (!bs.getLsbD k) = true := by
      rw [Bool.or_eq_true] at hprev
      rcases hprev with h | h
      · exact absurd h (by simp)
      · exact h
    have hfalse : bs.getLsbD k = false := by simpa using hk0
    rw [runParityBefore, ite_eq_right (by rw [hfalse]; simp)]
    simp

/-- **Across a run of set lanes the parity toggles once per lane.** -/
theorem runParity_iterate {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) :
    ∀ {s i : Nat}, s ≤ i → i ≤ w → (∀ k, s ≤ k → k < i → bs.getLsbD k = true) →
      runParityBefore bs runOpen ppar i
        = (runParityBefore bs runOpen ppar s ^^ ((i - s) % 2 == 1)) := by
  intro s i hsi hiw
  induction i with
  | zero =>
    intro _
    have hsz : s = 0 := by omega
    subst hsz
    simp
  | succ i ih =>
    intro hset
    rcases Nat.eq_or_lt_of_le hsi with hsi0 | hsi0
    · rw [← hsi0, Nat.sub_self]
      simp
    · have hbi : bs.getLsbD i = true := hset i (by omega) (by omega)
      have hrec : runParityBefore bs runOpen ppar i
          = (runParityBefore bs runOpen ppar s ^^ ((i - s) % 2 == 1)) :=
        ih (by omega) (by omega) (fun k hsk hki => hset k hsk (by omega))
      have hstep : runParityBefore bs runOpen ppar (i + 1)
          = !(runParityBefore bs runOpen ppar i) := by
        rw [runParityBefore, ite_eq_left hbi]
      rw [hstep, hrec, show i + 1 - s = (i - s) + 1 from by omega, mod_two_succ_eq_one]
      cases (runParityBefore bs runOpen ppar s) <;> cases (i - s) % 2 == 1 <;> rfl

/-! ### The crux: the kernel's escape mask on non-backslash lanes

At a lane that is not a backslash, the kernel's scatter lands the parity of the
run that ends one lane below, or is clear when no run ends there.  The pairing of
a run's start with its end is `startsUpTo_end`; the "all lanes of a run are set"
step is what makes the toggle count the run's length. -/

/-- A run-start lane is a backslash. -/
theorem startLane_backslash {w : Nat} (bs : BitVec w) {s : Nat} (h : startLane bs s = true) :
    bs.getLsbD s = true := by
  unfold startLane at h
  cases hb : bs.getLsbD s
  · rw [hb] at h
    simp at h
  · rfl

/-- **The escape bit at the end of a run.**  When the lanes from a run's first
lane `s` to its last lane `e` are all backslashes and `s` starts the run, the
parity of the alternation words at `s` and `e` is the run's length parity, so the
kernel's gathered value is the negation of the parity after the run. -/
theorem escape_at_run_end {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {s e : Nat}
    (he : e < w) (hse : s ≤ e) (hstart : startLane bs s = true)
    (hallset : ∀ t, s ≤ t → t ≤ e → bs.getLsbD t = true) :
    (Bool.not (((s % 2 == 0) ^^ (decide (s = 0) && (runOpen && ppar))) ^^ (e % 2 == 0)))
      = runParityBefore bs runOpen ppar (e + 1) := by
  have hpar : runParityBefore bs runOpen ppar (e + 1)
      = (runParityBefore bs runOpen ppar s ^^ (((e + 1) - s) % 2 == 1)) :=
    runParity_iterate bs runOpen ppar (by omega) (by omega)
      (fun k hsk hki => hallset k hsk (by omega))
  have hseed : runParityBefore bs runOpen ppar s
      = (decide (s = 0) && (runOpen && ppar)) :=
    runParityBefore_start bs runOpen ppar hstart
  have hstep : ((((e + 1) - s) % 2) == 1) = !(((e - s) % 2) == 1) := by
    rw [show e + 1 - s = (e - s) + 1 from by omega, mod_two_succ_eq_one]
  have hA : ((s % 2 == 0) ^^ (e % 2 == 0)) = (((e - s) % 2) == 1) := by
    have h := evenXor_add s (e - s)
    rw [show s + (e - s) = e from by omega] at h
    exact h
  rw [hpar, hseed, hstep, ← hA]
  cases (s % 2 == 0) <;> cases (decide (s = 0) && (runOpen && ppar)) <;>
    cases (e % 2 == 0) <;> rfl

theorem kernelEscape_of_clear {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {i : Nat}
    (hi : i < w) (hclear : bs.getLsbD i = false) :
    (kernelEscape bs runOpen ppar).getLsbD i = runParityBefore bs runOpen ppar i := by
  unfold kernelEscape
  rw [BitVec.getLsbD_or]
  cases i with
  | zero =>
    have hw : 0 < w := hi
    have hafter0 : (afterRuns bs).getLsbD 0 = false := by
      rw [afterRuns_getLsbD bs hw]
      simp
    rw [escapedRuns_getLsbD bs runOpen ppar hw, hafter0, Bool.false_and,
      boundaryEscape_getLsbD bs runOpen ppar hw, hclear, Bool.not_false,
      Bool.and_true, Bool.false_or, runParityBefore]
    rfl
  | succ i =>
    have hi' : i < w := by omega
    have hne : (i + 1) ≠ 0 := by omega
    have hafter : (afterRuns bs).getLsbD (i + 1) = endLane bs i := by
      rw [afterRuns_getLsbD bs (by omega)]
      rw [show decide (1 ≤ i + 1) = true from decide_eq_true (by omega), Bool.true_and,
        show i + 1 - 1 = i from by omega]
    have hbnd : (boundaryEscape bs runOpen ppar).getLsbD (i + 1) = false := by
      rw [boundaryEscape_getLsbD bs runOpen ppar (by omega)]
      rw [show decide (i + 1 = 0) = false from decide_eq_false (by omega)]
      rfl
    rw [escapedRuns_getLsbD bs runOpen ppar (by omega), hafter, hbnd, Bool.or_false]
    unfold endLane
    cases hb : bs.getLsbD i with
    | false =>
      rw [runParityBefore, hb]
      simp
    | true =>
      -- the run ends at `i`, so its end lane is the `j`-th end and its start is
      -- the `j`-th start
      obtain ⟨j, hjdef⟩ : ∃ j, endsBelow bs i = j := ⟨_, rfl⟩
      have hrankj : rank (afterRuns bs) (i + 1) = j := by
        rw [rank_afterRuns bs (by omega), show i + 1 - 1 = i from by omega, hjdef]
      rw [hclear, hrankj]
      simp only [Bool.not_false, Bool.true_and]
      have hjend : (setLanes (runEnds bs))[j]? = some i := by
        have h := setLanes_getElem?_rank (runEnds bs) hi'
          (by rw [runEnds_getLsbD bs hi']; unfold endLane; rw [hb, hclear]; rfl)
        rwa [rank_runEnds bs (by omega), hjdef] at h
      have hje : j < (setLanes (runEnds bs)).length :=
        (List.getElem?_eq_some_iff.mp hjend).1
      have hendlane : (setLanes (runEnds bs))[j] = i := by
        have h := hjend
        rw [List.getElem?_eq_getElem hje] at h
        exact Option.some.inj h
      have hinv : startsBelow bs runOpen (i + 1) = j + 1 := by
        rw [startsUpTo_end bs runOpen i hi', hb, hjdef]
        rfl
      have hjstarts : j < (setLanes (runStarts bs runOpen)).length := by
        have hle : countBelow (runStarts bs runOpen) (i + 1)
            ≤ countBelow (runStarts bs runOpen) w := countBelow_mono _ (by omega)
        have htop : countBelow (runStarts bs runOpen) w
            = (setLanes (runStarts bs runOpen)).length := rfl
        rw [htop] at hle
        have hinv' := hinv
        unfold startsBelow at hinv'
        omega
      obtain ⟨s, hsdef⟩ : ∃ s, (setLanes (runStarts bs runOpen))[j] = s := ⟨_, rfl⟩
      have hsstart : startLane bs s = true := by
        rw [← hsdef]
        have h := setLanes_getElem_true (runStarts bs runOpen) hjstarts
        rwa [runStarts_getLsbD bs runOpen (setLanes_getElem_lt _ hjstarts)] at h
      have hsbs : bs.getLsbD s = true := startLane_backslash bs hsstart
      have hrankstart : rank (runStarts bs runOpen) s = j := by
        rw [← hsdef]
        exact rank_setLanes_getElem (runStarts bs runOpen) hjstarts
      have hslt : s < i + 1 := by
        rcases Nat.lt_or_ge s (i + 1) with h | h
        · exact h
        · exfalso
          have hmono : rank (runStarts bs runOpen) (i + 1) ≤ rank (runStarts bs runOpen) s :=
            rank_mono _ h
          rw [hrankstart, rank_runStarts bs runOpen (by omega)] at hmono
          omega
      have hscount : startsBelow bs runOpen (s + 1) = j + 1 := by
        unfold startsBelow
        rw [countBelow_succ, countBelow_eq_rank (runStarts bs runOpen) (by omega),
          hrankstart, runStarts_getLsbD bs runOpen (by omega), hsstart]
        rfl
      have hsend : endsBelow bs s = j := by
        have hinv2 := startsUpTo_end bs runOpen s (by omega)
        rw [hscount, hsbs] at hinv2
        simp at hinv2
        omega
      -- every lane from the start to the end of the run is set
      have hallset : ∀ t, s ≤ t → t ≤ i → bs.getLsbD t = true := by
        intro t
        induction t using Nat.strongRecOn with
        | _ t ih =>
          intro hst hti
          rcases Nat.lt_or_ge s t with hlt | hge
          · cases hbt : bs.getLsbD t with
            | true => rfl
            | false =>
              exfalso
              have hpt : bs.getLsbD (t - 1) = true := ih (t - 1) (by omega) (by omega) (by omega)
              have hendl : endLane bs (t - 1) = true := by
                unfold endLane
                rw [show t - 1 + 1 = t from by omega, hpt, hbt]
                rfl
              have hstep : endsBelow bs t = endsBelow bs (t - 1) + 1 := by
                rw [show t = (t - 1) + 1 from by omega, endsBelow_succ bs (by omega), hendl]
                simp
              have hmono1 : endsBelow bs s ≤ endsBelow bs (t - 1) := countBelow_mono _ (by omega)
              have hmono2 : endsBelow bs t ≤ endsBelow bs i := countBelow_mono _ (by omega)
              have hendi : endsBelow bs i = j := hjdef
              omega
          · have hst' : s = t := by omega
            rw [← hst']
            exact hsbs
      have hjw : j < w := Nat.lt_of_lt_of_le hjstarts (setLanes_length_le _)
      rw [oddRuns_getLsbD bs runOpen ppar hjw, startPara_getLsbD bs runOpen ppar hjstarts,
        endPara_getLsbD bs (j := j) hje, hendlane, hsdef]
      exact escape_at_run_end bs runOpen ppar hi' (by omega) hsstart hallset

/-- The kernel's escape mask is clear at a backslash lane: the scatter only writes
the lanes after run ends and the boundary bit only writes lane zero. -/
theorem kernelEscape_of_set {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) {i : Nat}
    (hi : i < w) (hset : bs.getLsbD i = true) :
    (kernelEscape bs runOpen ppar).getLsbD i = false := by
  unfold kernelEscape
  rw [BitVec.getLsbD_or]
  have hbnd : (boundaryEscape bs runOpen ppar).getLsbD i = false := by
    rw [boundaryEscape_getLsbD bs runOpen ppar hi]
    cases i with
    | zero =>
      rw [hset]
      simp
    | succ k =>
      rw [show decide (k + 1 = 0) = false from decide_eq_false (by omega)]
      rfl
  have hrun : (escapedRuns bs runOpen ppar).getLsbD i = false := by
    rw [escapedRuns_getLsbD bs runOpen ppar hi]
    cases i with
    | zero =>
      rw [afterRuns_getLsbD bs hi]
      simp
    | succ k =>
      rw [afterRuns_getLsbD bs hi,
        show decide (1 ≤ k + 1) = true from decide_eq_true (by omega), Bool.true_and]
      unfold endLane
      rw [show k + 1 - 1 = k from by omega, hset, Bool.not_true, Bool.and_false]
      rfl
  rw [hbnd, hrun]
  rfl

/-- **The escape mask is the parity mask on the lanes that are not backslashes.**
The kernel's scatter writes only the lane after a run's end, while the parity mask
is set at every lane whose preceding run is odd — including a run's interior.  The
two agree wherever a lane is not itself a backslash. -/
theorem kernelEscape_eq {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) :
    kernelEscape bs runOpen ppar = escapeLanes bs runOpen ppar &&& ~~~bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt bs hi, escapeLanes_getLsbD bs runOpen ppar hi]
  cases hb : bs.getLsbD i with
  | false =>
    rw [Bool.not_false, Bool.and_true]
    exact kernelEscape_of_clear bs runOpen ppar hi hb
  | true =>
    rw [Bool.not_true, Bool.and_false]
    exact kernelEscape_of_set bs runOpen ppar hi hb

/-- **The derivation.**  The unescaped-quote mask the kernel computes, `%qrawc2 &
~%escc2`, is the raw quote mask with the odd-run lanes removed — and since no byte
is both a quote and a backslash, that is exactly the raw quote mask with the
parity mask removed.

The disjointness hypothesis is a fact about the two byte predicates, not a
restriction: `specQuote64_disjoint` below discharges it for the specification's
own masks. -/
theorem kernelQuote_eq {w : Nat} (qraw bs : BitVec w) (runOpen ppar : Bool)
    (hdisj : qraw &&& bs = 0#w) :
    kernelQuote qraw bs runOpen ppar = qraw &&& ~~~escapeLanes bs runOpen ppar := by
  have hq : ∀ i, i < w → ((qraw.getLsbD i && bs.getLsbD i) = false) := by
    intro i hi
    have h := congrArg (fun x : BitVec w => x.getLsbD i) hdisj
    rwa [BitVec.getLsbD_and, BitVec.getLsbD_zero] at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold kernelQuote
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hi, kernelEscape_eq bs runOpen ppar,
    BitVec.getLsbD_and, getLsbD_not_of_lt _ hi, escapeLanes_getLsbD bs runOpen ppar hi,
    BitVec.getLsbD_and, getLsbD_not_of_lt _ hi, escapeLanes_getLsbD bs runOpen ppar hi]
  cases hb : bs.getLsbD i with
  | false => simp
  | true =>
    have hqf : qraw.getLsbD i = false := by
      have h := hq i hi
      rw [hb, Bool.and_true] at h
      exact h
    rw [hqf]
    rfl

/-! ### The specification's masks against the lane recursion

`JsonScanSpec` states the classifier's masks over the bytes of a window and the
`classStep` carry; the lane recursion above is the same rule read at one lane.
The two bridges below say so: the fold's `oddRun` at a lane is `runParityBefore`,
and a lane is an escaped quote exactly when it is a quote and the run before it is
odd.  Nothing here reads the kernel's registers — the link to them is
`kernelQuote64`, below. -/

/-- A quote byte is not a backslash, so the two masks are disjoint. -/
theorem isQuoteB_and_isBackslashB (b : UInt8) : (IsQuoteB b && IsBackslashB b) = false := by
  by_cases h : b = 0x22
  · rw [h]
    decide
  · have hf : IsQuoteB b = false := by
      unfold IsQuoteB
      rw [decide_eq_false_iff_not]
      exact h
    rw [hf]
    rfl

/-- The specification's raw quote mask and backslash mask over one block are
disjoint. -/
theorem specQuote64_disjoint (lo hi : Block32) :
    specMask64 IsQuoteB lo hi &&& specMask64 IsBackslashB lo hi = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  by_cases hk32 : k < 32
  · rw [specMask64_getLsbD_lo IsQuoteB lo hi hk32,
      specMask64_getLsbD_lo IsBackslashB lo hi hk32]
    exact isQuoteB_and_isBackslashB _
  · rw [show k = (k - 32) + 32 from by omega,
      specMask64_getLsbD_hi IsQuoteB lo hi (by omega),
      specMask64_getLsbD_hi IsBackslashB lo hi (by omega)]
    exact isQuoteB_and_isBackslashB _

/-- The fold at lane zero is the incoming state. -/
theorem classCarryAt_oddRun_zero (bs : List UInt8) (st : ClassState) :
    (classCarryAt bs st 0).oddRun = st.oddRun := by
  unfold classCarryAt
  rw [List.take_zero, List.foldl_nil]

/-- **The low half's fold parity is the lane recursion**, seeded by the incoming
state. -/
theorem oddRun_lo {lo hi : Block32} {st : ClassState} {runOpen ppar : Bool}
    (hst : st.oddRun = (runOpen && ppar)) :
    ∀ k, k ≤ 32 →
      (classCarryAt (List.ofFn lo) st k).oddRun
        = runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar k
  | 0, _ => by rw [classCarryAt_oddRun_zero]; exact hst
  | k + 1, hk => by
    have hk32 : k < 32 := by omega
    have hsucc : classCarryAt (List.ofFn lo) st (k + 1)
        = classStep (classCarryAt (List.ofFn lo) st k) (lo ⟨k, hk32⟩) := by
      rw [classCarryAt_succ, List.getElem?_ofFn, dite_eq_left hk32]
    rw [hsucc]
    simp only [classStep]
    rw [runParityBefore, specMask64_getLsbD_lo IsBackslashB lo hi hk32,
      oddRun_lo hst k (by omega)]

/-- **The high half's fold parity is the lane recursion one half higher**, seeded
by the carry the low half leaves. -/
theorem oddRun_hi {lo hi : Block32} {st : ClassState} {runOpen ppar : Bool}
    (hst : st.oddRun = (runOpen && ppar)) :
    ∀ m, m ≤ 32 →
      (classCarryAt (List.ofFn hi) (classWindow (List.ofFn lo) st).carry m).oddRun
        = runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar (32 + m)
  | 0, _ => by
    have h0 : (classCarryAt (List.ofFn hi) (classWindow (List.ofFn lo) st).carry 0).oddRun
        = (classCarryAt (List.ofFn lo) st 32).oddRun := by
      rw [classCarryAt_oddRun_zero, classWindow_carry]
    rw [h0, show 32 + 0 = 32 from rfl]
    exact oddRun_lo hst 32 (by omega)
  | m + 1, hm => by
    have hm32 : m < 32 := by omega
    have hsucc : classCarryAt (List.ofFn hi) (classWindow (List.ofFn lo) st).carry (m + 1)
        = classStep (classCarryAt (List.ofFn hi) (classWindow (List.ofFn lo) st).carry m)
            (hi ⟨m, hm32⟩) := by
      rw [classCarryAt_succ, List.getElem?_ofFn, dite_eq_left hm32]
    rw [hsucc]
    simp only [classStep]
    rw [show 32 + (m + 1) = (32 + m) + 1 from by omega, runParityBefore,
      show (specMask64 IsBackslashB lo hi).getLsbD (32 + m) = IsBackslashB (hi ⟨m, hm32⟩) from by
        rw [show 32 + m = m + 32 from by omega, specMask64_getLsbD_hi IsBackslashB lo hi hm32],
      oddRun_hi hst m (by omega)]

/-- The lane recursion over the low half, as a mask. -/
def parityLo (lo hi : Block32) (runOpen ppar : Bool) : BitVec 32 :=
  ofLanes (fun i => runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar i.val)

/-- The lane recursion over the high half, as a mask. -/
def parityHi (lo hi : Block32) (runOpen ppar : Bool) : BitVec 32 :=
  ofLanes (fun i => runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar (32 + i.val))

/-- **The parity mask is the two halves the kernel joins.** -/
theorem escapeLanes_eq_join (lo hi : Block32) (runOpen ppar : Bool) :
    escapeLanes (specMask64 IsBackslashB lo hi) runOpen ppar
      = mask64 (parityLo lo hi runOpen ppar) (parityHi lo hi runOpen ppar) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hlanes : (escapeLanes (specMask64 IsBackslashB lo hi) runOpen ppar).getLsbD k
      = runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar k :=
    escapeLanes_getLsbD _ _ _ hk
  rw [hlanes]
  by_cases hk32 : k < 32
  · rw [mask64_getLsbD_lo _ _ hk32]
    exact (ofLanes_getLsbD
      (fun i => runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar i.val) hk32).symm
  · rw [show k = (k - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
      show (k - 32) + 32 = 32 + (k - 32) from by omega]
    exact (ofLanes_getLsbD
      (fun i => runParityBefore (specMask64 IsBackslashB lo hi) runOpen ppar (32 + i.val))
      (by omega)).symm

/-- **The low half's unescaped-quote mask is the raw quote mask without the odd
lanes.** -/
theorem quoteMask_lo {lo hi : Block32} {st : ClassState} {runOpen ppar : Bool}
    (hst : st.oddRun = (runOpen && ppar)) :
    quoteMask (List.ofFn lo) st
      = pack32 IsQuoteB lo &&& ~~~parityLo lo hi runOpen ppar := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hk32 : k < 32 := hk
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hk, parityLo, ofLanes_getLsbD _ hk32,
    quoteMask_getLsbD hk32 (by rw [List.getElem?_ofFn, dite_eq_left hk32]),
    pack32_getLsbD IsQuoteB lo ⟨k, hk32⟩, isUnescapedQuote, oddRun_lo hst k (by omega)]

/-- **The high half's unescaped-quote mask is the raw quote mask without the odd
lanes.** -/
theorem quoteMask_hi {lo hi : Block32} {st : ClassState} {runOpen ppar : Bool}
    (hst : st.oddRun = (runOpen && ppar)) :
    quoteMask (List.ofFn hi) (classWindow (List.ofFn lo) st).carry
      = pack32 IsQuoteB hi &&& ~~~parityHi lo hi runOpen ppar := by
  apply BitVec.eq_of_getLsbD_eq
  intro m hm
  have hm32 : m < 32 := hm
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hm, parityHi, ofLanes_getLsbD _ hm32,
    quoteMask_getLsbD hm32 (by rw [List.getElem?_ofFn, dite_eq_left hm32]),
    pack32_getLsbD IsQuoteB hi ⟨m, hm32⟩, isUnescapedQuote, oddRun_hi hst m (by omega)]

/-- **The derivation the kernel performs.**  The kernel's `%qmc2 = %qrawc2 &
~%escc2` over a sixty-four-lane block is the specification's unescaped-quote mask
for that block, under the invariant that a nonzero run parity implies an open run.

The `st.oddRun = (runOpen && ppar)` hypothesis is the kernel's own invariant, not a
restriction on `ClassState`: the kernel carries `open` as its previous block's top
lane and derives its parity from `%topc2`, so a nonzero parity implies an open run
in every state it reaches.  See the module docstring. -/
theorem kernelQuote64 (lo hi : Block32) (st : ClassState) (runOpen ppar : Bool)
    (hst : st.oddRun = (runOpen && ppar)) :
    kernelQuote (specMask64 IsQuoteB lo hi) (specMask64 IsBackslashB lo hi) runOpen ppar
      = specQuote64 lo hi st := by
  rw [kernelQuote_eq _ _ _ _ (specQuote64_disjoint lo hi), escapeLanes_eq_join]
  unfold specMask64 specQuote64 classMask64
  rw [mask64_not, mask64_and, ← quoteMask_lo hst, ← quoteMask_hi hst]

/-! ### `%lzpc2` and the outgoing run parity

The kernel takes its outgoing run parity from `ctlz(~~~bs) & 1` and an all-ones
correction: `%allonc2 = (%bsc2 == -1)`, `%keepc2 = %allonc2 & %opennzc2`,
`%contribc2 = select %keepc2, %ppar, 0`, `%ppc2 = %contribc2 ^ %lzpc2`, and
`%ppnc2 = %topc2 & %ppc2`.  The theorems below read that: the `ctlz` parity is the
trailing run's parity, the whole expression is `runParityBefore` at the block's end,
and that is the `oddRun` the specification's `classStep` fold leaves. -/

/-- A negated left summand is a negated sum. -/
theorem not_xor (p q : Bool) : ((!p) ^^ q) = !(p ^^ q) := by
  cases p <;> cases q <;> rfl

/-- Successor cancellation for the lane's rank, as `decide` equality. -/
theorem decide_succ_eq_succ (s n : Nat) : decide (s + 1 = n + 1) = decide (s = n) := by
  rw [decide_eq_decide]
  exact ⟨fun h => Nat.succ.inj h, fun h => by rw [h]⟩

/-- **The run parity at a lane is the trailing run's parity**, carrying the incoming
run's parity when the run fills the lanes counted. -/
theorem runParityBefore_eq {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) :
    ∀ n, n ≤ w →
      runParityBefore bs runOpen ppar n
        = (decide (suffixRun bs n % 2 = 1)
            ^^ (decide (suffixRun bs n = n) && (runOpen && ppar))) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [runParityBefore, suffixRun, Nat.zero_mod,
      show decide (0 = 1) = false from rfl, show decide (0 = 0) = true from rfl]
    cases runOpen <;> cases ppar <;> rfl
  | succ n ih =>
    intro hn
    have hrec : runParityBefore bs runOpen ppar (n + 1)
        = if bs.getLsbD n = true then !(runParityBefore bs runOpen ppar n) else false := by
      rw [runParityBefore]
    cases hb : bs.getLsbD n with
    | false =>
      have hzero : suffixRun bs (n + 1) = 0 := by rw [suffixRun, hb]; rfl
      rw [hrec, hzero, hb]
      rfl
    | true =>
      have hstep : suffixRun bs (n + 1) = suffixRun bs n + 1 := by rw [suffixRun, hb]; rfl
      have hmod : decide ((suffixRun bs n + 1) % 2 = 1) = !decide (suffixRun bs n % 2 = 1) :=
        mod_two_succ_eq_one (suffixRun bs n)
      rw [hrec, hb, hstep, decide_succ_eq_succ, ih (by omega), hmod, not_xor]
      rfl

/-- The trailing run fills the word exactly when every lane is set. -/
theorem suffixRun_eq_self_iff {w : Nat} (bs : BitVec w) :
    suffixRun bs w = w ↔ bs = BitVec.allOnes w := by
  constructor
  · intro h
    have hall : ∀ n, n ≤ w → suffixRun bs n = n → ∀ k, k < n → bs.getLsbD k = true := by
      intro n
      induction n with
      | zero =>
        intro _ _ k hk
        omega
      | succ n ih =>
        intro hn hs k hk
        rw [suffixRun] at hs
        split at hs
        · rename_i hbn
          rcases Nat.lt_or_ge k n with hlt | hge
          · exact ih (by omega) (by omega) k hlt
          · have hkn : k = n := by omega
            rw [hkn]
            exact hbn
        · omega
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [allOnes_getLsbD_of_lt hk]
    exact hall w (Nat.le_refl w) h k hk
  · intro h
    rw [h]
    have hall : ∀ n, n ≤ w → suffixRun (BitVec.allOnes w) n = n := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [suffixRun]
      | succ n ih =>
        intro hn
        rw [suffixRun, allOnes_getLsbD_of_lt (by omega), ih (by omega)]
        simp
    exact hall w (Nat.le_refl w)

/-- **`%lzpc2` is the trailing run's parity**: `ctlz` of the complement counts the
suffix run of set lanes, and the kernel's `& 1` is its parity. -/
theorem lzParity_eq_suffixRun {w : Nat} (bs : BitVec w) :
    decide (ctlz (~~~bs) % 2 = 1) = decide (suffixRun bs w % 2 = 1) := by
  rw [ctlz_not_eq_trailingRun]
  rfl

/-- `%lzpc2`: `ctlz(~~~bs) & 1`, as the kernel computes it. -/
def lzpc {w : Nat} (bs : BitVec w) : BitVec w :=
  BitVec.ofNat w (ctlz (~~~bs)) &&& 1#w

/-- Lane zero of `%lzpc2` is the parity `ctlz` reports. -/
theorem lzpc_getLsbD_zero {w : Nat} (bs : BitVec w) (hw : 0 < w) :
    (lzpc bs).getLsbD 0 = decide (ctlz (~~~bs) % 2 = 1) := by
  unfold lzpc
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_one, Nat.testBit_zero]
  simp [hw]

/-- `%ppnc2`: the outgoing run parity — the top backslash lane, and `ctlz`'s
parity, corrected to the incoming parity when the block is all backslashes and the
run continues. -/
def nextParity {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) : BitVec w :=
  (bs >>> (w - 1)) &&&
    ((if decide (bs = BitVec.allOnes w) && runOpen then oneLane w ppar else 0#w) ^^^ lzpc bs)

/-- **The all-ones correction and the `ctlz` parity are the run parity at the
block's end.** -/
theorem parity_top {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) (hw : 0 < w) :
    (bs.getLsbD (w - 1)
        && ((if decide (bs = BitVec.allOnes w) && runOpen then ppar else false)
          ^^ decide (suffixRun bs w % 2 = 1)))
      = runParityBefore bs runOpen ppar w := by
  rw [runParityBefore_eq bs runOpen ppar w (Nat.le_refl w)]
  have hsuffix : suffixRun bs w
      = if bs.getLsbD (w - 1) then suffixRun bs (w - 1) + 1 else 0 := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [suffixRun, show w' + 1 - 1 = w' from by omega]
  cases htop : bs.getLsbD (w - 1) with
  | false =>
    have hzero : suffixRun bs w = 0 := by rw [hsuffix, htop]; rfl
    have hw0 : decide (0 = w) = false := decide_eq_false (by omega)
    rw [hzero, hw0]
    rfl
  | true =>
    by_cases hfill : suffixRun bs w = w
    · have hall : bs = BitVec.allOnes w := (suffixRun_eq_self_iff bs).mp hfill
      have heq : decide (bs = BitVec.allOnes w) = true := decide_eq_true hall
      rw [hfill, heq]
      cases runOpen <;> cases ppar <;> simp [Bool.xor_comm]
    · have hall : bs ≠ BitVec.allOnes w := fun h => hfill ((suffixRun_eq_self_iff bs).mpr h)
      have hne : decide (bs = BitVec.allOnes w) = false := decide_eq_false hall
      rw [hne, decide_eq_false hfill]
      simp

/-- Lane zero of the all-ones correction: the bit when the correction applies, and
clear otherwise. -/
theorem contrib_getLsbD_zero {w : Nat} (c ppar : Bool) (hw : 0 < w) :
    (if c then oneLane w ppar else 0#w).getLsbD 0 = (if c then ppar else false) := by
  cases c <;> cases ppar <;> simp [oneLane, hw]

/-- Lane zero of `%ppnc2`. -/
theorem nextParity_getLsbD_zero {w : Nat} (bs : BitVec w) (runOpen ppar : Bool)
    (hw : 0 < w) :
    (nextParity bs runOpen ppar).getLsbD 0
      = (bs.getLsbD (w - 1)
          && ((if decide (bs = BitVec.allOnes w) && runOpen then ppar else false)
            ^^ decide (ctlz (~~~bs) % 2 = 1))) := by
  unfold nextParity
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    show w - 1 + 0 = w - 1 from by omega, BitVec.getLsbD_xor, lzpc_getLsbD_zero bs hw,
    contrib_getLsbD_zero _ ppar hw]

/-- Lanes other than the first of `%ppnc2` are clear. -/
theorem nextParity_getLsbD_of_pos {w : Nat} (bs : BitVec w) (runOpen ppar : Bool)
    {k : Nat} (hk : k < w) (hk0 : k ≠ 0) : (nextParity bs runOpen ppar).getLsbD k = false := by
  unfold nextParity
  rw [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  have h1 : (bs >>> (w - 1)).getLsbD k = false := by
    rw [BitVec.getLsbD_ushiftRight]
    exact BitVec.getLsbD_of_ge bs (w - 1 + k) (by omega)
  have h2 : (lzpc bs).getLsbD k = false := by
    unfold lzpc
    rw [BitVec.getLsbD_and, BitVec.getLsbD_one,
      show decide (k = 0) = false from decide_eq_false hk0]
    simp
  have h3 : (if decide (bs = BitVec.allOnes w) && runOpen then oneLane w ppar else 0#w).getLsbD k
      = false := by
    by_cases hc : (decide (bs = BitVec.allOnes w) && runOpen) = true
    · rw [ite_eq_left hc, oneLane_getLsbD _ hk,
        show decide (k = 0) = false from decide_eq_false hk0]
      rfl
    · rw [ite_eq_right hc, BitVec.getLsbD_zero]
  rw [h1, h3, h2]
  rfl

/-- **`%ppnc2` is the fold's outgoing `oddRun`.** -/
theorem nextParity_eq {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) (hw : 0 < w) :
    nextParity bs runOpen ppar = oneLane w (runParityBefore bs runOpen ppar w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [nextParity_getLsbD_zero bs runOpen ppar hw, lzParity_eq_suffixRun,
      parity_top bs runOpen ppar hw, oneLane_getLsbD _ hk]
    simp
  · rw [nextParity_getLsbD_of_pos bs runOpen ppar hk hk0, oneLane_getLsbD _ hk,
      show decide (k = 0) = false from decide_eq_false hk0]
    rfl

/-- **The specification's `oddRun` is the kernel's `%ppnc2`.**  Over one
sixty-four-byte block, the kernel's `ctlz` parity and all-ones correction leave the
run parity the specification's fold reports — the field the next block is entered
with. -/
theorem ppn64 (lo hi : Block32) (st : ClassState) (runOpen ppar : Bool)
    (hst : st.oddRun = (runOpen && ppar)) :
    nextParity (specMask64 IsBackslashB lo hi) runOpen ppar
      = oneLane 64
          (classWindow (List.ofFn hi) (classWindow (List.ofFn lo) st).carry).carry.oddRun := by
  rw [nextParity_eq _ _ _ (by decide : 0 < 64), classWindow_carry]
  have h := oddRun_hi (lo := lo) (hi := hi) (st := st) (runOpen := runOpen) (ppar := ppar)
    hst 32 (by omega)
  rw [show 32 + 32 = 64 from rfl] at h
  rw [h]

/-! ### The hypothesis is an invariant of both sides

The derivation's hypothesis `st.oddRun = (o && ppar)` is not a restriction on the
specification: each side reaches only states that satisfy it, and each side says so
in its own vocabulary.

On the kernel's side `%ppnc2 = %topc2 & %ppc2`, so the parity word is clear wherever
`%topc2` is (`nextParity_and_not_top`); since `%openn = %topc2`, a nonzero outgoing
parity therefore implies an open run in the state the next block is entered with
(`nextParity_ne_zero_imp_open`).  On the specification's side, `classStep` gates the
run parity on the byte it reads — `classStep_oddRun_gated` — so a nonzero parity is
itself the run-open bit, read from the window's bytes (`byteOpen`), and every state
the fold reaches from a parity-false seed satisfies the hypothesis with that open bit
(`specCarry_hypothesis`). -/

/-- **The kernel's parity word is confined to the top lane.**  `%ppnc2 = %topc2 & %ppc2`,
so it is clear wherever `%topc2` is clear. -/
theorem nextParity_and_not_top {w : Nat} (bs : BitVec w) (runOpen ppar : Bool) :
    nextParity bs runOpen ppar &&& ~~~(bs >>> (w - 1)) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hk, BitVec.getLsbD_zero]
  unfold nextParity
  rw [BitVec.getLsbD_and]
  cases (bs >>> (w - 1)).getLsbD k <;> simp

/-- The top-lane word is zero exactly when the block's last lane is not a
backslash. -/
theorem topWord_eq_zero_iff {w : Nat} (bs : BitVec w) (hw : 0 < w) :
    (bs >>> (w - 1) = 0#w) ↔ bs.getLsbD (w - 1) = false := by
  constructor
  · intro h
    have h0 := congrArg (fun x : BitVec w => x.getLsbD 0) h
    rwa [BitVec.getLsbD_ushiftRight, show w - 1 + 0 = w - 1 from by omega,
      BitVec.getLsbD_zero] at h0
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_zero, BitVec.getLsbD_ushiftRight]
    cases k with
    | zero => rw [show w - 1 + 0 = w - 1 from by omega, h]
    | succ j => exact BitVec.getLsbD_of_ge bs (w - 1 + (j + 1)) (by omega)

/-- **A nonzero outgoing parity implies an open run.**  The parity word lives on the
top lane alone, and the top lane *is* the next block's `%open`. -/
theorem nextParity_ne_zero_imp_open {w : Nat} (bs : BitVec w) (runOpen ppar : Bool)
    (hw : 0 < w) : nextParity bs runOpen ppar ≠ 0#w → bs.getLsbD (w - 1) = true := by
  intro hne
  cases h : bs.getLsbD (w - 1) with
  | false =>
    exfalso
    apply hne
    unfold nextParity
    rw [(topWord_eq_zero_iff bs hw).mpr h]
    simp
  | true => rfl

/-- The run-open bit a window's bytes leave for lane `k`: the lane before it is a
backslash.  This is the kernel's `%open` read from bytes instead of from a mask. -/
def byteOpen (bs : List UInt8) : Nat → Bool
  | 0 => false
  | j + 1 => ((bs[j]?).map IsBackslashB).getD false

/-- The classifier's step gates the run parity on the byte it reads: the parity after
a byte is nonzero only if that byte is a backslash. -/
theorem classStep_oddRun_gated (st : ClassState) (b : UInt8) :
    (classStep st b).oddRun = (IsBackslashB b && (classStep st b).oddRun) := by
  unfold classStep
  cases hb : IsBackslashB b <;> simp

/-- **Every state the specification's fold reaches satisfies the hypothesis.**  From a
parity-false seed the fold's `oddRun` is gated by the byte before the lane, so reading
the run-open bit as `byteOpen` — the run is open exactly when that byte is a backslash
— gives `st.oddRun = (runOpen && ppar)` for every lane the fold has reached. -/
theorem specCarry_hypothesis (bs : List UInt8) (inside : Bool) :
    ∀ k, k ≤ bs.length →
      (classCarryAt bs ⟨inside, false⟩ k).oddRun
        = (byteOpen bs k && (classCarryAt bs ⟨inside, false⟩ k).oddRun)
  | 0, _ => by
    rw [classCarryAt_oddRun_zero]
    rfl
  | k + 1, hk => by
    have hk' : k < bs.length := by omega
    have hb : bs[k]? = some (bs[k]'hk') := List.getElem?_eq_getElem hk'
    have hsucc : classCarryAt bs ⟨inside, false⟩ (k + 1)
        = classStep (classCarryAt bs ⟨inside, false⟩ k) (bs[k]'hk') := by
      rw [classCarryAt_succ, hb]
    rw [hsucc, show byteOpen bs (k + 1) = IsBackslashB (bs[k]'hk') from by
      rw [show byteOpen bs (k + 1) = ((bs[k]?).map IsBackslashB).getD false from rfl, hb]
      rfl]
    exact classStep_oddRun_gated _ _

/-- **Any `ClassState` satisfies the hypothesis** when the run-open bit is read as the
parity itself: a nonzero parity is then an open run by construction. -/
theorem classState_self_open (st : ClassState) : st.oddRun = (st.oddRun && st.oddRun) :=
  (Bool.and_self st.oddRun).symm

end LeanLLVM.Refinement.QuoteDerive

