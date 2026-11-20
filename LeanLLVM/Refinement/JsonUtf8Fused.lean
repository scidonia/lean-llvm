/-
The fused, ASCII-gated form of the UTF-8 stage: the state and the step a host
block loop carries, and what they are worth.

`JsonUtf8Spec` states the stage as a function of the document, and
`JsonUtf8Steps`' `klStep`/`klRun` fold its inline `if` over the blocks of the
staged window.  Both are written for a loop that owns the window and nothing
else.  A host loop — `s1_blocks.c`'s classification loop, or any loop that
already holds a block's two 32-byte vectors — has no window list: it has the
block's bytes, the three bytes read before them (the DFA's load-form carry) and
the two cells this stage adds to it.  This module states that pair of cells and
that step, and proves the step is the stage's.

The state is `(u8k, prev_ascii)`.  `u8k` is the accumulated thirty-two-byte
error vector and `prev_ascii` is the previous block's `ascii` answer; the
preheader's `%prev_ascii = 1` is `FusedState.init`.  The step takes the block's
three carry bytes and its sixty-four bytes as two lists, which is exactly what a
host that has loaded the vectors and their carry reads has, and it returns the
same pair.  Nothing here is a new semantics: `fusedStep` is `klStep` with the
window slices supplied by the caller, and `fusedRun` is the same fold.

The gate state is `prev_ascii` and nothing else: `kernel/json/utf8.c`'s gated
branch — the measured text at `kernel/json/measured/s1fuse.h:1832-1843`, at the
`S1F_UTF8=7`, `S1F_KL_DOC=1` arm — carries that one cell beside `u8k`, and the
DFA has no cross-block state of its own because its load form reads the three
bytes before the block.  There is no `prev_incomplete` or `prev_input_block`
cell in that branch, and this module introduces neither.

## What is proved

* `fusedStep_klStep` — the step is `klStep`'s, at the window's own slices.  So
  a host loop that supplies the block's bytes composes the stage, rather than a
  look-alike of it.
* `fusedRun_word_eq_klAll` — for **both** gate values, the loop's accumulated
  word at the document's block count is `klAll gate bs`, the stage's own
  accumulator.  `klAll_gate_invariant` is what makes one statement cover the
  two paths; the skip is elided, not reinterpreted.
* `fusedStep_advances` and `fusedRun_advance` — one block advances the
  accumulator exactly as the stage's window walk does:
  `zipWith (·|||·) acc (klErrBlk pre blk)`.  This is the per-block invariant a
  host loop carries; `packLanes u8k = bytesToNat (klAcc bs i)` is the emitted
  body's form of it, in `JsonUtf8Steps`' `utf8Gated_loop_run`.
* `fusedVerdict_run_eq_klStage` — the loop's word, read by the stage's
  document-end rule, is `klStage` at the same length and gate.
* `fusedVerdict_zero_iff_unit_post` — that verdict is zero exactly on
  `utf8WinPrefix (utf8Window bs n nb)`, which is `utf8_stage_refines`' post.  The
  two are the same predicate, so a body run's returned word and this loop's
  verdict share a zero set; `fusedVerdict_eq_of_unit_post` turns that into
  equality for the unit's `{0,1}` word.
* `ascii_window_prefix` — every byte of the document below `0x80` makes the
  staged window a valid prefix, so the stage's word is zero and the call can be
  skipped.  It is the gated path's own special case: every block is ASCII and
  the skip fires, so the accumulator never leaves its initial zero
  (`fusedRun_ascii`).

## What the emitted body must contain

These theorems are about the computation, not about a body, and the body they
apply to is the one `JsonUtf8Steps` already refines: the gated loop's `%u8k`
phi, its `%prev_ascii` phi, the block's two `<4 x i64>` loads, the `ptestz` on
their `or`, and the `ascii && prev_ascii` branch.  The correspondence is that
loop's invariant `packLanes u8k = bytesToNat (klAcc bs i)` at `for.body.us`,
together with `fusedRun_word_eq_klAcc` here: the two agree at every block, so
the body's accumulator at the end is the word this module's verdict is read
from.

A fixture for a *host* loop that fuses this step into a wider block loop — the
contracted `s1_blocks` body with a UTF-8 arm — cannot be added yet: that body
today writes every block's entry word and, at `arm & 2`, appends the escape
list; it carries no `u8k`, and bit 2 of its arm word is the UTF-8 error arm its
header assigns to the caller's stage, so there is no UTF-8 arm to capture.
Capturing it now would pin a body that does not contain the step, and a
refinement of it would say nothing about this module.  It waits for the block
unit — or a caller-side fused body — to carry the arm.  Its refinement is also
not this module's: the unit's own body is emitted and refined in
`JsonUtf8Steps`, while the host body is the block unit's, which `JsonS1BlocksIR`
pins.  What such a body must contain is fixed by the statements
above and needs no new theorem: the two vectors it has already loaded, the
three-byte carry at `p - 3`, the `prev_ascii` cell beside the accumulator, the
gate branch, and the accumulator's lane count.  The load-form carry is why the
host shape needs no cross-block DFA state: `pre` is the three bytes at `p - 3`,
which are the three bytes before the block and, for block `bi + 1`, the previous
block's last three (`klPre_succ`).
-/
import LeanLLVM.Refinement.JsonUtf8Steps

namespace LeanLLVM.Refinement.JsonUtf8Fused

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

/-! ### The state and the step

The two cells the stage adds to a host loop, and one block's step over them. -/

/-- The fused loop's state: the accumulated error vector, and whether the
previous block was all-ASCII.  `prev_ascii` starts set, as the preheader's
`%prev_ascii = 1` does, so the first block is judged on its own bytes. -/
structure FusedState where
  /-- The accumulated thirty-two-byte error vector (`u8k`). -/
  u8k : List UInt8
  /-- The previous block's `ascii` answer (`prev_ascii`). -/
  prevAscii : Bool

/-- The state the loop is entered with: the zero error vector and a set
`prev_ascii`. -/
def FusedState.init : FusedState := ⟨List.replicate 32 0x00, true⟩

/-- The pair `klAll`'s fold carries, at this state. -/
def FusedState.toPair (st : FusedState) : List UInt8 × Bool := (st.u8k, st.prevAscii)

/-- One block's fused step, from the three carry bytes before it and its
sixty-four bytes: the block's `ascii`, the skip when the gate selects it and the
previous block was ASCII, and the error vector or-ed in otherwise.

This is `klStep` with `klPre`/`klBlk` supplied by the caller, so it is the same
computation at a host's own reads rather than a second one. -/
def fusedStep (gate : Bool) (pre blk : List UInt8) (st : FusedState) : FusedState :=
  let ascii := klAsciiBlk blk
  let skip := (gate && ascii && st.prevAscii) = true
  { u8k := if skip then st.u8k
           else List.zipWith (· ||| ·) st.u8k (klErrBlk pre blk)
    prevAscii := ascii }

/-- **The step is `klStep`'s**, at the window's own slices.  A host loop that
supplies the block's three carry bytes and its sixty-four bytes therefore runs
the stage's step, and every theorem stated about `klStep`/`klRun` applies. -/
theorem fusedStep_klStep (win : List UInt8) (gate : Bool) (bi : Nat) (st : FusedState) :
    (fusedStep gate (klPre win bi) (klBlk win bi) st).toPair
      = klStep win gate st.toPair bi := by
  obtain ⟨u8k, prev⟩ := st
  rfl

/-- The loop's fold over `nb` blocks of the window, from a state. -/
def fusedRun (win : List UInt8) (gate : Bool) (nb : Nat) (st : FusedState) : FusedState :=
  (List.range nb).foldl
    (fun st bi => fusedStep gate (klPre win bi) (klBlk win bi) st) st

/-! ### The fold bridge

`fusedRun` and `klRun` are the same fold at the pair the specification carries;
the only difference is the initial state, which this bridge leaves free. -/

theorem fusedRun_toPair (win : List UInt8) (gate : Bool) :
    ∀ (nb : Nat) (st : FusedState) (p : List UInt8 × Bool), st.toPair = p →
      (fusedRun win gate nb st).toPair
        = (List.range nb).foldl (fun (st : List UInt8 × Bool) bi => klStep win gate st bi) p := by
  intro nb
  induction nb with
  | zero =>
      intro st p hp
      rw [fusedRun, List.range_zero, List.foldl_nil, List.foldl_nil, hp]
  | succ n ih =>
      intro st p hp
      have hstep : fusedRun win gate (n + 1) st
          = fusedStep gate (klPre win n) (klBlk win n) (fusedRun win gate n st) := by
        unfold fusedRun
        rw [List.range_succ, List.foldl_append]
        rfl
      have hkl : (List.range (n + 1)).foldl
            (fun (st : List UInt8 × Bool) bi => klStep win gate st bi) p
          = klStep win gate
              ((List.range n).foldl
                (fun (st : List UInt8 × Bool) bi => klStep win gate st bi) p) n := by
        rw [List.range_succ, List.foldl_append]
        rfl
      rw [hstep, hkl, fusedStep_klStep win gate n (fusedRun win gate n st), ih st p hp]

/-- The run from the initial state is `klRun`, at the pair `klRun` starts
from. -/
theorem fusedRun_init_toPair (win : List UInt8) (gate : Bool) (nb : Nat) :
    (fusedRun win gate nb FusedState.init).toPair = klRun win gate nb := by
  unfold klRun
  exact fusedRun_toPair win gate nb FusedState.init _ rfl

/-- The loop's accumulated word is `klRun`'s first component. -/
theorem fusedRun_word_eq_klRun (win : List UInt8) (gate : Bool) (nb : Nat) :
    (fusedRun win gate nb FusedState.init).u8k = (klRun win gate nb).1 := by
  have h := fusedRun_init_toPair win gate nb
  exact congrArg Prod.fst h

/-! ### The unit's window walk

`klAcc` is the ungated fold `JsonUtf8Steps` states against the document's own
window; the gated run is its equal block for block, which is what lets the fused
word be read as the unit's. -/

/-- `klRun` at the ungated gate is `klAcc`, at the document's window. -/
theorem klRun_false_word (bs : List UInt8) (nb : Nat) :
    (klRun (0x00 :: 0x00 :: 0x00 :: bs) false nb).1 = klAcc bs nb := by
  unfold klRun klAcc
  exact klRun_false_fst bs nb (List.replicate 32 0x00) true

/-- **The fused word is the unit's window walk**, for both gate values: after
`i` blocks the accumulator is `klAcc bs i`.  This is the invariant a host loop
carries, and the reason the gate is one statement rather than two. -/
theorem fusedRun_word_eq_klAcc (bs : List UInt8) (gate : Bool) (i : Nat) :
    (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate i FusedState.init).u8k = klAcc bs i := by
  rw [fusedRun_word_eq_klRun]
  cases gate with
  | false => exact klRun_false_word bs i
  | true =>
      rw [(klRun_invariant bs i).1]
      exact klRun_false_word bs i

/-- **One block's advance**, at a host's own state: a block whose step is taken
advances the accumulator by its error vector, and a skipped one is that same
advance because the skipped block's error vector is zero.  The two hypotheses
are the loop's own: the accumulator's lane count, and `prev_ascii` meaning the
three carry bytes are ASCII. -/
theorem fusedStep_advances (win : List UInt8) (gate : Bool) (bi : Nat) (st : FusedState)
    (hlen : st.u8k.length = 32)
    (hprev : st.prevAscii = true → ∀ b ∈ klPre win bi, b.toNat < 0x80) :
    (fusedStep gate (klPre win bi) (klBlk win bi) st).u8k
      = List.zipWith (· ||| ·) st.u8k
          (klErrBlk (klPre win bi) (klBlk win bi)) := by
  have hstep : (fusedStep gate (klPre win bi) (klBlk win bi) st).u8k
      = if (gate && klAsciiBlk (klBlk win bi) && st.prevAscii) = true then st.u8k
        else List.zipWith (· ||| ·) st.u8k (klErrBlk (klPre win bi) (klBlk win bi)) :=
    rfl
  rw [hstep]
  by_cases hskip : (gate && klAsciiBlk (klBlk win bi) && st.prevAscii) = true
  · have hparts : klAsciiBlk (klBlk win bi) = true ∧ st.prevAscii = true := by
      have h := hskip
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact ⟨h.1.2, h.2⟩
    obtain ⟨hascii, hprevSet⟩ := hparts
    have hzero : klErrBlk (klPre win bi) (klBlk win bi) = List.replicate 32 0x00 :=
      utf8Skip_eq_zero _ _ (hprev hprevSet) (klAsciiBlk_iff _ |>.mp hascii)
    rw [ite_eq_left hskip, hzero,
      zipWith_zero_right (· ||| ·) (0 : UInt8) st.u8k (fun x => UInt8.or_zero) hlen]
  · rw [ite_eq_right hskip]

/-- **The run advances as the unit's window walk**: block `i`'s contribution to
the fused accumulator is exactly the `klErrBlk` the stage's fold ors in.  A host
loop that keeps this at every block keeps `klAcc`'s own step. -/
theorem fusedRun_advance (bs : List UInt8) (gate : Bool) (i : Nat) :
    (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate (i + 1) FusedState.init).u8k
      = List.zipWith (· ||| ·)
          (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate i FusedState.init).u8k
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)) := by
  rw [fusedRun_word_eq_klAcc, fusedRun_word_eq_klAcc, klAcc_succ]

/-! ### The document's accumulator

At the document's block count the fused word is `klAll`, the stage's own
accumulator, for each gate value. -/

/-- **The loop's accumulated word is the stage's**, for both gate values.  The
right-hand side is `JsonUtf8Spec`'s `klAll`, the accumulator `klStage` reads, so
the fused loop and the document-level unit are the same computation at the same
staging. -/
theorem fusedRun_word_eq_klAll (bs : List UInt8) (gate : Bool) :
    (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate ((bs.length + 63) / 64)
        FusedState.init).u8k = klAll gate bs := by
  rw [fusedRun_word_eq_klRun, ← klAll_eq_klRun bs gate]

/-! ### The verdict

The stage's document-end rule, read at the loop's word.  Its shape is
`klStage`'s, and the definition below is that shape with the word supplied. -/

/-- The stage's verdict, at a word, a length and the document's last byte: the
accumulator's non-emptiness, then `klTailByte`'s own test at a document whose
length is a whole number of blocks.  This is `klStage`'s body with `klAll`'s
result passed in, which `fusedVerdict_eq_klStage` records. -/
def fusedVerdict (word : List UInt8) (n : Nat) (last : UInt8) : Nat :=
  let err := if word.all (fun x => decide (x = 0x00)) then 0 else 1
  if decide (n ≠ 0) && decide (n % 64 = 0) && klTailByte last then 1 else err

/-- The verdict at `klAll`'s word **is** `klStage`. -/
theorem fusedVerdict_eq_klStage (bs : List UInt8) (n : Nat) (gate : Bool) :
    fusedVerdict (klAll gate bs) n (klByte bs (n - 1)) = klStage bs n gate :=
  rfl

/-- **The loop's verdict is the stage's**, at the same length and gate. -/
theorem fusedVerdict_run_eq_klStage (bs : List UInt8) (gate : Bool) :
    fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate ((bs.length + 63) / 64)
          FusedState.init).u8k
        bs.length (klByte bs (bs.length - 1))
      = klStage bs bs.length gate := by
  rw [fusedRun_word_eq_klAll, fusedVerdict_eq_klStage]

/-- The verdict is one of the ABI's two words. -/
theorem fusedVerdict_eq_zero_or_one (word : List UInt8) (n : Nat) (last : UInt8) :
    fusedVerdict word n last = 0 ∨ fusedVerdict word n last = 1 := by
  dsimp only [fusedVerdict]
  by_cases htail :
      (decide (n ≠ 0) && decide (n % 64 = 0) && klTailByte last) = true
  · rw [ite_eq_left htail]; exact Or.inr rfl
  · rw [ite_eq_right htail]
    by_cases hacc : (word.all (fun x => decide (x = 0x00))) = true
    · rw [ite_eq_left hacc]; exact Or.inl rfl
    · rw [ite_eq_right hacc]; exact Or.inr rfl

/-- The stage's verdict is zero exactly when the error vector is clear and the
document-end byte test is not due: the two halves `klStage`'s body forms. -/
theorem klStage_eq_zero_iff (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64) :
    klStage bs n gate = 0 ↔
      (klErrAll (utf8Window bs n nb) (64 * nb) ∧
        ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true)) := by
  have hacc := klAll_zero_iff_klErrAll bs n nb gate hn hnb
  dsimp only [klStage]
  constructor
  · intro h
    by_cases htail : (decide (n ≠ 0) && decide (n % 64 = 0) &&
        klTailByte (klByte bs (n - 1))) = true
    · rw [ite_eq_left htail] at h
      exact absurd h (by decide)
    · rw [ite_eq_right htail] at h
      have hall : (klAll gate bs).all (fun x => decide (x = 0x00)) = true := by
        by_cases hno : (klAll gate bs).all (fun x => decide (x = 0x00)) = true
        · exact hno
        · rw [ite_eq_right hno] at h
          exact absurd h (by decide)
      refine ⟨hacc.mp hall, ?_⟩
      rintro ⟨h0, hmod, hb⟩
      apply htail
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨decide_eq_true h0, decide_eq_true hmod⟩, hb⟩
  · rintro ⟨herr, htail⟩
    have hall : (klAll gate bs).all (fun x => decide (x = 0x00)) = true := hacc.mpr herr
    have htail' : ¬ (decide (n ≠ 0) && decide (n % 64 = 0) &&
        klTailByte (klByte bs (n - 1))) = true := by
      intro hh
      rw [Bool.and_eq_true, Bool.and_eq_true] at hh
      exact htail ⟨of_decide_eq_true hh.1.1, of_decide_eq_true hh.1.2, hh.2⟩
    rw [ite_eq_right htail', ite_eq_left hall]

/-- **The loop's verdict's zero set is the unit's post**: `utf8_stage_refines`
concludes `err' = 0 ↔ utf8WinPrefix (utf8Window bs.toList n nb)`, and the loop's
verdict is zero exactly on that same predicate.  This is the composition at the
unit's staging; no new semantics is introduced on either side. -/
theorem fusedVerdict_zero_iff_unit_post (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64) :
    fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
        n (klByte bs (n - 1)) = 0 ↔
      utf8WinPrefix (utf8Window bs n nb) := by
  have hword : (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
      = klAll gate bs := by
    rw [show nb = (bs.length + 63) / 64 from by rw [hnb, hn]]
    exact fusedRun_word_eq_klAll bs gate
  rw [hword, fusedVerdict_eq_klStage, klStage_eq_zero_iff bs n nb gate hn hnb]
  exact klErrAll_window_iff bs n nb hn hnb

/-- **A `{0,1}` word with the unit's zero set is the loop's verdict.**  The unit's
returned word is in `{0,1}` and satisfies the post (`utf8_stage_refines`), so
this turns the shared zero set into an equality with the fused verdict. -/
theorem fusedVerdict_eq_of_unit_post {bs : List UInt8} {n nb : Nat} {gate : Bool}
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64) {err' : Nat}
    (h01 : err' = 0 ∨ err' = 1)
    (hpost : err' = 0 ↔ utf8WinPrefix (utf8Window bs n nb)) :
    err' = fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
        n (klByte bs (n - 1)) := by
  have hff := fusedVerdict_zero_iff_unit_post bs n nb gate hn hnb
  rcases h01 with h | h
  · have hf : fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
        n (klByte bs (n - 1)) = 0 := hff.mpr (hpost.mp h)
    rw [h, hf]
  · have hpre : ¬ utf8WinPrefix (utf8Window bs n nb) := by
      intro hp
      have := hpost.mpr hp
      rw [h] at this
      exact absurd this (by decide)
    have hf : fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
        n (klByte bs (n - 1)) = 1 := by
      rcases fusedVerdict_eq_zero_or_one _ _ _ with g | g
      · exact absurd (hff.mp g) hpre
      · exact g
    rw [h, hf]

/-! ### The ASCII shortcut

Every byte below `0x80` makes every block ASCII, so the gate's skip fires on
every block of either path and the accumulator never leaves its initial zero.
The document-end rule is the stage's, and `klTailByte` is clear at an ASCII last
byte, so the verdict is zero and the call can be skipped. -/

/-- A block of the window is inside it. -/
theorem klBlk_subset (win : List UInt8) (i : Nat) :
    ∀ b ∈ klBlk win i, b ∈ win := by
  intro b hb
  exact List.mem_of_mem_drop (List.mem_of_mem_take hb)

/-- The three bytes before a block are inside the window too. -/
theorem klPre_subset (win : List UInt8) (i : Nat) :
    ∀ b ∈ klPre win i, b ∈ win := by
  intro b hb
  exact List.mem_of_mem_drop (List.mem_of_mem_take hb)

/-- **An all-ASCII window never moves the accumulator.**  The step's skip fires
at every block of the gated path, and the ungated path ors in a zero vector; the
state is the initial one after every block. -/
theorem fusedRun_ascii (win : List UInt8) (gate : Bool) (nb : Nat)
    (hwin : ∀ b ∈ win, b.toNat < 0x80) :
    (fusedRun win gate nb FusedState.init).u8k = List.replicate 32 0x00 := by
  suffices H : ∀ i, (fusedRun win gate i FusedState.init).u8k = List.replicate 32 0x00 ∧
      (fusedRun win gate i FusedState.init).prevAscii = true by
    exact (H nb).1
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      have hstep : fusedRun win gate (n + 1) FusedState.init
          = fusedStep gate (klPre win n) (klBlk win n)
              (fusedRun win gate n FusedState.init) := by
        unfold fusedRun
        rw [List.range_succ, List.foldl_append]
        rfl
      obtain ⟨hacc, hprev⟩ := ih
      have hblk : ∀ b ∈ klBlk win n, b.toNat < 0x80 :=
        fun b hb => hwin b (klBlk_subset win n b hb)
      have hpre : ∀ b ∈ klPre win n, b.toNat < 0x80 :=
        fun b hb => hwin b (klPre_subset win n b hb)
      have hascii : klAsciiBlk (klBlk win n) = true := (klAsciiBlk_iff _).mpr hblk
      have hzero : klErrBlk (klPre win n) (klBlk win n) = List.replicate 32 0x00 :=
        utf8Skip_eq_zero _ _ hpre hblk
      rw [hstep]
      have hsu : (fusedStep gate (klPre win n) (klBlk win n)
            (fusedRun win gate n FusedState.init)).u8k
          = (if (gate && klAsciiBlk (klBlk win n) && true) = true
              then List.replicate 32 0x00
              else List.zipWith (· ||| ·) (List.replicate 32 0x00)
                (klErrBlk (klPre win n) (klBlk win n))) := by
        rw [show (fusedStep gate (klPre win n) (klBlk win n)
              (fusedRun win gate n FusedState.init)).u8k
            = if (gate && klAsciiBlk (klBlk win n) &&
                  (fusedRun win gate n FusedState.init).prevAscii) = true
                then (fusedRun win gate n FusedState.init).u8k
                else List.zipWith (· ||| ·) (fusedRun win gate n FusedState.init).u8k
                  (klErrBlk (klPre win n) (klBlk win n)) from rfl,
          hacc, hprev]
      have hsp : (fusedStep gate (klPre win n) (klBlk win n)
            (fusedRun win gate n FusedState.init)).prevAscii = true := by
        rw [show (fusedStep gate (klPre win n) (klBlk win n)
              (fusedRun win gate n FusedState.init)).prevAscii
            = klAsciiBlk (klBlk win n) from rfl, hascii]
      rw [hsu, hsp]
      constructor
      · by_cases hskip : (gate && klAsciiBlk (klBlk win n) && true) = true
        · rw [ite_eq_left hskip]
        · rw [ite_eq_right hskip, hzero,
            zipWith_zero_right (· ||| ·) (0 : UInt8) (List.replicate 32 0x00)
              (n := 32) (fun x => UInt8.or_zero) (by simp)]
      · rfl

/-- The last readable byte of an ASCII document is ASCII; at an empty document
the read is the padded zero. -/
theorem klByte_last_ascii (l : List UInt8) (h : ∀ b ∈ l, b.toNat < 0x80) :
    (klByte l (l.length - 1)).toNat < 0x80 := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD]
  rcases l with _ | ⟨x, xs⟩
  · decide
  · have hlt : xs.length < (x :: xs).length := by simp
    have hidx : (x :: xs).length - 1 = xs.length := by simp
    rw [hidx, List.getElem?_eq_getElem hlt]
    exact h _ (List.getElem_mem hlt)

/-- The document window of an ASCII document is all ASCII (the three leading
zeros are). -/
theorem ascii_doc_window (bs : List UInt8) (hbs : ∀ b ∈ bs, b.toNat < 0x80) :
    ∀ b ∈ (0x00 :: 0x00 :: 0x00 :: bs), b.toNat < 0x80 := by
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | rfl | rfl | hb
  · decide
  · decide
  · decide
  · exact hbs b hb

/-- **The ASCII shortcut**: an all-ASCII document's verdict is zero, so the
stage's call can be skipped.  This is the gated path's special case — every
block skips and the accumulator stays zero. -/
theorem fusedVerdict_ascii (bs : List UInt8) (gate : Bool)
    (hbs : ∀ b ∈ bs, b.toNat < 0x80) :
    fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate ((bs.length + 63) / 64)
          FusedState.init).u8k
        bs.length (klByte bs (bs.length - 1)) = 0 := by
  have hword := fusedRun_ascii _ gate ((bs.length + 63) / 64)
    (ascii_doc_window bs hbs)
  have hkl : klAll gate bs = List.replicate 32 0x00 := by
    rw [← fusedRun_word_eq_klAll bs gate, hword]
  have hlast : (klByte bs (bs.length - 1)).toNat < 0x80 := klByte_last_ascii bs hbs
  rw [fusedVerdict_run_eq_klStage]
  dsimp only [klStage]
  have htail : ¬ (decide (bs.length ≠ 0) && decide (bs.length % 64 = 0) &&
      klTailByte (klByte bs (bs.length - 1))) = true := by
    intro hh
    rw [Bool.and_eq_true, Bool.and_eq_true] at hh
    have hf := klTailByte_false_of_charEnd (Or.inl hlast)
    rw [hf] at hh
    exact absurd hh.2 (by decide)
  rw [hkl, ite_eq_right htail]
  simp

/-- **An ASCII document's accumulator is the zero vector** — the unit's own word,
not only the loop's. -/
theorem klAll_ascii_zero (bs : List UInt8) (gate : Bool)
    (hbs : ∀ b ∈ bs, b.toNat < 0x80) : klAll gate bs = List.replicate 32 0x00 := by
  rw [← fusedRun_word_eq_klAll bs gate]
  exact fusedRun_ascii _ gate _ (ascii_doc_window bs hbs)

/-- **An ASCII document's stage verdict is zero**: the unit's word is zero and
`klTailByte` is clear at an ASCII byte, so the call can be skipped. -/
theorem klStage_ascii_zero (bs : List UInt8) (gate : Bool)
    (hbs : ∀ b ∈ bs, b.toNat < 0x80) : klStage bs bs.length gate = 0 := by
  rw [← fusedVerdict_run_eq_klStage]
  exact fusedVerdict_ascii bs gate hbs

/-- **An ASCII document's staged window is a valid prefix**: the unit's word is
zero at that staging, so the call can be skipped.  This is
`fusedVerdict_zero_iff_unit_post` at the ASCII verdict. -/
theorem ascii_window_prefix (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hbs : ∀ b ∈ bs, b.toNat < 0x80) :
    utf8WinPrefix (utf8Window bs n nb) := by
  have hzero : fusedVerdict
      (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
      n (klByte bs (n - 1)) = 0 := by
    rw [hn]
    rw [show nb = (bs.length + 63) / 64 from by omega]
    exact fusedVerdict_ascii bs gate hbs
  exact (fusedVerdict_zero_iff_unit_post bs n nb gate hn hnb).mp hzero

/-! ### The footprint

Every statement above is over the specification's own definitions; the pins are
the measured carriers, and they are repeated in `LeanLLVMTest/Refinement.lean`. -/

#print axioms fusedStep_klStep
#print axioms fusedRun_init_toPair
#print axioms fusedRun_word_eq_klAcc
#print axioms fusedStep_advances
#print axioms fusedRun_advance
#print axioms fusedRun_word_eq_klAll
#print axioms fusedVerdict_run_eq_klStage
#print axioms fusedVerdict_eq_zero_or_one
#print axioms klStage_eq_zero_iff
#print axioms fusedVerdict_zero_iff_unit_post
#print axioms fusedVerdict_eq_of_unit_post
#print axioms fusedRun_ascii
#print axioms fusedVerdict_ascii
#print axioms klAll_ascii_zero
#print axioms klStage_ascii_zero
#print axioms ascii_window_prefix

end LeanLLVM.Refinement.JsonUtf8Fused
