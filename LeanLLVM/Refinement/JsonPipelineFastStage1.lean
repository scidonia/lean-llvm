/-
The fast stage-1 pass, at the pieces its C body composes.

`kernel/json/pipeline_fast.c`'s mask pass is the certified stage-1 classifier
with two differences: the structural/whitespace shuffle pair is read as a
delimiter word and a *neither* word (the lanes whose table byte is zero) instead
of a delimiter and a whitespace word, and the UTF-8 gate is the fused ASCII-gated
step `JsonUtf8Fused` already states, folded over the vectors the classifier
loaded.  The entry word, the tail clamp and the emitter call are the pipeline's
own three lines.

This module proves the identities the pass rests on, at the models the certified
units already state:

* `pf_neither_lane` and `pf_masks_word_eq` — the classifier word identity.  For
  an 8-bit table byte `r`, `r = 0` exactly when both nibble classes are clear, so
  the candidate's `n` word (`movemask (r = 0)`) is the complement of
  `delimiter | whitespace`.  The candidate's scalar word
  `n & ~quote & ~in_string` is therefore the specification's `specScalar64`,
  whose four-term complement is the default's line.
* `pf_entry_word_eq` — the candidate's entry-word line at those words is
  `entryMask64`.
* `pf_plain_spec` — the `ent`-array shape: one emitter call over the whole list
  has the cursor and stream the per-block singleton calls compose, so the
  certified `entry_pos8_refines`/`entry_b8_refines` apply unchanged.
* `pf_utf8_word_eq` — the fused gate's verdict at the candidate's block count is
  the unit's `{0,1}` word and `utf8_stage_refines`'s post, by `JsonUtf8Fused`'s
  `fusedVerdict_eq_of_unit_post`.

The pass's own control flow — the full-block loop, the peeled partial block and
the `limMask` clamp — is not restated as a body theorem here: the candidate has
no emitted fixture, and `pf_mask_pass_spec` is the statement that needs one.
-/
import LeanLLVM.Refinement.JsonEntryAgreement
import LeanLLVM.Refinement.JsonEntSpec
import LeanLLVM.Refinement.JsonUtf8Fused

namespace LeanLLVM.Refinement.JsonPipelineFastStage1

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonB8Steps
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

set_option maxHeartbeats 1000000

/-! ### The classifier word identity -/

/-- **The neither lane, for an 8-bit table byte.**  `r` is zero exactly when the
six structural bits and the two whitespace bits are both clear.  This is the
identity behind `pf_sw32_dn`'s `n = movemask (r = 0)` and `s1f_sw32`'s
`sm | ws`: the table byte is eight bits wide, so the two halves leave nothing
out. -/
theorem pf_neither_lane (r : BitVec 8) :
    (r = 0) ↔ ((r &&& 0x3F = 0) ∧ (r &&& 0xC0 = 0)) := by
  constructor
  · intro h
    subst h
    decide
  · intro ⟨h1, h2⟩
    have hsplit : r = (r &&& 0x3F) ||| (r &&& 0xC0) := by
      rw [← BitVec.and_or_distrib_left]
      have hf : (0x3F : BitVec 8) ||| 0xC0 = BitVec.allOnes 8 := by decide
      rw [hf, BitVec.and_allOnes]
    rw [hsplit, h1, h2]
    decide

/-- **The classifier's scalar word.**  The candidate's
`n & ~quote & ~in_string`, with `n = ~(delimiter | whitespace)`, is the
specification's `specScalar64`; the default's `~(quote | delim | in_string | ws)`
is the same four-term complement.  `pf_neither_lane` is why the candidate's `n`
is that complement at every lane. -/
theorem pf_masks_word_eq (lo hi : Block32) (st : ClassState) :
    (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) &&&
        ~~~ (specQuote64 lo hi st) &&& ~~~ (specInString64 lo hi st)
      = specScalar64 lo hi st := by
  simp only [specScalar64, BitVec.not_or]
  ac_rfl

/-- The candidate's entry-word line at the specification's words.  `q`, `d`,
`im` and `nn` are the block's quote, delimiter, in-string and neither words;
the scalar word is `nn & ~q & ~im`, and the candidate's three lines are
`entryMask64` once `pf_masks_word_eq` identifies that word with
`specScalar64`. -/
def pfEntryWord (q d im nn : BitVec 64) (prevS : Bool) : BitVec 64 :=
  q ||| (d &&& ~~~ im) |||
    ((nn &&& ~~~ q &&& ~~~ im) &&&
      ~~~ (((nn &&& ~~~ q &&& ~~~ im) <<< 1) ||| (if prevS then 1 else 0)))

/-- **The candidate's entry-word line is `entryMask64`.** -/
theorem pf_entry_word_eq (lo hi : Block32) (st : ClassState) (prevS : Bool) :
    pfEntryWord (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st)
        (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) prevS
      = entryMask64 lo hi st prevS := by
  simp only [pfEntryWord, entryMask64, structuralOnly64, scalarStarts64]
  rw [pf_masks_word_eq]

/-! ### The plain shape: one emitter call over the list -/

/-- The per-block singleton emitter's composition, in the model: each block's
population count advances the cursor and each block's positions append to the
stream at that block's own base. -/
def perBlockFold : List (BitVec 64) → Nat → Nat → Nat × List Nat
  | [], _, k => (k, [])
  | w :: ws, base, k =>
      let rest := perBlockFold ws (base + 64) (k + ctpop w)
      (rest.1, positionsOf w base ++ rest.2)

/-- **The per-block composition is the single call's model.**  The fold's cursor
is the starting cursor plus the stream's population count and its stream is
`streamPrefix` at the block count, so one emitter call over the whole word list
has exactly the output the default's per-block singleton calls compose. -/
theorem perBlockFold_eq (ent : List (BitVec 64)) (blk0 k : Nat) :
    perBlockFold ent (64 * blk0) k =
      (k + (ent.map ctpop).sum, streamPrefix ent blk0 ent.length) := by
  induction ent generalizing blk0 k with
  | nil => rfl
  | cons w ws ih =>
      have hbase : 64 * blk0 + 64 = 64 * (blk0 + 1) := by omega
      simp only [perBlockFold, List.map_cons, List.sum_cons, streamPrefix,
        List.take_length, List.mapIdx_cons, List.flatten_cons]
      rw [hbase, ih (blk0 + 1) (k + ctpop w)]
      refine Prod.ext ?_ ?_
      · omega
      · simp only [Nat.add_zero]
        congr 1
        apply congrArg List.flatten
        rw [List.mapIdx_eq_zipIdx_map, List.mapIdx_eq_zipIdx_map, List.take_length]
        apply List.map_congr_left
        intro p _
        obtain ⟨m, i⟩ := p
        dsimp only
        rw [show blk0 + 1 + i = blk0 + (i + 1) from by omega]

/-! ### The entry-array collection -/

/-- The candidate's collected entry words and the carry it hands the next block:
the `S`/`e` line of `pipeline_fast.c`, with `S` the scalar word and the run
start's carry the top lane of `S`. -/
def collectWords : List (Block32 × Block32) → ClassState → Bool →
    List (BitVec 64) × ClassState × Bool
  | [], st, prevS => ([], st, prevS)
  | (lo, hi) :: rest, st, prevS =>
      let S := specScalar64 lo hi st
      let w := pfEntryWord (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st)
        (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) prevS
      let rest' := collectWords rest (carry64 lo hi st) (S.getLsbD 63)
      (w :: rest'.1, rest'.2.1, rest'.2.2)

/-- The default's entry words at the same block sequence: `entryMask64` at each
block's state and previous top lane. -/
def specWords : List (Block32 × Block32) → ClassState → Bool → List (BitVec 64)
  | [], _, _ => []
  | (lo, hi) :: rest, st, prevS =>
      entryMask64 lo hi st prevS ::
        specWords rest (carry64 lo hi st) ((specScalar64 lo hi st).getLsbD 63)

/-- **The candidate's collected words are the default's.**  The block sequence's
carry and previous-top-lane evolve the same way, and `pf_entry_word_eq` turns
each block's `S`/`e` line into `entryMask64`. -/
theorem collectWords_eq (blocks : List (Block32 × Block32)) (st : ClassState)
    (prevS : Bool) :
    (collectWords blocks st prevS).1 = specWords blocks st prevS := by
  induction blocks generalizing st prevS with
  | nil => rfl
  | cons b rest ih =>
      obtain ⟨lo, hi⟩ := b
      simp only [collectWords, specWords, pf_entry_word_eq, ih]

/-! ### The plain entry shape -/

/-- **One emitter call over the array is the per-block singleton calls.**  POS8's
certified post at `(ent, blk0, nblk)` is the cursor and stream the default's
`nblk` singleton calls compose (`perBlockFold`); with `nblk = ent.length` the
two are the same output.  The candidate's `ent[0..nblk)` collection is
`collectWords_eq` above, so this is the whole of the `_plain_*` entry's stage-1
stream. -/
theorem pf_plain_spec (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab outCap : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hdisjP : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
              (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hcap : k + 64 * ent.length + 9 ≤ outCap)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (m' : Mem),
      runFuel entryCalls (3 * nblk + 3) entryPos8Function
        { (initState entryPos8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab])
          with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) m') ∧
      perBlockFold ent (64 * blk0) k =
        (k', streamPrefix ent blk0 nblk) ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 m' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk := by
  obtain ⟨k', m', hrun, hk', hlane, _⟩ :=
    entry_pos8_refines ent blk0 nblk k mem e o tab outCap
      hnblk hblk hent htab hdisjP hcap hk63
  refine ⟨k', m', hrun, ?_, hk', hlane⟩
  rw [perBlockFold_eq, hk', ← hnblk]

/-- The B8 variant of `pf_plain_spec`: the same array shape, with the b8
emitter's fuel and no table or capacity hypothesis. -/
theorem pf_plain_spec_b8 (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (m' : Mem),
      runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
        { (initState entryB8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k])
          with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) m') ∧
      perBlockFold ent (64 * blk0) k =
        (k', streamPrefix ent blk0 nblk) ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 m' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk := by
  obtain ⟨k', m', hrun, hk', hlane, _⟩ :=
    entry_b8_refines ent blk0 nblk k mem e o hnblk hblk hent hdisj hk63
  refine ⟨k', m', hrun, ?_, hk', hlane⟩
  rw [perBlockFold_eq, hk', ← hnblk]

/-! ### The fused pass, one block at a time -/

/-- One block of the list-free fused pass: the candidate's `S`/`e` line, its
carry and previous top lane, and `JsonUtf8Fused`'s gated step over the block and
the three bytes before it.  This is the pass's per-block model; the C body's
full-block loop and peeled partial block are the shape a fixture would pin. -/
def passBlock (pre blk : List UInt8) (lo hi : Block32) (st : ClassState)
    (prevS : Bool) (u : FusedState) :
    BitVec 64 × ClassState × Bool × FusedState :=
  let S := specScalar64 lo hi st
  ( pfEntryWord (specQuote64 lo hi st) (specDelimiter64 lo hi st)
      (specInString64 lo hi st)
      (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) prevS,
    carry64 lo hi st, S.getLsbD 63,
    fusedStep true pre blk u )

/-- The list-free pass's fold over a block list, at the window the gate reads.
The state is the entry words, the classifier's carry and previous top lane, and
the two fused-gate cells; `xp`/`*nxp` are the caller's on this arm. -/
def passRun (win : List UInt8) : Nat → List (Block32 × Block32) → ClassState →
    Bool → FusedState → List (BitVec 64) × ClassState × Bool × FusedState
  | _, [], st, prevS, u => ([], st, prevS, u)
  | i, (lo, hi) :: rest, st, prevS, u =>
      let step := passBlock (klPre win i) (klBlk win i) lo hi st prevS u
      let rest' := passRun win (i + 1) rest step.2.1 step.2.2.1 step.2.2.2
      (step.1 :: rest'.1, rest'.2.1, rest'.2.2.1, rest'.2.2.2)

/-- **The pass's word list is the collection's.**  The per-block step and the
collection carry the same state and write the same word, so the pass's `ent`
is `collectWords`'s and therefore the default's `entryMask64` sequence. -/
theorem passRun_words (win : List UInt8) (blocks : List (Block32 × Block32))
    (st : ClassState) (prevS : Bool) (i : Nat) (u : FusedState) :
    (passRun win i blocks st prevS u).1 = (collectWords blocks st prevS).1 := by
  induction blocks generalizing st prevS i u with
  | nil => rfl
  | cons b rest ih =>
      obtain ⟨lo, hi⟩ := b
      simp only [passRun, collectWords, passBlock]
      rw [ih]

/-- The gate's fold from a block index, for the pass's suffix form. -/
def fusedSuffix (win : List UInt8) (i n : Nat) (u : FusedState) : FusedState :=
  (List.range n).foldl
    (fun u j => fusedStep true (klPre win (i + j)) (klBlk win (i + j)) u) u

/-- One more block at the front is the fold from the next index. -/
theorem fusedSuffix_succ (win : List UInt8) (i n : Nat) (u : FusedState) :
    fusedSuffix win i (n + 1) u =
      fusedSuffix win (i + 1) n
        (fusedStep true (klPre win i) (klBlk win i) u) := by
  unfold fusedSuffix
  induction n generalizing i u with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, List.range_succ, List.foldl_append,
        ih (i := i) (u := u), List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [show i + (n + 1) = i + 1 + n from by omega]

/-- The generalized form of `passRun_gate`: the gate state after a block list is
the fused fold from that block's index. -/
theorem passRun_gate_aux (win : List UInt8) (blocks : List (Block32 × Block32))
    (st : ClassState) (prevS : Bool) (u : FusedState) (i : Nat) :
    (passRun win i blocks st prevS u).2.2.2 =
      fusedSuffix win i blocks.length u := by
  induction blocks generalizing st prevS u i with
  | nil => rfl
  | cons b rest ih =>
      obtain ⟨lo, hi⟩ := b
      simp only [passRun, List.length_cons, passBlock]
      rw [ih]
      exact (fusedSuffix_succ win i rest.length u).symm

/-- **The pass's gate is the fused run.**  At the document's start the fold is
`fusedRun`, so the pass's UTF-8 word is the unit's word `pf_utf8_word_eq` names. -/
theorem passRun_gate (win : List UInt8) (blocks : List (Block32 × Block32))
    (st : ClassState) (prevS : Bool) :
    (passRun win 0 blocks st prevS FusedState.init).2.2.2 =
      fusedRun win true blocks.length FusedState.init := by
  have hrun : fusedRun win true blocks.length FusedState.init =
      fusedSuffix win 0 blocks.length FusedState.init := by
    unfold fusedRun fusedSuffix
    simp only [Nat.zero_add]
  rw [hrun]
  exact passRun_gate_aux win blocks st prevS FusedState.init 0

/-- **The list-free fused pass, at its model.**  The pass's entry words are the
default's `entryMask64` sequence, and its gate state after the block list is
`fusedRun`, the accumulator `pf_utf8_word_eq` reads the verdict from.  The
`xp`/`*nxp` arm is the list pass's own (`escape_positions_satisfies` supplies
it), and the C body's full-block loop and peeled partial block still need an
emitted fixture before a run of the linked object can be the subject. -/
theorem pf_mask_pass_spec (win : List UInt8) (blocks : List (Block32 × Block32))
    (st : ClassState) (prevS : Bool) :
    (passRun win 0 blocks st prevS FusedState.init).1 = specWords blocks st prevS ∧
      (passRun win 0 blocks st prevS FusedState.init).2.2.2 =
        fusedRun win true blocks.length FusedState.init :=
  ⟨by rw [passRun_words, collectWords_eq], passRun_gate win blocks st prevS⟩

/-! ### The fused gate's word -/

/-- **The fused gate's verdict is the unit's word and post.**  At the
candidate's block count and the document's last byte, the gate's accumulated
word read by the stage's document-end rule is the `{0,1}` word
`utf8_stage_refines` returns, and the zero set is that theorem's
`utf8WinPrefix` post at `ungated=false`.  The candidate always takes the gated
branch; `JsonUtf8Fused` proves the word is the same for either gate. -/
theorem pf_utf8_word_eq (bs : Bytes) (n nb : Nat) (mem : Mem) (b : Nat)
    (ungated : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b) (hlen : n + 63 < 2 ^ 64) (haddr : n < 2 ^ 63)
    (hread : readBytes mem (b - 3) (3 + 64 * nb)
      = some (utf8Window bs.toList n nb))
    (hpos : 0 < n) :
    ∃ err' : Nat,
      runFuel utf8Calls (fuelOf nb) utf8Function
        { (initState utf8Function
            [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)]) with mem := mem }
        = some (.ret (some (.int 64 err')) mem) ∧
      err' = fusedVerdict
        (fusedRun (0x00 :: 0x00 :: 0x00 :: bs.toList) true nb
          FusedState.init).u8k
        n (klByte bs.toList (n - 1)) ∧
      (err' = 0 ↔ utf8WinPrefix (utf8Window bs.toList n nb)) := by
  obtain ⟨err', mem', hrun, h01, hpost, hmem⟩ :=
    utf8_stage_refines bs n nb mem b ungated hn hnb hb hlen haddr hread hpos
  refine ⟨err', ?_, ?_, hpost⟩
  · rw [hmem] at hrun
    exact hrun
  · have hlistlen : n = bs.toList.length := by
      rw [hn]
      exact (LeanLLVM.JSON.ByteString.toList_length bs).symm
    exact fusedVerdict_eq_of_unit_post hlistlen hnb h01 hpost

end LeanLLVM.Refinement.JsonPipelineFastStage1
