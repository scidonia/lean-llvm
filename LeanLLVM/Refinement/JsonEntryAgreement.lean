/-
The three entry emitters produce one stream.

`entry_b3_refines` (`JsonB3Steps.lean`), `entry_pos8_refines`
(`JsonEntrySteps.lean`) and `entry_b8_refines` (`JsonB8Steps.lean`) each state
the same conclusion for their own body: the run returns the model's cursor and
the lanes `[k, k')` at the output base hold `streamPrefix ent blk0 nblk`.
`entry_pos8_b8_agree` (`JsonB8Steps.lean`) states that POS8 and B8 agree with
each other on both the cursor and those lanes.  The two statements here add the
pair that was missing — B3 against POS8, and B3 against B8 — so that the three
bodies are pairwise interchangeable as emitters: whichever one a stage-1 pass
calls, the caller observes one cursor and one stream.

The declarations are a recombination of the three refinement conclusions; no
body is re-executed and no new arithmetic is introduced.  B3's loop has two
early exits into the join and a counted scalar tail, and POS8's group writes a
whole eight-lane row; none of that reaches these statements, because each
emitter's own theorem already absorbed it into the cursor and the prefix.
-/
import LeanLLVM.Refinement.JsonB3Steps

namespace LeanLLVM.Refinement.JsonEntryAgreement

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonB8Steps
open LeanLLVM.Refinement.JsonB3Steps

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **B3 and POS8 emit the same stream.**  From the same document word list,
block base, output base and cursor, the B3 run and the POS8 run return the same
cursor and write the same lane words: both are `streamPrefix ent blk0 nblk`.

POS8 also reads its static table, so its own refinement hypotheses are carried
here — the table's bytes, the two disjunctions and the output capacity.  B3
reads no table and has no capacity promise; the extra hypotheses are POS8's and
are not used by the B3 half. -/
theorem entry_b3_pos8_agree (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab outCap : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hdisjP : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
              (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hcap : k + 64 * ent.length + 9 ≤ outCap)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k3 kP : Nat) (m3 mP : Mem),
      runFuel entryCalls (b3RunSteps ent + nblk + 2) entryB3Function
        { (initState entryB3Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k3))) m3) ∧
      runFuel entryCalls (3 * nblk + 3) entryPos8Function
        { (initState entryPos8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 kP))) mP) ∧
      k3 = kP ∧
      readLanes32 m3 (o + 4 * k) (k3 - k) = streamPrefix ent blk0 nblk ∧
      readLanes32 mP (o + 4 * k) (kP - k) = streamPrefix ent blk0 nblk := by
  obtain ⟨k3, m3, h3, hk3, hl3, _⟩ :=
    entry_b3_refines ent blk0 nblk k mem e o hnblk hblk hent hdisj hk63
  obtain ⟨kP, mP, hP, hkP, hlP, _⟩ :=
    entry_pos8_refines ent blk0 nblk k mem e o tab outCap
      hnblk hblk hent htab hdisjP hcap hk63
  exact ⟨k3, kP, m3, mP, h3, hP, hk3.trans hkP.symm, hl3, hlP⟩

/-- **B3 and B8 emit the same stream.**  The same statement against B8, which
reads no table and carries no output-capacity promise: the two runs return the
same cursor and both write `streamPrefix ent blk0 nblk`. -/
theorem entry_b3_b8_agree (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k3 kB : Nat) (m3 mB : Mem),
      runFuel entryCalls (b3RunSteps ent + nblk + 2) entryB3Function
        { (initState entryB3Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k3))) m3) ∧
      runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
        { (initState entryB8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 kB))) mB) ∧
      k3 = kB ∧
      readLanes32 m3 (o + 4 * k) (k3 - k) = streamPrefix ent blk0 nblk ∧
      readLanes32 mB (o + 4 * k) (kB - k) = streamPrefix ent blk0 nblk := by
  obtain ⟨k3, m3, h3, hk3, hl3, _⟩ :=
    entry_b3_refines ent blk0 nblk k mem e o hnblk hblk hent hdisj hk63
  obtain ⟨kB, mB, hB, hkB, hlB, _⟩ :=
    entry_b8_refines ent blk0 nblk k mem e o hnblk hblk hent hdisj hk63
  exact ⟨k3, kB, m3, mB, h3, hB, hk3.trans hkB.symm, hl3, hlB⟩

end LeanLLVM.Refinement.JsonEntryAgreement
