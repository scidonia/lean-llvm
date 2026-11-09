/-
The pipeline's loop step: the call sites.

`PipelineBodyFacts` states the instance's vocabulary — the four arms, the carried
state, `pipelineLoopInv` — and leaves `PipelineLoop.step` as the work this module
does.  `step` is one arm iteration at cost one: the arm's own trace, whose
hypotheses are three call-site preconditions and the memory words the units'
posts leave behind.  This module derives those preconditions from the invariant
and the staging, so the dispatch itself is a term rather than a derivation:

* `masksPre_of_window` (re-exported from `JsonPipelineRefine`) is the first site;
* `pos8Pre_of_stored_word` is the entry emitter's, after the body's own store of
  the entry word — the store is what makes the emitter's `e` clause true;
* `escapePre_of_staged_window` is the escape list's, **at the document base**:
  its block clause is `readBytes mem (base + blockAddr blk0) 64`, and the base is
  what makes it name the block the masks describe (`escapeBlockClause_of_staged_window`).

Each is stated with exactly the hypotheses the invariant carries, so a dispatch
lemma supplies them by projection and no call site re-derives a staging fact.
-/
import LeanLLVM.Vellum.PipelineBodyFacts

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON (Block32)
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonS1MasksIR (block64 carrySlot)
open LeanLLVM.Vellum.PipelineBodyFacts
open LeanLLVM.Vellum.JsonEntryIR (pos8Table wordsOf)
open LeanLLVM.Vellum.JsonPipelineIR (Γ_entry_pos8at)

/-! ### The escape list's pre, at the document base

The gate-on arms call `leanllvm_json_escape_list` with the loop index as `blk0`
and the stream, its count and the carry as pointers.  The record's block clause
is at `base + blockAddr blk0`; `escapeBlockClause_of_staged_window` is what
supplies it from the staged window, and the masks, the pair, the count and the
three exclusions are the invariant's own conjuncts. -/

/-- **The escape list's `pre` at the pipeline's call site.**  Every hypothesis is
either a staging fact the invariant carries (`hblk`'s read is
`escapeBlockClause_of_staged_window`'s conclusion) or a clause the record reads
back.  `hblk` is stated at the re-based address so the caller chooses the block's
halves once — the same `lo hi` the mask unit's post names at the same call — and
no injectivity argument is needed to make the two agree. -/
theorem escapePre_of_staged_window (base : Nat) (budget : List Value → Mem → Nat)
    {mem : Mem} {next : Nat} {m : Nat}
    {bsMask ctlMask imMask : BitVec 64} {lo hi : Block32} {st : ClassState}
    {prevb prevs : Bool} {xp xn carry xn0 : Nat}
    (hblk : readBytes mem (base + blockAddr (BitVec.ofNat 64 m)) 64 =
      some (block64 lo hi))
    (hbs : bsMask = specBackslash64 lo hi st)
    (hctl : ctlMask = specControl64 lo hi st)
    (him : imMask = specInString64 lo hi st)
    (hcarry : carryPair mem carry st prevb prevs)
    (hcount : readBytes mem xn 8 = some (wordBytes 8 xn0))
    (hxn0 : xn0 < 2 ^ 63)
    (hdisjCount : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hdisjCarry : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hdisjStream : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hhas : HasBytes mem xp (4 * blockMax xn0))
    (hcap : (BitVec.ofNat 64 m).toNat * 64 + 64 < 2 ^ 32) :
    (Γ_escape_positions base budget).pre
      [.int 64 bsMask, .int 64 ctlMask, .int 64 imMask, .int 64 (BitVec.ofNat 64 m),
        .ptr xp, .ptr xn, .ptr carry] mem next :=
  ⟨xp, xn, carry, BitVec.ofNat 64 m, bsMask, ctlMask, imMask, lo, hi, st, prevb, prevs,
    xn0, rfl, hblk, hbs, hctl, him, hcarry, hcount, hxn0, hdisjCount, hdisjCarry,
    hdisjStream, hhas, hcap⟩

/-! ### The entry emitter's pre, after the body's store

The arm stores the entry word at `%entw` and then calls the emitter with
`[.ptr entw, .int 64 i, .int 64 1, .ptr ep, .int 64 k]` on the memory the store
left.  The emitter's `e` clause is `readBytes mem e (8 * ent.length) =
some (wordsOf ent)`; with one block and the word just stored, that is the store's
own write.  The table, the block bound, the two separations and the count's room
are the staging's and the invariant's. -/

/-- **The entry emitter's `pre` at the pipeline's call site, after the store.**
`hstored` is `readBytes_writeBytes_same` at the body's store, which is why the
emitter's entry-word clause is not a staging obligation. -/
theorem pos8Pre_of_stored_word {mem : Mem} {entw ep tab : Nat}
    {blk0 k : BitVec 64} {word : BitVec 64} {outCap : Nat}
    (hstored : readBytes mem entw 8 = some (natToBytes word.toNat 8))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hblk : 64 * (blk0.toNat + 1) + 63 < 2 ^ 32)
    (hsepWord : entw + 8 ≤ ep ∨ ep + 4 * (k.toNat + 64 + 8) ≤ entw)
    (hsepTab : tab + 8192 ≤ ep ∨ ep + 4 * (k.toNat + 64 + 8) ≤ tab)
    (hcap : k.toNat + 64 + 9 ≤ outCap)
    (hroom : k.toNat + 64 + 9 < 2 ^ 63) :
    Γ_entry_pos8.pre [.ptr entw, .int 64 blk0, .int 64 (1 : BitVec 64), .ptr ep,
      .int 64 k, .ptr tab] mem 0 := by
  refine ⟨entw, ep, tab, blk0, 1, k, [word], outCap, rfl, by simp, hblk, ?_, htab,
    ⟨hsepWord, hsepTab⟩, hcap, hroom⟩
  simpa [wordsOf] using hstored

/-- The same at the re-indexed record the pipeline's environment resolves: the
POS8 member's `Γ_entry_pos8at` appends the staged table, so the pre is the one
above at `args ++ [.ptr tab]`. -/
theorem pos8PreAt_of_stored_word {mem : Mem} {entw ep tab : Nat}
    {blk0 k : BitVec 64} {word : BitVec 64} {outCap : Nat}
    (hstored : readBytes mem entw 8 = some (natToBytes word.toNat 8))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hblk : 64 * (blk0.toNat + 1) + 63 < 2 ^ 32)
    (hsepWord : entw + 8 ≤ ep ∨ ep + 4 * (k.toNat + 64 + 8) ≤ entw)
    (hsepTab : tab + 8192 ≤ ep ∨ ep + 4 * (k.toNat + 64 + 8) ≤ tab)
    (hcap : k.toNat + 64 + 9 ≤ outCap)
    (hroom : k.toNat + 64 + 9 < 2 ^ 63) :
    (Γ_entry_pos8at tab).pre [.ptr entw, .int 64 blk0, .int 64 (1 : BitVec 64),
      .ptr ep, .int 64 k] mem 0 := by
  simpa [Γ_entry_pos8at] using
    pos8Pre_of_stored_word hstored htab hblk hsepWord hsepTab hcap hroom

/-! ### Axiom footprints

The three call-site derivations are records' conjunctions and one store read;
none adds a carrier. -/

/-- info: 'LeanLLVM.Vellum.escapePre_of_staged_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePre_of_staged_window

/-- info: 'LeanLLVM.Vellum.pos8Pre_of_stored_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pos8Pre_of_stored_word

/-- info: 'LeanLLVM.Vellum.pos8PreAt_of_stored_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pos8PreAt_of_stored_word

end LeanLLVM.Vellum
