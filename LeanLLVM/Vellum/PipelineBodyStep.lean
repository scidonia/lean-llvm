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
open LeanLLVM.JSON (Block32 IsBackslashB)
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonS1MasksIR (block64 carrySlot carry64)
open LeanLLVM.Vellum.PipelineBodyFacts
open LeanLLVM.Vellum.JsonEntryIR (pos8Table wordsOf)
open LeanLLVM.Vellum.JsonPipelineIR (Γ_entry_pos8at)
open LeanLLVM.Vellum.JsonPipelineBlockEval (sh6 vinc one vexit)

/-! ### The block address's bound

The arm computes `%shl = shl i, 6` and `gep i8, %b, %shl`; the builder's `hpos`
asks `(signExtend 64 (sh6 i)).toNat < 2 ^ 63`.  That is the staging's own bound
at the loop's index: the block index is below the block count, and the count's
`64 * blocks + 63 < 2 ^ 32` keeps the shift inside the address domain. -/

/-- **The block's byte offset is a forward `getelementptr` index.**  From the
index's bound and the staging's block-count bound.  Its carrier is named rather
than hidden: `Classical.choice` arrives with the `Nat`/`BitVec` shift lemmas the
arithmetic uses (`Nat.shiftLeft_eq`, `Nat.mod_eq_of_lt`, `BitVec.toNat_shiftLeft`),
not from a witness chosen in the statement — the statement is a closed
inequality over the index and the block count. -/
theorem sh6_signExtend_toNat_lt {i : BitVec 64} {blocks : Nat}
    (hi : i.toNat < blocks) (hblk : 64 * blocks + 63 < 2 ^ 32) :
    (BitVec.signExtend 64 (sh6 i)).toNat < 2 ^ 63 := by
  have h6 : sh6 i = i <<< 6 := rfl
  rw [h6, BitVec.signExtend_eq]
  rw [BitVec.toNat_shiftLeft]
  have hlt : i.toNat * 2 ^ 6 < 2 ^ 64 := by
    have hb : blocks ≤ 2 ^ 32 := by omega
    have : i.toNat * 64 < 2 ^ 32 * 64 := by
      calc i.toNat * 64 < blocks * 64 := by omega
        _ ≤ 2 ^ 32 * 64 := by omega
    simpa [Nat.pow_succ] using by omega
  rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from by decide,
    Nat.mod_eq_of_lt hlt]
  omega

/-! ### The entry emitter's consequence: the count's growth

The loop's successor needs the count's *room*, not its contents: POS8's post pins
`k' = k + Σ ctpop ent`, and one block's words hold at most sixty-four lanes each,
so the growth is at most `64 * ent.length`.  With the call site's `nblk = 1` and
the record's `nblk.toNat = ent.length` this is `k' ≤ k + 64`, which is what
`cursorRoom`'s successor step consumes. -/

/-- **The entry emitter's count does not outgrow its words.**  A sum of popcounts
is at most sixty-four per word. -/
theorem entryPost_count_le {args : List Value} {mem m : Mem} {v : Value}
    (hpost : entryPos8Post args mem v m) :
    ∃ (k : BitVec 64) (ent : List (BitVec 64)) (k' : Nat),
      v = .int 64 (BitVec.ofNat 64 k') ∧ k' ≤ k.toNat + 64 * ent.length := by
  obtain ⟨e, o, tab, blk0, nblk, k, ent, k', -, hv, hk', -, -⟩ := hpost
  refine ⟨k, ent, k', hv, ?_⟩
  rw [hk']
  have hsum : ∀ (l : List (BitVec 64)), (l.map BitLanes.ctpop).sum ≤ 64 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hx : BitLanes.ctpop x ≤ 64 := by
          rw [BitLanes.ctpop_eq_setLanes_length]
          exact BitLanes.setLanes_length_le x
        have : 64 * (xs.length + 1) = 64 * xs.length + 64 := by omega
        omega
  have := hsum ent
  omega

/-! ### One mask post, six words

The four arm bodies differ in *which* of the mask stage's six words they consume —
the gate-off arms read four, the gate-on arms six — and not in what the stage
wrote.  So the six are named once, here, at the addresses the traces read: the
invariant's five offset conjuncts are the connection between the slots the post
writes (`maskSlot`, `+8` … `+40`) and the fields the builders pass
(`delim`, `inString`, `ws`, `backslash`, `ctl`).  A per-arm projection would
restate this one post four times, and each restatement would be a place for the
four to drift apart. -/

/-- **The mask unit's `post`, at the arm's six words.**  `hargs` and the five
offset equalities are the invariant's: `S.maskSlot`/`S.delim`/… and their
`maskSlot + 8k` forms.  The frame is the post's own, at the store regions. -/
theorem maskWords_of_masksPost {args : List Value} {mem m : Mem}
    {p c maskSlot delim inString ws backslash ctl : Nat}
    (hargs : args = [.ptr p, .ptr c, .ptr maskSlot])
    (hdelim : delim = maskSlot + 8)
    (hin : inString = maskSlot + 16)
    (hws : ws = maskSlot + 24)
    (hbs : backslash = maskSlot + 32)
    (hctl : ctl = maskSlot + 40)
    (hpost : masksPost args mem m) :
    ∃ (lo hi : Block32) (st : ClassState) (opened ppar : Bool),
      readBytes mem p 64 = some (block64 lo hi) ∧
      readBytes m maskSlot 8 = some (natToBytes (specQuote64 lo hi st).toNat 8) ∧
      readBytes m delim 8 = some (natToBytes (specDelimiter64 lo hi st).toNat 8) ∧
      readBytes m inString 8 = some (natToBytes (specInString64 lo hi st).toNat 8) ∧
      readBytes m ws 8 = some (natToBytes (specSpace64 lo hi st).toNat 8) ∧
      readBytes m backslash 8 = some (natToBytes (specBackslash64 lo hi st).toNat 8) ∧
      readBytes m ctl 8 = some (natToBytes (specControl64 lo hi st).toNat 8) ∧
      readBytes m c 24 = some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩))
        (carry64 lo hi st).oddRun (carry64 lo hi st).inside) ∧
      st.oddRun = (opened && ppar) ∧
      (∀ a, ¬ (c ≤ a ∧ a < c + 24) → ¬ (maskSlot ≤ a ∧ a < maskSlot + 48) →
        readByte m a = readByte mem a) := by
  obtain ⟨p', c', o, lo, hi, st, opened, ppar, hargs', hblk, hcarry, hodd, hw1, hw2, hw3,
    hw4, hw5, hw6, hcarry', hframe⟩ := hpost
  have hsame : ([.ptr p, .ptr c, .ptr maskSlot] : List Value) = [.ptr p', .ptr c', .ptr o] :=
    hargs.symm.trans hargs'
  simp only [List.cons.injEq, and_true, Value.ptr.injEq] at hsame
  obtain ⟨rfl, rfl, rfl⟩ := hsame
  refine ⟨lo, hi, st, opened, ppar, hblk, hw1, ?_, ?_, ?_, ?_, ?_, hcarry', hodd, ?_⟩
  · rw [hdelim]; exact hw2
  · rw [hin]; exact hw3
  · rw [hws]; exact hw4
  · rw [hbs]; exact hw5
  · rw [hctl]; exact hw6
  · intro a hc ho
    exact hframe a hc (by simpa using ho)

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
emitter's entry-word clause is not a staging obligation: a precondition the body
creates for itself is the strongest kind of call site there is, and this record's
`e` clause is exactly that — the arm stores the entry word and then hands the
emitter the slot it just wrote. -/
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

/-- **The mask unit's `pre` at a carried carry slot.**  `masksPre_of_window`
states the document's first block, where the slot holds `carrySlot false false
false`.  Every later iteration passes the slot the previous block's mask post
wrote, so the derivation is needed at an arbitrary classifier state and pair of
run flags; the three separations and the block read are the caller's, exactly as
at `masksPre_at`. -/
theorem masksPre_of_carrySlot {mem : Mem} {p sc mk : Nat}
    {lo hi : Block32} {st : ClassState} {opened ppar : Bool}
    (hp : readBytes mem p 64 = some (block64 lo hi))
    (hsc : readBytes mem sc 24 = some (carrySlot opened ppar st.inside))
    (hodd : st.oddRun = (opened && ppar))
    (hpc : p + 64 ≤ sc ∨ sc + 24 ≤ p)
    (hpo : p + 64 ≤ mk ∨ mk + 48 ≤ p)
    (hco : sc + 24 ≤ mk ∨ mk + 48 ≤ sc) :
    Γ_masks.pre [.ptr p, .ptr sc, .ptr mk] mem 0 :=
  ⟨p, sc, mk, lo, hi, st, opened, ppar, rfl, hp, hsc, hodd, hpc, hpo, hco⟩

/-- **The B8 emitter's `pre` at the pipeline's call site, after the store.**  The
same shape as `pos8Pre_of_stored_word` without the staged table: the emitter's
entry-word clause is the body's own store, and the block bound, the separation
and the count's room are the staging's and the invariant's. -/
theorem b8Pre_of_stored_word {mem : Mem} {entw ep : Nat}
    {blk0 k : BitVec 64} {word : BitVec 64}
    (hstored : readBytes mem entw 8 = some (natToBytes word.toNat 8))
    (hblk : 64 * (blk0.toNat + 1) + 63 < 2 ^ 32)
    (hsepWord : entw + 8 ≤ ep ∨ ep + 4 * (k.toNat + 64 + 8) ≤ entw)
    (hroom : k.toNat + 64 + 9 < 2 ^ 63) :
    Γ_entry_b8.pre [.ptr entw, .int 64 blk0, .int 64 (1 : BitVec 64), .ptr ep,
      .int 64 k] mem 0 := by
  refine ⟨entw, ep, blk0, 1, k, [word], rfl, by simp, hblk, ?_, ?_, hroom⟩
  · simpa [wordsOf] using hstored
  · simpa using hsepWord

/-! ### The step's invariant-independent support

The four arm dispatches share three shapes, and none of them is about an arm: a
region pair read off the invariant's separation list, a range preserved from a
unit post's byte-level frame, and the carried block index's arithmetic at the
exit test.  They are stated here so the step itself is a dispatch.

`DisjointRegions` is `List.Pairwise` over a literal list, so a pair is read by
peeling the earlier region into head position and applying the head lemma to the
tail.  `readBytes_of_readByte_eq` is the turn from a post's `readByte` frame to a
range read, and `hasBytes_of_readByte_eq` its presence counterpart; together they
are what lets every unit post's frame preserve the invariant's fixed regions. -/

/-- The tail of a separated region list is separated. -/
theorem disjointRegions_tail {r : Nat × Nat} {rs : List (Nat × Nat)}
    (h : DisjointRegions (r :: rs)) : DisjointRegions rs :=
  (List.pairwise_cons.mp h).2

/-- The head of a separated region list is separated from every later region. -/
theorem disjointRegions_head {r s : Nat × Nat} {rs : List (Nat × Nat)}
    (h : DisjointRegions (r :: rs)) (hs : s ∈ rs) :
    r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 :=
  (List.pairwise_cons.mp h).1 s hs

/-- A byte of a range disjoint from a region is outside it: the range lies
entirely before the region or entirely after it. -/
theorem not_inside_of_disjoint {a n x w k : Nat}
    (h : a + n ≤ x ∨ x + w ≤ a) (hk : k < n) :
    ¬ (x ≤ a + k ∧ a + k < x + w) := by
  rintro ⟨h1, h2⟩
  omega

/-- Two memories that agree byte for byte over a range read the same range. -/
theorem readBytes_of_readByte_eq {m m' : Mem} {a n : Nat}
    (h : ∀ k, k < n → readByte m' (a + k) = readByte m (a + k)) :
    readBytes m' a n = readBytes m a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      have h0 : readByte m' a = readByte m a := by simpa using h 0 (by omega)
      simp only [readBytes]
      rw [h0]
      cases readByte m a with
      | none => rfl
      | some b =>
          rw [ih (a := a + 1) (fun k hk => by
            rw [show a + 1 + k = a + (k + 1) from by omega]
            exact h (k + 1) (by omega))]

/-- Presence is a byte-level fact: a range present in one memory is present in
another that agrees with it byte for byte over the range.  This is how a unit
post's frame carries the invariant's capacity clause across a call. -/
theorem hasBytes_of_readByte_eq {m m' : Mem} {a K : Nat} (h : HasBytes m a K)
    (heq : ∀ k, k < K → readByte m' (a + k) = readByte m (a + k)) :
    HasBytes m' a K := by
  obtain ⟨vs, hvs⟩ := h
  exact ⟨vs, by rw [readBytes_of_readByte_eq heq, hvs]⟩

/-- A present range has every shorter prefix present: the shorter read is the
longer read's take. -/
theorem hasBytes_of_le {m : Mem} {a K n : Nat} (h : HasBytes m a K) (hn : n ≤ K) :
    HasBytes m a n := by
  obtain ⟨vs, hvs⟩ := h
  refine ⟨vs.take n, ?_⟩
  have hK : readBytes m a K = readBytes m a (n + (K - n)) := by
    rw [Nat.add_sub_cancel' hn]
  rw [hK] at hvs
  exact (readBytes_split m a n (K - n) hvs).1

/-- The low `64`-bit reading of a `Nat` below the address bound. -/
theorem ofNat64_toNat {m : Nat} (h : m < 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The arm's block offset.**  `%shl = shl i, 6` with `%i = ofNat 64 m` reads
back as the document offset `64 * m` while that product fits the address word.
The pipeline's block bound (`64 * blocks + 63 < 2 ^ 32`) and `m < blocks` are
what make the hypothesis hold at the call site. -/
theorem sh6_ofNat_toNat {m : Nat} (h : m * 64 < 2 ^ 64) :
    (BitVec.signExtend 64 (sh6 (BitVec.ofNat 64 m))).toNat = 64 * m := by
  have h6 : sh6 (BitVec.ofNat 64 m) = BitVec.ofNat 64 m <<< 6 := rfl
  rw [h6, BitVec.signExtend_eq]
  rw [BitVec.toNat_shiftLeft]
  have hlt : (BitVec.ofNat 64 m).toNat * 2 ^ 6 < 2 ^ 64 := by
    rw [ofNat64_toNat (by omega)]
    simpa using h
  rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from by decide, Nat.mod_eq_of_lt hlt]
  rw [ofNat64_toNat (by omega)]
  omega

/-- The successor's block index: the arm increments `%i` by one, and the
sixty-four-bit word and the `Nat` stay in step while the index is below the
address bound. -/
theorem vinc_ofNat {m : Nat} (h : m + 1 < 2 ^ 64) :
    vinc (BitVec.ofNat 64 m) = BitVec.ofNat 64 (m + 1) := by
  unfold vinc
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hone : (one : BitVec 64).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64), Nat.mod_eq_of_lt h]

/-- The exit test at its one value: the arm's increment reached the bound, so the
step takes the cleanup successor.  The `r = 0` side of the dispatch reads this,
and its negation reads the self-loop. -/
theorem vexit_eq_one {i shr : BitVec 64} : vexit i shr = 1 ↔ vinc i = shr := by
  by_cases h : vinc i = shr <;> simp [vexit, evalICmp, h]

/-- The exit test at its zero value: the arm's increment is short of the bound,
so the step returns to the arm's head. -/
theorem vexit_eq_zero {i shr : BitVec 64} : vexit i shr = 0 ↔ vinc i ≠ shr := by
  by_cases h : vinc i = shr <;> simp [vexit, evalICmp, h]

/-- `ofNat` is injective below the word's bound: the arm's exit test compares two
`Nat`s through their sixty-four-bit forms, and this is what turns the comparison
back into an equation of counts. -/
theorem ofNat64_eq_iff {m n : Nat} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 m = BitVec.ofNat 64 n ↔ m = n := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [ofNat64_toNat hm, ofNat64_toNat hn] using this
  · intro h; rw [h]

/-! ### Axiom footprints

The call-site derivations are records' conjunctions and one store read; none adds
a carrier. -/

/-- info: 'LeanLLVM.Vellum.escapePre_of_staged_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePre_of_staged_window

/-- info: 'LeanLLVM.Vellum.pos8Pre_of_stored_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pos8Pre_of_stored_word

/-- info: 'LeanLLVM.Vellum.pos8PreAt_of_stored_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pos8PreAt_of_stored_word

/-- info: 'LeanLLVM.Vellum.maskWords_of_masksPost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms maskWords_of_masksPost

/-- info: 'LeanLLVM.Vellum.entryPost_count_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entryPost_count_le

/-- info: 'LeanLLVM.Vellum.sh6_signExtend_toNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sh6_signExtend_toNat_lt

/-- info: 'LeanLLVM.Vellum.disjointRegions_tail' does not depend on any axioms -/
#guard_msgs in
#print axioms disjointRegions_tail

/-- info: 'LeanLLVM.Vellum.disjointRegions_head' does not depend on any axioms -/
#guard_msgs in
#print axioms disjointRegions_head

/-- info: 'LeanLLVM.Vellum.not_inside_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_inside_of_disjoint

/-- info: 'LeanLLVM.Vellum.readBytes_of_readByte_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_of_readByte_eq

/-- info: 'LeanLLVM.Vellum.hasBytes_of_readByte_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_of_readByte_eq

/-- info: 'LeanLLVM.Vellum.hasBytes_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_of_le

/-- info: 'LeanLLVM.Vellum.ofNat64_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofNat64_toNat

/-- info: 'LeanLLVM.Vellum.sh6_ofNat_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sh6_ofNat_toNat

/-- info: 'LeanLLVM.Vellum.vinc_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vinc_ofNat

/-- info: 'LeanLLVM.Vellum.vexit_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vexit_eq_one

/-- info: 'LeanLLVM.Vellum.vexit_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vexit_eq_zero

/-- info: 'LeanLLVM.Vellum.ofNat64_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ofNat64_eq_iff

end LeanLLVM.Vellum
