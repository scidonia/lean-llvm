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
open LeanLLVM.Vellum.JsonEntryIR (pos8Table wordsOf readLanes32 streamPrefix)
open LeanLLVM.Vellum.JsonPipelineIR (Γ_entry_pos8at pipelineBody PipelineUnits
  pipelineCalls masksSym entryPos8Sym entryB8Sym escapeListSym)
open LeanLLVM.Vellum.JsonPipelineBlockEval (sh6 vinc one vexit vent)
open LeanLLVM.Vellum.BlockEval (stateAt cells)
open LeanLLVM.Vellum.JsonPipelineBlockEval (pUsUs findBlock_usus usUsIn usUsOut usUs_denote)

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

/-! ### The arm dispatch, decided

`usUs_step_at` … `body_step_at` conclude a *disjunction* of successors, because
they do not know the exit test's value.  A loop step does: the budget and the
block index settle it, since `%shr` is the block count and `%inc` the index plus
one.  The eight lemmas below are those four with the test's value supplied, so
the step reaches the successor it has already decided on rather than splitting
and discarding one branch.  Each pair is the arm at `vexit = 0` (the self-loop)
and at `vexit = 1` (the cleanup). -/

/-- **`for.body.us.us` delays at its head** when the exit test is zero. -/
theorem usUs_step_at_head (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us.us")
    (hagree : AgreeOn (blockUses pUsUs)
      (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUsUs.instrs
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 0) :
    ∃ (t' : State) (j : Nat), j ≤ 1 ∧
      denoteCode calls pUsUs.instrs s = some t' ∧
      AgreeOn (blockUses pUsUs)
        (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret) { s with mem := m'.mem, next := m'.next }) t' ∧
      ∀ k, runFuel calls (j + k) pipelineBody s =
        runFuel calls k pipelineBody { t' with pc := "for.body.us.us", pre := some s.pc } := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUsUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUsUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond116.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond116.not" (by
      simp only [blockUses, pUsUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usUsOut, cells, lookupName]
    simp +decide
  refine ⟨t', 1, Nat.le_refl 1, ht', hag, fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.body.us.us", pre := some s.pc } := by
    refine step_of_blocks (b := pUsUs) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_usus
    · exact ht'
    · rw [pUsUs_term]
      have h := PipelineBodyFacts.execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond116.not")
        (t := "for.cond.cleanup") (f := "for.body.us.us")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body.us.us` leaves for the cleanup** when the exit test is one. -/
theorem usUs_step_at_exit (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us.us")
    (hagree : AgreeOn (blockUses pUsUs)
      (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUsUs.instrs
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 1) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "for.cond.cleanup" ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUsUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUsUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond116.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond116.not" (by
      simp only [blockUses, pUsUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usUsOut, cells, lookupName]
    simp +decide
  refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1, rfl,
    fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
    refine step_of_blocks (b := pUsUs) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_usus
    · exact ht'
    · rw [pUsUs_term]
      have h := PipelineBodyFacts.execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond116.not")
        (t := "for.cond.cleanup") (f := "for.body.us.us")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body.us` delays at its head** when the exit test is zero. -/
theorem us_step_at_head (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body.us")
    (hagree : AgreeOn (blockUses pUs)
      (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs.instrs
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 0) :
    ∃ (t' : State) (j : Nat), j ≤ 1 ∧
      denoteCode calls pUs.instrs s = some t' ∧
      AgreeOn (blockUses pUs)
        (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret) { s with mem := m'.mem, next := m'.next }) t' ∧
      ∀ k, runFuel calls (j + k) pipelineBody s =
        runFuel calls k pipelineBody { t' with pc := "for.body.us", pre := some s.pc } := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond115.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond115.not" (by
      simp only [blockUses, pUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usOut, cells, lookupName]
    simp +decide
  refine ⟨t', 1, Nat.le_refl 1, ht', hag, fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.body.us", pre := some s.pc } := by
    refine step_of_blocks (b := pUs) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_us
    · exact ht'
    · rw [pUs_term]
      have h := PipelineBodyFacts.execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond115.not")
        (t := "for.cond.cleanup") (f := "for.body.us")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body.us` leaves for the cleanup** when the exit test is one. -/
theorem us_step_at_exit (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body.us")
    (hagree : AgreeOn (blockUses pUs)
      (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs.instrs
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 1) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "for.cond.cleanup" ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond115.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond115.not" (by
      simp only [blockUses, pUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usOut, cells, lookupName]
    simp +decide
  refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1, rfl,
    fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
    refine step_of_blocks (b := pUs) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_us
    · exact ht'
    · rw [pUs_term]
      have h := PipelineBodyFacts.execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond115.not")
        (t := "for.cond.cleanup") (f := "for.body.us")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body.us83` delays at its head** when the exit test is zero. -/
theorem us83_step_at_head (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us83")
    (hagree : AgreeOn (blockUses pUs83)
      (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs83.instrs
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 0) :
    ∃ (t' : State) (j : Nat), j ≤ 1 ∧
      denoteCode calls pUs83.instrs s = some t' ∧
      AgreeOn (blockUses pUs83)
        (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret) { s with mem := m'.mem, next := m'.next }) t' ∧
      ∀ k, runFuel calls (j + k) pipelineBody s =
        runFuel calls k pipelineBody { t' with pc := "for.body.us83", pre := some s.pc } := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs83.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs83 hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond114.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond114.not" (by
      simp only [blockUses, pUs83_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, us83Out, cells, lookupName]
    simp +decide
  refine ⟨t', 1, Nat.le_refl 1, ht', hag, fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.body.us83", pre := some s.pc } := by
    refine step_of_blocks (b := pUs83) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_us83
    · exact ht'
    · rw [pUs83_term]
      have h := PipelineBodyFacts.execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond114.not")
        (t := "for.cond.cleanup") (f := "for.body.us83")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body.us83` leaves for the cleanup** when the exit test is one. -/
theorem us83_step_at_exit (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us83")
    (hagree : AgreeOn (blockUses pUs83)
      (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs83.instrs
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 1) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "for.cond.cleanup" ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs83.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs83 hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond114.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond114.not" (by
      simp only [blockUses, pUs83_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, us83Out, cells, lookupName]
    simp +decide
  refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1, rfl,
    fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
    refine step_of_blocks (b := pUs83) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_us83
    · exact ht'
    · rw [pUs83_term]
      have h := PipelineBodyFacts.execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond114.not")
        (t := "for.cond.cleanup") (f := "for.body.us83")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body` delays at its head** when the exit test is zero. -/
theorem body_step_at_head (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body")
    (hagree : AgreeOn (blockUses pBody)
      (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pBody.instrs
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 0) :
    ∃ (t' : State) (j : Nat), j ≤ 1 ∧
      denoteCode calls pBody.instrs s = some t' ∧
      AgreeOn (blockUses pBody)
        (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret) { s with mem := m'.mem, next := m'.next }) t' ∧
      ∀ k, runFuel calls (j + k) pipelineBody s =
        runFuel calls k pipelineBody { t' with pc := "for.body", pre := some s.pc } := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pBody.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pBody hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond.not" (by
      simp only [blockUses, pBody_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, bodyOut, cells, lookupName]
    simp +decide
  refine ⟨t', 1, Nat.le_refl 1, ht', hag, fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.body", pre := some s.pc } := by
    refine step_of_blocks (b := pBody) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_body
    · exact ht'
    · rw [pBody_term]
      have h := PipelineBodyFacts.execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond.not")
        (t := "for.cond.cleanup") (f := "for.body")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- **`for.body` leaves for the cleanup** when the exit test is one. -/
theorem body_step_at_exit (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body")
    (hagree : AgreeOn (blockUses pBody)
      (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pBody.instrs
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }))
    (hb : vexit inc shr = 1) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "for.cond.cleanup" ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pBody.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pBody hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond.not" (by
      simp only [blockUses, pBody_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, bodyOut, cells, lookupName]
    simp +decide
  refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1, rfl,
    fun k => ?_⟩
  have hstep : step calls pipelineBody s =
      .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
    refine step_of_blocks (b := pBody) (s' := t') ?_ ?_ ?_
    · simpa only [hpc] using findBlock_body
    · exact ht'
    · rw [pBody_term]
      have h := PipelineBodyFacts.execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond.not")
        (t := "for.cond.cleanup") (f := "for.body")
        (by simp only [evalOperand, hval, hb])
      simpa only [hpc'] using h
  exact runFuel_one_of_step hstep k

/-- One byte outside the arm's two call regions and the body's own store reads
the same after the iteration.  The mask post's frame covers the two regions it
writes, the entry post's the span its emitter wrote, and the body's store the
eight bytes at the entry slot; a byte outside all four is untouched. -/
theorem step_readByte_arm {s r1 r2 : Mem} {sc mk entw ep : Nat} {bs : List UInt8}
    {k' : Nat}
    (hmask : ∀ a, ¬ (sc ≤ a ∧ a < sc + 24) → ¬ (mk ≤ a ∧ a < mk + 48) →
      readByte r1 a = readByte s a)
    (hentry : ∀ a, a < ep ∨ ep + 4 * (k' + 8) ≤ a →
      readByte r2 a = readByte (writeBytes r1 entw bs) a)
    {a : Nat} (hsc : ¬ (sc ≤ a ∧ a < sc + 24)) (hmk : ¬ (mk ≤ a ∧ a < mk + 48))
    (hent : a < ep ∨ ep + 4 * (k' + 8) ≤ a)
    (hw : a < entw ∨ entw + bs.length ≤ a) :
    readByte r2 a = readByte s a := by
  rw [hentry a hent, readByte_writeBytes_outside r1 bs hw, hmask a hsc hmk]

/-- The range form of `step_readByte_arm`. -/
theorem step_readBytes_arm {s r1 r2 : Mem} {sc mk entw ep : Nat} {bs : List UInt8}
    {k' : Nat} {a n : Nat}
    (hmask : ∀ a, ¬ (sc ≤ a ∧ a < sc + 24) → ¬ (mk ≤ a ∧ a < mk + 48) →
      readByte r1 a = readByte s a)
    (hentry : ∀ a, a < ep ∨ ep + 4 * (k' + 8) ≤ a →
      readByte r2 a = readByte (writeBytes r1 entw bs) a)
    (hsc : ∀ k, k < n → ¬ (sc ≤ a + k ∧ a + k < sc + 24))
    (hmk : ∀ k, k < n → ¬ (mk ≤ a + k ∧ a + k < mk + 48))
    (hent : ∀ k, k < n → (a + k < ep ∨ ep + 4 * (k' + 8) ≤ a + k))
    (hw : ∀ k, k < n → (a + k < entw ∨ entw + bs.length ≤ a + k)) :
    readBytes r2 a n = readBytes s a n :=
  readBytes_of_readByte_eq (fun k hk =>
    step_readByte_arm hmask hentry (hsc k hk) (hmk k hk) (hent k hk) (hw k hk))

/-! ### The two calls, at one block

Both are here rather than in each arm because all four copies make them at the
same arguments: the mask unit at the block's staged address, and the entry
emitter at the word the body has just stored.  What the arms differ in is which
emitter, and whether the escape list is called at all. -/

/-- **The mask call at the loop's block.**  The four arm bodies pass the same
three arguments, so the dispatch reads one derivation: the block's bytes from
the staged window, the carry slot the invariant carries, the three separations
from the staged regions, and the six words the post writes — at the arm's own
read addresses, through the five offset equalities. -/
theorem maskCall_at (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried}
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hcnt : 64 * blocks + 63 < 2 ^ 32)
    (hdoc : S.doc.length = 64 * blocks)
    (hdelim : S.delim = S.maskSlot + 8) (hinS : S.inString = S.maskSlot + 16)
    (hwsS : S.ws = S.maskSlot + 24) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40)
    (hdist : (S.b + 64 * S.i + 64 ≤ S.sc ∨ S.sc + 24 ≤ S.b + 64 * S.i) ∧
      (S.b + 64 * S.i + 64 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b + 64 * S.i) ∧
      (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc)) :
    ∃ (lo hi : Block32) (st : ClassState) (r1 : CallOutcome),
      pipelineCalls tab base s2 masksSym
        [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc, .ptr S.maskSlot]
        s.mem s.next = some r1 ∧
      readBytes r1.mem S.maskSlot 8 = some (natToBytes (specQuote64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.delim 8 = some (natToBytes (specDelimiter64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.inString 8 = some (natToBytes (specInString64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.ws 8 = some (natToBytes (specSpace64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.backslash 8 = some (natToBytes (specBackslash64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.ctl 8 = some (natToBytes (specControl64 lo hi st).toNat 8) ∧
      readBytes r1.mem S.sc 24 =
        some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi st).oddRun
          (carry64 lo hi st).inside) ∧
      (∀ a, ¬ (S.sc ≤ a ∧ a < S.sc + 24) → ¬ (S.maskSlot ≤ a ∧ a < S.maskSlot + 48) →
        readByte r1.mem a = readByte s.mem a) := by
  have haddr : S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat = S.b + 64 * S.i := by
    rw [hiw, sh6_ofNat_toNat (by omega)]
  obtain ⟨lo, hi, hblk⟩ := blockRead_of_window (mem := s.mem) (b := S.b)
    (blocks := blocks) (bs := S.doc) (pad := []) (m := S.i) (by simpa using hwin)
    (by simpa using hdoc) hilt
  -- the carry state the slot describes: its two fields are the slot's own
  have hpre : Γ_masks.pre
      [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc, .ptr S.maskSlot]
      s.mem s.next := by
    rw [haddr]
    exact masksPre_of_carrySlot (st := ⟨S.inside, S.opened && S.ppar⟩) hblk hsc rfl
      hdist.1 hdist.2.1 hdist.2.2
  obtain ⟨r1, hcall, hpost, -⟩ := units.masks _ s.mem s.next hpre
  have hpostM : masksPost
      [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc, .ptr S.maskSlot]
      s.mem r1.mem := hpost
  obtain ⟨lo', hi', st, opened, ppar, -, hw1, hw2, hw3, hw4, hw5, hw6, hcarrySlot, -, hframe⟩ :=
    maskWords_of_masksPost (p := S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat)
      (c := S.sc) (maskSlot := S.maskSlot) (hargs := rfl) hdelim hinS hwsS hbsS hctl hpostM
  exact ⟨lo', hi', st, r1, hcall, hw1, hw2, hw3, hw4, hw5, hw6, hcarrySlot, hframe⟩

/-- The emitter's stream read returns one lane per requested block slot, so a
`k'` in the post is pinned to the stream's own length. -/
theorem step_readLanes32_length (m : Mem) (a : Nat) :
    ∀ (n : Nat) {l : List Nat}, readLanes32 m a n = some l → l.length = n
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      rfl
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m a 4 with
      | none =>
          simp only [hb, Option.bind_none] at h
          cases h
      | some bs =>
          cases hr : readLanes32 m (a + 4) n with
          | none =>
              simp only [hb, hr, Option.bind_some, Option.map_none,
                Option.bind_none] at h
              cases h
          | some rest =>
              simp only [hb, hr, Option.bind_some, Option.map_some,
                Option.some.injEq] at h
              subst h
              simp [step_readLanes32_length m (a + 4) n hr]

/-- A block's position list is at most one lane per bit. -/
theorem step_positionsOf_length (m : BitVec 64) (base : Nat) :
    (positionsOf m base).length ≤ 64 := by
  simp only [positionsOf, List.length_map]
  exact BitLanes.setLanes_length_le m

/-- The stream after one block is one word's positions. -/
theorem step_streamPrefix_length_one (ent : List (BitVec 64)) (blk0 : Nat) :
    (streamPrefix ent blk0 1).length ≤ 64 := by
  rw [streamPrefix]
  cases ent with
  | nil => simp
  | cons e es =>
      rw [show (e :: es).take 1 = [e] from rfl]
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.flatten_cons,
        List.flatten_nil, List.length_append, List.length_singleton, Nat.add_zero]
      exact step_positionsOf_length e (64 * blk0)


/-- The entry call's argument list read back: the six values the record names. -/
theorem entryArgs_six {e0 o0 t0 : Nat} {b0 one0 k0 : BitVec 64}
    {e o t : Nat} {blk0 nblk k : BitVec 64}
    (h : ([.ptr e0, .int 64 b0, .int 64 one0, .ptr o0, .int 64 k0] ++ [.ptr t0] :
        List Value) =
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr t]) :
    e = e0 ∧ blk0 = b0 ∧ nblk = one0 ∧ o = o0 ∧ k = k0 ∧ t = t0 := by
  have h' : ([.ptr e0, .int 64 b0, .int 64 one0, .ptr o0, .int 64 k0, .ptr t0] :
      List Value) = [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr t] := h
  simp only [List.cons.injEq, List.nil_eq, Value.ptr.injEq, Value.int.injEq,
    and_true, HEq] at h'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h'
  exact ⟨h1.symm, (eq_of_heq h2.2).symm, (eq_of_heq h3.2).symm, h4.symm,
    (eq_of_heq h5.2).symm, h6.symm⟩

/-- **The POS8 entry call at the loop's block**, after the body's own store.  The
record's `pre` is the emitter's five arguments plus the staged table; the
`readBytes` at the entry slot is the body's own store, so it is a fact the arm
creates rather than a staging obligation.  The post is returned as the record
states it: the count's growth bound is the caller's to read out of
`streamPrefix`, whose one-block stream is a single word's positions. -/
theorem pos8Call_at (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {S : PipelineLoopCarried}
    {r1 : CallOutcome} {blocks : Nat} {lo hi : Block32} {st : ClassState}
    (htabEq : S.tab = tab)
    (hstored : readBytes (writeBytes r1.mem S.entw (natToBytes
      (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8))
    (htab : readBytes (writeBytes r1.mem S.entw (natToBytes
      (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) S.tab 8192 =
      some pos8Table)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hib : S.i + 1 ≤ blocks)
    (hcnt : 64 * blocks + 63 < 2 ^ 32)
    (hkw : S.kw = BitVec.ofNat 64 S.k) (hk64 : S.k < 2 ^ 64)
    (hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw)
    (hsepTab : S.tab + 8192 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.tab)
    (hroom : S.k + 64 + 9 < 2 ^ 63) :
    ∃ (r2 : CallOutcome) (k' o : Nat),
      pipelineCalls tab base s2 entryPos8Sym
        [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
        (writeBytes r1.mem S.entw (natToBytes
          (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
            (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) r1.next = some r2 ∧
      r2.ret = .int 64 (BitVec.ofNat 64 k') ∧
      (∀ a, a < o ∨ o + 4 * (k' + 8) ≤ a →
        readByte r2.mem a = readByte (writeBytes r1.mem S.entw (natToBytes
          (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
            (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) a) ∧
      o = S.ep ∧
      k' ≤ S.k + 64 := by
  have hblkP : 64 * (S.iw.toNat + 1) + 63 < 2 ^ 32 := by
    rw [hiw, ofNat64_toNat (by omega)]
    omega
  have hk0 : S.kw.toNat = S.k := by rw [hkw, ofNat64_toNat hk64]
  have htab' : readBytes (writeBytes r1.mem S.entw (natToBytes
      (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) tab 8192 =
      some pos8Table := by
    rw [← htabEq]; exact htab
  have hpre : (Γ_entry_pos8at tab).pre
      [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
      (writeBytes r1.mem S.entw (natToBytes
        (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) r1.next := by
    refine pos8PreAt_of_stored_word (entw := S.entw) (ep := S.ep) (tab := tab)
      (blk0 := S.iw) (k := S.kw) (word := vent S.n S.iw (specQuote64 lo hi st)
        (specDelimiter64 lo hi st) (specInString64 lo hi st) (specSpace64 lo hi st) S.sw)
      (outCap := S.k + 64 + 9) hstored htab' hblkP ?_ ?_ ?_ ?_
    · rw [hk0]; exact hsepWord
    · rw [hk0, ← htabEq]; exact hsepTab
    · rw [hk0]; omega
    · rw [hk0]; exact hroom
  obtain ⟨r2, hcall, hpost, -⟩ := units.pos8 _ _ r1.next hpre
  have hpost' : entryPos8Post
      ([.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw] ++
        [.ptr tab])
      (writeBytes r1.mem S.entw (natToBytes
        (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8))
      r2.ret r2.mem := by
    simpa only [Γ_entry_pos8at, Γ_entry_pos8] using hpost
  obtain ⟨e, o, t, blk0, nblk, k, ent, k', hargs, hv, hk', hread, hframe⟩ := hpost'
  obtain ⟨-, -, hnblk, ho, hk, -⟩ := entryArgs_six hargs
  have hkn : k.toNat = S.k := by rw [hk]; exact hk0
  have hklen : k' - k.toNat ≤ 64 := by
    have hl := step_readLanes32_length r2.mem (o + 4 * k.toNat) (k' - k.toNat) hread
    have hb := step_streamPrefix_length_one ent blk0.toNat
    rw [hnblk, show ((1 : BitVec 64)).toNat = 1 from by decide] at hl
    omega
  have hge : k.toNat ≤ k' := by rw [hk']; omega
  refine ⟨r2, k', o, hcall, hv, hframe, ho, ?_⟩
  rw [← hkn]
  omega


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

/-! ### Axiom footprints

The decided dispatch is the four transported traces with the test's value
supplied, so it adds nothing to `PipelineBodyFacts`' own footprint.  The two
call-site derivations are one record conjunction and one record's frame; their
`Classical.choice` is the bitvector shift arithmetic `sh6_ofNat_toNat` uses
(`BitVec.toNat_shiftLeft`, `Nat.shiftLeft_eq`, `Nat.mod_eq_of_lt`), named here
because a pin that records a carrier without saying where it came from hides a
choice behind a number. -/

/-- info: 'LeanLLVM.Vellum.usUs_step_at_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUs_step_at_head

/-- info: 'LeanLLVM.Vellum.usUs_step_at_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUs_step_at_exit

/-- info: 'LeanLLVM.Vellum.us_step_at_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us_step_at_head

/-- info: 'LeanLLVM.Vellum.us_step_at_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us_step_at_exit

/-- info: 'LeanLLVM.Vellum.us83_step_at_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us83_step_at_head

/-- info: 'LeanLLVM.Vellum.us83_step_at_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us83_step_at_exit

/-- info: 'LeanLLVM.Vellum.body_step_at_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_step_at_head

/-- info: 'LeanLLVM.Vellum.body_step_at_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_step_at_exit

/-- info: 'LeanLLVM.Vellum.step_readByte_arm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_readByte_arm

/-- info: 'LeanLLVM.Vellum.step_readBytes_arm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_readBytes_arm

/-- info: 'LeanLLVM.Vellum.maskCall_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms maskCall_at

/-- info: 'LeanLLVM.Vellum.step_readLanes32_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_readLanes32_length

/-- info: 'LeanLLVM.Vellum.step_positionsOf_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms step_positionsOf_length

/-- info: 'LeanLLVM.Vellum.step_streamPrefix_length_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_streamPrefix_length_one

/-- info: 'LeanLLVM.Vellum.entryArgs_six' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entryArgs_six

/-- info: 'LeanLLVM.Vellum.pos8Call_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pos8Call_at

end LeanLLVM.Vellum

