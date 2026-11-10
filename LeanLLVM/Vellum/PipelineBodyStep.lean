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
open LeanLLVM.Vellum.JsonPipelineBlockEval (sh6 vinc one vexit vent vshr13)
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
      readBytes mem c 24 = some (carrySlot opened ppar st.inside) ∧
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
  refine ⟨lo, hi, st, opened, ppar, hblk, hcarry, hw1, ?_, ?_, ?_, ?_, ?_, hcarry', hodd, ?_⟩
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

/-! ### The staged region list, as one name -/

abbrev stagedRegions (S : PipelineLoopCarried) (blocks : Nat) : List (Nat × Nat) :=
  [(S.b, 64 * blocks), (S.tab, 8192), (S.sc, 24), (S.maskSlot, 48),
   (S.entw, 8), (S.ep, 4 * (S.k0 + 64 * blocks + 9)), (S.nxp, 8),
   (S.xp, 4 * S.xpExtent), (S.xcarry, 16)]

structure StagedSep (S : PipelineLoopCarried) (blocks : Nat) : Prop where
  win_tab : S.b + 64 * blocks ≤ S.tab ∨ S.tab + 8192 ≤ S.b
  win_sc : S.b + 64 * blocks ≤ S.sc ∨ S.sc + 24 ≤ S.b
  win_mk : S.b + 64 * blocks ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b
  win_ent : S.b + 64 * blocks ≤ S.entw ∨ S.entw + 8 ≤ S.b
  win_ep : S.b + 64 * blocks ≤ S.ep ∨ S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.b
  win_nxp : S.b + 64 * blocks ≤ S.nxp ∨ S.nxp + 8 ≤ S.b
  win_xp : S.b + 64 * blocks ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.b
  win_xc : S.b + 64 * blocks ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.b
  tab_sc : S.tab + 8192 ≤ S.sc ∨ S.sc + 24 ≤ S.tab
  tab_mk : S.tab + 8192 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.tab
  tab_ent : S.tab + 8192 ≤ S.entw ∨ S.entw + 8 ≤ S.tab
  tab_ep : S.tab + 8192 ≤ S.ep ∨ S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.tab
  tab_nxp : S.tab + 8192 ≤ S.nxp ∨ S.nxp + 8 ≤ S.tab
  tab_xp : S.tab + 8192 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.tab
  tab_xc : S.tab + 8192 ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.tab
  sc_mk : S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc
  sc_ent : S.sc + 24 ≤ S.entw ∨ S.entw + 8 ≤ S.sc
  sc_ep : S.sc + 24 ≤ S.ep ∨ S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.sc
  sc_nxp : S.sc + 24 ≤ S.nxp ∨ S.nxp + 8 ≤ S.sc
  sc_xp : S.sc + 24 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.sc
  sc_xc : S.sc + 24 ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.sc
  mk_ent : S.maskSlot + 48 ≤ S.entw ∨ S.entw + 8 ≤ S.maskSlot
  mk_ep : S.maskSlot + 48 ≤ S.ep ∨ S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.maskSlot
  mk_nxp : S.maskSlot + 48 ≤ S.nxp ∨ S.nxp + 8 ≤ S.maskSlot
  mk_xp : S.maskSlot + 48 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.maskSlot
  mk_xc : S.maskSlot + 48 ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.maskSlot
  ent_ep : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.entw
  ent_nxp : S.entw + 8 ≤ S.nxp ∨ S.nxp + 8 ≤ S.entw
  ent_xp : S.entw + 8 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.entw
  ent_xc : S.entw + 8 ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.entw
  ep_nxp : S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.nxp ∨ S.nxp + 8 ≤ S.ep
  ep_xp : S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.ep
  ep_xc : S.ep + 4 * (S.k0 + 64 * blocks + 9) ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.ep
  nxp_xp : S.nxp + 8 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.nxp
  nxp_xc : S.nxp + 8 ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.nxp
  xp_xc : S.xp + 4 * S.xpExtent ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.xp

theorem stagedSep {S : PipelineLoopCarried} {blocks : Nat}
    (h : DisjointRegions (stagedRegions S blocks)) : StagedSep S blocks where
  win_tab := disjointRegions_head (s := (S.tab, 8192)) h (by simp)
  win_sc := disjointRegions_head (s := (S.sc, 24)) h (by simp)
  win_mk := disjointRegions_head (s := (S.maskSlot, 48)) h (by simp)
  win_ent := disjointRegions_head (s := (S.entw, 8)) h (by simp)
  win_ep := disjointRegions_head (s := (S.ep, 4 * (S.k0 + 64 * blocks + 9))) h (by simp)
  win_nxp := disjointRegions_head (s := (S.nxp, 8)) h (by simp)
  win_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent)) h (by simp)
  win_xc := disjointRegions_head (s := (S.xcarry, 16)) h (by simp)
  tab_sc := disjointRegions_head (s := (S.sc, 24))
    (disjointRegions_tail h) (by simp)
  tab_mk := disjointRegions_head (s := (S.maskSlot, 48))
    (disjointRegions_tail h) (by simp)
  tab_ent := disjointRegions_head (s := (S.entw, 8))
    (disjointRegions_tail h) (by simp)
  tab_ep := disjointRegions_head (s := (S.ep, 4 * (S.k0 + 64 * blocks + 9)))
    (disjointRegions_tail h) (by simp)
  tab_nxp := disjointRegions_head (s := (S.nxp, 8))
    (disjointRegions_tail h) (by simp)
  tab_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail h) (by simp)
  tab_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail h) (by simp)
  sc_mk := disjointRegions_head (s := (S.maskSlot, 48))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  sc_ent := disjointRegions_head (s := (S.entw, 8))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  sc_ep := disjointRegions_head (s := (S.ep, 4 * (S.k0 + 64 * blocks + 9)))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  sc_nxp := disjointRegions_head (s := (S.nxp, 8))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  sc_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  sc_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail h)) (by simp)
  mk_ent := disjointRegions_head (s := (S.entw, 8))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h))) (by simp)
  mk_ep := disjointRegions_head (s := (S.ep, 4 * (S.k0 + 64 * blocks + 9)))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h))) (by simp)
  mk_nxp := disjointRegions_head (s := (S.nxp, 8))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h))) (by simp)
  mk_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h))) (by simp)
  mk_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h))) (by simp)
  ent_ep := disjointRegions_head (s := (S.ep, 4 * (S.k0 + 64 * blocks + 9)))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail h)))) (by simp)
  ent_nxp := disjointRegions_head (s := (S.nxp, 8))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail h)))) (by simp)
  ent_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail h)))) (by simp)
  ent_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail h)))) (by simp)
  ep_nxp := disjointRegions_head (s := (S.nxp, 8))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail h))))) (by simp)
  ep_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail h))))) (by simp)
  ep_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail h))))) (by simp)
  nxp_xp := disjointRegions_head (s := (S.xp, 4 * S.xpExtent))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h)))))) (by simp)
  nxp_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail h)))))) (by simp)
  xp_xc := disjointRegions_head (s := (S.xcarry, 16))
    (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
      (disjointRegions_tail (disjointRegions_tail (disjointRegions_tail
        (disjointRegions_tail h))))))) (by simp)

/-- A separation, read in the other order: the regions the staged list names in
address order are also read from the region the arm preserves. -/
theorem sep_comm {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) : b + m ≤ a ∨ a + n ≤ b :=
  h.symm

/-- A sub-range of a separated region is separated from the region's partner. -/
theorem disjoint_of_sub {a' n' a n x w : Nat} (hle : a ≤ a') (hhi : a' + n' ≤ a + n)
    (h : a + n ≤ x ∨ x + w ≤ a) : a' + n' ≤ x ∨ x + w ≤ a' := by
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)


/-! ### Range preservation through an arm's writes -/

/-- A range preserved through the mask unit's two store regions, the body's own
store, and the entry emitter's frame. -/
theorem readBytes_mask_store_entry {s r1 r2 : Mem} {sc mk entw ep ext : Nat}
    {bs : List UInt8} {a n : Nat}
    (hmask : ∀ x, ¬ (sc ≤ x ∧ x < sc + 24) → ¬ (mk ≤ x ∧ x < mk + 48) →
      readByte r1 x = readByte s x)
    (hentry : ∀ x, x < ep ∨ ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 entw bs) x)
    (hsc : ∀ k, k < n → ¬ (sc ≤ a + k ∧ a + k < sc + 24))
    (hmk : ∀ k, k < n → ¬ (mk ≤ a + k ∧ a + k < mk + 48))
    (hep : ∀ k, k < n → (a + k < ep ∨ ep + 4 * ext ≤ a + k))
    (hew : ∀ k, k < n → (a + k < entw ∨ entw + bs.length ≤ a + k)) :
    readBytes r2 a n = readBytes s a n :=
  readBytes_of_readByte_eq (fun k hk => by
    rw [hentry _ (hep k hk), readByte_writeBytes_outside r1 bs (hew k hk),
      hmask _ (hsc k hk) (hmk k hk)])

/-- The same at four whole ranges. -/
theorem readBytes_mask_store_entry_of_disj {s r1 r2 : Mem} {sc mk entw ep ext : Nat}
    {bs : List UInt8} {a n : Nat}
    (hmask : ∀ x, ¬ (sc ≤ x ∧ x < sc + 24) → ¬ (mk ≤ x ∧ x < mk + 48) →
      readByte r1 x = readByte s x)
    (hentry : ∀ x, x < ep ∨ ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 entw bs) x)
    (hsc : a + n ≤ sc ∨ sc + 24 ≤ a) (hmk : a + n ≤ mk ∨ mk + 48 ≤ a)
    (hep : a + n ≤ ep ∨ ep + 4 * ext ≤ a)
    (hew : a + n ≤ entw ∨ entw + bs.length ≤ a) :
    readBytes r2 a n = readBytes s a n :=
  readBytes_mask_store_entry hmask hentry
    (fun k hk => not_inside_of_disjoint hsc hk) (fun k hk => not_inside_of_disjoint hmk hk)
    (fun k hk => by
      rcases hep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    (fun k hk => by
      rcases hew with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))

/-- Presence through the same three writes. -/
theorem hasBytes_mask_store_entry_of_disj {s r1 r2 : Mem} {sc mk entw ep ext : Nat}
    {bs : List UInt8} {a K : Nat}
    (hmask : ∀ x, ¬ (sc ≤ x ∧ x < sc + 24) → ¬ (mk ≤ x ∧ x < mk + 48) →
      readByte r1 x = readByte s x)
    (hentry : ∀ x, x < ep ∨ ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 entw bs) x)
    (hsc : a + K ≤ sc ∨ sc + 24 ≤ a) (hmk : a + K ≤ mk ∨ mk + 48 ≤ a)
    (hep : a + K ≤ ep ∨ ep + 4 * ext ≤ a)
    (hew : a + K ≤ entw ∨ entw + bs.length ≤ a)
    (h : HasBytes s a K) : HasBytes r2 a K :=
  hasBytes_of_readByte_eq h (fun k hk => by
    rw [hentry _ (by
          rcases hep with h' | h'
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)),
      readByte_writeBytes_outside r1 bs (by
        rcases hew with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)),
      hmask _ (not_inside_of_disjoint hsc hk) (not_inside_of_disjoint hmk hk)])

/-- A range read off an entry emitter's frame: the read at `a` of `n` bytes is
the read before the call, when the range is outside the emitter's written extent
and outside the body's own store. -/
theorem readBytes_entry_frame {r1 r2 : Mem} {ep entw ext : Nat} {bs : List UInt8}
    {a n : Nat}
    (hframe : ∀ x, x < ep ∨ ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 entw bs) x)
    (hep : a + n ≤ ep ∨ ep + 4 * ext ≤ a)
    (hew : a + n ≤ entw ∨ entw + bs.length ≤ a) :
    readBytes r2 a n = readBytes r1 a n :=
  readBytes_of_readByte_eq (fun k hk => by
    rw [hframe _ (by
          rcases hep with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)),
      readByte_writeBytes_outside r1 bs (by
        rcases hew with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))])

/-- A successful read returns as many bytes as it asks for. -/

theorem readBytes_len {m : Mem} {a n : Nat} {bs : List UInt8}
    (h : readBytes m a n = some bs) : bs.length = n := by
  induction n generalizing a bs with
  | zero =>
      simp only [readBytes, Option.some.injEq] at h
      subst h
      rfl
  | succ k ih =>
      simp only [readBytes] at h
      cases hb : readByte m a with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (a + 1) k with
          | none => rw [hr] at h; cases h
          | some bs' =>
              rw [hr] at h
              rw [Option.some.injEq] at h
              subst h
              rw [List.length_cons, ih hr]


/-! ### The mask unit's inbound parity, read off its slot -/

/-- A little-endian word of eight bytes decides the number it encodes, while the
number is below the word's capacity. -/
theorem natToBytes8_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : natToBytes x 8 = natToBytes y 8) : x = y := by
  have h1 := congrArg bytesToNat h
  rw [natToBytes_toNat, natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
  exact h1

/-- A flag word decides its flag. -/
theorem flagBytes_inj {a b : Bool} (h : flagBytes a = flagBytes b) : a = b := by
  have h2 : natToBytes (if a then 1 else 0) 8 = natToBytes (if b then 1 else 0) 8 := h
  have h3 : (if a then 1 else 0) = (if b then 1 else 0) :=
    natToBytes8_inj (by split <;> omega) (by split <;> omega) h2
  cases a <;> cases b <;> simp_all

/-- **A carry slot's two flag words decide the pair.**  The slot is three
eight-byte words, so its first two decide the run-open and run-parity flags. -/
theorem carrySlot_flags {a b c a' b' c' : Bool}
    (h : carrySlot a b c = carrySlot a' b' c') : a = a' ∧ b = b' := by
  have h' : flagBytes a ++ (flagBytes b ++ natToBytes (if c then 0xFFFFFFFFFFFFFFFF else 0) 8)
      = flagBytes a' ++
        (flagBytes b' ++ natToBytes (if c' then 0xFFFFFFFFFFFFFFFF else 0) 8) := h
  have hlen : (flagBytes a).length = (flagBytes a').length := by
    simp [flagBytes, natToBytes_length]
  obtain ⟨h1, hrest⟩ := List.append_inj h' hlen
  have hlen2 : (flagBytes b).length = (flagBytes b').length := by
    simp [flagBytes, natToBytes_length]
  obtain ⟨h2, -⟩ := List.append_inj hrest hlen2
  exact ⟨flagBytes_inj h1, flagBytes_inj h2⟩

/-- **The mask unit's classifier state has the parity its slot describes.**  The
post's incoming slot clause and the caller's read are the same bytes, so the flags
the post carries are the caller's; the state's parity is their conjunction. -/
theorem parity_of_slot {mem : Mem} {c : Nat} {st : ClassState}
    {opened ppar op ppar' ins : Bool}
    (hin : readBytes mem c 24 = some (carrySlot opened ppar st.inside))
    (hodd : st.oddRun = (opened && ppar))
    (hsc : readBytes mem c 24 = some (carrySlot op ppar' ins)) :
    st.oddRun = (op && ppar') := by
  have heq : carrySlot opened ppar st.inside = carrySlot op ppar' ins := by
    rw [hin] at hsc
    exact Option.some.inj hsc
  obtain ⟨h1, h2⟩ := carrySlot_flags heq
  rw [hodd, h1, h2]

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
        readByte r1.mem a = readByte s.mem a) ∧
      st.oddRun = (S.opened && S.ppar) ∧
      readBytes s.mem (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat) 64 =
        some (block64 lo hi) := by
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
  obtain ⟨lo', hi', st, opened, ppar, hblkPost, hcarryIn, hw1, hw2, hw3, hw4, hw5, hw6,
    hcarrySlot, hoddPost, hframe⟩ :=
    maskWords_of_masksPost (p := S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat)
      (c := S.sc) (maskSlot := S.maskSlot) (hargs := rfl) hdelim hinS hwsS hbsS hctl hpostM
  exact ⟨lo', hi', st, r1, hcall, hw1, hw2, hw3, hw4, hw5, hw6, hcarrySlot, hframe,
    parity_of_slot (mem := s.mem) (c := S.sc) hcarryIn hoddPost hsc, hblkPost⟩

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
  obtain ⟨e, o, t, blk0, nblk, k, ent, k', hargs, hv, hk', hread, hnbP, hentP,
    hframe⟩ := hpost'
  obtain ⟨-, -, hnblk, ho, hk, -⟩ := entryArgs_six hargs
  have hkn : k.toNat = S.k := by rw [hk]; exact hk0
  have hklen : k' - k.toNat ≤ 64 := by
    have hl := step_readLanes32_length r2.mem (o + 4 * k.toNat) (k' - k.toNat) hread
    have hb := step_streamPrefix_length_one ent blk0.toNat
    rw [hnblk, show ((1 : BitVec 64)).toNat = 1 from by decide] at hl
    omega
  have hge : k.toNat ≤ k' := by rw [hk']; omega
  have hframeL : ∀ a, a < o ∨ o + 4 * (k' + 8) ≤ a →
      readByte r2.mem a = readByte (writeBytes r1.mem S.entw
        (natToBytes (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) a := by
    intro a ha
    exact hframe a (ha.elim (fun h => Or.inl (by omega)) Or.inr)
  refine ⟨r2, k', o, hcall, hv, hframeL, ho, ?_⟩
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

/-! ### The successor invariant's cell half

`pipelineLoopInv`'s successor is a `PipelineLoopCarried` rebuilt from the units'
posts.  Two facts at the carried state are the whole difficulty of re-establishing
its *register* conjuncts: the successor's incoming builder must be found, cell by
cell, in the outgoing builder the arm's trace leaves (`usUs_cells_agree` is the
`for.body.us.us` arm's list, at the values the successor carries), and the
transport's agreement must then be read backwards through the incoming builder
(`agreeOn_succ`).  The remaining region conjuncts are read through one unit post's
byte frame composed with the body's own store (`readBytes_of_entry_frame`).

**All four arms are assembled**, each as twenty-eight named conjuncts at the
successor the arm leaves, proved and pinned separately.  The gate-on pair reads its
extra conjuncts off the escape list: the count's word is pinned by
`escapePositionsPost`'s `xn0 < 2 ^ 64` — without it every width the post stated was
a function of a representative the caller could not order against its own count —
and the two carry slots' pair by `pair_flags` (the same sixteen bytes read by the
mask unit and the list) together with `carry64_oddRun_congr`.
`block64_inj` is what makes the list's block the mask unit's, `escape_capacity` and
`readBytes_unchangedOutside` carry the staged stream and the static regions through
the list's run.

**What the assembled loop does and does not close.**  `pipelineLoop` is the
`PipelineLoop` the four steps dispatch into, so the block loop's own induction
runs.  `pipeline_satisfies_of_units` nevertheless keeps its `hbody` hypothesis:
the pipeline's post's `dst`/`ndst`/`ev`/`nev`/`err` clauses and the verdict come
from the stage-2 record, `Γ_stage2` does not exist in this tree, and no arbitrary
`Γ2` implies them.  The loop closing is not the pipeline closing.
-/

/-! ### Literal-list membership, for the staged region list -/

macro "lm1" : tactic => `(tactic| apply List.mem_cons_self)
macro "lm2" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm1))
macro "lm3" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm2))
macro "lm4" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm3))
macro "lm5" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm4))
macro "lm6" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm5))
macro "lm7" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm6))
macro "lm8" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm7))
macro "lm9" : tactic => `(tactic| (apply List.mem_cons_of_mem; lm8))

/-! ### Lookups through a builder -/

theorem lookupName_cells_of_some :
    ∀ (cs : List (String × Value)) (n : String) (env : Env) {v : Value},
      lookupName cs n = some v → lookupName (cells cs env) n = some v
  | [], n, env, v, h => by simp only [lookupName_nil] at h; cases h
  | (k, w) :: cs, n, env, v, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h
        cases h
        exact lookupName_cons_self k w (cells cs env)
      · simp only [lookupName_cons_ne w cs hkn] at h
        simp only [cells, lookupName_cons_ne w (cells cs env) hkn]
        exact lookupName_cells_of_some cs n env h

theorem not_mem_names_of_lookup_none :
    ∀ (cs : List (String × Value)) (n : String), lookupName cs n = none →
      n ∉ cs.map (fun p => p.1)
  | [], n, _ => by simp
  | (k, w) :: cs, n, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h; cases h
      · simp only [lookupName_cons_ne w cs hkn] at h
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h2
        · exact hkn h1.symm
        · exact not_mem_names_of_lookup_none cs n h h2

theorem mem_of_lookupName_some :
    ∀ (cs : List (String × Value)) (n : String) {v : Value},
      lookupName cs n = some v → (n, v) ∈ cs
  | [], n, v, h => by simp only [lookupName_nil] at h; cases h
  | (k, w) :: cs, n, v, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h
        cases h
        exact List.mem_cons_self ..
      · simp only [lookupName_cons_ne w cs hkn] at h
        exact List.mem_cons_of_mem _ (mem_of_lookupName_some cs n h)

/-- **The successor's agreement, from the transport's.**  Every cell of the
incoming builder is found with the same value in the outgoing builder, and the
transport relates the outgoing builder to the state it left, so the incoming
builder at that state agrees with it at every name. -/
theorem agreeOn_succ {ns : List String} {inCells : List (String × Value)} {outEnv : Env}
    {s s' : State}
    (hL : ∀ p ∈ inCells, lookupName outEnv p.1 = some p.2)
    (hag : State.AgreeOn ns (stateAt outEnv s) s') :
    State.AgreeOn ns (stateAt (cells inCells s'.env) s') s' := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro n hn
  show lookupName (cells inCells s'.env) n = lookupName s'.env n
  by_cases hnone : lookupName inCells n = none
  · rw [lookupName_cells_of_notin inCells n s'.env
      (not_mem_names_of_lookup_none inCells n hnone)]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [lookupName_cells_of_some inCells n s'.env hv,
      ← hL (n, v) (mem_of_lookupName_some inCells n hv)]
    exact hag.2.2.2 n hn

/-! ### Axiom footprints of the successor's cell half

The lookup and agreement facts are the builder's own `lookupName` recursion, and
the region read is one post's byte frame composed with a store; none adds a
carrier.  The arm's cell list is `block_lk` at literal cells, which is the same
footprint.

-/

/-- info: 'LeanLLVM.Vellum.lookupName_cells_of_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lookupName_cells_of_some

/-- info: 'LeanLLVM.Vellum.not_mem_names_of_lookup_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_mem_names_of_lookup_none

/-- info: 'LeanLLVM.Vellum.mem_of_lookupName_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_of_lookupName_some

/-- info: 'LeanLLVM.Vellum.agreeOn_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms agreeOn_succ

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


/-! ### The `for.body.us.us` iteration -/

/-- The carried state a `for.body.us.us` iteration leaves: the entry emitter's
count, the mask unit's outgoing carry, and the arm's own back-edge values. -/
def usUsSucc (S : PipelineLoopCarried) (ins o p : Bool) (k' : Nat)
    (sw : BitVec 64) : PipelineLoopCarried :=
  { S with arm := .pos8NoGate, i := S.i + 1, iw := vinc S.iw, sw := sw, kw := BitVec.ofNat 64 k', stM := ⟨ins, o && p⟩, opened := o, ppar := p, inside := ins, k := k' }

/-- **One `for.body.us.us` iteration's calls.**  The mask unit at the block's
staged address, the body's own store of the entry word, and the POS8 emitter at
the slot the body wrote; then the three words the block loads back for its
report. -/
theorem usUs_calls (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hdelim : S.delim = S.maskSlot + 8) (hinS : S.inString = S.maskSlot + 16)
    (hwsS : S.ws = S.maskSlot + 24) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40) (Ssep : StagedSep S blocks)
    (htabEq : S.tab = tab)
    (htab : readBytes s.mem S.tab 8192 = some pos8Table)
    (hkw : S.kw = BitVec.ofNat 64 S.k)
    (hkgrow : S.k ≤ S.k0 + 64 * S.i) (hroomk : cursorRoom S.k (blocks - S.i) 9) :
    ∃ (lo hi : Block32) (stm : ClassState) (r1 r2 : CallOutcome) (k' : Nat)
      (w1 w2 w3 w4 w5 w6 w7 : BitVec 64),
      pipelineCalls tab base s2 masksSym
        [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc,
         .ptr S.maskSlot] s.mem s.next = some r1 ∧
      (∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
        ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) →
        readByte r1.mem x = readByte s.mem x) ∧
      readBytes r1.mem S.maskSlot 8 = some (natToBytes w1.toNat 8) ∧
      readBytes r1.mem S.delim 8 = some (natToBytes w2.toNat 8) ∧
      readBytes r1.mem S.inString 8 = some (natToBytes w3.toNat 8) ∧
      readBytes r1.mem S.ws 8 = some (natToBytes w4.toNat 8) ∧
      readBytes r1.mem S.sc 24 =
        some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩))
          (carry64 lo hi stm).oddRun (carry64 lo hi stm).inside) ∧
      pipelineCalls tab base s2 entryPos8Sym
        [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep,
         .int 64 S.kw]
        (writeBytes r1.mem S.entw
          (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8)) r1.next = some r2 ∧
      r2.ret = .int 64 (BitVec.ofNat 64 k') ∧
      (∀ x, x < S.ep ∨ S.ep + 4 * (k' + 8) ≤ x →
        readByte r2.mem x = readByte (writeBytes r1.mem S.entw
          (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8)) x) ∧
      k' ≤ S.k + 64 ∧
      readBytes r2.mem S.backslash 8 = some (natToBytes w5.toNat 8) ∧
      readBytes r2.mem S.ctl 8 = some (natToBytes w6.toNat 8) ∧
      readBytes r2.mem S.inString 8 = some (natToBytes w7.toNat 8) := by
  have hdoc : S.doc.length = 64 * blocks := by
    have := readBytes_len hwin
    simpa using this
  have hdist : (S.b + 64 * S.i + 64 ≤ S.sc ∨ S.sc + 24 ≤ S.b + 64 * S.i) ∧
      (S.b + 64 * S.i + 64 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b + 64 * S.i) ∧
      (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc) :=
    ⟨disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_sc,
     disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_mk,
     Ssep.sc_mk⟩
  obtain ⟨lo, hi, stm, r1, hcall1, hw1, hw2, hw3, hw4, hw5, hw6, hscPost, hmaskFrame, hparM,
    hblkAt⟩ :=
    maskCall_at tab base s2 Γ2 units (S := S) hwin hsc hiw hilt hcap hdoc hdelim hinS
      hwsS hbsS hctl hdist
  have hbslen : (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
      (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
      (specSpace64 lo hi stm) S.sw).toNat 8).length = 8 := natToBytes_length ..
  have hstored : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8) := by
    have h := readBytes_writeBytes_same r1.mem
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)
      (addr := S.entw)
    rw [hbslen] at h
    exact h
  have htab' : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.tab 8192 =
      some pos8Table := by
    have htabS : readBytes s.mem S.tab 8192 = some pos8Table := htab
    have hew : S.tab + 8192 ≤ S.entw ∨
        S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
          (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
          (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.tab := by
      rcases Ssep.tab_ent with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hbslen]; exact h)
    refine Eq.trans ?_ htabS
    exact readBytes_of_readByte_eq (fun k hk => by
      rw [readByte_writeBytes_outside r1.mem _ (by
            rcases hew with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)),
        hmaskFrame _ (not_inside_of_disjoint Ssep.tab_sc hk)
          (not_inside_of_disjoint Ssep.tab_mk hk)])
  have hk64 : S.k < 2 ^ 64 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  have hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw := by
    rcases Ssep.ent_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hsepTab : S.tab + 8192 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.tab := by
    rcases Ssep.tab_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hroom : S.k + 64 + 9 < 2 ^ 63 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  obtain ⟨r2, k', o, hcall2, hret2, hentFrame, ho, hk'le⟩ :=
    pos8Call_at tab base s2 Γ2 units (S := S) (lo := lo) (hi := hi) (st := stm)
      htabEq hstored htab' hiw (by omega) hcap hkw hk64 hsepWord hsepTab hroom
  rw [ho] at hentFrame
  have hextK : k' + 8 ≤ S.k0 + 64 * blocks + 9 := by omega
  have hep5 : S.backslash + 8 ≤ S.ep ∨ S.ep + 4 * (k' + 8) ≤ S.backslash := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew5 : S.backslash + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.backslash := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld5 : readBytes r2.mem S.backslash 8 =
      some (natToBytes (specBackslash64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := k' + 8) hentFrame hep5 hew5, hw5]
  have hep6 : S.ctl + 8 ≤ S.ep ∨ S.ep + 4 * (k' + 8) ≤ S.ctl := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew6 : S.ctl + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.ctl := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld6 : readBytes r2.mem S.ctl 8 =
      some (natToBytes (specControl64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := k' + 8) hentFrame hep6 hew6, hw6]
  have hep7 : S.inString + 8 ≤ S.ep ∨ S.ep + 4 * (k' + 8) ≤ S.inString := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew7 : S.inString + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.inString := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld7 : readBytes r2.mem S.inString 8 =
      some (natToBytes (specInString64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := k' + 8) hentFrame hep7 hew7, hw3]
  exact ⟨lo, hi, stm, r1, r2, k', specQuote64 lo hi stm, specDelimiter64 lo hi stm,
    specInString64 lo hi stm, specSpace64 lo hi stm, specBackslash64 lo hi stm,
    specControl64 lo hi stm, specInString64 lo hi stm, hcall1, hmaskFrame, hw1, hw2, hw3,
    hw4, hscPost, hcall2, hret2, hentFrame, hk'le, hld5, hld6, hld7⟩


/-! ### The successor's facts, one name per conjunct -/

/-- The staged window survives the iteration: the mask unit's frame, the body's
store, and the emitter's frame leave every byte of it as it was. -/
theorem usUsSucc_window {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9)
    (hmask : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1 x = readByte s x)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (hwin : readBytes s S.b (64 * blocks) = some S.doc) :
    readBytes r2 S.b (64 * blocks) = some S.doc := by
  have hep : S.b + 64 * blocks ≤ S.ep ∨ S.ep + 4 * ext ≤ S.b := by
    rcases Ssep.win_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hew : S.b + 64 * blocks ≤ S.entw ∨ S.entw + bs.length ≤ S.b := by
    rcases Ssep.win_ent with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hbs]; exact h)
  rw [readBytes_mask_store_entry_of_disj hmask hentry Ssep.win_sc Ssep.win_mk hep hew, hwin]

/-- The staged table survives the iteration. -/
theorem usUsSucc_table {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9)
    (hmask : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1 x = readByte s x)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (htab : readBytes s S.tab 8192 = some pos8Table) :
    readBytes r2 S.tab 8192 = some pos8Table := by
  have hep : S.tab + 8192 ≤ S.ep ∨ S.ep + 4 * ext ≤ S.tab := by
    rcases Ssep.tab_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hew : S.tab + 8192 ≤ S.entw ∨ S.entw + bs.length ≤ S.tab := by
    rcases Ssep.tab_ent with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hbs]; exact h)
  rw [readBytes_mask_store_entry_of_disj hmask hentry Ssep.tab_sc Ssep.tab_mk hep hew, htab]

/-- The escape count's slot survives the iteration. -/
theorem usUsSucc_count {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9)
    (hmask : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1 x = readByte s x)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (hcnt : readBytes s S.nxp 8 = some (wordBytes 8 S.xn)) :
    readBytes r2 S.nxp 8 = some (wordBytes 8 S.xn) := by
  have hep : S.nxp + 8 ≤ S.ep ∨ S.ep + 4 * ext ≤ S.nxp := by
    rcases Ssep.ep_nxp with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hew : S.nxp + 8 ≤ S.entw ∨ S.entw + bs.length ≤ S.nxp := by
    rcases Ssep.ent_nxp with h | h
    · exact Or.inr (by rw [hbs]; exact h)
    · exact Or.inl h
  rw [readBytes_mask_store_entry_of_disj hmask hentry (sep_comm Ssep.sc_nxp)
    (sep_comm Ssep.mk_nxp) hep hew]
  exact hcnt

/-- The escape stream's capacity survives the iteration: presence is what a store
cannot take away, and the frames say no byte of it was read back. -/
theorem usUsSucc_capacity {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9)
    (hmask : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1 x = readByte s x)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (hhas : HasBytes s S.xp (4 * S.xpExtent)) :
    HasBytes r2 S.xp (4 * S.xpExtent) := by
  have hep : S.xp + 4 * S.xpExtent ≤ S.ep ∨ S.ep + 4 * ext ≤ S.xp := by
    rcases Ssep.ep_xp with h | h
    · exact Or.inr (by omega)
    · exact Or.inl h
  have hew : S.xp + 4 * S.xpExtent ≤ S.entw ∨ S.entw + bs.length ≤ S.xp := by
    rcases Ssep.ent_xp with h | h
    · exact Or.inr (by rw [hbs]; exact h)
    · exact Or.inl (by omega)
  exact hasBytes_mask_store_entry_of_disj hmask hentry (sep_comm Ssep.sc_xp)
    (sep_comm Ssep.mk_xp) hep hew hhas

/-- The mask unit's carry slot survives the iteration: the emitter does not write
it, and the body's store is elsewhere. -/
theorem usUsSucc_carrySlot {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8} {op p ins : Bool}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (hread : readBytes r1 S.sc 24 = some (carrySlot op p ins)) :
    readBytes r2 S.sc 24 = some (carrySlot op p ins) := by
  have hep : S.sc + 24 ≤ S.ep ∨ S.ep + 4 * ext ≤ S.sc := by
    rcases Ssep.sc_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hew : S.sc + 24 ≤ S.entw ∨ S.entw + bs.length ≤ S.sc := by
    rcases Ssep.sc_ent with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hbs]; exact h)
  rw [readBytes_entry_frame hentry hep hew, hread]

/-- The arm's outgoing builder holds a value for every cell the next iteration's
incoming builder binds.  `c21` is the count word the block's phi holds on entry
and `c21'` the count the emitter returns: the outgoing builder carries both, the
return under `%call21.us.us` and the incoming word under `%k.081.us.us`, so the
two are separate arguments. -/
theorem usUs_cells_agree' (env : Env) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 c21' inc shr w1 w2 w3 w4 : BitVec 64) (ret : Value)
    (hret : ret = .int 64 c21') :
    ∀ p ∈ [("%shr", .int 64 shr), ("%inc.us.us", .int 64 (vinc inc)),
           ("%call21.us.us", .int 64 c21'),
           ("%shr13.us.us", .int 64 (vshr13 w1 w2 w3 w4)), ("%ep", .ptr ep),
           ("%entw", .ptr entw), ("%ws", .ptr ws), ("%in_string", .ptr inString),
           ("%delim", .ptr delim), ("%mk", .ptr mk), ("%sc", .ptr sc), ("%b", .ptr b),
           ("%n", .int 64 n)],
      lookupName (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr
        w1 w2 w3 w4 ret) p.1 = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals (try rw [hret])
  all_goals block_lk

/-- **The successor's agreement**: every cell of the next iteration's incoming
builder is a value the arm's outgoing builder holds, so the trace's agreement
carries. -/
theorem usUsSucc_agree {S : PipelineLoopCarried} {e : State} {env : Env}
    {k' : Nat} {w1 w2 w3 w4 : BitVec 64} {ret : Value}
    (hret : ret = .int 64 (BitVec.ofNat 64 k'))
    (hag : State.AgreeOn (blockUses pUsUs)
      (stateAt (usUsOut env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr w1 w2 w3 w4 ret) e) e) :
    State.AgreeOn (blockUses pUsUs)
      (stateAt (usUsIn e.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e := by
  refine agreeOn_succ (fun p hp => ?_) hag
  exact usUs_cells_agree' env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw
    S.ep S.sw S.kw (BitVec.ofNat 64 k') S.iw S.shr w1 w2 w3 w4 ret hret p hp


/-! ### The step, at the arm's two successors -/

/-- **A `for.body.us.us` iteration that delays.**  With more than one iteration of
budget left the exit test is zero and the arm branches to itself; the successor's
twenty-eight clauses are the invariant's own projections, the posts' facts, and
the frames that leave every static region in place. -/
theorem usUs_step_head (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks n : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks (n + 1) s)
    (hn : 0 < n) (hpc0 : s.pc = "for.body.us.us") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks n e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n' =>
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .pos8NoGate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨lo, hi, stm, r1, r2, k', w1, w2, w3, w4, w5, w6, w7, hcall1, hmaskFrame, hw1,
    hw2, hw3, hw4, hscPost, hcall2, hret2, hentFrame, hk'le, hld5, hld6, hld7⟩ :=
    usUs_calls tab base s2 Γ2 units (S := S) hcap hiw hilt hwin hsc hdelim hinS hwsS hbsS
      hctl hsep htabEq htab hkw hkgrow hroomk
  have hbslen : (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8).length = 8 :=
    natToBytes_length ..
  have hextK : k' + 8 ≤ S.k0 + 64 * blocks + 9 := by omega
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := usUs_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3 w4 r1 r2 hpre'
    hw1 hw2 hw3 hw4 hpos hcall1 hcall2
  have hvexit : vexit S.iw S.shr = 0 := by
    rw [vexit_eq_zero]
    intro hcon
    rw [hiw, vinc_ofNat (by omega), hshr] at hcon
    exact (by omega : S.i + 1 ≠ blocks) ((ofNat64_eq_iff (by omega) (by omega)).mp hcon)
  obtain ⟨t', jt, hjt, hden, hag, hrun⟩ := usUs_step_at_head (pipelineCalls tab base s2) s.env s S.n
    S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3
    w4 r2 r2 hpcS hagree hcode hvexit
  let e : State := { t' with pc := "for.body.us.us", pre := some s.pc }
  have hmem : e.mem = r2.mem := hag.1.symm
  have hagE : State.AgreeOn (blockUses pUsUs)
      (stateAt (usUsOut s.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr w1 w2 w3 w4 r2.ret) e) e :=
    ⟨rfl, rfl, rfl, fun x hx => hag.2.2.2 x hx⟩
  refine ⟨e, jt, hjt, ?_, hrun⟩
  refine ⟨usUsSucc S (carry64 lo hi stm).inside (IsBackslashB (hi ⟨31, by decide⟩))
    (carry64 lo hi stm).oddRun k' (vshr13 w1 w2 w3 w4), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show some s.pc = some "for.body.us.us"
    rw [hpc0]
  · show S.i + 1 + (n' + 1) = blocks
    omega
  · exact hshr
  · show vinc S.iw = BitVec.ofNat 64 (S.i + 1)
    rw [hiw, vinc_ofNat (by omega)]
  · show State.AgreeOn (blockUses pUsUs) (stateAt (usUsIn e.env S.n S.b S.sc S.maskSlot
      S.delim S.inString S.ws S.entw S.ep (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k')
      (vinc S.iw) S.shr) e) e
    exact usUsSucc_agree hret2 hagE
  · exact hb
  · rw [hmem]
    exact usUsSucc_window (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem) hsep hbslen hextK hmaskFrame hentFrame hwin
  · rw [hmem]
    exact usUsSucc_carrySlot (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem) (op := IsBackslashB (hi ⟨31, by decide⟩))
      (p := (carry64 lo hi stm).oddRun) (ins := (carry64 lo hi stm).inside)
      hsep hbslen hextK hentFrame hscPost
  · rfl
  · exact hdelim
  · exact hinS
  · exact hwsS
  · exact hbsS
  · exact hctl
  · exact htabEq
  · rw [hmem]
    exact usUsSucc_table (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem) hsep hbslen hextK hmaskFrame hentFrame htab
  · rfl
  · rw [hmem]
    exact usUsSucc_count (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem) hsep hbslen hextK hmaskFrame hentFrame hcnt
  · exact hxpExt
  · show k' ≤ S.k0 + 64 * (S.i + 1)
    omega
  · show S.xn ≤ S.xn0 + 64 * (S.i + 1)
    omega
  · intro hc
    exact Bool.noConfusion hc
  · intro hc
    exact Bool.noConfusion hc
  · show cursorRoom k' (blocks - (S.i + 1)) 9
    have hh := hroomk
    unfold cursorRoom at hh ⊢
    omega
  · show cursorRoom S.xn (blocks - (S.i + 1)) 9
    have hh := hroomxn
    unfold cursorRoom at hh ⊢
    omega
  · rw [hmem]
    exact usUsSucc_capacity (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem) hsep hbslen hextK hmaskFrame hentFrame hhas
  · exact hdisj

/-- **A `for.body.us.us` iteration that leaves.**  With one iteration of budget
left the exit test is one, the arm's increment reached the block count, and the
successor is the cleanup — the loop's exit, which the invariant admits at `0`. -/
theorem usUs_step_exit (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks 1 s)
    (hpc0 : s.pc = "for.body.us.us") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks 0 e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .pos8NoGate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨lo, hi, stm, r1, r2, k', w1, w2, w3, w4, w5, w6, w7, hcall1, hmaskFrame, hw1,
    hw2, hw3, hw4, hscPost, hcall2, hret2, hentFrame, hk'le, hld5, hld6, hld7⟩ :=
    usUs_calls tab base s2 Γ2 units (S := S) hcap hiw hilt hwin hsc hdelim hinS hwsS hbsS
      hctl hsep htabEq htab hkw hkgrow hroomk
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := usUs_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3 w4 r1 r2 hpre'
    hw1 hw2 hw3 hw4 hpos hcall1 hcall2
  have hvexit : vexit S.iw S.shr = 1 := by
    rw [vexit_eq_one]
    rw [hiw, vinc_ofNat (by omega), hshr]
    exact (ofNat64_eq_iff (by omega) (by omega)).mpr (by omega)
  obtain ⟨e, je, hje, hpcE, hrunE⟩ := usUs_step_at_exit (pipelineCalls tab base s2) s.env s S.n
    S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3
    w4 r2 r2 hpcS hagree hcode hvexit
  exact ⟨e, je, hje, hpcE, hrunE⟩


/-! ### The `for.body.us83` iteration -/

/-- **The B8 entry call at the loop's block**, after the body's own store.  The
same shape as `pos8Call_at` without the staged table: the emitter's entry-word
clause is the store, and its frame's extent is one byte shorter than the POS8
emitter's, because the word it writes is shorter. -/
theorem b8Call_at (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {S : PipelineLoopCarried}
    {r1 : CallOutcome} {blocks : Nat} {lo hi : Block32} {st : ClassState}
    (hstored : readBytes (writeBytes r1.mem S.entw (natToBytes
      (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
        (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8))
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hib : S.i + 1 ≤ blocks)
    (hcnt : 64 * blocks + 63 < 2 ^ 32)
    (hkw : S.kw = BitVec.ofNat 64 S.k) (hk64 : S.k < 2 ^ 64)
    (hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw)
    (hroom : S.k + 64 + 9 < 2 ^ 63) :
    ∃ (r2 : CallOutcome) (k' o : Nat),
      pipelineCalls tab base s2 entryB8Sym
        [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
        (writeBytes r1.mem S.entw (natToBytes
          (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
            (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) r1.next = some r2 ∧
      r2.ret = .int 64 (BitVec.ofNat 64 k') ∧
      (∀ a, a < o ∨ o + 4 * (k' + 7) ≤ a →
        readByte r2.mem a = readByte (writeBytes r1.mem S.entw (natToBytes
          (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
            (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) a) ∧
      o = S.ep ∧ k' ≤ S.k + 64 := by
  have hblkP : 64 * (S.iw.toNat + 1) + 63 < 2 ^ 32 := by
    rw [hiw, ofNat64_toNat (by omega)]
    omega
  have hk0 : S.kw.toNat = S.k := by rw [hkw, ofNat64_toNat hk64]
  have hpre : Γ_entry_b8.pre
      [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
      (writeBytes r1.mem S.entw (natToBytes
        (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) r1.next := by
    refine b8Pre_of_stored_word (entw := S.entw) (ep := S.ep)
      (blk0 := S.iw) (k := S.kw) (word := vent S.n S.iw (specQuote64 lo hi st)
        (specDelimiter64 lo hi st) (specInString64 lo hi st) (specSpace64 lo hi st) S.sw)
      hstored hblkP ?_ ?_
    · rw [hk0]; exact hsepWord
    · rw [hk0]; exact hroom
  obtain ⟨r2, hcall, hpost, -⟩ := units.b8 _ _ r1.next hpre
  have hpost' : entryB8Post
      [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
      (writeBytes r1.mem S.entw (natToBytes
        (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8))
      r2.ret r2.mem := hpost
  obtain ⟨e, o, blk0, nblk, k, ent, k', hargs, hv, hk', hread, hnbP, hentP,
    hframe⟩ := hpost'
  have hargs' : ([.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep,
      .int 64 S.kw] : List Value) =
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k] := hargs
  simp only [List.cons.injEq, List.nil_eq, Value.ptr.injEq, Value.int.injEq, and_true,
    HEq] at hargs'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hargs'
  have ho : o = S.ep := h4.symm
  have hnblk : nblk = (1 : BitVec 64) := (eq_of_heq h3.2).symm
  have hkEq : k = S.kw := (eq_of_heq h5.2).symm
  have hkn : k.toNat = S.k := by rw [hkEq]; exact hk0
  have hklen : k' - k.toNat ≤ 64 := by
    have hl := step_readLanes32_length r2.mem (o + 4 * k.toNat) (k' - k.toNat) hread
    have hb := step_streamPrefix_length_one ent blk0.toNat
    rw [hnblk, show ((1 : BitVec 64)).toNat = 1 from by decide] at hl
    omega
  have hge : k.toNat ≤ k' := by rw [hk']; omega
  have hframeL : ∀ a, a < o ∨ o + 4 * (k' + 7) ≤ a →
      readByte r2.mem a = readByte (writeBytes r1.mem S.entw
        (natToBytes (vent S.n S.iw (specQuote64 lo hi st) (specDelimiter64 lo hi st)
          (specInString64 lo hi st) (specSpace64 lo hi st) S.sw).toNat 8)) a := by
    intro a ha
    exact hframe a (ha.elim (fun h => Or.inl (by omega)) Or.inr)
  refine ⟨r2, k', o, hcall, hv, hframeL, ho, ?_⟩
  rw [← hkn]
  omega

/-- The carried state a `for.body.us83` iteration leaves. -/
def us83Succ (S : PipelineLoopCarried) (ins o p : Bool) (k' : Nat)
    (sw : BitVec 64) : PipelineLoopCarried :=
  { S with arm := .b8NoGate, i := S.i + 1, iw := vinc S.iw, sw := sw, kw := BitVec.ofNat 64 k', stM := ⟨ins, o && p⟩, opened := o, ppar := p, inside := ins, k := k' }

/-- **One `for.body.us83` iteration's calls.** -/
theorem us83_calls (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hdelim : S.delim = S.maskSlot + 8) (hinS : S.inString = S.maskSlot + 16)
    (hwsS : S.ws = S.maskSlot + 24) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40) (Ssep : StagedSep S blocks)
    (hkw : S.kw = BitVec.ofNat 64 S.k)
    (hkgrow : S.k ≤ S.k0 + 64 * S.i) (hroomk : cursorRoom S.k (blocks - S.i) 9) :
    ∃ (lo hi : Block32) (stm : ClassState) (r1 r2 : CallOutcome) (k' : Nat)
      (w1 w2 w3 w4 : BitVec 64),
      pipelineCalls tab base s2 masksSym
        [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc,
         .ptr S.maskSlot] s.mem s.next = some r1 ∧
      (∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
        ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) →
        readByte r1.mem x = readByte s.mem x) ∧
      readBytes r1.mem S.maskSlot 8 = some (natToBytes w1.toNat 8) ∧
      readBytes r1.mem S.delim 8 = some (natToBytes w2.toNat 8) ∧
      readBytes r1.mem S.inString 8 = some (natToBytes w3.toNat 8) ∧
      readBytes r1.mem S.ws 8 = some (natToBytes w4.toNat 8) ∧
      readBytes r1.mem S.sc 24 =
        some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩))
          (carry64 lo hi stm).oddRun (carry64 lo hi stm).inside) ∧
      pipelineCalls tab base s2 entryB8Sym
        [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep,
         .int 64 S.kw]
        (writeBytes r1.mem S.entw
          (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8)) r1.next = some r2 ∧
      r2.ret = .int 64 (BitVec.ofNat 64 k') ∧
      (∀ x, x < S.ep ∨ S.ep + 4 * (k' + 7) ≤ x →
        readByte r2.mem x = readByte (writeBytes r1.mem S.entw
          (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8)) x) ∧
      k' ≤ S.k + 64 := by
  have hdoc : S.doc.length = 64 * blocks := by
    have := readBytes_len hwin
    simpa using this
  have hdist : (S.b + 64 * S.i + 64 ≤ S.sc ∨ S.sc + 24 ≤ S.b + 64 * S.i) ∧
      (S.b + 64 * S.i + 64 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b + 64 * S.i) ∧
      (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc) :=
    ⟨disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_sc,
     disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_mk,
     Ssep.sc_mk⟩
  obtain ⟨lo, hi, stm, r1, hcall1, hw1, hw2, hw3, hw4, -, -, hscPost, hmaskFrame, hparM,
    hblkAt⟩ :=
    maskCall_at tab base s2 Γ2 units (S := S) hwin hsc hiw hilt hcap hdoc hdelim hinS
      hwsS hbsS hctl hdist
  have hbslen : (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
      (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
      (specSpace64 lo hi stm) S.sw).toNat 8).length = 8 := natToBytes_length ..
  have hstored : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8) := by
    have h := readBytes_writeBytes_same r1.mem
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)
      (addr := S.entw)
    rw [hbslen] at h
    exact h
  have hk64 : S.k < 2 ^ 64 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  have hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw := by
    rcases Ssep.ent_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hroom : S.k + 64 + 9 < 2 ^ 63 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  obtain ⟨r2, k', o, hcall2, hret2, hentFrame, ho, hk'le⟩ :=
    b8Call_at tab base s2 Γ2 units (S := S) (lo := lo) (hi := hi) (st := stm)
      (r1 := r1) hstored hiw (by omega) hcap hkw hk64 hsepWord hroom
  rw [ho] at hentFrame
  exact ⟨lo, hi, stm, r1, r2, k', specQuote64 lo hi stm, specDelimiter64 lo hi stm,
    specInString64 lo hi stm, specSpace64 lo hi stm, hcall1, hmaskFrame, hw1, hw2, hw3,
    hw4, hscPost, hcall2, hret2, hentFrame, hk'le⟩

/-- The B8 arm's outgoing builder holds every cell the next iteration binds. -/
theorem us83_cells_agree' (env : Env) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 c21' inc shr w1 w2 w3 w4 : BitVec 64) (ret : Value)
    (hret : ret = .int 64 c21') :
    ∀ p ∈ [("%shr", .int 64 shr), ("%inc.us106", .int 64 (vinc inc)),
           ("%call.us", .int 64 c21'),
           ("%shr13.us98", .int 64 (vshr13 w1 w2 w3 w4)), ("%ep", .ptr ep),
           ("%entw", .ptr entw), ("%ws", .ptr ws), ("%in_string", .ptr inString),
           ("%delim", .ptr delim), ("%mk", .ptr mk), ("%sc", .ptr sc), ("%b", .ptr b),
           ("%n", .int 64 n)],
      lookupName (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr
        w1 w2 w3 w4 ret) p.1 = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals (try rw [hret])
  all_goals block_lk

/-- The B8 arm's successor agreement. -/
theorem us83Succ_agree {S : PipelineLoopCarried} {e : State} {env : Env}
    {k' : Nat} {w1 w2 w3 w4 : BitVec 64} {ret : Value}
    (hret : ret = .int 64 (BitVec.ofNat 64 k'))
    (hag : State.AgreeOn (blockUses pUs83)
      (stateAt (us83Out env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr w1 w2 w3 w4 ret) e) e) :
    State.AgreeOn (blockUses pUs83)
      (stateAt (us83In e.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e := by
  refine agreeOn_succ (fun p hp => ?_) hag
  exact us83_cells_agree' env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw
    S.ep S.sw S.kw (BitVec.ofNat 64 k') S.iw S.shr w1 w2 w3 w4 ret hret p hp

/-- **A `for.body.us83` iteration that delays.** -/
theorem us83_step_head (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks n : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks (n + 1) s)
    (hn : 0 < n) (hpc0 : s.pc = "for.body.us83") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks n e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n' =>
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .b8NoGate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨lo, hi, stm, r1, r2, k', w1, w2, w3, w4, hcall1, hmaskFrame, hw1, hw2, hw3, hw4,
    hscPost, hcall2, hret2, hentFrame, hk'le⟩ :=
    us83_calls tab base s2 Γ2 units (S := S) hcap hiw hilt hwin hsc hdelim hinS hwsS hbsS
      hctl hsep hkw hkgrow hroomk
  have hbslen : (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8).length = 8 :=
    natToBytes_length ..
  have hextK : k' + 7 ≤ S.k0 + 64 * blocks + 9 := by omega
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := us83_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3 w4 r1 r2 hpre'
    hw1 hw2 hw3 hw4 hpos hcall1 hcall2
  have hvexit : vexit S.iw S.shr = 0 := by
    rw [vexit_eq_zero]
    intro hcon
    rw [hiw, vinc_ofNat (by omega), hshr] at hcon
    exact (by omega : S.i + 1 ≠ blocks) ((ofNat64_eq_iff (by omega) (by omega)).mp hcon)
  obtain ⟨t', jt, hjt, hden, hag, hrun⟩ := us83_step_at_head (pipelineCalls tab base s2)
    s.env s S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw
    S.shr w1 w2 w3 w4 r2 r2 hpcS hagree hcode hvexit
  let e : State := { t' with pc := "for.body.us83", pre := some s.pc }
  have hmem : e.mem = r2.mem := hag.1.symm
  have hagE : State.AgreeOn (blockUses pUs83)
      (stateAt (us83Out s.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr w1 w2 w3 w4 r2.ret) e) e :=
    ⟨rfl, rfl, rfl, fun x hx => hag.2.2.2 x hx⟩
  refine ⟨e, jt, hjt, ?_, hrun⟩
  refine ⟨us83Succ S (carry64 lo hi stm).inside (IsBackslashB (hi ⟨31, by decide⟩))
    (carry64 lo hi stm).oddRun k' (vshr13 w1 w2 w3 w4), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show some s.pc = some "for.body.us83"
    rw [hpc0]
  · show S.i + 1 + (n' + 1) = blocks
    omega
  · exact hshr
  · show vinc S.iw = BitVec.ofNat 64 (S.i + 1)
    rw [hiw, vinc_ofNat (by omega)]
  · show State.AgreeOn (blockUses pUs83) (stateAt (us83In e.env S.n S.b S.sc S.maskSlot
      S.delim S.inString S.ws S.entw S.ep (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k')
      (vinc S.iw) S.shr) e) e
    exact us83Succ_agree hret2 hagE
  · exact hb
  · rw [hmem]
    exact usUsSucc_window (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem)
      hsep hbslen hextK hmaskFrame hentFrame hwin
  · rw [hmem]
    exact usUsSucc_carrySlot (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem)
      (op := IsBackslashB (hi ⟨31, by decide⟩)) (p := (carry64 lo hi stm).oddRun)
      (ins := (carry64 lo hi stm).inside) hsep hbslen hextK hentFrame hscPost
  · rfl
  · exact hdelim
  · exact hinS
  · exact hwsS
  · exact hbsS
  · exact hctl
  · exact htabEq
  · rw [hmem]
    exact usUsSucc_table (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem)
      hsep hbslen hextK hmaskFrame hentFrame htab
  · rfl
  · rw [hmem]
    exact usUsSucc_count (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem)
      hsep hbslen hextK hmaskFrame hentFrame hcnt
  · exact hxpExt
  · show k' ≤ S.k0 + 64 * (S.i + 1)
    omega
  · show S.xn ≤ S.xn0 + 64 * (S.i + 1)
    omega
  · intro hc
    exact Bool.noConfusion hc
  · intro hc
    exact Bool.noConfusion hc
  · show cursorRoom k' (blocks - (S.i + 1)) 9
    have hh := hroomk
    unfold cursorRoom at hh ⊢
    omega
  · show cursorRoom S.xn (blocks - (S.i + 1)) 9
    have hh := hroomxn
    unfold cursorRoom at hh ⊢
    omega
  · rw [hmem]
    exact usUsSucc_capacity (S := S) (s := s.mem) (r1 := r1.mem) (r2 := r2.mem)
      hsep hbslen hextK hmaskFrame hentFrame hhas
  · exact hdisj

/-- **A `for.body.us83` iteration that leaves.** -/
theorem us83_step_exit (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks 1 s)
    (hpc0 : s.pc = "for.body.us83") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks 0 e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .b8NoGate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨lo, hi, stm, r1, r2, k', w1, w2, w3, w4, hcall1, hmaskFrame, hw1, hw2, hw3, hw4,
    hscPost, hcall2, hret2, hentFrame, hk'le⟩ :=
    us83_calls tab base s2 Γ2 units (S := S) hcap hiw hilt hwin hsc hdelim hinS hwsS hbsS
      hctl hsep hkw hkgrow hroomk
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := us83_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1 w2 w3 w4 r1 r2 hpre'
    hw1 hw2 hw3 hw4 hpos hcall1 hcall2
  have hvexit : vexit S.iw S.shr = 1 := by
    rw [vexit_eq_one]
    rw [hiw, vinc_ofNat (by omega), hshr]
    exact (ofNat64_eq_iff (by omega) (by omega)).mpr (by omega)
  obtain ⟨e, je, hje, hpcE, hrunE⟩ := us83_step_at_exit (pipelineCalls tab base s2) s.env s
    S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep S.sw S.kw S.iw S.shr w1
    w2 w3 w4 r2 r2 hpcS hagree hcode hvexit
  exact ⟨e, je, hje, hpcE, hrunE⟩



/-! ### The block's two halves, and the pair's two flags -/

/-- The staged block's two halves are recoverable from its sixty-four bytes. -/
theorem block64_inj {lo hi lo' hi' : Block32} (h : block64 lo hi = block64 lo' hi') :
    lo = lo' ∧ hi = hi' := by
  have hlen : (List.ofFn lo).length = (List.ofFn lo').length := by
    simp only [List.length_ofFn]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  have hp : ∀ (f g : Fin 32 → UInt8), List.ofFn f = List.ofFn g → f = g := by
    intro f g hfg
    funext i
    have h := congrArg (fun l => l[i.1]?) hfg
    rw [List.getElem?_ofFn, List.getElem?_ofFn] at h
    simpa using h
  exact ⟨hp lo lo' h1, hp hi hi' h2⟩

/-- The sixteen bytes of a carry slot decide its two flags. -/
theorem pair_flags {mem : Mem} {a : Nat} {p q p' q' : Bool}
    (h : readBytes mem a 16 = some (flagBytes p ++ flagBytes q))
    (h' : readBytes mem a 16 = some (flagBytes p' ++ flagBytes q')) : p = p' ∧ q = q' := by
  have heq : flagBytes p ++ flagBytes q = flagBytes p' ++ flagBytes q' := by
    rw [h] at h'
    exact Option.some.inj h'
  have hl : (flagBytes p).length = (flagBytes p').length := by
    simp [flagBytes, natToBytes_length]
  obtain ⟨h1, h2⟩ := List.append_inj heq hl
  exact ⟨flagBytes_inj h1, flagBytes_inj h2⟩

/-- A little-endian word of eight bytes depends only on the value modulo its
width: the record reads a count back from the bytes, so the representative the
post names is not the value it denotes. -/
theorem natToBytes_mod (v n : Nat) : natToBytes (v % 256 ^ n) n = natToBytes v n := by
  induction n generalizing v with
  | zero => rfl
  | succ k ih =>
      show UInt8.ofNat ((v % 256 ^ (k + 1)) % 256) ::
          natToBytes ((v % 256 ^ (k + 1)) / 256) k =
        UInt8.ofNat (v % 256) :: natToBytes (v / 256) k
      rw [Nat.pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self,
        ih (v / 256)]

/-- A count read back from eight bytes denotes its own residue. -/
theorem wordBytes8_eq_of_mod {x y : Nat} (h : x % 2 ^ 64 = y % 2 ^ 64) :
    natToBytes x 8 = natToBytes y 8 := by
  rw [← natToBytes_mod x 8, ← natToBytes_mod y 8,
    show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, h]


/-! ### Expansion's exclusion, and the escape list's call

The gate-on arms add the escape list after the entry emitter.  Its record promises
the advanced count, the outgoing pair, the block's positions and every byte outside
its three regions; the step reads that exclusion for the regions it carries. -/

/-- A range outside every region a unit's exclusion names reads as it did. -/
theorem readBytes_unchangedOutside {mem m : Mem} {regs : List (Nat × Nat)} {a n : Nat}
    (hu : UnchangedOutside mem m regs)
    (h : ∀ r ∈ regs, a + n ≤ r.1 ∨ r.1 + r.2 ≤ a) :
    readBytes m a n = readBytes mem a n :=
  readBytes_of_readByte_eq (fun k hk =>
    hu (a + k) (fun r hr => not_inside_of_disjoint (h r hr) hk))

/-- Presence of every byte of a range is a `readBytes`. -/
theorem hasBytes_of_forall (m : Mem) : ∀ (M a : Nat),
    (∀ k, k < M → ∃ b, readByte m (a + k) = some b) → HasBytes m a M
  | 0, a, _ => ⟨[], rfl⟩
  | M + 1, a, h => by
      obtain ⟨b, hb⟩ := h 0 (by omega)
      have hb' : readByte m a = some b := by simpa using hb
      obtain ⟨vs, hvs⟩ := hasBytes_of_forall m M (a + 1) (fun k hk => by
        have := h (k + 1) (by omega)
        simpa [show a + (k + 1) = a + 1 + k from by omega] using this)
      exact ⟨b :: vs, by simp only [readBytes, hb', hvs]⟩

/-- **The escape stream's capacity, extended to the staged extent.**  The record
promises presence of the block's per-call capacity and byte equality outside its
three regions, so the staged extent's tail is the caller's bytes and the two
together are the whole staged stream. -/
theorem escape_capacity {r2 r3 : Mem} {xp xn xcarry xn0 extent : Nat}
    (hu : UnchangedOutside r2 r3 [(xp, 4 * blockMax xn0), (xn, 8), (xcarry, 16)])
    (hpost : HasBytes r3 xp (4 * blockMax xn0))
    (hpre : HasBytes r2 xp (4 * extent))
    (hK : blockMax xn0 ≤ extent)
    (hxn : xp + 4 * extent ≤ xn ∨ xn + 8 ≤ xp)
    (hxc : xp + 4 * extent ≤ xcarry ∨ xcarry + 16 ≤ xp) :
    HasBytes r3 xp (4 * extent) := by
  refine hasBytes_of_forall r3 (4 * extent) xp (fun k hk => ?_)
  by_cases hlt : k < 4 * blockMax xn0
  · obtain ⟨vs, hvs⟩ := hpost
    exact ⟨vs.getD k 0, readByte_of_readBytes hvs hlt⟩
  · have hout : readByte r3 (xp + k) = readByte r2 (xp + k) := by
      refine hu (xp + k) (fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · omega
      · rcases hxn with h | h <;> omega
      · rcases hxc with h | h <;> omega
    obtain ⟨vs, hvs⟩ := hpre
    exact ⟨vs.getD k 0, by rw [hout]; exact readByte_of_readBytes hvs (by omega)⟩



/-! ### The gate-on arms: the list's exclusion, and the call site

The two arms that call the escape list differ from the two that do not in one
call and in what its post promises.  What all four share is the frame machinery
above — the mask unit's two store regions, the body's own store, and the entry
emitter's written extent — so the gate-on successor's facts are that frame
composed with the list's exclusion, stated once here for both arms.

The exclusion's extent is `4 * blockMax xn0` at the count the caller passes, while
the staged capacity the invariant carries is `4 * S.xpExtent`; `blockMax xn0 ≤
S.xpExtent` is what makes the first a sub-range of the second, and the count's
growth bound is what makes it true at every block. -/

/-- The outgoing parity is a function of the parity the block is entered with, so
two states that agree there leave the same carry parity. -/
theorem carry64_oddRun_congr {lo hi : Block32} {st st' : ClassState}
    (h : st.oddRun = st'.oddRun) :
    (carry64 lo hi st).oddRun = (carry64 lo hi st').oddRun := by
  rw [carry64_oddRun_eq, carry64_oddRun_eq, h]

/-- A byte outside the escape list's three regions reads as it did: the post's
exclusion is the frame the successor's static regions survive by. -/
theorem escapeOutside {r2 r3 : Mem} {S : PipelineLoopCarried} {xn0 : Nat}
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    {a : Nat}
    (hxp : a < S.xp ∨ S.xp + 4 * blockMax xn0 ≤ a)
    (hnxp : a < S.nxp ∨ S.nxp + 8 ≤ a)
    (hxc : a < S.xcarry ∨ S.xcarry + 16 ≤ a) :
    readByte r3 a = readByte r2 a := by
  refine hesc a ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rcases hxp with h | h <;> omega
  · rintro ⟨h1, h2⟩; rcases hnxp with h | h <;> omega
  · rintro ⟨h1, h2⟩; rcases hxc with h | h <;> omega

/-- The range form of `escapeOutside`. -/
theorem escapeReadBytes {r2 r3 : Mem} {S : PipelineLoopCarried} {xn0 : Nat}
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    {a n : Nat}
    (hxp : a + n ≤ S.xp ∨ S.xp + 4 * blockMax xn0 ≤ a)
    (hnxp : a + n ≤ S.nxp ∨ S.nxp + 8 ≤ a)
    (hxc : a + n ≤ S.xcarry ∨ S.xcarry + 16 ≤ a) :
    readBytes r3 a n = readBytes r2 a n :=
  readBytes_of_readByte_eq (fun k hk => escapeOutside hesc
    (by rcases hxp with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    (by rcases hnxp with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    (by rcases hxc with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)))

/-- The presence form of `escapeOutside`. -/
theorem escapeHasBytes {r2 r3 : Mem} {S : PipelineLoopCarried} {xn0 K a : Nat}
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    (hxp : a + K ≤ S.xp ∨ S.xp + 4 * blockMax xn0 ≤ a)
    (hnxp : a + K ≤ S.nxp ∨ S.nxp + 8 ≤ a)
    (hxc : a + K ≤ S.xcarry ∨ S.xcarry + 16 ≤ a)
    (h : HasBytes r2 a K) : HasBytes r3 a K :=
  hasBytes_of_readByte_eq h (fun k hk => escapeOutside hesc
    (by rcases hxp with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    (by rcases hnxp with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    (by rcases hxc with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)))

/-- The staged window survives the escape list's run: its three regions are
disjoint from the document at `blockMax`'s extent. -/
theorem gateSucc_window {S : PipelineLoopCarried} {blocks : Nat} {r2 r3 : Mem}
    {xn0 : Nat}
    (Ssep : StagedSep S blocks) (hbm : blockMax xn0 ≤ S.xpExtent)
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    (hwin : readBytes r2 S.b (64 * blocks) = some S.doc) :
    readBytes r3 S.b (64 * blocks) = some S.doc := by
  have hxp : S.b + 64 * blocks ≤ S.xp ∨ S.xp + 4 * blockMax xn0 ≤ S.b := by
    rcases Ssep.win_xp with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hnxp : S.b + 64 * blocks ≤ S.nxp ∨ S.nxp + 8 ≤ S.b := Ssep.win_nxp
  have hxc : S.b + 64 * blocks ≤ S.xcarry ∨ S.xcarry + 16 ≤ S.b := Ssep.win_xc
  exact (escapeReadBytes hesc hxp hnxp hxc).trans hwin

/-- The staged table survives the escape list's run. -/
theorem gateSucc_table {S : PipelineLoopCarried} {blocks : Nat} {r2 r3 : Mem}
    {xn0 : Nat}
    (Ssep : StagedSep S blocks) (hbm : blockMax xn0 ≤ S.xpExtent)
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    (htab : readBytes r2 S.tab 8192 = some pos8Table) :
    readBytes r3 S.tab 8192 = some pos8Table := by
  have hxp : S.tab + 8192 ≤ S.xp ∨ S.xp + 4 * blockMax xn0 ≤ S.tab := by
    rcases Ssep.tab_xp with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  exact (escapeReadBytes hesc hxp Ssep.tab_nxp Ssep.tab_xc).trans htab

/-- The mask unit's carry slot survives the escape list's run. -/
theorem gateSucc_scSlot {S : PipelineLoopCarried} {blocks : Nat} {r2 r3 : Mem}
    {xn0 : Nat} {op pp ins : Bool}
    (Ssep : StagedSep S blocks) (hbm : blockMax xn0 ≤ S.xpExtent)
    (hesc : UnchangedOutside r2 r3
      [(S.xp, 4 * blockMax xn0), (S.nxp, 8), (S.xcarry, 16)])
    (hsc : readBytes r2 S.sc 24 = some (carrySlot op pp ins)) :
    readBytes r3 S.sc 24 = some (carrySlot op pp ins) := by
  have hxp : S.sc + 24 ≤ S.xp ∨ S.xp + 4 * blockMax xn0 ≤ S.sc := by
    rcases Ssep.sc_xp with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  exact (escapeReadBytes hesc hxp Ssep.sc_nxp Ssep.sc_xc).trans hsc

/-- The staged block's two halves survive the mask unit's stores, the body's own
store and the entry emitter's writes, at the index's document offset. -/
theorem gateBlock_at {S : PipelineLoopCarried} {blocks : Nat} {s r1 r2 : Mem}
    {ext : Nat} {bs : List UInt8} {lo hi : Block32}
    (Ssep : StagedSep S blocks) (hbs : bs.length = 8)
    (hext : ext ≤ S.k0 + 64 * blocks + 9) (hilt : S.i < blocks)
    (hmask : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1 x = readByte s x)
    (hentry : ∀ x, x < S.ep ∨ S.ep + 4 * ext ≤ x →
      readByte r2 x = readByte (writeBytes r1 S.entw bs) x)
    (hblk : readBytes s (S.b + 64 * S.i) 64 = some (block64 lo hi)) :
    readBytes r2 (S.b + 64 * S.i) 64 = some (block64 lo hi) := by
  have hsc := disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega)
    Ssep.win_sc
  have hmk := disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega)
    Ssep.win_mk
  have hep : S.b + 64 * S.i + 64 ≤ S.ep ∨ S.ep + 4 * ext ≤ S.b + 64 * S.i := by
    rcases Ssep.win_ep with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hew : S.b + 64 * S.i + 64 ≤ S.entw ∨ S.entw + bs.length ≤ S.b + 64 * S.i := by
    rcases Ssep.win_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbs]; omega)
  rw [readBytes_mask_store_entry_of_disj hmask hentry hsc hmk hep hew, hblk]

/-- **The escape list's call at the pipeline's block.**  The record's `pre` is
`escapePre_of_staged_window` at the three words the arm loaded, and its `post` is
destructured to the four facts the successor reads: the advanced count, the
outgoing pair, the capacity at the block's own extent, and the exclusion.

The post names its own classifier state, which need not be the mask unit's; what
the successor needs is not the state but the outgoing *parity*, and that is pinned
by the pair the two records both read — the post's incoming `carryPair` and the
caller's are the same sixteen bytes, so `pair_flags` makes their flags one pair
and `carry64_oddRun_congr` carries the equality through the block.  That is the
`opened = prevb ∧ ppar = prevs` conjunct the invariant carries, used where it is
needed rather than assumed into the records. -/
theorem escapeCall_at (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {S : PipelineLoopCarried}
    {r2 : CallOutcome} {lo hi : Block32} {stm : ClassState}
    {w5 w6 w7 : BitVec 64}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hblk : readBytes r2.mem (base + blockAddr (BitVec.ofNat 64 S.i)) 64 =
      some (block64 lo hi))
    (hbs : w5 = specBackslash64 lo hi stm)
    (hctl : w6 = specControl64 lo hi stm)
    (him : w7 = specInString64 lo hi stm)
    (hcarry : carryPair r2.mem S.xcarry stm S.prevb S.prevs)
    (hcount : readBytes r2.mem S.nxp 8 = some (wordBytes 8 S.xn))
    (hxn0 : S.xn < 2 ^ 63)
    (hdCount : S.nxp + 8 ≤ S.xp ∨ S.xp + 4 * blockMax S.xn ≤ S.nxp)
    (hdCarry : S.xcarry + 16 ≤ S.nxp ∨ S.nxp + 8 ≤ S.xcarry)
    (hdStream : S.xcarry + 16 ≤ S.xp ∨ S.xp + 4 * blockMax S.xn ≤ S.xcarry)
    (hhas : HasBytes r2.mem S.xp (4 * blockMax S.xn)) :
    ∃ (r3 : CallOutcome) (ste : ClassState) (len : Nat),
      pipelineCalls tab base s2 escapeListSym
        [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 S.iw, .ptr S.xp, .ptr S.nxp,
         .ptr S.xcarry] r2.mem r2.next = some r3 ∧
      readBytes r3.mem S.nxp 8 = some (wordBytes 8 (S.xn + len)) ∧
      len ≤ 64 ∧
      carryPair r3.mem S.xcarry ste (IsBackslashB (hi ⟨31, by decide⟩)) ste.oddRun ∧
      ste.oddRun = (carry64 lo hi stm).oddRun ∧
      HasBytes r3.mem S.xp (4 * blockMax S.xn) ∧
      UnchangedOutside r2.mem r3.mem
        [(S.xp, 4 * blockMax S.xn), (S.nxp, 8), (S.xcarry, 16)] := by
  have hi64 : S.i < 2 ^ 64 := by omega
  have hcapArg : (BitVec.ofNat 64 S.i).toNat * 64 + 64 < 2 ^ 32 := by
    rw [ofNat64_toNat hi64]
    omega
  have hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 S.iw, .ptr S.xp, .ptr S.nxp,
       .ptr S.xcarry] r2.mem r2.next := by
    rw [hiw]
    refine escapePre_of_staged_window base escapePositionsBudget
      (next := r2.next) (m := S.i) (lo := lo) (hi := hi) (st := stm)
      (prevb := S.prevb) (prevs := S.prevs) (xp := S.xp) (xn := S.nxp)
      (carry := S.xcarry) (xn0 := S.xn) ?_ ?_ ?_ ?_ hcarry hcount hxn0 hdCount
      hdCarry hdStream hhas hcapArg
    · exact hblk
    · exact hbs
    · exact hctl
    · exact him
  obtain ⟨r3, hcall, hpost, -⟩ := units.escape _ r2.mem r2.next hpre
  obtain ⟨xp', xn', carry', blk0', bs', ctl', im', lo', hi', st', prevb', prevs',
    xn0', hargs, hblk', hbs', hctl', him', hcarry', hcount', hxn0', hcountOut,
    -, hcarryOut, hhasOut, hframe⟩ := hpost
  -- the seven arguments read back: an integer argument's injection survives as a
  -- heterogeneous equality, its width equation having reduced to `True`
  simp only [List.cons.injEq, List.nil_eq, Value.ptr.injEq, Value.int.injEq,
    and_true, HEq] at hargs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hargs
  have hbsEq : bs' = w5 := (eq_of_heq h1.2).symm
  have hctlEq : ctl' = w6 := (eq_of_heq h2.2).symm
  have himEq : im' = w7 := (eq_of_heq h3.2).symm
  have hblk0Eq : blk0' = BitVec.ofNat 64 S.i := by rw [← eq_of_heq h4.2, hiw]
  have hxpEq : xp' = S.xp := h5.symm
  have hxnEq : xn' = S.nxp := h6.symm
  have hcarryAddrEq : carry' = S.xcarry := h7.symm
  have hbsEq' : bs' = specBackslash64 lo hi stm := hbsEq.trans hbs
  have hctlEq' : ctl' = specControl64 lo hi stm := hctlEq.trans hctl
  have himEq' : im' = specInString64 lo hi stm := himEq.trans him
  rw [hxpEq] at hframe hhasOut
  rw [hxnEq] at hframe hcountOut
  rw [hcarryAddrEq] at hframe hcarry' hcarryOut
  -- the block's halves are the ones the mask unit's post named
  have hblkEq : block64 lo' hi' = block64 lo hi := by
    rw [hblk0Eq] at hblk'
    rw [hblk'] at hblk
    exact Option.some.inj hblk
  obtain ⟨hlo, hhi⟩ := block64_inj hblkEq
  rw [hlo, hhi] at hcarryOut hcountOut
  -- the incoming pair is the caller's, so the two states' parities agree
  have hpairEq : prevb' = S.prevb ∧ prevs' = S.prevs :=
    pair_flags hcarry'.1 hcarry.1
  have hstEq : st'.oddRun = stm.oddRun := by
    rw [hcarry'.2, hcarry.2, hpairEq.1, hpairEq.2]
  have hparity : (carry64 lo hi st').oddRun = (carry64 lo hi stm).oddRun :=
    carry64_oddRun_congr hstEq
  -- the count's representative is the caller's, so the extents agree
  have hcntEq : xn0' = S.xn := by
    have hbytes : wordBytes 8 xn0' = wordBytes 8 S.xn := by
      rw [hxnEq, hcount] at hcount'
      exact (Option.some.inj hcount').symm
    exact natToBytes8_inj hxn0' (by omega) hbytes
  rw [hcntEq] at hcountOut hhasOut hframe
  -- the record's `31 < 32` witness is not the caller's; the lane is the same
  have hfin : (⟨31, escapePositionsPost._proof_1⟩ : Fin 32) = ⟨31, by decide⟩ :=
    Fin.ext rfl
  rw [hfin] at hcarryOut
  exact ⟨r3, carry64 lo hi st', _, by simpa only [hiw] using hcall, hcountOut,
    escapePositionsFrom_length_le_block lo hi st', hcarryOut, hparity, hhasOut, hframe⟩

/-! ### One gate-on iteration's calls, named one fact per field

The two gate-on arms make the same five-step iteration: the mask unit at the
block's staged address, the body's own store of the entry word, one of the two
emitters at the slot it wrote, the three words the block loads back for its
report, and the escape list at those words.  A successor's conjunct reads one of
those facts, so the bundle is a structure with a field apiece rather than one
conjunction: a field's name says which conjunct consumes it, and a change to one
step of the iteration cannot silently renumber the rest. -/
structure GateCalls (calls : Calls) (entrySym : String) (S : PipelineLoopCarried)
    (blocks : Nat) (s : State) : Type where
  /-- The block the iteration reads, as two halves.  Each field is declared on a
  line of its own: a multi-name field group's later names leak into the next
  field's type as binders, which silently turns a field into a function. -/
  lo : Block32
  hi : Block32
  /-- The mask unit's incoming classifier state, and the escape list's outgoing
  one: the two records name their own witnesses, and only the outgoing parity is
  shared. -/
  stm : ClassState
  ste : ClassState
  /-- The three calls' outcomes. -/
  r1 : CallOutcome
  r2 : CallOutcome
  r3 : CallOutcome
  /-- The entry emitter's count, the extent its record writes, and the block's own
  number of escape positions: the two emitters reserve seven and eight entries, so
  the extent is a field rather than a constant. -/
  k' : Nat
  entryExt : Nat
  len : Nat
  /-- The seven words the arm loads: the mask unit's four and the report's three,
  the in-string word being read twice. -/
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  /-- The mask unit's call at the block's staged address. -/
  blockCall : calls JsonPipelineIR.masksSym
    [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc, .ptr S.maskSlot]
    s.mem s.next = some r1
  /-- Its frame: everything outside the two slots it writes. -/
  blockFrame : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
    ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1.mem x = readByte s.mem x
  /-- The four words the arm loads from the mask unit's post. -/
  ld1 : readBytes r1.mem S.maskSlot 8 = some (natToBytes w1.toNat 8)
  ld2 : readBytes r1.mem S.delim 8 = some (natToBytes w2.toNat 8)
  ld3 : readBytes r1.mem S.inString 8 = some (natToBytes w3.toNat 8)
  ld4 : readBytes r1.mem S.ws 8 = some (natToBytes w4.toNat 8)
  /-- The slot's outgoing pair, which is the successor's mask carry. -/
  scSlot : readBytes r1.mem S.sc 24 = some (carrySlot
    (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi stm).oddRun
    (carry64 lo hi stm).inside)
  /-- The entry emitter's call, after the body's own store. -/
  entryCall : calls entrySym
    [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
    (writeBytes r1.mem S.entw (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8))
    r1.next = some r2
  /-- Its returned count. -/
  entryRet : r2.ret = .int 64 (BitVec.ofNat 64 k')
  /-- Its frame, at the extent its own record reserves for one block. -/
  entryFrame : ∀ x, x < S.ep ∨ S.ep + 4 * entryExt ≤ x →
    readByte r2.mem x = readByte (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw w1 w2 w3 w4 S.sw).toNat 8)) x
  /-- The extent sits inside the staged entry stream, so the frames compose. -/
  entryExtLe : entryExt ≤ S.k0 + 64 * blocks + 9
  /-- The count grows by at most one block's sixty-four lanes. -/
  kgrow : k' ≤ S.k + 64
  /-- The three words the escape list is called at, read after the emitter. -/
  ld5 : readBytes r2.mem S.backslash 8 = some (natToBytes w5.toNat 8)
  ld6 : readBytes r2.mem S.ctl 8 = some (natToBytes w6.toNat 8)
  ld7 : readBytes r2.mem S.inString 8 = some (natToBytes w7.toNat 8)
  /-- The escape list's call at those words and the arm's pointers. -/
  escapeCall : calls JsonPipelineIR.escapeListSym
    [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 S.iw, .ptr S.xp, .ptr S.nxp,
     .ptr S.xcarry] r2.mem r2.next = some r3
  /-- Its exclusion, at the block's own extent: the frame the successor's static
  regions survive by. -/
  escapeFrame : UnchangedOutside r2.mem r3.mem
    [(S.xp, 4 * blockMax S.xn), (S.nxp, 8), (S.xcarry, 16)]
  /-- The count it leaves, advanced by the block's positions. -/
  escapeCount : readBytes r3.mem S.nxp 8 = some (wordBytes 8 (S.xn + len))
  /-- A block's positions number at most sixty-four, so the count's growth bound
  survives the list as it survived the emitter. -/
  lenLe : len ≤ 64
  /-- The outgoing carry pair, at the state the list names. -/
  escapeCarry : carryPair r3.mem S.xcarry ste
    (IsBackslashB (hi ⟨31, by decide⟩)) ste.oddRun
  /-- The list's own state leaves the block with the mask unit's outgoing parity:
  the two records' incoming pairs are the same sixteen bytes. -/
  parity : ste.oddRun = (carry64 lo hi stm).oddRun
  /-- The staged stream's whole capacity, carried through the list. -/
  escapeCapacity : HasBytes r3.mem S.xp (4 * S.xpExtent)
  /-- The window, the table and the mask unit's carry slot, untouched. -/
  window : readBytes r3.mem S.b (64 * blocks) = some S.doc
  table : readBytes r3.mem S.tab 8192 = some pos8Table
  scSlot3 : readBytes r3.mem S.sc 24 = some (carrySlot
    (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi stm).oddRun
    (carry64 lo hi stm).inside)

/-- **One gate-on iteration after its entry emitter.**  The loads, the escape
list's call and what survives it are the same at both gate-on arms; the arms
differ in which emitter ran, at which symbol and at which reserve.  So the trace
after the emitter takes the emitter's three facts — its call, its returned count
and its frame at its own extent — and derives the rest once.

Two identifications are the work rather than the calls: the block the list is
given is the one the mask unit's post named (`gateBlock_at` at the index's
offset, then `block64_inj`, since the record reads the block itself rather than
taking the halves), and the list's outgoing parity is the mask unit's
(`escapeCall_at` reads the two records' shared incoming pair). -/
theorem gateCalls_after_entry (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried} {entrySym : String}
    {lo hi : Block32} {stm : ClassState} {r1 r2 : CallOutcome}
    {k' entryExt : Nat}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hib : S.i + 1 ≤ blocks) (hb : S.b = base)
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hcarry : carryPair s.mem S.xcarry S.stE S.prevb S.prevs)
    (hflags : S.opened = S.prevb ∧ S.ppar = S.prevs)
    (hinS : S.inString = S.maskSlot + 16) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40)
    (Ssep : StagedSep S blocks)
    (htab : readBytes s.mem S.tab 8192 = some pos8Table)
    (hkgrow : S.k ≤ S.k0 + 64 * S.i) (hxngrow : S.xn ≤ S.xn0 + 64 * S.i)
    (hroomk : cursorRoom S.k (blocks - S.i) 9)
    (hroomxn : cursorRoom S.xn (blocks - S.i) 9)
    (hcnt : readBytes s.mem S.nxp 8 = some (wordBytes 8 S.xn))
    (hhas : HasBytes s.mem S.xp (4 * S.xpExtent))
    (hxpExtent : S.xpExtent = S.xn0 + 64 * blocks + 8)
    (hcall1 : (pipelineCalls tab base s2) JsonPipelineIR.masksSym
      [.ptr (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat), .ptr S.sc, .ptr S.maskSlot]
      s.mem s.next = some r1)
    (hmaskFrame : ∀ x, ¬ (S.sc ≤ x ∧ x < S.sc + 24) →
      ¬ (S.maskSlot ≤ x ∧ x < S.maskSlot + 48) → readByte r1.mem x = readByte s.mem x)
    (hw1 : readBytes r1.mem S.maskSlot 8 = some (natToBytes (specQuote64 lo hi stm).toNat 8))
    (hw2 : readBytes r1.mem S.delim 8 = some (natToBytes (specDelimiter64 lo hi stm).toNat 8))
    (hw3 : readBytes r1.mem S.inString 8 = some (natToBytes (specInString64 lo hi stm).toNat 8))
    (hw4 : readBytes r1.mem S.ws 8 = some (natToBytes (specSpace64 lo hi stm).toNat 8))
    (hw5 : readBytes r1.mem S.backslash 8 = some (natToBytes (specBackslash64 lo hi stm).toNat 8))
    (hw6 : readBytes r1.mem S.ctl 8 = some (natToBytes (specControl64 lo hi stm).toNat 8))
    (hscPost : readBytes r1.mem S.sc 24 = some (carrySlot
      (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi stm).oddRun
      (carry64 lo hi stm).inside))
    (hparM : stm.oddRun = (S.opened && S.ppar))
    (hblkAt : readBytes s.mem (S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat) 64 =
      some (block64 lo hi))
    (hentryCall : (pipelineCalls tab base s2) entrySym
      [.ptr S.entw, .int 64 S.iw, .int 64 (1 : BitVec 64), .ptr S.ep, .int 64 S.kw]
      (writeBytes r1.mem S.entw (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)) r1.next = some r2)
    (hentryRet : r2.ret = .int 64 (BitVec.ofNat 64 k'))
    (hentFrame : ∀ x, x < S.ep ∨ S.ep + 4 * entryExt ≤ x →
      readByte r2.mem x = readByte (writeBytes r1.mem S.entw
        (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
          (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) x)
    (hkgrow' : k' ≤ S.k + 64)
    (hentExtLe : entryExt ≤ S.k0 + 64 * blocks + 9) :
    Nonempty (GateCalls (pipelineCalls tab base s2) entrySym S blocks s) := by
  have hbslen : (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
      (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
      (specSpace64 lo hi stm) S.sw).toNat 8).length = 8 := natToBytes_length ..
  have hstored : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8) := by
    have h := readBytes_writeBytes_same r1.mem
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)
      (addr := S.entw)
    rw [hbslen] at h
    exact h
  have htab' : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.tab 8192 =
      some pos8Table := by
    have hew : S.tab + 8192 ≤ S.entw ∨
        S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
          (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
          (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.tab := by
      rcases Ssep.tab_ent with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hbslen]; exact h)
    refine Eq.trans ?_ htab
    exact readBytes_of_readByte_eq (fun k hk => by
      rw [readByte_writeBytes_outside r1.mem _ (by
            rcases hew with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)),
        hmaskFrame _ (not_inside_of_disjoint Ssep.tab_sc hk)
          (not_inside_of_disjoint Ssep.tab_mk hk)])
  have hep5 : S.backslash + 8 ≤ S.ep ∨ S.ep + 4 * (entryExt) ≤ S.backslash := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew5 : S.backslash + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.backslash := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld5 : readBytes r2.mem S.backslash 8 =
      some (natToBytes (specBackslash64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := entryExt) hentFrame hep5 hew5, hw5]
  have hep6 : S.ctl + 8 ≤ S.ep ∨ S.ep + 4 * (entryExt) ≤ S.ctl := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew6 : S.ctl + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.ctl := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld6 : readBytes r2.mem S.ctl 8 =
      some (natToBytes (specControl64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := entryExt) hentFrame hep6 hew6, hw6]
  have hep7 : S.inString + 8 ≤ S.ep ∨ S.ep + 4 * (entryExt) ≤ S.inString := by
    rcases Ssep.mk_ep with h | h
    · omega
    · exact Or.inr (by omega)
  have hew7 : S.inString + 8 ≤ S.entw ∨
      S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.inString := by
    rcases Ssep.mk_ent with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hbslen]; omega)
  have hld7 : readBytes r2.mem S.inString 8 =
      some (natToBytes (specInString64 lo hi stm).toNat 8) := by
    rw [readBytes_entry_frame (ext := entryExt) hentFrame hep7 hew7, hw3]
  -- the block, at the offset the record reads it at
  have hblkR2 : readBytes r2.mem (S.b + 64 * S.i) 64 = some (block64 lo hi) :=
    gateBlock_at (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
      (r2 := r2.mem) (ext := entryExt)
      (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)
      Ssep hbslen hentExtLe hilt hmaskFrame hentFrame (by
        have haddr : S.b + (BitVec.signExtend 64 (sh6 S.iw)).toNat = S.b + 64 * S.i := by
          rw [hiw, sh6_ofNat_toNat (by omega)]
        rw [← haddr]
        exact hblkAt)
  have hblkBase : readBytes r2.mem (base + blockAddr (BitVec.ofNat 64 S.i)) 64 =
      some (block64 lo hi) := by
    have hba : blockAddr (BitVec.ofNat 64 S.i) = 64 * S.i := by
      unfold blockAddr
      rw [ofNat64_toNat (by omega)]
      omega
    rw [← hb, hba]
    exact hblkR2
  -- the pair the list reads is the one the invariant carries, at the memory the
  -- emitter left: its sixteen bytes are outside every store of the iteration
  have hcarryR2 : carryPair r2.mem S.xcarry stm S.prevb S.prevs := by
    have hxcBytes : readBytes r2.mem S.xcarry 16 =
        some (flagBytes S.prevb ++ flagBytes S.prevs) := by
      have hep : S.xcarry + 16 ≤ S.ep ∨ S.ep + 4 * (entryExt) ≤ S.xcarry := by
        rcases Ssep.ep_xc with h | h
        · exact Or.inr (by omega)
        · exact Or.inl h
      have hew : S.xcarry + 16 ≤ S.entw ∨
          S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
            (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
            (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.xcarry := by
        rcases Ssep.ent_xc with h | h
        · exact Or.inr (by rw [hbslen]; omega)
        · exact Or.inl h
      rw [readBytes_mask_store_entry_of_disj hmaskFrame hentFrame
        (sep_comm Ssep.sc_xc) (sep_comm Ssep.mk_xc) hep hew, hcarry.1]
    refine ⟨hxcBytes, ?_⟩
    rw [hparM, hflags.1, hflags.2]
  -- the count's room, and the block's extent inside the staged capacity
  have hxn0 : S.xn < 2 ^ 63 := by
    have h := hroomxn
    unfold cursorRoom at h
    omega
  have hbm' : S.xn + 72 ≤ S.xpExtent := by
    have h := hxngrow
    rw [hxpExtent]
    omega
  have hbm : blockMax S.xn ≤ S.xpExtent := by
    unfold blockMax
    exact hbm'
  have hdCount : S.nxp + 8 ≤ S.xp ∨ S.xp + 4 * blockMax S.xn ≤ S.nxp := by
    rcases Ssep.nxp_xp with h | h
    · exact Or.inl h
    · exact Or.inr (by unfold blockMax batchReserve; omega)
  have hdCarry : S.xcarry + 16 ≤ S.nxp ∨ S.nxp + 8 ≤ S.xcarry := by
    rcases Ssep.nxp_xc with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hdStream : S.xcarry + 16 ≤ S.xp ∨ S.xp + 4 * blockMax S.xn ≤ S.xcarry := by
    rcases Ssep.xp_xc with h | h
    · exact Or.inr (by unfold blockMax batchReserve; omega)
    · exact Or.inl h
  have hhasR2 : HasBytes r2.mem S.xp (4 * blockMax S.xn) := by
    refine hasBytes_of_le (a := S.xp) (K := 4 * S.xpExtent)
      (usUsSucc_capacity (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
        (r2 := r2.mem) (ext := entryExt)
        (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
          (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
          (specSpace64 lo hi stm) S.sw).toNat 8)
        Ssep hbslen hentExtLe hmaskFrame hentFrame hhas) ?_
    unfold blockMax batchReserve
    omega
  have hcnt2 : readBytes r2.mem S.nxp 8 = some (wordBytes 8 S.xn) :=
    usUsSucc_count (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
      (r2 := r2.mem) (ext := entryExt)
      (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)
      Ssep hbslen hentExtLe hmaskFrame hentFrame hcnt
  obtain ⟨r3, ste, len, hcall3, hescCount, hlen, hescCarry, hparity, hhasPost,
    hframe⟩ :=
    escapeCall_at (tab := tab) (base := base) (s2 := s2) (Γ2 := Γ2) units
      (S := S) (r2 := r2) (lo := lo) (hi := hi) (stm := stm)
      (w5 := specBackslash64 lo hi stm) (w6 := specControl64 lo hi stm)
      (w7 := specInString64 lo hi stm)
      hcap hiw hilt hblkBase rfl rfl rfl hcarryR2 hcnt2 hxn0 hdCount hdCarry hdStream
      hhasR2
  -- what survives the list: the window, the table, the mask slot and the stream
  have hwin2 : readBytes r2.mem S.b (64 * blocks) = some S.doc :=
    usUsSucc_window (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
      (r2 := r2.mem) (ext := entryExt)
      (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)
      Ssep hbslen hentExtLe hmaskFrame hentFrame hwin
  have htab2 : readBytes r2.mem S.tab 8192 = some pos8Table :=
    usUsSucc_table (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
      (r2 := r2.mem) (ext := entryExt)
      (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)
      Ssep hbslen hentExtLe hmaskFrame hentFrame htab
  have hsc2 : readBytes r2.mem S.sc 24 = some (carrySlot
      (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi stm).oddRun
      (carry64 lo hi stm).inside) :=
    usUsSucc_carrySlot (S := S) (blocks := blocks) (s := s.mem) (r1 := r1.mem)
      (r2 := r2.mem) (ext := entryExt)
      (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8)
      (op := IsBackslashB (hi ⟨31, by decide⟩)) (p := (carry64 lo hi stm).oddRun)
      (ins := (carry64 lo hi stm).inside)
      Ssep hbslen hentExtLe hentFrame hscPost
  refine ⟨{
    lo := lo, hi := hi, stm := stm, ste := ste, r1 := r1, r2 := r2, r3 := r3,
    k' := k', entryExt := entryExt, len := len,
    w1 := specQuote64 lo hi stm, w2 := specDelimiter64 lo hi stm,
    w3 := specInString64 lo hi stm, w4 := specSpace64 lo hi stm,
    w5 := specBackslash64 lo hi stm, w6 := specControl64 lo hi stm,
    w7 := specInString64 lo hi stm,
    blockCall := hcall1, blockFrame := hmaskFrame, ld1 := hw1, ld2 := hw2,
    ld3 := hw3, ld4 := hw4, scSlot := hscPost, entryCall := hentryCall,
    entryRet := hentryRet, entryFrame := hentFrame, entryExtLe := hentExtLe,
    kgrow := hkgrow', ld5 := hld5, ld6 := hld6, ld7 := hld7,
    escapeCall := hcall3, escapeFrame := hframe,
    escapeCount := hescCount, lenLe := hlen, escapeCarry := hescCarry,
    parity := hparity, escapeCapacity := ?_, window := ?_, table := ?_,
    scSlot3 := ?_ }⟩
  · -- the staged capacity, extended to the call's own extent
    refine escape_capacity (r2 := r2.mem) (r3 := r3.mem) (xp := S.xp)
      (xn := S.nxp) (xcarry := S.xcarry) (xn0 := S.xn)
      (extent := S.xpExtent) hframe hhasPost ?_ hbm ?_ ?_
    · exact usUsSucc_capacity (S := S) (blocks := blocks) (s := s.mem)
        (r1 := r1.mem) (r2 := r2.mem) (ext := entryExt)
        (bs := natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
          (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
          (specSpace64 lo hi stm) S.sw).toNat 8)
        Ssep hbslen hentExtLe hmaskFrame hentFrame hhas
    · rcases Ssep.nxp_xp with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases Ssep.xp_xc with h | h
      · exact Or.inl h
      · exact Or.inr h
  · exact gateSucc_window (S := S) (blocks := blocks) Ssep hbm hframe hwin2
  · exact gateSucc_table (S := S) (blocks := blocks) Ssep hbm hframe htab2
  · exact gateSucc_scSlot (S := S) (blocks := blocks) Ssep hbm hframe hsc2

  -- hhbm is the extent hypothesis the three static survivors take

/-- **One POS8-with-gate iteration's calls.**  The mask unit at the block's staged
address, the body's own store of the entry word, the POS8 emitter at the slot the
body wrote, and then `gateCalls_after_entry` at the emitter's facts. -/
theorem us_calls (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hib : S.i + 1 ≤ blocks) (hb : S.b = base)
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hcarry : carryPair s.mem S.xcarry S.stE S.prevb S.prevs)
    (hflags : S.opened = S.prevb ∧ S.ppar = S.prevs)
    (hdelim : S.delim = S.maskSlot + 8) (hinS : S.inString = S.maskSlot + 16)
    (hwsS : S.ws = S.maskSlot + 24) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40) (Ssep : StagedSep S blocks)
    (htabEq : S.tab = tab)
    (htab : readBytes s.mem S.tab 8192 = some pos8Table)
    (hkw : S.kw = BitVec.ofNat 64 S.k)
    (hkgrow : S.k ≤ S.k0 + 64 * S.i) (hxngrow : S.xn ≤ S.xn0 + 64 * S.i)
    (hroomk : cursorRoom S.k (blocks - S.i) 9)
    (hroomxn : cursorRoom S.xn (blocks - S.i) 9)
    (hcnt : readBytes s.mem S.nxp 8 = some (wordBytes 8 S.xn))
    (hhas : HasBytes s.mem S.xp (4 * S.xpExtent))
    (hxpExtent : S.xpExtent = S.xn0 + 64 * blocks + 8) :
    Nonempty (GateCalls (pipelineCalls tab base s2) JsonPipelineIR.entryPos8Sym S blocks s) := by
  have hdoc : S.doc.length = 64 * blocks := by
    have := readBytes_len hwin
    simpa using this
  have hdist : (S.b + 64 * S.i + 64 ≤ S.sc ∨ S.sc + 24 ≤ S.b + 64 * S.i) ∧
      (S.b + 64 * S.i + 64 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b + 64 * S.i) ∧
      (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc) :=
    ⟨disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_sc,
     disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_mk,
     Ssep.sc_mk⟩
  obtain ⟨lo, hi, stm, r1, hcall1, hw1, hw2, hw3, hw4, hw5, hw6, hscPost, hmaskFrame,
    hparM, hblkAt⟩ :=
    maskCall_at tab base s2 Γ2 units (S := S) hwin hsc hiw hilt hcap hdoc hdelim hinS
      hwsS hbsS hctl hdist
  have hbslen : (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
      (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
      (specSpace64 lo hi stm) S.sw).toNat 8).length = 8 := natToBytes_length ..
  have hstored : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8) := by
    have h := readBytes_writeBytes_same r1.mem
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)
      (addr := S.entw)
    rw [hbslen] at h
    exact h
  have htab' : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.tab 8192 =
      some pos8Table := by
    have hew : S.tab + 8192 ≤ S.entw ∨
        S.entw + (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
          (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
          (specSpace64 lo hi stm) S.sw).toNat 8).length ≤ S.tab := by
      rcases Ssep.tab_ent with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hbslen]; exact h)
    refine Eq.trans ?_ htab
    exact readBytes_of_readByte_eq (fun k hk => by
      rw [readByte_writeBytes_outside r1.mem _ (by
            rcases hew with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)),
        hmaskFrame _ (not_inside_of_disjoint Ssep.tab_sc hk)
          (not_inside_of_disjoint Ssep.tab_mk hk)])
  have hk64 : S.k < 2 ^ 64 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  have hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw := by
    rcases Ssep.ent_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hsepTab : S.tab + 8192 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.tab := by
    rcases Ssep.tab_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hroom : S.k + 64 + 9 < 2 ^ 63 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  obtain ⟨r2, k', o, hcall2, hret2, hentFrame, ho, hk'le⟩ :=
    pos8Call_at tab base s2 Γ2 units (S := S) (lo := lo) (hi := hi) (st := stm)
      htabEq hstored htab' hiw hib hcap hkw hk64 hsepWord hsepTab hroom
  rw [ho] at hentFrame
  have hextK : k' + 8 ≤ S.k0 + 64 * blocks + 9 := by omega
  exact gateCalls_after_entry tab base s2 Γ2 units (S := S)
    (entrySym := JsonPipelineIR.entryPos8Sym) (lo := lo) (hi := hi) (stm := stm)
    (r1 := r1) (r2 := r2) (k' := k') (entryExt := k' + 8)
    hcap hiw hilt hib hb hwin hsc hcarry hflags hinS hbsS hctl Ssep htab hkgrow
    hxngrow hroomk hroomxn hcnt hhas hxpExtent hcall1 hmaskFrame hw1 hw2 hw3 hw4 hw5
    hw6 hscPost hparM hblkAt hcall2 hret2 hentFrame hk'le hextK

/-- **One B8-with-gate iteration's calls.**  The same iteration at the B8 emitter,
whose record reserves seven entries rather than eight; the entry call is the only
difference, and the rest is `gateCalls_after_entry`. -/
theorem body_calls (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) {blocks : Nat} {s : State}
    {S : PipelineLoopCarried}
    (hcap : 64 * blocks + 63 < 2 ^ 32)
    (hiw : S.iw = BitVec.ofNat 64 S.i) (hilt : S.i < blocks)
    (hib : S.i + 1 ≤ blocks) (hb : S.b = base)
    (hwin : readBytes s.mem S.b (64 * blocks) = some S.doc)
    (hsc : readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside))
    (hcarry : carryPair s.mem S.xcarry S.stE S.prevb S.prevs)
    (hflags : S.opened = S.prevb ∧ S.ppar = S.prevs)
    (hdelim : S.delim = S.maskSlot + 8) (hinS : S.inString = S.maskSlot + 16)
    (hwsS : S.ws = S.maskSlot + 24) (hbsS : S.backslash = S.maskSlot + 32)
    (hctl : S.ctl = S.maskSlot + 40) (Ssep : StagedSep S blocks)
    (htab : readBytes s.mem S.tab 8192 = some pos8Table)
    (hkw : S.kw = BitVec.ofNat 64 S.k)
    (hkgrow : S.k ≤ S.k0 + 64 * S.i) (hxngrow : S.xn ≤ S.xn0 + 64 * S.i)
    (hroomk : cursorRoom S.k (blocks - S.i) 9)
    (hroomxn : cursorRoom S.xn (blocks - S.i) 9)
    (hcnt : readBytes s.mem S.nxp 8 = some (wordBytes 8 S.xn))
    (hhas : HasBytes s.mem S.xp (4 * S.xpExtent))
    (hxpExtent : S.xpExtent = S.xn0 + 64 * blocks + 8) :
    Nonempty (GateCalls (pipelineCalls tab base s2) JsonPipelineIR.entryB8Sym S blocks s) := by
  have hdoc : S.doc.length = 64 * blocks := by
    have := readBytes_len hwin
    simpa using this
  have hdist : (S.b + 64 * S.i + 64 ≤ S.sc ∨ S.sc + 24 ≤ S.b + 64 * S.i) ∧
      (S.b + 64 * S.i + 64 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b + 64 * S.i) ∧
      (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc) :=
    ⟨disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_sc,
     disjoint_of_sub (a' := S.b + 64 * S.i) (n' := 64) (by omega) (by omega) Ssep.win_mk,
     Ssep.sc_mk⟩
  obtain ⟨lo, hi, stm, r1, hcall1, hw1, hw2, hw3, hw4, hw5, hw6, hscPost, hmaskFrame,
    hparM, hblkAt⟩ :=
    maskCall_at tab base s2 Γ2 units (S := S) hwin hsc hiw hilt hcap hdoc hdelim hinS
      hwsS hbsS hctl hdist
  have hbslen : (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
      (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
      (specSpace64 lo hi stm) S.sw).toNat 8).length = 8 := natToBytes_length ..
  have hstored : readBytes (writeBytes r1.mem S.entw
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)) S.entw 8 =
      some (natToBytes (vent S.n S.iw (specQuote64 lo hi stm)
        (specDelimiter64 lo hi stm) (specInString64 lo hi stm)
        (specSpace64 lo hi stm) S.sw).toNat 8) := by
    have h := readBytes_writeBytes_same r1.mem
      (natToBytes (vent S.n S.iw (specQuote64 lo hi stm) (specDelimiter64 lo hi stm)
        (specInString64 lo hi stm) (specSpace64 lo hi stm) S.sw).toNat 8)
      (addr := S.entw)
    rw [hbslen] at h
    exact h
  have hk64 : S.k < 2 ^ 64 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  have hsepWord : S.entw + 8 ≤ S.ep ∨ S.ep + 4 * (S.k + 64 + 8) ≤ S.entw := by
    rcases Ssep.ent_ep with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hroom : S.k + 64 + 9 < 2 ^ 63 := by
    have h := hroomk
    unfold cursorRoom at h
    omega
  obtain ⟨r2, k', o, hcall2, hret2, hentFrame, ho, hk'le⟩ :=
    b8Call_at tab base s2 Γ2 units (S := S) (lo := lo) (hi := hi) (st := stm)
      hstored hiw hib hcap hkw hk64 hsepWord hroom
  rw [ho] at hentFrame
  have hextK : k' + 7 ≤ S.k0 + 64 * blocks + 9 := by omega
  exact gateCalls_after_entry tab base s2 Γ2 units (S := S)
    (entrySym := JsonPipelineIR.entryB8Sym) (lo := lo) (hi := hi) (stm := stm)
    (r1 := r1) (r2 := r2) (k' := k') (entryExt := k' + 7)
    hcap hiw hilt hib hb hwin hsc hcarry hflags hinS hbsS hctl Ssep htab hkgrow
    hxngrow hroomk hroomxn hcnt hhas hxpExtent hcall1 hmaskFrame hw1 hw2 hw3 hw4 hw5
    hw6 hscPost hparM hblkAt hcall2 hret2 hentFrame hk'le hextK

/-! ### The gate-on successors, and their cell half

The two gate-on arms leave a carried state with the four conjuncts the earlier two
do not carry: the escape list's count, its outgoing state, and the pair the two
slots agree on.  The mask unit's pair and the list's are separate arguments
because they come from separate posts: `opened`/`ppar` are the `%sc` slot's, and
`prevb`/`prevs` the `%xcarry` slot's, and the invariant's `opened = prevb` clause
is where the two are proved one pair. -/

/-- The carried state a `for.body.us` iteration leaves. -/
def usSucc (S : PipelineLoopCarried) (ins bm pm : Bool) (k' xn : Nat)
    (sw : BitVec 64) (stE : ClassState) (eb ep : Bool) : PipelineLoopCarried :=
  { S with arm := .pos8Gate, i := S.i + 1, iw := vinc S.iw, sw := sw, kw := BitVec.ofNat 64 k', stM := ⟨ins, bm && pm⟩, opened := bm, ppar := pm, inside := ins, k := k', xn := xn, stE := stE, prevb := eb, prevs := ep }

/-- The carried state a `for.body` iteration leaves. -/
def bodySucc (S : PipelineLoopCarried) (ins bm pm : Bool) (k' xn : Nat)
    (sw : BitVec 64) (stE : ClassState) (eb ep : Bool) : PipelineLoopCarried :=
  { S with arm := .b8Gate, i := S.i + 1, iw := vinc S.iw, sw := sw, kw := BitVec.ofNat 64 k', stM := ⟨ins, bm && pm⟩, opened := bm, ppar := pm, inside := ins, k := k', xn := xn, stE := stE, prevb := eb, prevs := ep }

/-- The gate-on arm's outgoing builder holds a value for every cell the next
iteration's incoming builder binds. -/
theorem us_cells_agree' (env : Env) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 c21' inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (ret : Value)
    (hret : ret = .int 64 c21') :
    ∀ p ∈ [("%shr", .int 64 shr), ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp),
           ("%xp", .ptr xp), ("%inc.us", .int 64 (vinc inc)),
           ("%call21.us", .int 64 c21'),
           ("%shr13.us", .int 64 (vshr13 w1 w2 w3 w4)), ("%ep", .ptr ep),
           ("%entw", .ptr entw), ("%ctl", .ptr ctl), ("%backslash", .ptr backslash),
           ("%ws", .ptr ws), ("%in_string", .ptr inString), ("%delim", .ptr delim),
           ("%mk", .ptr mk), ("%sc", .ptr sc), ("%b", .ptr b),
           ("%n", .int 64 n)],
      lookupName (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 ret) p.1 = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals (try rw [hret])
  all_goals block_lk

/-- **The POS8-with-gate successor's agreement**, read back through `agreeOn_succ`. -/
theorem usSucc_agree {S : PipelineLoopCarried} {e : State} {env : Env}
    {k' : Nat} {w1 w2 w3 w4 w5 w6 w7 : BitVec 64} {ret : Value}
    (hret : ret = .int 64 (BitVec.ofNat 64 k'))
    (hag : State.AgreeOn (blockUses pUs)
      (stateAt (usOut env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6
        w7 ret) e) e) :
    State.AgreeOn (blockUses pUs)
      (stateAt (usIn e.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry (vshr13 w1 w2 w3 w4)
        (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e := by
  refine agreeOn_succ (fun p hp => ?_) hag
  exact us_cells_agree' env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
    S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw (BitVec.ofNat 64 k') S.iw S.shr
    w1 w2 w3 w4 w5 w6 w7 ret hret p hp

/-- The B8-with-gate arm's outgoing builder holds a value for every cell the next
iteration's incoming builder binds. -/
theorem body_cells_agree' (env : Env) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 c21' inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (ret : Value)
    (hret : ret = .int 64 c21') :
    ∀ p ∈ [("%shr", .int 64 shr), ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp),
           ("%xp", .ptr xp), ("%inc", .int 64 (vinc inc)),
           ("%call", .int 64 c21'),
           ("%shr13", .int 64 (vshr13 w1 w2 w3 w4)), ("%ep", .ptr ep),
           ("%entw", .ptr entw), ("%ctl", .ptr ctl), ("%backslash", .ptr backslash),
           ("%ws", .ptr ws), ("%in_string", .ptr inString), ("%delim", .ptr delim),
           ("%mk", .ptr mk), ("%sc", .ptr sc), ("%b", .ptr b),
           ("%n", .int 64 n)],
      lookupName (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 ret) p.1 = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals (try rw [hret])
  all_goals block_lk

/-- **The B8-with-gate successor's agreement**, read back through `agreeOn_succ`. -/
theorem bodySucc_agree {S : PipelineLoopCarried} {e : State} {env : Env}
    {k' : Nat} {w1 w2 w3 w4 w5 w6 w7 : BitVec 64} {ret : Value}
    (hret : ret = .int 64 (BitVec.ofNat 64 k'))
    (hag : State.AgreeOn (blockUses pBody)
      (stateAt (bodyOut env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6
        w7 ret) e) e) :
    State.AgreeOn (blockUses pBody)
      (stateAt (bodyIn e.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry (vshr13 w1 w2 w3 w4)
        (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e := by
  refine agreeOn_succ (fun p hp => ?_) hag
  exact body_cells_agree' env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
    S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw (BitVec.ofNat 64 k') S.iw S.shr
    w1 w2 w3 w4 w5 w6 w7 ret hret p hp

/-- **A `for.body.us` iteration that delays.**  With more than one iteration of
budget left the exit test is zero and the arm branches to itself; the successor's
twenty-eight clauses are the invariant's own projections, the call bundle's fields,
and the frames that leave every static region in place. -/
theorem us_step_head (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks n : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks (n + 1) s)
    (hn : 0 < n) (hpc0 : s.pc = "for.body.us") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks n e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n' =>
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .pos8Gate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hcarryI : carryPair s.mem S.xcarry S.stE S.prevb S.prevs := hcarry rfl
  have hflagsI : S.opened = S.prevb ∧ S.ppar = S.prevs := hflags rfl
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨g⟩ := us_calls tab base s2 Γ2 units (S := S) hcap hiw hilt (by omega) hb hwin
    hsc hcarryI hflagsI hdelim hinS hwsS hbsS hctl hsep htabEq htab hkw hkgrow hxngrow
    hroomk hroomxn hcnt hhas hxpExt
  obtain ⟨lo, hi, stm, ste, r1, r2, r3, k', entryExt, len, w1, w2, w3, w4, w5, w6, w7,
    hcall1, hmaskFrame, hld1, hld2, hld3, hld4, hscPost, hcall2, hret2, hentFrame,
    hextLe, hkgrow', hld5, hld6, hld7, hcall3, hescFrame, hescCount, hlenLe, hescCarry,
    hparity, hescCap, hwinR3, htabR3, hscR3⟩ := g
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := us_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw
    S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r1 r2 r3 hpre' hld1 hld2 hld3 hld4 hpos hcall1
    hcall2 hld5 hld6 hld7 hcall3
  have hvexit : vexit S.iw S.shr = 0 := by
    rw [vexit_eq_zero]
    intro hcon
    rw [hiw, vinc_ofNat (by omega), hshr] at hcon
    exact (by omega : S.i + 1 ≠ blocks) ((ofNat64_eq_iff (by omega) (by omega)).mp hcon)
  obtain ⟨t', jt, hjt, hden, hag, hrun⟩ := us_step_at_head (pipelineCalls tab base s2)
    s.env s S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl S.entw
    S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r2 r3 hpcS
    hagree hcode hvexit
  let e : State := { t' with pc := "for.body.us", pre := some s.pc }
  have hmem : e.mem = r3.mem := hag.1.symm
  have hagE : State.AgreeOn (blockUses pUs)
      (stateAt (usOut s.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7
        r2.ret) e) e :=
    ⟨rfl, rfl, rfl, fun x hx => hag.2.2.2 x hx⟩
  refine ⟨e, jt, hjt, ?_, hrun⟩
  refine ⟨usSucc S (carry64 lo hi stm).inside (IsBackslashB (hi ⟨31, by decide⟩))
    (carry64 lo hi stm).oddRun k' (S.xn + len) (vshr13 w1 w2 w3 w4) ste
    (IsBackslashB (hi ⟨31, by decide⟩)) ste.oddRun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show some s.pc = some "for.body.us"
    rw [hpc0]
  · show S.i + 1 + (n' + 1) = blocks
    omega
  · exact hshr
  · show vinc S.iw = BitVec.ofNat 64 (S.i + 1)
    rw [hiw, vinc_ofNat (by omega)]
  · show State.AgreeOn (blockUses pUs) (stateAt (usIn e.env S.n S.b S.sc S.maskSlot
      S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry
      (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e
    exact usSucc_agree hret2 hagE
  · exact hb
  · rw [hmem]; exact hwinR3
  · rw [hmem]; exact hscR3
  · rfl
  · exact hdelim
  · exact hinS
  · exact hwsS
  · exact hbsS
  · exact hctl
  · exact htabEq
  · rw [hmem]; exact htabR3
  · rfl
  · rw [hmem]; exact hescCount
  · exact hxpExt
  · show k' ≤ S.k0 + 64 * (S.i + 1)
    omega
  · show S.xn + len ≤ S.xn0 + 64 * (S.i + 1)
    omega
  · intro _
    rw [hmem]
    exact hescCarry
  · intro _
    refine ⟨rfl, ?_⟩
    show (carry64 lo hi stm).oddRun = ste.oddRun
    exact hparity.symm
  · show cursorRoom k' (blocks - (S.i + 1)) 9
    have hh := hroomk
    unfold cursorRoom at hh ⊢
    omega
  · show cursorRoom (S.xn + len) (blocks - (S.i + 1)) 9
    have hh := hroomxn
    unfold cursorRoom at hh ⊢
    omega
  · rw [hmem]
    exact hescCap
  · exact hdisj

/-- **A `for.body` iteration that delays.**  The B8 emitter's arm, at the same
successor shape: only the entry call differs. -/
theorem body_step_head (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks n : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks (n + 1) s)
    (hn : 0 < n) (hpc0 : s.pc = "for.body") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks n e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n' =>
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .b8Gate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hcarryI : carryPair s.mem S.xcarry S.stE S.prevb S.prevs := hcarry rfl
  have hflagsI : S.opened = S.prevb ∧ S.ppar = S.prevs := hflags rfl
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨g⟩ := body_calls tab base s2 Γ2 units (S := S) hcap hiw hilt (by omega) hb hwin
    hsc hcarryI hflagsI hdelim hinS hwsS hbsS hctl hsep htab hkw hkgrow hxngrow
    hroomk hroomxn hcnt hhas hxpExt
  obtain ⟨lo, hi, stm, ste, r1, r2, r3, k', entryExt, len, w1, w2, w3, w4, w5, w6, w7,
    hcall1, hmaskFrame, hld1, hld2, hld3, hld4, hscPost, hcall2, hret2, hentFrame,
    hextLe, hkgrow', hld5, hld6, hld7, hcall3, hescFrame, hescCount, hlenLe, hescCarry,
    hparity, hescCap, hwinR3, htabR3, hscR3⟩ := g
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := body_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw
    S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r1 r2 r3 hpre' hld1 hld2 hld3 hld4 hpos hcall1
    hcall2 hld5 hld6 hld7 hcall3
  have hvexit : vexit S.iw S.shr = 0 := by
    rw [vexit_eq_zero]
    intro hcon
    rw [hiw, vinc_ofNat (by omega), hshr] at hcon
    exact (by omega : S.i + 1 ≠ blocks) ((ofNat64_eq_iff (by omega) (by omega)).mp hcon)
  obtain ⟨t', jt, hjt, hden, hag, hrun⟩ := body_step_at_head (pipelineCalls tab base s2)
    s.env s S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl S.entw
    S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r2 r3 hpcS
    hagree hcode hvexit
  let e : State := { t' with pc := "for.body", pre := some s.pc }
  have hmem : e.mem = r3.mem := hag.1.symm
  have hagE : State.AgreeOn (blockUses pBody)
      (stateAt (bodyOut s.env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash
        S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7
        r2.ret) e) e :=
    ⟨rfl, rfl, rfl, fun x hx => hag.2.2.2 x hx⟩
  refine ⟨e, jt, hjt, ?_, hrun⟩
  refine ⟨bodySucc S (carry64 lo hi stm).inside (IsBackslashB (hi ⟨31, by decide⟩))
    (carry64 lo hi stm).oddRun k' (S.xn + len) (vshr13 w1 w2 w3 w4) ste
    (IsBackslashB (hi ⟨31, by decide⟩)) ste.oddRun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show some s.pc = some "for.body"
    rw [hpc0]
  · show S.i + 1 + (n' + 1) = blocks
    omega
  · exact hshr
  · show vinc S.iw = BitVec.ofNat 64 (S.i + 1)
    rw [hiw, vinc_ofNat (by omega)]
  · show State.AgreeOn (blockUses pBody) (stateAt (bodyIn e.env S.n S.b S.sc S.maskSlot
      S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry
      (vshr13 w1 w2 w3 w4) (BitVec.ofNat 64 k') (vinc S.iw) S.shr) e) e
    exact bodySucc_agree hret2 hagE
  · exact hb
  · rw [hmem]; exact hwinR3
  · rw [hmem]; exact hscR3
  · rfl
  · exact hdelim
  · exact hinS
  · exact hwsS
  · exact hbsS
  · exact hctl
  · exact htabEq
  · rw [hmem]; exact htabR3
  · rfl
  · rw [hmem]; exact hescCount
  · exact hxpExt
  · show k' ≤ S.k0 + 64 * (S.i + 1)
    omega
  · show S.xn + len ≤ S.xn0 + 64 * (S.i + 1)
    omega
  · intro _
    rw [hmem]
    exact hescCarry
  · intro _
    refine ⟨rfl, ?_⟩
    show (carry64 lo hi stm).oddRun = ste.oddRun
    exact hparity.symm
  · show cursorRoom k' (blocks - (S.i + 1)) 9
    have hh := hroomk
    unfold cursorRoom at hh ⊢
    omega
  · show cursorRoom (S.xn + len) (blocks - (S.i + 1)) 9
    have hh := hroomxn
    unfold cursorRoom at hh ⊢
    omega
  · rw [hmem]
    exact hescCap
  · exact hdisj

/-- **A `for.body.us` iteration that leaves.**  With one iteration of budget left
the exit test is one, the arm's increment reached the block count, and the
successor is the cleanup — the loop's exit, which the invariant admits at `0`. -/
theorem us_step_exit (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks 1 s)
    (hpc0 : s.pc = "for.body.us") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks 0 e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .pos8Gate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hcarryI : carryPair s.mem S.xcarry S.stE S.prevb S.prevs := hcarry rfl
  have hflagsI : S.opened = S.prevb ∧ S.ppar = S.prevs := hflags rfl
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨g⟩ := us_calls tab base s2 Γ2 units (S := S) hcap hiw hilt (by omega) hb hwin
    hsc hcarryI hflagsI hdelim hinS hwsS hbsS hctl hsep htabEq htab hkw hkgrow hxngrow
    hroomk hroomxn hcnt hhas hxpExt
  obtain ⟨lo, hi, stm, ste, r1, r2, r3, k', entryExt, len, w1, w2, w3, w4, w5, w6, w7,
    hcall1, hmaskFrame, hld1, hld2, hld3, hld4, hscPost, hcall2, hret2, hentFrame,
    hextLe, hkgrow', hld5, hld6, hld7, hcall3, hescFrame, hescCount, hlenLe, hescCarry,
    hparity, hescCap, hwinR3, htabR3, hscR3⟩ := g
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := us_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw
    S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r1 r2 r3 hpre' hld1 hld2 hld3 hld4 hpos hcall1
    hcall2 hld5 hld6 hld7 hcall3
  have hvexit : vexit S.iw S.shr = 1 := by
    rw [vexit_eq_one]
    rw [hiw, vinc_ofNat (by omega), hshr]
    exact (ofNat64_eq_iff (by omega) (by omega)).mpr (by omega)
  obtain ⟨e, je, hje, hpcE, hrunE⟩ := us_step_at_exit (pipelineCalls tab base s2)
    s.env s S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl S.entw
    S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r2 r3 hpcS
    hagree hcode hvexit
  exact ⟨e, je, hje, hpcE, hrunE⟩

/-- **A `for.body` iteration that leaves.**  The B8 emitter's arm at its exit. -/
theorem body_step_exit (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (s : State)
    (h : pipelineLoopInv base tab blocks 1 s)
    (hpc0 : s.pc = "for.body") :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks 0 e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  obtain ⟨S, hpcS, hpre', hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
    hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry, hflags,
    hroomk, hroomxn, hhas, hdisj⟩ := h
  have harm : S.arm = .b8Gate := by
    revert hpc0
    rw [hpcS]
    cases S.arm <;> simp [PipelineBodyArm.head]
  rw [harm] at hpcS hpre' hagree hcarry hflags
  have hcarryI : carryPair s.mem S.xcarry S.stE S.prevb S.prevs := hcarry rfl
  have hflagsI : S.opened = S.prevb ∧ S.ppar = S.prevs := hflags rfl
  have hsep : StagedSep S blocks := stagedSep hdisj
  have hilt : S.i < blocks := by omega
  obtain ⟨g⟩ := body_calls tab base s2 Γ2 units (S := S) hcap hiw hilt (by omega) hb hwin
    hsc hcarryI hflagsI hdelim hinS hwsS hbsS hctl hsep htab hkw hkgrow hxngrow
    hroomk hroomxn hcnt hhas hxpExt
  obtain ⟨lo, hi, stm, ste, r1, r2, r3, k', entryExt, len, w1, w2, w3, w4, w5, w6, w7,
    hcall1, hmaskFrame, hld1, hld2, hld3, hld4, hscPost, hcall2, hret2, hentFrame,
    hextLe, hkgrow', hld5, hld6, hld7, hcall3, hescFrame, hescCount, hlenLe, hescCarry,
    hparity, hescCap, hwinR3, htabR3, hscR3⟩ := g
  have hpos : (BitVec.signExtend 64 (sh6 S.iw)).toNat < 2 ^ 63 :=
    sh6_signExtend_toNat_lt (i := S.iw) (hblk := hcap) (by
      rw [hiw, ofNat64_toNat (by omega)]
      exact hilt)
  have hcode := body_denote (pipelineCalls tab base s2) s.env s S.n S.b S.sc S.maskSlot
    S.delim S.inString S.ws S.backslash S.ctl S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw
    S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r1 r2 r3 hpre' hld1 hld2 hld3 hld4 hpos hcall1
    hcall2 hld5 hld6 hld7 hcall3
  have hvexit : vexit S.iw S.shr = 1 := by
    rw [vexit_eq_one]
    rw [hiw, vinc_ofNat (by omega), hshr]
    exact (ofNat64_eq_iff (by omega) (by omega)).mpr (by omega)
  obtain ⟨e, je, hje, hpcE, hrunE⟩ := body_step_at_exit (pipelineCalls tab base s2)
    s.env s S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl S.entw
    S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr w1 w2 w3 w4 w5 w6 w7 r2 r3 hpcS
    hagree hcode hvexit
  exact ⟨e, je, hje, hpcE, hrunE⟩

/-! ### The loop instance

The four arms' steps are stated above at one successor apiece; the instance's
`step` is the dispatch on the arm the invariant carries, and `exit` is the spent
budget.  The block bound `hcap` is a **parameter** of the instance rather than a
conjunct of the invariant: it is a fact about the block count the staging supplies
(`pipelineStaging`'s `64 * pipelineBlocks (bs.length) + 63 < 2 ^ 32`), and the
invariant is about the state the loop runs, not about its arguments.  So the loop
is a `PipelineLoop` for every block count the staging admits, and the bound is
discharged where the loop is used. -/

/-- **One loop iteration, at whichever arm the state is in.**  The arm's head is
the state's program counter, so the dispatch reads the arm off the invariant and
hands the state to that arm's step; the budget is `r` iterations left, so a spent
budget is the exit step and a live one the head step. -/
theorem pipelineLoop_step (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) (r : Nat) (s : State)
    (h : pipelineLoopInv base tab blocks (r + 1) s) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ pipelineLoopInv base tab blocks r e ∧
      ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody s =
        runFuel (pipelineCalls tab base s2) k pipelineBody e := by
  cases r with
  | zero =>
      have hh : pipelineLoopInv base tab blocks 1 s := h
      obtain ⟨S, hpc, hpre, hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
        hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry,
        hflags, hroomk, hroomxn, hhas, hdisj⟩ := h
      have hcases : S.arm = .pos8NoGate ∨ S.arm = .pos8Gate ∨
          S.arm = .b8NoGate ∨ S.arm = .b8Gate := by
        cases S.arm <;> simp
      rcases hcases with h | h | h | h
      · rw [h] at hpc
        exact usUs_step_exit tab base s2 Γ2 units blocks hcap s hh hpc
      · rw [h] at hpc
        exact us_step_exit tab base s2 Γ2 units blocks hcap s hh hpc
      · rw [h] at hpc
        exact us83_step_exit tab base s2 Γ2 units blocks hcap s hh hpc
      · rw [h] at hpc
        exact body_step_exit tab base s2 Γ2 units blocks hcap s hh hpc
  | succ r' =>
      have hh : pipelineLoopInv base tab blocks (r' + 1 + 1) s := h
      obtain ⟨S, hpc, hpre, hiblk, hshr, hiw, hagree, hb, hwin, hsc, hodd, hdelim, hinS,
        hwsS, hbsS, hctl, htabEq, htab, hkw, hcnt, hxpExt, hkgrow, hxngrow, hcarry,
        hflags, hroomk, hroomxn, hhas, hdisj⟩ := h
      have hcases : S.arm = .pos8NoGate ∨ S.arm = .pos8Gate ∨
          S.arm = .b8NoGate ∨ S.arm = .b8Gate := by
        cases S.arm <;> simp
      rcases hcases with h | h | h | h
      · rw [h] at hpc
        exact usUs_step_head tab base s2 Γ2 units blocks (r' + 1) hcap s hh (by omega) hpc
      · rw [h] at hpc
        exact us_step_head tab base s2 Γ2 units blocks (r' + 1) hcap s hh (by omega) hpc
      · rw [h] at hpc
        exact us83_step_head tab base s2 Γ2 units blocks (r' + 1) hcap s hh (by omega) hpc
      · rw [h] at hpc
        exact body_step_head tab base s2 Γ2 units blocks (r' + 1) hcap s hh (by omega) hpc

/-- **The pipeline's block loop, as `PipelineLoop` asks for it.**  The bound is the
document's block count, one control step per iteration, the invariant
`pipelineLoopInv` and the exit `pipelineLoopExit`.

`pipeline_satisfies` keeps its `hbody` hypothesis at this instance: `PipelineBodyFacts.exit`
is stated at the arbitrary stage-2 slot and `Γ_stage2` does not exist in this tree,
so the loop's own induction — which is all this structure states — is not the
pipeline's refinement.  The loop closes; the pipeline does not, and the gap is the
stage-2 record. -/
def pipelineLoop (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) (blocks : Nat)
    (hcap : 64 * blocks + 63 < 2 ^ 32) :
    PipelineLoop (pipelineCalls tab base s2) pipelineBody where
  N := blocks
  cost := 1
  Inv := pipelineLoopInv base tab blocks
  Exit := pipelineLoopExit
  step := fun r s h => pipelineLoop_step tab base s2 Γ2 units blocks hcap r s h
  exit := fun s h => by
    obtain ⟨e, j, hj, hex, hrun⟩ :=
      pipelineLoop_exitObligation (pipelineCalls tab base s2) base tab blocks s h
    exact ⟨e, j, by omega, hex, hrun⟩

/-! ### Axiom footprints of the loop step

The step is one control step per arm: the units' records at the pipeline's own call
sites, the traces, and the frames.  Every declaration below is at `[propext,
Quot.sound]` or below; the `Classical.choice` the call sites carry is the
bitvector shift arithmetic `sh6_ofNat_toNat` names.
-/

/-- info: 'LeanLLVM.Vellum.stagedSep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stagedSep

/-- info: 'LeanLLVM.Vellum.sep_comm' does not depend on any axioms -/
#guard_msgs in
#print axioms sep_comm

/-- info: 'LeanLLVM.Vellum.disjoint_of_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disjoint_of_sub

/-- info: 'LeanLLVM.Vellum.readBytes_mask_store_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_mask_store_entry

/-- info: 'LeanLLVM.Vellum.readBytes_mask_store_entry_of_disj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_mask_store_entry_of_disj

/-- info: 'LeanLLVM.Vellum.hasBytes_mask_store_entry_of_disj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_mask_store_entry_of_disj

/-- info: 'LeanLLVM.Vellum.readBytes_entry_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_entry_frame

/-- info: 'LeanLLVM.Vellum.readBytes_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readBytes_len

/-- info: 'LeanLLVM.Vellum.natToBytes8_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms natToBytes8_inj

/-- info: 'LeanLLVM.Vellum.flagBytes_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms flagBytes_inj

/-- info: 'LeanLLVM.Vellum.carrySlot_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carrySlot_flags

/-- info: 'LeanLLVM.Vellum.parity_of_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parity_of_slot

/-- info: 'LeanLLVM.Vellum.usUsSucc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms usUsSucc

/-- info: 'LeanLLVM.Vellum.usUs_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usUs_calls

/-- info: 'LeanLLVM.Vellum.usUsSucc_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_window

/-- info: 'LeanLLVM.Vellum.usUsSucc_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_table

/-- info: 'LeanLLVM.Vellum.usUsSucc_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_count

/-- info: 'LeanLLVM.Vellum.usUsSucc_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_capacity

/-- info: 'LeanLLVM.Vellum.usUsSucc_carrySlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_carrySlot

/-- info: 'LeanLLVM.Vellum.usUsSucc_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSucc_agree

/-- info: 'LeanLLVM.Vellum.usUs_step_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usUs_step_head

/-- info: 'LeanLLVM.Vellum.usUs_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms usUs_step_exit

/-- info: 'LeanLLVM.Vellum.b8Call_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms b8Call_at

/-- info: 'LeanLLVM.Vellum.us83Succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms us83Succ

/-- info: 'LeanLLVM.Vellum.us83_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us83_calls

/-- info: 'LeanLLVM.Vellum.us83Succ_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us83Succ_agree

/-- info: 'LeanLLVM.Vellum.us83_step_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us83_step_head

/-- info: 'LeanLLVM.Vellum.us83_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us83_step_exit

/-- info: 'LeanLLVM.Vellum.block64_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block64_inj

/-- info: 'LeanLLVM.Vellum.pair_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pair_flags

/-- info: 'LeanLLVM.Vellum.natToBytes_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natToBytes_mod

/-- info: 'LeanLLVM.Vellum.wordBytes8_eq_of_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wordBytes8_eq_of_mod

/-- info: 'LeanLLVM.Vellum.readBytes_unchangedOutside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_unchangedOutside

/-- info: 'LeanLLVM.Vellum.hasBytes_of_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_of_forall

/-- info: 'LeanLLVM.Vellum.escape_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_capacity

/-- info: 'LeanLLVM.Vellum.stagedRegions' does not depend on any axioms -/
#guard_msgs in
#print axioms stagedRegions

/-- info: 'LeanLLVM.Vellum.StagedSep' does not depend on any axioms -/
#guard_msgs in
#print axioms StagedSep

/-! ### Axiom footprints of the gate-on arms and the loop instance

The list's frames are `UnchangedOutside` and `readBytes` equalities, the call site
is one record's conjunction and one exclusion, and the successors are definitions.
The `Classical.choice` in the call bundles and the steps is `maskCall_at`'s and
`pos8Call_at`'s — the bitvector shift arithmetic `sh6_ofNat_toNat` names, not a
witness chosen in any statement here.
-/

/-- info: 'LeanLLVM.Vellum.carry64_oddRun_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carry64_oddRun_congr

/-- info: 'LeanLLVM.Vellum.escapeOutside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeOutside

/-- info: 'LeanLLVM.Vellum.escapeReadBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeReadBytes

/-- info: 'LeanLLVM.Vellum.escapeHasBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeHasBytes

/-- info: 'LeanLLVM.Vellum.gateSucc_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gateSucc_window

/-- info: 'LeanLLVM.Vellum.gateSucc_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gateSucc_table

/-- info: 'LeanLLVM.Vellum.gateSucc_scSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gateSucc_scSlot

/-- info: 'LeanLLVM.Vellum.gateBlock_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gateBlock_at

/-- info: 'LeanLLVM.Vellum.escapeCall_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeCall_at

/-- info: 'LeanLLVM.Vellum.GateCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GateCalls

/-- info: 'LeanLLVM.Vellum.gateCalls_after_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gateCalls_after_entry

/-- info: 'LeanLLVM.Vellum.us_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us_calls

/-- info: 'LeanLLVM.Vellum.body_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_calls

/-- info: 'LeanLLVM.Vellum.usSucc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms usSucc

/-- info: 'LeanLLVM.Vellum.bodySucc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bodySucc

/-- info: 'LeanLLVM.Vellum.us_cells_agree'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us_cells_agree'

/-- info: 'LeanLLVM.Vellum.usSucc_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usSucc_agree

/-- info: 'LeanLLVM.Vellum.body_cells_agree'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_cells_agree'

/-- info: 'LeanLLVM.Vellum.bodySucc_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bodySucc_agree

/-- info: 'LeanLLVM.Vellum.us_step_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us_step_head

/-- info: 'LeanLLVM.Vellum.us_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms us_step_exit

/-- info: 'LeanLLVM.Vellum.body_step_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_step_head

/-- info: 'LeanLLVM.Vellum.body_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_step_exit

/-- info: 'LeanLLVM.Vellum.pipelineLoop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_step

/-- info: 'LeanLLVM.Vellum.pipelineLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop


end LeanLLVM.Vellum
