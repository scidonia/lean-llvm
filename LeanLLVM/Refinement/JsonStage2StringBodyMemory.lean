import LeanLLVM.Refinement.JsonStage2StringBodyFootprints

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### Writing a region twice

The closing must match the body's memory to the model's, and the scan's own
invariant must update the cursor word once per iteration.  Both need the same
fact, and it is not the one the list encoding makes obvious: `writeByte` replaces
a cell in place when the address is present and **appends** it otherwise, so two
writes over separated regions are *not* interchangeable as lists — the write order
survives in the appended cells (`writeBytes_absent_comm_witness` is the witness).
What does hold is the weaker, sufficient form proved here: writing a region twice
is the second write, when the second write is at least as long.  The first write's
cells inside the region are then all replaced in place, and the cells the two
writes append are the same cells in the same order — so the appended tail, which
is what the order would have distinguished, is identical.

This ordering rule is the one the scan needs at `(xj, 8)` every iteration and the
one the closing needs wherever the body rewrites a region the model writes once. -/

/-- Writing one address twice is the second write: the first leaves a cell there,
in place or appended, and the second replaces that cell. -/
theorem writeByte_writeByte_same (m : Mem) (a : Nat) (b₁ b : UInt8) :
    writeByte (writeByte m a b₁) a b = writeByte m a b := by
  induction m with
  | nil => simp [writeByte]
  | cons cell rest ih =>
      obtain ⟨a', b'⟩ := cell
      by_cases h : a' = a
      · subst h; simp [writeByte]
      · simp only [writeByte, ite_eq_right h]
        rw [ih]

/-- Writes at two different addresses commute as lists when the second address is
occupied: an absent cell is appended, so its *position* is what makes the two
orders differ, and an occupied one is replaced where it stands. -/
theorem writeByte_swap_of_readByte (m : Mem) (a : Nat) (b : UInt8) :
    ∀ (a' : Nat) (b' : UInt8), a ≠ a' → readByte m a ≠ none →
      writeByte (writeByte m a b) a' b' = writeByte (writeByte m a' b') a b := by
  induction m with
  | nil => intro a' b' _ hp; exact absurd rfl hp
  | cons cell rest ih =>
      obtain ⟨x, c⟩ := cell
      intro a' b' hne hp
      by_cases h1 : x = a
      · have hxa' : x ≠ a' := by rw [h1]; exact hne
        simp only [writeByte, ite_eq_left h1, ite_eq_right hxa']
      · by_cases h2 : x = a'
        · simp only [writeByte, ite_eq_right h1, ite_eq_left h2]
        · have hp' : readByte rest a ≠ none := by
            intro hc
            apply hp
            simp only [readByte, ite_eq_right h1, hc]
          simp only [writeByte, ite_eq_right h1, ite_eq_right h2]
          rw [ih a' b' hne hp']

/-- Reads above a single written cell are unchanged, so a sequence's presence
survives a write below it. -/
theorem readBytes_writeByte_below (m : Mem) {x : Nat} {v : UInt8} :
    ∀ (n a : Nat), x < a → readBytes (writeByte m x v) a n = readBytes m a n
  | 0, _, _ => by simp only [readBytes]
  | n + 1, a, h => by
      have hb : readByte (writeByte m x v) a = readByte m a :=
        readByte_writeByte_other m v (by omega)
      simp only [readBytes, hb]
      cases hr : readByte m a with
      | none => rfl
      | some b =>
          rw [readBytes_writeByte_below m n (a + 1) (by omega)]

/-- Reads at or above a written range are unchanged (`Memory` states the below
case; this is its dual, in the form a four-byte lane read needs). -/
theorem s2StringBodyReadBytes_above (m : Mem) :
    ∀ (bs : List UInt8) (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | _, 0, _, _, _ => by simp only [readBytes]
  | bs, n + 1, addr, start, h => by
      have hb : readByte (writeBytes m start bs) addr = readByte m addr :=
        readByte_writeBytes_above m bs h
      simp only [readBytes, hb]
      cases hr : readByte m addr with
      | none => simp only [hr]
      | some b =>
          simp only [hr]
          rw [s2StringBodyReadBytes_above m bs n (addr + 1) start (by omega)]

/-- Reads entirely below a single written cell are unchanged — the dual of
`readBytes_writeByte_below`, and the other half of what a presence fact needs: a
write on either side of a region leaves it alone. -/
theorem readBytes_writeByte_above (m : Mem) {x : Nat} {v : UInt8} :
    ∀ (n a : Nat), a + n ≤ x → readBytes (writeByte m x v) a n = readBytes m a n
  | 0, _, _ => by simp only [readBytes]
  | n + 1, a, h => by
      have hb : readByte (writeByte m x v) a = readByte m a :=
        readByte_writeByte_other m v (by omega)
      simp only [readBytes, hb]
      cases hr : readByte m a with
      | none => rfl
      | some b => rw [readBytes_writeByte_above m n (a + 1) (by omega)]

/-- **The position list survives a write away from every lane**: a write whose region
misses each lane's four bytes leaves `readLanes32` as it was.  This is the frame the
callee's own read of the list needs at a memory the scan has written the cursor
word into. -/
theorem readLanes32_writeBytes_away {m : Mem} {start : Nat} {ws : List UInt8}
    {addr k : Nat}
    (h : ∀ j, j < k → addr + 4 * j + 4 ≤ start ∨ start + ws.length ≤ addr + 4 * j) :
    readLanes32 (writeBytes m start ws) addr k = readLanes32 m addr k := by
  induction k generalizing addr with
  | zero => rfl
  | succ k ih =>
      have h4 : readBytes (writeBytes m start ws) addr 4 = readBytes m addr 4 := by
        rcases h 0 (Nat.succ_pos k) with hb | ha
        · exact readBytes_writeBytes_below m ws 4 addr start hb
        · exact s2StringBodyReadBytes_above m ws 4 addr start (by simpa using ha)
      have hrec : readLanes32 (writeBytes m start ws) (addr + 4) k
          = readLanes32 m (addr + 4) k :=
        ih (addr := addr + 4) (fun j hj => by
          have := h (j + 1) (by omega)
          simpa [show addr + 4 + 4 * j = addr + 4 * (j + 1) by omega] using this)
      simp only [readLanes32, h4, hrec]

/-- **The swap with the presence on the other address.**  The equality is symmetric
in its two writes, so this is `writeByte_swap_of_readByte` with the addresses
exchanged — the variant the commutation's upper case needs, where the region, not
the odd byte, is the address the memory is known to hold. -/
theorem writeByte_swap_of_present_second (m : Mem) (a : Nat) (b : UInt8)
    (a' : Nat) (b' : UInt8) (h : a ≠ a') (hp : readByte m a' ≠ none) :
    writeByte (writeByte m a b) a' b' = writeByte (writeByte m a' b') a b :=
  (writeByte_swap_of_readByte m a' b' a b (Ne.symm h) hp).symm


/-- **A single byte at `b` commutes with a sequence at `a`**, given that the memory
holds a sequence of the same length at `a` and that the two ranges are disjoint.
The induction peels the presence one cell at a time (each peel is the `readBytes`
recursion), which is why presence is stated existentially — the *written* bytes and
the *present* bytes are different lists of the same length. -/
theorem writeByte_writeBytes_comm (m : Mem) (b : Nat) (y : UInt8) :
    ∀ (a : Nat) (X : List UInt8), (∃ X₀, readBytes m a X.length = some X₀) →
      (b < a ∨ a + X.length ≤ b) →
      writeByte (writeBytes m a X) b y = writeBytes (writeByte m b y) a X
  | _, [], _, _ => rfl
  | a, c :: cs, hpres, hdisj => by
      obtain ⟨X₀, hX₀⟩ := hpres
      simp only [List.length_cons] at hX₀ hdisj
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, readByte m a = some c₀ := by
        cases h : readByte m a with
        | none =>
            rw [show readBytes m a (cs.length + 1) = none from by
              simp only [readBytes, h]] at hX₀
            cases hX₀
        | some c₀ => exact ⟨c₀, rfl⟩
      obtain ⟨cs₀, hcs₀⟩ : ∃ cs₀, readBytes m (a + 1) cs.length = some cs₀ := by
        rw [show readBytes m a (cs.length + 1) = (match readByte m a with
          | none => none
          | some c₀ => match readBytes m (a + 1) cs.length with
            | none => none
            | some bs => some (c₀ :: bs))
          from rfl, hc₀] at hX₀
        cases h : readBytes m (a + 1) cs.length with
        | none => rw [h] at hX₀; cases hX₀
        | some cs₀ => exact ⟨cs₀, rfl⟩
      have htail : ∃ cs₀, readBytes (writeByte m a c) (a + 1) cs.length = some cs₀ :=
        ⟨cs₀, by
          rw [readBytes_writeByte_below m cs.length (a + 1) (by omega)]
          exact hcs₀⟩
      have hdisj' : b < a + 1 ∨ (a + 1) + cs.length ≤ b := by
        rcases hdisj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hne : a ≠ b := by
        intro heq
        rw [heq] at hdisj
        rcases hdisj with h | h <;> omega
      show writeByte (writeBytes (writeByte m a c) (a + 1) cs) b y
        = writeBytes (writeByte m b y) a (c :: cs)
      rw [writeByte_writeBytes_comm (writeByte m a c) b y (a + 1) cs htail hdisj']
      rw [show writeBytes (writeByte m b y) a (c :: cs)
        = writeBytes (writeByte (writeByte m b y) a c) (a + 1) cs from rfl]
      rw [writeByte_swap_of_readByte m a c b y hne (by rw [hc₀]; exact Option.some_ne_none c₀)]

/-- A cell outside a written range keeps its place: the write sequence conses
nothing at that address and appends nothing before it. -/
theorem writeBytes_cons_outside (a' : Nat) (b' : UInt8) :
    ∀ (a : Nat) (bs : List UInt8), a' < a ∨ a + bs.length ≤ a' →
      ∀ rest : Mem,
        writeBytes ((a', b') :: rest) a bs = (a', b') :: writeBytes rest a bs
  | _, [], _, _ => rfl
  | a, b :: bs, h, rest => by
      have hne : a' ≠ a := by
        intro heq
        subst heq
        rcases h with h | h
        · exact absurd h (Nat.lt_irrefl a')
        · simp only [List.length_cons] at h; omega
      show writeBytes (writeByte ((a', b') :: rest) a b) (a + 1) bs
        = (a', b') :: writeBytes rest a (b :: bs)
      rw [show writeByte ((a', b') :: rest) a b = (a', b') :: writeByte rest a b from by
        simp only [writeByte, ite_eq_right hne]]
      exact writeBytes_cons_outside a' b' (a + 1) bs (by
        rcases h with h | h
        · exact Or.inl (by omega)
        · simp only [List.length_cons] at h; omega) (writeByte rest a b)

/-- A single write below a sequence's range commutes with the whole sequence, when
the address it writes is occupied. -/
theorem writeByte_writeBytes_above (m : Mem) (a : Nat) (b : UInt8) :
    ∀ (a' : Nat) (bs : List UInt8), a < a' → readByte m a ≠ none →
      writeByte (writeBytes m a' bs) a b = writeBytes (writeByte m a b) a' bs
  | _, [], _, _ => rfl
  | a', b' :: bs, hlt, hp => by
      show writeByte (writeBytes (writeByte m a' b') (a' + 1) bs) a b
        = writeBytes (writeByte (writeByte m a b) a' b') (a' + 1) bs
      have hpres : readByte (writeByte m a' b') a ≠ none := by
        rw [readByte_writeByte_other m b' (by omega)]; exact hp
      rw [writeByte_writeBytes_above (writeByte m a' b') a b (a' + 1) bs (by omega) hpres]
      rw [writeByte_swap_of_readByte m a b a' b' (by omega) hp]

/-- A write at the head of a sequence is the sequence with its head replaced: the
rest of the sequence pushes the cell out of the way, so the write lands on the
head's own cell wherever the sequence appended it. -/
theorem writeByte_writeBytes_head (m : Mem) (a : Nat) :
    ∀ (b₁ : UInt8) (bs : List UInt8) (b : UInt8),
      writeByte (writeBytes m a (b₁ :: bs)) a b
        = writeBytes (writeByte m a b) (a + 1) bs
  | b₁, bs, b => by
      show writeByte (writeBytes (writeByte m a b₁) (a + 1) bs) a b = _
      rw [writeByte_writeBytes_above (writeByte m a b₁) a b (a + 1) bs (by omega)
        (by rw [readByte_writeByte_same]; exact Option.some_ne_none b₁)]
      rw [writeByte_writeByte_same]

/-- A successful read of `n` bytes has `n` of them. -/
theorem readBytes_length_some {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : readBytes m addr n = some bs) : bs.length = n := by
  induction n generalizing addr bs with
  | zero => simp only [readBytes, Option.some.injEq] at h; subst h; rfl
  | succ n ih =>
      simp only [readBytes] at h
      cases hb : readByte m addr with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (addr + 1) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons, ih hr]

/-- A byte read back at an address is the byte that is there, so writing it back
changes nothing: the cell is replaced where it stands. -/
theorem writeByte_readByte_self (m : Mem) (a : Nat) (b : UInt8)
    (h : readByte m a = some b) : writeByte m a b = m := by
  induction m with
  | nil => simp only [readByte] at h; cases h
  | cons cell rest ih =>
      obtain ⟨a', b'⟩ := cell
      by_cases ha : a' = a
      · subst ha
        simp only [readByte] at h
        rw [ite_eq_left trivial] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [writeByte]
        rw [ite_eq_left trivial]
      · simp only [readByte, ite_eq_right ha] at h
        simp only [writeByte, ite_eq_right ha]
        rw [ih h]

/-- **A region the memory already holds is written back with no effect.**  This is
the presence fact the scan's invariant and the closing's memory term both need:
the bytes a `readBytes` returned are exactly the bytes a `writeBytes` of them
leaves, because every cell is replaced in place. -/
theorem writeBytes_of_readBytes_self (m : Mem) :
    ∀ (n a : Nat) {bs : List UInt8}, readBytes m a n = some bs →
      bs.length = n → writeBytes m a bs = m
  | 0, _, _, h, _ => by
      simp only [readBytes, Option.some.injEq] at h
      subst h
      rfl
  | n + 1, a, bs, h, hlen => by
      simp only [readBytes] at h
      cases hb : readByte m a with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (a + 1) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons] at hlen
              show writeBytes (writeByte m a b) (a + 1) tl = m
              rw [writeByte_readByte_self m a b hb]
              exact writeBytes_of_readBytes_self m n (a + 1) hr (by omega)

/-- **The cursor word's presence, at the model's own vocabulary.**  A word the
staging reads at `xj` is already the memory's there, so the scan's first write of
it is a no-op — which is the seating's first clause, and the same fact the closing
needs for every region the body rewrites. -/
theorem stage2ReadWord_writeBytes_self (mem : Mem) (xj w j : Nat)
    (h : stage2ReadWord mem xj w = some j) :
    writeBytes mem xj (wordBytes w j) = mem := by
  unfold stage2ReadWord at h
  cases hr : readBytes mem xj w with
  | none => rw [hr] at h; cases h
  | some bs =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hlen : bs.length = w := readBytes_length_some hr
      have hbs0 : List.take bs.length (natToBytes (bytesToNat bs) w) = bs :=
        natToBytes_bytesToNat bs w (by omega)
      have htake : List.take bs.length (natToBytes (bytesToNat bs) w)
          = natToBytes (bytesToNat bs) w :=
        List.take_of_length_le (by rw [natToBytes_length]; omega)
      have hbs : natToBytes (bytesToNat bs) w = bs := by rw [← htake]; exact hbs0
      simp only [wordBytes]
      rw [hbs]
      exact writeBytes_of_readBytes_self mem w xj hr hlen


/-- **Writing a region twice is the second write**, when the second write is at
least as long: the first write's cells inside the region are replaced in place,
and the two writes append the same cells in the same order.  This is the form the
scan's invariant and the closing's memory term both consume. -/
theorem writeBytes_writeBytes_same (m : Mem) (a : Nat) :
    ∀ (bs₁ bs₂ : List UInt8), bs₁.length ≤ bs₂.length →
      writeBytes (writeBytes m a bs₁) a bs₂ = writeBytes m a bs₂
  | [], _, _ => rfl
  | _ :: _, [], h => by
      simp only [List.length_cons, List.length_nil] at h; omega
  | b₁ :: bs₁, b :: bs, h => by
      show writeBytes (writeByte (writeBytes m a (b₁ :: bs₁)) a b) (a + 1) bs
        = writeBytes (writeByte m a b) (a + 1) bs
      rw [writeByte_writeBytes_head m a b₁ bs₁ b]
      exact writeBytes_writeBytes_same (writeByte m a b) (a + 1) bs₁ bs
        (by simp only [List.length_cons] at h; omega)

/-- **Two writes over disjoint present regions commute.**  Both regions are present,
so both writes are replacements in place and the append order — the one thing that
distinguishes the two sides as lists — never enters.  This is
`writeBytes_absent_comm_witness`'s statement with the hypothesis the absent case
cannot meet. -/
theorem writeBytes_comm_of_present (A : Mem) :
    ∀ (a : Nat) (X : List UInt8) (b : Nat) (Y : List UInt8),
      (∃ X₀, readBytes A a X.length = some X₀) →
      (∃ Y₀, readBytes A b Y.length = some Y₀) →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X
  | a, X, b, [], _, _, _ => rfl
  | a, X, b, y :: Ys, hX, hY, hdisj => by
      obtain ⟨Y₀, hY₀⟩ := hY
      simp only [List.length_cons] at hY₀ hdisj
      obtain ⟨y₀, hy₀⟩ : ∃ y₀, readByte A b = some y₀ := by
        cases h : readByte A b with
        | none =>
            rw [show readBytes A b (Ys.length + 1) = none from by
              simp only [readBytes, h]] at hY₀
            cases hY₀
        | some y₀ => exact ⟨y₀, rfl⟩
      obtain ⟨Ys₀, hYs₀⟩ : ∃ Ys₀, readBytes A (b + 1) Ys.length = some Ys₀ := by
        rw [show readBytes A b (Ys.length + 1) = (match readByte A b with
          | none => none
          | some y₀ => match readBytes A (b + 1) Ys.length with
            | none => none
            | some bs => some (y₀ :: bs))
          from rfl, hy₀] at hY₀
        cases h : readBytes A (b + 1) Ys.length with
        | none => rw [h] at hY₀; cases hY₀
        | some Ys₀ => exact ⟨Ys₀, rfl⟩
      -- the single byte at `b` lifts past the whole of `X`
      have hlift : writeByte (writeBytes A a X) b y = writeBytes (writeByte A b y) a X := by
        refine writeByte_writeBytes_comm (m := A) (b := b) (y := y) a X hX ?_
        rcases hdisj with h | h
        · exact Or.inr h
        · exact Or.inl (by omega)
      -- the region's presence in the memory the byte write leaves: the write is on
      -- one side of it or the other
      have hX' : ∃ X₀, readBytes (writeByte A b y) a X.length = some X₀ := by
        obtain ⟨X₀, hX₀⟩ := hX
        refine ⟨X₀, ?_⟩
        rcases hdisj with h | h
        · rw [readBytes_writeByte_above A X.length a (by omega)]
          exact hX₀
        · rw [readBytes_writeByte_below A X.length a (by omega)]
          exact hX₀
      have hY' : ∃ Y₀, readBytes (writeByte A b y) (b + 1) Ys.length = some Y₀ :=
        ⟨Ys₀, by
          rw [readBytes_writeByte_below A Ys.length (b + 1) (by omega)]
          exact hYs₀⟩
      have hdisj' : a + X.length ≤ b + 1 ∨ (b + 1) + Ys.length ≤ a := by
        rcases hdisj with h | h
        · exact Or.inl (Nat.le_trans h (Nat.le_succ b))
        · refine Or.inr ?_
          have heq : b + (Ys.length + 1) = (b + 1) + Ys.length := by omega
          rwa [heq] at h
      show writeBytes (writeByte (writeBytes A a X) b y) (b + 1) Ys
        = writeBytes (writeBytes A b (y :: Ys)) a X
      rw [hlift]
      rw [show writeBytes (writeBytes A b (y :: Ys)) a X
        = writeBytes (writeBytes (writeByte A b y) (b + 1) Ys) a X from rfl]
      exact writeBytes_comm_of_present (writeByte A b y) a X (b + 1) Ys hX' hY' hdisj'

/-- **A commutation needs one presence, not two.**  `writeBytes_comm_of_present`'s
statement spends the presence of both regions; the first region's alone suffices.  A
region the memory holds is replaced in place, so that write leaves the address
sequence alone, and the second write — present or not — now meets the same addresses
on both sides and appends the same cells in the same order.  Two *absent* regions are
exactly the case that fails (`writeBytes_absent_comm_witness`), so one present region
is what rules it out.  The induction is the two-sided lemma's, peeling the second
region one byte at a time; the peeled byte is no longer required to be there, because
`writeByte_writeBytes_comm` carries the whole of the first region past it and
`readBytes_writeByte_above`/`readBytes_writeByte_below` keep that region present in
the memory the byte write leaves. -/
theorem writeBytes_comm_of_present_left (A : Mem) :
    ∀ (a : Nat) (X : List UInt8) (b : Nat) (Y : List UInt8),
      (∃ X₀, readBytes A a X.length = some X₀) →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X
  | a, X, b, [], _, _ => rfl
  | a, X, b, y :: Ys, hX, hdisj => by
      simp only [List.length_cons] at hdisj
      have hX' : ∃ X₀, readBytes (writeByte A b y) a X.length = some X₀ := by
        obtain ⟨X₀, hX₀⟩ := hX
        refine ⟨X₀, ?_⟩
        rcases hdisj with h | h
        · rw [readBytes_writeByte_above A X.length a h]; exact hX₀
        · rw [readBytes_writeByte_below A X.length a (by omega)]; exact hX₀
      have hb_a : b < a ∨ a + X.length ≤ b := by
        rcases hdisj with h | h
        · exact Or.inr h
        · exact Or.inl (by omega)
      show writeBytes (writeByte (writeBytes A a X) b y) (b + 1) Ys
        = writeBytes (writeBytes (writeByte A b y) (b + 1) Ys) a X
      rw [writeByte_writeBytes_comm A b y a X hX hb_a]
      exact writeBytes_comm_of_present_left (writeByte A b y) a X (b + 1) Ys hX'
        (by rcases hdisj with h | h
            · exact Or.inl (Nat.le_trans h (Nat.le_succ b))
            · exact Or.inr (by omega))

/-- **One presence, the other side**: the lemma above at the exchanged writes, since
the claim is symmetric in them.  This is the form whose spent witness is the second
region's — the one a crossing uses when the write it moves is the write whose own
region nothing states. -/
theorem writeBytes_comm_of_present_right (A : Mem) :
    ∀ (a : Nat) (X : List UInt8) (b : Nat) (Y : List UInt8),
      (∃ Y₀, readBytes A b Y.length = some Y₀) →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X
  | a, X, b, Y, hY, hdisj => by
      refine (writeBytes_comm_of_present_left A b Y a X hY ?_).symm
      rcases hdisj with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- Presence as an existential, from the `≠ none` form the section states. -/
theorem exists_readBytes_of_ne {A : Mem} {a n : Nat} (h : readBytes A a n ≠ none) :
    ∃ bs, readBytes A a n = some bs := by
  cases hb : readBytes A a n with
  | none => exact absurd hb h
  | some bs => exact ⟨bs, rfl⟩

/-- **The absorption**: an earlier write to a region, crossed by two writes disjoint
from it, is erased by a later write to that same region.  Two presences, and they are
the regions the crossings move into — not the erased region's, which no crossing
reads: a write that moves needs only the region it meets to be a replacement in
place, and the erased write is overwritten by the last one before any reader could
observe whether it appended.  The crossing itself is two commutations and then
`writeBytes_writeBytes_same`, because the two writes to the erased region end up
adjacent. -/
theorem writeBytes_absorb_one (B : Mem) {ei dst xj : Nat} {X out Wj Z : List UInt8}
    (hdst : readBytes B dst out.length ≠ none)
    (hxj : readBytes B xj Wj.length ≠ none)
    (hlen : X.length ≤ Z.length)
    (hd_ei : ei + X.length ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + X.length ≤ xj ∨ xj + Wj.length ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + Wj.length ≤ dst) :
    writeBytes (writeBytes (writeBytes (writeBytes B ei X) dst out) xj Wj) ei Z
      = writeBytes (writeBytes (writeBytes B dst out) xj Wj) ei Z := by
  obtain ⟨O₀, hO₀⟩ := exists_readBytes_of_ne hdst
  -- 1. the clear crosses `dst`, spending the presence of the region it moves into
  rw [writeBytes_comm_of_present_right B ei X dst out ⟨O₀, hO₀⟩ hd_ei]
  -- 2. and then `xj`: the `xj` region is still present after `dst`'s write
  have hxj' : readBytes (writeBytes B dst out) xj Wj.length ≠ none := by
    rcases hd_xj with h | h
    · rw [s2StringBodyReadBytes_above B out Wj.length xj dst h]
      exact hxj
    · rw [readBytes_writeBytes_below B out Wj.length xj dst h]
      exact hxj
  obtain ⟨W₁, hW₁⟩ := exists_readBytes_of_ne hxj'
  rw [writeBytes_comm_of_present_right (writeBytes B dst out) ei X xj Wj ⟨W₁, hW₁⟩ hx_ei]
  -- 3. the two writes to `ei` are adjacent, and the second one is the memory
  exact writeBytes_writeBytes_same (writeBytes (writeBytes B dst out) xj Wj) ei X Z hlen

/-- **One intermediate write is enough for the absorption.**  The pair is commuted so
that the write at `a` lands beside the later `Z`, which erases it by
`writeBytes_writeBytes_same`.  **The presence this form spends is the region at `a`
— the write `Z` erases — and not the region at `b` it is commuted past**, which is
the opposite spending from `writeBytes_absorb_one` (there the erased write's region
is the absent one and the two it crosses are present).  The refused chain needs this
form because the write it erases at `a` is `xj`'s — the staged escape list, whose
presence the staging states — and the region it crosses at `b` is the caller's own
stack slot, whose presence the staging does not state. -/
theorem writeBytes_absorb_single (A : Mem) {a : Nat} {X : List UInt8} {b : Nat}
    {Y Z : List UInt8}
    (ha : readBytes A a X.length ≠ none)
    (hlen : X.length ≤ Z.length) (hd : a + X.length ≤ b ∨ b + Y.length ≤ a) :
    writeBytes (writeBytes (writeBytes A a X) b Y) a Z =
      writeBytes (writeBytes A b Y) a Z := by
  rw [writeBytes_comm_of_present_left A a X b Y (exists_readBytes_of_ne ha) hd]
  exact writeBytes_writeBytes_same (writeBytes A b Y) a X Z hlen

/-- **A word read is the byte read the body's blocks make**: a successful
`stage2ReadWord` returns the `readBytes` of the model's `wordBytes`.  The staging's
clauses are stated as word reads (that is the model's vocabulary) and each block's
run is stated as byte reads (that is the body's), so the two are bridged here once
rather than at every use. -/
theorem readBytes_of_stage2ReadWord {mem : Mem} {a w v : Nat}
    (h : stage2ReadWord mem a w = some v) :
    readBytes mem a w = some (wordBytes w v) := by
  unfold stage2ReadWord at h
  cases hr : readBytes mem a w with
  | none => rw [hr] at h; cases h
  | some bs =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hlen : bs.length = w := readBytes_length_some hr
      have hbs : natToBytes (bytesToNat bs) w = bs := by
        have htake : List.take bs.length (natToBytes (bytesToNat bs) w)
            = natToBytes (bytesToNat bs) w :=
          List.take_of_length_le (by rw [natToBytes_length]; omega)
        rw [← htake]
        exact natToBytes_bytesToNat bs w (by omega)
      simpa only [wordBytes, hbs] using hr

/-- A word's bytes read back as the word, in range. -/
theorem bytesToNat_natToBytes {v w : Nat} (h : v < 256 ^ w) :
    bytesToNat (natToBytes v w) = v := by
  rw [natToBytes_toNat, Nat.mod_eq_of_lt h]

/-- **The byte read as a word read**: the dual of `readBytes_of_stage2ReadWord`, at a
value the staging's bound keeps in range.  The callee's own read is stated as a word
read (its model's vocabulary) and the exit's memory carries the cursor as bytes. -/
theorem stage2ReadWord_of_readBytes {mem : Mem} {a w v : Nat} (hv : v < 256 ^ w)
    (h : readBytes mem a w = some (wordBytes w v)) : stage2ReadWord mem a w = some v := by
  unfold stage2ReadWord
  rw [h]
  simp only [Option.map_some]
  rw [wordBytes, bytesToNat_natToBytes hv]

/-- **A counter whose every position below it satisfies the predicate, and whose own
position does not (or is past the list), is the `takeWhile` length.**  Induction on
the counter, with the head peeled by `takeWhile_cons_of_pos`/`_of_neg`. -/
theorem takeWhile_length_of_counter {l : List Nat} {pos0 : Nat} :
    ∀ (n : Nat), (∀ k, k < n → ∃ q, l[k]? = some q ∧ q < pos0) →
      (l[n]? = none ∨ ∃ q, l[n]? = some q ∧ pos0 ≤ q) →
      (l.takeWhile (fun q => decide (q < pos0))).length = n
  | 0, _, hstop => by
      cases l with
      | nil => rfl
      | cons a t =>
          have hneg : ¬ decide (a < pos0) = true := by
            rcases hstop with h | ⟨q, hq, hle⟩
            · simp only [List.getElem?_cons_zero, Option.some_ne_none] at h
            · simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
              subst hq
              simp only [decide_eq_true_eq]
              omega
          rw [List.takeWhile_cons_of_neg (p := fun q => decide (q < pos0)) hneg]
          rfl
  | n + 1, hstep, hstop => by
      cases l with
      | nil =>
          obtain ⟨q, hq, _⟩ := hstep 0 (by omega)
          simp only [List.getElem?_nil] at hq
          cases hq
      | cons a t =>
          obtain ⟨q, hq, hlt⟩ := hstep 0 (by omega)
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          subst hq
          rw [List.takeWhile_cons_of_pos (p := fun q => decide (q < pos0))
            (by simpa using hlt)]
          simp only [List.length_cons]
          rw [takeWhile_length_of_counter n ?_ ?_]
          · intro k hk
            obtain ⟨q', hq', hlt'⟩ := hstep (k + 1) (by omega)
            exact ⟨q', by simpa using hq', hlt'⟩
          · rcases hstop with h | ⟨q', hq', hle⟩
            · exact Or.inl (by simpa using h)
            · exact Or.inr ⟨q', by simpa using hq', hle⟩

/-- **The scan's counter is the model's `j1`.**  From the invariant's counter `c`
at the exit — every position between `j0` and `c` below the body's first position,
and `c` itself past it or past the list — the model's
`j0 + ((ps.drop j0).takeWhile (fun q => decide (q < pos0))).length` is `c`. -/
theorem scanCounter_eq_takeWhile (ps : List Nat) (pos0 : Nat) (j0 c : Nat)
    (hjc : j0 ≤ c)
    (hstep : ∀ k, j0 ≤ k → k < c → ∃ q, ps[k]? = some q ∧ q < pos0)
    (hstop : ps[c]? = none ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) :
    c = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < pos0))).length := by
  have h := takeWhile_length_of_counter (l := ps.drop j0) (pos0 := pos0) (n := c - j0)
    (by
      intro k hk
      obtain ⟨q, hq, hlt⟩ := hstep (j0 + k) (by omega) (by omega)
      exact ⟨q, by rw [List.getElem?_drop]; simpa using hq, hlt⟩)
    (by
      rcases hstop with h' | ⟨q, hq, hle⟩
      · refine Or.inl ?_
        rw [List.getElem?_drop, Nat.add_sub_cancel' hjc]
        exact h'
      · exact Or.inr ⟨q, by
          rw [List.getElem?_drop, Nat.add_sub_cancel' hjc]
          exact hq, hle⟩)
  omega

/-! ### The scan's bound

The scan is the body's only loop: `land.rhs` reads the lane at the counter, and
`while.body` advances the counter and writes it back.  It leaves in two ways —
`land.rhs` for `land.lhs.true` when the lane is already inside the body, and
`while.body` for `if.then` when the counter reaches the count — so the exit is a
predicate and the head's test is the disjunction of both.

**The cost is two control steps.**  One iteration is `land.rhs`'s step —
`getelementptr`, the lane load, the zero-extension and the test — then
`while.body`'s — the counter's increment, its write-back and the exit test — and
the back edge is the second one's jump, so every instantiation passes `cost = 2`;
the exit is `land.rhs`'s own jump to `land.lhs.true`, one step, inside that bound.
The field is a parameter here for the reason the decoder's instance makes it one:
the arms are the body's facts, and the bound's arithmetic is `BoundLoop`'s.

**The measure is the counter's distance to the count.**  `while.body` writes
`c + 1` to the cursor word it was given, so at the head the cursor word holds the
counter; `Inv r s c` says exactly that, together with `c + r = N`.  Both ways out
are then `atBound`'s two disjuncts: the first is the count reached, the second is
the lane already at or past the body's first position.  Neither is a decrease of
the lane's index — it is the *distance* that falls — which is why the bound is
`N` and not the position list's length. -/

/-- The scan's invariant at the head.  It carries what one iteration needs to run
and to be re-established: the state is at `land.rhs`; its cursor word holds the
counter and the counter plus the budget is the count; the predecessor names a
`phi` whose selected operand already reads the counter (so the `phi` and its edge
are part of the invariant, not of the arm's hypotheses); the four registers the
head reads are the model's arguments widened to `i64`; and the lane at the counter
is the model's `ps` entry there — its bytes and their value, together.  The lane
clause is what forces `c < N`, because `ps[c]?` has no entry at `c = N`.

`mem0` is the memory the scan started from and `xj` the cursor word's address: the
loop's only memory effect is that word's write, one per iteration. -/
def s2StringBodyScanInv (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "land.rhs" ∧ s.mem = writeBytes mem0 xj (wordBytes 8 c) ∧ c + r = N ∧
  (∃ p op, s.pre = some p ∧
    phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op ∧
    evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 c))) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%xj" = some (.ptr xj) ∧
  lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 N)) ∧
  (∃ q bs, ps[c]? = some q ∧ bs.length = 4 ∧ bytesToNat bs = q ∧
    readBytes s.mem (xp + 4 * c) 4 = some bs)

/-- The head's test: the next index reaches the count, or the lane at this index is
already inside the body.  The `match` is the second disjunct in a decidable form —
an unbounded `∃` over `Nat` is not a decision — and
`s2StringBodyScanAtBound_eq` states the disjunction it stands for. -/
def s2StringBodyScanAtBound (ps : List Nat) (pos0 N : Nat) : State → Nat → Bool :=
  fun _ c =>
    decide (N ≤ c + 1) ||
      match ps[c]? with
      | some q => decide (pos0 ≤ q)
      | none => false

/-- The head's test, as the two ways out. -/
theorem s2StringBodyScanAtBound_eq (ps : List Nat) (pos0 N : Nat) (s : State)
    (c : Nat) :
    s2StringBodyScanAtBound ps pos0 N s c = true ↔
      (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) := by
  unfold s2StringBodyScanAtBound
  rw [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · split at h
      · rename_i q hq
        exact Or.inr ⟨q, hq, of_decide_eq_true h⟩
      · cases h
  · rintro (h | ⟨q, hq, hle⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [hq]; exact decide_eq_true hle)

/-! ### The head's bits, from the head's test

The steps take the branch bits as hypotheses; the loop's arms must produce them,
and producing them is this section: the comparison's two outcomes as `BitVec 1`
values, the lane read's value as the model's `ps` entry, and then the head's test
in both of its forms.  Nothing here is about a state's history — the bits are
functions of the counter, the lane and the two bounds — which is why the arms can
be proved once rather than at each iteration. -/

/-- Sign-extending an `i64` value to `i64` is the value. -/
theorem signExtend_ofNat (c : Nat) (hc : c < 2 ^ 64) :
    ((BitVec.ofNat 64 c).signExtend 64).toNat = c := by
  rw [BitVec.toNat_signExtend]
  have hset : (BitVec.setWidth 64 (BitVec.ofNat 64 c)).toNat = c := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hc]
  rw [hset]
  split <;> omega

/-- The counter's increment at the model's width. -/
theorem ofNat_add_one (c : Nat) :
    (BitVec.ofNat 64 c) + 1#64 = BitVec.ofNat 64 (c + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The unsigned-greater test is `1` exactly when the second operand is below the
first, both below `2 ^ 64` (the width the model reads them at). -/
theorem evalICmpNat_ugt_one {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : y < x) : evalICmpNat .ugt 64 x y = 1#1 := by
  simp only [evalICmpNat, evalICmp, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, h, BitVec.ofBool]
  rfl

/-- The same test as `0` when the first operand is at or below the second. -/
theorem evalICmpNat_ugt_zero {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : x ≤ y) : evalICmpNat .ugt 64 x y = 0#1 := by
  have hlt : ¬ y < x := by omega
  simp only [evalICmpNat, evalICmp, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, hlt, BitVec.ofBool]
  rfl

/-- Equality as a one-bit value. -/
theorem evalICmp_eq_one {x y : BitVec 64} (h : x = y) : evalICmp .eq x y = 1#1 := by
  subst h
  simp only [evalICmp, BitVec.ofBool]
  rfl

/-- Inequality as a one-bit value. -/
theorem evalICmp_eq_zero {x y : BitVec 64} (h : x ≠ y) : evalICmp .eq x y = 0#1 := by
  simp only [evalICmp, BitVec.ofBool, h]
  rfl

/-- A four-byte lane is below `2 ^ 32`, so a lane's value is its own widening to
`i64`. -/
theorem bytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have := bytesToNat_lt bs
  rw [h] at this
  calc bytesToNat bs < 256 ^ 4 := this
    _ = 2 ^ 32 := by decide

/-- **The lane the model names.**  A successful lane read gives, at every index
inside it, the list's entry there and the four bytes it was read from — with the
entry being exactly the bytes' value.  This is what lets the head's read at
`xp + c * 4` be the model's `ps[c]`. -/
theorem readLanes32_lane {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧
          bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := readLanes32_lane (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

/-- The head's test, in its false form: the scan has not reached the count and the
lane at the counter is below the body's first position. -/
theorem s2StringBodyScanAtBound_false (ps : List Nat) (pos0 N : Nat) (s : State)
    (c : Nat) :
    s2StringBodyScanAtBound ps pos0 N s c = false ↔
      ¬ (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q) := by
  by_cases h : s2StringBodyScanAtBound ps pos0 N s c = true
  · have hp : N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q :=
      (s2StringBodyScanAtBound_eq ps pos0 N s c).mp h
    exact ⟨fun hf => absurd (hf.symm.trans h) (by decide), fun hn => absurd hp hn⟩
  · have hf : s2StringBodyScanAtBound ps pos0 N s c = false := by
      cases hb : s2StringBodyScanAtBound ps pos0 N s c with
      | false => rfl
      | true => exact absurd hb h
    exact ⟨fun _ hp => h ((s2StringBodyScanAtBound_eq ps pos0 N s c).mpr hp),
      fun _ => hf⟩

/-- The head's lane test when the lane is already inside the body: `0`, so the scan
leaves at the head in one step (`s2StringBodyScanExit`'s bit). -/
theorem evalICmpNat_ugt_of_ge {pos0 q : Nat} (hpos0 : pos0 < 2 ^ 64)
    (hq64 : q < 2 ^ 64) (hge : pos0 ≤ q) :
    evalICmpNat .ugt 64 pos0 q = 0#1 :=
  evalICmpNat_ugt_zero hpos0 hq64 hge

/-- The exit test when the counter has reached the count: `1`, so `while.body`
leaves for `if.then` (`s2StringBodyScanIterate`'s second bit in its exit form). -/
theorem evalICmp_eq_of_eq {c N : Nat} (hN : N < 2 ^ 64) (heq : N = c + 1) :
    evalICmp .eq ((BitVec.ofNat 64 c) + 1#64) (BitVec.ofNat 64 N) = 1#1 := by
  have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hbit : (BitVec.ofNat 64 c) + 1#64 = BitVec.ofNat 64 N := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, heq]
  exact evalICmp_eq_one hbit

/-- **The head's two bits, from the head's test being false**: the lane is the
model's `ps` entry at the counter, `sub` is the body's first position, and the
counter is the index — under which the lane test holds (the scan advances) and the
exit test does not (the counter has not reached the count).  These are exactly the
two hypotheses `s2StringBodyScanIterate` consumes. -/
theorem s2StringBodyScan_bits_of_not_atBound
    {ps : List Nat} {pos0 N c q : Nat} {bs : List UInt8} {s : State}
    {sub inc24 nxp : BitVec 64}
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = false)
    (hq : ps[c]? = some q) (hval : bytesToNat bs = q) (hblen : bs.length = 4)
    (hsub : sub = BitVec.ofNat 64 pos0) (hpos0 : pos0 < 2 ^ 64)
    (hinc24 : inc24 = BitVec.ofNat 64 c) (hnxp : nxp = BitVec.ofNat 64 N)
    (hN : N < 2 ^ 64) :
    evalICmpNat .ugt 64 sub.toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1 ∧
      evalICmp .eq (inc24 + 1#64) nxp = 0#1 := by
  rw [s2StringBodyScanAtBound_false] at hbound
  have hnot : ¬ (N ≤ c + 1 ∨ ∃ q', ps[c]? = some q' ∧ pos0 ≤ q') := hbound
  have hlt : c + 1 < N := by
    by_contra h; exact hnot (Or.inl (by omega))
  have hqlt : q < pos0 := by
    by_contra h; exact hnot (Or.inr ⟨q, hq, by omega⟩)
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = q := by
    have h32 := bytesToNat_lt_32 hblen
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega), hval]
  constructor
  · rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
    exact evalICmpNat_ugt_one hpos0 (by have := bytesToNat_lt_32 hblen; omega) hqlt
  · have hne : (BitVec.ofNat 64 c) + 1#64 ≠ BitVec.ofNat 64 N := by
      intro heq
      have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      have := congrArg BitVec.toNat heq
      rw [htoNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at this
      omega
    rw [hinc24, hnxp]
    exact evalICmp_eq_zero hne

/-- **The invariant's entry**: the head carrying the entry's counter `j0`, with the
count as the whole budget.  The clauses are the staging's facts read at the head —
the predecessor (`entry`, through the `phi`), the four registers, and the lane at
`j0` — which is why this is the only place the pre's content is consumed. -/
theorem s2StringBodyScanInv_entry (mem0 : Mem) (xj pos0 xp N j0 : Nat)
    (ps : List Nat) (s : State)
    (hpc : s.pc = "land.rhs") (hmem : s.mem = writeBytes mem0 xj (wordBytes 8 j0))
    (hj0 : j0 ≤ N)
    (hphi : ∃ p op, s.pre = some p ∧
      phiIncoming p [("while.body", Operand.reg "%inc"),
        ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op ∧
      evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 j0)))
    (hxp : lookupName s.env "%xp" = some (.ptr xp))
    (hsub : lookupName s.env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hxj : lookupName s.env "%xj" = some (.ptr xj))
    (hnxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 N)))
    (hlane : ∃ q bs, ps[j0]? = some q ∧ bs.length = 4 ∧ bytesToNat bs = q ∧
      readBytes s.mem (xp + 4 * j0) 4 = some bs) :
    s2StringBodyScanInv mem0 xj pos0 xp N ps (N - j0) s j0 :=
  ⟨hpc, hmem, by omega, hphi, hxp, hsub, hxj, hnxp, hlane⟩

/-- **The scan is a `BoundLoop`.**  The bound, the head's test, the invariant and
the budget are fixed here; the two arms are the body's — the exit step and one
iteration's return to the head — stated as the shape's per-iteration facts, as the
decoder's and the copy loops' instances state theirs.  The two exits share one
induction: `Exit` is the disjunction of the blocks they leave for. -/
def s2StringBodyScanBoundLoop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e) :
    BoundLoop s2StringBodyCalls s2StringBodyBody where
  head := "land.rhs"
  exitBlock := "land.lhs.true"
  N := N
  cost := cost
  Inv := s2StringBodyScanInv mem0 xj pos0 xp N ps
  atBound := s2StringBodyScanAtBound ps pos0 N
  Exit := Exit
  ExitWord := ExitWord
  step_exit := fun r s c => step_exit r c s
  step_loop := fun r s c => step_loop r c s
  exit_at_zero := by
    intro s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    rw [s2StringBodyScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    omega

/-- **The scan's fuel is a term of the arguments.**  With the body's two arms, the
head reaches an exit within `(N + 1) * cost` control steps, and a completed exit
continuation lifts to the whole loop.  The induction is `BoundLoop.run_at`'s;
nothing here is specific to the scan beyond its invariant. -/
theorem s2StringBodyScan_run_at (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (cost : Nat) (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps r s c →
      s2StringBodyScanAtBound ps pos0 N s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (step_loop : ∀ (r c : Nat) (s : State),
      s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c →
      s2StringBodyScanAtBound ps pos0 N s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.rhs" ∧ c < c' ∧
        s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
        ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
          runFuel s2StringBodyCalls k s2StringBodyBody e)
    (s : State) (c : Nat) (k : Nat) (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps N s c)
    {o : Outcome}
    (hcont : ∀ (e : State), Exit e → ExitWord e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * cost + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanBoundLoop mem0 xj pos0 xp N ps cost Exit ExitWord step_exit
    step_loop).run_at s c hinv k hcont

end LeanLLVM.Refinement
