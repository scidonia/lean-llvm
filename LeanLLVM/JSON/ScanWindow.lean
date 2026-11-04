/-
The window fold: one pass over a block's lanes that reports the masks the scanner
consumes, the lane where the body stops, and the state that crosses the window's
boundary.

`windowOf` asks the byte rule of `ScanBody.lean` once per lane and records its answer
in the mask the answer belongs to: `delim` is set where the rule answers `closed`,
`content` where the rule skips the byte, `stop` at the first lane the rule does not
continue past, and `carry` threads the one `BodyState`.  `carryAt` is the same state
read at a single lane, so a readback below can name the state the rule held at that
lane rather than describe the fold again.

`windowAt` reads the window at a carrier position through the block operation's own
block, so the classification mask and the block layer's are one object; `windowAt`
takes the block's lanes and `windowOf` folds them, so the fold is not a second
classifier.
-/
import LeanLLVM.JSON.ScanBlock
import LeanLLVM.JSON.ScanBody

namespace LeanLLVM.JSON

open ByteString

/-! ### The window and its stop -/

/-- A window's first stop.  `close k` is the lane that closes the body, `refuse k s`
the lane the byte rule refuses at; `none` means every lane the fold read continued —
thirty-two for a full window, fewer for a shorter one. -/
inductive Stop where
  | close (k : Nat)
  | refuse (k : Nat) (stop : BodyStop)
deriving DecidableEq, Repr

/-- What one window reports, and the carry it leaves. -/
structure Window where
  structural : BitVec 32
  quote : BitVec 32
  backslash : BitVec 32
  content : BitVec 32
  delim : BitVec 32
  stop : Option Stop
  carry : BodyState
deriving DecidableEq, Repr

/-- The window a fold starts from: no lane set, no stop, and the state the caller
holds. -/
private def windowInit (st : BodyState) : Window :=
  { structural := 0, quote := 0, backslash := 0, content := 0, delim := 0,
    stop := none, carry := st }

/-- One lane of the fold, as a function of the lane's byte and index, so the lemmas
below can name it.  Each field is the byte rule's own decision at that lane,
recorded: `delim` is set exactly where the rule answers `.closed`, `content` exactly
where it skips, `structural` on the scalar transition's decision whatever the rule
answers, and the carry advances only on `.cont`.  A stop is recorded at the first
lane to raise one and is not overwritten. -/
private def windowLane (w : Window) (p : UInt8 × Nat) : Window :=
  match p with
  | (b, k) =>
    match bodyStep w.carry b with
    | .cont st' =>
        { w with
          structural := if IsStructOrSpaceB b then w.structural ||| ((1 : BitVec 32) <<< k) else w.structural
          quote := if IsQuoteB b then w.quote ||| ((1 : BitVec 32) <<< k) else w.quote
          backslash := if IsBackslashB b then w.backslash ||| ((1 : BitVec 32) <<< k) else w.backslash
          content := if IsContentLane w.carry b then w.content ||| ((1 : BitVec 32) <<< k) else w.content
          carry := st' }
    | .closed =>
        { w with
          structural := if IsStructOrSpaceB b then w.structural ||| ((1 : BitVec 32) <<< k) else w.structural
          quote := w.quote ||| ((1 : BitVec 32) <<< k)
          delim := w.delim ||| ((1 : BitVec 32) <<< k)
          stop := (match w.stop with | some s => some s | none => some (.close k)) }
    | .refused s =>
        { w with
          structural := if IsStructOrSpaceB b then w.structural ||| ((1 : BitVec 32) <<< k) else w.structural
          stop := (match w.stop with | some s => some s | none => some (.refuse k s)) }

/-- The one lane fold.  Each lane asks the byte rule once: `delim` is set exactly on
the lanes it answers `.closed`, `content` exactly on the lanes it skips, `stop` records
the first lane it does not continue past, and the accumulator threads the single
`BodyState`.  Every lane is asked, the lanes past a stop included, so each mask field
is the rule's decision at its own lane; the carry past a stop is the clamped fold's,
and a window read as a run of `bodyStep` reaches the lanes before `stop` and no
further. -/
def windowOf (bs : List UInt8) (st : BodyState) : Window :=
  (bs.zipIdx.take 32).foldl windowLane (windowInit st)

/-- The window of a carrier at `i`: the same fold at the block's lanes. -/
def windowAt (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (st : BodyState) : Window :=
  windowOf (List.ofFn (blockAt bs i h)) st

/-- The carry on entry to lane `k`: the fold's prefix, which is the state the byte
rule holds at that lane. -/
def carryAt (bs : List UInt8) (st : BodyState) (k : Nat) : BodyState :=
  (bs.take k).foldl
    (fun st b => match bodyStep st b with | .cont st' => st' | _ => st) st

/-! ### The lanes of the block

The fold runs over `bs.zipIdx.take 32`, so lane `k` is the pair `(bs[k], k)`, and the
pairs before it are the lanes before it.  The lemmas below state those two facts about
the list the fold is given, and the two bits of a packed lane the readbacks read.
-/

/-- Bit `k` of a packed lane is unaffected by a lane that is not `k`. -/
private theorem getLsbD_or_shift_of_ne {x : BitVec 32} {j k : Nat} (hjk : j ≠ k) :
    (x ||| ((1 : BitVec 32) <<< j)).getLsbD k = x.getLsbD k := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
  by_cases hk : k < 32
  · by_cases h : k < j
    · simp [hk, h]
    · have h0 : k - j ≠ 0 := by omega
      simp [hk, h, h0]
  · simp [hk]

/-- Bit `j` of a packed lane is set by its own lane. -/
private theorem getLsbD_or_shift_self {x : BitVec 32} {j : Nat} (hj : j < 32) :
    (x ||| ((1 : BitVec 32) <<< j)).getLsbD j = true := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
  have h0 : j - j = 0 := by omega
  have hnn : ¬ j < j := by omega
  simp [hj, h0, hnn]

/-- Bit `j` of a lane written under a condition is the lane's own bit or-ed with the
condition, which is the shape every mask field has. -/
private theorem getLsbD_ite_or {x : BitVec 32} {c : Bool} {j : Nat} (hj : j < 32) :
    (if c = true then x ||| ((1 : BitVec 32) <<< j) else x).getLsbD j = (x.getLsbD j || c) := by
  by_cases hc : c = true
  · rw [ite_eq_left hc, hc]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
    have h0 : j - j = 0 := by omega
    have hnn : ¬ j < j := by omega
    simp [hj, h0, hnn]
  · rw [ite_eq_right hc]
    simp [hc]

/-- Bit `k` of a lane written under a condition is untouched when the lane is not `k`. -/
private theorem getLsbD_ite_or_ne {x : BitVec 32} {c : Bool} {j k : Nat} (hjk : j ≠ k) :
    (if c = true then x ||| ((1 : BitVec 32) <<< j) else x).getLsbD k = x.getLsbD k := by
  by_cases hc : c = true
  · rw [ite_eq_left hc]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
    by_cases hk : k < 32
    · by_cases h : k < j
      · simp [hk, h]
      · have h0 : k - j ≠ 0 := by omega
        simp [hk, h, h0]
    · simp [hk]
  · rw [ite_eq_right hc]

/-- Lane `k` of the fold's list is the byte at `k`, while the list reaches it. -/
private theorem zipIdx_take_getElem? (bs : List UInt8) {k : Nat} (hk : k < 32) :
    (bs.zipIdx.take 32)[k]? = (bs[k]?).map (fun b => (b, k)) := by
  rw [List.getElem?_take, ite_eq_left hk, List.getElem?_zipIdx]
  simp

/-- Lane `k` of the fold's list, when the carrier has a byte there. -/
private theorem zipIdx_take_getElem?_some {bs : List UInt8} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (bs.zipIdx.take 32)[k]? = some (b, k) := by
  rw [zipIdx_take_getElem? bs hk, hb]
  rfl

/-- Every lane of the fold's list is one of the first thirty-two. -/
private theorem snd_lt_of_mem_zipIdx_take {bs : List UInt8} {p : UInt8 × Nat}
    (h : p ∈ bs.zipIdx.take 32) : p.2 < 32 := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨i, hi⟩ := h
  rw [List.getElem?_take] at hi
  by_cases h32 : i < 32
  · rw [ite_eq_left h32, List.getElem?_zipIdx] at hi
    cases hb : bs[i]? with
    | none => rw [hb] at hi; simp at hi
    | some c =>
        rw [hb] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        rw [← hi]
        simpa using h32
  · rw [ite_eq_right h32] at hi
    simp at hi

/-- The lanes before `k` do not include `k`. -/
private theorem snd_ne_of_mem_take {bs : List UInt8} {k : Nat} (hk : k < 32) {p : UInt8 × Nat}
    (h : p ∈ (bs.zipIdx.take 32).take k) : p.2 ≠ k := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨j, hj⟩ := h
  rw [List.getElem?_take] at hj
  by_cases hjk : j < k
  · rw [ite_eq_left hjk, zipIdx_take_getElem? bs (by omega)] at hj
    cases hb : bs[j]? with
    | none => rw [hb] at hj; simp at hj
    | some c =>
        rw [hb] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        rw [← hj]
        omega
  · rw [ite_eq_right hjk] at hj
    simp at hj

/-- The lanes after `k` do not include `k`. -/
private theorem snd_ne_of_mem_drop {bs : List UInt8} {k : Nat} {p : UInt8 × Nat}
    (h : p ∈ (bs.zipIdx.take 32).drop (k + 1)) : p.2 ≠ k := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨i, hi⟩ := h
  rw [List.getElem?_drop] at hi
  by_cases h32 : k + 1 + i < 32
  · rw [zipIdx_take_getElem? bs h32] at hi
    cases hb : bs[k + 1 + i]? with
    | none => rw [hb] at hi; simp at hi
    | some c =>
        rw [hb] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        rw [← hi]
        omega
  · rw [List.getElem?_take, ite_eq_right h32] at hi
    simp at hi

/-! ### What the byte rule answers

The readbacks below are of the form "the lane's own bit is the rule's decision at the
lane's carry", so they need three facts about `bodyStep` that its `if`-chain states
implicitly: a content lane continues, a closing lane is a quote, and a closing lane is
not a backslash.
-/

/-- A byte below `0x80` is a complete character. -/
private theorem step_none_of_lt {b : UInt8} (hb : b < 0x80) :
    Utf8Need.step .none b = some .none := by
  simp only [Utf8Need.step]
  rw [ite_eq_left hb]

/-- A content lane continues the run: the predicate the mask records is exactly the
byte rule's skip decision, so the mask cannot mark a lane the rule stopped at. -/
private theorem cont_of_content {st : BodyState} {b : UInt8}
    (h : IsContentLane st b = true) : ∃ st', bodyStep st b = .cont st' := by
  unfold IsContentLane at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hinside, hodd⟩, hutf8⟩, hquote⟩, hslash⟩, hspace⟩, hascii⟩ := h
  have hctl : ¬ b < 0x20 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hspace ⊢
    omega
  have hbs : IsBackslashB b = false := hslash
  have hq : IsQuoteB b = false := hquote
  have hstep : Utf8Need.step .none b = some .none := step_none_of_lt hascii
  simp only [bodyStep, hutf8, hodd, hq, hbs, hinside, hctl, hstep]
  exact ⟨_, rfl⟩

/-- No content lane is refused or closing, which is what makes the content mask and
the byte rule one rule. -/
private theorem not_content_of_not_cont {st : BodyState} {b : UInt8}
    (h : ∀ st', bodyStep st b ≠ .cont st') : IsContentLane st b = false := by
  cases hc : IsContentLane st b with
  | false => rfl
  | true =>
      obtain ⟨st', hst'⟩ := cont_of_content hc
      exact absurd hst' (h st')

/-- A lane that closes the body is a quote lane. -/
private theorem isQuote_of_closed {st : BodyState} {b : UInt8}
    (h : bodyStep st b = .closed) : IsQuoteB b = true := by
  unfold bodyStep at h
  by_cases h1 : st.utf8 ≠ Utf8Need.none
  · cases hs : st.utf8.step b with
    | none =>
        simp only [ite_eq_left h1, hs] at h
        cases h
    | some u =>
        simp only [ite_eq_left h1, hs] at h
        cases h
  · simp only [ite_eq_right h1] at h
    by_cases h2 : st.oddRun = true
    · simp only [h2] at h
      cases h
    · simp only [h2] at h
      by_cases h3 : IsQuoteB b = true
      · exact h3
      · simp only [h3] at h
        by_cases h4 : IsBackslashB b = true
        · simp only [h4] at h
          cases h
        · simp only [h4] at h
          by_cases h5 : (st.inside && decide (b < 0x20)) = true
          · simp only [h5] at h
            cases h
          · simp only [h5] at h
            by_cases h6 : st.inside = true
            · simp only [h6] at h
              cases hs : Utf8Need.step .none b with
              | none =>
                  simp only [hs] at h
                  cases h
              | some u =>
                  simp only [hs] at h
                  cases h
            · simp only [h6] at h
              cases h

/-- A quote lane is not a backslash lane, so the two masks never mark one byte. -/
private theorem isBackslash_false_of_quote {b : UInt8} (h : IsQuoteB b = true) :
    IsBackslashB b = false := by
  have hb : b = 0x22 := of_decide_eq_true h
  subst hb
  decide

/-! ### The carry

`carryAt` is the fold's prefix state, so the two facts the readbacks need are that the
fold's carry is the clamped byte fold and that the clamped byte fold over the first
`k` lanes is `carryAt` at `k`.
-/

/-- One byte of the clamped fold: it advances on a continuing step and stays put
otherwise, which is exactly what the fold's carry does. -/
private theorem carryAt_succ (bs : List UInt8) (st : BodyState) (k : Nat) :
    carryAt bs st (k + 1) =
      (match bs[k]? with
       | some b =>
           (match bodyStep (carryAt bs st k) b with
            | .cont st' => st'
            | _ => carryAt bs st k)
       | none => carryAt bs st k) := by
  unfold carryAt
  rw [List.take_add_one, List.foldl_append]
  cases h : bs[k]? with
  | none => simp
  | some b => simp

/-- The fold's carry is the clamped fold over the lanes' bytes. -/
private theorem fold_carry (l : List (UInt8 × Nat)) (w : Window) :
    (l.foldl windowLane w).carry =
      l.foldl
        (fun (st : BodyState) (p : UInt8 × Nat) =>
          match bodyStep st p.1 with | .cont st' => st' | _ => st)
        w.carry := by
  induction l generalizing w with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨b, k⟩ := p
    rw [List.foldl_cons, List.foldl_cons, ih]
    cases h : bodyStep w.carry b <;> simp [windowLane, h]

/-- The clamped fold over the first `k` lanes is `carryAt` at `k`. -/
private theorem fold_take_carry (bs : List UInt8) (st : BodyState) :
    ∀ k ≤ 32,
      ((bs.zipIdx.take 32).take k).foldl
          (fun (st : BodyState) (p : UInt8 × Nat) =>
            match bodyStep st p.1 with | .cont st' => st' | _ => st)
          st = carryAt bs st k := by
  intro k
  induction k with
  | zero => intro _; simp [carryAt]
  | succ k ih =>
    intro hk
    have hk32 : k < 32 := by omega
    rw [List.take_add_one, List.foldl_append, ih (by omega)]
    cases hb : bs[k]? with
    | none =>
        rw [zipIdx_take_getElem? bs hk32, hb, carryAt_succ bs st k, hb]
        simp [Option.toList_none]
    | some b =>
        rw [zipIdx_take_getElem? bs hk32, hb, carryAt_succ bs st k, hb]
        simp [Option.toList_some]

/-! ### Reading one lane

`windowLane` writes each mask at the lane's own index, so a mask's bit `k` is decided
by lane `k` alone: the lanes before it leave the bit as the initial window's, and the
lanes after it cannot touch it.  The two lemmas below state that for the five masks.
-/

/-- Lane `k` is the only lane that writes bit `k`, and it writes it with the rule's
decision at the lane's carry. -/
private theorem windowLane_self (w : Window) (b : UInt8) (k : Nat) (hk : k < 32) :
    (windowLane w (b, k)).structural.getLsbD k = (w.structural.getLsbD k || IsStructOrSpaceB b) ∧
    (windowLane w (b, k)).quote.getLsbD k =
      (w.quote.getLsbD k ||
        (match bodyStep w.carry b with
         | .cont _ => IsQuoteB b
         | .closed => true
         | .refused _ => false)) ∧
    (windowLane w (b, k)).backslash.getLsbD k =
      (w.backslash.getLsbD k ||
        (match bodyStep w.carry b with | .cont _ => IsBackslashB b | _ => false)) ∧
    (windowLane w (b, k)).content.getLsbD k =
      (w.content.getLsbD k ||
        (match bodyStep w.carry b with
         | .cont _ => IsContentLane w.carry b
         | _ => false)) ∧
    (windowLane w (b, k)).delim.getLsbD k =
      (w.delim.getLsbD k ||
        (match bodyStep w.carry b with | .closed => true | _ => false)) := by
  cases hs : bodyStep w.carry b
  · simp only [windowLane, hs]
    exact ⟨getLsbD_ite_or hk, getLsbD_ite_or hk, getLsbD_ite_or hk, getLsbD_ite_or hk, by simp⟩
  · simp only [windowLane, hs]
    refine ⟨getLsbD_ite_or hk, ?_, by simp, by simp, ?_⟩
    · rw [getLsbD_or_shift_self hk]; simp
    · rw [getLsbD_or_shift_self hk]; simp
  · simp only [windowLane, hs]
    exact ⟨getLsbD_ite_or hk, by simp, by simp, by simp, by simp⟩

/-- A lane that is not `k` leaves bit `k` of every mask alone. -/
private theorem windowLane_other (w : Window) (b : UInt8) (j : Nat) {k : Nat}
    (hjk : j ≠ k) :
    (windowLane w (b, j)).structural.getLsbD k = w.structural.getLsbD k ∧
    (windowLane w (b, j)).quote.getLsbD k = w.quote.getLsbD k ∧
    (windowLane w (b, j)).backslash.getLsbD k = w.backslash.getLsbD k ∧
    (windowLane w (b, j)).content.getLsbD k = w.content.getLsbD k ∧
    (windowLane w (b, j)).delim.getLsbD k = w.delim.getLsbD k := by
  cases hs : bodyStep w.carry b
  · simp only [windowLane, hs]
    exact ⟨getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk,
      getLsbD_ite_or_ne hjk, by simp⟩
  · simp only [windowLane, hs]
    refine ⟨getLsbD_ite_or_ne hjk, ?_, by simp, by simp, ?_⟩
    · rw [getLsbD_or_shift_of_ne hjk]
    · rw [getLsbD_or_shift_of_ne hjk]
  · simp only [windowLane, hs]
    exact ⟨getLsbD_ite_or_ne hjk, by simp, by simp, by simp, by simp⟩

/-- Lanes that are not `k` leave bit `k` of every mask alone. -/
private theorem fold_no_hit (l : List (UInt8 × Nat)) (w : Window) (k : Nat)
    (hne : ∀ p ∈ l, p.2 ≠ k) :
    (l.foldl windowLane w).structural.getLsbD k = w.structural.getLsbD k ∧
    (l.foldl windowLane w).quote.getLsbD k = w.quote.getLsbD k ∧
    (l.foldl windowLane w).backslash.getLsbD k = w.backslash.getLsbD k ∧
    (l.foldl windowLane w).content.getLsbD k = w.content.getLsbD k ∧
    (l.foldl windowLane w).delim.getLsbD k = w.delim.getLsbD k := by
  induction l generalizing w with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    obtain ⟨b, j⟩ := p
    have hjk : j ≠ k := hne (b, j) (by simp)
    have htl : ∀ q ∈ l, q.2 ≠ k := fun q hq => hne q (List.mem_cons_of_mem _ hq)
    rw [List.foldl_cons]
    have hrec := ih (windowLane w (b, j)) htl
    have hstep := windowLane_other w b j hjk
    exact ⟨hrec.1.trans hstep.1, hrec.2.1.trans hstep.2.1,
      hrec.2.2.1.trans hstep.2.2.1, hrec.2.2.2.1.trans hstep.2.2.2.1,
      hrec.2.2.2.2.trans hstep.2.2.2.2⟩

/-- The fold split at a lane: the lanes after it fold the window the lanes up to it
leave, and the lane itself is applied last to that window. -/
private theorem foldl_lane_split (l : List (UInt8 × Nat)) (w : Window) (k : Nat)
    (p : UInt8 × Nat) (h : l[k]? = some p) :
    l.foldl windowLane w =
      (l.drop (k + 1)).foldl windowLane (windowLane ((l.take k).foldl windowLane w) p) := by
  conv => lhs; rw [← List.take_append_drop (k + 1) l]
  rw [List.foldl_append, List.take_add_one, h]
  simp

/-- The fold split at lane `k` of a window over a byte list: the lanes after it fold
the window the lanes up to it leave.  Lane `k` is the byte the carrier holds there. -/
private theorem fold_take_split (bs : List UInt8) (st : BodyState) {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (bs.zipIdx.take 32).foldl windowLane (windowInit st) =
      ((bs.zipIdx.take 32).drop (k + 1)).foldl windowLane
        (windowLane (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st))
          (b, k)) :=
  foldl_lane_split _ _ k (b, k) (zipIdx_take_getElem?_some hk hb)

/-! ### The readbacks -/

/-- **The mask and the machine cannot drift.**  A lane is marked content exactly when
the byte rule skips it, on the carry the fold reached at that lane — both read
`IsContentLane`. -/
theorem windowOf_content_agrees {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (windowOf bs st).content.getLsbD k = IsContentLane (carryAt bs st k) b := by
  have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
  have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
  have hpre : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).content.getLsbD k
      = false := by
    rw [(fold_no_hit _ _ k hnt).2.2.2.1]
    simp [windowInit]
  have hcarry : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).carry
      = carryAt bs st k := by
    rw [fold_carry]
    exact fold_take_carry bs st k (by omega)
  rw [windowOf, fold_take_split bs st hk hb, (fold_no_hit _ _ k hnd).2.2.2.1,
    windowLane_self _ b k hk |>.2.2.2.1, hpre, hcarry]
  cases hstep : bodyStep (carryAt bs st k) b with
  | cont st' => simp
  | closed =>
      have hnc := not_content_of_not_cont (st := carryAt bs st k) (b := b)
        (fun st' h => by rw [hstep] at h; cases h)
      simp [hnc]
  | refused s =>
      have hnc := not_content_of_not_cont (st := carryAt bs st k) (b := b)
        (fun st' h => by rw [hstep] at h; cases h)
      simp [hnc]

/-- A delimiter lane is exactly a lane where the byte rule closes the body: the mask
is the rule's closure decision, not a formula that has to agree with it. -/
theorem windowOf_delim {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (windowOf bs st).delim.getLsbD k =
      (match bodyStep (carryAt bs st k) b with | .closed => true | _ => false) := by
  have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
  have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
  have hpre : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).delim.getLsbD k
      = false := by
    rw [(fold_no_hit _ _ k hnt).2.2.2.2]
    simp [windowInit]
  have hcarry : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).carry
      = carryAt bs st k := by
    rw [fold_carry]
    exact fold_take_carry bs st k (by omega)
  rw [windowOf, fold_take_split bs st hk hb, (fold_no_hit _ _ k hnd).2.2.2.2,
    windowLane_self _ b k hk |>.2.2.2.2, hpre, hcarry]
  cases hstep : bodyStep (carryAt bs st k) b <;> simp

/-- A stop the fold records is one of its lanes, and a lane that closes writes its own
delimiter bit: so the stop's lane is a delimiter lane. -/
private theorem fold_stop_close_delim (l : List (UInt8 × Nat)) (w : Window)
    (hlt : ∀ p ∈ l, p.2 < 32)
    (hw : ∀ j, w.stop = some (.close j) → w.delim.getLsbD j = true) :
    ∀ j, (l.foldl windowLane w).stop = some (.close j) →
      (l.foldl windowLane w).delim.getLsbD j = true := by
  induction l generalizing w with
  | nil => intro j hj; exact hw j hj
  | cons p l ih =>
    obtain ⟨b, i⟩ := p
    have hi : i < 32 := hlt (b, i) (by simp)
    have hlt' : ∀ q ∈ l, q.2 < 32 := fun q hq => hlt q (List.mem_cons_of_mem _ hq)
    have hstep : ∀ j, (windowLane w (b, i)).stop = some (.close j) →
        (windowLane w (b, i)).delim.getLsbD j = true := by
      intro j hj
      cases hs : bodyStep w.carry b
      · simp only [windowLane, hs] at hj ⊢
        exact hw j hj
      · simp only [windowLane, hs] at hj ⊢
        cases hw' : w.stop with
        | none =>
            simp only [hw'] at hj
            cases hj
            exact getLsbD_or_shift_self hi
        | some s =>
            simp only [hw'] at hj
            cases hj
            by_cases hik : i = j
            · subst hik
              exact getLsbD_or_shift_self hi
            · rw [getLsbD_or_shift_of_ne hik]
              exact hw j hw'
      · simp only [windowLane, hs] at hj ⊢
        cases hw' : w.stop with
        | none =>
            simp only [hw'] at hj
            cases hj
        | some s =>
            simp only [hw'] at hj
            cases hj
            exact hw j hw'
    exact ih (windowLane w (b, i)) hlt' hstep

/-- A closing stop's lane is a delimiter lane: the scan reads its close from the mask. -/
theorem windowOf_stop_close {bs : List UInt8} {st : BodyState} {k : Nat}
    (h : (windowOf bs st).stop = some (.close k)) : (windowOf bs st).delim.getLsbD k = true :=
  fold_stop_close_delim (bs.zipIdx.take 32) (windowInit st)
    (fun p hp => snd_lt_of_mem_zipIdx_take hp)
    (fun j hj => by simp [windowInit] at hj) k (by simpa [windowOf] using h)

/-- The quote mask is the fold's, read back lane by lane — **with the hypothesis that
the lane was not refused**.  The fold's `.refused` branch records only the
classification bit and the stop, and a lane at a quote can be refused: an outstanding
sequence is consulted first, and `0x22` is outside every continuation range, so
`[0xC3, 0x22]` from `BodyState.body` refuses lane 1 as `.badUtf8`. -/
theorem windowOf_quote {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b)
    (hnr : ∀ s, bodyStep (carryAt bs st k) b ≠ .refused s) :
    (windowOf bs st).quote.getLsbD k = IsQuoteB b := by
  have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
  have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
  have hpre : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).quote.getLsbD k
      = false := by
    rw [(fold_no_hit _ _ k hnt).2.1]
    simp [windowInit]
  have hcarry : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).carry
      = carryAt bs st k := by
    rw [fold_carry]
    exact fold_take_carry bs st k (by omega)
  rw [windowOf, fold_take_split bs st hk hb, (fold_no_hit _ _ k hnd).2.1,
    windowLane_self _ b k hk |>.2.1, hpre, hcarry]
  cases hstep : bodyStep (carryAt bs st k) b with
  | cont st' => simp
  | closed => simp [isQuote_of_closed hstep]
  | refused s => exact absurd hstep (hnr s)

/-- The backslash mask, read back on the same terms as the quote mask. -/
theorem windowOf_backslash {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b)
    (hnr : ∀ s, bodyStep (carryAt bs st k) b ≠ .refused s) :
    (windowOf bs st).backslash.getLsbD k = IsBackslashB b := by
  have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
  have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
  have hpre : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).backslash.getLsbD k
      = false := by
    rw [(fold_no_hit _ _ k hnt).2.2.1]
    simp [windowInit]
  have hcarry : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).carry
      = carryAt bs st k := by
    rw [fold_carry]
    exact fold_take_carry bs st k (by omega)
  rw [windowOf, fold_take_split bs st hk hb, (fold_no_hit _ _ k hnd).2.2.1,
    windowLane_self _ b k hk |>.2.2.1, hpre, hcarry]
  cases hstep : bodyStep (carryAt bs st k) b with
  | cont st' => simp
  | closed => simp [isBackslash_false_of_quote (isQuote_of_closed hstep)]
  | refused s => exact absurd hstep (hnr s)

/-- The mask fold leaves bit `k` clear when no lane it reads is lane `k`: the fold
writes only the lanes' own bits, and the accumulator starts clear. -/
private theorem maskFold_testBit_false {f : UInt8 → Bool}
    (l : List (UInt8 × Nat)) (acc : Nat) (k : Nat) (hacc : acc.testBit k = false)
    (hne : ∀ p ∈ l, p.2 ≠ k) :
    (l.foldl (fun acc (p : UInt8 × Nat) => if f p.1 then acc ||| (1 <<< p.2) else acc) acc).testBit k
      = false := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons p l ih =>
    obtain ⟨b, j⟩ := p
    rw [List.foldl_cons]
    apply ih
    · by_cases hf : f b = true
      · rw [ite_eq_left hf, Nat.testBit_or, hacc, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
          decide_eq_false (hne (b, j) (by simp))]
        simp
      · rw [ite_eq_right hf]; exact hacc
    · intro q hq; exact hne q (List.mem_cons_of_mem _ hq)

/-- The classification mask has no bit past the carrier's length. -/
private theorem maskOfList_getLsbD_of_none {bs : List UInt8} {k : Nat} (hk : k < 32)
    (hb : bs[k]? = none) : (maskOfList bs).getLsbD k = false := by
  unfold maskOfList
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
  apply maskFold_testBit_false
  · exact Nat.zero_testBit k
  · intro p hp hpk
    rw [List.mem_iff_getElem?] at hp
    obtain ⟨i, hi⟩ := hp
    have h32 : i < 32 := by
      by_cases h : i < 32
      · exact h
      · rw [List.getElem?_take, ite_eq_right h] at hi
        simp at hi
    have hi' : (bs.zipIdx)[i]? = some p := by
      rw [← hi, List.getElem?_take, ite_eq_left h32]
    rw [List.getElem?_zipIdx] at hi'
    cases hbi : bs[i]? with
    | none => rw [hbi] at hi'; simp at hi'
    | some c =>
        rw [hbi] at hi'
        simp only [Option.map_some, Option.some.injEq] at hi'
        have hp2 : p.2 = i := by
          rw [← hi']
          simp
        rw [hp2] at hpk
        rw [hpk] at hbi
        rw [hb] at hbi
        cases hbi

/-- The fold's classification mask is the block layer's, so the classifier's mask and
the scanner's are one object. -/
theorem windowOf_structural (bs : List UInt8) (st : BodyState) :
    (windowOf bs st).structural = maskOfList bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  cases hb : bs[k]? with
  | some b =>
    have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
    have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
    have hpre : (((bs.zipIdx.take 32).take k).foldl windowLane (windowInit st)).structural.getLsbD k
        = false := by
      rw [(fold_no_hit _ _ k hnt).1]
      simp [windowInit]
    rw [windowOf, fold_take_split bs st hk hb, (fold_no_hit _ _ k hnd).1,
      windowLane_self _ b k hk |>.1, hpre, Bool.false_or]
    exact (maskOfList_getLsbD hk hb).symm
  | none =>
    have hnone : bs[k]? = none := hb
    have hne : ∀ p ∈ bs.zipIdx.take 32, p.2 ≠ k := by
      intro p hp hpk
      rw [List.mem_iff_getElem?] at hp
      obtain ⟨i, hi⟩ := hp
      have h32 : i < 32 := by
        by_cases h : i < 32
        · exact h
        · rw [List.getElem?_take, ite_eq_right h] at hi
          simp at hi
      have hi' : (bs.zipIdx)[i]? = some p := by
        rw [← hi, List.getElem?_take, ite_eq_left h32]
      rw [List.getElem?_zipIdx] at hi'
      cases hbi : bs[i]? with
      | none => rw [hbi] at hi'; simp at hi'
      | some c =>
          rw [hbi] at hi'
          simp only [Option.map_some, Option.some.injEq] at hi'
          have hp2 : p.2 = i := by
            rw [← hi']
            simp
          rw [hp2] at hpk
          rw [hpk] at hbi
          rw [hnone] at hbi
          cases hbi
    rw [windowOf, (fold_no_hit _ _ k hne).1]
    simp only [windowInit]
    rw [maskOfList_getLsbD_of_none hk hnone]
    simp

/-- The window at a carrier position reports the block operation's mask. -/
theorem windowAt_structural (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (st : BodyState) :
    (windowAt bs i h st).structural = (scanBlock ⟨i⟩ (blockAt bs i h) 32).2.1 := by
  rw [windowAt, windowOf_structural]
  rfl

/-- The fold leaves the carry the window's own byte run leaves. -/
theorem windowOf_carry (bs : List UInt8) (st : BodyState) :
    (windowOf bs st).carry = carryAt bs st 32 := by
  rw [windowOf, fold_carry, show (windowInit st).carry = st from rfl]
  have h := fold_take_carry bs st 32 (by omega)
  rw [List.take_take, Nat.min_self] at h
  exact h

/-- Well-formedness is preserved by the fold. -/
theorem windowOf_wellFormed {bs : List UInt8} {st : BodyState} (h : st.WellFormed) :
    (windowOf bs st).carry.WellFormed := by
  have hfold : ∀ (l : List (UInt8 × Nat)) (w : Window), w.carry.WellFormed →
      (l.foldl windowLane w).carry.WellFormed := by
    intro l
    induction l with
    | nil => intro w hw; exact hw
    | cons p l ih =>
      intro w hw
      obtain ⟨b, k⟩ := p
      rw [List.foldl_cons]
      apply ih
      cases hs : bodyStep w.carry b with
      | cont st' =>
          simp only [windowLane, hs]
          exact bodyStep_wellFormed hw hs
      | closed => simpa only [windowLane, hs] using hw
      | refused s => simpa only [windowLane, hs] using hw
  exact hfold (bs.zipIdx.take 32) (windowInit st) h

/-- The carry folds across a window boundary: the state after `a` then `k` bytes of
`b` is the state `k` bytes into `b` from the state after `a`. -/
theorem carryAt_append (a b : List UInt8) (st : BodyState) (k : Nat) :
    carryAt (a ++ b) st (a.length + k) = carryAt b (carryAt a st a.length) k := by
  unfold carryAt
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.foldl_append, List.take_length]

/-! ### The escape rule that is not the fold's

The fold's quote lane is the byte rule's closure decision, and the byte rule reads the
parity of the backslash run **immediately** before the quote.  The tempting
alternative is parity over every backslash since the body's opening quote.  The two
agree exactly when the parity of all backslashes equals the parity of that run, that
is, when the backslashes outside the run number evenly: `\"`, `\\`, the two-escape
pair `\uD83D\uDE00` and `\n\n"` agree, while `\n\\"` closes the body and the
alternative calls that quote escaped, and the single escape `\u"` disagrees as well.
The definition below is the alternative; the theorem refuses it on `\n\\"`, because a
comparison of two `Bool`s would assert nothing about the rule. -/

/-- The alternative rule: a quote is escaped when the body has seen an odd number of
backslashes since its opening quote.  The fold is the parity itself, since that is all
the alternative reads. -/
def backslashParityEscapes (bs : List UInt8) (k : Nat) : Bool :=
  (bs.take k).foldl (fun (odd : Bool) b => if b = 0x5C then !odd else odd) false

/-- The alternative rule is not the fold's: on `\n\\"` it calls the closing quote
escaped, and the fold marks that lane a delimiter. -/
theorem backslashParityEscapes_not_refines :
    ¬ (∀ (bs : List UInt8) (k : Nat), k < 32 → bs[k]? = some 0x22 →
        ((windowOf bs BodyState.body).delim.getLsbD k = true ↔
          backslashParityEscapes bs k = false)) := by
  intro h
  have hdelim : (windowOf [0x5C, 0x6E, 0x5C, 0x5C, 0x22] BodyState.body).delim.getLsbD 4 = true := by
    decide
  have := (h [0x5C, 0x6E, 0x5C, 0x5C, 0x22] 4 (by decide) rfl).mp hdelim
  exact absurd this (by decide)

end LeanLLVM.JSON
