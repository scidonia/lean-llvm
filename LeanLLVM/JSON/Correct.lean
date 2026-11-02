/-
The correctness theorems: the parser, the grammar and the decoder related.

This is the only module that mentions both sides.  `parseRef_sound` and
`parseRef_complete` are the two directions of the parser's relation to
`ValidDocument`; `tape_valid` and `decodeTape_correct` establish that the tape
carries the meaning rather than a private copy of it; and the two adherence
theorems restate the pair in RFC 8259's vocabulary.
-/
import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Tape
import LeanLLVM.JSON.Parse
import LeanLLVM.JSON.TapeCorrect

namespace LeanLLVM.JSON

/-! #### Byte and number helpers -/

private theorem drop_eq_cons_of_get? {l : List UInt8} {i : Nat} {a : UInt8}
    (h : l[i]? = some a) : l.drop i = a :: l.drop (i + 1) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hlt, hget]

private theorem hasPrefix_head {bs : Bytes} {i : Nat} {b : UInt8} {p : Bytes}
    (h : HasPrefix bs i (b :: p)) : bs[i]? = some b := by
  unfold HasPrefix at h
  have h1 : ((bs.drop i).take (b :: p).length).head? = some b := by
    rw [h]; rfl
  rw [List.head?_take] at h1
  simp only [List.length_cons] at h1
  rw [if_neg (by omega)] at h1
  rwa [List.head?_drop] at h1

private def ValueStartB (b : UInt8) : Bool :=
  decide (b = 0x6E) || decide (b = 0x74) || decide (b = 0x66) ||
  decide (b = 0x22) || decide (b = 0x5B) || decide (b = 0x7B) ||
  decide (b = 0x2D) || IsDigitB b

private theorem isDigit_not_space {b : UInt8} (h : IsDigitB b = true) :
    IsSpaceB b = false := by
  simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [UInt8.le_iff_toNat_le] at h1 h2
  have h20 : decide (b = 0x20) = false := by
    rw [decide_eq_false_iff_not]; intro hb; subst hb; simp at h1
  have h09 : decide (b = 0x09) = false := by
    rw [decide_eq_false_iff_not]; intro hb; subst hb; simp at h1
  have h0a : decide (b = 0x0A) = false := by
    rw [decide_eq_false_iff_not]; intro hb; subst hb; simp at h1
  have h0d : decide (b = 0x0D) = false := by
    rw [decide_eq_false_iff_not]; intro hb; subst hb; simp at h1
  simp only [IsSpaceB, h20, h09, h0a, h0d, Bool.or_false]

private theorem valueStart_not_space {b : UInt8} (h : ValueStartB b = true) :
    IsSpaceB b = false := by
  simp only [ValueStartB] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · exact isDigit_not_space h

private theorem valueStart_ne_ef : ValueStartB 0xEF = false := by decide
private theorem valueStart_closeBracket : ValueStartB 0x5D = false := by decide

/-! #### Number productions are number constituents -/

private theorem isDigit_constituent {b : UInt8} (h : IsDigitB b = true) :
    NumConstituent b = true := by
  simp [NumConstituent, h]

private theorem digits_constituent {bs : Bytes} (h : Digits bs) :
    ∀ b ∈ bs, NumConstituent b = true := fun b hb =>
  isDigit_constituent (digits_all h b hb)

private theorem digits0_constituent {bs : Bytes} (h : Digits0 bs) :
    ∀ b ∈ bs, NumConstituent b = true := fun b hb =>
  isDigit_constituent (digits0_all h b hb)

private theorem intPart_head {b : UInt8} {rest : Bytes}
    (h : IntPart (b :: rest)) : IsDigitB b = true := by
  cases h with
  | zero => decide
  | lead h1 h2 _ =>
      simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨UInt8.le_trans (by decide : (0x30 : UInt8) ≤ 0x31) h1, h2⟩

private theorem intPart_constituent {bs : Bytes} (h : IntPart bs) :
    ∀ b ∈ bs, NumConstituent b = true := by
  cases h with
  | zero =>
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      decide
  | lead h1 h2 hr =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact isDigit_constituent (by
          simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨UInt8.le_trans (by decide : (0x30 : UInt8) ≤ 0x31) h1, h2⟩)
      · exact digits0_constituent hr b hb

private theorem expPart_constituent {bs : Bytes} (h : ExpPart bs) :
    ∀ b ∈ bs, NumConstituent b = true := by
  cases h with
  | mk he hs hd =>
      intro b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
        or_assoc] at hb
      rcases hb with rfl | hb | hb
      · rcases he with rfl | rfl <;> decide
      · rcases hs with rfl | rfl | rfl
        · simp at hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          subst hb; decide
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          subst hb; decide
      · exact digits_constituent hd b hb

private theorem numBody_constituent {bs : Bytes} (h : NumBody bs) :
    ∀ b ∈ bs, NumConstituent b = true := by
  cases h with
  | plain hi => exact intPart_constituent hi
  | frac hi hf =>
      intro b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
        or_assoc] at hb
      rcases hb with hb | rfl | hb
      · exact intPart_constituent hi b hb
      · decide
      · exact digits_constituent hf b hb
  | exp hi he =>
      intro b hb
      rw [List.mem_append] at hb
      rcases hb with hb | hb
      · exact intPart_constituent hi b hb
      · exact expPart_constituent he b hb
  | fracExp hi hf he =>
      intro b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
        or_assoc] at hb
      rcases hb with hb | rfl | hb | hb
      · exact intPart_constituent hi b hb
      · decide
      · exact digits_constituent hf b hb
      · exact expPart_constituent he b hb

private theorem rfcNumber_constituent {lex : Bytes} (h : RfcNumber lex) :
    ∀ b ∈ lex, NumConstituent b = true := by
  cases h with
  | pos hb => exact numBody_constituent hb
  | neg hb =>
      intro b hbmem
      simp only [List.mem_cons] at hbmem
      rcases hbmem with rfl | hbmem
      · decide
      · exact numBody_constituent hb b hbmem

private theorem numBody_head {bs : Bytes} (h : NumBody bs) :
    ∀ b rest, bs = b :: rest → IsDigitB b = true := by
  cases h with
  | plain hi =>
      intro b rest heq
      exact intPart_head (by rwa [heq] at hi)
  | frac hi hf =>
      intro b rest heq
      cases hi with
      | zero =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]; decide
      | lead h1 h2 hr =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]
          exact intPart_head (.lead h1 h2 hr)
  | exp hi he =>
      intro b rest heq
      cases hi with
      | zero =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]; decide
      | lead h1 h2 hr =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]
          exact intPart_head (.lead h1 h2 hr)
  | fracExp hi hf he =>
      intro b rest heq
      cases hi with
      | zero =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]; decide
      | lead h1 h2 hr =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rw [← heq.1]
          exact intPart_head (.lead h1 h2 hr)

private theorem rfcNumber_head_aux {lex : Bytes} (h : RfcNumber lex) :
    ∀ b rest, lex = b :: rest → IsDigitB b = true ∨ b = 0x2D := by
  cases h with
  | pos hb =>
      intro b rest heq
      exact Or.inl (numBody_head hb b rest heq)
  | neg hb =>
      intro b rest heq
      simp only [List.cons.injEq] at heq
      exact Or.inr (heq.1.symm)

private theorem rfcNumber_head {b : UInt8} {rest : Bytes}
    (h : RfcNumber (b :: rest)) : IsDigitB b = true ∨ b = 0x2D :=
  rfcNumber_head_aux h b rest rfl

/-! #### `numRun` facts -/

private theorem numRun_all (b : Bytes) : ∀ x ∈ numRun b, NumConstituent x = true := by
  induction b with
  | nil => simp [numRun]
  | cons a rest ih =>
      rw [numRun]
      split
      · rename_i ha
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih x hx
      · simp

private theorem length_le_numRun :
    ∀ (b : Bytes) (n : Nat), n ≤ b.length →
      (∀ x ∈ b.take n, NumConstituent x = true) → n ≤ (numRun b).length
  | [], n, hn, _ => by simp at hn; omega
  | a :: t, n, hn, hall => by
      cases n with
      | zero => simp
      | succ m =>
          rw [numRun]
          split
          · rename_i ha
            simp only [List.length_cons]
            have hm : m ≤ t.length := by simpa using hn
            have hmem : ∀ x ∈ t.take m, NumConstituent x = true := by
              intro x hx
              exact hall x (by
                rw [List.take_succ_cons]
                exact List.mem_cons_of_mem a hx)
            have := length_le_numRun t m hm hmem
            omega
          · rename_i ha
            have htrue : NumConstituent a = true := hall a (by
              rw [List.take_succ_cons]
              exact List.mem_cons_self)
            exact absurd htrue ha

private theorem numRun_byte {b : Bytes} {k : Nat} (hk : k < (numRun b).length) :
    ∃ c rest, b.drop k = c :: rest ∧ NumConstituent c = true := by
  have htake := (numRun_spec b).1
  have hlen : (numRun b).length ≤ b.length := numRun_length_le b
  have hklt : k < b.length := Nat.lt_of_lt_of_le hk hlen
  have hget : b[k]? = (numRun b)[k]? := by
    rw [← htake, List.getElem?_take]
    simp [hk]
  have hval : b[k] = (numRun b)[k] := by
    rw [List.getElem?_eq_getElem hklt, List.getElem?_eq_getElem hk] at hget
    injection hget
  refine ⟨b[k], b.drop (k+1), List.drop_eq_getElem_cons hklt, ?_⟩
  rw [hval]
  exact numRun_all b _ (List.getElem_mem hk)

/-! #### Whitespace -/

private theorem spaceRun_eq_of_all {l : Bytes} {n : Nat} {b : UInt8}
    (hall : ∀ k c, k < n → l[k]? = some c → IsSpaceB c = true)
    (hn : l[n]? = some b) (hns : IsSpaceB b = false) :
    spaceRun l = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a t ih =>
      cases n with
      | zero =>
          have ha : IsSpaceB a = false := by
            have h0 : (a :: t)[0]? = some b := hn
            simp only [List.getElem?_cons_zero] at h0
            injection h0 with h0
            rw [h0]; exact hns
          rw [spaceRun]
          simp [ha]
      | succ m =>
          have ha : IsSpaceB a = true := hall 0 a (by omega) rfl
          have htail : ∀ k c, k < m → t[k]? = some c → IsSpaceB c = true := by
            intro k c hk hc
            exact hall (k+1) c (by omega) (by simpa using hc)
          have hnt : t[m]? = some b := by simpa using hn
          have ih' : spaceRun t = m := ih htail hnt
          rw [spaceRun]
          simp only [ha, if_true]
          omega

private theorem skipFrom_eq_of_spaceAt {bs : Bytes} {i j : Nat} {b : UInt8}
    (hsp : SpaceAt bs i j) (hj : bs[j]? = some b) (hns : IsSpaceB b = false) :
    skipFrom bs i = j := by
  obtain ⟨hij, hall⟩ := hsp
  have hspace : ∀ k c, k < j - i → (bs.drop i)[k]? = some c → IsSpaceB c = true := by
    intro k c hk hc
    rw [List.getElem?_drop] at hc
    exact hall (i + k) c (by omega) (by omega) hc
  have hni : (bs.drop i)[j - i]? = some b := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hij]
    exact hj
  have h := spaceRun_eq_of_all hspace hni hns
  unfold skipFrom
  rw [h]
  omega

private theorem isSpace_not_constituent {b : UInt8} (h : IsSpaceB b = true) :
    NumConstituent b = false := by
  simp only [IsSpaceB, Bool.or_eq_true, decide_eq_true_eq, or_assoc] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-! #### Value heads, followers and the string span -/

private theorem valueAt_startB {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) :
    ∃ b, bs[i]? = some b ∧ ValueStartB b = true := by
  cases h with
  | null hp => exact ⟨0x6E, hasPrefix_head hp, by decide⟩
  | true hp => exact ⟨0x74, hasPrefix_head hp, by decide⟩
  | false hp => exact ⟨0x66, hasPrefix_head hp, by decide⟩
  | string hs => exact ⟨0x22, hs.1, by decide⟩
  | array hl _ _ => exact ⟨0x5B, hl, by decide⟩
  | object hl _ _ => exact ⟨0x7B, hl, by decide⟩
  | number hn =>
      obtain ⟨hij, hnum⟩ := hn
      have hne := rfcNumber_nonempty hnum
      have hlen : ((bs.drop i).take (j - i)).length = min (j - i) (bs.length - i) := by
        rw [List.length_take, List.length_drop]
      have hmpos : 0 < min (j - i) (bs.length - i) := by rwa [hlen] at hne
      have hpos : 0 < j - i := by omega
      have hlt : i < bs.length := by omega
      obtain ⟨m, hm⟩ : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
      have hdrop := List.drop_eq_getElem_cons hlt
      have hlex : (bs.drop i).take (j - i) = bs[i] :: ((bs.drop (i + 1)).take m) := by
        rw [hm, hdrop, List.take_succ_cons]
      have hnum' : RfcNumber (bs[i] :: (bs.drop (i + 1)).take m) := by
        rwa [hlex] at hnum
      have hhead : IsDigitB bs[i] = true ∨ bs[i] = 0x2D := rfcNumber_head hnum'
      refine ⟨bs[i], List.getElem?_eq_getElem hlt, ?_⟩
      rcases hhead with h | h
      · simp [ValueStartB, h]
      · simp [ValueStartB, h]

private theorem valueAt_not_space {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) {b : UInt8} (hb : bs[i]? = some b) : IsSpaceB b = false := by
  obtain ⟨b', hb', hstart⟩ := valueAt_startB h
  rw [hb] at hb'
  injection hb' with hb''
  subst hb''
  exact valueStart_not_space hstart

private theorem valueAt_not_bom {m : Strictness} {bs : Bytes} {v : Value} {j : Nat}
    (h : ValueAt m bs 0 v j) (hb : bs[0]? = some 0xEF) : False := by
  obtain ⟨b, hb', hstart⟩ := valueAt_startB h
  rw [hb] at hb'
  injection hb' with hb''
  subst hb''
  rw [valueStart_ne_ef] at hstart
  exact Bool.noConfusion hstart

/-- What can follow a complete value at `j` in an accepted document: end of input,
or whitespace then `,`, `]`, `}`. -/
private def ValueFollow (bs : Bytes) (j : Nat) : Prop :=
  skipFrom bs j = bs.length ∨
  (∃ k, SpaceAt bs j k ∧ bs[k]? = some 0x2C) ∨
  (∃ k, SpaceAt bs j k ∧ bs[k]? = some 0x5D) ∨
  (∃ k, SpaceAt bs j k ∧ bs[k]? = some 0x7D)

private theorem follow_of_spaceAt_comma {bs : Bytes} {j k : Nat} (h : SpaceAt bs j k)
    (hk : bs[k]? = some 0x2C) : ValueFollow bs j := Or.inr (Or.inl ⟨k, h, hk⟩)

private theorem follow_of_spaceAt_closeBracket {bs : Bytes} {j k : Nat} (h : SpaceAt bs j k)
    (hk : bs[k]? = some 0x5D) : ValueFollow bs j :=
  Or.inr (Or.inr (Or.inl ⟨k, h, hk⟩))

private theorem follow_of_spaceAt_closeBrace {bs : Bytes} {j k : Nat} (h : SpaceAt bs j k)
    (hk : bs[k]? = some 0x7D) : ValueFollow bs j :=
  Or.inr (Or.inr (Or.inr ⟨k, h, hk⟩))

private theorem follow_le_length {bs : Bytes} {j : Nat} (h : ValueFollow bs j) :
    j ≤ bs.length := by
  rcases h with h | ⟨k, hsp, hk⟩ | ⟨k, hsp, hk⟩ | ⟨k, hsp, hk⟩
  · rw [← h]; exact skipFrom_ge bs j
  · have hjk : j ≤ k := hsp.1
    have := length_gt_of_get? hk; omega
  · have hjk : j ≤ k := hsp.1
    have := length_gt_of_get? hk; omega
  · have hjk : j ≤ k := hsp.1
    have := length_gt_of_get? hk; omega

private theorem follow_numberStop {bs : Bytes} {j : Nat} (h : ValueFollow bs j) :
    NumberStop bs j := by
  rintro c rest hd
  rcases h with hsf | ⟨k, hsp, hk⟩ | ⟨k, hsp, hk⟩ | ⟨k, hsp, hk⟩
  · have hjlt : j < bs.length := by
      have := congrArg List.length hd
      simp only [List.length_cons] at this
      rw [List.length_drop] at this
      omega
    have hrun : spaceRun (bs.drop j) = bs.length - j := by
      have := hsf
      unfold skipFrom at this
      omega
    rw [hd] at hrun
    rw [spaceRun] at hrun
    split at hrun
    · rename_i hc
      exact isSpace_not_constituent hc
    · omega
  · obtain ⟨hjk, hall⟩ := hsp
    have hjb : bs[j]? = some c := by
      have h := congrArg List.head? hd
      simpa [List.head?_drop] using h
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact isSpace_not_constituent (hall j c (Nat.le_refl _) hlt hjb)
    · have hk_eq : k = j := by omega
      subst hk_eq
      have hc : c = 0x2C := by
        rw [hjb] at hk
        injection hk
      subst hc
      decide
  · obtain ⟨hjk, hall⟩ := hsp
    have hjb : bs[j]? = some c := by
      have h := congrArg List.head? hd
      simpa [List.head?_drop] using h
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact isSpace_not_constituent (hall j c (Nat.le_refl _) hlt hjb)
    · have hk_eq : k = j := by omega
      subst hk_eq
      have hc : c = 0x5D := by
        rw [hjb] at hk
        injection hk
      subst hc
      decide
  · obtain ⟨hjk, hall⟩ := hsp
    have hjb : bs[j]? = some c := by
      have h := congrArg List.head? hd
      simpa [List.head?_drop] using h
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact isSpace_not_constituent (hall j c (Nat.le_refl _) hlt hjb)
    · have hk_eq : k = j := by omega
      subst hk_eq
      have hc : c = 0x7D := by
        rw [hjb] at hk
        injection hk
      subst hc
      decide

/-- A scanned string literal, read against the bytes, is a `StringAt` span. -/
private theorem stringAt_of_scan {bs : Bytes} {i : Nat} {cs : List Nat} {after : Bytes}
    (hb : bs[i]? = some 0x22) (hs : scanChars (bs.drop (i + 1)) = .ok (cs, after)) :
    StringAt .strict bs i (bs.length - after.length) cs := by
  have hstr : StrChars .strict (bs.drop (i + 1)) cs after := (scanChars_iff _ _ _).mp hs
  obtain ⟨pre, hp⟩ := strChars_split hstr
  have hbs : bs = (bs.take (i + 1) ++ pre) ++ after := by
    have h := List.take_append_drop (i + 1) bs
    rw [hp, ← List.append_assoc] at h
    exact h.symm
  exact ⟨hb, after, hstr, drop_of_split hbs⟩

/-! #### Reading back a value's shape from its first byte -/

private theorem numberAt_head {bs : Bytes} {i j : Nat} {b : UInt8}
    (hn : NumberAt bs i j) (hb : bs[i]? = some b) :
    IsDigitB b = true ∨ b = 0x2D := by
  obtain ⟨hij, hnum⟩ := hn
  have hne := rfcNumber_nonempty hnum
  have hlen : ((bs.drop i).take (j - i)).length = min (j - i) (bs.length - i) := by
    rw [List.length_take, List.length_drop]
  have hmpos : 0 < min (j - i) (bs.length - i) := by rwa [hlen] at hne
  have hpos : 0 < j - i := by omega
  obtain ⟨m, hm⟩ : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
  have hlt : i < bs.length := by
    have := List.getElem?_eq_some_iff.mp hb
    omega
  have hdrop := List.drop_eq_getElem_cons hlt
  have hlex : (bs.drop i).take (j - i) = b :: ((bs.drop (i + 1)).take m) := by
    rw [hm, hdrop, List.getElem?_eq_some_iff.mp hb |>.2, List.take_succ_cons]
  have hnum' : RfcNumber (b :: (bs.drop (i + 1)).take m) := by
    rw [hlex] at hnum
    exact hnum
  exact rfcNumber_head hnum'

private theorem valueAt_null_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x6E) :
    v = .null ∧ j = i + 4 ∧ HasPrefix bs i [0x6E, 0x75, 0x6C, 0x6C] := by
  cases h with
  | null hp => exact ⟨rfl, rfl, hp⟩
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      exact absurd (Option.some.inj hq) (by decide)
  | array hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | object hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem valueAt_true_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x74) :
    v = .bool true ∧ j = i + 4 ∧ HasPrefix bs i [0x74, 0x72, 0x75, 0x65] := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | true hp => exact ⟨rfl, rfl, hp⟩
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      exact absurd (Option.some.inj hq) (by decide)
  | array hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | object hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem valueAt_false_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x66) :
    v = .bool false ∧ j = i + 5 ∧ HasPrefix bs i [0x66, 0x61, 0x6C, 0x73, 0x65] := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | false hp => exact ⟨rfl, rfl, hp⟩
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      exact absurd (Option.some.inj hq) (by decide)
  | array hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | object hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem valueAt_string_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x22) :
    ∃ cs, v = .string cs ∧ StringAt m bs i j cs := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | string hs => exact ⟨_, rfl, hs⟩
  | array hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | object hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem valueAt_array_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x5B) :
    ∃ vs k, v = .array vs ∧ ArrBody m bs (skipFrom bs (i + 1)) vs k ∧
      bs[k]? = some 0x5D ∧ j = k + 1 := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      exact absurd (Option.some.inj hq) (by decide)
  | array _ hbody hr => exact ⟨_, _, rfl, hbody, hr, rfl⟩
  | object hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem valueAt_object_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) (hb : bs[i]? = some 0x7B) :
    ∃ ms k, v = .object ms ∧ ObjBody m bs (skipFrom bs (i + 1)) ms k ∧
      bs[k]? = some 0x7D ∧ j = k + 1 := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      exact absurd (Option.some.inj hh) (by decide)
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      exact absurd (Option.some.inj hq) (by decide)
  | array hl _ _ =>
      rw [hb] at hl
      exact absurd (Option.some.inj hl) (by decide)
  | object _ hbody hr => exact ⟨_, _, rfl, hbody, hr, rfl⟩
  | number hn =>
      rcases numberAt_head hn hb with hd | hd
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)

private theorem elems_first_valueAt {m : Strictness} {bs : Bytes} {i : Nat}
    {vs : List Value} {k : Nat} (h : Elems m bs i vs k) :
    ∃ v j, ValueAt m bs i v j := by
  cases h with
  | last hv _ => exact ⟨_, _, hv⟩
  | cons hv _ _ _ _ => exact ⟨_, _, hv⟩

private theorem elems_first_valueAt_follow {m : Strictness} {bs : Bytes} {i : Nat}
    {vs : List Value} {k : Nat} (h : Elems m bs i vs k)
    (hk : bs[k]? = some 0x5D) :
    ∃ v j, ValueAt m bs i v j ∧ ValueFollow bs j := by
  cases h with
  | last hv hw => exact ⟨_, _, hv, follow_of_spaceAt_closeBracket hw hk⟩
  | cons hv hw1 hc hw2 hr => exact ⟨_, _, hv, follow_of_spaceAt_comma hw1 hc⟩

private theorem parseElemsTail_done_of_not_comma {bs : Bytes} {i depth : Nat}
    (h : bs[skipFrom bs i]? ≠ some 0x2C) :
    ∃ t : ArrayTail i, parseElemsTail bs i depth = .done t := by
  rw [parseElemsTail.eq_def]
  split
  all_goals
    first
    | exact absurd ‹bs[skipFrom bs i]? = some 44› h
    | exact ⟨_, rfl⟩

private theorem parseMembersTail_done_of_not_comma {bs : Bytes} {i depth : Nat}
    (h : bs[skipFrom bs i]? ≠ some 0x2C) :
    ∃ t : ObjectTail i, parseMembersTail bs i depth = .done t := by
  rw [parseMembersTail.eq_def]
  split
  all_goals
    first
    | exact absurd ‹bs[skipFrom bs i]? = some 44› h
    | exact ⟨_, rfl⟩

private def DecodesValue (bs : Bytes) (i : Nat) (toks : List Token) (v : Value) (next : Nat) : Prop :=
  ∀ rest : List Token, ∃ d : Decoded (toks ++ rest),
    decodeValue bs i (toks ++ rest) = some d ∧
    d.value = v ∧ d.rest = rest ∧ d.cursor = next

private def NoCommaHead : List Token → Prop
  | .punct .comma _ :: _ => False
  | _ => True

private def DecodesElems (bs : Bytes) (j : Nat) (toks : List Token) (vs : List Value) (next : Nat) : Prop :=
  ∀ rest : List Token, NoCommaHead rest → ∃ t : ElemsTail (toks ++ rest),
    decodeElemsTail bs j (toks ++ rest) = some t ∧
    t.values = vs ∧ t.rest = rest ∧ t.cursor = next

private def DecodesMembers (bs : Bytes) (j : Nat) (toks : List Token)
    (ms : List (List Nat × Value)) (next : Nat) : Prop :=
  ∀ rest : List Token, NoCommaHead rest → ∃ t : MembersTail (toks ++ rest),
    decodeMembersTail bs j (toks ++ rest) = some t ∧
    t.members = ms ∧ t.rest = rest ∧ t.cursor = next

private theorem noCommaHead_closeBracket {s : Span} {rest : List Token} :
    NoCommaHead (.punct .closeBracket s :: rest) := by simp [NoCommaHead]

private theorem noCommaHead_closeBrace {s : Span} {rest : List Token} :
    NoCommaHead (.punct .closeBrace s :: rest) := by simp [NoCommaHead]

private def ElemsTailSpec (bs : Bytes) (j : Nat) (toks : List Token) (vs : List Value)
    (next : Nat) : Prop :=
  (vs = [] ∧ toks = [] ∧ next = skipFrom bs j) ∨
  (bs[skipFrom bs j]? = some 0x2C ∧
    Elems .strict bs (skipFrom bs (skipFrom bs j + 1)) vs next)

private def MembersTailSpec (bs : Bytes) (j : Nat) (toks : List Token)
    (ms : List (List Nat × Value)) (next : Nat) : Prop :=
  (ms = [] ∧ toks = [] ∧ next = skipFrom bs j) ∨
  (bs[skipFrom bs j]? = some 0x2C ∧
    Members .strict bs (skipFrom bs (skipFrom bs j + 1)) ms next)

/-- The possible ends a tail's grammar continuation can have: no elements (so the
end is the skip), or a comma and some remaining elements.  The list itself is
existential: the parser's tail agreement only needs the end. -/
private theorem decodeValue_some_head_ne_close {bs : Bytes} {i : Nat}
    {toks : List Token} {d : Decoded toks} (h : decodeValue bs i toks = some d) :
    ∀ (s : Span) (rest : List Token), toks ≠ .punct .closeBracket s :: rest := by
  intro s rest heq
  cases heq
  simp [decodeValue] at h

private theorem decodeValue_cast {bs : Bytes} {i : Nat} {l1 l2 : List Token}
    (he : l1 = l2) {d : Decoded l1} (h : decodeValue bs i l1 = some d) :
    ∃ d' : Decoded l2, decodeValue bs i l2 = some d' ∧ d'.value = d.value ∧
      d'.rest = d.rest ∧ d'.cursor = d.cursor := by
  cases he
  exact ⟨d, h, rfl, rfl, rfl⟩

private theorem decodeValue_array_of {bs : Bytes} {i first : Nat}
    {pvToks : List Token} {pvV : Value} {pvNext : Nat}
    {tToks : List Token} {tVals : List Value} {tNext : Nat}
    (hfirst : first = skipFrom bs (i + 1)) (hb : bs[i]? = some 0x5B)
    (hne : pvToks ≠ [])
    (hnotclose : ∀ (s : Span) (r : List Token), pvToks ≠ .punct .closeBracket s :: r)
    (hdecv : DecodesValue bs first pvToks pvV pvNext)
    (hdecT : DecodesElems bs pvNext tToks tVals tNext)
    (hclose : bs[tNext]? = some 0x5D) :
    DecodesValue bs i
      (Token.punct .openBracket ⟨i, i + 1⟩ ::
        (pvToks ++ (tToks ++ [Token.punct .closeBracket ⟨tNext, tNext + 1⟩])))
      (.array (pvV :: tVals)) (tNext + 1) := by
  intro rest
  obtain ⟨d, hd, hdv, hdr, hdc⟩ :=
    hdecv (tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest))
  obtain ⟨t', ht, htv, htr, htc⟩ :=
    hdecT (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest)
      noCommaHead_closeBracket
  obtain ⟨dval, drest, dcursor, dshrunk⟩ := d
  obtain ⟨tvals, trest, tcursor, tmoved⟩ := t'
  have hdv' : dval = pvV := by simpa using hdv
  have hdr' : drest = tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest) := by
    simpa using hdr
  have hdc' : dcursor = pvNext := by simpa using hdc
  have htv' : tvals = tVals := by simpa using htv
  have htr' : trest = Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest := by
    simpa using htr
  have htc' : tcursor = tNext := by simpa using htc
  have hd1 : decodeValue bs first
      (pvToks ++ (tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest))) =
      some { value := pvV, rest := tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest),
             cursor := pvNext, shrunk := by simpa [hdr'] using dshrunk } := by
    simpa [hdv', hdr', hdc'] using hd
  have ht1 : decodeElemsTail bs pvNext
      (tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest)) =
      some { values := tVals, rest := Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest,
             cursor := tNext, moved := by simpa [htr'] using tmoved } := by
    simpa [htv', htr', htc'] using ht
  have hdR : decodeValue bs i
      (Token.punct .openBracket ⟨i, i + 1⟩ ::
        (pvToks ++ (tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest))))
      = some { value := .array (pvV :: tVals), rest := rest, cursor := tNext + 1,
               shrunk := by simp only [List.length_append, List.length_cons]; omega } := by
    cases pvToks with
    | nil => exact absurd rfl hne
    | cons tok toks =>
        cases tok <;> (try (cases ‹Punct›))
        all_goals
          first
          | exact absurd rfl (hnotclose _ toks)
          | (rw [decodeValue.eq_def]
             simp only [List.cons_append, List.nil_append, hfirst.symm, hb,
               decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, decide_true, if_true]
             simp only [List.cons_append] at hd1
             rw [hd1]
             dsimp only
             rw [ht1]
             simp [hclose])
  have he : ((Token.punct .openBracket ⟨i, i + 1⟩ ::
        (pvToks ++ (tToks ++ [Token.punct .closeBracket ⟨tNext, tNext + 1⟩]))) ++ rest)
      = (Token.punct .openBracket ⟨i, i + 1⟩ ::
        (pvToks ++ (tToks ++ (Token.punct .closeBracket ⟨tNext, tNext + 1⟩ :: rest)))) := by
    simp [List.append_assoc, List.singleton_append]
  obtain ⟨d', hd', hdv', hdr', hdc'⟩ := decodeValue_cast he.symm hdR
  exact ⟨d', hd', hdv', hdr', hdc'⟩


private theorem parseKey_sound {bs : Bytes} {i : Nat} {k : Key i}
    (hk : parseKey bs i = .done k) :
    bs[i]? = some 0x22 ∧ StringAt .strict bs i k.next k.name ∧
    k.token = .string ⟨i, k.next⟩ ∧
    ∀ rest : List Token,
      decodeValue bs i (k.token :: rest) = some
        { value := .string k.name, rest := rest, cursor := k.next,
          shrunk := by simp } := by
  unfold parseKey at hk
  split at hk
  · rename_i hb
    split at hk
    · cases hk
    · rename_i cs after hs
      cases hk
      refine ⟨hb, stringAt_of_scan hb hs, rfl, ?_⟩
      intro rest
      simp [decodeValue, hs, hb]
  · cases hk

private theorem parseKey_reject {bs : Bytes} {i : Nat} {r : Reject}
    (hk : parseKey bs i = .fail (.invalid r)) :
    ¬ ∃ (cs : List Nat) (j : Nat), StringAt .strict bs i j cs := by
  unfold parseKey at hk
  split at hk
  · rename_i hb
    split at hk
    · rename_i hs
      rintro ⟨cs, j, hsAt⟩
      obtain ⟨-, rest, hstr, -⟩ := hsAt
      have := (scanChars_iff (bs.drop (i + 1)) cs rest).mpr hstr
      rw [hs] at this
      cases this
    · cases hk
  · rename_i hb
    rintro ⟨cs, j, hsAt⟩
    exact hb hsAt.1

private theorem members_first_stringAt {m : Strictness} {bs : Bytes} {i : Nat}
    {ms : List (List Nat × Value)} {k : Nat} (h : Members m bs i ms k) :
    ∃ (cs : List Nat) (j : Nat), StringAt m bs i j cs := by
  cases h with
  | last hm _ =>
      cases hm with
      | mk hk _ _ _ _ => exact ⟨_, _, hk⟩
  | cons hm _ _ _ _ =>
      cases hm with
      | mk hk _ _ _ _ => exact ⟨_, _, hk⟩

private theorem parseKey_next_le {bs : Bytes} {i : Nat} {k : Key i}
    (hk : parseKey bs i = .done k) : k.next ≤ bs.length := by
  unfold parseKey at hk
  split at hk
  · rename_i hb
    split at hk
    · cases hk
    · rename_i cs after hs
      cases hk
      change bs.length - after.length ≤ bs.length
      have hstr := (scanChars_iff _ _ _).mp hs
      have := strChars_suffix_lt hstr
      simp only [List.length_drop] at this
      omega
  · cases hk

private theorem stringAt_end_unique {bs : Bytes} {i j1 j2 : Nat}
    {cs1 cs2 : List Nat} (h1 : StringAt .strict bs i j1 cs1) (h2 : StringAt .strict bs i j2 cs2)
    (hj1 : j1 ≤ bs.length) (hj2 : j2 ≤ bs.length) : j1 = j2 := by
  obtain ⟨-, r1, hstr1, hdrop1⟩ := h1
  obtain ⟨-, r2, hstr2, hdrop2⟩ := h2
  have hs1 := (scanChars_iff (bs.drop (i + 1)) cs1 r1).mpr hstr1
  have hs2 := (scanChars_iff (bs.drop (i + 1)) cs2 r2).mpr hstr2
  rw [hs1] at hs2
  injection hs2 with heq
  have hr : r1 = r2 := by injection heq
  have hl1 : bs.length - j1 = r1.length := by
    have := congrArg List.length hdrop1
    rwa [List.length_drop] at this
  have hl2 : bs.length - j2 = r2.length := by
    have := congrArg List.length hdrop2
    rwa [List.length_drop] at this
  rw [hr] at hl1
  omega

private def ElemsTailEnd (bs : Bytes) (j : Nat) (k : Nat) : Prop :=
  k = skipFrom bs j ∨
  (bs[skipFrom bs j]? = some 0x2C ∧
    ∃ vs, Elems .strict bs (skipFrom bs (skipFrom bs j + 1)) vs k)

private def MembersTailEnd (bs : Bytes) (j : Nat) (k : Nat) : Prop :=
  k = skipFrom bs j ∨
  (bs[skipFrom bs j]? = some 0x2C ∧
    ∃ ms, Members .strict bs (skipFrom bs (skipFrom bs j + 1)) ms k)

private def ElemsCont (bs : Bytes) (j : Nat) : Prop :=
  bs[skipFrom bs j]? = some 0x2C ∧
    ∃ vs k, Elems .strict bs (skipFrom bs (skipFrom bs j + 1)) vs k ∧
      bs[k]? = some 0x5D

private def MembersCont (bs : Bytes) (j : Nat) : Prop :=
  bs[skipFrom bs j]? = some 0x2C ∧
    ∃ ms k, Members .strict bs (skipFrom bs (skipFrom bs j + 1)) ms k ∧
      bs[k]? = some 0x7D

private theorem elems_tail_end {bs : Bytes} {i pvNext k : Nat}
    {vs : List Value} (he : Elems .strict bs i vs k) (hk : bs[k]? = some 0x5D)
    (hagree : ∀ (v : Value) (j : Nat), ValueAt .strict bs i v j → ValueFollow bs j → j = pvNext) :
    ElemsTailEnd bs pvNext k := by
  cases he with
  | last hv1 hw =>
      have hf : ValueFollow bs _ := follow_of_spaceAt_closeBracket hw hk
      have hj : _ = pvNext := hagree _ _ hv1 hf
      have hskip := skipFrom_eq_of_spaceAt hw hk (by decide)
      rw [hj] at hskip
      exact Or.inl hskip.symm
  | cons hv1 hw1 hc hw2 hr =>
      have hf : ValueFollow bs _ := follow_of_spaceAt_comma hw1 hc
      have hj : _ = pvNext := hagree _ _ hv1 hf
      have hskip := skipFrom_eq_of_spaceAt hw1 hc (by decide)
      rw [hj] at hskip
      rw [← hskip] at hc
      obtain ⟨v3, j3, hv3⟩ := elems_first_valueAt hr
      obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv3
      have hskip2 := skipFrom_eq_of_spaceAt hw2 hb3 (valueStart_not_space hstart3)
      rw [← hskip] at hskip2
      rw [← hskip2] at hr
      exact Or.inr ⟨hc, ⟨_, hr⟩⟩

/-- The single-member case of the object tail-end description, with the
grammar's indices explicit so their positions can be pinned. -/
private theorem member_tail_end_last {bs : Bytes}
    {first kNext j1 j2 j3 j4 k pvNext : Nat} {nm : List Nat} {vv : Value}
    (hkStr : StringAt .strict bs first j1 nm)
    (hkeyAt : ∃ cs : List Nat, StringAt .strict bs first kNext cs)
    (hkle : kNext ≤ bs.length)
    (hwkey : SpaceAt bs j1 j2) (hcol : bs[j2]? = some 0x3A)
    (hwval : SpaceAt bs (j2 + 1) j3) (hv : ValueAt .strict bs j3 vv j4)
    (hw : SpaceAt bs j4 k) (hk : bs[k]? = some 0x7D)
    (hagree : ∀ (v : Value) (j : Nat),
      ValueAt .strict bs (skipFrom bs (skipFrom bs kNext + 1)) v j →
      ValueFollow bs j → j = pvNext) :
    MembersTailEnd bs pvNext k := by
  have hcolLt := length_gt_of_get? hcol
  have hjk1 := hwkey.1
  obtain ⟨csAt, hcsAt⟩ := hkeyAt
  have hj1 : j1 = kNext := stringAt_end_unique hkStr hcsAt (by omega) hkle
  rw [hj1] at hwkey
  have hskip : skipFrom bs kNext = j2 := skipFrom_eq_of_spaceAt hwkey hcol (by decide)
  obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv
  have hskip2 : skipFrom bs (skipFrom bs kNext + 1) = j3 := by
    rw [hskip]
    exact skipFrom_eq_of_spaceAt hwval hb3 (valueStart_not_space hstart3)
  have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs kNext + 1)) vv j4 := by
    rw [hskip2]; exact hv
  have hf : ValueFollow bs j4 := follow_of_spaceAt_closeBrace hw hk
  have hj : j4 = pvNext := hagree vv j4 hval hf
  have hskipk : skipFrom bs j4 = k := skipFrom_eq_of_spaceAt hw hk (by decide)
  rw [hj] at hskipk
  exact Or.inl hskipk.symm

/-- The multi-member case of the object tail-end description. -/
private theorem member_tail_end_cons {bs : Bytes}
    {first kNext j1 j2 j3 j4 jc1 jc2 jrest pvNext : Nat}
    {nm : List Nat} {vv : Value} {rest : List (List Nat × Value)}
    (hkStr : StringAt .strict bs first j1 nm)
    (hkeyAt : ∃ cs : List Nat, StringAt .strict bs first kNext cs)
    (hkle : kNext ≤ bs.length)
    (hwkey : SpaceAt bs j1 j2) (hcol : bs[j2]? = some 0x3A)
    (hwval : SpaceAt bs (j2 + 1) j3) (hv : ValueAt .strict bs j3 vv j4)
    (hwcomma : SpaceAt bs j4 jc1) (hc : bs[jc1]? = some 0x2C)
    (hw2 : SpaceAt bs (jc1 + 1) jc2)
    (hr : Members .strict bs jc2 rest jrest)
    (hagree : ∀ (v : Value) (j : Nat),
      ValueAt .strict bs (skipFrom bs (skipFrom bs kNext + 1)) v j →
      ValueFollow bs j → j = pvNext) :
    MembersTailEnd bs pvNext jrest := by
  have hcolLt := length_gt_of_get? hcol
  have hjk1 := hwkey.1
  obtain ⟨csAt, hcsAt⟩ := hkeyAt
  have hj1 : j1 = kNext := stringAt_end_unique hkStr hcsAt (by omega) hkle
  rw [hj1] at hwkey
  have hskip : skipFrom bs kNext = j2 := skipFrom_eq_of_spaceAt hwkey hcol (by decide)
  obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv
  have hskip2 : skipFrom bs (skipFrom bs kNext + 1) = j3 := by
    rw [hskip]
    exact skipFrom_eq_of_spaceAt hwval hb3 (valueStart_not_space hstart3)
  have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs kNext + 1)) vv j4 := by
    rw [hskip2]; exact hv
  have hf : ValueFollow bs j4 := follow_of_spaceAt_comma hwcomma hc
  have hj : j4 = pvNext := hagree vv j4 hval hf
  have hskipc : skipFrom bs j4 = jc1 := skipFrom_eq_of_spaceAt hwcomma hc (by decide)
  rw [hj] at hskipc
  have hc' : bs[skipFrom bs pvNext]? = some 0x2C := by rw [hskipc]; exact hc
  obtain ⟨cs3, j3', hs3⟩ := members_first_stringAt hr
  have hskip3 : skipFrom bs (skipFrom bs pvNext + 1) = jc2 := by
    rw [hskipc]
    exact skipFrom_eq_of_spaceAt hw2 hs3.1 (by decide)
  have hr' : Members .strict bs (skipFrom bs (skipFrom bs pvNext + 1)) rest jrest := by
    rw [hskip3]; exact hr
  exact Or.inr ⟨hc', ⟨_, hr'⟩⟩

/-- The object analogue of `elems_tail_end`: a nonempty member list's first
member is the one the parser consumed, so the continuation the tail will see is
determined by that member's value end. -/
private theorem members_tail_end {bs : Bytes} {first kNext pvNext k : Nat}
    {nm : List Nat} {vv : Value} {ms : List (List Nat × Value)}
    (hm : Members .strict bs first ((nm, vv) :: ms) k)
    (hk : bs[k]? = some 0x7D)
    (hkeyAt : ∃ cs : List Nat, StringAt .strict bs first kNext cs)
    (hkle : kNext ≤ bs.length)
    (hbcolon : bs[skipFrom bs kNext]? = some 0x3A)
    (hagree : ∀ (v : Value) (j : Nat),
      ValueAt .strict bs (skipFrom bs (skipFrom bs kNext + 1)) v j →
      ValueFollow bs j → j = pvNext) :
    MembersTailEnd bs pvNext k := by
  cases hm with
  | last hme hw =>
      cases hme with
      | mk hkStr hwkey hcol hwval hv =>
          exact member_tail_end_last hkStr hkeyAt hkle hwkey hcol hwval hv hw hk hagree
  | cons hme hwcomma hc hw2 hr =>
      cases hme with
      | mk hkStr hwkey hcol hwval hv =>
          exact member_tail_end_cons hkStr hkeyAt hkle hwkey hcol hwval hv
            hwcomma hc hw2 hr hagree

/-- Transport a decoded element tail across an equality of token lists. -/
private theorem decodeElemsTail_cast {bs : Bytes} {j : Nat} {l1 l2 : List Token}
    (he : l1 = l2) {t : ElemsTail l1} (h : decodeElemsTail bs j l1 = some t) :
    ∃ t' : ElemsTail l2, decodeElemsTail bs j l2 = some t' ∧ t'.values = t.values ∧
      t'.rest = t.rest ∧ t'.cursor = t.cursor := by
  cases he
  exact ⟨t, h, rfl, rfl, rfl⟩

/-- Transport a decoded member tail across an equality of token lists. -/
private theorem decodeMembersTail_cast {bs : Bytes} {j : Nat} {l1 l2 : List Token}
    (he : l1 = l2) {t : MembersTail l1} (h : decodeMembersTail bs j l1 = some t) :
    ∃ t' : MembersTail l2, decodeMembersTail bs j l2 = some t' ∧ t'.members = t.members ∧
      t'.rest = t.rest ∧ t'.cursor = t.cursor := by
  cases he
  exact ⟨t, h, rfl, rfl, rfl⟩

/-- Compose a parsed comma-separated element list into the decoder's element
tail. -/
private theorem decodeElemsTail_of {bs : Bytes} {j c first : Nat}
    {pvToks : List Token} {pvV : Value} {pvNext : Nat}
    {tToks : List Token} {tVals : List Value} {tNext : Nat}
    (hc : c = skipFrom bs j) (hbcomma : bs[c]? = some 0x2C)
    (hfirst : first = skipFrom bs (c + 1))
    (hdecv : DecodesValue bs first pvToks pvV pvNext)
    (hdecT : DecodesElems bs pvNext tToks tVals tNext) :
    DecodesElems bs j
      (Token.punct .comma ⟨c, c + 1⟩ :: (pvToks ++ tToks)) (pvV :: tVals) tNext := by
  intro rest hnc
  obtain ⟨d, hd, hdv, hdr, hdc⟩ := hdecv (tToks ++ rest)
  obtain ⟨t', ht, htv, htr, htc⟩ := hdecT rest hnc
  obtain ⟨dval, drest, dcursor, dshrunk⟩ := d
  obtain ⟨tvals, trest, tcursor, tmoved⟩ := t'
  have hdv' : dval = pvV := by simpa using hdv
  have hdr' : drest = tToks ++ rest := by simpa using hdr
  have hdc' : dcursor = pvNext := by simpa using hdc
  have htv' : tvals = tVals := by simpa using htv
  have htr' : trest = rest := by simpa using htr
  have htc' : tcursor = tNext := by simpa using htc
  have hv1 : decodeValue bs first (pvToks ++ (tToks ++ rest)) =
      some { value := pvV, rest := tToks ++ rest, cursor := pvNext,
             shrunk := by simpa [hdr'] using dshrunk } := by
    simpa [hdv', hdr', hdc'] using hd
  have ht1 : decodeElemsTail bs pvNext (tToks ++ rest) =
      some { values := tVals, rest := rest, cursor := tNext,
             moved := by simpa [htr'] using tmoved } := by
    simpa [htv', htr', htc'] using ht
  have hdR : decodeElemsTail bs j
      (Token.punct .comma ⟨c, c + 1⟩ :: (pvToks ++ (tToks ++ rest))) =
      some { values := pvV :: tVals, rest := rest, cursor := tNext,
             moved := (by
               simp only [List.length_append, List.length_cons]
               have h1 := dshrunk
               have h2 := tmoved
               omega) } := by
    rw [decodeElemsTail.eq_def]
    simp only [← hc, hbcomma, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      decide_true, if_true]
    rw [show skipFrom bs (c + 1) = first from hfirst.symm, hv1]
    dsimp only
    rw [ht1]
    rfl
  have he : (Token.punct .comma ⟨c, c + 1⟩ :: (pvToks ++ tToks)) ++ rest
      = Token.punct .comma ⟨c, c + 1⟩ :: (pvToks ++ (tToks ++ rest)) := by
    simp [List.append_assoc]
  obtain ⟨t'', ht'', htv'', htr'', htc''⟩ := decodeElemsTail_cast he.symm hdR
  exact ⟨t'', ht'', htv'', htr'', htc''⟩

/-- Compose a parsed member into the decoder's member tail. -/
private theorem decodeMembersTail_of {bs : Bytes} {j c first colon : Nat}
    {cs : List Nat} {kNext : Nat}
    {pvToks : List Token} {pvV : Value} {pvNext : Nat}
    {tToks : List Token} {tMs : List (List Nat × Value)} {tNext : Nat}
    (hc : c = skipFrom bs j) (hbcomma : bs[c]? = some 0x2C)
    (hfirst : first = skipFrom bs (c + 1))
    (hkey : ∀ rest : List Token,
      decodeValue bs first (Token.string ⟨first, kNext⟩ :: rest) =
        some { value := .string cs, rest := rest, cursor := kNext, shrunk := by simp })
    (hcolonEq : colon = skipFrom bs kNext)
    (hbcolon : bs[colon]? = some 0x3A)
    (hdecv : DecodesValue bs (skipFrom bs (colon + 1)) pvToks pvV pvNext)
    (hdecT : DecodesMembers bs pvNext tToks tMs tNext) :
    DecodesMembers bs j
      (Token.punct .comma ⟨c, c + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          ([Token.punct .colon ⟨colon, colon + 1⟩] ++ (pvToks ++ tToks))))
      ((cs, pvV) :: tMs) tNext := by
  intro rest hnc
  obtain ⟨d, hd, hdv, hdr, hdc⟩ := hdecv (tToks ++ rest)
  obtain ⟨t', ht, htv, htr, htc⟩ := hdecT rest hnc
  obtain ⟨dval, drest, dcursor, dshrunk⟩ := d
  obtain ⟨tms, trest, tcursor, tmoved⟩ := t'
  have hdv' : dval = pvV := by simpa using hdv
  have hdr' : drest = tToks ++ rest := by simpa using hdr
  have hdc' : dcursor = pvNext := by simpa using hdc
  have htv' : tms = tMs := by simpa using htv
  have htr' : trest = rest := by simpa using htr
  have htc' : tcursor = tNext := by simpa using htc
  have hk1 : decodeValue bs first
      (Token.string ⟨first, kNext⟩ ::
        (Token.punct .colon ⟨colon, colon + 1⟩ ::
          (pvToks ++ (tToks ++ rest)))) =
      some { value := .string cs,
             rest := Token.punct .colon ⟨colon, colon + 1⟩ ::
               (pvToks ++ (tToks ++ rest)),
             cursor := kNext, shrunk := by simp } := by
    simpa using hkey (Token.punct .colon ⟨colon, colon + 1⟩ :: (pvToks ++ (tToks ++ rest)))
  have hv1 : decodeValue bs (skipFrom bs (colon + 1)) (pvToks ++ (tToks ++ rest)) =
      some { value := pvV, rest := tToks ++ rest, cursor := pvNext,
             shrunk := by simpa [hdr'] using dshrunk } := by
    simpa [hdv', hdr', hdc'] using hd
  have ht1 : decodeMembersTail bs pvNext (tToks ++ rest) =
      some { members := tMs, rest := rest, cursor := tNext,
             moved := by simpa [htr'] using tmoved } := by
    simpa [htv', htr', htc'] using ht
  have hdR : decodeMembersTail bs j
      (Token.punct .comma ⟨c, c + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          (Token.punct .colon ⟨colon, colon + 1⟩ ::
            (pvToks ++ (tToks ++ rest))))) =
      some { members := (cs, pvV) :: tMs, rest := rest, cursor := tNext,
             moved := (by
               simp only [List.length_append, List.length_cons]
               have h1 := dshrunk
               have h2 := tmoved
               omega) } := by
    rw [decodeMembersTail.eq_def]
    simp only [← hc, hbcomma, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      decide_true, if_true]
    rw [show skipFrom bs (c + 1) = first from hfirst.symm, hk1]
    dsimp only
    rw [← hcolonEq]
    simp only [hbcolon, decide_true, if_true]
    rw [hv1]
    dsimp only
    rw [ht1]
    rfl
  have he : (Token.punct .comma ⟨c, c + 1⟩ ::
          (Token.string ⟨first, kNext⟩ ::
            ([Token.punct .colon ⟨colon, colon + 1⟩] ++ (pvToks ++ tToks)))) ++ rest
      = Token.punct .comma ⟨c, c + 1⟩ ::
          (Token.string ⟨first, kNext⟩ ::
            (Token.punct .colon ⟨colon, colon + 1⟩ ::
              (pvToks ++ (tToks ++ rest)))) := by
    simp [List.append_assoc, List.singleton_append]
  obtain ⟨t'', ht'', htv'', htr'', htc''⟩ := decodeMembersTail_cast he.symm hdR
  exact ⟨t'', ht'', htv'', htr'', htc''⟩

/-- Compose a parsed member's key, colon, value and tail into the decoder's
object branch. -/
private theorem decodeValue_object_of {bs : Bytes} {i first colon : Nat}
    {cs : List Nat} {kNext : Nat}
    {pvToks : List Token} {pvV : Value} {pvNext : Nat}
    {tToks : List Token} {tMs : List (List Nat × Value)} {tNext : Nat}
    (hfirst : first = skipFrom bs (i + 1)) (hb : bs[i]? = some 0x7B)
    (hkey : ∀ rest : List Token,
      decodeValue bs first (Token.string ⟨first, kNext⟩ :: rest) =
        some { value := .string cs, rest := rest, cursor := kNext, shrunk := by simp })
    (hcolonEq : colon = skipFrom bs kNext)
    (hbcolon : bs[colon]? = some 0x3A)
    (hdecv : DecodesValue bs (skipFrom bs (colon + 1)) pvToks pvV pvNext)
    (hdecT : DecodesMembers bs pvNext tToks tMs tNext)
    (hclose : bs[tNext]? = some 0x7D) :
    DecodesValue bs i
      (Token.punct .openBrace ⟨i, i + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          ([Token.punct .colon ⟨colon, colon + 1⟩] ++
            (pvToks ++ (tToks ++ [Token.punct .closeBrace ⟨tNext, tNext + 1⟩])))))
      (.object ((cs, pvV) :: tMs)) (tNext + 1) := by
  intro rest
  obtain ⟨d, hd, hdv, hdr, hdc⟩ :=
    hdecv (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest))
  obtain ⟨t', ht, htv, htr, htc⟩ :=
    hdecT (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest) noCommaHead_closeBrace
  obtain ⟨dval, drest, dcursor, dshrunk⟩ := d
  obtain ⟨tms, trest, tcursor, tmoved⟩ := t'
  have hdv' : dval = pvV := by simpa using hdv
  have hdr' : drest = tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest) := by
    simpa using hdr
  have hdc' : dcursor = pvNext := by simpa using hdc
  have htv' : tms = tMs := by simpa using htv
  have htr' : trest = Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest := by simpa using htr
  have htc' : tcursor = tNext := by simpa using htc
  have hk1 : decodeValue bs first
      (Token.string ⟨first, kNext⟩ ::
        (Token.punct .colon ⟨colon, colon + 1⟩ ::
          (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest))))) =
      some { value := .string cs,
             rest := Token.punct .colon ⟨colon, colon + 1⟩ ::
               (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest))),
             cursor := kNext, shrunk := by simp } := by
    simpa using hkey (Token.punct .colon ⟨colon, colon + 1⟩ ::
      (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest))))
  have hv1 : decodeValue bs (skipFrom bs (colon + 1))
      (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest))) =
      some { value := pvV,
             rest := tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest),
             cursor := pvNext, shrunk := by simpa [hdr'] using dshrunk } := by
    simpa [hdv', hdr', hdc'] using hd
  have ht1 : decodeMembersTail bs pvNext
      (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest)) =
      some { members := tMs,
             rest := Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest,
             cursor := tNext, moved := by simpa [htr'] using tmoved } := by
    simpa [htv', htr', htc'] using ht
  have hdR : decodeValue bs i
      (Token.punct .openBrace ⟨i, i + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          (Token.punct .colon ⟨colon, colon + 1⟩ ::
            (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest)))))) =
      some { value := .object ((cs, pvV) :: tMs), rest := rest, cursor := tNext + 1,
             shrunk := by simp only [List.length_append, List.length_cons]; omega } := by
    rw [decodeValue.eq_def]
    simp only [hfirst.symm, hb, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      decide_true, if_true]
    rw [hk1]
    dsimp only
    rw [← hcolonEq]
    simp only [hbcolon, decide_true, if_true]
    rw [hv1]
    dsimp only
    rw [ht1]
    dsimp only
    simp [hclose]
  have he : ((Token.punct .openBrace ⟨i, i + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          ([Token.punct .colon ⟨colon, colon + 1⟩] ++
            (pvToks ++ (tToks ++ [Token.punct .closeBrace ⟨tNext, tNext + 1⟩]))))) ++ rest)
      = (Token.punct .openBrace ⟨i, i + 1⟩ ::
        (Token.string ⟨first, kNext⟩ ::
          (Token.punct .colon ⟨colon, colon + 1⟩ ::
            (pvToks ++ (tToks ++ (Token.punct .closeBrace ⟨tNext, tNext + 1⟩ :: rest)))))) := by
    simp [List.append_assoc, List.singleton_append]
  obtain ⟨d', hd', hdv', hdr', hdc'⟩ := decodeValue_cast he.symm hdR
  exact ⟨d', hd', hdv', hdr', hdc'⟩

/-- The decoder equation for a `null` token. -/
private theorem decodeValue_null_of {bs : Bytes} {i : Nat}
    (hlit : HasPrefixB bs i [0x6E, 0x75, 0x6C, 0x6C] = true) :
    DecodesValue bs i [Token.null ⟨i, i + 4⟩] .null (i + 4) := by
  intro rest
  refine ⟨{ value := .null, rest := rest, cursor := i + 4, shrunk := by simp }, ?_, rfl, rfl, rfl⟩
  simp [decodeValue, hlit]

/-- The decoder equation for a `true` token. -/
private theorem decodeValue_true_of {bs : Bytes} {i : Nat}
    (hlit : HasPrefixB bs i [0x74, 0x72, 0x75, 0x65] = true) :
    DecodesValue bs i [Token.bool true ⟨i, i + 4⟩] (.bool true) (i + 4) := by
  intro rest
  refine ⟨{ value := .bool true, rest := rest, cursor := i + 4, shrunk := by simp }, ?_, rfl, rfl, rfl⟩
  simp [decodeValue, hlit]

/-- The decoder equation for a `false` token. -/
private theorem decodeValue_false_of {bs : Bytes} {i : Nat}
    (hlit : HasPrefixB bs i [0x66, 0x61, 0x6C, 0x73, 0x65] = true) :
    DecodesValue bs i [Token.bool false ⟨i, i + 5⟩] (.bool false) (i + 5) := by
  intro rest
  refine ⟨{ value := .bool false, rest := rest, cursor := i + 5, shrunk := by simp }, ?_, rfl, rfl, rfl⟩
  simp [decodeValue, hlit]

/-- The decoder equation for a number token whose lexeme is the maximal run. -/
private theorem decodeValue_number_of {bs : Bytes} {i : Nat} {lex : Bytes}
    (hlex : lex = numRun (bs.drop i)) (hnum : numLexB lex = true) :
    DecodesValue bs i [Token.number ⟨i, i + lex.length⟩] (.number lex) (i + lex.length) := by
  intro rest
  subst hlex
  refine ⟨{ value := .number (numRun (bs.drop i)), rest := rest,
            cursor := i + (numRun (bs.drop i)).length, shrunk := by simp }, ?_, rfl, rfl, rfl⟩
  simp [decodeValue, hnum]

/-- A value whose head byte starts a number is a number, and its end index is the
one the grammar gives it. -/
private theorem valueAt_digit_inv {m : Strictness} {bs : Bytes} {i : Nat} {v : Value} {j : Nat}
    (h : ValueAt m bs i v j) {b : UInt8} (hb : bs[i]? = some b)
    (hd : (decide (b = 0x2D) || IsDigitB b) = true) :
    NumberAt bs i j ∧ v = .number ((bs.drop i).take (j - i)) := by
  cases h with
  | null hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      have e : b = 0x6E := Option.some.inj hh
      rw [e] at hd
      exact absurd hd (by decide)
  | true hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      have e : b = 0x74 := Option.some.inj hh
      rw [e] at hd
      exact absurd hd (by decide)
  | false hp =>
      have hh := hasPrefix_head hp
      rw [hb] at hh
      have e : b = 0x66 := Option.some.inj hh
      rw [e] at hd
      exact absurd hd (by decide)
  | string hs =>
      have hq := hs.1
      rw [hb] at hq
      have e : b = 0x22 := Option.some.inj hq
      rw [e] at hd
      exact absurd hd (by decide)
  | array hl _ _ =>
      rw [hb] at hl
      have e : b = 0x5B := Option.some.inj hl
      rw [e] at hd
      exact absurd hd (by decide)
  | object hl _ _ =>
      rw [hb] at hl
      have e : b = 0x7B := Option.some.inj hl
      rw [e] at hd
      exact absurd hd (by decide)
  | number hn => exact ⟨hn, rfl⟩

/-- The maximal number run stops at the first non-constituent, so a number whose
end index is followed by a non-constituent ends exactly where the run does. -/
private theorem numberAt_eq {bs : Bytes} {i j : Nat} (hn : NumberAt bs i j)
    (hj : j ≤ bs.length) (hstop : NumberStop bs j) :
    j = i + (numRun (bs.drop i)).length := by
  obtain ⟨hij, hnum⟩ := hn
  have hlen : ((bs.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  have hall : ∀ x ∈ (bs.drop i).take (j - i), NumConstituent x = true := by
    intro x hx
    exact rfcNumber_constituent hnum x hx
  have h1 : j - i ≤ (numRun (bs.drop i)).length :=
    length_le_numRun (bs.drop i) (j - i) (by rw [List.length_drop]; omega) hall
  have h2 : (numRun (bs.drop i)).length ≤ j - i := by
    rcases Nat.lt_or_ge (j - i) (numRun (bs.drop i)).length with hlt | hge
    · exfalso
      obtain ⟨c, rest, hdrop, hc⟩ := numRun_byte (b := bs.drop i) (k := j - i) hlt
      have hbs : bs.drop j = c :: rest := by
        rw [← hdrop, List.drop_drop, Nat.add_sub_of_le hij]
      exact absurd (hstop c rest hbs) (by rw [hc]; simp)
    · exact hge
  have h3 : j - i = (numRun (bs.drop i)).length := Nat.le_antisymm h1 h2
  omega

/-- No number derivation starts with a byte that is neither `-` nor a digit. -/
private theorem not_numberAt_of_head {bs : Bytes} {i : Nat} {b : UInt8}
    (hb : bs[i]? = some b) (hd : (decide (b = 0x2D) || IsDigitB b) = false) :
    ∀ j, ¬ NumberAt bs i j := by
  intro j hn
  obtain ⟨hij, hnum⟩ := hn
  have hne := rfcNumber_nonempty hnum
  have hlen : ((bs.drop i).take (j - i)).length = min (j - i) (bs.length - i) := by
    rw [List.length_take, List.length_drop]
  have hmpos : 0 < min (j - i) (bs.length - i) := by rwa [hlen] at hne
  have hpos : 0 < j - i := by omega
  have hlt : i < bs.length := by have := length_gt_of_get? hb; omega
  obtain ⟨m, hm⟩ : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
  have hdrop := List.drop_eq_getElem_cons hlt
  have hlex : (bs.drop i).take (j - i) = b :: ((bs.drop (i + 1)).take m) := by
    rw [hm, hdrop, List.getElem?_eq_some_iff.mp hb |>.2, List.take_succ_cons]
  have hhead := rfcNumber_head (by rwa [hlex] at hnum)
  rcases hhead with hh | hh
  · rw [hh] at hd; simp at hd
  · rw [hh] at hd; simp at hd

private theorem keyDecode_of {bs : Bytes} {first : Nat} {k : Key first}
    (hk : parseKey bs first = .done k) :
    ∀ rest : List Token,
      decodeValue bs first (Token.string ⟨first, k.next⟩ :: rest) =
        some { value := .string k.name, rest := rest, cursor := k.next,
               shrunk := by simp } := by
  obtain ⟨-, -, hktok, hkdec⟩ := parseKey_sound hk
  intro rest
  rw [← hktok]
  exact hkdec rest

private def ValueSound (bs : Bytes) (i depth : Nat) : Prop :=
  (∀ (p : Parsed i), parseValue bs i depth = .done p →
    ValueAt .strict bs i p.value p.next ∧
    p.next ≤ bs.length ∧
    p.tokens ≠ [] ∧
    DecodesValue bs i p.tokens p.value p.next ∧
    (∀ (v : Value) (j : Nat), ValueAt .strict bs i v j → ValueFollow bs j → j = p.next)) ∧
  (∀ (r : Reject), parseValue bs i depth = .fail (.invalid r) →
    ¬ ∃ v j, ValueAt .strict bs i v j ∧ ValueFollow bs j)

private def MembersTailSound (bs : Bytes) (j depth : Nat) : Prop :=
  ((∀ (t : ObjectTail j), parseMembersTail bs j depth = .done t →
    MembersTailSpec bs j t.tokens t.members t.next ∧
    DecodesMembers bs j t.tokens t.members t.next) ∧
  (∀ (r : Reject), parseMembersTail bs j depth = .fail (.invalid r) → ¬ MembersCont bs j)) ∧
  (∀ (t : ObjectTail j), parseMembersTail bs j depth = .done t →
    ∀ (k : Nat), MembersTailEnd bs j k →
      bs[k]? = some 0x7D → t.next = k)

private def ElemsTailSound (bs : Bytes) (j depth : Nat) : Prop :=
  ((∀ (t : ArrayTail j), parseElemsTail bs j depth = .done t →
    ElemsTailSpec bs j t.tokens t.values t.next ∧
    DecodesElems bs j t.tokens t.values t.next) ∧
  (∀ (r : Reject), parseElemsTail bs j depth = .fail (.invalid r) → ¬ ElemsCont bs j)) ∧
  (∀ (t : ArrayTail j), parseElemsTail bs j depth = .done t →
    ∀ (k : Nat), ElemsTailEnd bs j k →
      bs[k]? = some 0x5D → t.next = k)

private theorem parse_all (bs : Bytes) :
    (∀ i depth, ValueSound bs i depth) ∧
    (∀ j depth, MembersTailSound bs j depth) ∧
    (∀ j depth, ElemsTailSound bs j depth) := by
  refine parseValue.mutual_induct bs (ValueSound bs) (MembersTailSound bs) (ElemsTailSound bs)
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [parseValue.eq_def] at hp
      split at hp <;> simp_all
    · intro r hr
      rintro ⟨v, j, hv, -⟩
      obtain ⟨b, hb, -⟩ := valueAt_startB hv
      rw [hnone] at hb
      cases hb
  case c2 =>
    intro i hb
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [parseValue.eq_def] at hp
      split at hp <;> simp_all
    · intro r hr
      rw [parseValue.eq_def] at hr
      split at hr <;> simp_all
  case c3 =>
    intro i depth hb hd hi first hfirst hclose
    have hclose' : bs[first]? = some 0x5D := by simpa using hclose
    let pv : Parsed i :=
      { tokens := [Token.punct .openBracket ⟨i, i + 1⟩,
                   Token.punct .closeBracket ⟨first, first + 1⟩],
        value := .array [], next := first + 1, consumed := by omega }
    have hres : parseValue bs i depth = .done pv := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [pv, first, hbi])
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      injection hp with hp'
      subst p
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact ValueAt.array hb (ArrBody.empty hclose') hclose'
      · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hclose').1
      · simp [pv]
      · intro rest
        refine ⟨{ value := .array [], rest := rest, cursor := first + 1,
                  shrunk := by simp only [pv, List.length_append, List.length_cons,
                    List.length_nil]; omega }, ?_, rfl, rfl, rfl⟩
        simp [decodeValue, pv, first, hb, hclose']
      · intro v j hv hf
        obtain ⟨vs, k, rfl, hbody, hk, rfl⟩ := valueAt_array_inv hv hb
        cases hbody with
        | empty _ => rfl
        | elems he h =>
            obtain ⟨v', j', hv'⟩ := elems_first_valueAt he
            obtain ⟨b, hb', hstart⟩ := valueAt_startB hv'
            have hfb : bs[first]? = some b := hb'
            rw [hclose'] at hfb
            have hb_eq : b = 0x5D := (Option.some.inj hfb).symm
            subst hb_eq
            rw [valueStart_closeBracket] at hstart
            exact Bool.noConfusion hstart
    · intro r hr
      rw [hres] at hr
      cases hr
  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hcall]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨vs, k, rfl, hbody, hk, rfl⟩ := valueAt_array_inv hv hb
      cases hbody with
      | empty h =>
          exact hnc (by simpa using h)
      | elems he' h =>
          obtain ⟨v', j', hv', hf'⟩ := elems_first_valueAt_follow he' hk
          exact (ihm.2 r (by cases he; exact hcall)) ⟨v', j', hv', hf'⟩
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hcall, htail]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨vs, k, rfl, hbody, hk, rfl⟩ := valueAt_array_inv hv hb
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      have htail_invalid : parseElemsTail bs pv.next (depth - 1) = .fail (.invalid r) := by
        cases he
        exact htail
      have hrej := ihtm.1.2 r htail_invalid
      cases hbody with
      | empty h =>
          exact hnc (by simpa using h)
      | elems he' h =>
          cases he' with
          | last hv' hw =>
              have hf' : ValueFollow bs _ := follow_of_spaceAt_closeBracket hw hk
              have hj : _ = pv.next := hagree _ _ hv' hf'
              have hskip' := skipFrom_eq_of_spaceAt hw hk (by decide)
              rw [hj] at hskip'
              rw [← hskip'] at hk
              have hnc2 : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
                intro hc
                rw [hk] at hc
                exact absurd (Option.some.inj hc) (by decide)
              obtain ⟨t, ht⟩ := parseElemsTail_done_of_not_comma hnc2
              rw [ht] at htail
              cases htail
          | cons hv' hw1 hc hw2 hr =>
              have hf' : ValueFollow bs _ := follow_of_spaceAt_comma hw1 hc
              have hj : _ = pv.next := hagree _ _ hv' hf'
              have hskip' := skipFrom_eq_of_spaceAt hw1 hc (by decide)
              rw [hj] at hskip'
              rw [← hskip'] at hc
              obtain ⟨v3, j3, hv3⟩ := elems_first_valueAt hr
              obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv3
              have hskip2 := skipFrom_eq_of_spaceAt hw2 hb3 (valueStart_not_space hstart3)
              rw [← hskip'] at hskip2
              rw [← hskip2] at hr
              exact hrej ⟨hc, _, _, hr, hk⟩
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm
    have hclose' : bs[t.next]? = some 0x5D := by simpa using hclose
    let p : Parsed i :=
      { tokens := Token.punct .openBracket ⟨i, i + 1⟩ ::
          (pv.tokens ++ (t.tokens ++ [Token.punct .closeBracket ⟨t.next, t.next + 1⟩])),
        value := .array (pv.value :: t.values), next := t.next + 1,
        consumed := by have := t.moved; omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hcall, htail, hclose, p]
    obtain ⟨hv, hvlen, hvtok, hdecv, hagree⟩ := ihm.1 pv hcall
    obtain ⟨hspec, hdecT⟩ := ihtm.1.1 t htail
    have hta := ihtm.2 t htail
    refine ⟨?_, ?_⟩
    · intro p' hp
      rw [hres] at hp
      injection hp with hpeq
      subst p'
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- ValueAt
        have helems : Elems .strict bs first (pv.value :: t.values) t.next := by
          rcases hspec with ⟨hvs, htoknil, hnext⟩ | ⟨hcomma, he⟩
          · rw [hvs, hnext]
            exact Elems.last hv (skipFrom_space bs pv.next)
          · exact Elems.cons hv (skipFrom_space bs pv.next) hcomma
              (skipFrom_space bs (skipFrom bs pv.next + 1)) he
        exact ValueAt.array hb (ArrBody.elems helems hclose') hclose'
      · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hclose').1
      · dsimp only [p]
        intro hnil
        cases hnil
      · -- DecodesValue
        have hnotclose : ∀ (s : Span) (r : List Token),
            pv.tokens ≠ .punct .closeBracket s :: r := by
          intro s r heq
          obtain ⟨d0, hd0, -, -, -⟩ := hdecv []
          exact decodeValue_some_head_ne_close hd0 s r (by simpa using heq)
        exact decodeValue_array_of rfl hb hvtok hnotclose hdecv hdecT hclose'
      · -- agreement
        intro v j hv' hf
        obtain ⟨vs, k, rfl, hbody, hk, rfl⟩ := valueAt_array_inv hv' hb
        cases hbody with
        | empty h =>
            exfalso
            exact hnc (by simpa using h)
        | elems he' h =>
            cases he' with
            | last hv1 hw =>
                have hf1 : ValueFollow bs _ := follow_of_spaceAt_closeBracket hw hk
                have hj : _ = pv.next := hagree _ _ hv1 hf1
                have hskip := skipFrom_eq_of_spaceAt hw hk (by decide)
                rw [hj] at hskip
                have hgram : ElemsTailEnd bs pv.next k := Or.inl hskip.symm
                have htnext := hta k hgram hk
                change k + 1 = t.next + 1
                omega
            | cons hv1 hw1 hc hw2 hr =>
                have hf1 : ValueFollow bs _ := follow_of_spaceAt_comma hw1 hc
                have hj : _ = pv.next := hagree _ _ hv1 hf1
                have hskip := skipFrom_eq_of_spaceAt hw1 hc (by decide)
                rw [hj] at hskip
                rw [← hskip] at hc
                obtain ⟨v3, j3, hv3⟩ := elems_first_valueAt hr
                obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv3
                have hskip2 := skipFrom_eq_of_spaceAt hw2 hb3 (valueStart_not_space hstart3)
                rw [← hskip] at hskip2
                rw [← hskip2] at hr
                have hgram : ElemsTailEnd bs pv.next k := Or.inr ⟨hc, ⟨_, hr⟩⟩
                have htnext := hta k hgram hk
                change k + 1 = t.next + 1
                omega
    · intro r hr
      rw [hres] at hr
      cases hr
  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm
    have hres : parseValue bs i depth = .fail (.invalid (.expectedCloseBracket t.next)) := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hcall, htail, hnclose]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨vs, k, rfl, hbody, hk, rfl⟩ := valueAt_array_inv hv hb
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      cases hbody with
      | empty h =>
          exfalso
          exact hnc (by simpa using h)
      | elems he' h =>
          have hgram := elems_tail_end he' hk hagree
          have htnext := ihtm.2 t htail k hgram hk
          exact hnclose (by rw [htnext]; simpa using hk)
  case c8 =>
    intro i hb
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [parseValue.eq_def] at hp
      split at hp <;> simp_all
    · intro r hr
      rw [parseValue.eq_def] at hr
      split at hr <;> simp_all
  case c9 =>
    intro i depth hb hd hi first hfirst hclose
    have hclose' : bs[first]? = some 0x7D := by simpa using hclose
    let pv : Parsed i :=
      { tokens := [Token.punct .openBrace ⟨i, i + 1⟩,
                   Token.punct .closeBrace ⟨first, first + 1⟩],
        value := .object [], next := first + 1, consumed := by omega }
    have hres : parseValue bs i depth = .done pv := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [pv, first, hbi]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      injection hp with hpeq
      subst p
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact ValueAt.object hb (ObjBody.empty hclose') hclose'
      · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hclose').1
      · dsimp only [pv]
        intro hnil
        cases hnil
      · dsimp only [pv]
        intro rest
        refine ⟨{ value := .object [], rest := rest, cursor := first + 1,
                  shrunk := by simp only [List.length_append, List.length_cons]; omega },
          ?_, rfl, rfl, rfl⟩
        simp [decodeValue, first, hb, hclose']
      · intro v j hv hf
        obtain ⟨ms, k, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
        cases hbody with
        | empty _ => rfl
        | members hm h =>
            obtain ⟨cs, j1, hsAt⟩ := members_first_stringAt hm
            have hq := hsAt.1
            rw [hclose'] at hq
            exact absurd (Option.some.inj hq) (by decide)
    · intro r hr
      rw [hres] at hr
      cases hr
  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      injection hr with he
      cases he
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨ms, k, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
      cases hbody with
      | empty h =>
          exfalso
          exact hnc (by simpa using h)
      | members hm h =>
          obtain ⟨cs, j1, hsAt⟩ := members_first_stringAt hm
          exact parseKey_reject hkey ⟨cs, j1, hsAt⟩
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon
    have hres : parseValue bs i depth = .fail (.invalid (.expectedColon (skipFrom bs k.next))) := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb
            rw [hbi] at h
            exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey, hncColon]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨ms, kk, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
      obtain ⟨-, hsKey, -, hkle⟩ := parseKey_sound hkey
      cases hbody with
      | empty h =>
          exfalso
          exact hnc (by simpa using h)
      | members hm h =>
          cases hm with
          | last hm' hw =>
              cases hm' with
              | mk hsAt hw1 hcol hw2 hv1 =>
                  have hj1 := stringAt_end_unique hsAt hsKey
                    (by have hlt := length_gt_of_get? hcol; have hle := hw1.1; omega)
                    (parseKey_next_le hkey)
                  have hskip := skipFrom_eq_of_spaceAt hw1 hcol (by decide)
                  rw [hj1] at hskip
                  have hcolon : decide (bs[skipFrom bs k.next]? = some 0x3A) = true := by
                    rw [hskip]
                    simpa using hcol
                  have hnot : decide (bs[skipFrom bs k.next]? = some 0x3A) = false := by
                    simpa using hncColon
                  rw [hcolon] at hnot
                  cases hnot
          | cons hm' hw1 hc hw2 hr =>
              cases hm' with
              | mk hsAt hw1' hcol hw2' hv1 =>
                  have hj1 := stringAt_end_unique hsAt hsKey
                    (by have hlt := length_gt_of_get? hcol; have hle := hw1'.1; omega)
                    (parseKey_next_le hkey)
                  have hskip := skipFrom_eq_of_spaceAt hw1' hcol (by decide)
                  rw [hj1] at hskip
                  have hcolon : decide (bs[skipFrom bs k.next]? = some 0x3A) = true := by
                    rw [hskip]
                    simpa using hcol
                  have hnot : decide (bs[skipFrom bs k.next]? = some 0x3A) = false := by
                    simpa using hncColon
                  rw [hcolon] at hnot
                  cases hnot
  case c16 =>
    intro i depth hb
    refine ⟨?_, ?_⟩
    · intro p hp
      have hres : parseValue bs i depth = parseString bs i := by
        rw [parseValue.eq_def]; split <;> simp_all
      rw [hres] at hp
      simp only [parseString] at hp
      split at hp
      · cases hp
      · rename_i k hk
        injection hp with hp'
        subst hp'
        obtain ⟨-, hsAt, -, hkdec⟩ := parseKey_sound hk
        refine ⟨ValueAt.string hsAt, parseKey_next_le hk, by simp, ?_, ?_⟩
        · intro rest
          refine ⟨{ value := .string k.name, rest := rest, cursor := k.next,
                    shrunk := by simp }, ?_, rfl, rfl, rfl⟩
          simpa [List.singleton_append] using hkdec rest
        · intro v j hv hf
          obtain ⟨cs, rfl, hsAt2⟩ := valueAt_string_inv hv hb
          exact stringAt_end_unique hsAt2 hsAt (follow_le_length hf) (parseKey_next_le hk)
    · intro r hr
      have hres : parseValue bs i depth = parseString bs i := by
        rw [parseValue.eq_def]; split <;> simp_all
      rw [hres] at hr
      simp only [parseString] at hr
      split at hr
      · rename_i e he
        injection hr with he'
        rintro ⟨v, j, hv, hf⟩
        obtain ⟨cs, rfl, hsAt2⟩ := valueAt_string_inv hv hb
        exact parseKey_reject (r := r) (by rw [he'] at he; exact he) ⟨cs, j, hsAt2⟩
      · cases hr
  case c17 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i [0x74, 0x72, 0x75, 0x65] .true (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      simp only [parseLiteral] at hp
      split at hp
      · rename_i hl
        injection hp with hp'
        subst hp'
        have hpfix := hasPrefixB_iff.mp hl
        refine ⟨ValueAt.true hpfix, ?_, by simp, decodeValue_true_of hl, ?_⟩
        · have := hasPrefix_le hpfix (by decide : 0 < [0x74, 0x72, 0x75, 0x65].length)
          omega
        · intro v j hv hf
          obtain ⟨-, hj, -⟩ := valueAt_true_inv hv hb
          exact hj
      · cases hp
    · intro r hr
      rw [hres] at hr
      simp only [parseLiteral] at hr
      split at hr
      · cases hr
      · rename_i hl
        rintro ⟨v, j, hv, hf⟩
        obtain ⟨-, -, hpfix⟩ := valueAt_true_inv hv hb
        exact absurd (hasPrefixB_iff.mpr hpfix) (by rw [hl]; simp)
  case c18 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i [0x66, 0x61, 0x6C, 0x73, 0x65] .false (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      simp only [parseLiteral] at hp
      split at hp
      · rename_i hl
        injection hp with hp'
        subst hp'
        have hpfix := hasPrefixB_iff.mp hl
        refine ⟨ValueAt.false hpfix, ?_, by simp, decodeValue_false_of hl, ?_⟩
        · have := hasPrefix_le hpfix (by decide : 0 < [0x66, 0x61, 0x6C, 0x73, 0x65].length)
          omega
        · intro v j hv hf
          obtain ⟨-, hj, -⟩ := valueAt_false_inv hv hb
          exact hj
      · cases hp
    · intro r hr
      rw [hres] at hr
      simp only [parseLiteral] at hr
      split at hr
      · cases hr
      · rename_i hl
        rintro ⟨v, j, hv, hf⟩
        obtain ⟨-, -, hpfix⟩ := valueAt_false_inv hv hb
        exact absurd (hasPrefixB_iff.mpr hpfix) (by rw [hl]; simp)
  case c19 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i [0x6E, 0x75, 0x6C, 0x6C] .null (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      simp only [parseLiteral] at hp
      split at hp
      · rename_i hl
        injection hp with hp'
        subst hp'
        have hpfix := hasPrefixB_iff.mp hl
        refine ⟨ValueAt.null hpfix, ?_, by simp, decodeValue_null_of hl, ?_⟩
        · have := hasPrefix_le hpfix (by decide : 0 < [0x6E, 0x75, 0x6C, 0x6C].length)
          omega
        · intro v j hv hf
          obtain ⟨-, hj, -⟩ := valueAt_null_inv hv hb
          exact hj
      · cases hp
    · intro r hr
      rw [hres] at hr
      simp only [parseLiteral] at hr
      split at hr
      · cases hr
      · rename_i hl
        rintro ⟨v, j, hv, hf⟩
        obtain ⟨-, -, hpfix⟩ := valueAt_null_inv hv hb
        exact absurd (hasPrefixB_iff.mpr hpfix) (by rw [hl]; simp)
  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd
    have hres : parseValue bs i depth = parseNumber bs i := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      simp only [parseNumber] at hp
      split at hp
      · rename_i hlex
        injection hp with hp'
        subst hp'
        have hnum : NumberAt bs i (i + (numRun (bs.drop i)).length) := by
          refine ⟨Nat.le_add_right _ _, ?_⟩
          show RfcNumber ((bs.drop i).take (i + (numRun (bs.drop i)).length - i))
          rw [Nat.add_sub_cancel_left, (numRun_spec (bs.drop i)).1]
          exact numLexB_iff _ |>.mp hlex
        refine ⟨?_, ?_, by simp, decodeValue_number_of rfl hlex, ?_⟩
        · have h := ValueAt.number (m := .strict) hnum
          rwa [Nat.add_sub_cancel_left, (numRun_spec (bs.drop i)).1] at h
        · have hle := numRun_length_le (bs.drop i)
          have hib := length_gt_of_get? hb
          rw [List.length_drop] at hle
          have h2 := Nat.add_le_add_left hle i
          rwa [Nat.add_sub_of_le (Nat.le_of_lt hib)] at h2
        · intro v j hv hf
          obtain ⟨hn, -⟩ := valueAt_digit_inv hv hb hd
          exact numberAt_eq hn (follow_le_length hf) (follow_numberStop hf)
      · cases hp
    · intro r hr
      rw [hres] at hr
      simp only [parseNumber] at hr
      split at hr
      · cases hr
      · rename_i hlex
        rintro ⟨v, j, hv, hf⟩
        obtain ⟨hn, -⟩ := valueAt_digit_inv hv hb hd
        have hj := numberAt_eq hn (follow_le_length hf) (follow_numberStop hf)
        have hrf : RfcNumber ((bs.drop i).take (j - i)) := hn.2
        rw [hj] at hrf
        have hnum : numLexB (numRun (bs.drop i)) = true := by
          refine numLexB_iff _ |>.mpr ?_
          rwa [Nat.add_sub_cancel_left, (numRun_spec (bs.drop i)).1] at hrf
        exact hlex hnum
  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd
    have hres : parseValue bs i depth = .fail (.invalid (.unexpectedByte i b)) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [hres] at hp
      cases hp
    · intro r hr
      rw [hres] at hr
      rintro ⟨v, j, hv, hf⟩
      have hdf : (decide (b = 0x2D) || IsDigitB b) = false := by
        rw [Bool.eq_false_iff]; exact hd
      cases hv with
      | null hp =>
          have hh := hasPrefix_head hp
          rw [hb] at hh
          exact hb110 (Option.some.inj hh)
      | true hp =>
          have hh := hasPrefix_head hp
          rw [hb] at hh
          exact hb116 (Option.some.inj hh)
      | false hp =>
          have hh := hasPrefix_head hp
          rw [hb] at hh
          exact hb102 (Option.some.inj hh)
      | string hs =>
          have hq := hs.1
          rw [hb] at hq
          exact hb34 (Option.some.inj hq)
      | array hl _ _ =>
          rw [hb] at hl
          exact hb91 (Option.some.inj hl)
      | object hl _ _ =>
          rw [hb] at hl
          exact hb123 (Option.some.inj hl)
      | number hn => exact not_numberAt_of_head hb hdf j hn
  case c27 =>
    intro i depth hnc
    have hres : parseMembersTail bs i depth =
        .done { tokens := [], members := [], next := skipFrom bs i,
                moved := by have := skipFrom_ge bs i; omega } := by
      rw [parseMembersTail.eq_def]
      split
      · exact absurd ‹bs[skipFrom bs i]? = some 44› hnc
      · rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht
      rw [hres] at ht
      injection ht with h'
      subst h'
      refine ⟨Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
      intro rest hno
      refine ⟨{ members := [], rest := rest, cursor := skipFrom bs i,
                moved := Nat.le_refl _ }, ?_, rfl, rfl, rfl⟩
      cases rest with
      | nil => simp [decodeMembersTail]
      | cons tok rest' =>
          cases tok with
          | punct p s =>
              cases p <;> simp_all [decodeMembersTail, NoCommaHead]
          | null s => simp [decodeMembersTail]
          | bool b s => simp [decodeMembersTail]
          | number s => simp [decodeMembersTail]
          | string s => simp [decodeMembersTail]
    · intro r hr
      rw [hres] at hr
      cases hr
    · intro t ht k hgram hk
      rw [hres] at ht
      injection ht with h'
      subst h'
      rcases hgram with h | ⟨hcomma, -⟩
      · exact h.symm
      · exact absurd hcomma hnc
  case c31 =>
    intro i depth hnc
    have hres : parseElemsTail bs i depth =
        .done { tokens := [], values := [], next := skipFrom bs i,
                moved := by have := skipFrom_ge bs i; omega } := by
      rw [parseElemsTail.eq_def]
      split
      · exact absurd ‹bs[skipFrom bs i]? = some 44› hnc
      · rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht
      rw [hres] at ht
      injection ht with h'
      subst h'
      refine ⟨Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
      intro rest hno
      refine ⟨{ values := [], rest := rest, cursor := skipFrom bs i,
                moved := Nat.le_refl _ }, ?_, rfl, rfl, rfl⟩
      cases rest with
      | nil => simp [decodeElemsTail]
      | cons tok rest' =>
          cases tok with
          | punct p s =>
              cases p <;> simp_all [decodeElemsTail, NoCommaHead]
          | null s => simp [decodeElemsTail]
          | bool b s => simp [decodeElemsTail]
          | number s => simp [decodeElemsTail]
          | string s => simp [decodeElemsTail]
    · intro r hr
      rw [hres] at hr
      cases hr
    · intro t ht k hgram hk
      rw [hres] at ht
      injection ht with h'
      subst h'
      rcases hgram with h | ⟨hcomma, -⟩
      · exact h.symm
      · exact absurd hcomma hnc

  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall ihm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey, hkskip, hncColon, hcall]
    refine ⟨?_, ?_⟩
    · intro p hp; rw [hres] at hp; cases hp
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨ms, kk, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have htail_invalid : parseValue bs (skipFrom bs (skipFrom bs k.next + 1)) (depth - 1)
          = .fail (.invalid r) := by
        rw [he] at hcall; exact hcall
      have hrej := ihm.2 r htail_invalid
      cases hbody with
      | empty h => exact hnc (by simpa using h)
      | members hm h =>
          cases hm with
          | last hm' hw =>
              cases hm' with
              | mk hsAt hw1 hcol hw2 hv1 =>
                  have hj1 := stringAt_end_unique hsAt hsKey
                    (by have hlt := length_gt_of_get? hcol; have hle := hw1.1; omega) hkle
                  rw [hj1] at hw1
                  have hskip := skipFrom_eq_of_spaceAt hw1 hcol (by decide)
                  obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv1
                  rw [← hskip] at hw2
                  have hskip2 := skipFrom_eq_of_spaceAt hw2 hb3 (valueStart_not_space hstart3)
                  rw [← hskip2] at hv1
                  have hval := hv1
                  have hf1 : ValueFollow bs _ := follow_of_spaceAt_closeBrace hw hk
                  exact hrej ⟨_, _, hval, hf1⟩
          | cons hm' hw1 hc2 hw2 hr =>
              cases hm' with
              | mk hsAt hw1' hcol hw2' hv1 =>
                  have hj1 := stringAt_end_unique hsAt hsKey
                    (by have hlt := length_gt_of_get? hcol; have hle := hw1'.1; omega) hkle
                  rw [hj1] at hw1'
                  have hskip := skipFrom_eq_of_spaceAt hw1' hcol (by decide)
                  rw [← hskip] at hw2'
                  obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv1
                  have hskip2 := skipFrom_eq_of_spaceAt hw2' hb3 (valueStart_not_space hstart3)
                  rw [← hskip2] at hv1
                  have hval := hv1
                  have hf1 : ValueFollow bs _ := follow_of_spaceAt_comma hw1 hc2
                  exact hrej ⟨_, _, hval, hf1⟩
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey, hkskip, hncColon, hcall, htail]
    refine ⟨?_, ?_⟩
    · intro p hp; rw [hres] at hp; cases hp
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨ms, kk, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      have htail_invalid : parseMembersTail bs pv.next (depth - 1) = .fail (.invalid r) := by
        rw [he] at htail; exact htail
      have hrej := ihtm.1.2 r htail_invalid
      cases hbody with
      | empty h => exact hnc (by simpa using h)
      | members hm h =>
          cases ms with
          | nil => cases hm
          | cons mem ms' =>
              obtain ⟨nm, vv⟩ := mem
              have hgram := members_tail_end hm hk ⟨_, hsKey⟩ hkle hbcolon hagree
              rcases hgram with hk_eq | ⟨hcomma, vs', he'⟩
              · have hnc2 : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
                  rw [hk_eq] at hk
                  intro hc
                  rw [hc] at hk
                  exact absurd (Option.some.inj hk) (by decide)
                obtain ⟨t, ht⟩ := parseMembersTail_done_of_not_comma hnc2
                rw [ht] at htail; cases htail
              · exact hrej ⟨hcomma, vs', kk, he', hk⟩
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hclose ihm ihtm
    have hclose' : bs[t.next]? = some 0x7D := by simpa using hclose
    let p : Parsed i :=
      { tokens := Token.punct .openBrace ⟨i, i + 1⟩ ::
          (k.token ::
            ([Token.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
              (pv.tokens ++ (t.tokens ++ [Token.punct .closeBrace ⟨t.next, t.next + 1⟩])))),
        value := .object ((k.name, pv.value) :: t.members), next := t.next + 1,
        consumed := by have := t.moved; omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey, hkskip, hncColon, hcall, htail, hclose, p]
    obtain ⟨hv, hvlen, hvtok, hdecv, hagree⟩ := ihm.1 pv hcall
    obtain ⟨-, hsKey, hktok, hkdec⟩ := parseKey_sound hkey
    have hkle := parseKey_next_le hkey
    have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
    obtain ⟨hspec, hdecT⟩ := ihtm.1.1 t htail
    have hta := ihtm.2 t htail
    have hm : Members .strict bs first ((k.name, pv.value) :: t.members) t.next := by
      rcases hspec with ⟨hms, htoknil, hnext⟩ | ⟨hcomcap, he⟩
      · rw [hms, hnext]
        exact Members.last
          (Member.mk hsKey (skipFrom_space bs k.next) hbcolon
            (skipFrom_space bs (skipFrom bs k.next + 1)) hv)
          (skipFrom_space bs pv.next)
      · exact Members.cons
          (Member.mk hsKey (skipFrom_space bs k.next) hbcolon
            (skipFrom_space bs (skipFrom bs k.next + 1)) hv)
          (skipFrom_space bs pv.next) hcomcap (skipFrom_space bs (skipFrom bs pv.next + 1)) he
    refine ⟨?_, ?_⟩
    · intro p2 hp2
      rw [hres] at hp2
      injection hp2 with hp2
      subst hp2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact ValueAt.object hb (ObjBody.members hm hclose') hclose'
      · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hclose').1
      · intro hnil
        simp [p] at hnil
      · simp only [p, hktok]
        exact decodeValue_object_of rfl hb (keyDecode_of hkey) rfl hbcolon hdecv hdecT hclose'
      · intro v j hv' hf
        obtain ⟨ms, kk, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv' hb
        cases hbody with
        | empty h => exfalso; exact hnc (by simpa using h)
        | members hm2 h2 =>
            cases ms with
            | nil => cases hm2
            | cons mem ms' =>
                obtain ⟨nm, vv⟩ := mem
                have hgram := members_tail_end hm2 h2 ⟨_, hsKey⟩ hkle hbcolon hagree
                have htnext := hta kk hgram h2
                change kk + 1 = t.next + 1
                omega
    · intro r hr
      rw [hres] at hr
      cases hr
  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hnclose ihm ihtm
    have hres : parseValue bs i depth = .fail (.invalid (.expectedCloseBrace t.next)) := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
            | simp_all [first, hd, hnc, hkey, hkskip, hncColon, hcall, htail, hnclose]
    refine ⟨?_, ?_⟩
    · intro p hp; rw [hres] at hp; cases hp
    · intro r hr
      rw [hres] at hr
      rintro ⟨v, j, hv, hf⟩
      obtain ⟨ms, kk, rfl, hbody, hk, rfl⟩ := valueAt_object_inv hv hb
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      cases hbody with
      | empty h => exact hnc (by simpa using h)
      | members hm h =>
          cases ms with
          | nil => cases hm
          | cons mem ms' =>
              obtain ⟨nm, vv⟩ := mem
              have hgram := members_tail_end hm hk ⟨_, hsKey⟩ hkle hbcolon hagree
              have htnext := ihtm.2 t htail kk hgram hk
              exact hnclose (by rw [htnext]; simpa using hk)
  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨hc, ms, kk, hm, hk⟩
      exact parseKey_reject (r := r) (by rw [he] at hkey; exact hkey) (members_first_stringAt hm)
    · intro t ht; rw [hres] at ht; cases ht
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon
    have hres : parseMembersTail bs i depth =
        .fail (.invalid (.expectedColon (skipFrom bs k.next))) := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      rintro ⟨hc, ms, kk, hm, hk⟩
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have hcolonNot : bs[skipFrom bs k.next]? ≠ some 0x3A := by simpa using hncColon
      cases hm with
      | last hm' hw =>
          cases hm' with
          | mk hsAt hw1 hcol hw2 hv1 =>
              have hj1 := stringAt_end_unique hsAt hsKey
                (by have hlt := length_gt_of_get? hcol; have hle := hw1.1; omega) hkle
              rw [hj1] at hw1
              have hskip := skipFrom_eq_of_spaceAt hw1 hcol (by decide)
              rw [← hskip] at hcol
              exact hcolonNot hcol
      | cons hm' hw1 hc2 hw2 hr =>
          cases hm' with
          | mk hsAt hw1' hcol hw2' hv1 =>
              have hj1 := stringAt_end_unique hsAt hsKey
                (by have hlt := length_gt_of_get? hcol; have hle := hw1'.1; omega) hkle
              rw [hj1] at hw1'
              have hskip := skipFrom_eq_of_spaceAt hw1' hcol (by decide)
              rw [← hskip] at hcol
              exact hcolonNot hcol
    · intro t ht; rw [hres] at ht; cases ht
  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨hc, ms, kk, hm, hk⟩
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have htail_invalid : parseValue bs (skipFrom bs (skipFrom bs k.next + 1)) depth
          = .fail (.invalid r) := by
        rw [he] at hcall; exact hcall
      have hrej := ihm.2 r htail_invalid
      cases hm with
      | last hm' hw =>
          cases hm' with
          | mk hsAt hw1 hcol hw2 hv1 =>
              have hj1 := stringAt_end_unique hsAt hsKey
                (by have hlt := length_gt_of_get? hcol; have hle := hw1.1; omega) hkle
              rw [hj1] at hw1
              have hskip := skipFrom_eq_of_spaceAt hw1 hcol (by decide)
              rw [← hskip] at hw2
              obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv1
              have hskip2 := skipFrom_eq_of_spaceAt hw2 hb3 (valueStart_not_space hstart3)
              rw [← hskip2] at hv1
              have hf1 : ValueFollow bs _ := follow_of_spaceAt_closeBrace hw hk
              exact hrej ⟨_, _, hv1, hf1⟩
      | cons hm' hw1 hc2 hw2 hr =>
          cases hm' with
          | mk hsAt hw1' hcol hw2' hv1 =>
              have hj1 := stringAt_end_unique hsAt hsKey
                (by have hlt := length_gt_of_get? hcol; have hle := hw1'.1; omega) hkle
              rw [hj1] at hw1'
              have hskip := skipFrom_eq_of_spaceAt hw1' hcol (by decide)
              obtain ⟨b3, hb3, hstart3⟩ := valueAt_startB hv1
              rw [← hskip] at hw2'
              have hskip2 := skipFrom_eq_of_spaceAt hw2' hb3 (valueStart_not_space hstart3)
              rw [← hskip2] at hv1
              have hval := hv1
              have hf1 : ValueFollow bs _ := follow_of_spaceAt_comma hw1 hc2
              exact hrej ⟨_, _, hval, hf1⟩
    · intro t ht; rw [hres] at ht; cases ht
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall]
        simp only [htail]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨hc, ms, kk, hm, hk⟩
      obtain ⟨-, hsKey, -, -⟩ := parseKey_sound hkey
      have hkle := parseKey_next_le hkey
      have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      have htail_invalid : parseMembersTail bs pv.next depth = .fail (.invalid r) := by
        rw [he] at htail; exact htail
      have hrej := ihtm.1.2 r htail_invalid
      cases ms with
      | nil => cases hm
      | cons mem ms' =>
          obtain ⟨nm, vv⟩ := mem
          have hgram := members_tail_end hm hk ⟨_, hsKey⟩ hkle hbcolon hagree
          rcases hgram with hk_eq | ⟨hcomma', vs', he'⟩
          · have hnc2 : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
              rw [hk_eq] at hk
              intro hc2
              rw [hc2] at hk
              exact absurd (Option.some.inj hk) (by decide)
            obtain ⟨t, ht⟩ := parseMembersTail_done_of_not_comma hnc2
            rw [ht] at htail; cases htail
          · exact hrej ⟨hcomma', vs', kk, he', hk⟩
    · intro t ht; rw [hres] at ht; cases ht
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail ihm ihtm
    let t2 : ObjectTail i :=
      { tokens := Token.punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ :: k.token ::
                  ([Token.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
                    (pv.tokens ++ t.tokens)),
        members := (k.name, pv.value) :: t.members, next := t.next,
        moved := by have := t.moved; omega }
    have hres : parseMembersTail bs i depth = .done t2 := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall, htail]
        rfl
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨-, hsKey, hktok, hkdec⟩ := parseKey_sound hkey
    have hkle := parseKey_next_le hkey
    have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
    obtain ⟨hv, hvlen, hvtok, hdecv, hagree⟩ := ihm.1 pv hcall
    obtain ⟨hspec, hdecT⟩ := ihtm.1.1 t htail
    have hta := ihtm.2 t htail
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t3 ht
      rw [hres] at ht
      injection ht with ht
      subst ht
      simp only [t2]
      refine ⟨?_, ?_⟩
      · rcases hspec with ⟨hms, htoknil, hnext⟩ | ⟨hcomcap, he⟩
        · rw [hms, hnext]
          exact Or.inr ⟨hcomma, Members.last
            (Member.mk hsKey (skipFrom_space bs k.next) hbcolon
              (skipFrom_space bs (skipFrom bs k.next + 1)) hv)
            (skipFrom_space bs pv.next)⟩
        · exact Or.inr ⟨hcomma, Members.cons
            (Member.mk hsKey (skipFrom_space bs k.next) hbcolon
              (skipFrom_space bs (skipFrom bs k.next + 1)) hv)
            (skipFrom_space bs pv.next) hcomcap
            (skipFrom_space bs (skipFrom bs pv.next + 1)) he⟩
      · simp only [t2, hktok]
        exact decodeMembersTail_of rfl hcomma rfl (keyDecode_of hkey) rfl hbcolon hdecv hdecT
    · intro r hr; rw [hres] at hr; cases hr
    · intro t3 ht kk hgram hk
      rw [hres] at ht
      injection ht with ht
      subst ht
      rcases hgram with hk_eq | ⟨hcomma', ms', hm'⟩
      · rw [hk_eq] at hk
        rw [hcomma] at hk
        exact absurd (Option.some.inj hk) (by decide)
      · cases ms' with
        | nil => cases hm'
        | cons mem ms'' =>
            obtain ⟨nm, vv⟩ := mem
            exact hta kk (members_tail_end hm' hk ⟨_, hsKey⟩ hkle hbcolon hagree) hk
  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨hc, vs, k, he', hk⟩
      obtain ⟨v, j, hv, hf⟩ := elems_first_valueAt_follow he' hk
      exact ihm.2 r (by rw [he] at hcall; exact hcall) ⟨v, j, hv, hf⟩
    · intro t ht; rw [hres] at ht; cases ht
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall]
        simp only [htail]
      · rename_i hother
        exact absurd hcomma hother
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t ht; rw [hres] at ht; cases ht
    · intro r hr
      rw [hres] at hr
      injection hr with he
      rintro ⟨hc, vs, k, he', hk⟩
      obtain ⟨-, -, -, -, hagree⟩ := ihm.1 pv hcall
      have htail_invalid : parseElemsTail bs pv.next depth = .fail (.invalid r) := by
        rw [he] at htail; exact htail
      have hrej := ihtm.1.2 r htail_invalid
      have hgram := elems_tail_end he' hk hagree
      rcases hgram with hk_eq | ⟨hcomma', vs', he''⟩
      · have hnc2 : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
          rw [hk_eq] at hk
          intro hc2
          rw [hc2] at hk
          exact absurd (Option.some.inj hk) (by decide)
        obtain ⟨t, ht⟩ := parseElemsTail_done_of_not_comma hnc2
        rw [ht] at htail; cases htail
      · exact hrej ⟨hcomma', vs', k, he'', hk⟩
    · intro t ht; rw [hres] at ht; cases ht
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail ihm ihtm
    let t2 : ArrayTail i :=
      { tokens := Token.punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ ::
                    (pv.tokens ++ t.tokens),
        values := pv.value :: t.values, next := t.next,
        moved := by have := t.moved; omega }
    have hres : parseElemsTail bs i depth = .done t2 := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall, htail]
        rfl
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨hv, hvlen, hvtok, hdecv, hagree⟩ := ihm.1 pv hcall
    obtain ⟨hspec, hdecT⟩ := ihtm.1.1 t htail
    have hta := ihtm.2 t htail
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro t3 ht
      rw [hres] at ht
      injection ht with ht
      subst ht
      simp only [t2]
      refine ⟨?_, ?_⟩
      · rcases hspec with ⟨hvs, htoknil, hnext⟩ | ⟨hcomcap, he⟩
        · rw [hvs, hnext]
          exact Or.inr ⟨hcomma, Elems.last hv (skipFrom_space bs pv.next)⟩
        · exact Or.inr ⟨hcomma, Elems.cons hv (skipFrom_space bs pv.next) hcomcap
            (skipFrom_space bs (skipFrom bs pv.next + 1)) he⟩
      · exact decodeElemsTail_of rfl hcomma rfl hdecv hdecT
    · intro r hr; rw [hres] at hr; cases hr
    · intro t3 ht kk hgram hk
      rw [hres] at ht
      injection ht with ht
      subst ht
      rcases hgram with hk_eq | ⟨hcomma', vs', he'⟩
      · rw [hk_eq] at hk
        rw [hcomma] at hk
        exact absurd (Option.some.inj hk) (by decide)
      · exact hta kk (elems_tail_end he' hk hagree) hk


/-- The tape decoding equation at the top level: a decode that consumes exactly
the tokens and lands on the input's end decodes the tape to its value. -/
private theorem decodeTape_of {bs : Bytes} {toks : List Token} {v : Value}
    {d : Decoded toks} (hd : decodeValue bs (skipFrom bs 0) toks = some d)
    (hdv : d.value = v) (hdr : d.rest = []) (hdc : skipFrom bs d.cursor = bs.length) :
    decodeTape ⟨bs, toks⟩ = some v := by
  unfold decodeTape
  dsimp only
  rw [hd]
  dsimp only
  rw [hdr, hdc, hdv]
  simp


/-! ### Soundness

A successful parse yields a tape over the same input whose decode is a value the
accepted language assigns to that input; a syntax rejection is a proof that no
value satisfies `ValidDocument`, which covers both a non-text and a text refused
by `Policy`.  The limit outcomes make no claim about validity — that asymmetry,
not a comment, is what distinguishes them. -/
theorem parseRef_sound (l : Limits) (bs : Bytes) :
    (∀ t : Tape, parseBytes l bs = .ok t →
      t.input = bs ∧ ∃ v : Value, ValidDocument bs v ∧ decodeTape t = some v) ∧
    (∀ r : Reject, parseBytes l bs = .error (.invalid r) →
      ¬ ∃ v : Value, ValidDocument bs v) := by
  obtain ⟨hVall, -, -⟩ := parse_all bs
  have hV := hVall (skipFrom bs 0) l.maxDepth
  constructor
  · intro t ht
    unfold parseBytes at ht
    by_cases hin : bs.length > l.maxInput
    · rw [if_pos hin] at ht; cases ht
    · rw [if_neg hin] at ht
      by_cases hbom : bs.take 3 = [0xEF, 0xBB, 0xBF]
      · rw [if_pos hbom] at ht; cases ht
      · rw [if_neg hbom] at ht
        cases hpv : parseValue bs (skipFrom bs 0) l.maxDepth with
        | fail e => simp only [hpv] at ht; cases ht
        | done p =>
            simp only [hpv] at ht
            by_cases htr : skipFrom bs p.next < bs.length
            · rw [if_pos htr] at ht; cases ht
            · rw [if_neg htr] at ht
              by_cases hcap : p.tokens.length ≤ l.maxTokens
              · rw [if_pos hcap] at ht
                injection ht with hteq
                cases hteq
                obtain ⟨hva, hvlen, hvtok, hdec, hagree⟩ := hV.1 p hpv
                have hslen : skipFrom bs p.next = bs.length := by
                  have h1 := skipFrom_le_length bs p.next hvlen
                  omega
                refine ⟨by simp, p.value, ?_, ?_⟩
                · exact (valid_iff_strict bs p.value).mpr ⟨skipFrom bs 0, p.next, rfl, hva, hslen⟩
                · obtain ⟨d, hd, hdv, hdr, hdc⟩ := hdec []
                  obtain ⟨d0, hd0, hdv0, hdr0, hdc0⟩ :=
                    decodeValue_cast (l1 := p.tokens ++ []) (l2 := p.tokens) (by simp) hd
                  exact decodeTape_of hd0 (by rw [hdv0, hdv]) (by rw [hdr0, hdr])
                    (by rw [hdc0, hdc]; exact hslen)
              · rw [if_neg hcap] at ht; cases ht
  · intro r hr
    unfold parseBytes at hr
    by_cases hin : bs.length > l.maxInput
    · rw [if_pos hin] at hr; cases hr
    · rw [if_neg hin] at hr
      by_cases hbom : bs.take 3 = [0xEF, 0xBB, 0xBF]
      · rw [if_pos hbom] at hr
        rintro ⟨v, hv⟩
        obtain ⟨i, j, h0, hva, hjlen⟩ := (valid_iff_strict bs v).mp hv
        have hbom0 : bs[0]? = some 0xEF := by
          have h : (bs.take 3)[0]? = some 0xEF := by rw [hbom]; rfl
          rwa [List.getElem?_take, if_pos (by decide : 0 < 3)] at h
        have hns : IsSpaceB 0xEF = false := by decide
        have hdrop := drop_eq_cons_of_get? hbom0
        have hskip0 : skipFrom bs 0 = 0 := by
          unfold skipFrom
          rw [hdrop]
          simp [spaceRun, hns]
        rw [← h0, hskip0] at hva
        exact valueAt_not_bom hva hbom0
      · rw [if_neg hbom] at hr
        cases hpv : parseValue bs (skipFrom bs 0) l.maxDepth with
        | fail e =>
            simp only [hpv] at hr
            injection hr with hr'
            rintro ⟨v, hv⟩
            obtain ⟨i, j, h0, hva, hjlen⟩ := (valid_iff_strict bs v).mp hv
            rw [← h0] at hva
            exact hV.2 r (by rw [hr'] at hpv; exact hpv) ⟨v, j, hva, Or.inl hjlen⟩
        | done p =>
            simp only [hpv] at hr
            by_cases htr : skipFrom bs p.next < bs.length
            · rw [if_pos htr] at hr
              rintro ⟨v, hv⟩
              obtain ⟨i, j, h0, hva, hjlen⟩ := (valid_iff_strict bs v).mp hv
              rw [← h0] at hva
              obtain ⟨-, -, -, -, hagree⟩ := hV.1 p hpv
              have hf : ValueFollow bs j := Or.inl hjlen
              have hj : j = p.next := hagree v j hva hf
              rw [hj] at hjlen
              omega
            · rw [if_neg htr] at hr
              by_cases hcap : p.tokens.length ≤ l.maxTokens
              · rw [if_pos hcap] at hr; cases hr
              · rw [if_neg hcap] at hr; cases hr

/-! ### Completeness inside the limits

The induction is the parser's own recursion, `parseValue.mutual_induct`: each
branch's conditions are a case's hypotheses, and each recursive call's statement is
the case's induction hypothesis at the callee's index and depth.  The grammar is
used only for inversion — which branch must be taken, and where the enclosing
separator sits — so nothing about the derivation's shape has to be re-proved.

The three predicates differ in what the enclosing production fixes.  A value's
statement carries its end index and `NumberStop`, the second of which is what makes
the number scan's maximal run equal the semantic lexeme.  A tail's statement
carries the remainder of the enclosing list and its end, because a tail is entered
after a value rather than at one: `elems_head` and `members_head` read the
continuation off the derivation, and `skipFrom bs j` is the comma a tail tests for
exactly when the byte there is a comma. -/

private def ValueComplete (bs : Bytes) (i depth : Nat) : Prop :=
  ∀ (v : Value) (j : Nat), ValueAt .strict bs i v j → j ≤ bs.length →
    v.depth ≤ depth → NumberStop bs j →
    ∃ p : Parsed i, parseValue bs i depth = .done p ∧ p.value = v ∧ p.next = j ∧
      p.tokens.length = v.tokenCount

private def ElemsTailComplete (bs : Bytes) (j depth : Nat) : Prop :=
  ∀ (vs : List Value) (k : Nat), (∀ v ∈ vs, v.depth ≤ depth) →
    bs[skipFrom bs j]? = some 0x2C →
    Elems .strict bs (skipFrom bs (skipFrom bs j + 1)) vs k →
    bs[k]? = some 0x5D →
    ∃ t : ArrayTail j, parseElemsTail bs j depth = .done t ∧ t.values = vs ∧
      t.next = k ∧ t.tokens.length = elemsCount vs

private def MembersTailComplete (bs : Bytes) (j depth : Nat) : Prop :=
  ∀ (ms : List (List Nat × Value)) (k : Nat), (∀ m ∈ ms, m.2.depth ≤ depth) →
    bs[skipFrom bs j]? = some 0x2C →
    Members .strict bs (skipFrom bs (skipFrom bs j + 1)) ms k →
    bs[k]? = some 0x7D →
    ∃ t : ObjectTail j, parseMembersTail bs j depth = .done t ∧ t.members = ms ∧
      t.next = k ∧ t.tokens.length = membersCount ms

/-- An element of a list is no deeper than the list. -/
private theorem value_depth_le_elemsDepth :
    ∀ (vs : List Value) {v : Value}, v ∈ vs → v.depth ≤ elemsDepth vs
  | [], v, hv => by simp at hv
  | e :: es, v, hv => by
      rw [elemsDepth]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (value_depth_le_elemsDepth es hv') (Nat.le_max_right _ _)

/-- A member's value is no deeper than the member list. -/
private theorem value_depth_le_membersDepth :
    ∀ (ms : List (List Nat × Value)) {v : Value}, (∃ k, (k, v) ∈ ms) →
      v.depth ≤ membersDepth ms
  | [], v, hv => by simp at hv
  | m :: ms, v, hv => by
      rw [membersDepth]
      rcases hv with ⟨k, hk⟩
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (value_depth_le_membersDepth ms ⟨k, hk'⟩) (Nat.le_max_right _ _)

/-- Two successful parses of one value at one index are the same parse. -/
private theorem parseValue_done_unique {bs : Bytes} {i depth : Nat} {p1 p2 : Parsed i}
    (h1 : parseValue bs i depth = .done p1) (h2 : parseValue bs i depth = .done p2) :
    p1 = p2 := by
  rw [h1] at h2
  injection h2 with h

private theorem parseElemsTail_done_unique {bs : Bytes} {j depth : Nat} {t1 t2 : ArrayTail j}
    (h1 : parseElemsTail bs j depth = .done t1) (h2 : parseElemsTail bs j depth = .done t2) :
    t1 = t2 := by
  rw [h1] at h2
  injection h2 with h

private theorem parseMembersTail_done_unique {bs : Bytes} {j depth : Nat} {t1 t2 : ObjectTail j}
    (h1 : parseMembersTail bs j depth = .done t1)
    (h2 : parseMembersTail bs j depth = .done t2) : t1 = t2 := by
  rw [h1] at h2
  injection h2 with h

/-- A tail with no comma ahead of it stops where the whitespace run stops. -/
private theorem parseElemsTail_stop {bs : Bytes} {j depth : Nat}
    (h : bs[skipFrom bs j]? ≠ some 0x2C) :
    parseElemsTail bs j depth = .done ⟨[], [], skipFrom bs j, skipFrom_ge bs j⟩ := by
  rw [parseElemsTail.eq_def]
  split
  · rename_i hc
    exact absurd hc h
  · rfl

private theorem parseMembersTail_stop {bs : Bytes} {j depth : Nat}
    (h : bs[skipFrom bs j]? ≠ some 0x2C) :
    parseMembersTail bs j depth = .done ⟨[], [], skipFrom bs j, skipFrom_ge bs j⟩ := by
  rw [parseMembersTail.eq_def]
  split
  · rename_i hc
    exact absurd hc h
  · rfl

/-- A value starts at `k`, so the whitespace run before it ends exactly at `k`. -/
private theorem skipFrom_of_spaceAt_value {bs : Bytes} {j k : Nat} {v : Value} {j' : Nat}
    (h : SpaceAt bs j k) (hv : ValueAt .strict bs k v j') : skipFrom bs j = k := by
  obtain ⟨b, hb, hstart⟩ := valueAt_startB hv
  exact skipFrom_eq_of_spaceAt h hb (valueStart_not_space hstart)

/-- A string literal starts at `k`, and its opening quote is not whitespace. -/
private theorem skipFrom_of_spaceAt_string {bs : Bytes} {j k : Nat} {cs : List Nat}
    {j' : Nat} (h : SpaceAt bs j k) (hk : StringAt .strict bs k j' cs) : skipFrom bs j = k :=
  skipFrom_eq_of_spaceAt h hk.1 (by decide)

/-- A string the strict grammar derives is the one `parseKey` scans: same name, and
an end one past the closing quote. -/
private theorem parseKey_complete {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict bs i j cs) (hj : j ≤ bs.length) :
    ∃ k : Key i, parseKey bs i = .done k ∧ k.name = cs ∧ k.next = j := by
  obtain ⟨hb, rest, hstr, hdrop⟩ := h
  have hs : scanChars (bs.drop (i + 1)) = .ok (cs, rest) :=
    (scanChars_iff _ _ _).mpr hstr
  have hlen : rest.length = bs.length - j := by
    have := congrArg List.length hdrop
    simp only [List.length_drop] at this
    omega
  have hnext : bs.length - rest.length = j := by omega
  have hi : i < bs.length := length_gt_of_get? hb
  have hle := scalar_suffix_le (bs.drop (i + 1)) cs rest hs
  simp only [List.length_drop] at hle
  refine ⟨⟨.string ⟨i, bs.length - rest.length⟩, cs, bs.length - rest.length, by omega⟩,
    ?_, rfl, hnext⟩
  unfold parseKey
  split
  · rename_i hb2
    split
    · rename_i e hs2
      rw [hs] at hs2
      cases hs2
    · rename_i cs2 after hs2
      rw [hs] at hs2
      cases hs2
      rfl
  · rename_i hb2
    rw [hb] at hb2
    exact absurd rfl hb2

/-- An element list's first element, and the continuation the parser resumes at:
the whitespace after the value, then either the enclosing close byte (when the list
ends here) or a comma and the remaining elements. -/
private theorem elems_head {bs : Bytes} {i k : Nat} {vs : List Value}
    (h : Elems .strict bs i vs k) (hk : bs[k]? = some 0x5D) :
    ∃ (v : Value) (j1 j2 : Nat) (rest : List Value),
      vs = v :: rest ∧ ValueAt .strict bs i v j1 ∧ ValueFollow bs j1 ∧
      SpaceAt bs j1 j2 ∧
      ((rest = [] ∧ j2 = k ∧ bs[j2]? = some 0x5D) ∨
        (bs[j2]? = some 0x2C ∧ Elems .strict bs (skipFrom bs (j2 + 1)) rest k)) := by
  cases h with
  | last hv hw =>
      exact ⟨_, _, _, _, rfl, hv, follow_of_spaceAt_closeBracket hw hk, hw,
        Or.inl ⟨rfl, rfl, hk⟩⟩
  | cons hv hw1 hc hw2 hr =>
      refine ⟨_, _, _, _, rfl, hv, follow_of_spaceAt_comma hw1 hc, hw1, Or.inr ⟨hc, ?_⟩⟩
      obtain ⟨v3, j3, hv3⟩ := elems_first_valueAt hr
      rw [skipFrom_of_spaceAt_value hw2 hv3]
      exact hr

/-- A member list's first member, read back: the key span, the colon, the value and
the continuation, at the indexes the parser will compute. -/
private theorem members_head {bs : Bytes} {i k : Nat} {ms : List (List Nat × Value)}
    (h : Members .strict bs i ms k) (hk : bs[k]? = some 0x7D) :
    ∃ (nm : List Nat) (v : Value) (j1 jc j3 j4 j5 : Nat) (rest : List (List Nat × Value)),
      ms = (nm, v) :: rest ∧ StringAt .strict bs i j1 nm ∧
      SpaceAt bs j1 jc ∧ bs[jc]? = some 0x3A ∧ SpaceAt bs (jc + 1) j3 ∧
      ValueAt .strict bs j3 v j4 ∧ ValueFollow bs j4 ∧ SpaceAt bs j4 j5 ∧
      ((rest = [] ∧ j5 = k ∧ bs[j5]? = some 0x7D) ∨
        (bs[j5]? = some 0x2C ∧ Members .strict bs (skipFrom bs (j5 + 1)) rest k)) := by
  cases h with
  | last hm hw =>
      cases hm with
      | mk hkStr hw1 hcol hwval hv =>
          exact ⟨_, _, _, _, _, _, _, _, rfl, hkStr, hw1, hcol, hwval, hv,
            follow_of_spaceAt_closeBrace hw hk, hw, Or.inl ⟨rfl, rfl, hk⟩⟩
  | cons hm hwcomma hc hw2 hr =>
      cases hm with
      | mk hkStr hw1 hcol hwval hv =>
          refine ⟨_, _, _, _, _, _, _, _, rfl, hkStr, hw1, hcol, hwval, hv,
            follow_of_spaceAt_comma hwcomma hc, hwcomma, Or.inr ⟨hc, ?_⟩⟩
          obtain ⟨cs3, j3', hs3⟩ := members_first_stringAt hr
          rw [skipFrom_of_spaceAt_string hw2 hs3]
          exact hr

/-- A non-empty whitespace run starts with a whitespace byte. -/
private theorem spaceRun_pos_head {l : Bytes} (h : 0 < spaceRun l) :
    ∀ (c : UInt8) (rest : Bytes), l = c :: rest → IsSpaceB c = true := by
  intro c rest he
  subst he
  rw [spaceRun] at h
  split at h
  · assumption
  · omega

/-- At the end of the input nothing follows, so no number constituent does. -/
private theorem numberStop_of_skipFrom_length {bs : Bytes} {j : Nat}
    (h : skipFrom bs j = bs.length) : NumberStop bs j := by
  intro c rest hd
  have hlen : j < bs.length := by
    have : 0 < (bs.drop j).length := by rw [hd]; simp
    simp only [List.length_drop] at this
    omega
  have hpos : 0 < spaceRun (bs.drop j) := by
    unfold skipFrom at h
    omega
  exact isSpace_not_constituent (spaceRun_pos_head hpos c rest hd)

/-- A number is scanned to its own lexeme when nothing that could extend it
follows: the maximal constituent run is the semantic lexeme, so `parseNumber`
returns it with the grammar's end. -/
private theorem parseNumber_done {bs : Bytes} {i j : Nat}
    (hn : NumberAt bs i j) (hj : j ≤ bs.length) (hstop : NumberStop bs j) :
    ∃ p : Parsed i, parseNumber bs i = .done p ∧ p.next = j ∧
      p.value = .number ((bs.drop i).take (j - i)) ∧ p.tokens.length = 1 := by
  obtain ⟨hij, hnum⟩ := hn
  have hJ : j = i + (numRun (bs.drop i)).length := numberAt_eq ⟨hij, hnum⟩ hj hstop
  have hlen : (numRun (bs.drop i)).length = j - i := by omega
  have hne : 0 < (numRun (bs.drop i)).length := by
    rw [hlen]
    have h2 : ((bs.drop i).take (j - i)).length = j - i := by
      rw [List.length_take, List.length_drop]
      omega
    have h3 := rfcNumber_nonempty hnum
    omega
  have hlex : (bs.drop i).take (j - i) = numRun (bs.drop i) := by
    rw [← hlen]
    exact (numRun_spec (bs.drop i)).1
  have hnum' : RfcNumber (numRun (bs.drop i)) := by rw [← hlex]; exact hnum
  have hb : numLexB (numRun (bs.drop i)) = true := (numLexB_iff _).mpr hnum'
  refine ⟨⟨[.number ⟨i, i + (numRun (bs.drop i)).length⟩], .number (numRun (bs.drop i)),
    i + (numRun (bs.drop i)).length, by omega⟩, ?_, hJ.symm, ?_, rfl⟩
  · unfold parseNumber
    dsimp only
    rw [dite_eq_left hb]
  · rw [hlex]

/-- `complete_all`.  The mutual induction over the parser's three recursive
definitions, at every index and depth.  Each case reconstructs the branch's result
from its own conditions; where the grammar says a recursive call must succeed, the
case's induction hypothesis supplies the result and `parseValue_done_unique` (or its
tail analogue) identifies it with the one the branch already carries. -/
private theorem complete_all (bs : Bytes) :
    (∀ i depth, ValueComplete bs i depth) ∧
    (∀ j depth, MembersTailComplete bs j depth) ∧
    (∀ j depth, ElemsTailComplete bs j depth) := by
  refine parseValue.mutual_induct bs (ValueComplete bs) (MembersTailComplete bs)
    (ElemsTailComplete bs)
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone v j hv hj hdep hstop
    obtain ⟨b, hb, -⟩ := valueAt_startB hv
    rw [hnone] at hb
    cases hb
  case c2 =>
    intro i hb v j hv hj hdep hstop
    obtain ⟨vs, k, rfl, -, -, -⟩ := valueAt_array_inv hv hb
    simp only [Value.depth] at hdep
    exact absurd hdep (by omega : ¬ 1 + elemsDepth vs ≤ 0)
  case c3 =>
    intro i depth hb hd hi first hfirst hclose v j hv hj hdep hstop
    have hclose' : bs[skipFrom bs (i + 1)]? = some 0x5D := by simpa using hclose
    obtain ⟨vs, k, rfl, hbody, hk, hj'⟩ := valueAt_array_inv hv hb
    cases hbody with
    | elems he h =>
        obtain ⟨v', j', hv'⟩ := elems_first_valueAt he
        obtain ⟨b, hb', hstart⟩ := valueAt_startB hv'
        have hfirst' : bs[skipFrom bs (i + 1)]? = some b := hb'
        rw [hclose'] at hfirst'
        have hbe : b = 0x5D := (Option.some.inj hfirst').symm
        subst hbe
        rw [valueStart_closeBracket] at hstart
        exact Bool.noConfusion hstart
    | empty h =>
        refine ⟨⟨[.punct .openBracket ⟨i, i + 1⟩,
            .punct .closeBracket ⟨skipFrom bs (i + 1), skipFrom bs (i + 1) + 1⟩],
          .array [], skipFrom bs (i + 1) + 1, by omega⟩, ?_, rfl, hj'.symm, rfl⟩
        rw [parseValue.eq_def]
        simp only [first] at *
        split
        all_goals
          first
          | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
          | (simp_all; done)
  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm v j hv hj hdep hstop
    obtain ⟨vs, k, rfl, hbody, hk, hj'⟩ := valueAt_array_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x5D) = true := by simpa using h
        exact absurd h' hnc
    | elems he h =>
        have hd1 : elemsDepth vs ≤ depth - 1 := by
          have h2 : 1 + elemsDepth vs ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head he hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        obtain ⟨p1, hcall1, -, -, -⟩ :=
          ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
        rw [hcall] at hcall1
        cases hcall1
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm
      v j hv hj hdep hstop
    obtain ⟨vs, k, rfl, hbody, hk, hj'⟩ := valueAt_array_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x5D) = true := by simpa using h
        exact absurd h' hnc
    | elems he h =>
        have hd1 : elemsDepth vs ≤ depth - 1 := by
          have h2 : 1 + elemsDepth vs ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head he hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ w ∈ rest, w.depth ≤ depth - 1 := by
          intro w hw
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (value_depth_le_elemsDepth rest hw)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj2k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          rw [parseElemsTail_stop hstop'] at htail
          cases htail
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Elems .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest k := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, -, -, -⟩ := ihtm rest k hbndR hcomma' hrest' hk
          rw [htail1] at htail
          cases htail
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm
      v j hv hj hdep hstop
    have hclose' : bs[t.next]? = some 0x5D := by simpa using hclose
    obtain ⟨vs, k, rfl, hbody, hk, hj'⟩ := valueAt_array_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x5D) = true := by simpa using h
        exact absurd h' hnc
    | elems he h =>
        have hd1 : elemsDepth vs ≤ depth - 1 := by
          have h2 : 1 + elemsDepth vs ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head he hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ w ∈ rest, w.depth ≤ depth - 1 := by
          intro w hw
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (value_depth_le_elemsDepth rest hw)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj2k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
            parseElemsTail_done_unique htail (parseElemsTail_stop hstop')
          have htvals : t.values = [] := by cases htcanon; rfl
          have httoks : t.tokens = [] := by cases htcanon; rfl
          have htnext : t.next = k := by
            cases htcanon
            exact hskip.trans hj2k
          subst hrestnil
          refine ⟨⟨.punct .openBracket ⟨i, i + 1⟩ :: pv.tokens ++ t.tokens ++
              [.punct .closeBracket ⟨t.next, t.next + 1⟩],
            .array (pv.value :: t.values), t.next + 1, by have := t.moved; omega⟩,
            ?_, ?_, ?_, ?_⟩
          · rw [parseValue.eq_def]
            simp only [first] at *
            split
            all_goals
              first
              | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
              | (simp_all; done)
          · rw [hval1, htvals, hvs]
          · show t.next + 1 = j
            omega
          · simp only [httoks, htvals, hvs, hval1, htok1, List.length_cons,
              List.length_append, List.length_nil, elemsCount, Value.tokenCount]
            omega
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Elems .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest k := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, htval, htnext, httok⟩ :=
            ihtm rest k hbndR hcomma' hrest' hk
          have htt : t1 = t := parseElemsTail_done_unique htail1 htail
          rw [htt] at htval htnext httok
          refine ⟨⟨.punct .openBracket ⟨i, i + 1⟩ :: pv.tokens ++ t.tokens ++
              [.punct .closeBracket ⟨t.next, t.next + 1⟩],
            .array (pv.value :: t.values), t.next + 1, by have := t.moved; omega⟩,
            ?_, ?_, ?_, ?_⟩
          · rw [parseValue.eq_def]
            simp only [first] at *
            split
            all_goals
              first
              | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
              | (simp_all; done)
          · rw [hval1, htval, hvs]
          · show t.next + 1 = j
            omega
          · simp only [httok, htval, hvs, hval1, htok1, List.length_cons,
              List.length_append, List.length_nil, elemsCount, Value.tokenCount]
            omega
  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm
      v j hv hj hdep hstop
    obtain ⟨vs, k, rfl, hbody, hk, hj'⟩ := valueAt_array_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x5D) = true := by simpa using h
        exact absurd h' hnc
    | elems he h =>
        have hd1 : elemsDepth vs ≤ depth - 1 := by
          have h2 : 1 + elemsDepth vs ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head he hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ w ∈ rest, w.depth ≤ depth - 1 := by
          intro w hw
          have hh := hd1
          rw [hvs] at hh
          simp only [elemsDepth] at hh
          exact Nat.le_trans (value_depth_le_elemsDepth rest hw)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj2k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
            parseElemsTail_done_unique htail (parseElemsTail_stop hstop')
          have htnk : t.next = k := by
            cases htcanon
            exact hskip.trans hj2k
          exact absurd (by rw [htnk]; simpa using hk) hnclose
        · have hskip : skipFrom bs pv.next = j2 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Elems .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest k := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, htval, htnext, httok⟩ := ihtm rest k hbndR hcomma' hrest' hk
          have htt : t1 = t := parseElemsTail_done_unique htail1 htail
          rw [htt] at htnext
          exact absurd (by rw [htnext]; simpa using hk) hnclose
  case c8 =>
    intro i hb v j hv hj hdep hstop
    obtain ⟨ms, k, rfl, -, -, -⟩ := valueAt_object_inv hv hb
    simp only [Value.depth] at hdep
    exact absurd hdep (by omega : ¬ 1 + membersDepth ms ≤ 0)
  case c9 =>
    intro i depth hb hd hi first hfirst hclose v j hv hj hdep hstop
    have hclose' : bs[skipFrom bs (i + 1)]? = some 0x7D := by simpa using hclose
    obtain ⟨ms, k, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | members hm h =>
        obtain ⟨cs, j', hs⟩ := members_first_stringAt hm
        have h1 : bs[skipFrom bs (i + 1)]? = some 0x22 := hs.1
        rw [hclose'] at h1
        exact absurd (Option.some.inj h1) (by decide)
    | empty h =>
        refine ⟨⟨[.punct .openBrace ⟨i, i + 1⟩,
            .punct .closeBrace ⟨skipFrom bs (i + 1), skipFrom bs (i + 1) + 1⟩],
          .object [], skipFrom bs (i + 1) + 1, by omega⟩, ?_, rfl, hj'.symm, rfl⟩
        rw [parseValue.eq_def]
        simp only [first] at *
        split
        all_goals
          first
          | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
          | (simp_all; done)
  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey v j hv hj hdep hstop
    obtain ⟨ms, k, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        obtain ⟨key, hkeyD, -, -⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        cases hkeyD
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon
      v j hv hj hdep hstop
    obtain ⟨ms, kk, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        injection hkeyD with hkeq
        subst hkeq
        have hskip : skipFrom bs k.next = jc := by
          rw [hkeyNext]
          exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
        have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by rw [hskip]; exact hcol
        have hdec : decide (bs[skipFrom bs k.next]? = some 0x3A) = true := by
          rw [hbcolon]
          rfl
        rw [hdec] at hncColon
        exact Bool.noConfusion hncColon
  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall
      ihm v j hv hj hdep hstop
    obtain ⟨ms, kk, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        have hd1 : membersDepth ms ≤ depth - 1 := by
          have h2 : 1 + membersDepth ms ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        injection hkeyD with hkeq
        subst hkeq
        have hskip1 : skipFrom bs k.next = jc := by
          rw [hkeyNext]
          exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
        have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
          rw [hskip1]
          exact skipFrom_of_spaceAt_value hw2 hv1
        have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
          rw [hskip2]; exact hv1
        obtain ⟨p1, hcall1, -, -, -⟩ :=
          ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
        rw [hcall] at hcall1
        cases hcall1
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall
      hpnext e htail ihm ihtm v j hv hj hdep hstop
    obtain ⟨ms, kk, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        have hd1 : membersDepth ms ≤ depth - 1 := by
          have h2 : 1 + membersDepth ms ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ m ∈ rest, m.2.depth ≤ depth - 1 := by
          intro m hm'
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (value_depth_le_membersDepth rest ⟨m.1, hm'⟩)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        injection hkeyD with hkeq
        subst hkeq
        have hskip1 : skipFrom bs k.next = jc := by
          rw [hkeyNext]
          exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
        have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
          rw [hskip1]
          exact skipFrom_of_spaceAt_value hw2 hv1
        have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
          rw [hskip2]; exact hv1
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj5k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          rw [parseMembersTail_stop hstop'] at htail
          cases htail
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Members .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest kk := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, -, -, -⟩ := ihtm rest kk hbndR hcomma' hrest' hk
          rw [htail1] at htail
          cases htail
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall
      hpnext t htail hclose ihm ihtm v j hv hj hdep hstop
    have hclose' : bs[t.next]? = some 0x7D := by simpa using hclose
    obtain ⟨ms, kk, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        have hd1 : membersDepth ms ≤ depth - 1 := by
          have h2 : 1 + membersDepth ms ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ m ∈ rest, m.2.depth ≤ depth - 1 := by
          intro m hm'
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (value_depth_le_membersDepth rest ⟨m.1, hm'⟩)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        injection hkeyD with hkeq
        subst hkeq
        have hskip1 : skipFrom bs k.next = jc := by
          rw [hkeyNext]
          exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
        have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
          rw [hskip1]
          exact skipFrom_of_spaceAt_value hw2 hv1
        have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
          rw [hskip2]; exact hv1
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj5k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
            parseMembersTail_done_unique htail (parseMembersTail_stop hstop')
          have htmems : t.members = [] := by cases htcanon; rfl
          have httoks : t.tokens = [] := by cases htcanon; rfl
          have htnk : t.next = kk := by
            cases htcanon
            exact hskip.trans hj5k
          subst hrestnil
          refine ⟨⟨.punct .openBrace ⟨i, i + 1⟩ :: k.token ::
              [.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
              pv.tokens ++ t.tokens ++ [.punct .closeBrace ⟨t.next, t.next + 1⟩],
            .object ((k.name, pv.value) :: t.members), t.next + 1,
            by have := t.moved; omega⟩, ?_, ?_, ?_, ?_⟩
          · rw [parseValue.eq_def]
            simp only [first] at *
            split
            all_goals
              first
              | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
              | (simp_all; done)
          · rw [hkeyName, hval1, htmems, hms]
          · show t.next + 1 = j
            omega
          · simp only [httoks, htmems, hms, hkeyName, hval1, htok1, List.length_cons,
              List.length_append, List.length_nil, membersCount, Value.tokenCount]
            omega
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Members .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest kk := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, htval, htnext, httok⟩ := ihtm rest kk hbndR hcomma' hrest' hk
          have htt : t1 = t := parseMembersTail_done_unique htail1 htail
          rw [htt] at htval htnext httok
          refine ⟨⟨.punct .openBrace ⟨i, i + 1⟩ :: k.token ::
              [.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
              pv.tokens ++ t.tokens ++ [.punct .closeBrace ⟨t.next, t.next + 1⟩],
            .object ((k.name, pv.value) :: t.members), t.next + 1,
            by have := t.moved; omega⟩, ?_, ?_, ?_, ?_⟩
          · rw [parseValue.eq_def]
            simp only [first] at *
            split
            all_goals
              first
              | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
              | (simp_all; done)
          · rw [hkeyName, hval1, htval, hms]
          · show t.next + 1 = j
            omega
          · simp only [httok, htval, hms, hkeyName, hval1, htok1, List.length_cons,
              List.length_append, List.length_nil, membersCount, Value.tokenCount]
            omega
  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall
      hpnext t htail hnclose ihm ihtm v j hv hj hdep hstop
    obtain ⟨ms, kk, rfl, hbody, hk, hj'⟩ := valueAt_object_inv hv hb
    cases hbody with
    | empty h =>
        have h' : decide (bs[first]? = some 0x7D) = true := by simpa using h
        exact absurd h' hnc
    | members hm h =>
        have hd1 : membersDepth ms ≤ depth - 1 := by
          have h2 : 1 + membersDepth ms ≤ depth := by simpa only [Value.depth] using hdep
          omega
        obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1,
          hf, hsp, hcont⟩ := members_head hm hk
        have hbnd1 : v1.depth ≤ depth - 1 := by
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (Nat.le_max_left _ _) hh
        have hbndR : ∀ m ∈ rest, m.2.depth ≤ depth - 1 := by
          intro m hm'
          have hh := hd1
          rw [hms] at hh
          simp only [membersDepth] at hh
          exact Nat.le_trans (value_depth_le_membersDepth rest ⟨m.1, hm'⟩)
            (Nat.le_trans (Nat.le_max_right _ _) hh)
        obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
        rw [hkey] at hkeyD
        injection hkeyD with hkeq
        subst hkeq
        have hskip1 : skipFrom bs k.next = jc := by
          rw [hkeyNext]
          exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
        have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
          rw [hskip1]
          exact skipFrom_of_spaceAt_value hw2 hv1
        have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
          rw [hskip2]; exact hv1
        obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
          ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
        have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
        rw [hpu] at hval1 hnext1 htok1
        rcases hcont with ⟨hrestnil, hj5k, hbclose⟩ | ⟨hbcomma, hrestG⟩
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
          have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
            rw [hskip, hbclose]
            simp
          have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
            parseMembersTail_done_unique htail (parseMembersTail_stop hstop')
          have htnk : t.next = kk := by
            cases htcanon
            exact hskip.trans hj5k
          exact absurd (by rw [htnk]; simpa using hk) hnclose
        · have hskip : skipFrom bs pv.next = j5 := by
            rw [hnext1]
            exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
          have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
            rw [hskip]; exact hbcomma
          have hrest' : Members .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest kk := by
            rw [hskip]; exact hrestG
          obtain ⟨t1, htail1, htval, htnext, httok⟩ := ihtm rest kk hbndR hcomma' hrest' hk
          have htt : t1 = t := parseMembersTail_done_unique htail1 htail
          rw [htt] at htnext
          exact absurd (by rw [htnext]; simpa using hk) hnclose
  case c16 =>
    intro i depth hb v j hv hj hdep hstop
    obtain ⟨cs, rfl, hstr⟩ := valueAt_string_inv hv hb
    obtain ⟨k, hk, hname, hnext⟩ := parseKey_complete hstr hj
    have hres : parseValue bs i depth = .done ⟨[k.token], .string k.name, k.next, k.consumed⟩ := by
      rw [parseValue.eq_def]
      split
      all_goals
        first
        | (exfalso; rw [List.getElem?_eq_getElem (length_gt_of_get? hb)] at *; simp_all; done)
        | (simp_all [parseString, hk]; done)
    exact ⟨_, hres, by rw [hname], hnext, rfl⟩
  case c17 =>
    intro i depth hb v j hv hj hdep hstop
    obtain ⟨rfl, rfl, hp⟩ := valueAt_true_inv hv hb
    have hi : i < bs.length := length_gt_of_get? hb
    have hpfx : HasPrefixB bs i [0x74, 0x72, 0x75, 0x65] = true := hasPrefixB_iff.mpr hp
    have hlres : parseLiteral bs i [0x74, 0x72, 0x75, 0x65] .true (by decide) =
        .done ⟨[.bool true ⟨i, i + 4⟩], .bool true, i + 4, by omega⟩ := by
      simp only [parseLiteral]
      rw [hpfx]
      rfl
    have hres : parseValue bs i depth = .done
        ⟨[.bool true ⟨i, i + 4⟩], .bool true, i + 4, by omega⟩ := by
      rw [parseValue.eq_def]
      split
      all_goals
        first
        | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
        | (rw [hlres]; done)
    exact ⟨_, hres, rfl, rfl, rfl⟩
  case c18 =>
    intro i depth hb v j hv hj hdep hstop
    obtain ⟨rfl, rfl, hp⟩ := valueAt_false_inv hv hb
    have hi : i < bs.length := length_gt_of_get? hb
    have hpfx : HasPrefixB bs i [0x66, 0x61, 0x6C, 0x73, 0x65] = true := hasPrefixB_iff.mpr hp
    have hlres : parseLiteral bs i [0x66, 0x61, 0x6C, 0x73, 0x65] .false (by decide) =
        .done ⟨[.bool false ⟨i, i + 5⟩], .bool false, i + 5, by omega⟩ := by
      simp only [parseLiteral]
      rw [hpfx]
      rfl
    have hres : parseValue bs i depth = .done
        ⟨[.bool false ⟨i, i + 5⟩], .bool false, i + 5, by omega⟩ := by
      rw [parseValue.eq_def]
      split
      all_goals
        first
        | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
        | (rw [hlres]; done)
    exact ⟨_, hres, rfl, rfl, rfl⟩
  case c19 =>
    intro i depth hb v j hv hj hdep hstop
    obtain ⟨rfl, rfl, hp⟩ := valueAt_null_inv hv hb
    have hi : i < bs.length := length_gt_of_get? hb
    have hpfx : HasPrefixB bs i [0x6E, 0x75, 0x6C, 0x6C] = true := hasPrefixB_iff.mpr hp
    have hlres : parseLiteral bs i [0x6E, 0x75, 0x6C, 0x6C] .null (by decide) =
        .done ⟨[.null ⟨i, i + 4⟩], .null, i + 4, by omega⟩ := by
      simp only [parseLiteral]
      rw [hpfx]
      rfl
    have hres : parseValue bs i depth = .done
        ⟨[.null ⟨i, i + 4⟩], .null, i + 4, by omega⟩ := by
      rw [parseValue.eq_def]
      split
      all_goals
        first
        | (exfalso; rw [List.getElem?_eq_getElem hi] at *; simp_all; done)
        | (rw [hlres]; done)
    exact ⟨_, hres, rfl, rfl, rfl⟩
  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd v j hv hj hdep hstop
    obtain ⟨hnum, rfl⟩ := valueAt_digit_inv hv hb hd
    obtain ⟨p, hpd, hpnext, hpval, hptok⟩ := parseNumber_done hnum hj hstop
    have hres : parseValue bs i depth = .done p := by
      rw [parseValue.eq_def]
      split
      all_goals
        first
        | (exfalso; rw [List.getElem?_eq_getElem (length_gt_of_get? hb)] at *; simp_all; done)
        | (simp_all; done)
    exact ⟨p, hres, hpval, hpnext, hptok⟩
  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd v j hv hj hdep hstop
    obtain ⟨b', hb', hstart⟩ := valueAt_startB hv
    rw [hb] at hb'
    have hbe : b = b' := Option.some.inj hb'
    subst hbe
    have h0 : ValueStartB b = false := by
      have hdf : (decide (b = 0x2D) || IsDigitB b) = false := by
        rw [Bool.eq_false_iff]
        exact hd
      have h2d : decide (b = 0x2D) = false := by
        have h := hdf
        simp only [Bool.or_eq_false_iff] at h
        exact h.1
      have hdig : IsDigitB b = false := by
        have h := hdf
        simp only [Bool.or_eq_false_iff] at h
        exact h.2
      simp only [ValueStartB, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨⟨⟨⟨⟨⟨⟨hb110, hb116⟩, hb102⟩, hb34⟩, hb91⟩, hb123⟩,
        decide_eq_false_iff_not.mp h2d⟩, hdig⟩
    rw [h0] at hstart
    exact Bool.noConfusion hstart
  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey ms k hbnd hcommaSt hMembers hk
    obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1, hf, hsp,
      hcont⟩ := members_head hMembers hk
    obtain ⟨key, hkeyD, -, -⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
    rw [hkey] at hkeyD
    cases hkeyD
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon ms kk hbnd hcommaSt
      hMembers hk
    obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1, hf, hsp,
      hcont⟩ := members_head hMembers hk
    obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
    rw [hkey] at hkeyD
    injection hkeyD with hkeq
    subst hkeq
    have hskip : skipFrom bs k.next = jc := by
      rw [hkeyNext]
      exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
    have hbcolon : bs[skipFrom bs k.next]? = some 0x3A := by rw [hskip]; exact hcol
    have hdec : decide (bs[skipFrom bs k.next]? = some 0x3A) = true := by
      rw [hbcolon]
      rfl
    rw [hdec] at hncColon
    exact Bool.noConfusion hncColon
  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm
      ms kk hbnd hcommaSt hMembers hk
    obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1, hf, hsp,
      hcont⟩ := members_head hMembers hk
    rw [hms] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd (nm, v1) (by simp)
    obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
    rw [hkey] at hkeyD
    injection hkeyD with hkeq
    subst hkeq
    have hskip1 : skipFrom bs k.next = jc := by
      rw [hkeyNext]
      exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
    have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
      rw [hskip1]
      exact skipFrom_of_spaceAt_value hw2 hv1
    have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
      rw [hskip2]; exact hv1
    obtain ⟨p1, hcall1, -, -, -⟩ :=
      ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
    rw [hcall] at hcall1
    cases hcall1
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall
      hpnext e htail ihm ihtm ms kk hbnd hcommaSt hMembers hk
    obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1, hf, hsp,
      hcont⟩ := members_head hMembers hk
    rw [hms] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd (nm, v1) (by simp)
    have hbndR : ∀ m ∈ rest, m.2.depth ≤ depth := by
      intro m hm'
      exact hbnd m (by simp [hm'])
    obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
    rw [hkey] at hkeyD
    injection hkeyD with hkeq
    subst hkeq
    have hskip1 : skipFrom bs k.next = jc := by
      rw [hkeyNext]
      exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
    have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
      rw [hskip1]
      exact skipFrom_of_spaceAt_value hw2 hv1
    have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
      rw [hskip2]; exact hv1
    obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
      ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
    have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
    rw [hpu] at hval1 hnext1 htok1
    rcases hcont with ⟨hrestnil, hj5k, hbclose⟩ | ⟨hbcomma, hrestG⟩
    · have hskip : skipFrom bs pv.next = j5 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
      have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
        rw [hskip, hbclose]
        simp
      rw [parseMembersTail_stop hstop'] at htail
      cases htail
    · have hskip : skipFrom bs pv.next = j5 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
      have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
        rw [hskip]; exact hbcomma
      have hrest' : Members .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest kk := by
        rw [hskip]; exact hrestG
      obtain ⟨t1, htail1, -, -, -⟩ := ihtm rest kk hbndR hcomma' hrest' hk
      rw [htail1] at htail
      cases htail
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall
      hpnext t htail ihm ihtm ms kk hbnd hcommaSt hMembers hk
    obtain ⟨nm, v1, j1, jc, j3, j4, j5, rest, hms, hkStr, hw1, hcol, hw2, hv1, hf, hsp,
      hcont⟩ := members_head hMembers hk
    rw [hms] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd (nm, v1) (by simp)
    have hbndR : ∀ m ∈ rest, m.2.depth ≤ depth := by
      intro m hm'
      exact hbnd m (by simp [hm'])
    obtain ⟨key, hkeyD, hkeyName, hkeyNext⟩ := parseKey_complete hkStr (by have h1 := hw1.1; have h2 := length_gt_of_get? hcol; omega)
    rw [hkey] at hkeyD
    injection hkeyD with hkeq
    subst hkeq
    have hskip1 : skipFrom bs k.next = jc := by
      rw [hkeyNext]
      exact skipFrom_eq_of_spaceAt hw1 hcol (by decide)
    have hskip2 : skipFrom bs (skipFrom bs k.next + 1) = j3 := by
      rw [hskip1]
      exact skipFrom_of_spaceAt_value hw2 hv1
    have hval : ValueAt .strict bs (skipFrom bs (skipFrom bs k.next + 1)) v1 j4 := by
      rw [hskip2]; exact hv1
    obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
      ihm v1 j4 hval (follow_le_length hf) hbnd1 (follow_numberStop hf)
    have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
    rw [hpu] at hval1 hnext1 htok1
    let t2 : ObjectTail i :=
      { tokens := Token.punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ :: k.token ::
                  ([Token.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
                    (pv.tokens ++ t.tokens)),
        members := (k.name, pv.value) :: t.members, next := t.next,
        moved := by have := t.moved; omega }
    have hres : parseMembersTail bs i depth = .done t2 := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall, htail]
        rfl
      · rename_i hother
        exact absurd hcomma hother
    rcases hcont with ⟨hrestnil, hj5k, hbclose⟩ | ⟨hbcomma, hrestG⟩
    · have hskip : skipFrom bs pv.next = j5 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
      have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
        rw [hskip, hbclose]
        simp
      have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
        parseMembersTail_done_unique htail (parseMembersTail_stop hstop')
      have htmems : t.members = [] := by cases htcanon; rfl
      have httoks : t.tokens = [] := by cases htcanon; rfl
      have htnk : t.next = kk := by
        cases htcanon
        exact hskip.trans hj5k
      subst hrestnil
      refine ⟨t2, hres, ?_, ?_, ?_⟩
      · rw [hms]
        simp only [t2, hkeyName, hval1, htmems]
      · simp only [t2]
        rw [htnk]
      · simp only [t2, httoks, hms, htok1, List.length_cons, List.length_append,
          List.length_nil, membersCount]
        omega
    · have hskip : skipFrom bs pv.next = j5 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
      have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
        rw [hskip]; exact hbcomma
      have hrest' : Members .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest kk := by
        rw [hskip]; exact hrestG
      obtain ⟨t1, htail1, htval, htnext, httok⟩ := ihtm rest kk hbndR hcomma' hrest' hk
      have htt : t1 = t := parseMembersTail_done_unique htail1 htail
      rw [htt] at htval htnext httok
      refine ⟨t2, hres, ?_, ?_, ?_⟩
      · rw [hms]
        simp only [t2, hkeyName, hval1, htval]
      · simp only [t2]
        rw [htnext]
      · simp only [t2, httok, hms, htok1, List.length_cons, List.length_append,
          List.length_nil, membersCount]
        omega
  case c27 =>
    intro i depth hnc ms k hbnd hcommaSt hMembers hk
    exact absurd (by simpa using hcommaSt) hnc
  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm vs k hbnd hcommaSt hElems hk
    obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head hElems hk
    rw [hvs] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd v1 (by simp)
    obtain ⟨p1, hcall1, -, -, -⟩ :=
      ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
    rw [hcall] at hcall1
    cases hcall1
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm vs k hbnd
      hcommaSt hElems hk
    obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head hElems hk
    rw [hvs] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd v1 (by simp)
    have hbndR : ∀ w ∈ rest, w.depth ≤ depth := by
      intro w hw
      exact hbnd w (by simp [hw])
    obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
      ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
    have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
    rw [hpu] at hval1 hnext1 htok1
    rcases hcont with ⟨hrestnil, hj2k, hbclose⟩ | ⟨hbcomma, hrestG⟩
    · have hskip : skipFrom bs pv.next = j2 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
      have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
        rw [hskip, hbclose]
        simp
      rw [parseElemsTail_stop hstop'] at htail
      cases htail
    · have hskip : skipFrom bs pv.next = j2 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
      have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
        rw [hskip]; exact hbcomma
      have hrest' : Elems .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest k := by
        rw [hskip]; exact hrestG
      obtain ⟨t1, htail1, -, -, -⟩ := ihtm rest k hbndR hcomma' hrest' hk
      rw [htail1] at htail
      cases htail
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail ihm ihtm vs k hbnd
      hcommaSt hElems hk
    obtain ⟨v1, j1, j2, rest, hvs, hv1, hf, hsp, hcont⟩ := elems_head hElems hk
    rw [hvs] at hbnd
    have hbnd1 : v1.depth ≤ depth := hbnd v1 (by simp)
    have hbndR : ∀ w ∈ rest, w.depth ≤ depth := by
      intro w hw
      exact hbnd w (by simp [hw])
    obtain ⟨p1, hcall1, hval1, hnext1, htok1⟩ :=
      ihm v1 j1 hv1 (follow_le_length hf) hbnd1 (follow_numberStop hf)
    have hpu : p1 = pv := parseValue_done_unique hcall1 hcall
    rw [hpu] at hval1 hnext1 htok1
    let t2 : ArrayTail i :=
      { tokens := Token.punct .comma ⟨skipFrom bs i, skipFrom bs i + 1⟩ ::
                    (pv.tokens ++ t.tokens),
        values := pv.value :: t.values, next := t.next,
        moved := by have := t.moved; omega }
    have hres : parseElemsTail bs i depth = .done t2 := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall, htail]
        rfl
      · rename_i hother
        exact absurd hcomma hother
    rcases hcont with ⟨hrestnil, hj2k, hbclose⟩ | ⟨hbcomma, hrestG⟩
    · have hskip : skipFrom bs pv.next = j2 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbclose (by decide)
      have hstop' : bs[skipFrom bs pv.next]? ≠ some 0x2C := by
        rw [hskip, hbclose]
        simp
      have htcanon : t = ⟨[], [], skipFrom bs pv.next, skipFrom_ge bs pv.next⟩ :=
        parseElemsTail_done_unique htail (parseElemsTail_stop hstop')
      have htvals : t.values = [] := by cases htcanon; rfl
      have httoks : t.tokens = [] := by cases htcanon; rfl
      have htnk : t.next = k := by
        cases htcanon
        exact hskip.trans hj2k
      subst hrestnil
      refine ⟨t2, hres, ?_, ?_, ?_⟩
      · rw [hvs]
        simp only [t2, hval1, htvals]
      · simp only [t2]
        rw [htnk]
      · simp only [t2, httoks, hvs, htok1, List.length_cons, List.length_append,
          List.length_nil, elemsCount]
    · have hskip : skipFrom bs pv.next = j2 := by
        rw [hnext1]
        exact skipFrom_eq_of_spaceAt hsp hbcomma (by decide)
      have hcomma' : bs[skipFrom bs pv.next]? = some 0x2C := by
        rw [hskip]; exact hbcomma
      have hrest' : Elems .strict bs (skipFrom bs (skipFrom bs pv.next + 1)) rest k := by
        rw [hskip]; exact hrestG
      obtain ⟨t1, htail1, htval, htnext, httok⟩ := ihtm rest k hbndR hcomma' hrest' hk
      have htt : t1 = t := parseElemsTail_done_unique htail1 htail
      rw [htt] at htval htnext httok
      refine ⟨t2, hres, ?_, ?_, ?_⟩
      · rw [hvs]
        simp only [t2, hval1, htval]
      · simp only [t2]
        rw [htnext]
      · simp only [t2, httok, hvs, htok1, List.length_cons, List.length_append,
          elemsCount]
        omega
  case c31 =>
    intro i depth hnc vs k hbnd hcommaSt hElems hk
    exact absurd (by simpa using hcommaSt) hnc

/-- `parseValue_complete`.  A value the strict grammar derives at `i`, ending inside
the input where no number constituent follows, and no deeper than `depth`, is the
one `parseValue bs i depth` returns: the same value, the same end, and one token per
`Value.tokenCount`. -/
private theorem parseValue_complete (bs : Bytes) (i depth : Nat) :
    ∀ (v : Value) (j : Nat), ValueAt .strict bs i v j → j ≤ bs.length →
      v.depth ≤ depth → NumberStop bs j →
      ∃ p : Parsed i, parseValue bs i depth = .done p ∧ p.value = v ∧ p.next = j ∧
        p.tokens.length = v.tokenCount :=
  (complete_all bs).1 i depth

/-- Completeness inside the limits.  Every text of the accepted language, whose
input, nesting and token count fit, is parsed to a tape that decodes to the same
interpretation.  The policy half is not optional: RFC 8259 §8.2's `"\uDEAD"` is a
`RfcText` this theorem says nothing about, because `Policy` excludes it. -/
theorem parseRef_complete (l : Limits) (bs : Bytes) (v : Value)
    (hvalid : ValidDocument bs v)
    (hinput : bs.length ≤ l.maxInput)
    (hdepth : v.depth ≤ l.maxDepth)
    (htokens : v.tokenCount ≤ l.maxTokens) :
    ∃ t : Tape, parseBytes l bs = .ok t ∧ t.input = bs ∧ decodeTape t = some v := by
  obtain ⟨hrfc, hpolicy⟩ := hvalid
  obtain ⟨i, j, hskip0, hva, hskipj⟩ := (valid_iff_strict bs v).mp ⟨hrfc, hpolicy⟩
  -- `parseBytes` starts at `skipFrom bs 0`; take that as the value's start so the
  -- soundness statement applies to the parse completeness produces.
  subst hskip0
  have hjle : j ≤ bs.length := by rw [← hskipj]; exact skipFrom_ge bs j
  have hstop : NumberStop bs j := numberStop_of_skipFrom_length hskipj
  obtain ⟨p, hpd, hpv, hpn, hpt⟩ :=
    parseValue_complete bs (skipFrom bs 0) l.maxDepth v j hva hjle hdepth hstop
  -- The tape's decode: soundness supplies the decoder equation for the very parse
  -- completeness just produced.
  obtain ⟨hVsnd, -, -⟩ := parse_all bs
  obtain ⟨-, -, -, hdec, -⟩ := (hVsnd (skipFrom bs 0) l.maxDepth).1 p hpd
  have hbom : bs.take 3 ≠ [0xEF, 0xBB, 0xBF] := by
    intro hb3
    have hbom0 : bs[0]? = some 0xEF := by
      have h : (bs.take 3)[0]? = some 0xEF := by rw [hb3]; rfl
      rwa [List.getElem?_take, if_pos (by decide : 0 < 3)] at h
    have hns : IsSpaceB 0xEF = false := by decide
    have hdrop := drop_eq_cons_of_get? hbom0
    have hskip0' : skipFrom bs 0 = 0 := by
      unfold skipFrom
      rw [hdrop]
      simp [spaceRun, hns]
    rw [hskip0'] at hva
    exact valueAt_not_bom hva hbom0
  refine ⟨⟨bs, p.tokens⟩, ?_, rfl, ?_⟩
  · unfold parseBytes
    rw [ite_eq_right (by omega : ¬ bs.length > l.maxInput), ite_eq_right hbom]
    rw [hpd]
    dsimp only
    rw [ite_eq_right (by rw [hpn]; omega : ¬ skipFrom bs p.next < bs.length)]
    rw [ite_eq_left (by rw [hpt]; exact htokens)]
  · obtain ⟨d, hd, hdv, hdr, hdc⟩ := hdec []
    obtain ⟨d', hd', hdv', hdr', hdc'⟩ :=
      decodeValue_cast (l1 := p.tokens ++ []) (l2 := p.tokens) (by simp) hd
    exact decodeTape_of hd' (by rw [hdv', hdv, hpv]) (by rw [hdr', hdr])
      (by rw [hdc', hdc, hpn]; exact hskipj)

/-- `decodeTape_correct`.  Every tape the parser produces decodes, and the value
it decodes to is one the accepted language assigns to the input.  Read with
`tape_valid`, this is the statement that the tape carries the meaning rather than
a private copy of it.  The decoded value is unique because `decodeTape` is a
function; no uniqueness theorem about the grammar is claimed or needed. -/
theorem decodeTape_correct (l : Limits) (bs : Bytes) (t : Tape)
    (h : parseBytes l bs = .ok t) :
    ∃ v : Value, decodeTape t = some v ∧ t.input = bs ∧ ValidDocument bs v := by
  obtain ⟨hin, v, hvalid, hdec⟩ := (parseRef_sound l bs).1 t h
  exact ⟨v, hdec, hin, hvalid⟩

/-! ### The two adherence theorems -/

/-- Conventions followed, forward direction.  Everything this API accepts is an
RFC 8259 JSON text, with an interpretation.  `parseRef_sound` read through
`ValidDocument`'s first conjunct; it is the statement that the accepted language
is a subset of RFC 8259's, and it is unaffected by limit outcomes, which say
nothing about validity either way. -/
theorem accepted_is_rfc_text (l : Limits) (bs : Bytes) (t : Tape)
    (h : parseBytes l bs = .ok t) :
    ∃ v : Value, RfcText bs v ∧ decodeTape t = some v := by
  obtain ⟨-, v, ⟨hrfc, -⟩, hdec⟩ := (parseRef_sound l bs).1 t h
  exact ⟨v, hrfc, hdec⟩

/-- Conventions followed, backward direction.  Every RFC 8259 text whose
interpretation satisfies `Policy`, inside the stated resource limits, is accepted
and decodes to that interpretation.  Three qualifications are load-bearing and
each is a clause, not a caveat: `Policy` (RFC 8259 §8.2's `"\uDEAD"` is a text we
refuse, so this is not §9's unconditional `MUST`), the limits (§9 permits an
implementation to bound size and depth, and without them the implication is
false), and the interpretation (`RfcText` is a relation, so the sentence speaks
of a reading, not of the bytes alone). -/
theorem rfc_text_accepted_on_policy (l : Limits) (bs : Bytes) (v : Value)
    (hrfc : RfcText bs v) (hpolicy : Policy v)
    (hinput : bs.length ≤ l.maxInput) (hdepth : v.depth ≤ l.maxDepth)
    (htokens : v.tokenCount ≤ l.maxTokens) :
    ∃ t : Tape, parseBytes l bs = .ok t ∧ decodeTape t = some v := by
  obtain ⟨t, hok, -, hdec⟩ :=
    parseRef_complete l bs v ⟨hrfc, hpolicy⟩ hinput hdepth htokens
  exact ⟨t, hok, hdec⟩

/-! ### Two corollaries and the lexeme statement -/

/-- A length limit is decided from the length alone, before any syntax check, so
it cannot be a syntax fault in disguise. -/
theorem parseRef_inputTooLong (l : Limits) (bs : Bytes) (h : l.maxInput < bs.length) :
    parseBytes l bs = .error .inputTooLong := by
  unfold parseBytes
  rw [if_pos (by omega)]

/-- A valid in-limit document is never reported invalid.  This is the separation
`parseRef_sound` and `parseRef_complete` give between the two families of
outcomes. -/
theorem parseRef_not_invalid_on_valid (l : Limits) (bs : Bytes) (v : Value)
    (hvalid : ValidDocument bs v) (hinput : bs.length ≤ l.maxInput)
    (hdepth : v.depth ≤ l.maxDepth) (htokens : v.tokenCount ≤ l.maxTokens)
    (r : Reject) : parseBytes l bs ≠ .error (.invalid r) := by
  intro hbad
  obtain ⟨t, hok, -⟩ := parseRef_complete l bs v hvalid hinput hdepth htokens
  rw [hok] at hbad
  exact ParseResult.noConfusion hbad

/-- Lexeme preservation.  A decoded number's lexeme is exactly the bytes its token
spans: the number case takes the lexeme from the input and requires the span to
cover it.  This is where "numbers keep their source lexeme" is a theorem rather
than a hope; §3.3 says why it is not a `Policy` clause. -/
theorem decoded_number_is_span_bytes (bs : Bytes) (i : Nat) (s : Span)
    (rest : List Token) (d : Decoded (.number s :: rest))
    (h : decodeValue bs i (.number s :: rest) = some d) :
    ∃ lex : Bytes, d.value = .number lex ∧
      lex = (bs.drop s.start).take (s.stop - s.start) := by
  rw [decodeValue] at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hs, -⟩ := hcond
    injection h with hd
    subst hd
    subst hs
    refine ⟨numRun (bs.drop i), rfl, ?_⟩
    have hp := (numRun_spec (bs.drop i)).1
    show numRun (bs.drop i) = (bs.drop i).take (i + (numRun (bs.drop i)).length - i)
    rw [Nat.add_sub_cancel_left]
    exact hp.symm
  · exact absurd h (by simp)

/-! ### The string half of the zero-copy seam -/

/-- The string half of the zero-copy seam.  A decoded string's code points are
exactly the decoding of the raw literal its token spans, and the span runs from the
opening quote to one past the closing one. -/
theorem decoded_string_is_span_literal (bs : Bytes) (i : Nat) (s : Span)
    (rest : List Token) (d : Decoded (.string s :: rest))
    (h : decodeValue bs i (.string s :: rest) = some d) :
    ∃ (cs : List Nat) (j : Nat), d.value = .string cs ∧ s = ⟨i, j⟩ ∧
      StringAt .strict bs i j cs := by
  rw [decodeValue] at h
  split at h
  · exact absurd h (by simp)
  · rename_i cs after hs
    dsimp only at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hq, hspan⟩ := hcond
      injection h with hd
      subst hd
      have hstr : StrChars .strict (bs.drop (i + 1)) cs after :=
        (scanChars_iff (bs.drop (i + 1)) cs after).mp hs
      refine ⟨cs, bs.length - after.length, rfl, hspan, ?_⟩
      unfold StringAt
      refine ⟨hq, after, hstr, ?_⟩
      obtain ⟨pre, hp⟩ := strChars_split hstr
      have hsuffix : ∃ pre', bs = pre' ++ after :=
        ⟨bs.take (i + 1) ++ pre, by
          rw [List.append_assoc, ← hp, List.take_append_drop]⟩
      obtain ⟨pre', hpre'⟩ := hsuffix
      exact drop_of_split hpre'
    · exact absurd h (by simp)

end LeanLLVM.JSON

