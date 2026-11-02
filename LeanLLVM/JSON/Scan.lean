/-
The scanners: the computable reflections of the string and number productions.

The string scanner returns the refusal reason, because the contract's diagnostic
row names `Policy` refusals (`unpairedSurrogate`, `noncharacter`) and the scenario
asserts them.  The number scan needs no reason type: a number has one refusal.
-/
import LeanLLVM.JSON.Spec

namespace LeanLLVM.JSON

/-- Why a string body was refused.  The offset is relative to the subject;
`parseString` adds the opening quote's index.  No theorem depends on the reason or
the offset — the contract's diagnostics row leaves them out of the equivalence —
so this type exists for the executable's report and for the scenario's assertions.
`ended` is the one reason that is about the subject running out rather than about
a byte: it is what makes `Reject.unterminatedString` reachable. -/
inductive ScanError where
  | ended
  | badEscape (offset : Nat)
  | badUTF8 (offset : Nat)
  | controlCharacter (offset : Nat)
  | unpairedSurrogate (offset : Nat)
  | noncharacter (offset : Nat)
deriving DecidableEq, Repr

mutual

/-- Decode a string body — the bytes after the opening quote — to the code points
and the remainder, which begins *after* the closing quote (`StrChars`'s `nil`
clause consumes it), or say why it was refused.  The discipline is `StrChar
.strict`, so an unpaired escape and a noncharacter are refused with their own
reasons, and a subject that ends before the quote is `ended`.  `off` is the
position of the argument within the body, so a refusal can name it. -/
def scanCharsFrom (off : Nat) : Bytes → Except ScanError (List Nat × Bytes)
  | [] => .error .ended
  | 0x22 :: rest => .ok ([], rest)
  | 0x5C :: rest =>
      match rest with
      | [] => .error .ended
      | e :: rest1 =>
          match EscVal e with
          | some c => scanCons off (off + 2) c rest1
          | none =>
              if e = 0x75 then
                match rest1 with
                | h0 :: h1 :: h2 :: h3 :: rest2 =>
                    match Hex4 h0 h1 h2 h3 with
                    | some c =>
                        if 0xD800 ≤ c ∧ c ≤ 0xDBFF then
                          match rest2 with
                          | 0x5C :: 0x75 :: l0 :: l1 :: l2 :: l3 :: rest3 =>
                              match Hex4 l0 l1 l2 l3 with
                              | some lo =>
                                  if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                                    scanCons off (off + 12)
                                      (0x10000 + (c - 0xD800) * 0x400 + (lo - 0xDC00))
                                      rest3
                                  else .error (.unpairedSurrogate off)
                              | none => .error (.badEscape (off + 8))
                          | _ => .error (.unpairedSurrogate off)
                        else if 0xDC00 ≤ c ∧ c ≤ 0xDFFF then
                          .error (.unpairedSurrogate off)
                        else scanCons off (off + 6) c rest2
                    | none => .error (.badEscape (off + 2))
                | _ => .error .ended
              else .error (.badEscape off)
  | b :: rest =>
      if b.toNat < 0x80 then
        if 0x20 ≤ b.toNat then scanCons off (off + 1) b.toNat rest
        else .error (.controlCharacter off)
      else if 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF then
        match rest with
        | b1 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then
              scanCons off (off + 2)
                ((b.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | [] => .error .ended
      else if b = 0xE0 then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              scanCons off (off + 3)
                ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              scanCons off (off + 3)
                ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xED then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              scanCons off (off + 3)
                (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF then
        match rest with
        | b1 :: b2 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
              scanCons off (off + 3)
                ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xF0 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              scanCons off (off + 4)
                ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
                  (b3.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              scanCons off (off + 4)
                ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
                  (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else if b = 0xF4 then
        match rest with
        | b1 :: b2 :: b3 :: rest1 =>
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧
                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
              scanCons off (off + 4)
                (0x100000 + (b1.toNat - 0x80) * 0x1000 +
                  (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1
            else .error (.badUTF8 off)
        | _ => .error .ended
      else .error (.badUTF8 off)

/-- The continuation of an accepted character: RFC 7493 §2.1 refuses a
noncharacter wherever it appears, so every accepting branch funnels here. -/
def scanCons (pos next : Nat) (c : Nat) (rest : Bytes) :
    Except ScanError (List Nat × Bytes) :=
  if IsNoncharacter c then .error (.noncharacter pos)
  else
    match scanCharsFrom next rest with
    | .error e => .error e
    | .ok (cs, fin) => .ok (c :: cs, fin)

end

/-- The string scanner at the start of a body. -/
def scanChars (bs : Bytes) : Except ScanError (List Nat × Bytes) :=
  scanCharsFrom 0 bs

/-! ### The number lexeme

`numLexB` decides the whole of RFC 8259 §6 on a lexeme: the leading `minus`, the
`int` with its `zero`/`digit1-9 *DIGIT` split, and the optional fraction and
exponent.  It is not a prefix matcher — the lexeme must be exhausted, which is
what makes `1.2.3` and `01` refusals rather than accepted prefixes. -/

/-- `*DIGIT` consumes the whole argument. -/
def allDigitsB : Bytes → Bool
  | [] => true
  | b :: rest => IsDigitB b && allDigitsB rest

/-- `1*DIGIT` consumes the whole argument. -/
def digits1B : Bytes → Bool
  | [] => false
  | b :: rest => IsDigitB b && allDigitsB rest

/-- The bytes after an `e`: `[ minus / plus ] 1*DIGIT`, exhausted. -/
def expB : Bytes → Bool
  | [] => false
  | b :: rest => if b = 0x2B ∨ b = 0x2D then digits1B rest else digits1B (b :: rest)

/-- The bytes after a fraction's digits: an optional exponent, exhausted. -/
def expTailB : Bytes → Bool
  | [] => true
  | b :: rest =>
      if decide (b = 0x65) || decide (b = 0x45) then expB rest else false

/-- The bytes after an `int`: an optional fraction, an optional exponent,
exhausted. -/
def numSuffixB : Bytes → Bool
  | [] => true
  | b :: rest =>
      if decide (b = 0x2E) then
        digits1B (rest.takeWhile IsDigitB) && expTailB (rest.dropWhile IsDigitB)
      else if decide (b = 0x65) || decide (b = 0x45) then expB rest
      else false

/-- `[ minus ] int [ frac ] [ exp ]`, exhausted. -/
def numLexB (lex : Bytes) : Bool :=
  match lex with
  | [] => numBodyB []
  | b :: rest =>
      if decide (b = 0x2D) then numBodyB rest else numBodyB (b :: rest)

where
  /-- `int [ frac ] [ exp ]`, exhausted. -/
  numBodyB : Bytes → Bool
    | [] => false
    | b :: rest =>
        if decide (b = 0x30) then numSuffixB rest
        else if 0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39 then
          numSuffixB (rest.dropWhile IsDigitB)
        else false


theorem digits_all : ∀ {bs : Bytes}, Digits bs → ∀ b ∈ bs, IsDigitB b = true
  | _, .one h, b, hb => by
      simp at hb; subst hb; exact h
  | _, .more h _, b, hb => by
      simp at hb
      rcases hb with rfl | hb
      · exact h
      · exact digits_all ‹_› b hb

theorem digits0_all : ∀ {bs : Bytes}, Digits0 bs → ∀ b ∈ bs, IsDigitB b = true
  | _, .nil, b, hb => by simp at hb
  | _, .more h hr, b, hb => by
      simp at hb
      rcases hb with rfl | hb
      · exact h
      · exact digits0_all hr b hb

theorem digits0_to_digits : ∀ {bs : Bytes}, Digits0 bs → bs ≠ [] → Digits bs
  | [], _, hne => absurd rfl hne
  | b :: rest, h, _ => by
      cases h with
      | more hb hr =>
          cases rest with
          | nil => exact .one hb
          | cons c cs => exact .more hb (digits0_to_digits hr (by simp))

theorem allDigitsB_spec : ∀ {bs : Bytes}, allDigitsB bs = true → Digits0 bs
  | [], _ => .nil
  | b :: rest, h => by
      simp only [allDigitsB, Bool.and_eq_true] at h
      exact .more h.1 (allDigitsB_spec h.2)

theorem digits1B_spec : ∀ {bs : Bytes}, digits1B bs = true → Digits bs
  | [], h => by simp [digits1B] at h
  | b :: rest, h => by
      simp only [digits1B, Bool.and_eq_true] at h
      cases rest with
      | nil => exact .one h.1
      | cons c cs =>
          exact .more h.1 (digits0_to_digits (allDigitsB_spec h.2) (by simp))

theorem allDigitsB_complete : ∀ {bs : Bytes}, Digits0 bs → allDigitsB bs = true
  | [], .nil => rfl
  | b :: rest, .more h hr => by
      simp only [allDigitsB, h, allDigitsB_complete hr, Bool.true_and, Bool.and_true]

theorem digits1B_complete : ∀ {bs : Bytes}, Digits bs → digits1B bs = true
  | _, .one h => by simp [digits1B, allDigitsB, h]
  | _, .more h hr => by
      simp only [digits1B, h, Bool.true_and]
      exact allDigitsB_complete (digits0_to_digits0_of_digits hr)
where
  digits0_to_digits0_of_digits : ∀ {bs : Bytes}, Digits bs → Digits0 bs
    | _, .one h => .more h .nil
    | _, .more h hr => .more h (digits0_to_digits0_of_digits hr)

theorem digits0_takeWhile (bs : Bytes) : Digits0 (bs.takeWhile IsDigitB) := by
  induction bs with
  | nil => simp [Digits0.nil]
  | cons b rest ih =>
      rw [List.takeWhile_cons]
      split
      · rename_i hb
        exact .more hb ih
      · exact .nil

theorem dropWhile_digits : ∀ {bs : Bytes}, Digits0 bs → bs.dropWhile IsDigitB = []
  | [], .nil => rfl
  | b :: rest, .more h hr => by
      rw [List.dropWhile_cons]
      simp [h, dropWhile_digits hr]

theorem takeWhile_digits : ∀ {bs : Bytes}, Digits0 bs → bs.takeWhile IsDigitB = bs
  | [], .nil => rfl
  | b :: rest, .more h hr => by
      rw [List.takeWhile_cons]
      simp [h, takeWhile_digits hr]

theorem eq_takeWhile_of_dropWhile_eq_nil {bs : Bytes} (h : bs.dropWhile IsDigitB = []) :
    bs = bs.takeWhile IsDigitB := by
  have hsplit := List.takeWhile_append_dropWhile (p := IsDigitB) (l := bs)
  rw [h, List.append_nil] at hsplit
  exact hsplit.symm

theorem expB_spec {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {bs : Bytes}
    (h : expB bs = true) : ExpPart (e :: bs) := by
  cases bs with
  | nil => exact absurd h (by simp [expB])
  | cons b rest =>
      rw [expB] at h
      by_cases hs : b = 0x2B ∨ b = 0x2D
      · rw [if_pos hs] at h
        have hd := digits1B_spec h
        refine ExpPart.mk (e := e) (sign := [b]) (ds := rest) he ?_ hd
        rcases hs with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rw [if_neg hs] at h
        have hd := digits1B_spec h
        exact ExpPart.mk (e := e) (sign := []) (ds := b :: rest) he (Or.inl rfl) hd

theorem expTailB_spec {bs : Bytes} (h : expTailB bs = true) :
    bs = [] ∨ ExpPart bs := by
  match bs with
  | [] => exact Or.inl rfl
  | b :: rest =>
      rw [expTailB] at h
      split at h
      · rename_i hcond
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with rfl | rfl
        · exact Or.inr (expB_spec (Or.inl rfl) h)
        · exact Or.inr (expB_spec (Or.inr rfl) h)
      · exact absurd h (by simp)

theorem numSuffixB_spec {ip : Bytes} (hi : IntPart ip) :
    ∀ {suf : Bytes}, numSuffixB suf = true → NumBody (ip ++ suf)
  | [], _ => by simpa using NumBody.plain hi
  | b :: rest, h => by
      rw [numSuffixB] at h
      split at h
      · rename_i hdot
        simp only [decide_eq_true_eq] at hdot
        subst hdot
        simp only [Bool.and_eq_true] at h
        have hf : Digits (rest.takeWhile IsDigitB) := digits1B_spec h.1
        have hsplit : rest.takeWhile IsDigitB ++ rest.dropWhile IsDigitB = rest :=
          List.takeWhile_append_dropWhile
        rcases expTailB_spec h.2 with he | he
        · have hrest : rest = rest.takeWhile IsDigitB :=
            eq_takeWhile_of_dropWhile_eq_nil he
          have hb : NumBody (ip ++ 0x2E :: rest.takeWhile IsDigitB) := NumBody.frac hi hf
          have hEq : ip ++ 0x2E :: rest.takeWhile IsDigitB = ip ++ 0x2E :: rest := by
            rw [← hrest]
          rwa [hEq] at hb
        · have hb : NumBody (ip ++ 0x2E :: rest.takeWhile IsDigitB ++
              rest.dropWhile IsDigitB) := NumBody.fracExp hi hf he
          simpa [hsplit] using hb
      · split at h
        · rename_i hexp
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hexp
          rcases hexp with rfl | rfl
          · exact NumBody.exp hi (expB_spec (Or.inl rfl) h)
          · exact NumBody.exp hi (expB_spec (Or.inr rfl) h)
        · exact absurd h (by simp)

theorem numBodyB_spec : ∀ {bs : Bytes}, numLexB.numBodyB bs = true → NumBody bs
  | [], h => by simp [numLexB.numBodyB] at h
  | b :: rest, h => by
      rw [numLexB.numBodyB] at h
      split at h
      · rename_i hzero
        simp only [decide_eq_true_eq] at hzero
        subst hzero
        simpa using numSuffixB_spec (IntPart.zero) h
      · split at h
        · rename_i hd
          have htake : Digits0 (rest.takeWhile IsDigitB) := digits0_takeWhile rest
          have hsplit : rest.takeWhile IsDigitB ++ rest.dropWhile IsDigitB = rest :=
            List.takeWhile_append_dropWhile
          have hip : IntPart (b :: rest.takeWhile IsDigitB) :=
            IntPart.lead hd.1 hd.2 htake
          have hbody := numSuffixB_spec hip h
          simpa [hsplit] using hbody
        · exact absurd h (by simp)

theorem digits0_of_digits : ∀ {bs : Bytes}, Digits bs → Digits0 bs
  | _, .one h => .more h .nil
  | _, .more h hr => .more h (digits0_of_digits hr)

theorem expB_digits {ds : Bytes} (hd : Digits ds) : expB ds = true := by
  cases ds with
  | nil => cases hd
  | cons b rest =>
      have hb : IsDigitB b = true := digits_all hd b (by simp)
      have hnot : ¬ (b = 0x2B ∨ b = 0x2D) := by
        intro h
        rcases h with rfl | rfl <;> simp [IsDigitB] at hb
      rw [expB]
      rw [if_neg hnot]
      exact digits1B_complete hd

theorem expB_complete {sign ds : Bytes}
    (hs : sign = [] ∨ sign = [0x2B] ∨ sign = [0x2D]) (hd : Digits ds) :
    expB (sign ++ ds) = true := by
  rcases hs with h | h | h
  · subst h; simpa using expB_digits hd
  · subst h
    show expB (0x2B :: ds) = true
    rw [expB]
    rw [if_pos (Or.inl rfl)]
    exact digits1B_complete hd
  · subst h
    show expB (0x2D :: ds) = true
    rw [expB]
    rw [if_pos (Or.inr rfl)]
    exact digits1B_complete hd

theorem digits_takeWhile_empty {e : UInt8} (he : e = 0x65 ∨ e = 0x45) (rest : Bytes) :
    (e :: rest).takeWhile IsDigitB = [] := by
  rw [List.takeWhile_cons]
  have h : IsDigitB e = false := by rcases he with rfl | rfl <;> rfl
  simp [h]

theorem digits_dropWhile_self {e : UInt8} (he : e = 0x65 ∨ e = 0x45) (rest : Bytes) :
    (e :: rest).dropWhile IsDigitB = e :: rest := by
  rw [List.dropWhile_cons]
  have h : IsDigitB e = false := by rcases he with rfl | rfl <;> rfl
  simp [h]

theorem expPart_takeWhile_nil {es : Bytes} (h : ExpPart es) :
    es.takeWhile IsDigitB = [] := by
  cases h with
  | mk he hs hd => exact digits_takeWhile_empty he _

theorem expPart_dropWhile_self {es : Bytes} (h : ExpPart es) :
    es.dropWhile IsDigitB = es := by
  cases h with
  | mk he hs hd => exact digits_dropWhile_self he _

theorem numSuffixB_frac {fs : Bytes} (hf : Digits fs) :
    numSuffixB (0x2E :: fs) = true := by
  have h0 : Digits0 fs := digits0_of_digits hf
  have ht : fs.takeWhile IsDigitB = fs := takeWhile_digits h0
  have hd : fs.dropWhile IsDigitB = [] := dropWhile_digits h0
  show numSuffixB (0x2E :: fs) = true
  simp [numSuffixB, expTailB, ht, hd, digits1B_complete hf]

theorem numSuffixB_exp {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {sign ds : Bytes}
    (hs : sign = [] ∨ sign = [0x2B] ∨ sign = [0x2D]) (hd : Digits ds) :
    numSuffixB (e :: sign ++ ds) = true := by
  have hne : decide (e = 0x2E) = false := by
    rcases he with rfl | rfl <;> rfl
  have hyes : (decide (e = 0x65) || decide (e = 0x45)) = true := by
    rcases he with rfl | rfl <;> rfl
  show numSuffixB (e :: (sign ++ ds)) = true
  simp [numSuffixB, hne, hyes, expB_complete hs hd]

theorem expTailB_exp {e : UInt8} (he : e = 0x65 ∨ e = 0x45) {sign ds : Bytes}
    (hs : sign = [] ∨ sign = [0x2B] ∨ sign = [0x2D]) (hd : Digits ds) :
    expTailB (e :: sign ++ ds) = true := by
  have hyes : (decide (e = 0x65) || decide (e = 0x45)) = true := by
    rcases he with rfl | rfl <;> rfl
  show expTailB (e :: (sign ++ ds)) = true
  simp [expTailB, hyes, expB_complete hs hd]

theorem expPart_expTailB {es : Bytes} (h : ExpPart es) : expTailB es = true := by
  cases h with
  | mk he hs hd => exact expTailB_exp he hs hd

theorem expPart_numSuffixB {es : Bytes} (h : ExpPart es) : numSuffixB es = true := by
  cases h with
  | mk he hs hd => exact numSuffixB_exp he hs hd

theorem numSuffixB_fracExp {fs es : Bytes} (hf : Digits fs) (he : ExpPart es) :
    numSuffixB (0x2E :: fs ++ es) = true := by
  have h0 : Digits0 fs := digits0_of_digits hf
  have hall : ∀ a ∈ fs, IsDigitB a = true := digits0_all h0
  have htake : (fs ++ es).takeWhile IsDigitB = fs := by
    rw [List.takeWhile_append_of_pos hall, expPart_takeWhile_nil he, List.append_nil]
  have hdrop : (fs ++ es).dropWhile IsDigitB = es := by
    rw [List.dropWhile_append_of_pos hall]
    exact expPart_dropWhile_self he
  have hd1 : digits1B fs = true := digits1B_complete hf
  have hexp : expTailB es = true := expPart_expTailB he
  show numSuffixB (0x2E :: (fs ++ es)) = true
  simp [numSuffixB, htake, hdrop, hd1, hexp]

theorem numSuffixB_nodigit {suf : Bytes} (h : numSuffixB suf = true) :
    suf = [] ∨ ∀ (b : UInt8) (rest : Bytes), suf = b :: rest → IsDigitB b = false := by
  cases suf with
  | nil => exact Or.inl rfl
  | cons b rest =>
      rw [numSuffixB] at h
      split at h
      · rename_i hdot
        have hb : b = 0x2E := by simpa using hdot
        subst hb
        exact Or.inr (fun b' rest' he => by
          injection he with hb' _
          subst hb'
          rfl)
      · split at h
        · rename_i hexp
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hexp
          exact Or.inr (fun b' rest' he => by
            injection he with hb' _
            subst hb'
            rcases hexp with rfl | rfl <;> rfl)
        · exact absurd h (by simp)

theorem digits_dropWhile_notdigit {rest suf : Bytes} (hr : Digits0 rest)
    (hs : suf = [] ∨ ∀ (b : UInt8) (rest' : Bytes), suf = b :: rest' → IsDigitB b = false) :
    (rest ++ suf).dropWhile IsDigitB = suf := by
  rw [List.dropWhile_append_of_pos (digits0_all hr)]
  rcases hs with rfl | hs
  · rfl
  · cases suf with
    | nil => rfl
    | cons b rest' =>
        rw [List.dropWhile_cons]
        have hb := hs b rest' rfl
        simp [hb]

theorem numBodyB_int {ip suf : Bytes} (hi : IntPart ip) (hsuf : numSuffixB suf = true) :
    numLexB.numBodyB (ip ++ suf) = true := by
  cases ip with
  | nil => cases hi
  | cons b bs =>
      cases hi with
      | zero =>
          show numLexB.numBodyB (([0x30] : Bytes) ++ suf) = true
          simp [numLexB.numBodyB, hsuf]
      | lead h1 h2 hr =>
          have hne' : ¬ (b = 0x30) := by
            intro hc
            rw [hc] at h1
            exact absurd h1 (by decide)
          have hdigit : (0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39) := by
            constructor
            · rwa [UInt8.le_iff_toNat_le] at h1
            · rwa [UInt8.le_iff_toNat_le] at h2
          show numLexB.numBodyB (b :: (bs ++ suf)) = true
          simp only [numLexB.numBodyB]
          rw [if_neg (by simp [hne']), if_pos hdigit]
          rw [digits_dropWhile_notdigit hr (numSuffixB_nodigit hsuf)]
          exact hsuf

theorem numBodyB_complete {bs : Bytes} (h : NumBody bs) : numLexB.numBodyB bs = true := by
  cases h with
  | plain hi => simpa using numBodyB_int (suf := []) hi (by rfl)
  | frac hi hf => exact numBodyB_int (suf := 0x2E :: _) hi (numSuffixB_frac hf)
  | exp hi he => exact numBodyB_int (suf := _) hi (expPart_numSuffixB he)
  | fracExp hi hf he =>
      simpa [List.append_assoc] using
        numBodyB_int (suf := 0x2E :: _) hi (numSuffixB_fracExp hf he)

theorem numLexB_spec {lex : Bytes} (h : numLexB lex = true) : RfcNumber lex := by
  match lex with
  | [] => simp [numLexB, numLexB.numBodyB] at h
  | b :: rest =>
      rw [numLexB] at h
      split at h
      · rename_i hminus
        have hb : b = 0x2D := by simpa using hminus
        subst hb
        exact RfcNumber.neg (numBodyB_spec h)
      · exact RfcNumber.pos (numBodyB_spec h)

theorem numLexB_complete {lex : Bytes} (h : RfcNumber lex) : numLexB lex = true := by
  cases h with
  | pos hb =>
      cases lex with
      | nil => exact absurd (numBodyB_complete hb) (by simp [numLexB.numBodyB])
      | cons b rest =>
          rw [numLexB]
          have hnot : decide (b = 0x2D) = false := by
            by_cases hb2d : b = 0x2D
            · exfalso
              subst hb2d
              have htrue := numBodyB_complete hb
              simp [numLexB.numBodyB] at htrue
            · simp [hb2d]
          rw [if_neg (by simp [hnot])]
          exact numBodyB_complete hb
  | neg hb =>
      simp [numLexB, numBodyB_complete hb]

theorem numLexB_iff (lex : Bytes) : numLexB lex = true ↔ RfcNumber lex :=
  ⟨numLexB_spec, numLexB_complete⟩

/-! ### Reflection lemmas

The scanners' specifications.  `scanChars_iff` is stated on the success side,
which is the side the theorems consume; the failure side adds nothing to what the
theorems know, because it is the complement. -/

/-! #### The scanner's equations

One equation per accepting branch: `scanCharsFrom` reduced by
`scanCharsFrom.eq_def` under that branch's side conditions.  The branches are
stated in the relation's own terms (`UInt8` bounds and the `Utf8Char` value
formulas), so completeness can apply them to a `StrChars` derivation's
`StrChar` directly. -/

theorem le_toNat {a b : UInt8} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  UInt8.le_iff_toNat_le.mp h

theorem scanCharsFrom_nil (off : Nat) : scanCharsFrom off ([] : Bytes) = .error .ended := by
  simp only [scanCharsFrom.eq_def]

theorem scanCharsFrom_quote (off : Nat) (rest : Bytes) :
    scanCharsFrom off (0x22 :: rest) = .ok ([], rest) := by
  simp only [scanCharsFrom.eq_def]

theorem scanCharsFrom_ascii (off : Nat) (b : UInt8) (rest : Bytes)
    (hq : b ≠ 0x22) (hs : b ≠ 0x5C) (h1 : b < 0x80) (h2 : 0x20 ≤ b.toNat) :
    scanCharsFrom off (b :: rest) = scanCons off (off + 1) b.toNat rest := by
  have h1' : b.toNat < 0x80 := UInt8.lt_iff_toNat_lt.mp h1
  simp only [scanCharsFrom.eq_def]
  simp [h1', h2]

theorem scanCharsFrom_escape (off : Nat) (e : UInt8) (rest1 : Bytes) (c : Nat)
    (hv : EscVal e = some c) :
    scanCharsFrom off (0x5C :: e :: rest1) = scanCons off (off + 2) c rest1 := by
  simp only [scanCharsFrom.eq_def]
  simp [hv]

theorem scanCharsFrom_uchar (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (c : Nat)
    (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some c)
    (hhi : ¬ (0xD800 ≤ c ∧ c ≤ 0xDBFF))
    (hlo : ¬ (0xDC00 ≤ c ∧ c ≤ 0xDFFF)) :
    scanCharsFrom off (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: rest2) =
      scanCons off (off + 6) c rest2 := by
  simp only [scanCharsFrom.eq_def, hv]
  simp [hx, hhi, hlo]

theorem scanCharsFrom_pair (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8)
    (rest3 : Bytes) (hi lo : Nat)
    (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some hi) (hy : Hex4 l0 l1 l2 l3 = some lo)
    (hh : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hl : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF) :
    scanCharsFrom off
        (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: 0x5C :: 0x75 ::
          l0 :: l1 :: l2 :: l3 :: rest3) =
      scanCons off (off + 12) (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) rest3 := by
  simp only [scanCharsFrom.eq_def, hv]
  simp [hx, hy, hh, hl]

theorem scanCharsFrom_utf8_two (off : Nat) (b0 b1 : UInt8) (rest1 : Bytes)
    (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF) (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) :
    scanCharsFrom off (b0 :: b1 :: rest1) =
      scanCons off (off + 2) ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest1 := by
  have h0n : (0xC2 : Nat) ≤ b0.toNat := by simpa using le_toNat h0
  have h0n' : b0.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have hq : b0 ≠ 0x22 := by intro h; subst h; simp at h0n
  have hs : b0 ≠ 0x5C := by intro h; subst h; simp at h0n
  have hlt : ¬ b0.toNat < 0x80 := by omega
  simp only [scanCharsFrom.eq_def]
  simp [hlt, h0n, h0n', h1n, h1n']

theorem scanCharsFrom_utf8_e0 (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0xA0 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (0xE0 :: b1 :: b2 :: rest1) =
      scanCons off (off + 3) ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := by
  have h1n : (0xA0 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  simp only [scanCharsFrom.eq_def]
  simp [h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_e1ec (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (b :: b1 :: b2 :: rest1) =
      scanCons off (off + 3)
        ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest1 := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  simp only [scanCharsFrom.eq_def]
  simp [hlt, htwo, he0, hbn, hbn', h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_ed (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x9F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (0xED :: b1 :: b2 :: rest1) =
      scanCons off (off + 3)
        (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x9F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  simp only [scanCharsFrom.eq_def]
  simp [h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_eeef (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
    scanCharsFrom off (b :: b1 :: b2 :: rest1) =
      scanCons off (off + 3)
        ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest1 := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  simp only [scanCharsFrom.eq_def]
  simp [hlt, htwo, he0, h31, hed, hbn, hbn', h1n, h1n', h2n, h2n']

theorem scanCharsFrom_utf8_f0 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x90 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (0xF0 :: b1 :: b2 :: b3 :: rest1) =
      scanCons off (off + 4)
        ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest1 := by
  have h1n : (0x90 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  simp only [scanCharsFrom.eq_def]
  simp [h1n, h1n', h2n, h2n', h3n, h3n']

theorem scanCharsFrom_utf8_f1f3 (off : Nat) (b b1 b2 b3 : UInt8) (rest1 : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (b :: b1 :: b2 :: b3 :: rest1) =
      scanCons off (off + 4)
        ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  have hq : b ≠ 0x22 := by intro h; subst h; simp at hbn
  have hs : b ≠ 0x5C := by intro h; subst h; simp at hbn
  have hlt : ¬ b.toNat < 0x80 := by omega
  have htwo : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) := by omega
  have he0 : b ≠ 0xE0 := by intro h; subst h; simp at hbn
  have h31 : ¬ (0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC) := by omega
  have hed : b ≠ 0xED := by intro h; subst h; simp at hbn
  have h33 : ¬ (0xEE ≤ b.toNat ∧ b.toNat ≤ 0xEF) := by omega
  have hf0 : b ≠ 0xF0 := by intro h; subst h; simp at hbn
  simp only [scanCharsFrom.eq_def]
  simp [hlt, htwo, he0, h31, hed, h33, hf0, hbn, hbn', h1n, h1n', h2n, h2n', h3n, h3n']

theorem scanCharsFrom_utf8_f4 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x8F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
    scanCharsFrom off (0xF4 :: b1 :: b2 :: b3 :: rest1) =
      scanCons off (off + 4)
        (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest1 := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x8F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  simp only [scanCharsFrom.eq_def]
  simp [h1n, h1n', h2n, h2n', h3n, h3n']

/-! #### Character and byte facts

The strict character policy on the relation's side, and the arithmetic the branch
conditions imply for the bytes they constrain. -/

theorem strict_noncharacter {n : Nat} (h : ModeAllows .strict n) :
    IsNoncharacter n = false := by
  simp only [ModeAllows, CharAllowed] at h
  exact h.2

theorem charAllowed_of {n : Nat} (hs : IsScalar n) (hn : IsNoncharacter n = false) :
    ModeAllows .strict n :=
  ⟨hs, hn⟩

theorem high_ne_of_scalar {n : Nat} (h : IsScalar n) : ¬ (0xD800 ≤ n ∧ n ≤ 0xDBFF) := by
  obtain ⟨_, h'⟩ := h
  rintro ⟨a, b⟩
  exact h' ⟨a, by omega⟩

theorem low_ne_of_scalar {n : Nat} (h : IsScalar n) : ¬ (0xDC00 ≤ n ∧ n ≤ 0xDFFF) := by
  obtain ⟨_, h'⟩ := h
  rintro ⟨a, b⟩
  exact h' ⟨by omega, b⟩

theorem escVal_noncharacter {e : UInt8} {c : Nat} (h : EscVal e = some c) :
    IsNoncharacter c = false := by
  unfold EscVal at h
  split at h <;> (first | (simp_all only [Option.some.injEq]; subst_vars; decide) | simp_all)

theorem byte_ne_quote {b : UInt8} (h : b.toNat ≠ 0x22) : b ≠ 0x22 := by
  intro hb
  exact h (congrArg UInt8.toNat hb)

theorem byte_ne_backslash {b : UInt8} (h : b.toNat ≠ 0x5C) : b ≠ 0x5C := by
  intro hb
  exact h (congrArg UInt8.toNat hb)

theorem hexVal_le {b : UInt8} {v : Nat} (h : HexVal b = some v) : v ≤ 15 := by
  unfold HexVal at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
      UInt8.toNat_ofNat] at hd
    omega
  · rename_i hd
    split at h
    · rename_i hu
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
        UInt8.toNat_ofNat] at hu
      omega
    · split at h
      · rename_i hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
          UInt8.toNat_ofNat] at hl
        omega
      · simp at h

theorem hex4_le {a b c d : UInt8} {n : Nat} (h : Hex4 a b c d = some n) : n ≤ 0xFFFF := by
  unfold Hex4 at h
  split at h
  · rename_i x y z w hx hy hz hw
    simp only [Option.some.injEq] at h
    subst h
    have hx' := hexVal_le hx
    have hy' := hexVal_le hy
    have hz' := hexVal_le hz
    have hw' := hexVal_le hw
    omega
  · simp at h

/-! #### The continuation step

`scanCons` accepts the character exactly when the policy allows it, and then
delegates to the body's remainder. -/

theorem scanCons_ok (pos next c rest cs fin)
    (hnc : IsNoncharacter c = false) (h : scanCharsFrom next rest = .ok (cs, fin)) :
    scanCons pos next c rest = .ok (c :: cs, fin) := by
  simp only [scanCons.eq_def]
  rw [ite_eq_right (by simp [hnc])]
  rw [h]

theorem scanCons_inv (pos next c rest cs fin)
    (h : scanCons pos next c rest = .ok (cs, fin)) :
    IsNoncharacter c = false ∧ ∃ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom next rest = .ok (cs', fin') ∧ cs = c :: cs' ∧ fin = fin' := by
  simp only [scanCons.eq_def] at h
  split at h
  · simp at h
  · rename_i hnc
    split at h
    · simp at h
    · rename_i cs0 fin0 hrec
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hcs, hfin⟩ := h
      subst hcs
      subst hfin
      refine ⟨?_, cs0, fin0, hrec, rfl, rfl⟩
      cases hb : IsNoncharacter c <;> simp_all

/-! #### Completeness

A `StrChars` derivation names a branch and its side conditions, so the scanner
takes that branch. -/

theorem scanCharsFrom_complete :
    ∀ (b : Bytes) (cs : List Nat) (rest : Bytes),
      StrChars .strict b cs rest → ∀ off : Nat, scanCharsFrom off b = .ok (cs, rest) := by
  intro b cs rest hr
  induction hr with
  | nil =>
      intro off
      exact scanCharsFrom_quote off _
  | cons hch hr ih =>
      intro off
      cases hch with
      | unescaped hutf hctrl hq hb hm =>
          have hnc := strict_noncharacter hm
          cases hutf with
          | one hlt =>
              rw [scanCharsFrom_ascii off _ _ (byte_ne_quote hq) (byte_ne_backslash hb) hlt hctrl]
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 1))
          | two h0 h0' h1 h1' =>
              rw [scanCharsFrom_utf8_two off _ _ _ h0 h0' h1 h1']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 2))
          | three₀ h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_e0 off _ _ _ h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₁ h0 h0' h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_e1ec off _ _ _ _ h0 h0' h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₂ h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_ed off _ _ _ h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | three₃ h0 h0' h1 h1' h2 h2' =>
              rw [scanCharsFrom_utf8_eeef off _ _ _ _ h0 h0' h1 h1' h2 h2']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 3))
          | four₀ h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f0 off _ _ _ _ h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
          | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f1f3 off _ _ _ _ _ h0 h0' h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
          | four₂ h1 h1' h2 h2' h3 h3' =>
              rw [scanCharsFrom_utf8_f4 off _ _ _ _ h1 h1' h2 h2' h3 h3']
              exact scanCons_ok _ _ _ _ _ _ hnc (ih (off + 4))
      | short hv =>
          rw [scanCharsFrom_escape off _ _ _ hv]
          exact scanCons_ok _ _ _ _ _ _ (escVal_noncharacter hv) (ih (off + 2))
      | escU hx hs hm =>
          rw [scanCharsFrom_uchar off _ _ _ _ _ _ (by decide) hx
            (high_ne_of_scalar hs) (low_ne_of_scalar hs)]
          exact scanCons_ok _ _ _ _ _ _ (strict_noncharacter hm) (ih (off + 6))
      | escPair hx hy hh hl hc hm =>
          rw [scanCharsFrom_pair off _ _ _ _ _ _ _ _ _ _ _ (by decide) hx hy hh hl]
          rw [← hc]
          exact scanCons_ok _ _ _ _ _ _ (strict_noncharacter hm) (ih (off + 12))
      | escLone hm _ _ => cases hm

/-! #### Reading each branch backwards

Each accepting branch, inverted: a successful scan of that branch's byte shape
is the corresponding `StrChar`. -/

theorem strChars_ascii (off : Nat) (q : UInt8) (tl : Bytes)
    (hq : q ≠ 0x22) (hs : q ≠ 0x5C) (hlt : q.toNat < 0x80) (hctrl : 0x20 ≤ q.toNat)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (q :: tl) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 1) tl = .ok (cs', fin') → StrChars .strict tl cs' fin') :
    StrChars .strict (q :: tl) cs fin := by
  rw [scanCharsFrom_ascii off q tl hq hs (UInt8.lt_iff_toNat_lt.mpr hlt) hctrl] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hutf : Utf8Char (q :: tl) q.toNat tl := Utf8Char.one (UInt8.lt_iff_toNat_lt.mpr hlt)
  refine StrChars.cons (StrChar.unescaped hutf hctrl ?_ ?_ ?_) ?_
  · intro hc
    exact hq (UInt8.toNat_inj.mp hc)
  · intro hc
    exact hs (UInt8.toNat_inj.mp hc)
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_escape (off : Nat) (e : UInt8) (rest1 : Bytes) (c : Nat)
    (hv : EscVal e = some c) {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0x5C :: e :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 2) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0x5C :: e :: rest1) cs fin := by
  rw [scanCharsFrom_escape off e rest1 c hv] at h
  obtain ⟨_, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  exact StrChars.cons (StrChar.short hv) (ih cs' fin' hrec)

theorem strChars_uchar (off : Nat) (h0 h1 h2 h3 : UInt8) (rest2 : Bytes) (c : Nat)
    (hv : EscVal (0x75 : UInt8) = none) (hx : Hex4 h0 h1 h2 h3 = some c)
    (hhi : ¬ (0xD800 ≤ c ∧ c ≤ 0xDBFF)) (hlo : ¬ (0xDC00 ≤ c ∧ c ≤ 0xDFFF))
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: rest2) =
      .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 6) rest2 = .ok (cs', fin') → StrChars .strict rest2 cs' fin') :
    StrChars .strict (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: rest2) cs fin := by
  rw [scanCharsFrom_uchar off h0 h1 h2 h3 rest2 c hv hx hhi hlo] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hbound := hex4_le hx
  have hscalar : IsScalar c := by
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b⟩
    by_cases hb' : c ≤ 0xDBFF
    · exact hhi ⟨a, hb'⟩
    · exact hlo ⟨by omega, b⟩
  exact StrChars.cons (StrChar.escU hx hscalar (charAllowed_of hscalar hnc))
    (ih cs' fin' hrec)

theorem strChars_pair (off : Nat) (h0 h1 h2 h3 l0 l1 l2 l3 : UInt8) (rest3 : Bytes)
    (hi lo : Nat) (hv : EscVal (0x75 : UInt8) = none)
    (hx : Hex4 h0 h1 h2 h3 = some hi) (hy : Hex4 l0 l1 l2 l3 = some lo)
    (hh : 0xD800 ≤ hi ∧ hi ≤ 0xDBFF) (hl : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off
      (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: 0x5C :: 0x75 ::
        l0 :: l1 :: l2 :: l3 :: rest3) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 12) rest3 = .ok (cs', fin') →
        StrChars .strict rest3 cs' fin') :
    StrChars .strict
      (0x5C :: 0x75 :: h0 :: h1 :: h2 :: h3 :: 0x5C :: 0x75 ::
        l0 :: l1 :: l2 :: l3 :: rest3) cs fin := by
  rw [scanCharsFrom_pair off h0 h1 h2 h3 l0 l1 l2 l3 rest3 hi lo hv hx hy hh hl] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  rw [hcs, hfin]
  have hb1 := hex4_le hx
  have hb2 := hex4_le hy
  have hscalar : IsScalar (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) := by
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b⟩
    omega
  exact StrChars.cons
    (StrChar.escPair hx hy hh hl rfl (charAllowed_of hscalar hnc))
    (ih cs' fin' hrec)

theorem strChars_utf8_two (off : Nat) (b0 b1 : UInt8) (rest1 : Bytes)
    (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF) (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b0 :: b1 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 2) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b0 :: b1 :: rest1) cs fin := by
  have h0n : (0xC2 : Nat) ≤ b0.toNat := by simpa using le_toNat h0
  have h0n' : b0.toNat ≤ (0xDF : Nat) := by simpa using le_toNat h0'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  rw [scanCharsFrom_utf8_two off b0 b1 rest1 h0 h0' h1 h1'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b0 :: b1 :: rest1)
      ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest1 := Utf8Char.two h0 h0' h1 h1'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_e0 (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0xA0 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xE0 :: b1 :: b2 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xE0 :: b1 :: b2 :: rest1) cs fin := by
  have h1n : (0xA0 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_e0 off b1 b2 rest1 h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xE0 :: b1 :: b2 :: rest1)
      ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 := Utf8Char.three₀ h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_e1ec (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xE1 ≤ b) (hb' : b ≤ 0xEC)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b :: b1 :: b2 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b :: b1 :: b2 :: rest1) cs fin := by
  have hbn : (0xE1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEC : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_e1ec off b b1 b2 rest1 hb hb' h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b :: b1 :: b2 :: rest1)
      ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₁ hb hb' h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_ed (off : Nat) (b1 b2 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x9F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xED :: b1 :: b2 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xED :: b1 :: b2 :: rest1) cs fin := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x9F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_ed off b1 b2 rest1 h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xED :: b1 :: b2 :: rest1)
      (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₂ h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_eeef (off : Nat) (b b1 b2 : UInt8) (rest1 : Bytes)
    (hb : 0xEE ≤ b) (hb' : b ≤ 0xEF)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b :: b1 :: b2 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 3) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b :: b1 :: b2 :: rest1) cs fin := by
  have hbn : (0xEE : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xEF : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  rw [scanCharsFrom_utf8_eeef off b b1 b2 rest1 hb hb' h1 h1' h2 h2'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b :: b1 :: b2 :: rest1)
      ((b.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest1 :=
    Utf8Char.three₃ hb hb' h1 h1' h2 h2'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f0 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x90 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xF0 :: b1 :: b2 :: b3 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xF0 :: b1 :: b2 :: b3 :: rest1) cs fin := by
  have h1n : (0x90 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f0 off b1 b2 b3 rest1 h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xF0 :: b1 :: b2 :: b3 :: rest1)
      ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₀ h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f1f3 (off : Nat) (b b1 b2 b3 : UInt8) (rest1 : Bytes)
    (hb : 0xF1 ≤ b) (hb' : b ≤ 0xF3)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (b :: b1 :: b2 :: b3 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (b :: b1 :: b2 :: b3 :: rest1) cs fin := by
  have hbn : (0xF1 : Nat) ≤ b.toNat := by simpa using le_toNat hb
  have hbn' : b.toNat ≤ (0xF3 : Nat) := by simpa using le_toNat hb'
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f1f3 off b b1 b2 b3 rest1 hb hb' h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (b :: b1 :: b2 :: b3 :: rest1)
      ((b.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
        (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₁ hb hb' h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

theorem strChars_utf8_f4 (off : Nat) (b1 b2 b3 : UInt8) (rest1 : Bytes)
    (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x8F) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
    (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF)
    {cs : List Nat} {fin : Bytes}
    (h : scanCharsFrom off (0xF4 :: b1 :: b2 :: b3 :: rest1) = .ok (cs, fin))
    (ih : ∀ (cs' : List Nat) (fin' : Bytes),
      scanCharsFrom (off + 4) rest1 = .ok (cs', fin') → StrChars .strict rest1 cs' fin') :
    StrChars .strict (0xF4 :: b1 :: b2 :: b3 :: rest1) cs fin := by
  have h1n : (0x80 : Nat) ≤ b1.toNat := by simpa using le_toNat h1
  have h1n' : b1.toNat ≤ (0x8F : Nat) := by simpa using le_toNat h1'
  have h2n : (0x80 : Nat) ≤ b2.toNat := by simpa using le_toNat h2
  have h2n' : b2.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h2'
  have h3n : (0x80 : Nat) ≤ b3.toNat := by simpa using le_toNat h3
  have h3n' : b3.toNat ≤ (0xBF : Nat) := by simpa using le_toNat h3'
  rw [scanCharsFrom_utf8_f4 off b1 b2 b3 rest1 h1 h1' h2 h2' h3 h3'] at h
  obtain ⟨hnc, cs', fin', hrec, hcs, hfin⟩ := scanCons_inv _ _ _ _ _ _ h
  have hutf : Utf8Char (0xF4 :: b1 :: b2 :: b3 :: rest1)
      (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
        (b3.toNat - 0x80)) rest1 :=
    Utf8Char.four₂ h1 h1' h2 h2' h3 h3'
  rw [hcs, hfin]
  refine StrChars.cons (StrChar.unescaped hutf ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · exact charAllowed_of ⟨by omega, by rintro ⟨a, b⟩; omega⟩ hnc
  · exact ih cs' fin' hrec

/-! #### Soundness

By induction on the subject's length: the scanner's recursive call is on a
strictly shorter remainder, and every accepting branch yields the corresponding
`StrChar`, so the body is a `StrChars` cons chain. -/

theorem le_of_toNat {a b : UInt8} (h : a.toNat ≤ b.toNat) : a ≤ b :=
  UInt8.le_iff_toNat_le.mpr h

theorem scanCharsFrom_sound_aux (n : Nat) :
    ∀ (b : Bytes), b.length ≤ n →
      ∀ (off : Nat) (cs : List Nat) (rest : Bytes),
        scanCharsFrom off b = .ok (cs, rest) → StrChars .strict b cs rest := by
  induction n with
  | zero =>
      intro b hlen off cs rest h
      cases b with
      | nil => rw [scanCharsFrom_nil] at h; simp at h
      | cons q tl => simp at hlen
  | succ n ih =>
      intro b hlen off cs rest h
      cases b with
      | nil => rw [scanCharsFrom_nil] at h; simp at h
      | cons q tl =>
          have htl : tl.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          by_cases hq : q = 0x22
          · subst hq
            rw [scanCharsFrom_quote] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact StrChars.nil
          · by_cases hs : q = 0x5C
            · subst hs
              cases tl with
              | nil => simp [scanCharsFrom.eq_def] at h
              | cons e rest1 =>
                  cases hv : EscVal e with
                  | some c =>
                      have hrest : rest1.length ≤ n := by
                        simp only [List.length_cons] at hlen
                        omega
                      exact strChars_escape off e rest1 c hv h (ih rest1 hrest (off + 2))
                  | none =>
                      by_cases he : e = 0x75
                      · subst he
                        rcases rest1 with _ | ⟨h0, r0⟩
                        · simp [scanCharsFrom.eq_def, hv] at h
                        · rcases r0 with _ | ⟨h1, r1⟩
                          · simp [scanCharsFrom.eq_def, hv] at h
                          · rcases r1 with _ | ⟨h2, r2⟩
                            · simp [scanCharsFrom.eq_def, hv] at h
                            · rcases r2 with _ | ⟨h3, rest2⟩
                              · simp [scanCharsFrom.eq_def, hv] at h
                              · cases hx : Hex4 h0 h1 h2 h3 with
                                | none => simp [scanCharsFrom.eq_def, hv, hx] at h
                                | some c =>
                                    by_cases hhi : 0xD800 ≤ c ∧ c ≤ 0xDBFF
                                    · rcases rest2 with _ | ⟨z0, w0⟩
                                      · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                      · by_cases hz0 : z0 = 0x5C
                                        · subst hz0
                                          rcases w0 with _ | ⟨z1, w1⟩
                                          · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                          · by_cases hz1 : z1 = 0x75
                                            · subst hz1
                                              rcases w1 with _ | ⟨l0, v0⟩
                                              · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                              · rcases v0 with _ | ⟨l1, v1⟩
                                                · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                                · rcases v1 with _ | ⟨l2, v2⟩
                                                  · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                                  · rcases v2 with _ | ⟨l3, rest3⟩
                                                    · simp [scanCharsFrom.eq_def, hv, hx, hhi] at h
                                                    · cases hy : Hex4 l0 l1 l2 l3 with
                                                      | none =>
                                                          simp [scanCharsFrom.eq_def, hv, hx, hhi, hy] at h
                                                      | some lo =>
                                                          by_cases hlo : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF
                                                          · have hrest : rest3.length ≤ n := by
                                                              simp only [List.length_cons] at hlen
                                                              omega
                                                            exact strChars_pair off h0 h1 h2 h3
                                                              l0 l1 l2 l3 rest3 c lo (by decide)
                                                              hx hy hhi hlo h
                                                              (ih rest3 hrest (off + 12))
                                                          · simp [scanCharsFrom.eq_def, hv, hx, hhi, hy, hlo] at h
                                            · simp [scanCharsFrom.eq_def, hv, hx, hhi, hz1] at h
                                        · simp [scanCharsFrom.eq_def, hv, hx, hhi, hz0] at h
                                    · by_cases hlo : 0xDC00 ≤ c ∧ c ≤ 0xDFFF
                                      · simp [scanCharsFrom.eq_def, hv, hx, hhi, hlo] at h
                                      · have hrest : rest2.length ≤ n := by
                                          simp only [List.length_cons] at hlen
                                          omega
                                        exact strChars_uchar off h0 h1 h2 h3 rest2 c
                                          (by decide) hx hhi hlo h (ih rest2 hrest (off + 6))
                      · simp [scanCharsFrom.eq_def, hv, he] at h
            · by_cases hlt : q.toNat < 0x80
              · by_cases hctrl : 0x20 ≤ q.toNat
                · exact strChars_ascii off q tl hq hs hlt hctrl h (ih tl htl (off + 1))
                · simp [scanCharsFrom.eq_def, hlt, hctrl] at h
              · by_cases htwo : 0xC2 ≤ q.toNat ∧ q.toNat ≤ 0xDF
                · rcases tl with _ | ⟨b1, rest1⟩
                  · simp [scanCharsFrom.eq_def, hlt, htwo] at h
                  · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                    · have hrest : rest1.length ≤ n := by
                        simp only [List.length_cons] at hlen
                        omega
                      exact strChars_utf8_two off q b1 rest1
                        (le_of_toNat htwo.1) (le_of_toNat htwo.2)
                        (le_of_toNat h12.1) (le_of_toNat h12.2) h
                        (ih rest1 hrest (off + 2))
                    · simp [scanCharsFrom.eq_def, hlt, htwo, h12] at h
                · by_cases he0 : q = 0xE0
                  · subst he0
                    rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                    · simp [scanCharsFrom.eq_def] at h
                    · simp [scanCharsFrom.eq_def] at h
                    · by_cases h12 : 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                          0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                      · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                        have hrest : rest1.length ≤ n := by
                          simp only [List.length_cons] at hlen
                          omega
                        exact strChars_utf8_e0 off b1 b2 rest1
                          (le_of_toNat h1n) (le_of_toNat h1n')
                          (le_of_toNat h2n) (le_of_toNat h2n') h
                          (ih rest1 hrest (off + 3))
                      · simp [scanCharsFrom.eq_def, h12] at h
                  · by_cases h31 : 0xE1 ≤ q.toNat ∧ q.toNat ≤ 0xEC
                    · rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                      · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31] at h
                      · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31] at h
                      · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                            0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                        · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                          have hrest : rest1.length ≤ n := by
                            simp only [List.length_cons] at hlen
                            omega
                          exact strChars_utf8_e1ec off q b1 b2 rest1
                            (le_of_toNat h31.1) (le_of_toNat h31.2)
                            (le_of_toNat h1n) (le_of_toNat h1n')
                            (le_of_toNat h2n) (le_of_toNat h2n') h
                            (ih rest1 hrest (off + 3))
                        · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, h12] at h
                    · by_cases hed : q = 0xED
                      · subst hed
                        rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                        · simp [scanCharsFrom.eq_def, he0] at h
                        · simp [scanCharsFrom.eq_def, he0] at h
                        · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧
                              0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                          · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                            have hrest : rest1.length ≤ n := by
                              simp only [List.length_cons] at hlen
                              omega
                            exact strChars_utf8_ed off b1 b2 rest1
                              (le_of_toNat h1n) (le_of_toNat h1n')
                              (le_of_toNat h2n) (le_of_toNat h2n') h
                              (ih rest1 hrest (off + 3))
                          · simp [scanCharsFrom.eq_def, he0, h12] at h
                      · by_cases h33 : 0xEE ≤ q.toNat ∧ q.toNat ≤ 0xEF
                        · rcases tl with _ | ⟨b1, _ | ⟨b2, rest1⟩⟩
                          · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33] at h
                          · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33] at h
                          · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                            · obtain ⟨h1n, h1n', h2n, h2n'⟩ := h12
                              have hrest : rest1.length ≤ n := by
                                simp only [List.length_cons] at hlen
                                omega
                              exact strChars_utf8_eeef off q b1 b2 rest1
                                (le_of_toNat h33.1) (le_of_toNat h33.2)
                                (le_of_toNat h1n) (le_of_toNat h1n')
                                (le_of_toNat h2n) (le_of_toNat h2n') h
                                (ih rest1 hrest (off + 3))
                            · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, h12] at h
                        · by_cases hf0 : q = 0xF0
                          · subst hf0
                            rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                            · simp [scanCharsFrom.eq_def, he0, hed] at h
                            · simp [scanCharsFrom.eq_def, he0, hed] at h
                            · simp [scanCharsFrom.eq_def, he0, hed] at h
                            · by_cases h12 : 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                  0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                  0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                              · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                have hrest : rest1.length ≤ n := by
                                  simp only [List.length_cons] at hlen
                                  omega
                                exact strChars_utf8_f0 off b1 b2 b3 rest1
                                  (le_of_toNat h1n) (le_of_toNat h1n')
                                  (le_of_toNat h2n) (le_of_toNat h2n')
                                  (le_of_toNat h3n) (le_of_toNat h3n') h
                                  (ih rest1 hrest (off + 4))
                              · simp [scanCharsFrom.eq_def, he0, hed, h12] at h
                          · by_cases h41 : 0xF1 ≤ q.toNat ∧ q.toNat ≤ 0xF3
                            · rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                              · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, hf0, h41] at h
                              · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧
                                    0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                    0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                  have hrest : rest1.length ≤ n := by
                                    simp only [List.length_cons] at hlen
                                    omega
                                  exact strChars_utf8_f1f3 off q b1 b2 b3 rest1
                                    (le_of_toNat h41.1) (le_of_toNat h41.2)
                                    (le_of_toNat h1n) (le_of_toNat h1n')
                                    (le_of_toNat h2n) (le_of_toNat h2n')
                                    (le_of_toNat h3n) (le_of_toNat h3n') h
                                    (ih rest1 hrest (off + 4))
                                · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, hf0, h41, h12] at h
                            · by_cases hf4 : q = 0xF4
                              · subst hf4
                                rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest1⟩⟩⟩
                                · simp [scanCharsFrom.eq_def, he0, hed, hf0] at h
                                · simp [scanCharsFrom.eq_def, he0, hed, hf0] at h
                                · simp [scanCharsFrom.eq_def, he0, hed, hf0] at h
                                · by_cases h12 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧
                                      0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧
                                      0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                                  · obtain ⟨h1n, h1n', h2n, h2n', h3n, h3n'⟩ := h12
                                    have hrest : rest1.length ≤ n := by
                                      simp only [List.length_cons] at hlen
                                      omega
                                    exact strChars_utf8_f4 off b1 b2 b3 rest1
                                      (le_of_toNat h1n) (le_of_toNat h1n')
                                      (le_of_toNat h2n) (le_of_toNat h2n')
                                      (le_of_toNat h3n) (le_of_toNat h3n') h
                                      (ih rest1 hrest (off + 4))
                                  · simp [scanCharsFrom.eq_def, he0, hed, hf0, h12] at h
                              · simp [scanCharsFrom.eq_def, hlt, htwo, he0, h31, hed, h33, hf0, h41, hf4] at h

theorem scanCharsFrom_sound {off : Nat} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : scanCharsFrom off b = .ok (cs, rest)) : StrChars .strict b cs rest :=
  scanCharsFrom_sound_aux b.length b (Nat.le_refl _) off cs rest h

/-! #### The reflection lemma -/

/-- The success side of `scanChars` is exactly the strict character relation.  The
failure side adds nothing to what the theorems know: it is the complement. -/
theorem scanChars_iff (b : Bytes) (cs : List Nat) (rest : Bytes) :
    scanChars b = .ok (cs, rest) ↔ StrChars .strict b cs rest := by
  constructor
  · intro h
    exact scanCharsFrom_sound h
  · intro h
    exact scanCharsFrom_complete b cs rest h 0

/-! #### The mode correspondence

The two modes differ in exactly two places in `StrChar`: the raw, `\u` and
surrogate-pair clauses carry `ModeAllows`, which is `True` in `rfc` and
`CharAllowed` in `strict`, and `escLone` — RFC 8259 §8.2's unpaired surrogate
escape — has no `strict` derivation at all.  `valid_iff_strict` is those two
differences read in each direction.  A value's policy is a property of its whole
tree, so each direction is a joint induction over the six grammar relations,
with `StrChars` supplying the string leaf. -/

/-- The three membership forms the list-level motives are stated in. -/
private theorem forall_mem_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  cases hx

private theorem forall_mem_singleton {α : Type} {P : α → Prop} {a : α} (h : P a) :
    ∀ x ∈ [a], P x := by
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact h

private theorem forall_mem_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (h1 : P a)
    (h2 : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1
  · exact h2 x hx

/-- Every code point a two-character escape denotes is a scalar: the eight escapes
of §7 all lie in the BMP. -/
theorem escVal_scalar {e : UInt8} {c : Nat} (h : EscVal e = some c) : IsScalar c := by
  unfold EscVal at h
  split at h <;> (first | (simp_all only [Option.some.injEq]; subst_vars; decide) | simp_all)

/-- Every code point a two-character escape denotes satisfies `Policy`. -/
theorem escVal_charAllowed {e : UInt8} {c : Nat} (h : EscVal e = some c) : CharAllowed c :=
  ⟨escVal_scalar h, escVal_noncharacter h⟩

/-- A `strict` character's code point satisfies RFC 7493 §2.1.  The raw and `\u`
clauses carry `ModeAllows .strict`, the two-character escape is enumerated, and
`escLone` cannot occur in `strict`. -/
theorem strChar_strict_allowed {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .strict b c rest) : CharAllowed c := by
  cases h with
  | unescaped _ _ _ _ hm => exact hm
  | short he => exact escVal_charAllowed he
  | escU _ _ hm => exact hm
  | escPair _ _ _ _ _ hm => exact hm
  | escLone hm _ _ => cases hm

/-- Every code point of a `strict` string body satisfies RFC 7493 §2.1. -/
theorem strChars_strict_policy {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .strict b cs rest) : ∀ c ∈ cs, CharAllowed c := by
  induction h with
  | nil => intro c hc; cases hc
  | cons hch _ ih =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact strChar_strict_allowed hch
      · exact ih c hc

/-- Mode weakening, character case: an `rfc` character is a `strict` one when its
code point satisfies `Policy`.  `escLone` is the case whose hypothesis refutes
it. -/
theorem strChar_rfc_strict {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .rfc b c rest) (hc : CharAllowed c) : StrChar .strict b c rest := by
  cases h with
  | unescaped h8 hctrl hq hb _ => exact .unescaped h8 hctrl hq hb hc
  | short he => exact .short he
  | escU hx hs _ => exact .escU hx hs hc
  | escPair hhi hlo hh hl hco _ => exact .escPair hhi hlo hh hl hco hc
  | escLone _ _ hs => exact absurd hc.1 hs

/-- Mode weakening for a string body. -/
theorem strChars_rfc_strict {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .rfc b cs rest) (hp : ∀ c ∈ cs, CharAllowed c) :
    StrChars .strict b cs rest := by
  induction h with
  | nil => exact .nil
  | cons hch _ ih =>
      exact .cons (strChar_rfc_strict hch (hp _ List.mem_cons_self))
        (ih (fun c hc => hp c (List.mem_cons_of_mem _ hc)))

/-- Mode weakening for a string literal. -/
theorem stringAt_rfc_strict {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .rfc bs i j cs) (hp : ∀ c ∈ cs, CharAllowed c) :
    StringAt .strict bs i j cs := by
  obtain ⟨hq, rest, hsc, hdrop⟩ := h
  exact ⟨hq, rest, strChars_rfc_strict hsc hp, hdrop⟩

/-- The other direction at the character level: a `strict` character is an `rfc`
one, because `ModeAllows .rfc` is `True`. -/
theorem strChar_strict_rfc {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar .strict b c rest) : StrChar .rfc b c rest := by
  cases h with
  | unescaped h8 hctrl hq hb _ => exact .unescaped h8 hctrl hq hb trivial
  | short he => exact .short he
  | escU hx hs _ => exact .escU hx hs trivial
  | escPair hhi hlo hh hl hc _ => exact .escPair hhi hlo hh hl hc trivial
  | escLone hm _ _ => cases hm

/-- A `strict` string body is an `rfc` one. -/
theorem strChars_strict_rfc {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .strict b cs rest) : StrChars .rfc b cs rest := by
  induction h with
  | nil => exact .nil
  | cons hch _ ih => exact .cons (strChar_strict_rfc hch) ih

/-- A `strict` string literal is an `rfc` one. -/
theorem stringAt_strict_rfc {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict bs i j cs) : StringAt .rfc bs i j cs := by
  obtain ⟨hq, rest, hsc, hdrop⟩ := h
  exact ⟨hq, rest, strChars_strict_rfc hsc, hdrop⟩

/-- A `strict` string literal's code points satisfy `Policy`. -/
theorem stringAt_strict_policy {bs : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict bs i j cs) : ∀ c ∈ cs, CharAllowed c := by
  obtain ⟨-, rest, hsc, -⟩ := h
  exact strChars_strict_policy hsc

/- Policy-directed mode weakening, value case: an `rfc` derivation of a value
whose code points satisfy `Policy` is a `strict` derivation. -/
mutual
theorem valueAt_rfc_strict : (bs : Bytes) → (i : Nat) → (v : Value) → (j : Nat) →
    ValueAt .rfc bs i v j → v.charPolicy → ValueAt .strict bs i v j
  | _, _, _, _, .null h, _ => .null h
  | _, _, _, _, .true h, _ => .true h
  | _, _, _, _, .false h, _ => .false h
  | _, _, _, _, .number h, _ => .number h
  | _, _, _, _, .string h, hp =>
      .string (stringAt_rfc_strict h ((charPolicy_string _).mp hp))
  | _, _, _, _, .array hl hb hr, hp =>
      .array hl (arrBody_rfc_strict _ _ _ _ hb ((charPolicy_array _).mp hp)) hr
  | _, _, _, _, .object hl hb hr, hp =>
      .object hl (objBody_rfc_strict _ _ _ _ hb
        ((membersPolicy_iff _).mp ((charPolicy_object _).mp hp))) hr

/-- Policy-directed mode weakening, array body case. -/
theorem arrBody_rfc_strict : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    ArrBody .rfc bs i vs k → (∀ v ∈ vs, v.charPolicy) → ArrBody .strict bs i vs k
  | _, _, _, _, .empty h, _ => .empty h
  | _, _, _, _, .elems he h, hp => .elems (elems_rfc_strict _ _ _ _ he hp) h

/-- Policy-directed mode weakening, element-list case. -/
theorem elems_rfc_strict : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    Elems .rfc bs i vs k → (∀ v ∈ vs, v.charPolicy) → Elems .strict bs i vs k
  | _, _, _, _, .last hv hw, hp =>
      .last (valueAt_rfc_strict _ _ _ _ hv (hp _ (List.mem_singleton_self _))) hw
  | _, _, _, _, .cons hv hw1 hc hw2 hr, hp =>
      .cons (valueAt_rfc_strict _ _ _ _ hv (hp _ List.mem_cons_self)) hw1 hc hw2
        (elems_rfc_strict _ _ _ _ hr (fun x hx => hp x (List.mem_cons_of_mem _ hx)))

/-- Policy-directed mode weakening, member case: the name and the value are
checked separately. -/
theorem member_rfc_strict : (bs : Bytes) → (i : Nat) → (mem : List Nat × Value) → (j : Nat) →
    Member .rfc bs i mem j → ((∀ c ∈ mem.1, CharAllowed c) ∧ mem.2.charPolicy) →
      Member .strict bs i mem j
  | _, _, _, _, .mk hk hw1 hc hw2 hv, hp =>
      .mk (stringAt_rfc_strict hk hp.1) hw1 hc hw2 (valueAt_rfc_strict _ _ _ _ hv hp.2)

/-- Policy-directed mode weakening, member-list case. -/
theorem members_rfc_strict : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    Members .rfc bs i ms k → (∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy) →
      Members .strict bs i ms k
  | _, _, _, _, .last hm hw, hp =>
      .last (member_rfc_strict _ _ _ _ hm (hp _ (List.mem_singleton_self _))) hw
  | _, _, _, _, .cons hm hw1 hc hw2 hr, hp =>
      .cons (member_rfc_strict _ _ _ _ hm (hp _ List.mem_cons_self)) hw1 hc hw2
        (members_rfc_strict _ _ _ _ hr (fun x hx => hp x (List.mem_cons_of_mem _ hx)))

/-- Policy-directed mode weakening, object body case. -/
theorem objBody_rfc_strict : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    ObjBody .rfc bs i ms k → (∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy) →
      ObjBody .strict bs i ms k
  | _, _, _, _, .empty h, _ => .empty h
  | _, _, _, _, .members hm h, hp => .members (members_rfc_strict _ _ _ _ hm hp) h
end

/- The reading side: a `strict` derivation is an `rfc` derivation, and the policy
of the value it names.  The second component is where `Policy` is produced rather
than consumed. -/
mutual
theorem valueAt_strict_rfc : (bs : Bytes) → (i : Nat) → (v : Value) → (j : Nat) →
    ValueAt .strict bs i v j → ValueAt .rfc bs i v j ∧ v.charPolicy
  | _, _, _, _, .null h => ⟨.null h, charPolicy_null⟩
  | _, _, _, _, .true h => ⟨.true h, charPolicy_bool _⟩
  | _, _, _, _, .false h => ⟨.false h, charPolicy_bool _⟩
  | _, _, _, _, .number h => ⟨.number h, charPolicy_number _⟩
  | _, _, _, _, .string h =>
      ⟨.string (stringAt_strict_rfc h),
       (charPolicy_string _).mpr (stringAt_strict_policy h)⟩
  | _, _, _, _, .array hl hb hr =>
      ⟨.array hl (arrBody_strict_rfc _ _ _ _ hb).1 hr,
       (charPolicy_array _).mpr (arrBody_strict_rfc _ _ _ _ hb).2⟩
  | _, _, _, _, .object hl hb hr =>
      ⟨.object hl (objBody_strict_rfc _ _ _ _ hb).1 hr,
       (charPolicy_object _).mpr
         ((membersPolicy_iff _).mpr (objBody_strict_rfc _ _ _ _ hb).2)⟩

/-- The reading side, array body case. -/
theorem arrBody_strict_rfc : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    ArrBody .strict bs i vs k → ArrBody .rfc bs i vs k ∧ (∀ v ∈ vs, v.charPolicy)
  | _, _, _, _, .empty h => ⟨.empty h, forall_mem_nil⟩
  | _, _, _, _, .elems he h =>
      ⟨.elems (elems_strict_rfc _ _ _ _ he).1 h, (elems_strict_rfc _ _ _ _ he).2⟩

/-- The reading side, element-list case. -/
theorem elems_strict_rfc : (bs : Bytes) → (i : Nat) → (vs : List Value) → (k : Nat) →
    Elems .strict bs i vs k → Elems .rfc bs i vs k ∧ (∀ v ∈ vs, v.charPolicy)
  | _, _, _, _, .last hv hw =>
      ⟨.last (valueAt_strict_rfc _ _ _ _ hv).1 hw,
       forall_mem_singleton (valueAt_strict_rfc _ _ _ _ hv).2⟩
  | _, _, _, _, .cons hv hw1 hc hw2 hr =>
      ⟨.cons (valueAt_strict_rfc _ _ _ _ hv).1 hw1 hc hw2
          (elems_strict_rfc _ _ _ _ hr).1,
       forall_mem_cons (valueAt_strict_rfc _ _ _ _ hv).2 (elems_strict_rfc _ _ _ _ hr).2⟩

/-- The reading side, member case. -/
theorem member_strict_rfc : (bs : Bytes) → (i : Nat) → (mem : List Nat × Value) → (j : Nat) →
    Member .strict bs i mem j →
      Member .rfc bs i mem j ∧ ((∀ c ∈ mem.1, CharAllowed c) ∧ mem.2.charPolicy)
  | _, _, _, _, .mk hk hw1 hc hw2 hv =>
      ⟨.mk (stringAt_strict_rfc hk) hw1 hc hw2 (valueAt_strict_rfc _ _ _ _ hv).1,
       ⟨stringAt_strict_policy hk, (valueAt_strict_rfc _ _ _ _ hv).2⟩⟩

/-- The reading side, member-list case. -/
theorem members_strict_rfc : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    Members .strict bs i ms k →
      Members .rfc bs i ms k ∧ ∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy
  | _, _, _, _, .last hm hw =>
      ⟨.last (member_strict_rfc _ _ _ _ hm).1 hw,
       forall_mem_singleton (member_strict_rfc _ _ _ _ hm).2⟩
  | _, _, _, _, .cons hm hw1 hc hw2 hr =>
      ⟨.cons (member_strict_rfc _ _ _ _ hm).1 hw1 hc hw2
          (members_strict_rfc _ _ _ _ hr).1,
       forall_mem_cons (member_strict_rfc _ _ _ _ hm).2
         (members_strict_rfc _ _ _ _ hr).2⟩

/-- The reading side, object body case. -/
theorem objBody_strict_rfc : (bs : Bytes) → (i : Nat) →
    (ms : List (List Nat × Value)) → (k : Nat) →
    ObjBody .strict bs i ms k →
      ObjBody .rfc bs i ms k ∧ ∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy
  | _, _, _, _, .empty h => ⟨.empty h, forall_mem_nil⟩
  | _, _, _, _, .members hm h =>
      ⟨.members (members_strict_rfc _ _ _ _ hm).1 h, (members_strict_rfc _ _ _ _ hm).2⟩
end

/-- `ValidDocument` and `StrictText` are the same language: the RFC 8259 grammar
restricted by RFC 7493 §2.1's character constraint.  The two directions are the
mode correspondence above; the top-level indices and the whitespace are mode
independent, so only the `ValueAt` derivation moves. -/
theorem valid_iff_strict (bs : Bytes) (v : Value) :
    (RfcText bs v ∧ Policy v) ↔ StrictText bs v := by
  constructor
  · rintro ⟨⟨i, j, h0, hv, hlen⟩, hp⟩
    exact ⟨i, j, h0, valueAt_rfc_strict bs i v j hv hp, hlen⟩
  · intro h
    obtain ⟨i, j, h0, hv, hlen⟩ := h
    obtain ⟨hrfc, hpol⟩ := valueAt_strict_rfc bs i v j hv
    exact ⟨⟨i, j, h0, hrfc, hlen⟩, hpol⟩

/-- `Utf8Char` consumes at least one byte. -/
theorem utf8_rest_lt {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    rest.length < b.length := by
  cases h <;> simp <;> omega

/-- A string character consumes at least one byte. -/
theorem strChar_rest_lt {m : Strictness} {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar m b c rest) : rest.length < b.length := by
  cases h with
  | unescaped h _ _ _ _ => exact utf8_rest_lt h
  | short h => simp <;> omega
  | escU _ _ _ => simp <;> omega
  | escPair _ _ _ _ _ _ => simp <;> omega
  | escLone _ _ _ => simp <;> omega

/-- A string body consumes at least its characters' bytes. -/
theorem strChars_suffix_lt {m : Strictness} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars m b cs rest) : rest.length < b.length := by
  induction h with
  | nil => simp
  | cons hch _ ih =>
      have h1 := strChar_rest_lt hch
      omega

/-- `Utf8Char` consumes a prefix. -/
theorem utf8_split {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    ∃ pre, b = pre ++ rest := by
  cases h with
  | @one b rest _ => exact ⟨[b], rfl⟩
  | @two b0 b1 rest _ _ _ _ => exact ⟨[b0, b1], rfl⟩
  | @three₀ b1 b2 rest _ _ _ _ => exact ⟨[0xE0, b1, b2], rfl⟩
  | @three₁ b0 b1 b2 rest _ _ _ _ _ _ => exact ⟨[b0, b1, b2], rfl⟩
  | @three₂ b1 b2 rest _ _ _ _ => exact ⟨[0xED, b1, b2], rfl⟩
  | @three₃ b0 b1 b2 rest _ _ _ _ _ _ => exact ⟨[b0, b1, b2], rfl⟩
  | @four₀ b1 b2 b3 rest _ _ _ _ _ _ => exact ⟨[0xF0, b1, b2, b3], rfl⟩
  | @four₁ b0 b1 b2 b3 rest _ _ _ _ _ _ _ _ => exact ⟨[b0, b1, b2, b3], rfl⟩
  | @four₂ b1 b2 b3 rest _ _ _ _ _ _ => exact ⟨[0xF4, b1, b2, b3], rfl⟩

/-- A string character consumes a prefix. -/
theorem strChar_split {m : Strictness} {b : Bytes} {c : Nat} {rest : Bytes}
    (h : StrChar m b c rest) : ∃ pre, b = pre ++ rest := by
  cases h with
  | @unescaped b c rest h8 _ _ _ _ => exact utf8_split h8
  | @short e c rest _ => exact ⟨[0x5C, e], rfl⟩
  | @escU h0 h1 h2 h3 c rest _ _ _ =>
      exact ⟨[0x5C, 0x75, h0, h1, h2, h3], rfl⟩
  | @escPair h0 h1 h2 h3 l0 l1 l2 l3 hi lo c rest _ _ _ _ _ _ =>
      exact ⟨[0x5C, 0x75, h0, h1, h2, h3, 0x5C, 0x75, l0, l1, l2, l3], rfl⟩
  | @escLone h0 h1 h2 h3 c rest _ _ _ =>
      exact ⟨[0x5C, 0x75, h0, h1, h2, h3], rfl⟩

/-- A string body consumes a prefix, so the remainder it leaves is a suffix. -/
theorem strChars_split {m : Strictness} {b : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars m b cs rest) : ∃ pre, b = pre ++ rest := by
  induction h with
  | nil => exact ⟨[0x22], rfl⟩
  | cons hch _ ih =>
      obtain ⟨pre1, hp1⟩ := strChar_split hch
      obtain ⟨pre2, hp2⟩ := ih
      exact ⟨pre1 ++ pre2, by rw [hp1, hp2, List.append_assoc]⟩

/-- Dropping the last `after.length` bytes of a split list gives `after`. -/
theorem drop_of_split {l pre after : Bytes} (h : l = pre ++ after) :
    l.drop (l.length - after.length) = after := by
  rw [h, List.length_append, Nat.add_sub_cancel, List.drop_left]

/-- The remainder a scanned body leaves is no longer than the body: the fact
`parseKey`'s `consumed` field needs. -/
theorem scalar_suffix_le (b : Bytes) (cs : List Nat) (after : Bytes)
    (h : scanChars b = .ok (cs, after)) : after.length ≤ b.length := by
  have hs := scanChars_iff b cs after |>.mp h
  have := strChars_suffix_lt hs
  omega

/-- A number lexeme is non-empty, so a parsed number consumes at least one byte. -/
theorem rfcNumber_nonempty {lex : Bytes} (h : RfcNumber lex) : 0 < lex.length := by
  cases h with
  | pos hb =>
      cases hb with
      | plain hi => cases hi <;> simp
      | frac hi _ => cases hi <;> simp
      | exp hi _ => cases hi <;> simp
      | fracExp hi _ _ => cases hi <;> simp
  | neg _ => simp

theorem numLexB_nonempty (lex : Bytes) (h : numLexB lex = true) : 0 < lex.length :=
  rfcNumber_nonempty (numLexB_iff lex |>.mp h)

theorem numRun_length_le : ∀ (b : Bytes), (numRun b).length ≤ b.length
  | [] => by simp [numRun]
  | c :: rest => by
      rw [numRun]
      split
      · have ih := numRun_length_le rest
        simp only [List.length_cons]
        omega
      · simp

/-- `numRun b` is the longest constituent prefix: it is a prefix of `b`, and the
byte where it stops is not a constituent. -/
theorem numRun_spec (b : Bytes) :
    b.take (numRun b).length = numRun b ∧
      ∀ (c : UInt8) (rest : Bytes), b.drop (numRun b).length = c :: rest →
        NumConstituent c = false := by
  induction b with
  | nil => simp [numRun]
  | cons a rest ih =>
      rw [numRun]
      split
      · rename_i hc
        obtain ⟨ih1, ih2⟩ := ih
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons, List.take_succ_cons]
          rw [ih1]
        · intro c tail hd
          rw [List.length_cons, List.drop_succ_cons] at hd
          exact ih2 c tail hd
      · rename_i hc
        refine ⟨?_, ?_⟩
        · simp
        · intro c tail hd
          rw [List.length_nil, List.drop_zero] at hd
          injection hd with h1 _
          rw [← h1]
          cases hv : NumConstituent a <;> simp_all

/-! ### Whitespace arithmetic

The parser's measure is `bs.length - i`, so it needs `skipFrom` to be at least its
index and at most the input's length. -/

theorem spaceRun_le_length : ∀ (bs : Bytes), spaceRun bs ≤ bs.length
  | [] => by simp [spaceRun]
  | b :: rest => by
      rw [spaceRun]
      split
      · have ih := spaceRun_le_length rest
        simp only [List.length_cons]
        omega
      · simp

theorem skipFrom_ge (bs : Bytes) (i : Nat) : i ≤ skipFrom bs i := by
  unfold skipFrom
  omega

/-- In range, the skip stays inside the input.  The `i ≤ bs.length` hypothesis is
not decoration: `skipFrom bs i = i` once `i` is past the end, and that exceeds
`bs.length`. -/
theorem skipFrom_le_length (bs : Bytes) (i : Nat) (h : i ≤ bs.length) :
    skipFrom bs i ≤ bs.length := by
  unfold skipFrom
  have hs := spaceRun_le_length (bs.drop i)
  have hd : (bs.drop i).length = bs.length - i := by simp
  omega

/-- Every byte of the leading whitespace run is whitespace. -/
theorem spaceRun_all : ∀ (bs : Bytes) (k : Nat) (b : UInt8),
    k < spaceRun bs → bs[k]? = some b → IsSpaceB b = true
  | [], k, b, hk, _ => by simp [spaceRun] at hk
  | a :: rest, k, b, hk, hget => by
      rw [spaceRun] at hk
      split at hk
      · rename_i ha
        cases k with
        | zero =>
            rw [List.getElem?_cons_zero] at hget
            injection hget with hb
            subst hb
            exact ha
        | succ k =>
            rw [List.getElem?_cons_succ] at hget
            exact spaceRun_all rest k b (by omega) hget
      · omega

/-- The leading whitespace run is a `ws` range: the empty range when the input
starts with a non-whitespace byte. -/
theorem spaceRun_space (bs : Bytes) : SpaceAt bs 0 (spaceRun bs) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro k b _ hk hget
  exact spaceRun_all bs k b hk hget

/-- A whitespace range in a dropped list is the same range in the whole list,
shifted by the drop. -/
theorem spaceAt_drop {bs : Bytes} {i j : Nat} (h : SpaceAt (bs.drop i) 0 j) :
    SpaceAt bs i (i + j) := by
  obtain ⟨_, hall⟩ := h
  refine ⟨by omega, ?_⟩
  intro k b hi hk hget
  have hbase : i + (k - i) = k := Nat.add_sub_of_le hi
  have hget' : (bs.drop i)[k - i]? = some b := by
    rw [List.getElem?_drop, hbase]
    exact hget
  have hlt : k - i < j := by
    rw [← hbase] at hk
    exact Nat.lt_of_add_lt_add_left hk
  show IsSpaceB b = true
  exact hall (k - i) b (Nat.zero_le _) hlt hget'

/-- The skipped range is whitespace: what a separator's `ws` run needs. -/
theorem skipFrom_space (bs : Bytes) (i : Nat) : SpaceAt bs i (skipFrom bs i) := by
  unfold skipFrom
  exact spaceAt_drop (spaceRun_space (bs.drop i))

/-- The Boolean prefix test and the proposition agree. -/
theorem hasPrefixB_iff {bs : Bytes} {i : Nat} {p : Bytes} :
    HasPrefixB bs i p = true ↔ HasPrefix bs i p := by
  simp [HasPrefixB, HasPrefix, decide_eq_true_eq]

/-- A checked prefix has room in the input: the fact a span's stop needs. -/
theorem hasPrefix_le {bs : Bytes} {i : Nat} {p : Bytes} (h : HasPrefix bs i p)
    (hne : 0 < p.length) : i + p.length ≤ bs.length := by
  unfold HasPrefix at h
  have h1 : ((bs.drop i).take p.length).length = p.length := by rw [h]
  rw [List.length_take] at h1
  rw [List.length_drop] at h1
  omega

end LeanLLVM.JSON
