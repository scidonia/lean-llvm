/-
RFC 3629 §4's `UTF8-octets` / `UTF8-char` ABNF, transcribed one constructor per
alternative, with the code point each clause encodes.

RFC 8259 §8.1 requires UTF-8 for interchange and RFC 3629 §3 requires every
decoder to protect against invalid sequences, so this transcription *is* part of
the language: overlongs, encoded surrogates and values above U+10FFFF are not
JSON texts.
-/
import LeanLLVM.JSON.Bytes

namespace LeanLLVM.JSON

open ByteString

/-- RFC 3629 §4: `UTF8-octets = *( UTF8-char )`, one constructor per `UTF8-char`
alternative.  `Utf8Char b c rest` holds when `b` begins with exactly one encoded
code point, `c`, and `rest` follows it. -/
inductive Utf8Char : Bytes → Nat → Bytes → Prop where
  /-- `UTF8-1 = %x00-7F` -/
  | one {b : UInt8} {rest : Bytes} (h : b < 0x80) :
      Utf8Char (b +: rest) b.toNat rest
  /-- `UTF8-2 = %xC2-DF UTF8-tail` -/
  | two {b0 b1 : UInt8} {rest : Bytes} (h0 : 0xC2 ≤ b0) (h0' : b0 ≤ 0xDF)
      (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) :
      Utf8Char (b0 +: b1 +: rest)
        ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) rest
  /-- `UTF8-3 = %xE0 %xA0-BF UTF8-tail` -/
  | three₀ {b1 b2 : UInt8} {rest : Bytes} (h1 : 0xA0 ≤ b1) (h1' : b1 ≤ 0xBF)
      (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
      Utf8Char (0xE0 +: b1 +: b2 +: rest)
        ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest
  /-- `UTF8-3 = %xE1-EC 2( UTF8-tail )` -/
  | three₁ {b0 b1 b2 : UInt8} {rest : Bytes} (h0 : 0xE1 ≤ b0) (h0' : b0 ≤ 0xEC)
      (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
      Utf8Char (b0 +: b1 +: b2 +: rest)
        ((b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest
  /-- `UTF8-3 = %xED %x80-9F UTF8-tail` -/
  | three₂ {b1 b2 : UInt8} {rest : Bytes} (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x9F)
      (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
      Utf8Char (0xED +: b1 +: b2 +: rest)
        (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest
  /-- `UTF8-3 = %xEE-EF 2( UTF8-tail )` -/
  | three₃ {b0 b1 b2 : UInt8} {rest : Bytes} (h0 : 0xEE ≤ b0) (h0' : b0 ≤ 0xEF)
      (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) :
      Utf8Char (b0 +: b1 +: b2 +: rest)
        ((b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80)) rest
  /-- `UTF8-4 = %xF0 %x90-BF 2( UTF8-tail )` -/
  | four₀ {b1 b2 b3 : UInt8} {rest : Bytes} (h1 : 0x90 ≤ b1) (h1' : b1 ≤ 0xBF)
      (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
      Utf8Char (0xF0 +: b1 +: b2 +: b3 +: rest)
        ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest
  /-- `UTF8-4 = %xF1-F3 3( UTF8-tail )` -/
  | four₁ {b0 b1 b2 b3 : UInt8} {rest : Bytes} (h0 : 0xF1 ≤ b0) (h0' : b0 ≤ 0xF3)
      (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0xBF) (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF)
      (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
      Utf8Char (b0 +: b1 +: b2 +: b3 +: rest)
        ((b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest
  /-- `UTF8-4 = %xF4 %x80-8F 2( UTF8-tail )` -/
  | four₂ {b1 b2 b3 : UInt8} {rest : Bytes} (h1 : 0x80 ≤ b1) (h1' : b1 ≤ 0x8F)
      (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) :
      Utf8Char (0xF4 +: b1 +: b2 +: b3 +: rest)
        (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)) rest

/-- `Utf8Spans b rest`: `b` is a concatenation of complete characters followed by
`rest`.  The base case is every `rest`, which is what makes this the *span*
relation rather than the document relation: `Utf8Spans b empty` is RFC 3629 §4's
`UTF8-octets` for the whole of `b`, and `Utf8Spans b t` with `t ≠ empty` says the
parse stopped before the end. -/
inductive Utf8Spans : Bytes → Bytes → Prop where
  /-- Nothing left to parse: what remains is the tail. -/
  | nil (t : Bytes) : Utf8Spans t t
  /-- One complete character, then the rest of the span. -/
  | char {b b' rest : Bytes} {c : Nat} (h : Utf8Char b c b') (hr : Utf8Spans b' rest) :
      Utf8Spans b rest

/-- RFC 3629 §4's `UTF8-octets = *( UTF8-char )`: the whole string is complete
characters. -/
def Utf8Chars (b : Bytes) : Prop := Utf8Spans b empty

/-- A proper nonempty prefix of one character's encoding, in `Bytes.lean`'s own
prefix predicate (`HasPrefix b 0 t` is `b.take t.length = t`).  This is the
unfinished character a caller may hold at the end of a window, and the reason the
relation below is not `Utf8Chars`. -/
def Utf8PrefixOf (t : Bytes) : Prop :=
  t ≠ empty ∧ ∃ (b : Bytes) (c : Nat) (r : Bytes),
    Utf8Char b c r ∧ t.length < b.length ∧ HasPrefix b 0 t

/-- The valid-prefix relation: complete characters, then at most one unfinished
one.  This is the predicate a staged window's verdict is judged against — the
relation below the document, because a window may end in the middle of a
character and the next window continues it. -/
def ValidPrefix (b : Bytes) : Prop :=
  ∃ t, Utf8Spans b t ∧ (t = empty ∨ Utf8PrefixOf t)

/-- The span relation splits in two shapes: nothing parsed, or one character and
a shorter span.  This is the elimination form the inversion proofs use: the
conclusion does not name the indices, so it needs no dependent elimination. -/
theorem utf8Spans_cases {b rest : Bytes} (h : Utf8Spans b rest) :
    rest = b ∨ ∃ (b' : Bytes) (c : Nat), Utf8Char b c b' ∧ Utf8Spans b' rest := by
  cases h with
  | nil t => exact Or.inl rfl
  | char hc hr => exact Or.inr ⟨_, _, hc, hr⟩

/-- The valid-prefix relation is a parse leaving either nothing or one partial
character, and a complete document is the first of those two cases. -/
theorem validPrefix_iff (b : Bytes) :
    ValidPrefix b ↔ Utf8Chars b ∨ ∃ t, Utf8Spans b t ∧ Utf8PrefixOf t := by
  unfold ValidPrefix Utf8Chars
  constructor
  · rintro ⟨t, hs, ht | hp⟩
    · exact Or.inl (ht ▸ hs)
    · exact Or.inr ⟨t, hs, hp⟩
  · rintro (h | ⟨t, hs, hp⟩)
    · exact ⟨empty, h, Or.inl rfl⟩
    · exact ⟨t, hs, Or.inr hp⟩

/-- A complete document is a valid prefix.  The converse fails, and the witness
below is what says so: only a final character that was cut is a prefix and not a
document. -/
theorem validPrefix_of_utf8Chars {b : Bytes} (h : Utf8Chars b) : ValidPrefix b :=
  (validPrefix_iff b).mpr (Or.inl h)

/-- The bytes RFC 3629 §4 lets a `UTF8-char` begin with: `UTF8-1`'s ASCII, or a
lead.  The leads `%xC2-DF`, `%xE0-EF` and `%xF0-F4` cover `0xC2..0xF4` exactly, so
what is left out is the continuations `0x80..0xBF`, the never-valid `0xC0`/`0xC1`
and the never-valid `0xF5..0xFF`. -/
def IsUtf8LeadByte (b : UInt8) : Prop := b < 0x80 ∨ (0xC2 ≤ b ∧ b ≤ 0xF4)

/-- Every character's encoding starts at a `IsUtf8LeadByte`, read off the
constructor whose first clause produced it. -/
theorem utf8Char_head {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest)
    {b0 : UInt8} (hb : b.head? = some b0) : IsUtf8LeadByte b0 := by
  unfold IsUtf8LeadByte
  cases h with
  | one hh =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inl hh
  | two h0 h0' _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' ⊢
      exact Or.inr ⟨by omega, by omega⟩
  | three₀ _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inr (by decide)
  | three₁ h0 h0' _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' ⊢
      exact Or.inr ⟨by omega, by omega⟩
  | three₂ _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inr (by decide)
  | three₃ h0 h0' _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' ⊢
      exact Or.inr ⟨by omega, by omega⟩
  | four₀ _ _ _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inr (by decide)
  | four₁ h0 h0' _ _ _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' ⊢
      exact Or.inr ⟨by omega, by omega⟩
  | four₂ _ _ _ _ _ _ =>
      rw [ByteString.head?_cons] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inr (by decide)

/-- A span whose head byte cannot begin a character parses nothing: the whole
argument is what is left. -/
theorem utf8Spans_eq_of_no_start {b0 : UInt8} {b' rest : Bytes}
    (hbad : ¬ IsUtf8LeadByte b0) (h : Utf8Spans (cons b0 b') rest) :
    rest = cons b0 b' := by
  rcases utf8Spans_cases h with hnil | ⟨b'', c, hc, _⟩
  · exact hnil
  · refine absurd (utf8Char_head hc ?_) hbad
    rw [ByteString.head?_cons]

/-- A byte string that begins with `cons b0 b'` begins with the byte `b0`: the
take has a head, and it is the string's. -/
theorem head?_eq_of_hasPrefix_cons {b : Bytes} {b0 : UInt8} {b' : Bytes}
    (h : HasPrefix b 0 (cons b0 b')) : b.head? = some b0 := by
  unfold HasPrefix at h
  rw [ByteString.drop_zero] at h
  have hlen : (cons b0 b').length = b'.toList.length + 1 := by
    rw [ByteString.length_cons]
    simp
  have hb : b.toList.take (b'.toList.length + 1) = b0 :: b'.toList := by
    have := congrArg (fun x : Bytes => x.toList) h
    rw [hlen, ByteString.toList_take, ByteString.toList_cons] at this
    exact this
  obtain ⟨x, xs, hbl⟩ : ∃ x xs, b.toList = x :: xs := by
    cases hbx : b.toList with
    | nil => rw [hbx] at hb; simp at hb
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [hbl] at hb
  simp only [List.take_succ_cons, List.cons.injEq] at hb
  rw [ByteString.head?_toList, hbl, hb.1]
  rfl

/-- A prefix of one character's encoding begins with that character's first
byte, so a byte that cannot begin a character cannot begin such a prefix. -/
theorem not_utf8PrefixOf_of_no_start {b0 : UInt8} {b' : Bytes}
    (hbad : ¬ IsUtf8LeadByte b0) : ¬ Utf8PrefixOf (cons b0 b') := by
  rintro ⟨-, b, c, r, hc, _hlen, hp⟩
  exact hbad (utf8Char_head hc (head?_eq_of_hasPrefix_cons hp))

/-- Every character's encoding has one of four shapes, by its constructor's own
byte count: `UTF8-1`'s single byte, `UTF8-2`'s two, `UTF8-3`'s three and
`UTF8-4`'s four.  The conclusion names no fixed argument, so the inversion needs
no unification against a constructor form. -/
theorem utf8Char_cases {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    (∃ b0 b', b = cons b0 b' ∧ b0 < 0x80) ∨
    (∃ b0 b1 b', b = cons b0 (cons b1 b')) ∨
    (∃ b0 b1 b2 b', b = cons b0 (cons b1 (cons b2 b'))) ∨
    (∃ b0 b1 b2 b3 b', b = cons b0 (cons b1 (cons b2 (cons b3 b')))) := by
  cases h with
  | one hh => exact Or.inl ⟨_, _, rfl, hh⟩
  | two _ _ _ _ => exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  | three₀ _ _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | three₁ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | three₂ _ _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | three₃ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | four₀ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩))
  | four₁ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩))
  | four₂ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩))

/-- A character on a one-byte string is `UTF8-1`: every longer shape needs a
second byte there, and `cons` is not empty. -/
theorem utf8Char_one_byte {b0 : UInt8} {c : Nat} {rest : Bytes}
    (h : Utf8Char (cons b0 empty) c rest) : b0 < 0x80 := by
  rcases utf8Char_cases h with ⟨x, x', hb, hx⟩ | ⟨y, y', y'', hb⟩ |
    ⟨z, z', z'', z''', hb⟩ | ⟨w, w', w'', w''', w'''', hb⟩
  · obtain ⟨rfl, -⟩ := ByteString.cons_inj.mp hb
    exact hx
  · exact absurd (ByteString.cons_inj.mp hb).2 (ByteString.cons_ne_empty y' y'').symm
  · exact absurd (ByteString.cons_inj.mp hb).2
      (ByteString.cons_ne_empty z' (cons z'' z''')).symm
  · exact absurd (ByteString.cons_inj.mp hb).2
      (ByteString.cons_ne_empty w' (cons w'' (cons w''' w''''))).symm

/-! ### The two relations' witnesses

The relations are not the same, and the witnesses below are what says so: a
complete document is both (`utf8Chars_two` is a `Utf8Chars`, hence by
`validPrefix_of_utf8Chars` a `ValidPrefix`), a lone lead is a valid prefix and
not a document (`validPrefix_lone_lead`, `not_utf8Chars_lone_lead`), and a lone
continuation is neither (`not_validPrefix_lone_cont`), which is the byte the DFA
restores at a document's end through `kl_tail_byte`. -/

/-- A two-byte character is a complete document: `UTF8-2`'s clause. -/
theorem utf8Chars_two : Utf8Chars (0xC3 +: 0xA9 +: empty) :=
  Utf8Spans.char
    (Utf8Char.two (b0 := 0xC3) (b1 := 0xA9) (rest := empty)
      (by decide) (by decide) (by decide) (by decide))
    (Utf8Spans.nil empty)

/-- A complete document is a valid prefix, at a two-byte character. -/
theorem validPrefix_two : ValidPrefix (0xC3 +: 0xA9 +: empty) :=
  validPrefix_of_utf8Chars utf8Chars_two

/-- A lone lead is a proper prefix of `UTF8-2`'s encoding. -/
theorem utf8PrefixOf_lone_lead : Utf8PrefixOf (0xC3 +: empty) := by
  have hlen : (0xC3 +: empty).length = 1 := by rw [ByteString.length_cons]; rfl
  have hlt : (0xC3 +: empty : Bytes).length < (0xC3 +: 0xA9 +: empty : Bytes).length := by
    rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons]
    omega
  have htake : (0xC3 +: 0xA9 +: empty : Bytes).take 1 = 0xC3 +: empty := by
    apply ByteString.eq_of_toList_eq
    simp [ByteString.toList_take, ByteString.toList_cons]
  refine ⟨ByteString.cons_ne_empty 0xC3 empty, 0xC3 +: 0xA9 +: empty, _, empty,
    Utf8Char.two (b0 := 0xC3) (b1 := 0xA9) (rest := empty)
      (by decide) (by decide) (by decide) (by decide), hlt, ?_⟩
  unfold HasPrefix
  rw [ByteString.drop_zero, hlen]
  exact htake

/-- A lone lead is a valid prefix: the truncated final character the window rule
accepts. -/
theorem validPrefix_lone_lead : ValidPrefix (0xC3 +: empty) := by
  refine ⟨0xC3 +: empty, Utf8Spans.nil _, Or.inr utf8PrefixOf_lone_lead⟩

/-- A lone lead is not a complete document: the asymmetry of the two corollaries,
at its smallest instance. -/
theorem not_utf8Chars_lone_lead : ¬ Utf8Chars (0xC3 +: empty) := by
  unfold Utf8Chars
  intro h
  rcases utf8Spans_cases h with hnil | ⟨b', c, hc, _⟩
  · exact (ByteString.cons_ne_empty 0xC3 empty) hnil.symm
  · exact absurd (utf8Char_one_byte hc) (by decide)

/-- A lone continuation is neither a document nor a prefix: no character begins
there. -/
theorem not_validPrefix_lone_cont : ¬ ValidPrefix (0x80 +: empty) := by
  have hbad : ¬ IsUtf8LeadByte 0x80 := by
    unfold IsUtf8LeadByte
    simp
  rintro ⟨t, hs, ht | hp⟩
  · have hparsed : t = 0x80 +: empty := utf8Spans_eq_of_no_start hbad hs
    rw [ht] at hparsed
    exact (ByteString.cons_ne_empty 0x80 empty) hparsed.symm
  · have hparsed : t = 0x80 +: empty := utf8Spans_eq_of_no_start hbad hs
    rw [hparsed] at hp
    exact not_utf8PrefixOf_of_no_start hbad hp

/-- Every encodable value is a scalar: the ranges above cannot denote a surrogate
and cannot exceed U+10FFFF. -/
theorem utf8_scalar {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    IsScalar c := by
  induction h with
  | one h =>
      unfold IsScalar
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat] at h
      omega
  | two _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | three₀ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | three₁ _ _ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | three₂ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | three₃ _ _ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | four₀ _ _ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | four₁ _ _ _ _ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega
  | four₂ _ _ _ _ _ _ =>
      unfold IsScalar
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at *
      omega

end LeanLLVM.JSON
