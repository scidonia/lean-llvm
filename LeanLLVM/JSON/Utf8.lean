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
