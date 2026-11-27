/-
The reader's own segmentation of a number lexeme, and the seams' hypotheses.

`JsonStage2NumFastSeams`'s digit-run ties take the reader's decomposition of the
lexeme as three hypotheses.  `t1_intRun_tie` takes

  `hint : intDigits d = d0 + (n - i0)`
  `hshape : d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0))`

and `t1_fracRun_tie`/`t1_fracCount_tie` take `hintF : fracDigits d = d0 + (n - i0)`
with the same `hshape` at the fraction's bytes.  Their `d` is
`StrtodReader.reader lex`'s output, and `i0`, `d0`, `n` are the emitted loops'
counters over the token `bs`.  The three hypotheses therefore say where the
*reader* cut a lexeme, and `StrtodReader` proves that cut: they are theorems
about the reading, not facts about the machine.  This module states the reader's
segmentation in the shape the seams consume and proves it, then discharges the
hypotheses at the counters the emitted scan enters its digit runs with.

**The general form.**  For `reader lex = some d`:

* `reader_int_segment` — the integer part's bytes are the lexeme's slice at the
  sign byte's length, of the run's length `intDigits d`;
* `reader_fr_segment` — the fraction's bytes, when there is one, are the slice
  one byte past the `int` part (the "shifted" form: `intDigits d` bytes and the
  `.` shift the fraction's offset), of length `fracDigits d`;
* `reader_ex_segment` — the exponent's digits are the lexeme's tail, the last
  `ds.length` bytes.

The three are read off `reader_ip_span`, `reader_fr_span` and `reader_ex_span`,
which already say the lexeme *is* the sign, the part's bytes and a remainder; the
slice is `List.drop_left`/`take_left` on that append.  No case on the lexeme's
shape is needed, and no normalisation is applied: the reader keeps leading zeros
of the exponent and trailing zeros of both parts, and its `int` part is exactly
the `takeWhile IsDigitB` run `body_cons_zero`/`body_cons_lead` cut, so the run is
maximal by definition (`d.ip` is that run, and the byte after it, if any, is the
remainder's first byte).

**The seams' indices.**  The emitted scan enters the integer run at
`i0 = negIndex b + 1`, `d0 = 1` and the fraction run at `i0 = fracStart`,
`d0 = 0`, over a token `bs` of length `n`.  Two shape facts translate the
reader's own offsets into those counters:

* `signBytes_length_eq_negIndex` — the sign byte's length is the scan's
  `negIndex` of the token's first byte;
* `reader_int_end_length`/`reader_fr_end_length` — a lexeme with no fraction and
  no exponent ends at the integer run, and one with a fraction but no exponent
  ends at the fraction run.  The second is the shifted form the absent exponent
  makes: the run reaches the token's end, so `n - fracStart` is `fracDigits d`.
  The case division is the reader's own: `suffix_eq_empty_of_no_frac_exp` and
  `suffix_eq_frac_of_frac_no_exp` say the suffix loop consumes no more bytes.

`intHead_of_reader` is the general integer case: the run stops at an in-lexeme
non-digit (`t1_headTie`'s `i1 = negIndex b + intDigits d`), so no end-of-token
shape is used.  `intRun_of_reader` is `t1_intRun_tie`'s `hint`/`hshape` at the
lexeme's end, and `fracRun_of_reader` is `t1_fracRun_tie`'s/`t1_fracCount_tie`'s
`hintF`/`hshape` at the fraction's end.  Each returns the conjunction the seam
takes, so a caller holding `reader lex = some d` supplies the hypotheses instead
of assuming them.  The seams' remaining side conditions are not reader facts:
`i0 ≤ n` follows by `omega` from the same length equation, and `d0 + n < 2 ^ 64`
is the token's word bound, which the caller has from its `readBytes`.

**What this does not close.**  These are the segmentation hypotheses only.  The
accumulator agreement (`NumFastAccumulatorAgreement`, `NumFastBodyArm`) still
takes the three out-of-line callees `num_d8_el1`, `num_el_el1` and
`stk_mul_u64` — `ub` at the walk's selection of the emitted dispatch
(`JsonStage2NumFastArm`) and answered from measured C text in
`JsonStage2NumFastCalls`, not from refined bodies — and tier 3's remaining
blocks (the `to_double` window and the region after `for.body.outer.i.i`).
Those are body-faithfulness obligations and are neither derived nor claimed
here.  Nothing here covers the exponent seam's `hacc`/`hes` either: those read
`%exp10` numerically, not as a byte span.

There is no `sorry`, `admit` or `native_decide` below, and the declarations'
axioms are pinned at the end.
-/
import LeanLLVM.Refinement.JsonStage2NumFastSeams
import LeanLLVM.StrtodReader

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine
open ByteString

/-! ### Slices of an append

The reader's spans are appends, so the segmentation is `drop`/`take` on the list
view.  The three lemmas below cut a slice at a prefix, after a prefix and one
byte, and at the end. -/

/-- The slice at a prefix: `pre ++ (mid ++ rest)` cut to `mid`. -/
theorem slice_append {α : Type} (pre mid rest : List α) :
    ((pre ++ (mid ++ rest)).drop pre.length).take mid.length = mid := by
  rw [List.drop_left, List.take_left]

/-- The slice after a prefix and one byte — the fraction's offset, one past the
`int` part and the `.` — cut to `mid`. -/
theorem slice_append_cons {α : Type} (a b : List α) (c : α) (mid rest : List α) :
    ((a ++ (b ++ (c :: (mid ++ rest)))).drop (a.length + b.length + 1)).take
        mid.length = mid := by
  have hsplit : a ++ (b ++ (c :: (mid ++ rest))) = (a ++ (b ++ [c])) ++ (mid ++ rest) := by
    simp
  rw [hsplit]
  have hlen : (a ++ (b ++ [c])).length = a.length + b.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  rw [← hlen]
  exact slice_append (a ++ (b ++ [c])) mid rest

/-- The slice at the end: the last `mid.length` bytes of `pre ++ mid`. -/
theorem slice_tail {α : Type} (pre mid : List α) :
    ((pre ++ mid).drop ((pre ++ mid).length - mid.length)).take mid.length = mid := by
  rw [List.length_append, Nat.add_sub_cancel, List.drop_left, List.take_length]

/-- The list view's length is the byte string's. -/
theorem data_toList_length (bs : Bytes) : bs.data.toList.length = bs.length := by
  rw [← ByteString.toList_eq_data_toList, ByteString.toList_length,
    ByteString.length_eq_size]

/-! ### The reader's own offsets

`reader_ip_span` says the lexeme is the sign byte, `d.ip` and a remainder, so the
integer part is the lexeme's slice at the sign byte.  The fraction's span puts
`fs` one byte past the `int` part and the `.`, and the exponent's span puts `ds`
at the end. -/

/-- **The integer run's slice**, in the list view the span lemma gives. -/
theorem reader_int_segment_toList {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) :
    d.ip.toList = (lex.toList.drop (Decimal.signBytes d.neg).length).take (intDigits d) := by
  obtain ⟨rest, hbytes⟩ := StrtodReader.reader_ip_span h
  have hsign : (Decimal.signBytes d.neg).toList.length = (Decimal.signBytes d.neg).length :=
    ByteString.toList_length _
  have hip : d.ip.toList.length = intDigits d := by
    simp [intDigits]
  rw [hbytes]
  simp only [ByteString.append_assoc, ByteString.toList_append]
  rw [← hsign, ← hip, List.drop_left, List.take_left]

/-- **The reader's integer run.**  The `int` bytes are the lexeme's slice after
the sign byte, of the run's length `intDigits d`: the seam's `hint`/`hshape` at
the reader's own offset. -/
theorem reader_int_segment {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) :
    d.ip.data.toList =
      (lex.data.toList.drop (Decimal.signBytes d.neg).length).take (intDigits d) := by
  simpa only [← ByteString.toList_eq_data_toList] using reader_int_segment_toList h

/-- The integer slice's length is the run's: the `hint` half at the reader's own
offset, in the form a caller reads off the slice. -/
theorem reader_int_run_length {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) :
    ((lex.data.toList.drop (Decimal.signBytes d.neg).length).take (intDigits d)).length
      = intDigits d := by
  rw [← reader_int_segment h, data_toList_length]
  simp only [intDigits]

/-- **The fraction's slice**, in the list view the span lemma gives. -/
theorem reader_fr_segment_toList {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {fs : Bytes} (hf : d.fr = some fs) :
    fs.toList =
      (lex.toList.drop ((Decimal.signBytes d.neg).length + intDigits d + 1)).take
        (fracDigits d) := by
  obtain ⟨rest, hbytes⟩ := StrtodReader.reader_fr_span h hf
  have hsign : (Decimal.signBytes d.neg).toList.length = (Decimal.signBytes d.neg).length :=
    ByteString.toList_length _
  have hip : d.ip.toList.length = intDigits d := by
    simp [intDigits]
  have hfr : fs.toList.length = fracDigits d := by
    simp [fracDigits, hf]
  rw [hbytes]
  simp only [ByteString.append_assoc, ByteString.toList_append, ByteString.toList_cons]
  rw [← hsign, ← hip, ← hfr]
  exact (slice_append_cons (Decimal.signBytes d.neg).toList d.ip.toList 0x2E
    fs.toList rest.toList).symm

/-- **The reader's fraction run.**  The digits after the `.` are the lexeme's
slice one byte past the `int` part, of length `fracDigits d`: the seam's `hintF`
and the fraction half of `hshape` at the reader's own offset. -/
theorem reader_fr_segment {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {fs : Bytes} (hf : d.fr = some fs) :
    fs.data.toList =
      (lex.data.toList.drop ((Decimal.signBytes d.neg).length + intDigits d + 1)).take
        (fracDigits d) := by
  simpa only [← ByteString.toList_eq_data_toList] using reader_fr_segment_toList h hf

/-- The fraction slice's length is the run's. -/
theorem reader_fr_run_length {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {fs : Bytes} (hf : d.fr = some fs) :
    ((lex.data.toList.drop
        ((Decimal.signBytes d.neg).length + intDigits d + 1)).take (fracDigits d)).length
      = fracDigits d := by
  rw [← reader_fr_segment h hf, data_toList_length]
  have hfd : fracDigits d = fs.length := by
    simp [fracDigits, hf]
  rw [hfd]

/-- **The exponent's digits are the lexeme's tail.**  The reader consumes the
maximal digit run after the marker and its optional sign byte to the end, so
`ds` is the last `ds.length` bytes. -/
theorem reader_ex_segment_toList {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {s : Bool} {ds : Bytes}
    (he : d.ex = some (s, ds)) :
    ds.toList =
      (lex.toList.drop (lex.toList.length - ds.toList.length)).take ds.toList.length := by
  obtain ⟨pre, m, sign, -, -, hbytes, -⟩ := StrtodReader.reader_ex_span h he
  have hlex : lex.toList = (pre.toList ++ (m :: sign.toList)) ++ ds.toList := by
    rw [hbytes]
    simp
  rw [hlex, slice_tail]

/-- **The reader's exponent run**, in the seams' list view. -/
theorem reader_ex_segment {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {s : Bool} {ds : Bytes}
    (he : d.ex = some (s, ds)) :
    ds.data.toList =
      (lex.data.toList.drop (lex.data.toList.length - ds.data.toList.length)).take
        ds.data.toList.length := by
  simpa only [← ByteString.toList_eq_data_toList] using reader_ex_segment_toList h he

/-! ### Where the suffix loop stops

A lexeme that records no fraction and no exponent ends at the integer run, and
one with a fraction but no exponent ends at the fraction run.  These are the
shape facts that turn the reader's offset into the token's end; both are cases
on `suffix`'s own cut. -/

/-- A suffix read that records no fraction and no exponent consumed no bytes. -/
theorem suffix_eq_empty_of_no_frac_exp {neg : Bool} {ip bs : Bytes} {d : Decimal}
    (h : StrtodReader.suffix neg ip bs = some d)
    (hfr : d.fr = none) (hex : d.ex = none) : bs = empty := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rfl
  · by_cases hdot : b = 0x2E
    · subst hdot
      rw [StrtodReader.suffix_cons_dot] at h
      by_cases hne : rest.takeWhile IsDigitB = empty
      · rw [ite_eq_left hne] at h
        exact absurd h (by simp)
      · rw [ite_eq_right hne] at h
        cases htail : StrtodReader.expTail (rest.dropWhile IsDigitB) with
        | none => rw [htail] at h; exact absurd h (by simp)
        | some ex =>
            rw [htail, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp at hfr
    · by_cases he65 : b = 0x65
      · subst he65
        rw [StrtodReader.suffix_cons_e] at h
        cases hpart : StrtodReader.expPart rest with
        | none => rw [hpart] at h; exact absurd h (by simp)
        | some ex =>
            rw [hpart, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp at hex
      · by_cases he45 : b = 0x45
        · subst he45
          rw [StrtodReader.suffix_cons_E] at h
          cases hpart : StrtodReader.expPart rest with
          | none => rw [hpart] at h; exact absurd h (by simp)
          | some ex =>
              rw [hpart, Option.map_some] at h
              simp only [Option.some.injEq] at h
              subst h
              simp at hex
        · rw [StrtodReader.suffix_cons_other rest hdot he65 he45] at h
          exact absurd h (by simp)

/-- A `some none` exponent tail has no bytes: the marker was absent. -/
theorem expTail_eq_empty_of_none {bs : Bytes} {ex : Option (Bool × Bytes)}
    (h : StrtodReader.expTail bs = some ex) (hex : ex = none) : bs = empty := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rfl
  · by_cases he65 : b = 0x65
    · subst he65
      rw [StrtodReader.expTail_cons_e] at h
      cases hpart : StrtodReader.expPart rest with
      | none => rw [hpart] at h; exact absurd h (by simp)
      | some r =>
          rw [hpart, Option.map_some] at h
          simp only [Option.some.injEq] at h
          subst h
          simp at hex
    · by_cases he45 : b = 0x45
      · subst he45
        rw [StrtodReader.expTail_cons_E] at h
        cases hpart : StrtodReader.expPart rest with
        | none => rw [hpart] at h; exact absurd h (by simp)
        | some r =>
            rw [hpart, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp at hex
      · rw [StrtodReader.expTail_cons_other rest he65 he45] at h
        exact absurd h (by simp)

/-- A suffix read that records a fraction but no exponent ends with the
fraction's digits: the absent exponent is what makes the run reach the end. -/
theorem suffix_eq_frac_of_frac_no_exp {neg : Bool} {ip bs : Bytes} {d : Decimal}
    {fs : Bytes} (h : StrtodReader.suffix neg ip bs = some d) (hfr : d.fr = some fs)
    (hex : d.ex = none) : bs = 0x2E +: fs := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [StrtodReader.suffix_end] at h
    simp only [Option.some.injEq] at h
    subst h
    simp at hfr
  · by_cases hdot : b = 0x2E
    · subst hdot
      rw [StrtodReader.suffix_cons_dot] at h
      by_cases hne : rest.takeWhile IsDigitB = empty
      · rw [ite_eq_left hne] at h
        exact absurd h (by simp)
      · rw [ite_eq_right hne] at h
        cases htail : StrtodReader.expTail (rest.dropWhile IsDigitB) with
        | none => rw [htail] at h; exact absurd h (by simp)
        | some ex =>
            rw [htail, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [Option.some.injEq] at hfr
            have hnil := expTail_eq_empty_of_none htail hex
            have hrest : rest.takeWhile IsDigitB = rest := by
              have hh := ByteString.takeWhile_append_dropWhile rest IsDigitB
              rw [hnil, ByteString.append_empty] at hh
              exact hh
            rw [← hfr, hrest]
    · by_cases he65 : b = 0x65
      · subst he65
        rw [StrtodReader.suffix_cons_e] at h
        cases hpart : StrtodReader.expPart rest with
        | none => rw [hpart] at h; exact absurd h (by simp)
        | some ex =>
            rw [hpart, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp at hfr
      · by_cases he45 : b = 0x45
        · subst he45
          rw [StrtodReader.suffix_cons_E] at h
          cases hpart : StrtodReader.expPart rest with
          | none => rw [hpart] at h; exact absurd h (by simp)
          | some ex =>
              rw [hpart, Option.map_some] at h
              simp only [Option.some.injEq] at h
              subst h
              simp at hfr
        · rw [StrtodReader.suffix_cons_other rest hdot he65 he45] at h
          exact absurd h (by simp)

/-- A body read that records no fraction and no exponent is exactly its `int`
part. -/
theorem body_eq_ip_of_no_frac_exp {neg : Bool} {bs : Bytes} {d : Decimal}
    (h : StrtodReader.body neg bs = some d) (hfr : d.fr = none) (hex : d.ex = none) :
    bs = d.ip := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [StrtodReader.body_empty] at h
    exact absurd h (by simp)
  · by_cases h0 : b = 0x30
    · subst h0
      rw [StrtodReader.body_cons_zero] at h
      obtain ⟨-, hip⟩ := StrtodReader.suffix_neg_ip h
      have hnil := suffix_eq_empty_of_no_frac_exp h hfr hex
      rw [hnil, hip]
    · by_cases hl : 0x31 ≤ b ∧ b ≤ 0x39
      · obtain ⟨h1, h2⟩ := hl
        rw [StrtodReader.body_cons_lead neg rest h1 h2] at h
        obtain ⟨-, hip⟩ := StrtodReader.suffix_neg_ip h
        have hnil := suffix_eq_empty_of_no_frac_exp h hfr hex
        have hrest : rest = rest.takeWhile IsDigitB := by
          have hh := ByteString.takeWhile_append_dropWhile rest IsDigitB
          rw [hnil, ByteString.append_empty] at hh
          exact hh.symm
        rw [hip, ← hrest]
      · rw [StrtodReader.body_cons_other rest h0 hl] at h
        exact absurd h (by simp)

/-- A body read that records a fraction but no exponent is its `int` part, the
`.`, and the fraction's digits. -/
theorem body_eq_ip_frac_of_no_exp {neg : Bool} {bs : Bytes} {d : Decimal} {fs : Bytes}
    (h : StrtodReader.body neg bs = some d) (hfr : d.fr = some fs) (hex : d.ex = none) :
    bs = d.ip ++ (0x2E +: fs) := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [StrtodReader.body_empty] at h
    exact absurd h (by simp)
  · by_cases h0 : b = 0x30
    · subst h0
      rw [StrtodReader.body_cons_zero] at h
      obtain ⟨-, hip⟩ := StrtodReader.suffix_neg_ip h
      have hs := suffix_eq_frac_of_frac_no_exp h hfr hex
      rw [hs, hip, ByteString.cons_append, ByteString.empty_append]
    · by_cases hl : 0x31 ≤ b ∧ b ≤ 0x39
      · obtain ⟨h1, h2⟩ := hl
        rw [StrtodReader.body_cons_lead neg rest h1 h2] at h
        obtain ⟨-, hip⟩ := StrtodReader.suffix_neg_ip h
        have hs := suffix_eq_frac_of_frac_no_exp h hfr hex
        rw [hip, ByteString.cons_append, ← hs, ByteString.takeWhile_append_dropWhile]
      · rw [StrtodReader.body_cons_other rest h0 hl] at h
        exact absurd h (by simp)

/-- A lexeme with no fraction and no exponent is its sign and `int` part. -/
theorem reader_int_end {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) (hfr : d.fr = none) (hex : d.ex = none) :
    lex = Decimal.signBytes d.neg ++ d.ip := by
  rcases ByteString.eq_empty_or_cons lex with rfl | ⟨b, rest, rfl⟩
  · rw [StrtodReader.reader_empty] at h
    exact absurd h (by simp)
  · by_cases hm : b = 0x2D
    · subst hm
      rw [StrtodReader.reader_cons_minus] at h
      have hip := body_eq_ip_of_no_frac_exp h hfr hex
      have hneg := (StrtodReader.body_neg_ip h).1
      rw [hneg, Decimal.signBytes_true, hip, ByteString.cons_append,
        ByteString.empty_append]
    · rw [StrtodReader.reader_cons_other hm] at h
      have hip := body_eq_ip_of_no_frac_exp h hfr hex
      have hneg := (StrtodReader.body_neg_ip h).1
      rw [hneg, Decimal.signBytes_false, ByteString.empty_append, hip]

/-- A lexeme with a fraction and no exponent is its sign, `int` part, `.`, and
the fraction's digits. -/
theorem reader_fr_end {lex : Bytes} {d : Decimal} {fs : Bytes}
    (h : StrtodReader.reader lex = some d) (hfr : d.fr = some fs) (hex : d.ex = none) :
    lex = Decimal.signBytes d.neg ++ d.ip ++ (0x2E +: fs) := by
  rcases ByteString.eq_empty_or_cons lex with rfl | ⟨b, rest, rfl⟩
  · rw [StrtodReader.reader_empty] at h
    exact absurd h (by simp)
  · by_cases hm : b = 0x2D
    · subst hm
      rw [StrtodReader.reader_cons_minus] at h
      have hbody := body_eq_ip_frac_of_no_exp h hfr hex
      have hneg := (StrtodReader.body_neg_ip h).1
      rw [hneg, Decimal.signBytes_true, hbody, ByteString.cons_append,
        ByteString.empty_append, ByteString.cons_append]
    · rw [StrtodReader.reader_cons_other hm] at h
      have hbody := body_eq_ip_frac_of_no_exp h hfr hex
      have hneg := (StrtodReader.body_neg_ip h).1
      rw [hneg, Decimal.signBytes_false, ByteString.empty_append, hbody]

/-- The integer-only lexeme's length: the run reaches the token's end. -/
theorem reader_int_end_length {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) (hfr : d.fr = none) (hex : d.ex = none) :
    lex.length = (Decimal.signBytes d.neg).length + intDigits d := by
  rw [reader_int_end h hfr hex, ByteString.length_append]
  simp only [intDigits]

/-- The fraction-only lexeme's length: the run reaches the token's end after the
`int` part and the `.`. -/
theorem reader_fr_end_length {lex : Bytes} {d : Decimal} {fs : Bytes}
    (h : StrtodReader.reader lex = some d) (hfr : d.fr = some fs) (hex : d.ex = none) :
    lex.length = (Decimal.signBytes d.neg).length + intDigits d + 1 + fracDigits d := by
  have hfd : fracDigits d = fs.length := by
    simp [fracDigits, hfr]
  rw [reader_fr_end h hfr hex, hfd, ByteString.length_append, ByteString.length_append,
    ByteString.length_cons]
  simp only [intDigits]
  omega

/-- The reader's `int` part is never empty: `0` alone or a lead digit and a
run. -/
theorem intDigits_pos_of_reader {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) : 0 < intDigits d := by
  have hwf := StrtodReader.reader_wf h
  obtain ⟨hip, -⟩ := hwf
  obtain ⟨c, B, hc, -⟩ := StrtodReader.intPart_head hip
  rw [intDigits, hc]
  simp only [ByteString.length_cons]
  omega

/-- The sign byte's length is the emitted scan's sign index at the token's first
byte. -/
theorem signBytes_length_eq_negIndex {lex : Bytes} {d : Decimal}
    (h : StrtodReader.reader lex = some d) {b : UInt8} {rest : Bytes}
    (hlex : lex = b +: rest) :
    (Decimal.signBytes d.neg).length = NumFastStarts.negIndex b := by
  subst hlex
  by_cases hb : b = 0x2D
  · subst hb
    rw [StrtodReader.reader_cons_minus] at h
    have hneg := (StrtodReader.body_neg_ip h).1
    rw [hneg]
    decide
  · rw [StrtodReader.reader_cons_other hb] at h
    have hneg := (StrtodReader.body_neg_ip h).1
    rw [hneg, Decimal.signBytes_false]
    have hz : NumFastStarts.negIndex b = 0 := by
      simp [NumFastStarts.negIndex, hb]
    rw [hz]
    exact ByteString.length_empty

/-! ### The seams' hypotheses at the emitted counters

The three wrappers return exactly the conjunctions the ties take, at
`i0 = negIndex b + 1`, `d0 = 1` for the integer run and `i0 = fracStart`,
`d0 = 0` for the fraction's. -/

/-- **The integer run's segmentation at the head.**  `t1_headTie`'s `hint` and
`hshape` at the scan's entry counters and the run's stop `i1 = negIndex b +
intDigits d`.  The run stops at an in-lexeme non-digit, so no end-of-token shape
is used: the reader's maximal digit run *is* the stop. -/
theorem intHead_of_reader {lex : Bytes} {d : Decimal} {bs : List UInt8} {b : UInt8}
    {rest : Bytes} {i0 d0 i1 : Nat}
    (hread : StrtodReader.reader lex = some d) (hlex : lex = b +: rest)
    (hbs : bs = lex.data.toList)
    (hi0 : i0 = NumFastStarts.negIndex b + 1) (hd0 : d0 = 1)
    (hi1 : i1 = NumFastStarts.negIndex b + intDigits d) :
    intDigits d = d0 + (i1 - i0) ∧
      d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (i1 - i0)) := by
  have hsl := signBytes_length_eq_negIndex hread hlex
  have hpos := intDigits_pos_of_reader hread
  have hidx : NumFastStarts.negIndex b + 1 - 1 = NumFastStarts.negIndex b := by omega
  have hlen : 1 + (NumFastStarts.negIndex b + intDigits d -
      (NumFastStarts.negIndex b + 1)) = intDigits d := by omega
  refine ⟨?_, ?_⟩
  · rw [hi0, hd0, hi1]
    omega
  · rw [hi0, hd0, hi1, hidx, hlen, hbs, ← hsl]
    exact reader_int_segment hread

/-- **The integer run's segmentation at the lexeme's end.**  `t1_intRun_tie`'s
`hint` and `hshape` at `i0 = negIndex b + 1`, `d0 = 1`, `n = bs.length`: with no
fraction and no exponent the run reaches the token's end. -/
theorem intRun_of_reader {lex : Bytes} {d : Decimal} {bs : List UInt8} {b : UInt8}
    {rest : Bytes} {i0 d0 n : Nat}
    (hread : StrtodReader.reader lex = some d) (hlex : lex = b +: rest)
    (hbs : bs = lex.data.toList)
    (hfr : d.fr = none) (hex : d.ex = none)
    (hi0 : i0 = NumFastStarts.negIndex b + 1) (hd0 : d0 = 1) (hn : n = bs.length) :
    intDigits d = d0 + (n - i0) ∧
      d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)) := by
  have hsl := signBytes_length_eq_negIndex hread hlex
  have hpos := intDigits_pos_of_reader hread
  have hlen := reader_int_end_length hread hfr hex
  have hbslen : bs.length = (Decimal.signBytes d.neg).length + intDigits d := by
    rw [hbs, data_toList_length, hlen]
  have hidx : NumFastStarts.negIndex b + 1 - 1 = NumFastStarts.negIndex b := by omega
  have htake : 1 + (n - (NumFastStarts.negIndex b + 1)) = intDigits d := by
    rw [hn, hbslen, ← hsl]
    omega
  refine ⟨?_, ?_⟩
  · rw [hi0, hd0, hn, hbslen, ← hsl]
    omega
  · rw [hi0, hd0, hidx, htake, hbs, ← hsl]
    exact reader_int_segment hread

/-- **The fraction run's segmentation at the lexeme's end.**
`t1_fracRun_tie`'s/`t1_fracCount_tie`'s `hintF` and `hshape` at
`i0 = signLen + intDigits d + 1` (the byte after the `.`), `d0 = 0`,
`n = bs.length`: with no exponent the run reaches the token's end. -/
theorem fracRun_of_reader {lex : Bytes} {d : Decimal} {bs : List UInt8} {fs : Bytes}
    {i0 d0 n : Nat}
    (hread : StrtodReader.reader lex = some d) (hfr : d.fr = some fs)
    (hex : d.ex = none) (hbs : bs = lex.data.toList)
    (hi0 : i0 = (Decimal.signBytes d.neg).length + intDigits d + 1)
    (hd0 : d0 = 0) (hn : n = bs.length) :
    fracDigits d = d0 + (n - i0) ∧
      fs.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)) := by
  have hlen := reader_fr_end_length hread hfr hex
  have hbslen : bs.length = (Decimal.signBytes d.neg).length + intDigits d + 1 + fracDigits d := by
    rw [hbs, data_toList_length, hlen]
  refine ⟨?_, ?_⟩
  · rw [hi0, hd0, Nat.zero_add, hn, hbslen, Nat.add_sub_cancel_left]
  · rw [hi0, hd0, Nat.sub_zero, Nat.zero_add, hn, hbslen, Nat.add_sub_cancel_left, hbs]
    exact reader_fr_segment hread hfr

/-! ### Axiom footprints -/

#print axioms slice_append
#print axioms slice_append_cons
#print axioms slice_tail
#print axioms data_toList_length
#print axioms reader_int_segment_toList
#print axioms reader_int_segment
#print axioms reader_int_run_length
#print axioms reader_fr_segment_toList
#print axioms reader_fr_segment
#print axioms reader_fr_run_length
#print axioms reader_ex_segment_toList
#print axioms reader_ex_segment
#print axioms suffix_eq_empty_of_no_frac_exp
#print axioms expTail_eq_empty_of_none
#print axioms suffix_eq_frac_of_frac_no_exp
#print axioms body_eq_ip_of_no_frac_exp
#print axioms body_eq_ip_frac_of_no_exp
#print axioms reader_int_end
#print axioms reader_fr_end
#print axioms reader_int_end_length
#print axioms reader_fr_end_length
#print axioms intDigits_pos_of_reader
#print axioms signBytes_length_eq_negIndex
#print axioms intHead_of_reader
#print axioms intRun_of_reader
#print axioms fracRun_of_reader

end LeanLLVM.Refinement
