/-
The reader both conversion proofs take as a parameter.

`StrtodTier1.emittedRefinesOn_tier1` and `StrtodTier3.emittedRefinesOn_tier3`
each take `read : Bytes → Option Decimal` with

  `hread : ∀ d : Decimal, d.wellFormed → read d.lexeme = some d`,

"the emitted scanner's own reading".  Neither proof establishes it: the tiers
prove what the conversion does with a decomposition, and the decomposition is
assumed to be what the scanner reads.  This module states that assumption field
by field, models the scanner's byte loops, and proves the round trip.

**The statement, field by field.**  For `d` well formed — `IntPart d.ip`,
`Digits` on the fraction when there is one, `Digits` on the exponent when there
is one — the emitted scan of `d.lexeme` yields exactly `d`:

* `neg` — `d.lexeme` starts with `0x2D` (or does not);
* `ip` — after the sign, `0` alone, or a `1`–`9` lead and the maximal following
  digit run: `d.ip`'s bytes;
* `fr` — the byte after `int` is `0x2E` and the maximal digit run after it is
  `d.fr`'s digits, and `fr` is `none` exactly when there is no `.`;
* `ex` — the byte after that is `0x65`/`0x45`, its optional sign byte is the
  recorded sign (`Decimal`'s `Bool`, `true` for `-`), and the maximal digit run
  after it is `d.ex`'s digits, with nothing left over.

`reader_lexeme` proves it, so `hread` is discharged at `reader` and the two
tier statements can be instantiated without a reader parameter
(`tier1_no_reader`, `tier3_no_reader` below).

**Was there a model?**  Yes, for the decision: `LeanLLVM.JSON.numLexB`
(`JSON/Scan.lean`) is the accepting scan of `[ minus ] int [ frac ] [ exp ]`,
with `numLexB_spec` and `numLexB_complete` against `RfcNumber` — sound and
complete, and written over the same `takeWhile IsDigitB` runs the emitted
`while` loops compute.  It returns a `Bool`, though: nothing in the tree turns
an accepted lexeme into the decomposition the tiers consume.  `reader` is that
missing half, and `reader_isSome_eq_numLexB` proves its accept/refuse decision
is `numLexB`'s, so the model here is the tree's model plus a field extraction,
not a second scanner.

**How faithful is it?**  Field level, provably: the sign byte, `int`'s cut (the
`0`-alone rule), the fraction's run and non-emptiness, the exponent's marker,
sign byte and run, and the whole-input requirement — the same `*err` exits and
the same `i != n` check.  It is faithful to the *counts and segmentation* the
tiers consume (`StrtodRefine.intDigits`, `fracDigits`, `expValue`), and not to
the emitted accumulators' word sizes: `num_fast_el1` stops adding into `ip`/
`fr` past 19 digits and saturates its exponent at 100000, and `to_double`
windows its digits at `STK_DIGITS` (768) behind a sticky bit.  Those are not
part of the decomposition and are not assumed here — they are where the tiers'
own proofs live: tier 1 is taken only at `digitCount d ≤ 15`, where nothing
truncates, and tier 3's `windowOf`/`stkDrop`/sticky bit are proved against the
exact `Decimal.mantissa`, so a truncated accumulator never has to be modelled.

So the model stands in for the emitted body's *reading*, and what remains
outside Lean is narrower than the original hypothesis: that the three C loops'
locals (`ip`, `fr`, `idig`, `fdig`, `exp10` in `num_fast_el1`; `dig`, `T`, `F`,
`lead`, `top`, `sticky` in `to_double`) hold the fields this module returns.
That is a per-local state equivalence over about ten variables, with no
arithmetic content, and it is the pipeline's existing body-faithfulness seam
(`stage2.c` has no Lean semantics anywhere in the tree) rather than a new one.

**Proved here.**  `reader_lexeme` (the hypothesis), `reader_wf` (accepted input
is grammatical), `reader_sound` (accepted input is a number lexeme),
`reader_complete` (every number lexeme is accepted), `reader_isSome_eq_numLexB`
(the decision is the tree's), and the field facts: the `0`-alone rule, the
refusals (empty input, a lone `-`, a bare `.`, an empty fraction or exponent, a
trailing byte, a leading `+`, `00`), `-0`, exponent sign and magnitude with its
leading zeros, and the mantissa/digit correspondence.

**Assumed.**  The two tier modules' own statements (`EmittedRefinesOn` at
`tier1Emitted`/`tier3Emitted`), which this module instantiates rather than
reaches into, and the C locals' agreement above.

There is no `sorry`, `admit` or `native_decide` below, and the declarations'
axioms are pinned at the end of the file.
-/
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Strtod
import LeanLLVM.StrtodTier1
import LeanLLVM.StrtodTier3

set_option autoImplicit false

namespace LeanLLVM.StrtodReader

open LeanLLVM.JSON
open ByteString

/-- A concrete byte string from a list of byte values. -/
def bytes (cs : List Nat) : Bytes := ByteString.literal (cs.map UInt8.ofNat)

/-! ### The emitted scanner's field reading

`kernel/json/stage2.c`'s `num_scan` (`:152`) and `num_fast_el1` (`:379`) read a
number lexeme with the same three loops: the optional `minus`, `int`'s digit run
cut at the `.`/`e`, the optional `.` and its digit run, and the optional
`e`/`E`, its sign byte and its digit run.  `to_double` (`:647`) reads the same
three loops a second time for the fallback.

`reader` is that reading as a function to `Decimal`, the decomposition the two
conversion proofs take as a parameter.  Each field is the bytes the emitted loop
consumes:

* `neg` — the leading `0x2D`'s presence;
* `ip` — `int`'s bytes, `0` alone or a `1`–`9` lead and its maximal digit run;
* `fr` — the `.`'s following maximal digit run, `none` when there is no `.`;
* `ex` — the exponent marker's optional `+`/`-` (recorded as `Decimal`'s `Bool`,
  `true` for `-`) and its maximal digit run.

The digit runs are `ByteString.takeWhile IsDigitB`, which is the emitted
`while (p[i] >= '0' && p[i] <= '9') i++;` loop: maximal munch.  A lexeme is
refused (`none`) when a loop's run is empty where the grammar needs one byte, or
when a byte is left over — the emitted `i != n` check, and the `*err` returns at
the same points. -/

/-- The bytes after an `e`: `[ minus / plus ] 1*DIGIT`, exhausted. -/
def expDigits (sign : Bool) (bs : Bytes) : Option (Bool × Bytes) :=
  let ds := bs.takeWhile IsDigitB
  if ds = empty then none
  else if bs.dropWhile IsDigitB = empty then some (sign, ds) else none

/-- The bytes after the `e`/`E`: an optional sign byte, then `1*DIGIT`. -/
def expPart (bs : Bytes) : Option (Bool × Bytes) :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      if decide (b = 0x2B) then expDigits false (literal rest)
      else if decide (b = 0x2D) then expDigits true (literal rest)
      else expDigits false (b +: literal rest)

/-- `[ exp ]` at the end of a lexeme: nothing, or `e`/`E` and the exponent,
with nothing after. -/
def expTail (bs : Bytes) : Option (Option (Bool × Bytes)) :=
  match bs.data.toList with
  | [] => some none
  | b :: rest =>
      if decide (b = 0x65) || decide (b = 0x45) then (expPart (literal rest)).map some
      else none

/-- The bytes after an `int`: an optional `.` and its `1*DIGIT`, then an
optional exponent, and nothing after. -/
def suffix (neg : Bool) (ip : Bytes) (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => some ⟨neg, ip, none, none⟩
  | b :: rest =>
      if decide (b = 0x2E) then
        let tail : Bytes := literal rest
        let fs := tail.takeWhile IsDigitB
        if fs = empty then none
        else (expTail (tail.dropWhile IsDigitB)).map fun ex => ⟨neg, ip, some fs, ex⟩
      else if decide (b = 0x65) || decide (b = 0x45) then
        (expPart (literal rest)).map fun ex => ⟨neg, ip, none, some ex⟩
      else none

/-- The bytes after the optional `minus`: `int [ frac ] [ exp ]`, exhausted. -/
def body (neg : Bool) (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      let tail : Bytes := literal rest
      if decide (b = 0x30) then suffix neg (0x30 +: empty) tail
      else if 0x31 ≤ b ∧ b ≤ 0x39 then
        suffix neg (b +: tail.takeWhile IsDigitB) (tail.dropWhile IsDigitB)
      else none

/-- `[ minus ] int [ frac ] [ exp ]`, exhausted: the emitted scanner's reading
of a number lexeme, as the decomposition it accumulates. -/
def reader (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      if decide (b = 0x2D) then body true (literal rest)
      else body false (literal (b :: rest))

/-! ### The reader's equations

One equation per shape: the form the proofs rewrite with.  The definitions match
on the carrier's list view, so each equation first pushes the byte and then
collects the tail with `literal_data_toList`. -/

theorem reader_cons_minus (bs : Bytes) : reader (0x2D +: bs) = body true bs := by
  simp [reader, ByteString.data_toList_cons, literal_data_toList]

theorem reader_cons_other {b : UInt8} (hb : b ≠ 0x2D) (bs : Bytes) :
    reader (b +: bs) = body false (b +: bs) := by
  simp [reader, ByteString.data_toList_cons, literal_cons, literal_data_toList, hb]

theorem body_cons_zero (neg : Bool) (bs : Bytes) :
    body neg (0x30 +: bs) = suffix neg (0x30 +: empty) bs := by
  simp [body, ByteString.data_toList_cons, literal_data_toList]

theorem body_cons_lead (neg : Bool) {b : UInt8} (bs : Bytes)
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) :
    body neg (b +: bs) = suffix neg (b +: bs.takeWhile IsDigitB) (bs.dropWhile IsDigitB) := by
  have h30 : b ≠ 0x30 := by
    intro h; subst h; exact absurd h1 (by decide)
  simp [body, ByteString.data_toList_cons, literal_data_toList, h30, h1, h2]

theorem suffix_cons_dot {neg : Bool} {ip : Bytes} (bs : Bytes) :
    suffix neg ip (0x2E +: bs) =
      (if bs.takeWhile IsDigitB = empty then none
       else (expTail (bs.dropWhile IsDigitB)).map
         fun ex => ⟨neg, ip, some (bs.takeWhile IsDigitB), ex⟩) := by
  simp [suffix, ByteString.data_toList_cons, literal_data_toList]

theorem suffix_cons_e {neg : Bool} {ip : Bytes} (bs : Bytes) :
    suffix neg ip (0x65 +: bs) =
      (expPart bs).map fun ex => ⟨neg, ip, none, some ex⟩ := by
  simp [suffix, ByteString.data_toList_cons, literal_data_toList]

theorem suffix_cons_E {neg : Bool} {ip : Bytes} (bs : Bytes) :
    suffix neg ip (0x45 +: bs) =
      (expPart bs).map fun ex => ⟨neg, ip, none, some ex⟩ := by
  simp [suffix, ByteString.data_toList_cons, literal_data_toList]

theorem expTail_cons_e (bs : Bytes) : expTail (0x65 +: bs) = (expPart bs).map some := by
  simp [expTail, ByteString.data_toList_cons, literal_data_toList]

theorem expTail_cons_E (bs : Bytes) : expTail (0x45 +: bs) = (expPart bs).map some := by
  simp [expTail, ByteString.data_toList_cons, literal_data_toList]

theorem expPart_cons_plus (bs : Bytes) : expPart (0x2B +: bs) = expDigits false bs := by
  simp [expPart, ByteString.data_toList_cons, literal_data_toList]

theorem expPart_cons_minus (bs : Bytes) : expPart (0x2D +: bs) = expDigits true bs := by
  simp [expPart, ByteString.data_toList_cons, literal_data_toList]

theorem expPart_cons_digit {b : UInt8} (bs : Bytes) (hb : b ≠ 0x2B) (hc : b ≠ 0x2D) :
    expPart (b +: bs) = expDigits false (b +: bs) := by
  simp [expPart, ByteString.data_toList_cons, literal_data_toList, hb, hc]

/-! ### The byte facts the parse tests

The emitted code's byte constants, and the two runs the loops cut. -/

theorem isDigitB_zero : IsDigitB 0x30 = true := by decide
theorem isDigitB_dot : IsDigitB 0x2E = false := by decide
theorem isDigitB_e : IsDigitB 0x65 = false := by decide
theorem isDigitB_E : IsDigitB 0x45 = false := by decide
theorem isDigitB_plus : IsDigitB 0x2B = false := by decide
theorem isDigitB_minus : IsDigitB 0x2D = false := by decide

theorem isDigitB_of_lead {b : UInt8} (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) :
    IsDigitB b = true := by
  simp only [IsDigitB, decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨UInt8.le_trans (by decide) h1, h2⟩

theorem takeWhile_ndigit {b : UInt8} (hb : IsDigitB b = false) (rest : Bytes) :
    (b +: rest).takeWhile IsDigitB = empty := by
  rw [ByteString.takeWhile_cons, ite_eq_right (by rw [hb]; simp)]

theorem dropWhile_ndigit {b : UInt8} (hb : IsDigitB b = false) (rest : Bytes) :
    (b +: rest).dropWhile IsDigitB = b +: rest := by
  rw [ByteString.dropWhile_cons, ite_eq_right (by rw [hb]; simp)]

theorem takeWhile_append_digits {ds : Bytes} (h : Digits0 ds) (rest : Bytes) :
    (ds ++ rest).takeWhile IsDigitB = ds ++ rest.takeWhile IsDigitB :=
  ByteString.takeWhile_append_of_pos (digits0_all h) rest

theorem dropWhile_append_digits {ds : Bytes} (h : Digits0 ds) (rest : Bytes) :
    (ds ++ rest).dropWhile IsDigitB = rest.dropWhile IsDigitB :=
  ByteString.dropWhile_append_of_pos (digits0_all h) rest

theorem digits_takeWhile {ds : Bytes} (h : Digits ds) : ds.takeWhile IsDigitB = ds :=
  takeWhile_digits (digits0_of_digits h)

theorem digits_dropWhile {ds : Bytes} (h : Digits ds) : ds.dropWhile IsDigitB = empty :=
  dropWhile_digits (digits0_of_digits h)

theorem digits_ne_empty {ds : Bytes} (h : Digits ds) : ds ≠ empty := by
  cases h with
  | one _ => exact ByteString.cons_ne_empty _ _
  | more _ _ => exact ByteString.cons_ne_empty _ _

theorem digits_shape {ds : Bytes} (h : Digits ds) : ∃ b rest, ds = b +: rest := by
  cases h with
  | one _ => exact ⟨_, _, rfl⟩
  | more _ _ => exact ⟨_, _, rfl⟩

/-- A run whose leading digit run is empty does not start with a digit, so the
`dropWhile` loop cuts nothing. -/
theorem dropWhile_of_takeWhile_eq_empty {bs : Bytes}
    (h : bs.takeWhile IsDigitB = empty) : bs.dropWhile IsDigitB = bs := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [ByteString.dropWhile_empty]
  · rw [ByteString.takeWhile_cons] at h
    by_cases hb : IsDigitB b = true
    · rw [ite_eq_left hb] at h
      exact absurd h (ByteString.cons_ne_empty b _)
    · have hf : IsDigitB b = false := by cases hh : IsDigitB b <;> simp_all
      exact dropWhile_ndigit hf rest

/-! ### The body's reading, split at the `int` part -/

theorem body_zero (neg : Bool) (suf : Bytes) :
    body neg (0x30 +: suf) = suffix neg (0x30 +: empty) suf :=
  body_cons_zero neg suf

theorem body_lead (neg : Bool) {b : UInt8} (bs suf : Bytes)
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs)
    (hsuf : suf.takeWhile IsDigitB = empty) :
    body neg (b +: (bs ++ suf)) = suffix neg (b +: bs) suf := by
  rw [body_cons_lead neg (bs ++ suf) h1 h2]
  rw [takeWhile_append_digits hr, hsuf, ByteString.append_empty,
    dropWhile_append_digits hr, dropWhile_of_takeWhile_eq_empty hsuf]

/-! ### The suffix's reading

The four shapes `Decimal.body` builds, each read back. -/

theorem suffix_end {neg : Bool} {ip : Bytes} :
    suffix neg ip empty = some ⟨neg, ip, none, none⟩ := rfl

theorem expDigits_of_digits {sign : Bool} {ds : Bytes} (h : Digits ds) :
    expDigits sign ds = some (sign, ds) := by
  obtain ⟨b, rest, rfl⟩ := digits_shape h
  have hd0 : Digits0 (b +: rest) := digits0_of_digits h
  simp only [expDigits]
  rw [takeWhile_digits hd0, dropWhile_digits hd0]
  rw [ite_eq_right (ByteString.cons_ne_empty b rest), ite_eq_left rfl]

theorem expPart_digits {ds : Bytes} (hds : Digits ds) :
    expPart ds = some (false, ds) := by
  obtain ⟨b, rest, rfl⟩ := digits_shape hds
  have hbdigit : IsDigitB b = true :=
    digits_all hds b (ByteString.mem_cons_self b rest)
  have hb : b ≠ 0x2B := by
    intro h; subst h; rw [isDigitB_plus] at hbdigit; exact absurd hbdigit (by simp)
  have hc : b ≠ 0x2D := by
    intro h; subst h; rw [isDigitB_minus] at hbdigit; exact absurd hbdigit (by simp)
  rw [expPart_cons_digit rest hb hc, expDigits_of_digits hds]

theorem expPart_minus {ds : Bytes} (hds : Digits ds) :
    expPart (0x2D +: ds) = some (true, ds) := by
  rw [expPart_cons_minus, expDigits_of_digits hds]

theorem expPart_signBytes (s : Bool) {ds : Bytes} (hds : Digits ds) :
    expPart (Decimal.signBytes s ++ ds) = some (s, ds) := by
  cases s
  · rw [Decimal.signBytes_false, ByteString.empty_append]
    exact expPart_digits hds
  · rw [Decimal.signBytes_true]
    simp only [ByteString.cons_append, ByteString.empty_append]
    exact expPart_minus hds

theorem suffix_frac {neg : Bool} {ip fs : Bytes} (hfs : Digits fs) :
    suffix neg ip (0x2E +: fs) = some ⟨neg, ip, some fs, none⟩ := by
  rw [suffix_cons_dot, digits_takeWhile hfs, ite_eq_right (digits_ne_empty hfs),
    digits_dropWhile hfs]
  rfl

theorem suffix_exp {neg : Bool} {ip : Bytes} {s : Bool} {ds : Bytes} (hds : Digits ds) :
    suffix neg ip (0x65 +: (Decimal.signBytes s ++ ds)) =
      some ⟨neg, ip, none, some (s, ds)⟩ := by
  rw [suffix_cons_e, expPart_signBytes s hds]
  rfl

theorem suffix_fracExp {neg : Bool} {ip fs : Bytes} (hfs : Digits fs) {s : Bool}
    {ds : Bytes} (hds : Digits ds) :
    suffix neg ip (0x2E +: (fs ++ (0x65 +: (Decimal.signBytes s ++ ds)))) =
      some ⟨neg, ip, some fs, some (s, ds)⟩ := by
  rw [suffix_cons_dot, takeWhile_append_digits (digits0_of_digits hfs)]
  rw [takeWhile_ndigit isDigitB_e (Decimal.signBytes s ++ ds), ByteString.append_empty,
    ite_eq_right (digits_ne_empty hfs), dropWhile_append_digits (digits0_of_digits hfs),
    dropWhile_ndigit isDigitB_e (Decimal.signBytes s ++ ds)]
  rw [expTail_cons_e, expPart_signBytes s hds]
  rfl

/-! ### The sign byte, and the body parse -/

/-- The optional `minus` is consumed, and the body parse follows.  The body
begins with `int`'s first byte, which is `0` or a lead digit, so it is never the
`minus` the sign check consumes. -/
theorem reader_sign (neg : Bool) {b : UInt8} {B' : Bytes} (hb : b ≠ 0x2D) :
    reader (Decimal.signBytes neg ++ (b +: B')) = body neg (b +: B') := by
  cases neg
  · rw [Decimal.signBytes_false, ByteString.empty_append]
    exact reader_cons_other hb B'
  · rw [Decimal.signBytes_true, ByteString.cons_append, ByteString.empty_append]
    exact reader_cons_minus (b +: B')

/-- The body of a lexeme read at its `int` part alone. -/
theorem body_lead_end (neg : Bool) {b : UInt8} (bs : Bytes)
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs) :
    body neg (b +: bs) = suffix neg (b +: bs) empty := by
  rw [body_cons_lead neg bs h1 h2, takeWhile_digits hr, dropWhile_digits hr]

theorem body_lead_of_noDigit {neg : Bool} {b : UInt8} {bs suf : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs)
    (hsuf : suf.takeWhile IsDigitB = empty) :
    body neg (b +: (bs ++ suf)) = suffix neg (b +: bs) suf :=
  body_lead neg bs suf h1 h2 hr hsuf

/-! ### The four shapes, at each `int` part

`Decimal.body`'s four shapes with `int`'s two: the reader's reading of each is
the decomposition.  These are the case lemmas `reader_lexeme` dispatches to. -/

theorem reader_zero_plain (neg : Bool) :
    reader (Decimal.lexeme ⟨neg, 0x30 +: empty, none, none⟩) =
      some ⟨neg, 0x30 +: empty, none, none⟩ := by
  simp only [Decimal.lexeme, Decimal.body]
  change reader (Decimal.signBytes neg ++ (0x30 +: empty)) = _
  rw [reader_sign neg (by decide), body_zero, suffix_end]

theorem reader_zero_frac (neg : Bool) {fs : Bytes} (hfs : Digits fs) :
    reader (Decimal.lexeme ⟨neg, 0x30 +: empty, some fs, none⟩) =
      some ⟨neg, 0x30 +: empty, some fs, none⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append, ByteString.empty_append]
  change reader (Decimal.signBytes neg ++ (0x30 +: (0x2E +: fs))) = _
  rw [reader_sign neg (by decide), body_zero, suffix_frac hfs]

theorem reader_zero_exp (neg : Bool) {s : Bool} {ds : Bytes} (hds : Digits ds) :
    reader (Decimal.lexeme ⟨neg, 0x30 +: empty, none, some (s, ds)⟩) =
      some ⟨neg, 0x30 +: empty, none, some (s, ds)⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append, ByteString.empty_append]
  change reader (Decimal.signBytes neg ++ (0x30 +: (0x65 +: (Decimal.signBytes s ++ ds)))) = _
  rw [reader_sign neg (by decide), body_zero, suffix_exp hds]

theorem reader_zero_fracExp (neg : Bool) {fs : Bytes} (hfs : Digits fs) {s : Bool}
    {ds : Bytes} (hds : Digits ds) :
    reader (Decimal.lexeme ⟨neg, 0x30 +: empty, some fs, some (s, ds)⟩) =
      some ⟨neg, 0x30 +: empty, some fs, some (s, ds)⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append, ByteString.empty_append]
  change reader (Decimal.signBytes neg ++
    (0x30 +: (0x2E +: (fs ++ (0x65 +: (Decimal.signBytes s ++ ds)))))) = _
  rw [reader_sign neg (by decide), body_zero, suffix_fracExp hfs hds]

theorem reader_lead_plain (neg : Bool) {b : UInt8} {bs : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs) (hb : b ≠ 0x2D) :
    reader (Decimal.lexeme ⟨neg, b +: bs, none, none⟩) =
      some ⟨neg, b +: bs, none, none⟩ := by
  simp only [Decimal.lexeme, Decimal.body]
  change reader (Decimal.signBytes neg ++ (b +: bs)) = _
  rw [reader_sign neg hb, body_lead_end neg bs h1 h2 hr, suffix_end]

theorem reader_lead_frac (neg : Bool) {b : UInt8} {bs fs : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs) (hb : b ≠ 0x2D)
    (hfs : Digits fs) :
    reader (Decimal.lexeme ⟨neg, b +: bs, some fs, none⟩) =
      some ⟨neg, b +: bs, some fs, none⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append]
  change reader (Decimal.signBytes neg ++ (b +: (bs ++ (0x2E +: fs)))) = _
  rw [reader_sign neg hb,
    body_lead_of_noDigit h1 h2 hr (takeWhile_ndigit isDigitB_dot fs), suffix_frac hfs]

theorem reader_lead_exp (neg : Bool) {b : UInt8} {bs : Bytes} {s : Bool} {ds : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs) (hb : b ≠ 0x2D)
    (hds : Digits ds) :
    reader (Decimal.lexeme ⟨neg, b +: bs, none, some (s, ds)⟩) =
      some ⟨neg, b +: bs, none, some (s, ds)⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append]
  change reader (Decimal.signBytes neg ++
    (b +: (bs ++ (0x65 +: (Decimal.signBytes s ++ ds))))) = _
  rw [reader_sign neg hb,
    body_lead_of_noDigit h1 h2 hr (takeWhile_ndigit isDigitB_e _), suffix_exp hds]

theorem reader_lead_fracExp (neg : Bool) {b : UInt8} {bs fs : Bytes} {s : Bool}
    {ds : Bytes} (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs) (hb : b ≠ 0x2D)
    (hfs : Digits fs) (hds : Digits ds) :
    reader (Decimal.lexeme ⟨neg, b +: bs, some fs, some (s, ds)⟩) =
      some ⟨neg, b +: bs, some fs, some (s, ds)⟩ := by
  simp only [Decimal.lexeme, Decimal.body, ByteString.cons_append, ByteString.append_assoc]
  change reader (Decimal.signBytes neg ++
    (b +: (bs ++ (0x2E +: (fs ++ (0x65 +: (Decimal.signBytes s ++ ds))))))) = _
  rw [reader_sign neg hb,
    body_lead_of_noDigit h1 h2 hr (takeWhile_ndigit isDigitB_dot _),
    suffix_fracExp hfs hds]

/-- **The reader recovers the decomposition of every well-formed lexeme.**  This
is the hypothesis `StrtodTier1.emittedRefinesOn_tier1` and
`StrtodTier3.emittedRefinesOn_tier3` take as `hread`: reading a well-formed
lexeme's bytes yields its own sign, `int` bytes, fraction digits, and exponent
sign and digits, field for field. -/
theorem reader_lexeme {d : Decimal} (h : d.wellFormed) : reader d.lexeme = some d := by
  obtain ⟨neg, ip, fr, ex⟩ := d
  simp only [Decimal.wellFormed] at h
  obtain ⟨hip, hfr, hex⟩ := h
  cases hip with
  | zero =>
    cases hf : fr with
    | none =>
      cases he : ex with
      | none => exact reader_zero_plain neg
      | some p =>
        obtain ⟨s, ds⟩ := p
        exact reader_zero_exp neg (hex s ds he)
    | some fs =>
      cases he : ex with
      | none => exact reader_zero_frac neg (hfr fs hf)
      | some p =>
        obtain ⟨s, ds⟩ := p
        exact reader_zero_fracExp neg (hfr fs hf) (hex s ds he)
  | lead h1 h2 hr =>
    rename_i b bs
    have hb : b ≠ 0x2D := by
      intro hh; subst hh; exact absurd h1 (by decide)
    cases hf : fr with
    | none =>
      cases he : ex with
      | none => exact reader_lead_plain neg h1 h2 hr hb
      | some p =>
        obtain ⟨s, ds⟩ := p
        exact reader_lead_exp neg h1 h2 hr hb (hex s ds he)
    | some fs =>
      cases he : ex with
      | none => exact reader_lead_frac neg h1 h2 hr hb (hfr fs hf)
      | some p =>
        obtain ⟨s, ds⟩ := p
        exact reader_lead_fracExp neg h1 h2 hr hb (hfr fs hf) (hex s ds he)


/-! ### The reader is the grammar's decision

Two directions, and they meet the tree's own model of the emitted scanner:
`LeanLLVM.JSON.numLexB` (`JSON/Scan.lean`) is the accepting scan of
`[ minus ] int [ frac ] [ exp ]` and is proved sound and complete for
`RfcNumber` (`numLexB_spec`, `numLexB_complete`).  Below, `reader` is proved
sound and complete for the same predicate, and `reader_isSome_eq_numLexB` is the
two together: the model's accept/refuse decision is the tree's. -/

theorem reader_empty : reader (empty : Bytes) = none := rfl
theorem expPart_empty : expPart (empty : Bytes) = none := rfl
theorem expTail_empty : expTail (empty : Bytes) = some none := rfl
theorem body_empty (neg : Bool) : body neg (empty : Bytes) = none := rfl

theorem expTail_cons_other {b : UInt8} (rest : Bytes) (hb : b ≠ 0x65) (hc : b ≠ 0x45) :
    expTail (b +: rest) = none := by
  simp [expTail, ByteString.data_toList_cons, hb, hc]

theorem suffix_cons_other {neg : Bool} {ip : Bytes} {b : UInt8} (rest : Bytes)
    (hdot : b ≠ 0x2E) (he : b ≠ 0x65) (hE : b ≠ 0x45) :
    suffix neg ip (b +: rest) = none := by
  simp [suffix, ByteString.data_toList_cons, hdot, he, hE]

theorem body_cons_other {neg : Bool} {b : UInt8} (rest : Bytes) (h0 : b ≠ 0x30)
    (hl : ¬ (0x31 ≤ b ∧ b ≤ 0x39)) :
    body neg (b +: rest) = none := by
  simp [body, ByteString.data_toList_cons, h0, hl]

/-! #### Acceptance is grammatical -/

/-- An accepted exponent's digits are a `1*DIGIT` run, and its sign is the
scanned one. -/
theorem expDigits_spec {sign : Bool} {bs : Bytes} {r : Bool × Bytes}
    (h : expDigits sign bs = some r) : r.1 = sign ∧ r.2 = bs ∧ Digits bs := by
  obtain ⟨pos, ds⟩ := r
  change pos = sign ∧ ds = bs ∧ Digits bs
  simp only [expDigits] at h
  by_cases hne : bs.takeWhile IsDigitB = empty
  · rw [ite_eq_left hne] at h
    exact absurd h (by simp)
  · rw [ite_eq_right hne] at h
    by_cases hd : bs.dropWhile IsDigitB = empty
    · rw [ite_eq_left hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hp, hds⟩ := h
      have hbs : bs = bs.takeWhile IsDigitB := eq_takeWhile_of_dropWhile_eq_nil hd
      refine ⟨hp.symm, ?_, ?_⟩
      · exact hds.symm.trans hbs.symm
      · rw [hbs]
        exact digits0_to_digits (digits0_takeWhile bs) hne
    · rw [ite_eq_right hd] at h
      exact absurd h (by simp)

theorem expPart_Digits {bs : Bytes} {r : Bool × Bytes} (h : expPart bs = some r) :
    Digits r.2 := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [expPart_empty] at h; exact absurd h (by simp)
  · by_cases hp : b = 0x2B
    · subst hp; rw [expPart_cons_plus] at h
      obtain ⟨_, hds, hD⟩ := expDigits_spec h
      rw [hds]; exact hD
    · by_cases hm : b = 0x2D
      · subst hm; rw [expPart_cons_minus] at h
        obtain ⟨_, hds, hD⟩ := expDigits_spec h
        rw [hds]; exact hD
      · rw [expPart_cons_digit rest hp hm] at h
        obtain ⟨_, hds, hD⟩ := expDigits_spec h
        rw [hds]; exact hD

theorem expPart_spec {bs : Bytes} {ex : Bool × Bytes} (h : expPart bs = some ex) :
    ∀ s ds, ex = (s, ds) → Digits ds := by
  have hD := expPart_Digits h
  intro s ds hex
  rw [hex] at hD
  exact hD

theorem expTail_spec {bs : Bytes} {ex : Option (Bool × Bytes)}
    (h : expTail bs = some ex) : ∀ s ds, ex = some (s, ds) → Digits ds := by
  intro s ds hex
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [expTail_empty] at h
    simp only [Option.some.injEq] at h
    subst h
    cases hex
  · by_cases he : b = 0x65 ∨ b = 0x45
    · rcases he with rfl | rfl
      · rw [expTail_cons_e] at h
        cases hpart : expPart rest with
        | none => rw [hpart] at h; simp at h
        | some r =>
          obtain ⟨a, d⟩ := r
          rw [hpart, Option.map_some] at h
          simp only [Option.some.injEq] at h
          rw [← h] at hex
          simp only [Option.some.injEq, Prod.mk.injEq] at hex
          obtain ⟨_, hds⟩ := hex
          rw [← hds]
          exact expPart_Digits hpart
      · rw [expTail_cons_E] at h
        cases hpart : expPart rest with
        | none => rw [hpart] at h; simp at h
        | some r =>
          obtain ⟨a, d⟩ := r
          rw [hpart, Option.map_some] at h
          simp only [Option.some.injEq] at h
          rw [← h] at hex
          simp only [Option.some.injEq, Prod.mk.injEq] at hex
          obtain ⟨_, hds⟩ := hex
          rw [← hds]
          exact expPart_Digits hpart
    · rw [expTail_cons_other rest (fun hh => he (Or.inl hh)) (fun hh => he (Or.inr hh))] at h
      exact absurd h (by simp)

theorem suffix_wf {neg : Bool} {ip : Bytes} {bs : Bytes} {d : Decimal}
    (hip : IntPart ip) (h : suffix neg ip bs = some d) : d.wellFormed := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [suffix_end] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [Decimal.wellFormed]
    refine ⟨hip, ?_, ?_⟩
    · intro fs hf; cases hf
    · intro s ds he; cases he
  · by_cases hdot : b = 0x2E
    · subst hdot
      rw [suffix_cons_dot] at h
      by_cases hne : rest.takeWhile IsDigitB = empty
      · rw [ite_eq_left hne] at h
        exact absurd h (by simp)
      · rw [ite_eq_right hne] at h
        have hfs : Digits (rest.takeWhile IsDigitB) :=
          digits0_to_digits (digits0_takeWhile rest) hne
        cases hex : expTail (rest.dropWhile IsDigitB) with
        | none => rw [hex] at h; simp at h
        | some ex =>
          rw [hex, Option.map_some] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [Decimal.wellFormed]
          refine ⟨hip, ?_, expTail_spec hex⟩
          intro fs hf
          simp only [Option.some.injEq] at hf
          subst hf
          exact hfs
    · by_cases he : b = 0x65 ∨ b = 0x45
      · rcases he with rfl | rfl
        · rw [suffix_cons_e] at h
          cases hpart : expPart rest with
          | none => rw [hpart] at h; simp at h
          | some ex =>
            rw [hpart, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [Decimal.wellFormed]
            refine ⟨hip, ?_, ?_⟩
            · intro fs hf; cases hf
            · intro s ds hsome
              simp only [Option.some.injEq] at hsome
              exact expPart_spec hpart s ds hsome
        · rw [suffix_cons_E] at h
          cases hpart : expPart rest with
          | none => rw [hpart] at h; simp at h
          | some ex =>
            rw [hpart, Option.map_some] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [Decimal.wellFormed]
            refine ⟨hip, ?_, ?_⟩
            · intro fs hf; cases hf
            · intro s ds hsome
              simp only [Option.some.injEq] at hsome
              exact expPart_spec hpart s ds hsome
      · rw [suffix_cons_other rest hdot (fun hh => he (Or.inl hh))
          (fun hh => he (Or.inr hh))] at h
        exact absurd h (by simp)

theorem body_wf {neg : Bool} {bs : Bytes} {d : Decimal} (h : body neg bs = some d) :
    d.wellFormed := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [body_empty] at h; exact absurd h (by simp)
  · by_cases h0 : b = 0x30
    · subst h0; rw [body_cons_zero] at h; exact suffix_wf IntPart.zero h
    · by_cases hl : 0x31 ≤ b ∧ b ≤ 0x39
      · obtain ⟨h1, h2⟩ := hl
        rw [body_cons_lead neg rest h1 h2] at h
        exact suffix_wf (IntPart.lead h1 h2 (digits0_takeWhile rest)) h
      · rw [body_cons_other rest h0 hl] at h; exact absurd h (by simp)

/-- **What the reader accepts is a well-formed decomposition**: `int`'s bytes
are an `IntPart`, the fraction's a `1*DIGIT` run or absent, and the exponent's a
`1*DIGIT` run or absent. -/
theorem reader_wf {bs : Bytes} {d : Decimal} (h : reader bs = some d) : d.wellFormed := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [reader_empty] at h; exact absurd h (by simp)
  · by_cases hm : b = 0x2D
    · subst hm; rw [reader_cons_minus] at h; exact body_wf h
    · rw [reader_cons_other hm] at h; exact body_wf h

/-! #### What the reader accepts is a number lexeme -/

/-- An accepted exponent's bytes are `e`/`E`, an optional sign byte and
`1*DIGIT`: RFC 8259's `exp` production, over the byte string the reader read. -/
theorem expPart_sound {m : UInt8} (hm : m = 0x65 ∨ m = 0x45) {bs : Bytes}
    {r : Bool × Bytes} (h : expPart bs = some r) : ExpPart (m +: bs) := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [expPart_empty] at h; exact absurd h (by simp)
  · by_cases hp : b = 0x2B
    · subst hp
      rw [expPart_cons_plus] at h
      have hd := (expDigits_spec h).2.2
      have hgoal : (0x2B +: empty) ++ rest = 0x2B +: rest := by
        rw [ByteString.cons_append, ByteString.empty_append]
      rw [← hgoal]
      exact ExpPart.mk (e := m) (sign := 0x2B +: empty) (ds := rest) hm
        (Or.inr (Or.inl rfl)) hd
    · by_cases hm' : b = 0x2D
      · subst hm'
        rw [expPart_cons_minus] at h
        have hd := (expDigits_spec h).2.2
        have hgoal : (0x2D +: empty) ++ rest = 0x2D +: rest := by
          rw [ByteString.cons_append, ByteString.empty_append]
        rw [← hgoal]
        exact ExpPart.mk (e := m) (sign := 0x2D +: empty) (ds := rest) hm
          (Or.inr (Or.inr rfl)) hd
      · rw [expPart_cons_digit rest hp hm'] at h
        have hd := (expDigits_spec h).2.2
        exact ExpPart.mk (e := m) (sign := empty) (ds := b +: rest) hm (Or.inl rfl) hd

theorem expTail_sound {bs : Bytes} {ex : Option (Bool × Bytes)}
    (h : expTail bs = some ex) : bs = empty ∨ ExpPart bs := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · exact Or.inl rfl
  · by_cases he : b = 0x65 ∨ b = 0x45
    · rcases he with rfl | rfl
      · rw [expTail_cons_e] at h
        cases hpart : expPart rest with
        | none => rw [hpart] at h; simp at h
        | some r => exact Or.inr (expPart_sound (Or.inl rfl) hpart)
      · rw [expTail_cons_E] at h
        cases hpart : expPart rest with
        | none => rw [hpart] at h; simp at h
        | some r => exact Or.inr (expPart_sound (Or.inr rfl) hpart)
    · rw [expTail_cons_other rest (fun hh => he (Or.inl hh)) (fun hh => he (Or.inr hh))] at h
      exact absurd h (by simp)

theorem suffix_sound {neg : Bool} {ip : Bytes} {bs : Bytes} {d : Decimal}
    (hip : IntPart ip) (h : suffix neg ip bs = some d) : NumBody (ip ++ bs) := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [suffix_end] at h
    simp only [Option.some.injEq] at h
    subst h
    rw [ByteString.append_empty]
    exact NumBody.plain hip
  · by_cases hdot : b = 0x2E
    · subst hdot
      rw [suffix_cons_dot] at h
      by_cases hne : rest.takeWhile IsDigitB = empty
      · rw [ite_eq_left hne] at h
        exact absurd h (by simp)
      · rw [ite_eq_right hne] at h
        have hfs : Digits (rest.takeWhile IsDigitB) :=
          digits0_to_digits (digits0_takeWhile rest) hne
        cases hex : expTail (rest.dropWhile IsDigitB) with
        | none => rw [hex] at h; simp at h
        | some ex =>
          rw [hex, Option.map_some] at h
          simp only [Option.some.injEq] at h
          subst h
          have hsplit : rest.takeWhile IsDigitB ++ rest.dropWhile IsDigitB = rest :=
            ByteString.takeWhile_append_dropWhile rest IsDigitB
          rw [← hsplit]
          rw [← ByteString.cons_append, ← ByteString.append_assoc]
          rcases expTail_sound hex with hemp | he
          · rw [hemp, ByteString.append_empty]
            exact NumBody.frac hip hfs
          · exact NumBody.fracExp hip hfs he
    · by_cases he : b = 0x65 ∨ b = 0x45
      · rcases he with rfl | rfl
        · rw [suffix_cons_e] at h
          cases hpart : expPart rest with
          | none => rw [hpart] at h; simp at h
          | some r => exact NumBody.exp hip (expPart_sound (Or.inl rfl) hpart)
        · rw [suffix_cons_E] at h
          cases hpart : expPart rest with
          | none => rw [hpart] at h; simp at h
          | some r => exact NumBody.exp hip (expPart_sound (Or.inr rfl) hpart)
      · rw [suffix_cons_other rest hdot (fun hh => he (Or.inl hh))
          (fun hh => he (Or.inr hh))] at h
        exact absurd h (by simp)

theorem body_sound {neg : Bool} {bs : Bytes} {d : Decimal} (h : body neg bs = some d) :
    NumBody bs := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [body_empty] at h; exact absurd h (by simp)
  · by_cases h0 : b = 0x30
    · subst h0
      rw [body_cons_zero] at h
      have := suffix_sound IntPart.zero h
      rw [ByteString.cons_append, ByteString.empty_append] at this
      exact this
    · by_cases hl : 0x31 ≤ b ∧ b ≤ 0x39
      · obtain ⟨h1, h2⟩ := hl
        rw [body_cons_lead neg rest h1 h2] at h
        have := suffix_sound (IntPart.lead h1 h2 (digits0_takeWhile rest)) h
        rw [ByteString.cons_append, ByteString.takeWhile_append_dropWhile] at this
        exact this
      · rw [body_cons_other rest h0 hl] at h; exact absurd h (by simp)

/-- **The reader accepts only number lexemes.** -/
theorem reader_sound {bs : Bytes} {d : Decimal} (h : reader bs = some d) : RfcNumber bs := by
  rcases ByteString.eq_empty_or_cons bs with rfl | ⟨b, rest, rfl⟩
  · rw [reader_empty] at h; exact absurd h (by simp)
  · by_cases hm : b = 0x2D
    · subst hm; rw [reader_cons_minus] at h; exact RfcNumber.neg (body_sound h)
    · rw [reader_cons_other hm] at h; exact RfcNumber.pos (body_sound h)

/-! #### Every number lexeme is accepted -/

theorem expPart_acc_self {ds : Bytes} (hds : Digits ds) : (expPart ds).isSome = true := by
  rw [expPart_digits hds]; rfl

theorem expPart_acc_plus {ds : Bytes} (hds : Digits ds) :
    (expPart (0x2B +: ds)).isSome = true := by
  rw [expPart_cons_plus, expDigits_of_digits hds]; rfl

theorem expPart_acc_minus {ds : Bytes} (hds : Digits ds) :
    (expPart (0x2D +: ds)).isSome = true := by
  rw [expPart_cons_minus, expDigits_of_digits hds]; rfl

theorem suffix_acc_empty {neg : Bool} {ip : Bytes} : (suffix neg ip empty).isSome = true := by
  rw [suffix_end]; rfl

theorem suffix_acc_frac {neg : Bool} {ip : Bytes} {fs : Bytes} (hfs : Digits fs) :
    (suffix neg ip (0x2E +: fs)).isSome = true := by
  rw [suffix_frac hfs]; rfl

theorem suffix_acc_exp {neg : Bool} {ip : Bytes} {m : UInt8} (hm : m = 0x65 ∨ m = 0x45)
    {bs : Bytes} (hex : (expPart bs).isSome = true) :
    (suffix neg ip (m +: bs)).isSome = true := by
  rcases hm with rfl | rfl
  · simp only [suffix_cons_e, Option.isSome_map]
    exact hex
  · simp only [suffix_cons_E, Option.isSome_map]
    exact hex

theorem suffix_acc_frac_exp {neg : Bool} {ip fs : Bytes} {m : UInt8}
    (hm : m = 0x65 ∨ m = 0x45) (hfs : Digits fs) {bs : Bytes}
    (hex : (expPart bs).isSome = true) :
    (suffix neg ip (0x2E +: (fs ++ (m +: bs)))).isSome = true := by
  have hnd : (m +: bs).takeWhile IsDigitB = empty := by
    rcases hm with rfl | rfl
    · exact takeWhile_ndigit isDigitB_e bs
    · exact takeWhile_ndigit isDigitB_E bs
  rw [suffix_cons_dot, takeWhile_append_digits (digits0_of_digits hfs), hnd,
    ByteString.append_empty, ite_eq_right (digits_ne_empty hfs),
    dropWhile_append_digits (digits0_of_digits hfs),
    dropWhile_of_takeWhile_eq_empty hnd]
  rcases hm with rfl | rfl
  · simp only [expTail_cons_e, Option.isSome_map]
    exact hex
  · simp only [expTail_cons_E, Option.isSome_map]
    exact hex

theorem body_acc_zero {neg : Bool} {suf : Bytes}
    (hs : (suffix neg (0x30 +: empty) suf).isSome = true) :
    (body neg (0x30 +: suf)).isSome = true := by
  rwa [body_cons_zero]

theorem body_acc_lead_end {neg : Bool} {b : UInt8} {bs : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs)
    (hs : (suffix neg (b +: bs) empty).isSome = true) :
    (body neg (b +: bs)).isSome = true := by
  rwa [body_lead_end neg bs h1 h2 hr]

theorem body_acc_lead {neg : Bool} {b : UInt8} {bs suf : Bytes}
    (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39) (hr : Digits0 bs)
    (hnd : suf.takeWhile IsDigitB = empty)
    (hs : (suffix neg (b +: bs) suf).isSome = true) :
    (body neg (b +: (bs ++ suf))).isSome = true := by
  rwa [body_lead neg bs suf h1 h2 hr hnd]

/-- The first byte of a `NumBody` lexeme: `int`'s lead, never the `minus` the
sign check consumes. -/
theorem intPart_head {ip : Bytes} (h : IntPart ip) :
    ∃ c B, ip = c +: B ∧ c ≠ 0x2D := by
  cases h with
  | zero => exact ⟨0x30, empty, rfl, by decide⟩
  | lead h1 h2 hr =>
    refine ⟨_, _, rfl, ?_⟩
    intro hh; subst hh; exact absurd h1 (by decide)

theorem numBody_head {bs : Bytes} (h : NumBody bs) :
    ∃ c B, bs = c +: B ∧ c ≠ 0x2D := by
  cases h with
  | plain hip => exact intPart_head hip
  | frac hip hf =>
    rename_i ip0 fs0
    obtain ⟨c, B, hc, hne⟩ := intPart_head hip
    exact ⟨c, B ++ (0x2E +: fs0), by rw [hc, ByteString.cons_append], hne⟩
  | exp hip he =>
    rename_i ip0 es0
    obtain ⟨c, B, hc, hne⟩ := intPart_head hip
    exact ⟨c, B ++ es0, by rw [hc, ByteString.cons_append], hne⟩
  | fracExp hip hf he =>
    rename_i ip0 fs0 es0
    obtain ⟨c, B, hc, hne⟩ := intPart_head hip
    exact ⟨c, (B ++ (0x2E +: fs0)) ++ es0,
      by rw [hc, ByteString.cons_append, ByteString.cons_append], hne⟩

theorem body_acc : ∀ {bs : Bytes}, NumBody bs → ∀ neg : Bool, (body neg bs).isSome = true
  | _, .plain hip, neg => by
    cases hip with
    | zero => exact body_acc_zero suffix_acc_empty
    | lead h1 h2 hr => exact body_acc_lead_end h1 h2 hr suffix_acc_empty
  | _, .frac hip hf, neg => by
    cases hip with
    | zero =>
      simp only [ByteString.cons_append, ByteString.empty_append]
      exact body_acc_zero (suffix_acc_frac hf)
    | lead h1 h2 hr =>
      rw [ByteString.cons_append]
      exact body_acc_lead h1 h2 hr (takeWhile_ndigit isDigitB_dot _) (suffix_acc_frac hf)
  | _, .exp hip he, neg => by
    cases he with
    | mk hm hs hd =>
      rename_i e sign ds
      have hex : (expPart (sign ++ ds)).isSome = true := by
        rcases hs with h0 | h0 | h0
        · rw [h0, ByteString.empty_append]; exact expPart_acc_self hd
        · rw [h0, ByteString.cons_append, ByteString.empty_append]; exact expPart_acc_plus hd
        · rw [h0, ByteString.cons_append, ByteString.empty_append]; exact expPart_acc_minus hd
      have hnd : (e +: (sign ++ ds)).takeWhile IsDigitB = empty := by
        rcases hm with rfl | rfl
        · exact takeWhile_ndigit isDigitB_e _
        · exact takeWhile_ndigit isDigitB_E _
      cases hip with
      | zero =>
        simp only [ByteString.cons_append, ByteString.empty_append]
        exact body_acc_zero (suffix_acc_exp hm hex)
      | lead h1 h2 hr =>
        rw [ByteString.cons_append]
        exact body_acc_lead h1 h2 hr hnd (suffix_acc_exp hm hex)
  | _, .fracExp hip hf he, neg => by
    cases he with
    | mk hm hs hd =>
      rename_i e sign ds
      have hex : (expPart (sign ++ ds)).isSome = true := by
        rcases hs with h0 | h0 | h0
        · rw [h0, ByteString.empty_append]; exact expPart_acc_self hd
        · rw [h0, ByteString.cons_append, ByteString.empty_append]; exact expPart_acc_plus hd
        · rw [h0, ByteString.cons_append, ByteString.empty_append]; exact expPart_acc_minus hd
      cases hip with
      | zero =>
        simp only [ByteString.cons_append, ByteString.empty_append]
        exact body_acc_zero (suffix_acc_frac_exp hm hf hex)
      | lead h1 h2 hr =>
        simp only [ByteString.cons_append, ByteString.append_assoc]
        exact body_acc_lead h1 h2 hr (takeWhile_ndigit isDigitB_dot _)
          (suffix_acc_frac_exp hm hf hex)

/-- **Every number lexeme is accepted.** -/
theorem reader_complete {bs : Bytes} (h : RfcNumber bs) : (reader bs).isSome = true := by
  rcases h with hb | hb
  · obtain ⟨c, B, hc, hne⟩ := numBody_head hb
    rw [hc] at hb ⊢
    rw [reader_cons_other hne]
    exact body_acc hb false
  · obtain ⟨c, B, hc, hne⟩ := numBody_head hb
    rw [hc] at hb ⊢
    have hsign : (0x2D +: (c +: B)) = Decimal.signBytes true ++ (c +: B) := by
      rw [Decimal.signBytes_true, ByteString.cons_append, ByteString.empty_append]
    rw [hsign, reader_sign true hne]
    exact body_acc hb true

/-- **The model's accept/refuse decision is the tree's.**  `LeanLLVM.JSON.numLexB`
is `JSON/Scan.lean`'s accepting scan of the same production, so the reader and
the scanner model agree on every byte string, and `numLexB_spec` /
`numLexB_complete` carry the decision to `RfcNumber`. -/
theorem reader_isSome_eq_numLexB (bs : Bytes) : (reader bs).isSome = numLexB bs := by
  by_cases hr : (reader bs).isSome = true
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hr
    rw [numLexB_complete (reader_sound hd), hr]
  · have hr' : (reader bs).isSome = false := by
      cases hh : (reader bs).isSome <;> simp_all
    have hnr : numLexB bs = false := by
      cases hb : numLexB bs
      · rfl
      · exact absurd (hr (reader_complete (numLexB_spec hb))) (by simp)
    rw [hr', hnr]

/-! ### The hypothesis, discharged at the model

`emittedRefinesOn_tier1` and `emittedRefinesOn_tier3` take `hread`, and
`reader_lexeme` is exactly it.  Instantiating them at `reader` removes the
reader parameter from both statements; what is left is each module's own
statement about the conversion, which this module does not restate. -/

/-- The tier-1 clause at the model reader. -/
theorem tier1_no_reader :
    LeanLLVM.StrtodRefine.EmittedRefinesOn
      (LeanLLVM.StrtodTier1.tier1Emitted reader) LeanLLVM.StrtodRefine.Tier1 :=
  LeanLLVM.StrtodTier1.emittedRefinesOn_tier1 reader (fun _ hd => reader_lexeme hd)

/-- The tier-3 clause at the model reader. -/
theorem tier3_no_reader (kernelDecides : Decimal → Bool) :
    LeanLLVM.StrtodRefine.EmittedRefinesOn
      (LeanLLVM.StrtodTier3.tier3Emitted reader)
      (fun d => LeanLLVM.StrtodRefine.Fallback d kernelDecides) :=
  LeanLLVM.StrtodTier3.emittedRefinesOn_tier3 reader kernelDecides
    (fun _ hd => reader_lexeme hd)

/-! ### The reading at the emitted constants

Each fact below is the emitted byte's own test: `0x2D` is the sign check, `0x30`
the `int` production's zero, `0x2E` the fraction's marker, `0x65`/`0x45` the
exponent's, and `0x31`–`0x39` the lead digit. -/

/-- `0` alone is the whole `int`: `00` is refused, because the emitted scan
consumes one `0` and then requires `.`, `e`, or the end. -/
theorem reader_refuses_double_zero : reader (bytes [0x30, 0x30]) = none := by decide

/-- The empty input is refused: the emitted scan's first `i >= n` exit. -/
theorem reader_refuses_empty : reader (empty : Bytes) = none := by decide

/-- A lone `-` is refused: the sign check consumes it and `i >= n`. -/
theorem reader_refuses_lone_minus : reader (bytes [0x2D]) = none := by decide

/-- `int` cannot begin with anything but `0` or `1`–`9`, so a leading `+` is
refused at the digit test. -/
theorem reader_refuses_plus : reader (bytes [0x2B, 0x31]) = none := by decide

/-- A bare `.` with no `int` is refused. -/
theorem reader_refuses_bare_dot : reader (bytes [0x2E, 0x35]) = none := by decide

/-- `1.` is refused: the fraction's `1*DIGIT` is empty. -/
theorem reader_refuses_empty_frac : reader (bytes [0x31, 0x2E]) = none := by decide

/-- `1e` is refused: the exponent's `1*DIGIT` is empty. -/
theorem reader_refuses_empty_exp : reader (bytes [0x31, 0x65]) = none := by decide

/-- `1e-` is refused: the sign byte is consumed and the digits are empty. -/
theorem reader_refuses_signed_empty_exp :
    reader (bytes [0x31, 0x65, 0x2D]) = none := by decide

/-- A byte after the lexeme is refused: the emitted scan's `i != n` exit. -/
theorem reader_refuses_trailing : reader (bytes [0x31, 0x20]) = none := by decide

/-- `-0` keeps the sign byte, and its magnitude is zero. -/
theorem reader_neg_zero :
    reader (bytes [0x2D, 0x30]) = some ⟨true, bytes [0x30], none, none⟩ := by decide

/-- `-0` is a zero mantissa with the sign set: the emitted scan's `neg` flag is
kept even when no digit is nonzero. -/
theorem reader_neg_zero_mantissa :
    Decimal.mantissa ⟨true, bytes [0x30], none, none⟩ = 0 := by decide

/-- The exponent's sign and digits are read as written: `1e-005` keeps the `-`
and the three digits `005`. -/
theorem reader_exp_sign_magnitude :
    reader (bytes [0x31, 0x65, 0x2D, 0x30, 0x30, 0x35]) =
      some ⟨false, bytes [0x31], none, some (true, bytes [0x30, 0x30, 0x35])⟩ := by
  decide

/-- The exponent's leading zeros are digits, not a stop: `005` accumulates to
5 through the emitted `exp10 * 10 + d` step. -/
theorem reader_exp_leading_zeros :
    Decimal.digitsNat (bytes [0x30, 0x30, 0x35]) = 5 := by decide

/-- An explicit `+` in the exponent is accepted; `Decimal` has no field for it,
so the sign reads `false`, as the emitted `esign = (p[i] == '-')` does. -/
theorem reader_exp_plus :
    reader (bytes [0x31, 0x65, 0x2B, 0x35]) =
      some ⟨false, bytes [0x31], none, some (false, bytes [0x35])⟩ := by decide

/-- `E` is the exponent marker too, and reads to the same decomposition as `e`:
the case is not part of the decomposition. -/
theorem reader_exp_upper :
    reader (bytes [0x31, 0x45, 0x35]) =
      some ⟨false, bytes [0x31], none, some (false, bytes [0x35])⟩ := by decide

/-- The two spellings read the same, which is why the hypothesis is stated on
`Decimal.lexeme` and not on every accepted byte string: `Decimal` cannot record
the marker's case or an explicit `+`. -/
theorem reader_exp_spellings_agree :
    reader (bytes [0x31, 0x65, 0x2B, 0x35]) = reader (bytes [0x31, 0x45, 0x35]) := by
  decide

/-- The digits accumulate across the `.` exactly as `Decimal.mantissa` sums
them: `12.34` reads as `1234`, which is the emitted `ip * 10 ^ fdig + fr` at
this size. -/
theorem reader_mantissa :
    Decimal.mantissa ⟨false, bytes [0x31, 0x32], some (bytes [0x33, 0x34]), none⟩ =
      1234 := by decide

/-- The reader's `int` bytes are the emitted `idig` digits, and its fraction's
the emitted `fdig`: `12.34` is two and two. -/
theorem reader_digit_counts :
    (bytes [0x31, 0x32] : Bytes).length = 2 ∧ (bytes [0x33, 0x34] : Bytes).length = 2 := by
  decide

/-! ### Checks -/

#guard reader (bytes [0x30]) = some ⟨false, bytes [0x30], none, none⟩
#guard reader (bytes [0x31, 0x32]) = some ⟨false, bytes [0x31, 0x32], none, none⟩
#guard reader (bytes [0x2D, 0x30]) = some ⟨true, bytes [0x30], none, none⟩
#guard reader (bytes [0x31, 0x2E, 0x35]) = some ⟨false, bytes [0x31], some (bytes [0x35]), none⟩
#guard reader (bytes [0x31, 0x65, 0x35]) =
  some ⟨false, bytes [0x31], none, some (false, bytes [0x35])⟩
#guard reader (bytes [0x31, 0x2E, 0x35, 0x65, 0x2D, 0x33]) =
  some ⟨false, bytes [0x31], some (bytes [0x35]), some (true, bytes [0x33])⟩

/-! ### Axioms

Every declaration above is pinned: `#print axioms` names what it depends on, so
a change that introduces an axiom is visible in the build log. -/

#print axioms LeanLLVM.StrtodReader.bytes
#print axioms LeanLLVM.StrtodReader.expDigits
#print axioms LeanLLVM.StrtodReader.expPart
#print axioms LeanLLVM.StrtodReader.expTail
#print axioms LeanLLVM.StrtodReader.suffix
#print axioms LeanLLVM.StrtodReader.body
#print axioms LeanLLVM.StrtodReader.reader
#print axioms LeanLLVM.StrtodReader.reader_cons_minus
#print axioms LeanLLVM.StrtodReader.reader_cons_other
#print axioms LeanLLVM.StrtodReader.body_cons_zero
#print axioms LeanLLVM.StrtodReader.body_cons_lead
#print axioms LeanLLVM.StrtodReader.suffix_cons_dot
#print axioms LeanLLVM.StrtodReader.suffix_cons_e
#print axioms LeanLLVM.StrtodReader.suffix_cons_E
#print axioms LeanLLVM.StrtodReader.expTail_cons_e
#print axioms LeanLLVM.StrtodReader.expTail_cons_E
#print axioms LeanLLVM.StrtodReader.expPart_cons_plus
#print axioms LeanLLVM.StrtodReader.expPart_cons_minus
#print axioms LeanLLVM.StrtodReader.expPart_cons_digit
#print axioms LeanLLVM.StrtodReader.isDigitB_zero
#print axioms LeanLLVM.StrtodReader.isDigitB_dot
#print axioms LeanLLVM.StrtodReader.isDigitB_e
#print axioms LeanLLVM.StrtodReader.isDigitB_E
#print axioms LeanLLVM.StrtodReader.isDigitB_plus
#print axioms LeanLLVM.StrtodReader.isDigitB_minus
#print axioms LeanLLVM.StrtodReader.isDigitB_of_lead
#print axioms LeanLLVM.StrtodReader.takeWhile_ndigit
#print axioms LeanLLVM.StrtodReader.dropWhile_ndigit
#print axioms LeanLLVM.StrtodReader.takeWhile_append_digits
#print axioms LeanLLVM.StrtodReader.dropWhile_append_digits
#print axioms LeanLLVM.StrtodReader.digits_takeWhile
#print axioms LeanLLVM.StrtodReader.digits_dropWhile
#print axioms LeanLLVM.StrtodReader.digits_ne_empty
#print axioms LeanLLVM.StrtodReader.digits_shape
#print axioms LeanLLVM.StrtodReader.dropWhile_of_takeWhile_eq_empty
#print axioms LeanLLVM.StrtodReader.body_zero
#print axioms LeanLLVM.StrtodReader.body_lead
#print axioms LeanLLVM.StrtodReader.suffix_end
#print axioms LeanLLVM.StrtodReader.expDigits_of_digits
#print axioms LeanLLVM.StrtodReader.expPart_digits
#print axioms LeanLLVM.StrtodReader.expPart_minus
#print axioms LeanLLVM.StrtodReader.expPart_signBytes
#print axioms LeanLLVM.StrtodReader.suffix_frac
#print axioms LeanLLVM.StrtodReader.suffix_exp
#print axioms LeanLLVM.StrtodReader.suffix_fracExp
#print axioms LeanLLVM.StrtodReader.reader_sign
#print axioms LeanLLVM.StrtodReader.body_lead_end
#print axioms LeanLLVM.StrtodReader.body_lead_of_noDigit
#print axioms LeanLLVM.StrtodReader.reader_zero_plain
#print axioms LeanLLVM.StrtodReader.reader_zero_frac
#print axioms LeanLLVM.StrtodReader.reader_zero_exp
#print axioms LeanLLVM.StrtodReader.reader_zero_fracExp
#print axioms LeanLLVM.StrtodReader.reader_lead_plain
#print axioms LeanLLVM.StrtodReader.reader_lead_frac
#print axioms LeanLLVM.StrtodReader.reader_lead_exp
#print axioms LeanLLVM.StrtodReader.reader_lead_fracExp
#print axioms LeanLLVM.StrtodReader.reader_lexeme
#print axioms LeanLLVM.StrtodReader.reader_empty
#print axioms LeanLLVM.StrtodReader.expPart_empty
#print axioms LeanLLVM.StrtodReader.expTail_empty
#print axioms LeanLLVM.StrtodReader.body_empty
#print axioms LeanLLVM.StrtodReader.expTail_cons_other
#print axioms LeanLLVM.StrtodReader.suffix_cons_other
#print axioms LeanLLVM.StrtodReader.body_cons_other
#print axioms LeanLLVM.StrtodReader.expDigits_spec
#print axioms LeanLLVM.StrtodReader.expPart_Digits
#print axioms LeanLLVM.StrtodReader.expPart_spec
#print axioms LeanLLVM.StrtodReader.expTail_spec
#print axioms LeanLLVM.StrtodReader.suffix_wf
#print axioms LeanLLVM.StrtodReader.body_wf
#print axioms LeanLLVM.StrtodReader.reader_wf
#print axioms LeanLLVM.StrtodReader.expPart_sound
#print axioms LeanLLVM.StrtodReader.expTail_sound
#print axioms LeanLLVM.StrtodReader.suffix_sound
#print axioms LeanLLVM.StrtodReader.body_sound
#print axioms LeanLLVM.StrtodReader.reader_sound
#print axioms LeanLLVM.StrtodReader.expPart_acc_self
#print axioms LeanLLVM.StrtodReader.expPart_acc_plus
#print axioms LeanLLVM.StrtodReader.expPart_acc_minus
#print axioms LeanLLVM.StrtodReader.suffix_acc_empty
#print axioms LeanLLVM.StrtodReader.suffix_acc_frac
#print axioms LeanLLVM.StrtodReader.suffix_acc_exp
#print axioms LeanLLVM.StrtodReader.suffix_acc_frac_exp
#print axioms LeanLLVM.StrtodReader.body_acc_zero
#print axioms LeanLLVM.StrtodReader.body_acc_lead_end
#print axioms LeanLLVM.StrtodReader.body_acc_lead
#print axioms LeanLLVM.StrtodReader.intPart_head
#print axioms LeanLLVM.StrtodReader.numBody_head
#print axioms LeanLLVM.StrtodReader.body_acc
#print axioms LeanLLVM.StrtodReader.reader_complete
#print axioms LeanLLVM.StrtodReader.reader_isSome_eq_numLexB
#print axioms LeanLLVM.StrtodReader.tier1_no_reader
#print axioms LeanLLVM.StrtodReader.tier3_no_reader
#print axioms LeanLLVM.StrtodReader.reader_refuses_double_zero
#print axioms LeanLLVM.StrtodReader.reader_refuses_empty
#print axioms LeanLLVM.StrtodReader.reader_refuses_lone_minus
#print axioms LeanLLVM.StrtodReader.reader_refuses_plus
#print axioms LeanLLVM.StrtodReader.reader_refuses_bare_dot
#print axioms LeanLLVM.StrtodReader.reader_refuses_empty_frac
#print axioms LeanLLVM.StrtodReader.reader_refuses_empty_exp
#print axioms LeanLLVM.StrtodReader.reader_refuses_signed_empty_exp
#print axioms LeanLLVM.StrtodReader.reader_refuses_trailing
#print axioms LeanLLVM.StrtodReader.reader_neg_zero
#print axioms LeanLLVM.StrtodReader.reader_neg_zero_mantissa
#print axioms LeanLLVM.StrtodReader.reader_exp_sign_magnitude
#print axioms LeanLLVM.StrtodReader.reader_exp_leading_zeros
#print axioms LeanLLVM.StrtodReader.reader_exp_plus
#print axioms LeanLLVM.StrtodReader.reader_exp_upper
#print axioms LeanLLVM.StrtodReader.reader_exp_spellings_agree
#print axioms LeanLLVM.StrtodReader.reader_mantissa
#print axioms LeanLLVM.StrtodReader.reader_digit_counts

end LeanLLVM.StrtodReader
