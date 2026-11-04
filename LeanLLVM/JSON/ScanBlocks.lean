/-
The refinement: scanning in thirty-two byte blocks, then the tail one byte at a time,
agrees with the parser's own string scan.

`scanStringAt` reads windows and `bodyRun` steps the byte rule; `scanStringAt_ok_of_bodyRun_closed`
says a run that closes is the scan's acceptance at the same position, and the character
lemmas below say the byte rule walks a body exactly as `scanCharsFrom` does, one character
per step, on the state `BodyState.body` at every character boundary.  `run_of_strChars`
transfers that to the reference scan's own success, and `scan_simd_refines_scalar` is the
whole-scan statement `docs/contract.md:89` names: **on every body `scanCharsEnd` accepts,
the scan reports the same closing position**, and every position the scan accepts ends at a
quote.

The accepting direction is the whole of it.  A body the model accepts is not claimed to be
one `scanCharsEnd` accepts: the byte rule needs no escape digits, no surrogate pairing and
no character policy, and those are the string stage's questions.
-/
import LeanLLVM.JSON.ScanString
import LeanLLVM.JSON.Scan

namespace LeanLLVM.JSON

open ByteString

set_option maxRecDepth 10000

/-! ### The run's equations

`bodyRun`'s two unfoldings, and one step of it: a continuing byte leaves the run with one
less fuel at the next position, and a closing byte ends it there.
-/

private theorem bodyRun_zero (bs : Bytes) (i : Nat) (st : BodyState) :
    bodyRun bs 0 i st = .open st i := rfl

private theorem bodyRun_succ (bs : Bytes) (fuel i : Nat) (st : BodyState) :
    bodyRun bs (fuel + 1) i st =
      (match bs[i]? with
       | none => .open st i
       | some b =>
           match bodyStep st b with
           | .cont st' => bodyRun bs fuel (i + 1) st'
           | .closed => .closed (i + 1)
           | .refused s => .refused s i) := rfl

/-- One continuing byte: the run's fuel drops by one and its position advances by one. -/
private theorem run_step {bs : Bytes} {i m : Nat} {st st' : BodyState} {b : UInt8}
    (hb : bs[i]? = some b) (hs : bodyStep st b = .cont st') :
    bodyRun bs (m + 1) i st = bodyRun bs m (i + 1) st' := by
  rw [bodyRun_succ, hb]
  simp only [hs]

/-- One closing byte: the run ends just past it. -/
private theorem run_close {bs : Bytes} {i m : Nat} {st : BodyState} {b : UInt8}
    (hb : bs[i]? = some b) (hs : bodyStep st b = .closed) :
    bodyRun bs (m + 1) i st = .closed (i + 1) := by
  rw [bodyRun_succ, hb]
  simp only [hs]

/-! ### Lookups in a dropped prefix

A window's run reads a cons chain by position; these put that position back in the
carrier's own indexing.
-/

/-- A lookup in a `foldr`-built cons chain is the list's own lookup, below its length. -/
private theorem getElem?_foldr_cons (l : List UInt8) (rest : Bytes) :
    ∀ {j : Nat}, j < l.length → (l.foldr ByteString.cons rest)[j]? = l[j]? := by
  induction l with
  | nil => intro j hj; simp at hj
  | cons a t ih =>
      intro j hj
      cases j with
      | zero => exact ByteString.getElem?_cons_zero a _
      | succ k =>
          have hk : k < t.length := by simpa using hj
          rw [List.foldr_cons, ByteString.getElem?_cons_succ, ih hk]
          rfl

/-- A lookup at an offset into a dropped cons chain. -/
private theorem lookup_cons {bs : Bytes} {i : Nat} {l : List UInt8} {rest : Bytes} {j : Nat}
    (hdrop : bs.drop i = l.foldr ByteString.cons rest) (hj : j < l.length) :
    bs[i + j]? = l[j]? := by
  rw [← ByteString.getElem?_drop, hdrop]
  exact getElem?_foldr_cons l rest hj

/-! ### The byte rule's state at a body's characters

The nine lead classes and the three continuation counts of the requirement, and the
byte-rule steps they induce.  `Utf8Char`'s ranges are these ranges, which is what
`utf8Len_iff` states; the lemmas here read them forward, as the run needs them.
-/

private theorem step_none_of_lt {b : UInt8} (hb : b < 0x80) :
    Utf8Need.step .none b = some .none := by
  simp only [Utf8Need.step]
  rw [ite_eq_left hb]

private theorem step_none_two {b : UInt8} (h0 : 0xC2 ≤ b) (h1 : b ≤ 0xDF) :
    Utf8Need.step .none b = some (.more 1 0x80 0xBF) := by
  have hlt : ¬ b < 0x80 := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_e0 : Utf8Need.step .none 0xE0 = some (.more 2 0xA0 0xBF) := by
  decide

private theorem step_none_e1ec {b : UInt8} (h0 : 0xE1 ≤ b) (h1 : b ≤ 0xEC) :
    Utf8Need.step .none b = some (.more 2 0x80 0xBF) := by
  have hlt : ¬ b < 0x80 := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
    omega
  have hne : ¬ (0xC2 ≤ b ∧ b ≤ 0xDF) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne0 : ¬ b = 0xE0 := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_ed : Utf8Need.step .none 0xED = some (.more 2 0x80 0x9F) := by
  decide

private theorem step_none_eeef {b : UInt8} (h0 : 0xEE ≤ b) (h1 : b ≤ 0xEF) :
    Utf8Need.step .none b = some (.more 2 0x80 0xBF) := by
  have hlt : ¬ b < 0x80 := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
    omega
  have hne : ¬ (0xC2 ≤ b ∧ b ≤ 0xDF) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne0 : ¬ b = 0xE0 := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne1 : ¬ (0xE1 ≤ b ∧ b ≤ 0xEC) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne2 : ¬ b = 0xED := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_right hne1,
    ite_eq_right hne2, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_f0 : Utf8Need.step .none 0xF0 = some (.more 3 0x90 0xBF) := by
  decide

private theorem step_none_f1f3 {b : UInt8} (h0 : 0xF1 ≤ b) (h1 : b ≤ 0xF3) :
    Utf8Need.step .none b = some (.more 3 0x80 0xBF) := by
  have hlt : ¬ b < 0x80 := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
    omega
  have hne : ¬ (0xC2 ≤ b ∧ b ≤ 0xDF) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne0 : ¬ b = 0xE0 := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne1 : ¬ (0xE1 ≤ b ∧ b ≤ 0xEC) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne2 : ¬ b = 0xED := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne3 : ¬ (0xEE ≤ b ∧ b ≤ 0xEF) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne4 : ¬ b = 0xF0 := by
    intro hc; subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_right hne1,
    ite_eq_right hne2, ite_eq_right hne3, ite_eq_right hne4, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_f4 : Utf8Need.step .none 0xF4 = some (.more 3 0x80 0x8F) := by
  decide

private theorem step_more_one {lo hi c : UInt8} (hlo : lo ≤ c) (hhi : c ≤ hi) :
    Utf8Need.step (.more 1 lo hi) c = some .none := by
  simp only [Utf8Need.step]
  rw [ite_eq_left ⟨hlo, hhi⟩]
  simp

private theorem step_more_two {lo hi c : UInt8} (hlo : lo ≤ c) (hhi : c ≤ hi) :
    Utf8Need.step (.more 2 lo hi) c = some (.more 1 0x80 0xBF) := by
  simp only [Utf8Need.step]
  rw [ite_eq_left ⟨hlo, hhi⟩]
  simp

private theorem step_more_three {lo hi c : UInt8} (hlo : lo ≤ c) (hhi : c ≤ hi) :
    Utf8Need.step (.more 3 lo hi) c = some (.more 2 0x80 0xBF) := by
  simp only [Utf8Need.step]
  rw [ite_eq_left ⟨hlo, hhi⟩]
  simp

/-- A lead byte in a multi-byte class is neither a quote nor a backslash, and is not a
control byte: the run consults the requirement, not the body's own refusals. -/
private theorem isQuoteB_false_of_ge {b : UInt8} (h : 0xC2 ≤ b) : IsQuoteB b = false := by
  simp only [IsQuoteB]
  rw [decide_eq_false_iff_not]
  intro hb; subst hb
  simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h
  omega

private theorem isBackslashB_false_of_ge {b : UInt8} (h : 0xC2 ≤ b) :
    IsBackslashB b = false := by
  simp only [IsBackslashB]
  rw [decide_eq_false_iff_not]
  intro hb; subst hb
  simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h
  omega

private theorem not_lt_of_ge_0xc2 {b : UInt8} (h : 0xC2 ≤ b) : ¬ b < 0x20 := by
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat] at h ⊢
  omega

private theorem bodyStep_lead {b : UInt8} {u : Utf8Need}
    (hq : IsQuoteB b = false) (hs : IsBackslashB b = false) (hlt : ¬ b < 0x20)
    (hu : Utf8Need.step .none b = some u) :
    bodyStep BodyState.body b = .cont ⟨true, false, u⟩ := by
  simp [bodyStep, BodyState.body, hq, hs, hlt, hu]

private theorem bodyStep_more {n : Nat} {lo hi c : UInt8} {u : Utf8Need}
    (hu : Utf8Need.step (.more n lo hi) c = some u) :
    bodyStep ⟨true, false, .more n lo hi⟩ c = .cont ⟨true, false, u⟩ := by
  simp [bodyStep, hu]

/-- A content lane leaves the body state where it was. -/
private theorem bodyStep_content {b : UInt8}
    (h : IsContentLane BodyState.body b = true) :
    bodyStep BodyState.body b = .cont BodyState.body := by
  unfold IsContentLane at h
  simp only [BodyState.body, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hq⟩, hs⟩, hge⟩, hlt⟩ := h
  have hctl : ¬ b < 0x20 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hge ⊢
    omega
  simp [bodyStep, BodyState.body, hq, hs, hctl, step_none_of_lt hlt]

private theorem bodyStep_body_quote : bodyStep BodyState.body 0x22 = .closed := rfl

private theorem bodyStep_body_backslash :
    bodyStep BodyState.body 0x5C = .cont ⟨true, true, Utf8Need.none⟩ := rfl

/-- The byte after a backslash is escaped content, whatever byte it is. -/
private theorem bodyStep_body_run {e : UInt8} :
    bodyStep ⟨true, true, Utf8Need.none⟩ e = .cont BodyState.body := by
  simp [bodyStep, BodyState.body]

/-- The four facts that make a byte a content lane at the body state. -/
private theorem isContentLane_body {b : UInt8} (hq : b ≠ 0x22) (hs : b ≠ 0x5C)
    (hge : (0x20 : UInt8) ≤ b) (hlt : b < 0x80) :
    IsContentLane BodyState.body b = true := by
  have hq' : IsQuoteB b = false := by
    simp only [IsQuoteB]; rw [decide_eq_false_iff_not]; exact hq
  have hs' : IsBackslashB b = false := by
    simp only [IsBackslashB]; rw [decide_eq_false_iff_not]; exact hs
  simp [IsContentLane, BodyState.body, hq', hs', hge, hlt]

/-! ### A character's bytes through the byte rule

Each accepted character is one step of the run: the body state is the same on entry and
on exit, and the position advances by exactly the character's bytes.  The lead byte's
class and its continuation bytes are `Utf8Char`'s ranges, so the run and the reference
scan consume the same bytes — a character that straddles a window boundary is no
different, because these are statements about the bytes and not about lanes.
-/

/-- A run of content lanes: the state is unchanged and the position advances by the
list's length. -/
private theorem run_content_list (l : List UInt8) :
    ∀ {bs : Bytes} {i : Nat} {rest : Bytes} {m : Nat},
      bs.drop i = l.foldr ByteString.cons rest →
      (∀ b, b ∈ l → IsContentLane BodyState.body b = true) →
      bodyRun bs (m + l.length) i BodyState.body =
        bodyRun bs m (i + l.length) BodyState.body := by
  induction l with
  | nil =>
      intro bs i rest m _ _
      simp
  | cons a t ih =>
      intro bs i rest m hdrop hc
      have hca : IsContentLane BodyState.body a = true := hc a (List.mem_cons_self ..)
      have hct : ∀ b, b ∈ t → IsContentLane BodyState.body b = true :=
        fun b hb => hc b (List.mem_cons_of_mem a hb)
      have hb : bs[i]? = some a := by
        have h := lookup_cons (bs := bs) (i := i) (l := a :: t) (rest := rest) (j := 0)
          hdrop (by simp)
        rw [show i + 0 = i from rfl] at h
        exact h
      have hdrop' : bs.drop (i + 1) = t.foldr ByteString.cons rest := by
        rw [← ByteString.drop_drop (bs := bs) (j := i) (i := 1), hdrop, List.foldr_cons,
          ByteString.drop_succ_cons, ByteString.drop_zero]
      rw [show m + (a :: t).length = (m + t.length) + 1 from by
            simp only [List.length_cons]; omega,
        run_step hb (bodyStep_content hca),
        ih (i := i + 1) (m := m) hdrop' hct,
        show (i + 1) + t.length = i + (a :: t).length from by
          simp only [List.length_cons]; omega]

/-- A two-byte escape: the backslash starts a run and the next byte consumes it. -/
private theorem run_escape {bs : Bytes} {i : Nat} {e : UInt8} {rest : Bytes}
    (hdrop : bs.drop i = 0x5C +: e +: rest) (m : Nat) :
    bodyRun bs (m + 2) i BodyState.body = bodyRun bs m (i + 2) BodyState.body := by
  have hb0 : bs[i]? = some 0x5C := by
    have h := lookup_cons (bs := bs) (i := i) (l := [0x5C, e]) (rest := rest) (j := 0)
      hdrop (by simp)
    rw [show i + 0 = i from rfl] at h
    exact h
  have hb1 : bs[i + 1]? = some e := by
    have h := lookup_cons (bs := bs) (i := i) (l := [0x5C, e]) (rest := rest) (j := 1)
      hdrop (by simp)
    exact h
  rw [show m + 2 = (m + 1) + 1 from by omega,
    run_step hb0 bodyStep_body_backslash, run_step hb1 bodyStep_body_run,
    show (i + 1) + 1 = i + 2 from by omega]

/-- A two-byte character: the lead's class and one continuation byte. -/
private theorem run_two {bs : Bytes} {i : Nat} {b0 b1 lo hi : UInt8} {rest : Bytes}
    (hdrop : bs.drop i = b0 +: b1 +: rest) (hge : 0xC2 ≤ b0)
    (h0 : Utf8Need.step .none b0 = some (.more 1 lo hi)) (hlo : lo ≤ b1) (hhi : b1 ≤ hi)
    (m : Nat) :
    bodyRun bs (m + 2) i BodyState.body = bodyRun bs m (i + 2) BodyState.body := by
  have hb0 : bs[i]? = some b0 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1]) (rest := rest) (j := 0)
      hdrop (by simp)
    rw [show i + 0 = i from rfl] at h
    exact h
  have hb1 : bs[i + 1]? = some b1 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1]) (rest := rest) (j := 1)
      hdrop (by simp)
    exact h
  rw [show m + 2 = (m + 1) + 1 from by omega,
    run_step hb0 (bodyStep_lead (isQuoteB_false_of_ge hge) (isBackslashB_false_of_ge hge)
      (not_lt_of_ge_0xc2 hge) h0),
    run_step hb1 (bodyStep_more (step_more_one hlo hhi)),
    show (i + 1) + 1 = i + 2 from by omega]
  rfl

/-- A three-byte character: the lead's class and two continuation bytes. -/
private theorem run_three {bs : Bytes} {i : Nat} {b0 b1 b2 lo hi : UInt8} {rest : Bytes}
    (hdrop : bs.drop i = b0 +: b1 +: b2 +: rest) (hge : 0xC2 ≤ b0)
    (h0 : Utf8Need.step .none b0 = some (.more 2 lo hi)) (hlo : lo ≤ b1) (hhi : b1 ≤ hi)
    (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) (m : Nat) :
    bodyRun bs (m + 3) i BodyState.body = bodyRun bs m (i + 3) BodyState.body := by
  have hb0 : bs[i]? = some b0 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2]) (rest := rest) (j := 0)
      hdrop (by simp)
    rw [show i + 0 = i from rfl] at h
    exact h
  have hb1 : bs[i + 1]? = some b1 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2]) (rest := rest) (j := 1)
      hdrop (by simp)
    exact h
  have hb2 : bs[(i + 1) + 1]? = some b2 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2]) (rest := rest) (j := 2)
      hdrop (by simp)
    rw [show i + 2 = (i + 1) + 1 from by omega] at h
    exact h
  rw [show m + 3 = ((m + 1) + 1) + 1 from by omega,
    run_step hb0 (bodyStep_lead (isQuoteB_false_of_ge hge) (isBackslashB_false_of_ge hge)
      (not_lt_of_ge_0xc2 hge) h0),
    run_step hb1 (bodyStep_more (step_more_two hlo hhi)),
    run_step hb2 (bodyStep_more (step_more_one h2 h2')),
    show ((i + 1) + 1) + 1 = i + 3 from by omega]
  rfl

/-- A four-byte character: the lead's class and three continuation bytes. -/
private theorem run_four {bs : Bytes} {i : Nat} {b0 b1 b2 b3 lo hi : UInt8} {rest : Bytes}
    (hdrop : bs.drop i = b0 +: b1 +: b2 +: b3 +: rest) (hge : 0xC2 ≤ b0)
    (h0 : Utf8Need.step .none b0 = some (.more 3 lo hi)) (hlo : lo ≤ b1) (hhi : b1 ≤ hi)
    (h2 : 0x80 ≤ b2) (h2' : b2 ≤ 0xBF) (h3 : 0x80 ≤ b3) (h3' : b3 ≤ 0xBF) (m : Nat) :
    bodyRun bs (m + 4) i BodyState.body = bodyRun bs m (i + 4) BodyState.body := by
  have hb0 : bs[i]? = some b0 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2, b3]) (rest := rest)
      (j := 0) hdrop (by simp)
    rw [show i + 0 = i from rfl] at h
    exact h
  have hb1 : bs[i + 1]? = some b1 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2, b3]) (rest := rest)
      (j := 1) hdrop (by simp)
    exact h
  have hb2 : bs[(i + 1) + 1]? = some b2 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2, b3]) (rest := rest)
      (j := 2) hdrop (by simp)
    rw [show i + 2 = (i + 1) + 1 from by omega] at h
    exact h
  have hb3 : bs[((i + 1) + 1) + 1]? = some b3 := by
    have h := lookup_cons (bs := bs) (i := i) (l := [b0, b1, b2, b3]) (rest := rest)
      (j := 3) hdrop (by simp)
    rw [show i + 3 = ((i + 1) + 1) + 1 from by omega] at h
    exact h
  rw [show m + 4 = (((m + 1) + 1) + 1) + 1 from by omega,
    run_step hb0 (bodyStep_lead (isQuoteB_false_of_ge hge) (isBackslashB_false_of_ge hge)
      (not_lt_of_ge_0xc2 hge) h0),
    run_step hb1 (bodyStep_more (step_more_three hlo hhi)),
    run_step hb2 (bodyStep_more (step_more_two h2 h2')),
    run_step hb3 (bodyStep_more (step_more_one h3 h3')),
    show (((i + 1) + 1) + 1) + 1 = i + 4 from by omega]
  rfl

/-- A `\u` escape: the two-byte escape and four content lanes. -/
private theorem run_uchar {bs : Bytes} {i : Nat} {h0 h1 h2 h3 : UInt8} {rest : Bytes}
    (hdrop : bs.drop i = 0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest)
    (c0 : IsContentLane BodyState.body h0 = true)
    (c1 : IsContentLane BodyState.body h1 = true)
    (c2 : IsContentLane BodyState.body h2 = true)
    (c3 : IsContentLane BodyState.body h3 = true) (m : Nat) :
    bodyRun bs (m + 6) i BodyState.body = bodyRun bs m (i + 6) BodyState.body := by
  have hdrop2 : bs.drop (i + 2) = h0 +: h1 +: h2 +: h3 +: rest := by
    rw [← ByteString.drop_drop (bs := bs) (j := i) (i := 2), hdrop]
    simp only [ByteString.drop, ByteString.data_toList_cons]
    rfl
  rw [show m + 6 = (m + 4) + 2 from by omega,
    run_escape (bs := bs) (i := i) (e := 0x75)
      (rest := h0 +: h1 +: h2 +: h3 +: rest) hdrop (m := m + 4),
    show m + 4 = m + [h0, h1, h2, h3].length from by simp,
    run_content_list [h0, h1, h2, h3] (bs := bs) (i := i + 2) (rest := rest) (m := m)
      hdrop2 (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact c0
        · exact c1
        · exact c2
        · exact c3),
    show (i + 2) + [h0, h1, h2, h3].length = i + 6 from by simp]

/-- A surrogate pair's twelve bytes: two `\u` escapes, no second pass for the digits. -/
private theorem run_pair {bs : Bytes} {i : Nat} {h0 h1 h2 h3 l0 l1 l2 l3 : UInt8}
    {rest : Bytes}
    (hdrop : bs.drop i = 0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
      l0 +: l1 +: l2 +: l3 +: rest)
    (c0 : IsContentLane BodyState.body h0 = true)
    (c1 : IsContentLane BodyState.body h1 = true)
    (c2 : IsContentLane BodyState.body h2 = true)
    (c3 : IsContentLane BodyState.body h3 = true)
    (d0 : IsContentLane BodyState.body l0 = true)
    (d1 : IsContentLane BodyState.body l1 = true)
    (d2 : IsContentLane BodyState.body l2 = true)
    (d3 : IsContentLane BodyState.body l3 = true) (m : Nat) :
    bodyRun bs (m + 12) i BodyState.body = bodyRun bs m (i + 12) BodyState.body := by
  have hdrop6 : bs.drop (i + 6) = 0x5C +: 0x75 +: l0 +: l1 +: l2 +: l3 +: rest := by
    rw [← ByteString.drop_drop (bs := bs) (j := i) (i := 6), hdrop]
    simp only [ByteString.drop, ByteString.data_toList_cons]
    rfl
  rw [show m + 12 = (m + 6) + 6 from by omega,
    run_uchar (bs := bs) (i := i) hdrop c0 c1 c2 c3 (m := m + 6),
    run_uchar (bs := bs) (i := i + 6) hdrop6 d0 d1 d2 d3 (m := m),
    show (i + 6) + 6 = i + 12 from by omega]

/-! ### The characters of the reference scan

`scanCharsFrom` accepts exactly `StrChars .strict`, and every character of that relation
is one of the shapes above.  `run_utf8Char` is the unescaped clause: the run advances by
the coded character's bytes whatever the class, because the requirement's ranges and
`Utf8Char`'s are one set of ranges.
-/

/-- A multi-byte class is above `0xC2`, so a class ordered above it is too. -/
private theorem le_0xc2_of_le {a b : UInt8} (h1 : 0xC2 ≤ a) (h2 : a ≤ b) : 0xC2 ≤ b := by
  simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h2 ⊢
  omega

/-- An unescaped character: the run advances by its bytes and stays at the body state. -/
private theorem run_utf8Char {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest)
    (hctrl : (0x20 : Nat) ≤ c) (hq : c ≠ 0x22) (hbs : c ≠ 0x5C) :
    ∀ {bs : Bytes} {i : Nat}, bs.drop i = b → ∀ m,
      bodyRun bs (m + (b.size - rest.size)) i BodyState.body =
        bodyRun bs m (i + (b.size - rest.size)) BodyState.body := by
  induction h with
  | @one b0 rest0 hlt =>
      intro bs i hdrop m
      have hsz : (b0 +: rest0).size - rest0.size = 1 := by
        rw [ByteString.size_cons]; omega
      rw [hsz]
      have hge : (0x20 : UInt8) ≤ b0 := by
        simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat]
        exact hctrl
      have hneq : b0 ≠ 0x22 := by
        intro hb; subst hb; exact hq rfl
      have hneq' : b0 ≠ 0x5C := by
        intro hb; subst hb; exact hbs rfl
      have hcont : IsContentLane BodyState.body b0 = true :=
        isContentLane_body hneq hneq' hge hlt
      have hlook : bs[i]? = some b0 := by
        have h' := lookup_cons (bs := bs) (i := i) (l := [b0]) (rest := rest0) (j := 0)
          hdrop (by simp)
        rw [show i + 0 = i from rfl] at h'
        exact h'
      exact run_step hlook (bodyStep_content hcont)
  | @two b0 b1 rest0 h0 h0' h1 h1' =>
      intro bs i hdrop m
      have hsz : (b0 +: b1 +: rest0).size - rest0.size = 2 := by
        rw [ByteString.size_cons, ByteString.size_cons]; omega
      rw [hsz]
      exact run_two hdrop h0 (step_none_two h0 h0') h1 h1' m
  | @three₀ b1 b2 rest0 h1 h1' h2 h2' =>
      intro bs i hdrop m
      have hsz : (0xE0 +: b1 +: b2 +: rest0).size - rest0.size = 3 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega
      rw [hsz]
      exact run_three hdrop (by decide) step_none_e0 h1 h1' h2 h2' m
  | @three₁ b0 b1 b2 rest0 h0 h0' h1 h1' h2 h2' =>
      intro bs i hdrop m
      have hsz : (b0 +: b1 +: b2 +: rest0).size - rest0.size = 3 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega
      rw [hsz]
      exact run_three hdrop (le_0xc2_of_le (by decide) h0) (step_none_e1ec h0 h0')
        h1 h1' h2 h2' m
  | @three₂ b1 b2 rest0 h1 h1' h2 h2' =>
      intro bs i hdrop m
      have hsz : (0xED +: b1 +: b2 +: rest0).size - rest0.size = 3 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega
      rw [hsz]
      exact run_three hdrop (by decide) step_none_ed h1 h1' h2 h2' m
  | @three₃ b0 b1 b2 rest0 h0 h0' h1 h1' h2 h2' =>
      intro bs i hdrop m
      have hsz : (b0 +: b1 +: b2 +: rest0).size - rest0.size = 3 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega
      rw [hsz]
      exact run_three hdrop (le_0xc2_of_le (by decide) h0) (step_none_eeef h0 h0')
        h1 h1' h2 h2' m
  | @four₀ b1 b2 b3 rest0 h1 h1' h2 h2' h3 h3' =>
      intro bs i hdrop m
      have hsz : (0xF0 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons]
        omega
      rw [hsz]
      exact run_four hdrop (by decide) step_none_f0 h1 h1' h2 h2' h3 h3' m
  | @four₁ b0 b1 b2 b3 rest0 h0 h0' h1 h1' h2 h2' h3 h3' =>
      intro bs i hdrop m
      have hsz : (b0 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons]
        omega
      rw [hsz]
      exact run_four hdrop (le_0xc2_of_le (by decide) h0) (step_none_f1f3 h0 h0')
        h1 h1' h2 h2' h3 h3' m
  | @four₂ b1 b2 b3 rest0 h1 h1' h2 h2' h3 h3' =>
      intro bs i hdrop m
      have hsz : (0xF4 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons]
        omega
      rw [hsz]
      exact run_four hdrop (by decide) step_none_f4 h1 h1' h2 h2' h3 h3' m

/-! ### The result the run never touches

`content_of_hexVal` and `hexVal_of_hex4` are the escape digits' classification: a hex
digit is a content lane, so `\u`'s four digits are bytes the run skips — the mask needs
no escape counter, which is why `BodyState` has none.
-/

private theorem isContentLane_body_nat {d : UInt8} (hq : d.toNat ≠ 0x22)
    (hs : d.toNat ≠ 0x5C) (hge : 0x20 ≤ d.toNat) (hlt : d.toNat < 0x80) :
    IsContentLane BodyState.body d = true := by
  refine isContentLane_body ?_ ?_ ?_ ?_
  · intro hh; subst hh; exact hq rfl
  · intro hh; subst hh; exact hs rfl
  · simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat]; exact hge
  · simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; exact hlt

/-- `HexVal`'s three classes, as the code-point bounds they are. -/
private theorem hexVal_bounds {d : UInt8} {v : Nat} (h : HexVal d = some v) :
    (0x30 ≤ d.toNat ∧ d.toNat ≤ 0x39) ∨ (0x41 ≤ d.toNat ∧ d.toNat ≤ 0x46) ∨
      (0x61 ≤ d.toNat ∧ d.toNat ≤ 0x66) := by
  unfold HexVal at h
  cases hd : IsDigitB d with
  | true =>
      left
      unfold IsDigitB at hd
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
        UInt8.toNat_ofNat] at hd
      omega
  | false =>
      simp only [hd] at h
      cases hb : (decide (0x41 ≤ d) && decide (d ≤ 0x46)) with
      | true =>
          right; left
          simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
            UInt8.toNat_ofNat] at hb
          omega
      | false =>
          simp only [hb] at h
          cases hc : (decide (0x61 ≤ d) && decide (d ≤ 0x66)) with
          | true =>
              right; right
              simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
                UInt8.toNat_ofNat] at hc
              omega
          | false =>
              simp only [hc] at h
              exact absurd h (by intro hh; cases hh)

/-- A hex digit is a content lane: `HexVal`'s three classes are inside `[0x20, 0x80)` and
away from the quote and the backslash. -/
private theorem content_of_hexVal {d : UInt8} {v : Nat} (h : HexVal d = some v) :
    IsContentLane BodyState.body d = true := by
  rcases hexVal_bounds h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact isContentLane_body_nat (by omega) (by omega) (by omega) (by omega)
  · exact isContentLane_body_nat (by omega) (by omega) (by omega) (by omega)
  · exact isContentLane_body_nat (by omega) (by omega) (by omega) (by omega)

/-- A successful `Hex4` reads its first digit. -/
private theorem hexVal_of_hex4_one {a b c d : UInt8} {v : Nat} (h : Hex4 a b c d = some v) :
    ∃ x, HexVal a = some x := by
  cases ha : HexVal a with
  | none => simp [Hex4, ha] at h
  | some x => exact ⟨x, rfl⟩

/-- A successful `Hex4` reads its second digit. -/
private theorem hexVal_of_hex4_two {a b c d : UInt8} {v : Nat} (h : Hex4 a b c d = some v) :
    ∃ x, HexVal b = some x := by
  cases ha : HexVal a with
  | none => simp [Hex4, ha] at h
  | some x =>
      cases hb : HexVal b with
      | none => simp [Hex4, ha, hb] at h
      | some y => exact ⟨y, rfl⟩

/-- A successful `Hex4` reads its third digit. -/
private theorem hexVal_of_hex4_three {a b c d : UInt8} {v : Nat} (h : Hex4 a b c d = some v) :
    ∃ x, HexVal c = some x := by
  cases ha : HexVal a with
  | none => simp [Hex4, ha] at h
  | some x =>
      cases hb : HexVal b with
      | none => simp [Hex4, ha, hb] at h
      | some y =>
          cases hc : HexVal c with
          | none => simp [Hex4, ha, hb, hc] at h
          | some z => exact ⟨z, rfl⟩

/-- A successful `Hex4` reads its fourth digit. -/
private theorem hexVal_of_hex4_four {a b c d : UInt8} {v : Nat} (h : Hex4 a b c d = some v) :
    ∃ x, HexVal d = some x := by
  cases ha : HexVal a with
  | none => simp [Hex4, ha] at h
  | some x =>
      cases hb : HexVal b with
      | none => simp [Hex4, ha, hb] at h
      | some y =>
          cases hc : HexVal c with
          | none => simp [Hex4, ha, hb, hc] at h
          | some z =>
              cases hd : HexVal d with
              | none => simp [Hex4, ha, hb, hc, hd] at h
              | some w => exact ⟨w, rfl⟩

/-- Dropping a cons chain's own length leaves the rest. -/
private theorem drop_cons_chain : ∀ (l : List UInt8) (rest : Bytes),
    (l.foldr ByteString.cons rest).drop l.length = rest := by
  intro l
  induction l with
  | nil => intro rest; exact ByteString.drop_zero rest
  | cons a t ih =>
      intro rest
      rw [List.foldr_cons, show (a :: t).length = t.length + 1 from by
            rw [List.length_cons],
        ByteString.drop_succ_cons, ih]

/-- A character's bytes are its own length's drop: the run's advance is the character's
own byte count, read off `Utf8Char`'s constructors. -/
private theorem drop_of_utf8Char {b : Bytes} {c : Nat} {rest : Bytes}
    (h : Utf8Char b c rest) : b.drop (b.size - rest.size) = rest := by
  induction h with
  | @one b0 rest0 hlt =>
      rw [show (b0 +: rest0).size - rest0.size = 1 from by rw [ByteString.size_cons]; omega]
      exact drop_cons_chain [b0] rest0
  | @two b0 b1 rest0 h0 h0' h1 h1' =>
      rw [show (b0 +: b1 +: rest0).size - rest0.size = 2 from by rw [ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [b0, b1] rest0
  | @three₀ b1 b2 rest0 h1 h1' h2 h2' =>
      rw [show (0xE0 +: b1 +: b2 +: rest0).size - rest0.size = 3 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [0xE0, b1, b2] rest0
  | @three₁ b0 b1 b2 rest0 h0 h0' h1 h1' h2 h2' =>
      rw [show (b0 +: b1 +: b2 +: rest0).size - rest0.size = 3 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [b0, b1, b2] rest0
  | @three₂ b1 b2 rest0 h1 h1' h2 h2' =>
      rw [show (0xED +: b1 +: b2 +: rest0).size - rest0.size = 3 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [0xED, b1, b2] rest0
  | @three₃ b0 b1 b2 rest0 h0 h0' h1 h1' h2 h2' =>
      rw [show (b0 +: b1 +: b2 +: rest0).size - rest0.size = 3 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [b0, b1, b2] rest0
  | @four₀ b1 b2 b3 rest0 h1 h1' h2 h2' h3 h3' =>
      rw [show (0xF0 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [0xF0, b1, b2, b3] rest0
  | @four₁ b0 b1 b2 b3 rest0 h0 h0' h1 h1' h2 h2' h3 h3' =>
      rw [show (b0 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [b0, b1, b2, b3] rest0
  | @four₂ b1 b2 b3 rest0 h1 h1' h2 h2' h3 h3' =>
      rw [show (0xF4 +: b1 +: b2 +: b3 +: rest0).size - rest0.size = 4 from by rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]; omega]
      exact drop_cons_chain [0xF4, b1, b2, b3] rest0

/-! ### One character of the reference relation

`StrChar` is five clauses and four of them are run steps: the unescaped clause is
`run_utf8Char`, the short escape is two bytes whatever the escaped byte is, a `\u`
escape is its two bytes and four content lanes, and a surrogate pair is that twice.
The lone escape belongs to the `rfc` mode, so at `.strict` it has no instance.
-/

private theorem run_strChar {b : Bytes} {c : Nat} {mid : Bytes}
    (h : StrChar .strict b c mid) :
    ∀ {bs : Bytes} {i : Nat}, bs.drop i = b → ∀ m,
      bodyRun bs (m + (b.size - mid.size)) i BodyState.body =
        bodyRun bs m (i + (b.size - mid.size)) BodyState.body := by
  cases h with
  | @unescaped _ _ _ hu hctrl hq hbs vm =>
      intro bs i hdrop m
      exact run_utf8Char hu hctrl hq hbs hdrop m
  | @short e0 _ _ hv =>
      intro bs i hdrop m
      have hL : (0x5C +: e0 +: mid).size - mid.size = 2 := by
        rw [ByteString.size_cons, ByteString.size_cons]; omega
      rw [hL]
      exact run_escape hdrop m
  | @escU h0 h1 h2 h3 _ _ hx hs vm =>
      intro bs i hdrop m
      obtain ⟨v0, hv0⟩ := hexVal_of_hex4_one hx
      obtain ⟨v1, hv1⟩ := hexVal_of_hex4_two hx
      obtain ⟨v2, hv2⟩ := hexVal_of_hex4_three hx
      obtain ⟨v3, hv3⟩ := hexVal_of_hex4_four hx
      have hL : (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: mid).size - mid.size = 6 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]
        omega
      rw [hL]
      exact run_uchar hdrop (content_of_hexVal hv0) (content_of_hexVal hv1)
        (content_of_hexVal hv2) (content_of_hexVal hv3) m
  | @escPair h0 h1 h2 h3 l0 l1 l2 l3 _ _ _ _ hhi hlo hh hl hc vm =>
      intro bs i hdrop m
      obtain ⟨v0, hv0⟩ := hexVal_of_hex4_one hhi
      obtain ⟨v1, hv1⟩ := hexVal_of_hex4_two hhi
      obtain ⟨v2, hv2⟩ := hexVal_of_hex4_three hhi
      obtain ⟨v3, hv3⟩ := hexVal_of_hex4_four hhi
      obtain ⟨w0, hw0⟩ := hexVal_of_hex4_one hlo
      obtain ⟨w1, hw1⟩ := hexVal_of_hex4_two hlo
      obtain ⟨w2, hw2⟩ := hexVal_of_hex4_three hlo
      obtain ⟨w3, hw3⟩ := hexVal_of_hex4_four hlo
      have hL : (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
          l0 +: l1 +: l2 +: l3 +: mid).size - mid.size = 12 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]
        omega
      rw [hL]
      exact run_pair hdrop (content_of_hexVal hv0) (content_of_hexVal hv1)
        (content_of_hexVal hv2) (content_of_hexVal hv3) (content_of_hexVal hw0)
        (content_of_hexVal hw1) (content_of_hexVal hw2) (content_of_hexVal hw3) m
  | @escLone _ _ _ _ _ _ vm hx hs =>
      exact absurd vm (by decide)

/-- A character's bytes are exactly its own drop. -/
private theorem drop_of_strChar {b : Bytes} {c : Nat} {mid : Bytes}
    (h : StrChar .strict b c mid) : b.drop (b.size - mid.size) = mid := by
  cases h with
  | @unescaped _ _ _ hu hctrl hq hbs vm =>
      exact drop_of_utf8Char hu
  | @short e0 _ _ hv =>
      have hL : (0x5C +: e0 +: mid).size - mid.size = 2 := by
        rw [ByteString.size_cons, ByteString.size_cons]; omega
      rw [hL]
      exact drop_cons_chain [0x5C, e0] mid
  | @escU h0 h1 h2 h3 _ _ hx hs vm =>
      have hL : (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: mid).size - mid.size = 6 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]
        omega
      rw [hL]
      exact drop_cons_chain [0x5C, 0x75, h0, h1, h2, h3] mid
  | @escPair h0 h1 h2 h3 l0 l1 l2 l3 _ _ _ _ hhi hlo hh hl hc vm =>
      have hL : (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
          l0 +: l1 +: l2 +: l3 +: mid).size - mid.size = 12 := by
        rw [ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons,
          ByteString.size_cons, ByteString.size_cons, ByteString.size_cons]
        omega
      rw [hL]
      exact drop_cons_chain [0x5C, 0x75, h0, h1, h2, h3, 0x5C, 0x75, l0, l1, l2, l3] mid
  | @escLone _ _ _ _ _ _ vm hx hs =>
      exact absurd vm (by decide)

/-! ### The reference scan closes the run

A body `scanCharsFrom` accepts is a `StrChars` derivation, and each of its characters is
one run step: so the run closes at the byte the reference scan stops at, from the body's
first byte, with no assumption about the characters beyond the relation itself.  A body
the reference would refuse can be one the model accepts — the byte rule needs no
well-formed `\u`, no paired surrogate and no character policy — so this is the direction
the refinement states and no other.
-/

private theorem run_of_strChars {t : Bytes} {cs : List Nat} {rest : Bytes}
    (h : StrChars .strict t cs rest) :
    ∀ {bs : Bytes} {i : Nat}, bs.drop i = t → ∀ n, bs.size - i ≤ n →
      bodyRun bs n i BodyState.body = .closed (bs.size - rest.size) := by
  induction h with
  | @nil rest0 =>
      intro bs i hdrop n hn
      have hquote : bs[i]? = some 0x22 := by
        have h' := lookup_cons (bs := bs) (i := i) (l := [0x22]) (rest := rest0)
          (j := 0) hdrop (by simp)
        rw [show i + 0 = i from rfl] at h'
        exact h'
      have hlen : bs.size - i = rest0.size + 1 := by
        have h' : (bs.drop i).size = bs.size - i := ByteString.length_drop bs i
        rw [hdrop, ByteString.size_cons] at h'
        exact h'.symm
      have hi : i + 1 = bs.size - rest0.size := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [← hi]
      exact run_close hquote bodyStep_body_quote
  | @cons b0 c0 mid0 rest0 cs0 hchar htail ih =>
      intro bs i hdrop n hn
      have hlen : bs.size - i = b0.size := by
        have h' := ByteString.length_drop bs i
        rw [hdrop] at h'
        exact h'.symm
      have hn' : n = (n - (b0.size - mid0.size)) + (b0.size - mid0.size) := by omega
      rw [hn', run_strChar hchar hdrop]
      have hdrop' : bs.drop (i + (b0.size - mid0.size)) = mid0 := by
        rw [← ByteString.drop_drop (bs := bs) (j := i), hdrop]
        exact drop_of_strChar hchar
      exact ih hdrop' (n - (b0.size - mid0.size)) (by omega)

/-! ### The byte rule's own facts

The three facts the scan's refinement needs about the reference run: a closed step is a
quote, a closed run reads a quote just before its stop, and the run's fuel can be raised
above the position it closed at — the last one is what lets a thirty-two byte window and a
tail's own remainder both speak about the same run.
-/

/-- A closing step is the quote: the byte rule's only `.closed` answer. -/
private theorem eq_quote_of_closed {st : BodyState} {b : UInt8}
    (h : bodyStep st b = .closed) : b = 0x22 := by
  have hq : IsQuoteB b = true := by
    obtain ⟨ins, odd, utf8⟩ := st
    cases utf8 with
    | more n lo hi =>
        unfold bodyStep at h
        repeat' split at h
        all_goals
          first
          | assumption
          | simp at h
    | none =>
        cases odd with
        | true =>
            unfold bodyStep at h
            repeat' split at h
            all_goals
              first
              | assumption
              | simp at h
        | false =>
            cases ins with
            | false =>
                unfold bodyStep at h
                repeat' split at h
                all_goals
                  first
                  | assumption
                  | simp at h
            | true =>
                by_cases hq : IsQuoteB b = true
                · exact hq
                · exact absurd hq (by
                    unfold bodyStep at h
                    rw [ite_eq_right hq] at h
                    repeat' split at h
                    all_goals
                      first
                      | assumption
                      | simp at h)
  simpa [IsQuoteB] using hq

/-- A run that closes reads a quote at `k - 1`. -/
private theorem bodyRun_closed_quote {bs : Bytes} {fuel i : Nat} {st : BodyState} {k : Nat}
    (h : bodyRun bs fuel i st = .closed k) : bs[k - 1]? = some 0x22 := by
  induction fuel generalizing i st with
  | zero =>
      rw [bodyRun_zero] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      cases hb : bs[i]? with
      | none =>
          rw [bodyRun_succ, hb] at h
          exact absurd h (by simp)
      | some b =>
          rw [bodyRun_succ, hb] at h
          cases hs : bodyStep st b with
          | cont st' =>
              simp only [hs] at h
              exact ih h
          | closed =>
              simp only [hs, RunEnd.closed.injEq] at h
              subst h
              have hq := eq_quote_of_closed hs
              subst hq
              rw [Nat.add_sub_cancel]
              exact hb
          | refused s =>
              simp only [hs] at h
              exact absurd h (by simp)

/-- A closed run's fuel can be any length at least the closing position: the run reads the
same bytes either way. -/
private theorem bodyRun_closed_mono {bs : Bytes} :
    ∀ (fuel i : Nat) (st : BodyState) (k : Nat), bodyRun bs fuel i st = .closed k →
      ∀ fuel', k - i ≤ fuel' → bodyRun bs fuel' i st = .closed k := by
  intro fuel
  induction fuel with
  | zero =>
      intro i st k h
      rw [bodyRun_zero] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro i st k h fuel' hf
      cases hb : bs[i]? with
      | none =>
          rw [bodyRun_succ, hb] at h
          exact absurd h (by simp)
      | some b =>
          rw [bodyRun_succ, hb] at h
          cases hs : bodyStep st b with
          | cont st' =>
              simp only [hs] at h
              obtain ⟨k', rfl⟩ : ∃ k', fuel' = k' + 1 := by
                have hi : i + 1 < k := (bodyRun_bound h).1
                exact ⟨fuel' - 1, by omega⟩
              simp only [bodyRun_succ, hb, hs]
              exact ih (i + 1) st' k h k' (by omega)
          | closed =>
              simp only [hs, RunEnd.closed.injEq] at h
              subst h
              obtain ⟨k', rfl⟩ : ∃ k', fuel' = k' + 1 := ⟨fuel' - 1, by omega⟩
              simp only [bodyRun_succ, hb, hs]
          | refused s =>
              simp only [hs] at h
              exact absurd h (by simp)

/-- The run over `a + b` bytes is the run over `a` bytes, continued from where it stopped
with the remaining fuel. -/
private theorem bodyRun_add (bs : Bytes) (a b i : Nat) (st : BodyState) :
    bodyRun bs (a + b) i st =
      (match bodyRun bs a i st with
       | .closed k => .closed k
       | .open st' pos => bodyRun bs b pos st'
       | .refused s pos => .refused s pos) := by
  induction a generalizing i st with
  | zero =>
      rw [Nat.zero_add, bodyRun_zero]
  | succ a ih =>
      simp only [show a + 1 + b = (a + b) + 1 from by omega, bodyRun_succ]
      cases hb : bs[i]? with
      | none =>
          cases b with
          | zero => rfl
          | succ b' => simp only [bodyRun_succ, hb]
      | some b0 =>
          cases hs : bodyStep st b0 with
          | cont st' =>
              simp only [hs]
              exact ih (i + 1) st'
          | closed => simp only [hs]
          | refused s => simp only [hs]

/-! ### The block layer's lanes back in the carrier

The window's stop names a lane, and a lane is a carrier position: this is the block
indexing bridge `scanWindow_stop` carries, and `windowAt_stop_byte` reads a closing
stop's own byte through it.
-/

private theorem lane_getElem? {bs : Bytes} {i : Nat} {h : i + 32 ≤ bs.size} {k : Nat}
    (hk : k < 32) : bs[i + k]? = (List.ofFn (blockAt bs i h))[k]? := by
  have hjlen : k < (List.ofFn (blockAt bs i h)).length := by
    rw [List.length_ofFn]; exact hk
  have h1 : (List.ofFn (blockAt bs i h))[k]? = some (blockAt bs i h ⟨k, hk⟩) := by
    rw [List.getElem?_eq_getElem hjlen, List.getElem_ofFn]
  have hs : i + k < bs.size := by omega
  have h2 : bs[i + k]? = some (blockAt bs i h ⟨k, hk⟩) := by
    rw [ByteString.getElem?_eq_getElem (by rwa [ByteString.length_eq_size]), blockAt_apply]
    rfl
  rw [h1, h2]

/-- A closing stop's lane is a quote byte of the carrier. -/
private theorem windowAt_stop_byte {bs : Bytes} {i : Nat} {h : i + 32 ≤ bs.size}
    {st : BodyState} {j : Nat} (hstop : (windowAt bs i h st).stop = some (.close j)) :
    j < 32 ∧ bs[i + j]? = some 0x22 := by
  let l := List.ofFn (blockAt bs i h)
  have hspec := windowOf_stop_spec (bs := l) (st := st)
  have hstopw : (windowOf l st).stop = (windowAt bs i h st).stop := rfl
  rw [show (windowOf l st).stop = some (.close j) from hstopw.trans hstop] at hspec
  obtain ⟨hj32, ⟨b, hbk⟩, -, hclosed⟩ := hspec
  have hb : bs[i + j]? = some b := by
    rw [lane_getElem? (bs := bs) (i := i) (h := h) hj32]
    exact hbk
  have hq : b = 0x22 := eq_quote_of_closed (hclosed hbk)
  subst hq
  exact ⟨hj32, hb⟩

/-! ### The scan against the run

`scanStringAt` is the window fold and the run is the byte rule; these say a run that
closes is the scan's own acceptance at the same position, and that every position the
scan accepts ends at a quote.  The window is where the fuel drops by one and the run by
thirty-two, and `scanWindow_stop` is what makes the two one step.  `RunEnd`'s `open`
constructor shares its name with a keyword, so a `cases` alternative names it `«open»`;
the statements spell it `.open`, where the position disambiguates.
-/

/-- A run that closes is the scan's acceptance at the same position. -/
private theorem scanStringAt_ok_of_bodyRun_closed (bs : Bytes) :
    ∀ (fuel i : Nat) (st : BodyState) (k : Nat),
      bodyRun bs fuel i st = .closed k → scanStringAt bs fuel i st = .ok k := by
  intro fuel
  induction fuel with
  | zero =>
      intro i st k h
      rw [bodyRun_zero] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro i st k h
      rw [scanStringAt_succ]
      by_cases hw : i + 32 ≤ bs.size
      · rw [dite_eq_left hw]
        rcases Nat.lt_or_ge (fuel + 1) 32 with hlt | hge
        · have h32 : bodyRun bs 32 i st = .closed k :=
            bodyRun_closed_mono (i := i) (st := st) (k := k) (fuel := fuel + 1) h 32
              (by have := (bodyRun_bound h).2.1; omega)
          rw [scanWindow_stop bs i hw st] at h32
          cases hstop : (windowAt bs i hw st).stop with
          | some s =>
              cases s with
              | close j =>
                  simp only [hstop, RunEnd.closed.injEq] at h32
                  simp only []
                  rw [h32]
              | refuse j s =>
                  rw [hstop] at h32
                  exact absurd h32 (by simp)
          | none =>
              rw [hstop] at h32
              exact absurd h32 (by simp)
        · rw [show fuel + 1 = 32 + (fuel + 1 - 32) from by omega, bodyRun_add] at h
          rw [scanWindow_stop bs i hw st] at h
          cases hstop : (windowAt bs i hw st).stop with
          | some s =>
              cases s with
              | close j =>
                  simp only [hstop, RunEnd.closed.injEq] at h
                  simp only []
                  rw [h]
              | refuse j s =>
                  rw [hstop] at h
                  exact absurd h (by simp)
          | none =>
              rw [hstop] at h
              rw [scanStringAt_pos bs i hw]
              exact ih (i + 32) (windowAt bs i hw st).carry k
                (bodyRun_closed_mono (i := i + 32) (st := (windowAt bs i hw st).carry)
                  (k := k) (fuel := fuel + 1 - 32) h fuel
                  (by have := (bodyRun_bound h).2.1; omega))
      · rw [dite_eq_right hw]
        unfold tailRun
        rw [show bodyRun bs (bs.size - i) i st = .closed k from
          bodyRun_closed_mono (i := i) (st := st) (k := k) (fuel := fuel + 1) h (bs.size - i)
            (by have := (bodyRun_bound h).2.2; omega)]

/-- Every position the scan accepts ends at a quote: the `.close` branch's lane and the
tail's closing byte are the same witness. -/
private theorem scanStringAt_ok_spec (bs : Bytes) :
    ∀ (fuel i : Nat) (st : BodyState) (k : Nat), scanStringAt bs fuel i st = .ok k →
      i < k ∧ k ≤ bs.size ∧ bs[k - 1]? = some 0x22 := by
  intro fuel
  induction fuel with
  | zero =>
      intro i st k h
      have h0 : scanStringAt bs 0 i st = tailRun bs i st := rfl
      rw [h0] at h
      unfold tailRun at h
      cases hr' : bodyRun bs (bs.size - i) i st with
      | closed k0 =>
          rw [hr'] at h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨h1, -, h3⟩ := bodyRun_bound hr'
          exact ⟨h1, h3, bodyRun_closed_quote hr'⟩
      | «open» st' pos =>
          rw [hr'] at h
          exact absurd h (by simp)
      | refused s pos =>
          rw [hr'] at h
          exact absurd h (by simp)
  | succ fuel ih =>
      intro i st k h
      rw [scanStringAt_succ] at h
      by_cases hw : i + 32 ≤ bs.size
      · rw [dite_eq_left hw] at h
        cases hstop : (windowAt bs i hw st).stop with
        | some s =>
            cases s with
            | close j =>
                rw [hstop] at h
                simp only [Except.ok.injEq] at h
                obtain ⟨hj32, hb⟩ := windowAt_stop_byte hstop
                subst h
                refine ⟨by omega, by omega, ?_⟩
                rw [show i + j + 1 - 1 = i + j from by omega]
                exact hb
            | refuse j s =>
                rw [hstop] at h
                exact absurd h (by simp)
        | none =>
            rw [hstop, scanStringAt_pos bs i hw] at h
            obtain ⟨h1, h2, h3⟩ := ih (i + 32) (windowAt bs i hw st).carry k h
            exact ⟨by omega, h2, h3⟩
      · rw [dite_eq_right hw] at h
        unfold tailRun at h
        cases hr' : bodyRun bs (bs.size - i) i st with
        | closed k0 =>
            rw [hr'] at h
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨h1, -, h3⟩ := bodyRun_bound hr'
            exact ⟨h1, h3, bodyRun_closed_quote hr'⟩
        | «open» st' pos =>
            rw [hr'] at h
            exact absurd h (by simp)
        | refused s pos =>
            rw [hr'] at h
            exact absurd h (by simp)

/-! ### The refinement

The statements `docs/contract.md:89` names.  The accepting direction is the whole of it:
a body the reference scan accepts is one the scan accepts at the same position, and a
position the scan accepts ends at a quote.  Nothing here claims the converse, and nothing
here strengthens the model into a decoder: a malformed `\u`, an escaped unpaired
surrogate, and raw and escaped noncharacters are the string stage's refusals, and a body
carrying them is a body the byte rule walks without complaint.
-/

/-- `scan_simd_refines_scalar` — the contract's whole-scan row
(`docs/contract.md:89`).  Scanning in thirty-two byte blocks, then the tail one
byte at a time, agrees with the parser's own string scan: on every body
`scanCharsEnd` accepts, the model reports the same closing position. -/
theorem scan_simd_refines_scalar (bs : Bytes) :
    (∀ (q : Nat) (cs : List Nat) (stop : { n : Nat // n ≤ bs.size }),
        bs[q]? = some 0x22 → scanCharsEnd bs (q + 1) 0 = .ok (cs, stop) →
          scanStringBlocks bs q = .ok stop.val) ∧
    (∀ (q : Nat) {k : Nat},
        bs[q]? = some 0x22 → scanStringBlocks bs q = .ok k →
          q < k ∧ k ≤ bs.size ∧ bs[k - 1]? = some 0x22) := by
  refine ⟨?_, ?_⟩
  · intro q cs stop hq h
    obtain ⟨rest, hfrom, hdrop⟩ := scanCharsEnd_sound h
    have hchars : StrChars .strict (bs.drop (q + 1)) cs rest := scanCharsFrom_sound hfrom
    have hclosed := run_of_strChars hchars (bs := bs) (i := q + 1) rfl (bs.size - (q + 1))
      (Nat.le_refl _)
    have hlen : rest.size = bs.size - stop.val := by
      have h' : (bs.drop stop.val).size = bs.size - stop.val :=
        ByteString.length_drop bs stop.val
      rw [hdrop] at h'
      exact h'
    have hstop : bs.size - rest.size = stop.val := by omega
    rw [hstop] at hclosed
    exact scanStringAt_ok_of_bodyRun_closed bs (bs.size + 1) (q + 1) BodyState.body stop.val
      (bodyRun_closed_mono (i := q + 1) (st := BodyState.body) (k := stop.val)
        (fuel := bs.size - (q + 1)) hclosed (bs.size + 1) (by omega))
  · intro q k hq h
    obtain ⟨h1, h2, h3⟩ := scanStringAt_ok_spec bs (bs.size + 1) (q + 1) BodyState.body k h
    exact ⟨by omega, h2, h3⟩

/-- The first conjunct, named so a failure says which half broke. -/
theorem scanStringBlocks_ok_of_scanCharsEnd {bs : Bytes} {q : Nat} {cs : List Nat}
    {stop : { n : Nat // n ≤ bs.size }}
    (hq : bs[q]? = some 0x22) (h : scanCharsEnd bs (q + 1) 0 = .ok (cs, stop)) :
    scanStringBlocks bs q = .ok stop.val :=
  (scan_simd_refines_scalar bs).1 q cs stop hq h

/-- No false refusal: the first conjunct's contrapositive, stated in the contract's
own language — a body the parser's scanner accepts is never refused here. -/
theorem scanStringBlocks_refusal {bs : Bytes} {q : Nat} {s : Refusal}
    (hq : bs[q]? = some 0x22) (h : scanStringBlocks bs q = .error s) :
    ∀ (cs : List Nat) (stop : { n : Nat // n ≤ bs.size }),
      scanCharsEnd bs (q + 1) 0 ≠ .ok (cs, stop) := by
  intro cs stop hok
  rw [(scan_simd_refines_scalar bs).1 q cs stop hq hok] at h
  exact absurd h (by simp)

/-- The tail and finalisation rule: with nothing left, the scan refuses `ended` — an
open body, an odd run at the end (an escape whose second byte never came) and an
unfinished UTF-8 sequence alike, because the tail's fuel is the input's remainder and
`open` there means the input ran out (`tailRun_open_at`). -/
theorem tailRun_ended (bs : Bytes) (i : Nat) (h : bs.size ≤ i) (st : BodyState) :
    tailRun bs i st = .error (.ended, i) := by
  unfold tailRun
  rw [show bs.size - i = 0 from by omega, bodyRun_zero]

end LeanLLVM.JSON
