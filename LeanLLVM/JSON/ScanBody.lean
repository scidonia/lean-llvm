/-
The stateful scanner's carry: the one state a block scanner threads across a
window boundary, and the byte rule that steps it one byte at a time.

`BodyState` is the state `ScanBlock.lean`'s `ScanState` docstring names: the body
flag, the escape-run parity and the pending UTF-8 requirement, in one record and
with no escape countdown — a `\u` escape's digits are ordinary content lanes, and
whether they are well formed is the string stage's question, so a counter here
would be state no byte could reach.  `bodyStep` is the reference transition,
`Utf8Need.step` is its UTF-8 part, `IsContentLane` is the one predicate the lane
fold and the byte rule share, and `utf8Len`/`utf8Rest` measure a character's bytes
against `Utf8Char`.

The module imports the lane vocabulary of `ScanBlock` and the character relation of
`Utf8`: the model sits above both chains and nothing below it imports the model.
-/
import LeanLLVM.JSON.ScanBlock
import LeanLLVM.JSON.Utf8

namespace LeanLLVM.JSON

open ByteString

/-! ### The carry -/

/-- A UTF-8 continuation requirement: `more n lo hi` wants `n` more bytes, the
next in `[lo, hi]` and any after it in `[0x80, 0xBF]`.  A `\u` escape is **not**
tracked alongside it and has no state of its own. -/
inductive Utf8Need where
  | none
  | more (n : Nat) (lo hi : UInt8)
deriving DecidableEq, Repr

/-- **One** state, and **no escape field**: a `\u` escape needs no countdown.  Its
digits are ordinary content lanes, the second `\` of a surrogate pair is a backslash
lane the run rule sees, and whether the digits are well formed is the string stage's
question — so a countdown field would be dead state with prose claiming otherwise.
What crosses a boundary is the body flag, the run parity and the UTF-8 requirement. -/
structure BodyState where
  inside : Bool
  oddRun : Bool
  utf8 : Utf8Need
deriving DecidableEq, Repr

/-- A requirement is well formed when its count is one to three: `more 0` is never
produced, and a four-byte character's requirement starts at three. -/
def Utf8Need.WellFormed : Utf8Need → Prop
  | .none => True
  | .more n _ _ => 0 < n ∧ n ≤ 3

/-- A state is well formed when its requirement is, an odd run exists only inside a
body — a `\` escapes nothing outside a string — and an odd run never overlaps a
sequence, because `\` is ASCII and no continuation byte is. -/
def BodyState.WellFormed (st : BodyState) : Prop :=
  st.utf8.WellFormed ∧ (st.oddRun = true → st.inside = true) ∧
    (st.oddRun = true → st.utf8 = Utf8Need.none)

/-- The state at a body's first byte: inside, no run, no sequence.  A body starts
**inside** — the opening quote has already been consumed — which is what makes the
next quote a closing one. -/
def BodyState.body : BodyState := ⟨true, false, .none⟩

/-- The arity detector: this `example` fixes the state's field count, so re-adding a
field fails elaboration rather than passing every pin and `#guard`. -/
example : BodyState.body = ⟨true, false, Utf8Need.none⟩ := rfl

/-- The state at a scan's first byte when no body is open. -/
def BodyState.init : BodyState := ⟨false, false, .none⟩

/-- One byte through the UTF-8 requirement: `Option.none` when the byte cannot continue
the sequence, the requirement the byte leaves otherwise.  The nine lead classes are
`Utf8Char`'s constructors, not a second grammar.  **Every fallback is written
`Option.none`**: `Utf8Need` has a constructor also named `none`, so a bare `none` here
reads two ways, and reading an arm as the constructor yields a `step` that accepts an
out-of-range continuation byte and an invalid lead byte.  The two `decide` theorems
below are what such a reading fails to prove. -/
def Utf8Need.step (u : Utf8Need) (b : UInt8) : Option Utf8Need :=
  match u with
  | .none =>
      if b < 0x80 then some .none
      else if 0xC2 ≤ b ∧ b ≤ 0xDF then some (.more 1 0x80 0xBF)
      else if b = 0xE0 then some (.more 2 0xA0 0xBF)
      else if 0xE1 ≤ b ∧ b ≤ 0xEC then some (.more 2 0x80 0xBF)
      else if b = 0xED then some (.more 2 0x80 0x9F)
      else if 0xEE ≤ b ∧ b ≤ 0xEF then some (.more 2 0x80 0xBF)
      else if b = 0xF0 then some (.more 3 0x90 0xBF)
      else if 0xF1 ≤ b ∧ b ≤ 0xF3 then some (.more 3 0x80 0xBF)
      else if b = 0xF4 then some (.more 3 0x80 0x8F)
      else Option.none
  | .more n lo hi =>
      if lo ≤ b ∧ b ≤ hi then
        some (if n ≤ 1 then .none else .more (n - 1) 0x80 0xBF)
      else Option.none

/-- The requirement rejects an out-of-range continuation byte — the statement a
transcription whose fallback read as `Utf8Need.none` cannot prove. -/
theorem step_rejects_cont : Utf8Need.step (.more 1 0x80 0xBF) 0x22 = Option.none := by
  decide

/-- The requirement rejects a byte no character starts with, on the same terms. -/
theorem step_rejects_lead : Utf8Need.step .none 0x80 = Option.none := by
  decide

/-- Why a block scan stopped short.  The escape *contents* are not here: `\u` digit
and surrogate validation belongs to the string stage, which the parser still runs. -/
inductive BodyStop where
  | ended
  | control
  | badUtf8
deriving DecidableEq, Repr

/-- A refusal and the carrier position that raised it. -/
abbrev Refusal := BodyStop × Nat

/-- The bytes a body may skip without visiting the byte rule: plain ASCII, not a
quote, not a backslash, reached with no run and no sequence outstanding.  **One**
predicate, read by both the lane fold and the byte rule, so the mask and the machine
cannot disagree about what is content.  A content lane leaves the state *unchanged*,
which is why skipping it costs nothing to prove. -/
def IsContentLane (st : BodyState) (b : UInt8) : Bool :=
  st.inside && !st.oddRun && decide (st.utf8 = Utf8Need.none) &&
    !(IsQuoteB b) && !(IsBackslashB b) && decide (0x20 ≤ b) && decide (b < 0x80)

/-- One byte of the body: it continues in a state, it closes the string, or it is
refused.  The order is the scalar scanner's: an outstanding sequence is consulted
first (a continuation byte is the only byte it can accept, and `\` and `"` are
ASCII, so a quote inside a sequence is `badUtf8`, not a delimiter), then an odd run
makes the byte escaped content, then the quote closes or opens, then a backslash
starts a run, then the body's own refusals. -/
inductive BodyStep where
  | cont (st : BodyState)
  | closed
  | refused (stop : BodyStop)

/-- One byte through the byte rule. -/
def bodyStep (st : BodyState) (b : UInt8) : BodyStep :=
  if st.utf8 ≠ Utf8Need.none then
    match st.utf8.step b with
    | some u => .cont { st with utf8 := u }
    | none => .refused .badUtf8
  else if st.oddRun then .cont { st with oddRun := false }
  else if IsQuoteB b then
    if st.inside then .closed
    else .cont { st with inside := true, oddRun := false }
  else if IsBackslashB b then .cont { st with oddRun := st.inside }
  else if st.inside && decide (b < 0x20) then .refused .control
  else if st.inside then
    match Utf8Need.step .none b with
    | some u => .cont { st with utf8 := u }
    | none => .refused .badUtf8
  else .cont st

/-! ### A character's bytes

`Utf8Need` is not a recursive type — its `more` constructor carries a count — so
`utf8Rest`'s recursion is on that count, which the helper below takes as its own
argument.  The public equation set is the requirement's: `none` and `more 0` owe
nothing, and `more (n+1)` owes one byte in `[lo, hi]` and then `more n`.
-/

/-- The count-drawn recursion `utf8Rest` delegates to: structural on `n`, with `0` as
the base case, so the `n + 1 → n` step is the recursor's own. -/
private def utf8Follows : Nat → UInt8 → UInt8 → Bytes → Option Nat
  | 0, _, _, _ => some 0
  | n + 1, lo, hi, b =>
      match b[0]? with
      | none => none
      | some c =>
          if lo ≤ c ∧ c ≤ hi then (utf8Follows n 0x80 0xBF (b.drop 1)).map (· + 1)
          else none

/-- The continuation bytes still owed, `none` if the input ends or a byte fails the
requirement.  `more 0 _ _` is the total case that well-formed states never reach.

The recursion is **structural on the count, which is why the count is a drawn
argument**: `Utf8Need` is not a recursive type, so it has no recursor and a call that
rebuilds `more n` is not seen to decrease.  `utf8Rest` therefore keeps the three arms
and delegates the `more` arm to the private `utf8Follows`, whose first argument is the
count; same type, same values, same equations, and **no `termination_by`**, so it
still computes definitionally — which `utf8Len_iff` below depends on.  A well-founded
recursion would lose that computation, and carrying a `Fin 4` count in the type would
remove the total `more 0` case `WellFormed` is stated against. -/
def utf8Rest : Utf8Need → Bytes → Option Nat
  | .none, _ => some 0
  | .more 0 _ _, _ => some 0
  | .more n lo hi, b => utf8Follows n lo hi b

/-- The bytes one character occupies: one lead byte plus the requirement it leaves.
Defined after `utf8Rest`, which it applies to the remainder. -/
def utf8Len (u : Utf8Need) (b : Bytes) : Option Nat :=
  match b[0]? with
  | none => none
  | some c =>
      match u.step c with
      | none => none
      | some u' => (utf8Rest u' (b.drop 1)).map (· + 1)

/-! ### Supporting lemmas

`utf8Len` reads the carrier at an index rather than by `cons`, so the two claims
about it are proved through the shapes a `cons` chain has: the byte at index zero,
the suffix after it, and the requirement's own count.
-/

/-- A byte string whose first byte is `c` is that byte followed by its drop: the
shape both `utf8Len` readbacks start from. -/
private theorem eq_cons_drop_one {bs : Bytes} {c : UInt8} (h : bs[0]? = some c) :
    bs = c +: bs.drop 1 := by
  rcases ByteString.eq_empty_or_cons bs with he | ⟨b, rest, rfl⟩
  · rw [he, ByteString.getElem?_empty] at h
    exact absurd h (by simp)
  · rw [ByteString.getElem?_cons_zero] at h
    have hcb : c = b := (Option.some.inj h).symm
    subst hcb
    rw [ByteString.drop_succ_cons, ByteString.drop_zero]

/-- The continuation bytes a requirement still owes, as the carrier's own cons
chain: `Utf8Tail (.more (n+1) lo hi) bs rest` holds when the head of `bs` is in
`[lo, hi]` and the rest of `bs` carries the remaining `n` bytes, while the two zero
cases end the chain at `rest = bs`.  This is `utf8Rest`'s graph, in the shape the
character constructors are stated over. -/
private inductive Utf8Tail : Utf8Need → Bytes → Bytes → Prop where
  | none (bs : Bytes) : Utf8Tail .none bs bs
  | zero {lo hi : UInt8} (bs : Bytes) : Utf8Tail (.more 0 lo hi) bs bs
  | more {n : Nat} {lo hi b : UInt8} {bs rest : Bytes} (hlo : lo ≤ b) (hhi : b ≤ hi)
      (h : Utf8Tail (.more n 0x80 0xBF) bs rest) :
      Utf8Tail (.more (n + 1) lo hi) (b +: bs) rest

/-- The number of bytes a requirement consumes. -/
private def utf8Count : Utf8Need → Nat
  | .none => 0
  | .more n _ _ => n

/-- A tail consumes exactly its requirement's count. -/
private theorem Utf8Tail.length_eq {u : Utf8Need} {bs rest : Bytes} (h : Utf8Tail u bs rest) :
    bs.length = rest.length + utf8Count u := by
  induction h with
  | none bs =>
      show bs.length = bs.length + 0
      omega
  | zero bs =>
      show bs.length = bs.length + 0
      omega
  | more hlo hhi h ih =>
      rw [ByteString.length_cons, ih]
      simp only [utf8Count]
      omega

/-- The total requirement consumes nothing. -/
private theorem Utf8Tail.zero_eq {lo hi : UInt8} {bs rest : Bytes}
    (h : Utf8Tail (.more 0 lo hi) bs rest) : rest = bs := by
  cases h
  rfl

/-- One step of a non-empty requirement, inverted: the byte it consumes and the
requirement it leaves. -/
private theorem Utf8Tail.succ_eq {n : Nat} {lo hi : UInt8} {bs rest : Bytes}
    (h : Utf8Tail (.more (n + 1) lo hi) bs rest) :
    ∃ (b : UInt8) (bs' : Bytes), lo ≤ b ∧ b ≤ hi ∧ bs = b +: bs' ∧
      Utf8Tail (.more n 0x80 0xBF) bs' rest := by
  cases h with
  | more hlo hhi ht => exact ⟨_, _, hlo, hhi, rfl, ht⟩

/-- `utf8Rest` at a requirement, in the helper's own terms. -/
private theorem utf8Rest_more (n : Nat) (lo hi : UInt8) (bs : Bytes) :
    utf8Rest (.more n lo hi) bs = utf8Follows n lo hi bs := by
  cases n <;> rfl

/-- The empty continuation count consumes nothing. -/
private theorem utf8Follows_zero (lo hi : UInt8) (bs : Bytes) :
    utf8Follows 0 lo hi bs = some 0 := rfl

/-- One continuation byte in range, then the rest of the requirement. -/
private theorem utf8Follows_cons {n : Nat} {lo hi b : UInt8} {bs : Bytes}
    (hlo : lo ≤ b) (hhi : b ≤ hi) :
    utf8Follows (n + 1) lo hi (b +: bs) = (utf8Follows n 0x80 0xBF bs).map (· + 1) := by
  have hcond : lo ≤ b ∧ b ≤ hi := ⟨hlo, hhi⟩
  simp only [utf8Follows, ByteString.getElem?_cons_zero, ByteString.drop_succ_cons,
    ByteString.drop_zero, ite_eq_left hcond]

/-- A continuation byte out of range, or the end of the input, ends the
requirement. -/
private theorem utf8Follows_refuses {n : Nat} {lo hi b : UInt8} {bs : Bytes}
    (h : ¬ (lo ≤ b ∧ b ≤ hi)) :
    utf8Follows (n + 1) lo hi (b +: bs) = Option.none := by
  simp only [utf8Follows, ByteString.getElem?_cons_zero, ByteString.drop_succ_cons,
    ByteString.drop_zero, ite_eq_right h]

private theorem utf8Follows_end (n : Nat) (lo hi : UInt8) :
    utf8Follows (n + 1) lo hi (ByteString.empty : Bytes) = Option.none := by
  simp only [utf8Follows, ByteString.getElem?_empty]

/-- `utf8Rest`'s graph: a successful run leaves a carrier in which the requirement's
bytes are consumed, and the count is exactly what was consumed.  The induction is on
the requirement's count, which is the recursion's own argument. -/
private theorem utf8Follows_graph : ∀ (n : Nat) (lo hi : UInt8) (bs : Bytes) (k : Nat),
    utf8Follows n lo hi bs = some k →
      ∃ rest, Utf8Tail (.more n lo hi) bs rest ∧ bs.length = rest.length + k := by
  intro n
  induction n with
  | zero =>
      intro lo hi bs k h
      have hk : k = 0 := by
        have h' : some 0 = some k := h
        exact (Option.some.inj h').symm
      exact ⟨bs, Utf8Tail.zero bs, by rw [hk]; simp⟩
  | succ n ih =>
      intro lo hi bs k h
      rcases ByteString.eq_empty_or_cons bs with he | ⟨b, bs', rfl⟩
      · rw [he, utf8Follows_end] at h
        exact absurd h (by simp)
      · by_cases hcond : lo ≤ b ∧ b ≤ hi
        · rw [utf8Follows_cons hcond.1 hcond.2] at h
          obtain ⟨k', hk', hk⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rest, htail, hlen⟩ := ih 0x80 0xBF bs' k' hk'
          refine ⟨rest, Utf8Tail.more hcond.1 hcond.2 htail, ?_⟩
          rw [ByteString.length_cons, hlen]
          omega
        · rw [utf8Follows_refuses hcond] at h
          exact absurd h (by simp)

private theorem utf8Tail_of_rest (u : Utf8Need) (bs : Bytes) (k : Nat)
    (h : utf8Rest u bs = some k) :
    ∃ rest, Utf8Tail u bs rest ∧ bs.length = rest.length + k := by
  cases u with
  | none =>
      simp only [utf8Rest] at h
      have hk : k = 0 := (Option.some.inj h).symm
      exact ⟨bs, Utf8Tail.none bs, by rw [hk]; simp⟩
  | more n lo hi =>
      rw [utf8Rest_more] at h
      exact utf8Follows_graph n lo hi bs k h

/-- A lead byte's class and the step equation it induces, in the direction
`utf8Len_iff`'s accepting half needs: the nine classes of `Utf8Char`'s constructors. -/
private theorem step_none_ascii {b : UInt8} (hb : b < 0x80) :
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

private theorem step_none_three₀ {b : UInt8} (h0 : b = 0xE0) :
    Utf8Need.step .none b = some (.more 2 0xA0 0xBF) := by
  subst h0
  decide

private theorem step_none_three₁ {b : UInt8} (h0 : 0xE1 ≤ b) (h1 : b ≤ 0xEC) :
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
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_three₂ {b : UInt8} (h0 : b = 0xED) :
    Utf8Need.step .none b = some (.more 2 0x80 0x9F) := by
  subst h0
  decide

private theorem step_none_three₃ {b : UInt8} (h0 : 0xEE ≤ b) (h1 : b ≤ 0xEF) :
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
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne1 : ¬ (0xE1 ≤ b ∧ b ≤ 0xEC) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne2 : ¬ b = 0xED := by
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_right hne1,
    ite_eq_right hne2, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_four₀ {b : UInt8} (h0 : b = 0xF0) :
    Utf8Need.step .none b = some (.more 3 0x90 0xBF) := by
  subst h0
  decide

private theorem step_none_four₁ {b : UInt8} (h0 : 0xF1 ≤ b) (h1 : b ≤ 0xF3) :
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
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne1 : ¬ (0xE1 ≤ b ∧ b ≤ 0xEC) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne2 : ¬ b = 0xED := by
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  have hne3 : ¬ (0xEE ≤ b ∧ b ≤ 0xEF) := by
    intro hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hc h0
    omega
  have hne4 : ¬ b = 0xF0 := by
    intro hc
    subst hc
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0
    omega
  simp only [Utf8Need.step]
  rw [ite_eq_right hlt, ite_eq_right hne, ite_eq_right hne0, ite_eq_right hne1,
    ite_eq_right hne2, ite_eq_right hne3, ite_eq_right hne4, ite_eq_left ⟨h0, h1⟩]

private theorem step_none_four₂ {b : UInt8} (h0 : b = 0xF4) :
    Utf8Need.step .none b = some (.more 3 0x80 0x8F) := by
  subst h0
  decide

/-- One byte through an outstanding requirement leaves a well-formed one: a
continuation clears it, and a further byte of a longer sequence leaves a count that
is still one to three. -/
private theorem step_wellFormed {u : Utf8Need} (hu : u.WellFormed) {b : UInt8}
    {u' : Utf8Need} (h : Utf8Need.step u b = some u') : u'.WellFormed := by
  cases u with
  | none =>
      simp only [Utf8Need.step] at h
      repeat' split at h
      · injection h with hh
        subst hh
        trivial
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · injection h with hh
        subst hh
        exact ⟨by decide, by decide⟩
      · exact absurd h (by simp)
  | more n lo hi =>
      obtain ⟨hn0, hn3⟩ := hu
      simp only [Utf8Need.step] at h
      split at h
      · split at h
        · injection h with hh
          subst hh
          trivial
        · injection h with hh
          subst hh
          exact ⟨by omega, by omega⟩
      · exact absurd h (by simp)

/-- `utf8Len`'s computation at a lead byte: the byte, the requirement it leaves, and
the continuation count. -/
private theorem utf8Len_cons {c : UInt8} {u : Utf8Need} {bs : Bytes}
    (h : Utf8Need.step .none c = some u) :
    utf8Len .none (c +: bs) = (utf8Rest u bs).map (· + 1) := by
  simp only [utf8Len, ByteString.getElem?_cons_zero, h, ByteString.drop_succ_cons,
    ByteString.drop_zero]

/-- The accepting half of `utf8Len_iff`: a character's bytes are read by the
requirement, one lead byte's class at a time. -/
private theorem utf8Len_of_char {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    utf8Len .none b = some (b.length - rest.length) := by
  induction h with
  | one hb =>
      rw [utf8Len_cons (step_none_ascii hb), utf8Rest]
      simp only [Option.map_some]
      rw [ByteString.length_cons]
      congr 1
      omega
  | two h0 h0' h1 h1' =>
      rw [utf8Len_cons (step_none_two h0 h0'), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons]
      congr 1
      omega
  | three₀ h1 h1' h2 h2' =>
      rw [utf8Len_cons (step_none_three₀ rfl), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons]
      congr 1
      omega
  | three₁ h0 h0' h1 h1' h2 h2' =>
      rw [utf8Len_cons (step_none_three₁ h0 h0'), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons]
      congr 1
      omega
  | three₂ h1 h1' h2 h2' =>
      rw [utf8Len_cons (step_none_three₂ rfl), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons]
      congr 1
      omega
  | three₃ h0 h0' h1 h1' h2 h2' =>
      rw [utf8Len_cons (step_none_three₃ h0 h0'), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons]
      congr 1
      omega
  | four₀ h1 h1' h2 h2' h3 h3' =>
      rw [utf8Len_cons (step_none_four₀ rfl), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_cons h3 h3', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons]
      congr 1
      omega
  | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
      rw [utf8Len_cons (step_none_four₁ h0 h0'), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_cons h3 h3', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons]
      congr 1
      omega
  | four₂ h1 h1' h2 h2' h3 h3' =>
      rw [utf8Len_cons (step_none_four₂ rfl), utf8Rest_more, utf8Follows_cons h1 h1',
        utf8Follows_cons h2 h2', utf8Follows_cons h3 h3', utf8Follows_zero]
      simp only [Option.map_some]
      rw [ByteString.length_cons, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons]
      congr 1
      omega

/-- The lead-byte half of `utf8Len_iff`'s refusing direction: the nine classes of
`Utf8Char`'s constructors, each read off the step equation and the tail's graph. -/
private theorem utf8Char_of_lead {b : Bytes} {c : UInt8} {u : Utf8Need} {k : Nat}
    (hb : b[0]? = some c) (hu : Utf8Need.step .none c = some u)
    (hk : utf8Rest u (b.drop 1) = some k) :
    ∃ (c' : Nat) (rest : Bytes), Utf8Char b c' rest ∧ b.length = rest.length + (k + 1) := by
  have hbc : b = c +: b.drop 1 := eq_cons_drop_one hb
  obtain ⟨rest, htail, hlen⟩ := utf8Tail_of_rest u (b.drop 1) k hk
  have hkm : k = utf8Count u := by
    have := Utf8Tail.length_eq htail
    omega
  simp only [Utf8Need.step] at hu
  repeat' split at hu
  · -- a byte below 0x80 is one ASCII character
    rename_i hlt
    cases hu
    have hk : k = 0 := by simpa [utf8Count] using hkm
    refine ⟨c.toNat, b.drop 1, ?_, ?_⟩
    · rw [hbc]; exact Utf8Char.one hlt
    · rw [hbc, ByteString.length_cons, ByteString.drop_succ_cons,
        ByteString.drop_zero]
      omega
  · -- 0xC2-0xDF: a two-byte character
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    have hz : rest = bs1 := Utf8Tail.zero_eq ht
    have hk : k = 1 := by simpa [utf8Count] using hkm
    refine ⟨(c.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80), rest, ?_, ?_⟩
    · rw [hbc, hbs, ← hz]; exact Utf8Char.two hcls.1 hcls.2 hl hh
    · rw [hbc, hbs, ByteString.length_cons, ByteString.length_cons, hz]
      omega
  · -- 0xE0: a three-byte character whose first continuation is in A0-BF
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    have hz : rest = bs2 := Utf8Tail.zero_eq ht2
    have hk : k = 2 := by simpa [utf8Count] using hkm
    refine ⟨(b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80), rest, ?_, ?_⟩
    · rw [hbc, hcls, hbs, hbs2, ← hz]
      exact Utf8Char.three₀ hl hh hl2 hh2
    · rw [hbc, hbs, hbs2, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, hz]
      omega
  · -- 0xE1-0xEC
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    have hz : rest = bs2 := Utf8Tail.zero_eq ht2
    have hk : k = 2 := by simpa [utf8Count] using hkm
    refine ⟨(c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80),
      rest, ?_, ?_⟩
    · rw [hbc, hbs, hbs2, ← hz]
      exact Utf8Char.three₁ hcls.1 hcls.2 hl hh hl2 hh2
    · rw [hbc, hbs, hbs2, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, hz]
      omega
  · -- 0xED
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    have hz : rest = bs2 := Utf8Tail.zero_eq ht2
    have hk : k = 2 := by simpa [utf8Count] using hkm
    refine ⟨0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80), rest, ?_, ?_⟩
    · rw [hbc, hcls, hbs, hbs2, ← hz]
      exact Utf8Char.three₂ hl hh hl2 hh2
    · rw [hbc, hbs, hbs2, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, hz]
      omega
  · -- 0xEE-0xEF
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    have hz : rest = bs2 := Utf8Tail.zero_eq ht2
    have hk : k = 2 := by simpa [utf8Count] using hkm
    refine ⟨(c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80),
      rest, ?_, ?_⟩
    · rw [hbc, hbs, hbs2, ← hz]
      exact Utf8Char.three₃ hcls.1 hcls.2 hl hh hl2 hh2
    · rw [hbc, hbs, hbs2, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, hz]
      omega
  · -- 0xF0
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    obtain ⟨b3, bs3, hl3, hh3, hbs3, ht3⟩ := Utf8Tail.succ_eq ht2
    have hz : rest = bs3 := Utf8Tail.zero_eq ht3
    have hk : k = 3 := by simpa [utf8Count] using hkm
    refine ⟨(b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80),
      rest, ?_, ?_⟩
    · rw [hbc, hcls, hbs, hbs2, hbs3, ← hz]
      exact Utf8Char.four₀ hl hh hl2 hh2 hl3 hh3
    · rw [hbc, hbs, hbs2, hbs3, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, ByteString.length_cons, hz]
      omega
  · -- 0xF1-0xF3
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    obtain ⟨b3, bs3, hl3, hh3, hbs3, ht3⟩ := Utf8Tail.succ_eq ht2
    have hz : rest = bs3 := Utf8Tail.zero_eq ht3
    have hk : k = 3 := by simpa [utf8Count] using hkm
    refine ⟨(c.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
      (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80), rest, ?_, ?_⟩
    · rw [hbc, hbs, hbs2, hbs3, ← hz]
      exact Utf8Char.four₁ hcls.1 hcls.2 hl hh hl2 hh2 hl3 hh3
    · rw [hbc, hbs, hbs2, hbs3, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, ByteString.length_cons, hz]
      omega
  · -- 0xF4
    rename_i hcls
    cases hu
    obtain ⟨b1, bs1, hl, hh, hbs, ht⟩ := Utf8Tail.succ_eq htail
    obtain ⟨b2, bs2, hl2, hh2, hbs2, ht2⟩ := Utf8Tail.succ_eq ht
    obtain ⟨b3, bs3, hl3, hh3, hbs3, ht3⟩ := Utf8Tail.succ_eq ht2
    have hz : rest = bs3 := Utf8Tail.zero_eq ht3
    have hk : k = 3 := by simpa [utf8Count] using hkm
    refine ⟨0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
      (b3.toNat - 0x80), rest, ?_, ?_⟩
    · rw [hbc, hcls, hbs, hbs2, hbs3, ← hz]
      exact Utf8Char.four₂ hl hh hl2 hh2 hl3 hh3
    · rw [hbc, hbs, hbs2, hbs3, ByteString.length_cons, ByteString.length_cons,
        ByteString.length_cons, ByteString.length_cons, hz]
      omega
  · -- no lead byte at all
    exact absurd hu (by simp)

/-- `utf8Len`'s computation at a lead byte: the byte's class and the requirement it
leaves, read out of the count and turned into the character. -/
private theorem utf8Len_cons_char {c : UInt8} {bs : Bytes} {n : Nat}
    (h : utf8Len .none (c +: bs) = some n) :
    ∃ (c' : Nat) (rest : Bytes), Utf8Char (c +: bs) c' rest ∧
      (c +: bs).length = rest.length + n := by
  simp only [utf8Len, ByteString.getElem?_cons_zero, ByteString.drop_succ_cons,
    ByteString.drop_zero] at h
  cases hstep : Utf8Need.step .none c with
  | none =>
      simp only [hstep] at h
      exact absurd h (by simp)
  | some u =>
      simp only [hstep] at h
      cases hk : utf8Rest u bs with
      | none =>
          simp only [hk] at h
          exact absurd h (by simp)
      | some k =>
          simp only [hk, Option.map_some, Option.some.injEq] at h
          obtain ⟨c', rest, hchar, hlen⟩ :=
            utf8Char_of_lead (ByteString.getElem?_cons_zero c bs) hstep hk
          exact ⟨c', rest, hchar, by rw [h.symm]; exact hlen⟩

/-- The refusing half of `utf8Len_iff`: a count that `utf8Len` reports is a
character's byte length. -/
private theorem utf8char_of_len {b : Bytes} {n : Nat} (h : utf8Len .none b = some n) :
    ∃ (c' : Nat) (rest : Bytes), Utf8Char b c' rest ∧ b.length = rest.length + n := by
  rcases ByteString.eq_empty_or_cons b with he | ⟨c, bs, rfl⟩
  · rw [he] at h
    simp only [utf8Len, ByteString.getElem?_empty] at h
    exact absurd h (by simp)
  · obtain ⟨c', rest, hchar, hlen⟩ := utf8Len_cons_char h
    exact ⟨c', rest, hchar, hlen⟩

/-! ### The two claims about `utf8Len` -/

theorem utf8Len_iff (b : Bytes) (n : Nat) :
    utf8Len .none b = some n ↔
      ∃ (c : Nat) (rest : Bytes), Utf8Char b c rest ∧ b.length = rest.length + n := by
  constructor
  · intro h
    exact utf8char_of_len h
  · rintro ⟨c, rest, hchar, hlen⟩
    rw [utf8Len_of_char hchar]
    congr 1
    omega

/-- One character's byte length is its code point's class, one to four bytes: the
advance is bounded whatever the input, which is what makes a truncated sequence a
carried state rather than an unbounded obligation. -/
theorem utf8Char_length {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    b.length = rest.length +
      (if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4) := by
  induction h with
  | one hb =>
      simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat] at hb
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | two h0 h0' h1 h1' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' h1 h1'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | three₀ h1 h1' h2 h2' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h1' h2 h2'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | three₁ h0 h0' h1 h1' h2 h2' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' h1 h1' h2 h2'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | three₂ h1 h1' h2 h2' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h1' h2 h2'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | three₃ h0 h0' h1 h1' h2 h2' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' h1 h1' h2 h2'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | four₀ h1 h1' h2 h2' h3 h3' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h1' h2 h2' h3 h3'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h0' h1 h1' h2 h2' h3 h3'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega
  | four₂ h1 h1' h2 h2' h3 h3' =>
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h1' h2 h2' h3 h3'
      simp only [ByteString.length_cons]
      repeat' split
      all_goals omega

/-! ### The carry's invariants -/

theorem BodyState.init_wellFormed : BodyState.init.WellFormed :=
  ⟨trivial, by simp [BodyState.init], by simp [BodyState.init]⟩

theorem BodyState.body_wellFormed : BodyState.body.WellFormed :=
  ⟨trivial, by simp [BodyState.body], by simp [BodyState.body]⟩

/-- Every byte the rule continues leaves a well-formed state: the UTF-8
requirement counts one to three while it is outstanding, an odd run only ever
exists inside the body, and a run never overlaps a sequence. -/
theorem bodyStep_wellFormed {st : BodyState} (h : st.WellFormed) {b : UInt8} {st' : BodyState}
    (h' : bodyStep st b = .cont st') : st'.WellFormed := by
  obtain ⟨hwf, hin, hrun⟩ := h
  unfold bodyStep at h'
  by_cases hseq : st.utf8 ≠ Utf8Need.none
  · cases hstep : st.utf8.step b with
    | none =>
        simp only [ite_eq_left hseq, hstep] at h'
        cases h'
    | some u =>
        simp only [ite_eq_left hseq, hstep] at h'
        cases h'
        exact ⟨step_wellFormed hwf hstep, hin, fun ho => absurd (hrun ho) hseq⟩
  · have hnone : st.utf8 = Utf8Need.none := by simpa using hseq
    simp only [ite_eq_right hseq] at h'
    by_cases hodd : st.oddRun = true
    · simp only [hodd] at h'
      cases h'
      exact ⟨hwf, by simp, by simp⟩
    · simp only [hodd] at h'
      by_cases hq : IsQuoteB b = true
      · simp only [hq] at h'
        by_cases hins : st.inside = true
        · simp only [hins] at h'
          cases h'
        · simp only [hins] at h'
          cases h'
          exact ⟨hwf, by simp, by simp⟩
      · simp only [hq] at h'
        by_cases hbs : IsBackslashB b = true
        · simp only [hbs] at h'
          cases h'
          exact ⟨hwf, by simp, fun _ => hnone⟩
        · simp only [hbs] at h'
          by_cases hctl : (st.inside && decide (b < 0x20)) = true
          · simp only [hctl] at h'
            cases h'
          · simp only [hctl] at h'
            by_cases hins : st.inside = true
            · simp only [hins] at h'
              cases hstep : Utf8Need.step .none b with
              | none =>
                  simp only [hstep] at h'
                  cases h'
              | some u =>
                  simp only [hstep] at h'
                  cases h'
                  exact ⟨step_wellFormed (u := Utf8Need.none) trivial hstep, by simp,
                    by simp⟩
            · simp only [hins] at h'
              cases h'
              exact ⟨hwf, hin, hrun⟩

end LeanLLVM.JSON
