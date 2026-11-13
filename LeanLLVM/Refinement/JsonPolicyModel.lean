/-
The character-policy scan's transition, its equivalence with the reference's
body scan, and the backward pass its block composition relies on.

`probes/json/route/policy.c` computes the answer `policyRefusal`
(`LeanLLVM/JsonKernelDomain.lean`) states, and its header says what that means:
`policy_step` is `scanCharsAt`'s branch structure — the same accept set, the same
lookahead, and the same order in which a refusal is raised, with the same reason.
This module turns that sentence into a theorem.

## The model, beside the reference

The reference's transition is `scanCharsFrom` (`LeanLLVM/JSON/Scan.lean`): the
body scan over the carrier, one character per step, with `off` the position it
labels the current byte with.  `policyStep` is the emission's transition, written
at the byte the emission reads — the first byte of the suffix `bs.drop i` and its
lookahead — and it returns the two things the emission's `pstep` carries: the
class the position itself raises (`self`) and the position a scan continues at
(`next`).  The two transitions are stated side by side in the module's own
branch order, and `policyStep_ref` proves every branch of one is the other.

The one spelling the model does not copy is the hex combination: the emission
writes `(a << 12) | (b << 8) | (c << 4) | d` and this module writes the sum
`a * 0x1000 + b * 0x100 + c * 0x10 + d`, which is `Hex4`'s own formula.  Each
`policyHexVal` result is at most `15` (`hexVal_le`), so the two spellings are the
same number; the model takes the reference's spelling because the equivalence
theorem is stated against `Hex4`, and the emission's spelling buys nothing a
proof can read.  Everything else — the accept sets, the lookahead, the refusal
order and the reason each branch names — is the emission's.

## The walk, and why it is a function of its start

Every branch that continues returns a position `> i` and at most `bs.size`, so a
walk from `i` ends within `bs.size - i` steps, and the emission's backward pass
(`cls[i]` filled from `cls[next]`) is the same answer as a forward walk:
`policyClass_backward` states it.  That is the property the block pass relies on.

## What is here, and what is not yet here

Here: the emission's transition (~`policyStep`~, `policyStep`) at its own byte and
lookahead, with the emission's branch order and the reason each branch names; its
three-valued class; the screen's shape; the reference's reading of a scan
(`refClass`) and the suffix decomposition its equations are stated over
(`suffix_some`, `suffix_ge`, `suffix_empty`, `suffix_len_lt`); and the reference's
own equations read at the lead ranges the model tests (`scanCharsFrom_3b`,
`scanCharsFrom_3b_bad`, `scanCharsFrom_3b_ended`, and the four-byte triple), so
that the equivalence proof's per-lead dispatch is already done.

Not yet here: the equivalence theorem itself — `policyStep`'s branches against
the reference's, one step at a time — and the walk and backward-fill theorems
that read it.  The step equivalence is the remaining work; it is a case analysis
over the model's branches, and the lemmas above are its premises.  The module
therefore proves nothing about agreement yet, and the ledger records the unit as
modelled, not as proved.  The emission's own body is also outside the modelled
fragment (`switch`, `insertvalue`/`extractvalue` and an anonymous-struct return
for `policy_step`), which is the second open piece and is recorded in
`docs/contract.md`. -/

import LeanLLVM.JSON.Scan

namespace LeanLLVM.Refinement.JsonPolicyModel

open LeanLLVM.JSON
open ByteString

/-! ### The class a position raises

The emission's three-valued class, `POLICY_NONE` included: `none` is the byte
that raises nothing, and the other two are the policy's two reasons. -/
inductive PClass where
  /-- `.unpairedSurrogate`: a high surrogate not followed by a low one, or a
  lone low surrogate. -/
  | unpaired
  /-- `.noncharacter`: a code point `IsNoncharacter` refuses. -/
  | noncharacter
deriving DecidableEq, Repr

/-- The emission's `pstep`: the class the position itself raises, if any, and the
position a scan continues at, if it continues.  A refusal carries `none` for
`next` and a continuing position carries `none` for `self`; no branch sets both,
which is what makes the `self`-first read of `policy_class_of` lose nothing. -/
structure PStep where
  next : Option Nat
  self : Option PClass
deriving DecidableEq, Repr

/-- `policy_hex` (`policy.c`), written over the carrier's byte: `HexVal`'s three
ranges and the value each range shifts by.  It is `HexVal` definitionally, which
is the bridge the step's `\u` branch reads. -/
def policyHexVal (b : UInt8) : Option Nat :=
  if IsDigitB b then some (b.toNat - 0x30)
  else if decide (0x41 ≤ b) && decide (b ≤ 0x46) then some (b.toNat - 0x37)
  else if decide (0x61 ≤ b) && decide (b ≤ 0x66) then some (b.toNat - 0x57)
  else none

/-- `policy_hex` is `HexVal`. -/
theorem policyHexVal_eq (b : UInt8) : policyHexVal b = HexVal b := rfl

/-- `policy_hex4` over the four bytes it is handed: the four digits or nothing.
The combination is `Hex4`'s own sum; the emission's `<< 12 | << 8 | << 4 |` is
the same number because each digit is at most `15`. -/
def policyHex4 (h0 h1 h2 h3 : UInt8) : Option Nat :=
  match policyHexVal h0, policyHexVal h1, policyHexVal h2, policyHexVal h3 with
  | some a, some b, some c, some d => some (a * 0x1000 + b * 0x100 + c * 0x10 + d)
  | _, _, _, _ => none

/-- `policy_hex4` is `Hex4`. -/
theorem policyHex4_eq (h0 h1 h2 h3 : UInt8) :
    policyHex4 h0 h1 h2 h3 = Hex4 h0 h1 h2 h3 := rfl

/-! ### The step

`policy.c`'s `policy_step`, branch for branch.  The suffix `bs.drop i` is the
emission's `b + i`; `s[k]?` is its `b[i + k]`, and `n` is `bs.size`, so each
`i + k >= n` test the emission writes is the missing lookup `s[k]? = none`.  The
order is the emission's: the quote, the escape, the ASCII range, the two- and
three- and four-byte forms, and inside the escape the four hex digits, the high
surrogate, the second escape and the low surrogate — each refusal raised at the
branch the emission raises it at. -/
def policyStep (bs : Bytes) (i : Nat) : PStep :=
  let s := bs.drop i
  match s[0]? with
  | none => ⟨none, none⟩
  | some c =>
    if c = 0x22 then ⟨none, none⟩
    else if c = 0x5C then
      match s[1]? with
      | none => ⟨none, none⟩
      | some e =>
        match EscVal e with
        | some _ => ⟨some (i + 2), none⟩
        | none =>
          if e = 0x75 then
            match s[2]?, s[3]?, s[4]?, s[5]? with
            | some h0, some h1, some h2, some h3 =>
              match Hex4 h0 h1 h2 h3 with
              | none => ⟨none, none⟩
              | some cv =>
                if 0xD800 ≤ cv ∧ cv ≤ 0xDBFF then
                  match s[6]?, s[7]?, s[8]?, s[9]?, s[10]?, s[11]? with
                  | some z0, some z1, some l0, some l1, some l2, some l3 =>
                    if z0 = 0x5C ∧ z1 = 0x75 then
                      match Hex4 l0 l1 l2 l3 with
                      | none => ⟨none, none⟩
                      | some lv =>
                        if 0xDC00 ≤ lv ∧ lv ≤ 0xDFFF then
                          if IsNoncharacter
                              (0x10000 + (cv - 0xD800) * 0x400 + (lv - 0xDC00)) then
                            ⟨none, some .noncharacter⟩
                          else ⟨some (i + 12), none⟩
                        else ⟨none, some .unpaired⟩
                    else ⟨none, some .unpaired⟩
                  | _, _, _, _, _, _ => ⟨none, some .unpaired⟩
                else if 0xDC00 ≤ cv ∧ cv ≤ 0xDFFF then ⟨none, some .unpaired⟩
                else if IsNoncharacter cv then ⟨none, some .noncharacter⟩
                else ⟨some (i + 6), none⟩
            | _, _, _, _ => ⟨none, none⟩
          else ⟨none, none⟩
    else if c.toNat < 0x80 then
      if c.toNat < 0x20 then ⟨none, none⟩ else ⟨some (i + 1), none⟩
    else if c.toNat < 0xC2 ∨ 0xF4 < c.toNat then ⟨none, none⟩
    else if c.toNat ≤ 0xDF then
      match s[1]? with
      | none => ⟨none, none⟩
      | some b1 =>
        if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then ⟨some (i + 2), none⟩
        else ⟨none, none⟩
    else if c.toNat ≤ 0xEF then
      match s[1]?, s[2]? with
      | some b1, some b2 =>
        if c = 0xE0 then
          if 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
            if IsNoncharacter ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) then
              ⟨none, some .noncharacter⟩
            else ⟨some (i + 3), none⟩
          else ⟨none, none⟩
        else if c = 0xED then
          if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
            if IsNoncharacter (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) then
              ⟨none, some .noncharacter⟩
            else ⟨some (i + 3), none⟩
          else ⟨none, none⟩
        else
          if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF then
            if IsNoncharacter
                ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                  (b2.toNat - 0x80)) then
              ⟨none, some .noncharacter⟩
            else ⟨some (i + 3), none⟩
          else ⟨none, none⟩
      | _, _ => ⟨none, none⟩
    else
      match s[1]?, s[2]?, s[3]? with
      | some b1, some b2, some b3 =>
        if 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF then
          if c = 0xF0 then
            if 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then
              if IsNoncharacter
                  ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
                    (b3.toNat - 0x80)) then
                ⟨none, some .noncharacter⟩
              else ⟨some (i + 4), none⟩
            else ⟨none, none⟩
          else if c.toNat ≤ 0xF3 then
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF then
              if IsNoncharacter
                  ((c.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
                    (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) then
                ⟨none, some .noncharacter⟩
              else ⟨some (i + 4), none⟩
            else ⟨none, none⟩
          else
            if 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F then
              if IsNoncharacter
                  (0x100000 + (b1.toNat - 0x80) * 0x1000 +
                    (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) then
                ⟨none, some .noncharacter⟩
              else ⟨some (i + 4), none⟩
            else ⟨none, none⟩
        else ⟨none, none⟩
      | _, _, _ => ⟨none, none⟩

/-! ### The walk

`policy_class_of`'s read of the step, iterated: the class at the position itself,
or the class of the position it continues at, or nothing.  `fuel` is the
emission's `cls` array read as a recursion; `policyClass` gives it the vector's
own budget, `bs.size - i`, which is as many steps as a walk from `i` can take. -/
def policyWalk (bs : Bytes) (i : Nat) : Nat → Option (PClass × Nat)
  | 0 => none
  | f + 1 =>
    let s := policyStep bs i
    match s.self with
    | some c => some (c, i)
    | none =>
      match s.next with
      | some j => policyWalk bs j f
      | none => none

/-- The answer a scan starting at `i` reaches: its class and the position that
raises it. -/
def policyClass (bs : Bytes) (i : Nat) : Option (PClass × Nat) :=
  policyWalk bs i (bs.size - i)

/-! ### The reference's reading

`scanCharsFrom off (bs.drop i)` is the reference's body scan from position `i`,
labelled `off`; `refClass` is its policy answer, with the refusal's position read
back into the document.  `d` is the position the scan started at: the label
advances with the position, so `off = i - d` at every position of one scan, and a
refusal at label `o` is at document position `d + o`.  Carrying `d` rather than
the label is what makes an accepted character's continuation the *same* term at
the next position. -/
def refClass (bs : Bytes) (i off d : Nat) : Option (PClass × Nat) :=
  match scanCharsFrom off (bs.drop i) with
  | .error (.unpairedSurrogate o) => some (.unpaired, d + o)
  | .error (.noncharacter o) => some (.noncharacter, d + o)
  | _ => none

/-- A later position in the document starts a cons: the shape every reference
equation is stated over. -/
theorem suffix_some (bs : Bytes) (i k : Nat) {b : UInt8}
    (h : bs[i + k]? = some b) : bs.drop (i + k) = b +: bs.drop (i + k + 1) :=
  ByteString.drop_eq_getElem_cons h

/-- A missing lookup bounds the document. -/
theorem suffix_ge (bs : Bytes) (i k : Nat) (h : bs[i + k]? = none) :
    bs.size ≤ i + k := ge_of_getElem?_eq_none h

/-- A missing lookup is the empty suffix. -/
theorem suffix_empty (bs : Bytes) (i k : Nat) (h : bs[i + k]? = none) :
    bs.drop (i + k) = empty := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_empty]
  exact List.drop_eq_nil_of_le (by rw [toList_length]; exact suffix_ge bs i k h)

theorem size_drop (bs : Bytes) (i : Nat) : (bs.drop i).size = bs.size - i := by
  rw [← length_eq_size, length_drop, length_eq_size]

/-- A short suffix's length: what the `ended` equations are stated with. -/
theorem suffix_len_lt (bs : Bytes) (i k m : Nat) (h : bs[i + m]? = none) (hk : k ≤ m) :
    (bs.drop (i + k)).length < m - k + 1 := by
  rw [length_eq_size, size_drop]
  have := suffix_ge bs i m h
  omega

/-- A byte below `0xFDD0` is no noncharacter. -/
theorem noncharacter_of_lt (c : Nat) (h : c < 0xFDD0) : IsNoncharacter c = false := by
  unfold IsNoncharacter
  have h1 : c < 0x10000 := by omega
  rw [Nat.mod_eq_of_lt h1]
  have h2 : ¬ 0xFDD0 ≤ c := by omega
  have h3 : ¬ c = 0xFFFE := by omega
  have h4 : ¬ c = 0xFFFF := by omega
  simp [h2, h3, h4, decide_eq_false_iff_not]

/-- `UInt8` order, read at the value: the reference's equations are stated either
way, and the model's conditions are at the value. -/
theorem u8le {a b : UInt8} (h : a.toNat ≤ b.toNat) : a ≤ b :=
  UInt8.le_iff_toNat_le.mpr h

/-- A byte equality read at the value: the arithmetic the lead ranges need. -/
theorem toNat_ne_of_ne {a b : UInt8} (h : a ≠ b) : a.toNat ≠ b.toNat :=
  fun hh => h (UInt8.toNat_inj.mp hh)

/-! ### The reference's three- and four-byte equations, at the lead's range

`LeanLLVM/JSON/Scan.lean` states one equation per exact lead range.  The model's
condition on a lead is a range, so these read those equations at the range, and
the disjunction the range leaves is decided here once instead of at every leaf.
The ranges are written at the value (`224 ≤ c.toNat`), because that is the form
`omega` reads; a byte comparison is one `UInt8.le_iff_toNat_le` away. -/

theorem scanCharsFrom_3b_ended (off : Nat) (c : UInt8) (l : Bytes)
    (h0 : 224 ≤ c.toNat) (h1 : c.toNat ≤ 239) (hl : l.length < 2) :
    scanCharsFrom off (c +: l) = .error .ended := by
  by_cases he0 : c = 0xE0
  · subst he0; exact scanCharsFrom_utf8_e0_ended off l hl
  by_cases hed : c = 0xED
  · subst hed; exact scanCharsFrom_utf8_ed_ended off l hl
  have hne0 : c.toNat ≠ 224 := toNat_ne_of_ne he0
  have hned : c.toNat ≠ 237 := toNat_ne_of_ne hed
  by_cases hle : c.toNat ≤ 236
  · exact scanCharsFrom_utf8_e1ec_ended off c l
      (u8le (by show (225 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (236 : Nat); omega)) hl
  · exact scanCharsFrom_utf8_eeef_ended off c l
      (u8le (by show (238 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (239 : Nat); omega)) hl

theorem scanCharsFrom_4b_ended (off : Nat) (c : UInt8) (l : Bytes)
    (h0 : 240 ≤ c.toNat) (h1 : c.toNat ≤ 244) (hl : l.length < 3) :
    scanCharsFrom off (c +: l) = .error .ended := by
  by_cases hf0 : c = 0xF0
  · subst hf0; exact scanCharsFrom_utf8_f0_ended off l hl
  by_cases hf4 : c = 0xF4
  · subst hf4; exact scanCharsFrom_utf8_f4_ended off l hl
  · have hne0 : c.toNat ≠ 240 := toNat_ne_of_ne hf0
    have hne4 : c.toNat ≠ 244 := toNat_ne_of_ne hf4
    exact scanCharsFrom_utf8_f1f3_ended off c l
      (u8le (by show (241 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (243 : Nat); omega)) hl

/-- The three-byte leads' refusal, at the range: the shared continuation test and
the two leads with their own first-half range. -/
theorem scanCharsFrom_3b_bad (off : Nat) (c b1 b2 : UInt8) (rest : Bytes)
    (h0 : 224 ≤ c.toNat) (h1 : c.toNat ≤ 239)
    (h2 : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF))
    (h3 : ¬ (0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF))
    (h4 : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)) :
    scanCharsFrom off (c +: b1 +: b2 +: rest) = .error (.badUTF8 off) := by
  by_cases he0 : c = 0xE0
  · subst he0; exact scanCharsFrom_utf8_e0_bad off b1 b2 rest h3
  by_cases hed : c = 0xED
  · subst hed; exact scanCharsFrom_utf8_ed_bad off b1 b2 rest h4
  have hne0 : c.toNat ≠ 224 := toNat_ne_of_ne he0
  have hned : c.toNat ≠ 237 := toNat_ne_of_ne hed
  by_cases hle : c.toNat ≤ 236
  · exact scanCharsFrom_utf8_e1ec_bad off c b1 b2 rest
      (u8le (by show (225 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (236 : Nat); omega)) h2
  · exact scanCharsFrom_utf8_eeef_bad off c b1 b2 rest
      (u8le (by show (238 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (239 : Nat); omega)) h2

/-- The four-byte leads' refusal, at the range. -/
theorem scanCharsFrom_4b_bad (off : Nat) (c b1 b2 b3 : UInt8) (rest : Bytes)
    (h0 : 240 ≤ c.toNat) (h1 : c.toNat ≤ 244)
    (h2 : ¬ (0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF))
    (h3 : ¬ (0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF))
    (h4 : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF))
    (h5 : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F)) :
    scanCharsFrom off (c +: b1 +: b2 +: b3 +: rest) = .error (.badUTF8 off) := by
  by_cases hf0 : c = 0xF0
  · subst hf0
    exact scanCharsFrom_utf8_f0_bad off b1 b2 b3 rest (by omega)
  by_cases hf4 : c = 0xF4
  · subst hf4
    exact scanCharsFrom_utf8_f4_bad off b1 b2 b3 rest (by omega)
  · have hne0 : c.toNat ≠ 240 := toNat_ne_of_ne hf0
    have hne4 : c.toNat ≠ 244 := toNat_ne_of_ne hf4
    exact scanCharsFrom_utf8_f1f3_bad off c b1 b2 b3 rest
      (u8le (by show (241 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (243 : Nat); omega)) (by omega)

/-- The three-byte accepting equation, at the range: the three leads' formulas are
the one expansion for the lead's own value. -/
theorem scanCharsFrom_3b (off : Nat) (c b1 b2 : UInt8) (rest : Bytes)
    (h0 : 224 ≤ c.toNat) (h1 : c.toNat ≤ 239)
    (hb1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (hb2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)
    (he0 : c = 0xE0 → 0xA0 ≤ b1.toNat) (hed : c = 0xED → b1.toNat ≤ 0x9F) :
    scanCharsFrom off (c +: b1 +: b2 +: rest) =
      scanCons off (off + 3)
        ((c.toNat - 224) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) rest := by
  by_cases he : c = 0xE0
  · subst he
    rw [scanCharsFrom_utf8_e0 off b1 b2 rest (u8le (he0 rfl)) (u8le hb1.2) (u8le hb2.1)
      (u8le hb2.2)]
    rw [show ((0xE0 : UInt8).toNat - 224) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80) = (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80) from by
      show (224 - 224) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80) =
        (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)
      omega]
  by_cases hd : c = 0xED
  · subst hd
    rw [scanCharsFrom_utf8_ed off b1 b2 rest (u8le hb1.1) (u8le (hed rfl)) (u8le hb2.1)
      (u8le hb2.2)]
    rw [show ((0xED : UInt8).toNat - 224) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
          (b2.toNat - 0x80) = 0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80) from by
      show (237 - 224) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80) =
        0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)
      omega]
  have hne0 : c.toNat ≠ 224 := toNat_ne_of_ne he
  have hned : c.toNat ≠ 237 := toNat_ne_of_ne hd
  by_cases hle : c.toNat ≤ 236
  · rw [scanCharsFrom_utf8_e1ec off c b1 b2 rest
      (u8le (by show (225 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (236 : Nat); omega))
      (u8le hb1.1) (u8le hb1.2) (u8le hb2.1) (u8le hb2.2)]
  · rw [scanCharsFrom_utf8_eeef off c b1 b2 rest
      (u8le (by show (238 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (239 : Nat); omega))
      (u8le hb1.1) (u8le hb1.2) (u8le hb2.1) (u8le hb2.2)]

/-- The four-byte accepting equation, at the range. -/
theorem scanCharsFrom_4b (off : Nat) (c b1 b2 b3 : UInt8) (rest : Bytes)
    (h0 : 240 ≤ c.toNat) (h1 : c.toNat ≤ 244)
    (hb1 : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF)
    (hb2 : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF)
    (hb3 : 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF)
    (hf0 : c = 0xF0 → 0x90 ≤ b1.toNat) (hf4 : c = 0xF4 → b1.toNat ≤ 0x8F) :
    scanCharsFrom off (c +: b1 +: b2 +: b3 +: rest) =
      scanCons off (off + 4)
        ((c.toNat - 240) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) rest := by
  by_cases hf : c = 0xF0
  · subst hf
    rw [scanCharsFrom_utf8_f0 off b1 b2 b3 rest (u8le (hf0 rfl)) (u8le hb1.2) (u8le hb2.1)
      (u8le hb2.2) (u8le hb3.1) (u8le hb3.2)]
    rw [show ((0xF0 : UInt8).toNat - 240) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) =
        (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) from by
      show (240 - 240) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) =
        (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)
      omega]
  by_cases h4 : c = 0xF4
  · subst h4
    rw [scanCharsFrom_utf8_f4 off b1 b2 b3 rest (u8le hb1.1) (u8le (hf4 rfl)) (u8le hb2.1)
      (u8le hb2.2) (u8le hb3.1) (u8le hb3.2)]
    rw [show ((0xF4 : UInt8).toNat - 240) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) =
        0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80) from by
      show (244 - 240) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
          (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) =
        0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 +
          (b3.toNat - 0x80)
      omega]
  · have hne0 : c.toNat ≠ 240 := toNat_ne_of_ne hf
    have hne4 : c.toNat ≠ 244 := toNat_ne_of_ne h4
    rw [scanCharsFrom_utf8_f1f3 off c b1 b2 b3 rest
      (u8le (by show (241 : Nat) ≤ c.toNat; omega))
      (u8le (by show c.toNat ≤ (243 : Nat); omega))
      (u8le hb1.1) (u8le hb1.2) (u8le hb2.1) (u8le hb2.2) (u8le hb3.1) (u8le hb3.2)]


end LeanLLVM.Refinement.JsonPolicyModel
