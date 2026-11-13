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
branch order, and `policyStep_spec` proves one step of one is one step of the other.

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

## What is proved, and what is not

Proved: the emission's transition at its own byte and lookahead
(`policyStep`), the reference's reading of a scan (`refClass`) over
`scanCharsFrom`, and the agreement between the two — `policyStep_spec` for one
step, `policyWalk_spec` for a whole walk (`policyClass_refClass` reads it at the
fuel the definition supplies), and `policyClass_backward` for the emission's
backward fill, which is the recurrence `cls[i] = cls[next]` that a pass filling
slots from the buffer's end computes.  The reference's `ended` equations at the
lead ranges, and the byte facts the step proof needs, are here too.

Still open: the body correspondence.  The emission's own body is outside the
modelled LLVM fragment (`switch`, `insertvalue`/`extractvalue` and an
anonymous-struct return for `policy_step`), so this module proves the transition
the emission's body computes, not that the body computes it.  That is a
structural obligation no proof in this fragment can close, and it is recorded in
`docs/contract.md` §7.5. -/

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
  simp [h2, h3, h4]

/-- `UInt8` order, read at the value: the reference's equations are stated either
way, and the model's conditions are at the value. -/
theorem u8le {a b : UInt8} (h : a.toNat ≤ b.toNat) : a ≤ b :=
  UInt8.le_iff_toNat_le.mpr h

/-- A byte equality read at the value: the arithmetic the lead ranges need. -/
theorem toNat_ne_of_ne {a b : UInt8} (h : a ≠ b) : a.toNat ≠ b.toNat :=
  fun hh => h (UInt8.toNat_inj.mp hh)

/-! ### The reference's `ended` equations, at the lead's range

`LeanLLVM/JSON/Scan.lean` states one equation per exact lead range.  The model's
condition on a lead is a range, so these read those equations at the range, and
the disjunction the range leaves is decided here once instead of at every leaf.

Only the `ended` pair is needed.  A full byte shape calls the reference's own
per-lead equation directly — each is stated for exactly the range the branch
tested, so the accept and refuse sides need no range wrapper — while the `ended`
equations are stated over the three- and four-byte leads together and are read
at the range here.  The ranges are written at the value (`224 ≤ c.toNat`),
because that is the form `omega` reads; a byte comparison is one
`UInt8.le_iff_toNat_le` away. -/

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


/-! ### The step's agreement with the reference

`policyStep` and `scanCharsFrom` are written at different levels — the emission's
at its own byte and lookahead, the reference's at the body it is handed — and
`policyStep_spec` proves that one step of each is the same step: the class the
position raises, the position the scan continues at, and nothing when the
emission's step answers nothing.  The proof is a case analysis over the
emission's branches, each discharged by the reference's own equation for that
byte shape.

`StepSpec` is the statement, so that the walk and the fill read it without
repeating the case analysis. -/

/-- A byte's order, strictly: the reference's ground-shape hypotheses are `UInt8`
comparisons and the model's byte tests are written at the value. -/
theorem u8lt {a b : UInt8} (h : a.toNat < b.toNat) : a < b :=
  UInt8.lt_iff_toNat_lt.mpr h

/-- What the reference's own scan says about the step at `i`, as a proposition
about the emission's step value.  `d` is the document position the scan started
at and `off` is the label at `i`, so `d + off = i` at every position of one
scan; a refusal the reference reports at label `o` is at document position
`d + o`.  A continuing step carries the character the reference accepted (`cv`)
and the position it continues at: that is the decomposition the walk rewrites
through, and `IsNoncharacter cv = false` is what `okCons` needs to pass the
character through instead of refusing it. -/
def StepSpec (bs : Bytes) (i off d : Nat) (s : PStep) : Prop :=
  match s.self with
  | some cl => refClass bs i off d = some (cl, i)
  | none =>
    match s.next with
    | some j =>
      i < j ∧ ∃ cv : Nat, IsNoncharacter cv = false ∧
        scanCharsFrom off (bs.drop i) =
          okCons off cv (scanCharsFrom (off + (j - i)) (bs.drop j))
    | none => refClass bs i off d = none

/-- Every escape denotes a code point below the noncharacter block, so an accepted
escape never trips the reference's `okCons`. -/
theorem escVal_lt {e : UInt8} {v : Nat} (h : EscVal e = some v) : v < 0xFDD0 := by
  unfold EscVal at h
  split at h <;> simp_all <;> omega

/-- A missing lookup within a fixed window leaves fewer bytes than the window:
the shape condition the reference's `ended` equations are stated with. -/
theorem drop_len_lt_of_missing (bs : Bytes) (j k n : Nat)
    (h : (bs.drop j)[k]? = none) (hk : k < n) : (bs.drop j).length < n := by
  have hs : (bs.drop j).size ≤ k := ge_of_getElem?_eq_none h
  rw [ByteString.length_eq_size]
  omega

/-- A suffix whose first lookup is missing is empty. -/
theorem drop_empty_of_missing (bs : Bytes) (j : Nat) (h : (bs.drop j)[0]? = none) :
    bs.drop j = empty := by
  have hs : (bs.drop j).size = 0 := by
    have := ge_of_getElem?_eq_none h
    omega
  apply ByteString.eq_empty_of_data_toList
  rw [ByteString.data_toList_drop, List.drop_eq_nil_of_le]
  rw [← ByteString.toList_eq_data_toList, ByteString.toList_length]
  rw [size_drop] at hs
  omega

/-- A lookup in a suffix, read at the suffix's own index: the emission's
`b[i + m + k]` seen through `bs.drop i`. -/
theorem drop_lookup_of (bs : Bytes) (i m k : Nat) {o : Option UInt8}
    (h : (bs.drop i)[m + k]? = o) : (bs.drop (i + m))[k]? = o := by
  have h' : bs[i + (m + k)]? = o := by rw [← ByteString.getElem?_drop]; exact h
  rw [ByteString.getElem?_drop]
  rwa [show i + m + k = i + (m + k) from by omega]

/-- The split a lookup makes: the byte it found, then the rest. -/
theorem cons_of_lookup (bs : Bytes) {k : Nat} {b : UInt8} (h : bs[k]? = some b) :
    bs.drop k = b +: bs.drop (k+1) := ByteString.drop_eq_getElem_cons h

/-- An accepted character contributes nothing to the policy answer: the reference's
`okCons` passes the rest of the scan through unchanged when the character it
accepted is no noncharacter, so the class at one position is the class at the
position it continues at.  This is what makes the walk a function of its start. -/
theorem refClass_cons (bs : Bytes) (i off d cv j noff : Nat)
    (hnc : IsNoncharacter cv = false)
    (h : scanCharsFrom off (bs.drop i) = okCons off cv (scanCharsFrom noff (bs.drop j))) :
    refClass bs i off d = refClass bs j noff d := by
  rw [refClass, h]
  simp [okCons, hnc]
  rw [refClass]
  cases scanCharsFrom noff (bs.drop j) with
  | error e => cases e <;> rfl
  | ok p => rfl

/-- The one-step equivalence.  Every branch of `policyStep` is the reference's own
step at the same byte: a continuing branch decomposes the reference's scan into
the character it accepted and the scan of the suffix the emission continues at,
a refusing branch names the reason the reference names and raises it at the
position the reference labels, and a branch that answers nothing is a step the
reference does not refuse on the character policy's account — the body ends, or
it fails for syntax. -/
theorem policyStep_spec (bs : Bytes) (i off d : Nat) (hdi : d + off = i) :
    StepSpec bs i off d (policyStep bs i) := by
  cases h0 : (bs.drop i)[0]? with
  | none =>
    have h0' : bs[i + 0]? = none := (ByteString.getElem?_drop bs i 0).symm.trans h0
    have hemp : bs.drop i = empty := by simpa using suffix_empty bs i 0 h0'
    have hstep : policyStep bs i = ⟨none, none⟩ := by simp [policyStep, h0]
    have href : scanCharsFrom off (bs.drop i) = .error .ended := by rw [hemp, scanCharsFrom_nil]
    simp only [StepSpec, hstep]; simp [refClass, href]
  | some c =>
    have hcons : bs.drop i = c +: bs.drop (i + 1) := by
      have h := ByteString.drop_eq_getElem_cons (bs := bs.drop i) (i := 0) h0
      rw [ByteString.drop_zero, ByteString.drop_drop] at h
      simpa using h
    by_cases hq : c = 0x22
    · subst hq
      have hstep : policyStep bs i = ⟨none, none⟩ := by simp [policyStep, h0]
      have href : scanCharsFrom off (bs.drop i) = .ok ([], bs.drop (i + 1)) := by
        rw [hcons, scanCharsFrom_quote]
      simp only [StepSpec, hstep]; simp [refClass, href]
    · by_cases hsc : c = 0x5C
      · subst hsc
        cases h1 : (bs.drop i)[1]? with
        | none =>
          have hemp1 : bs.drop (i + 1) = empty := drop_empty_of_missing bs (i+1) (drop_lookup_of bs i 1 0 h1)
          have hstep : policyStep bs i = ⟨none, none⟩ := by simp [policyStep, h0, h1]
          have href : scanCharsFrom off (bs.drop i) = .error .ended := by
            rw [hcons, hemp1, scanCharsFrom_escape_ended]
          simp only [StepSpec, hstep]; simp [refClass, href]
        | some e =>
          have hc2 : bs.drop (i + 1) = e +: bs.drop (i + 2) :=
            cons_of_lookup bs ((ByteString.getElem?_drop bs i 1).symm.trans h1)
          cases hEsc : EscVal e with
          | some v =>
            have hstep : policyStep bs i = ⟨some (i + 2), none⟩ := by
              simp [policyStep, h0, h1, hEsc]
            have href : scanCharsFrom off (bs.drop i) =
                okCons off v (scanCharsFrom (off + 2) (bs.drop (i + 2))) := by
              rw [hcons, hc2, scanCharsFrom_escape off e (bs.drop (i + 2)) v hEsc]
              rfl
            have hnc : IsNoncharacter v = false := noncharacter_of_lt v (escVal_lt hEsc)
            simp only [StepSpec, hstep]
            refine ⟨by omega, v, hnc, ?_⟩
            rw [href, show i + 2 - i = 2 from by omega]
          | none =>
            by_cases he75 : e = 0x75
            · subst he75
              have hu : EscVal (0x75 : UInt8) = none := hEsc
              cases h2 : (bs.drop i)[2]? with
              | none =>
                have hl : (bs.drop (i + 2)).length < 4 :=
                  drop_len_lt_of_missing bs (i+2) 0 4 (drop_lookup_of bs i 2 0 h2) (by omega)
                have hstep : policyStep bs i = ⟨none, none⟩ := by
                  simp [policyStep, h0, h1, hu, h2]
                have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                  rw [hcons, hc2, scanCharsFrom_uchar_ended off (bs.drop (i + 2)) hl]
                simp only [StepSpec, hstep]; simp [refClass, href]
              | some x0 =>
                cases h3 : (bs.drop i)[3]? with
                | none =>
                  have hl : (bs.drop (i + 2)).length < 4 :=
                    drop_len_lt_of_missing bs (i+2) 1 4 (drop_lookup_of bs i 2 1 h3) (by omega)
                  have hstep : policyStep bs i = ⟨none, none⟩ := by
                    simp [policyStep, h0, h1, hu, h2, h3]
                  have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                    rw [hcons, hc2, scanCharsFrom_uchar_ended off (bs.drop (i + 2)) hl]
                  simp only [StepSpec, hstep]; simp [refClass, href]
                | some x1 =>
                  cases h4 : (bs.drop i)[4]? with
                  | none =>
                    have hl : (bs.drop (i + 2)).length < 4 :=
                      drop_len_lt_of_missing bs (i+2) 2 4 (drop_lookup_of bs i 2 2 h4) (by omega)
                    have hstep : policyStep bs i = ⟨none, none⟩ := by
                      simp [policyStep, h0, h1, hu, h2, h3, h4]
                    have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                      rw [hcons, hc2, scanCharsFrom_uchar_ended off (bs.drop (i + 2)) hl]
                    simp only [StepSpec, hstep]; simp [refClass, href]
                  | some x2 =>
                    cases h5 : (bs.drop i)[5]? with
                    | none =>
                      have hl : (bs.drop (i + 2)).length < 4 :=
                        drop_len_lt_of_missing bs (i+2) 3 4 (drop_lookup_of bs i 2 3 h5) (by omega)
                      have hstep : policyStep bs i = ⟨none, none⟩ := by
                        simp [policyStep, h0, h1, hu, h2, h3, h4, h5]
                      have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                        rw [hcons, hc2, scanCharsFrom_uchar_ended off (bs.drop (i + 2)) hl]
                      simp only [StepSpec, hstep]; simp [refClass, href]
                    | some x3 =>
                      have e2 : bs.drop (i + 2) = x0 +: bs.drop (i + 3) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 2).symm.trans h2)
                      have e3 : bs.drop (i + 3) = x1 +: bs.drop (i + 4) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 3).symm.trans h3)
                      have e4 : bs.drop (i + 4) = x2 +: bs.drop (i + 5) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 4).symm.trans h4)
                      have e5 : bs.drop (i + 5) = x3 +: bs.drop (i + 6) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 5).symm.trans h5)
                      cases hHex : Hex4 x0 x1 x2 x3 with
                      | none =>
                        have hstep : policyStep bs i = ⟨none, none⟩ := by
                          simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex]
                        have href : scanCharsFrom off (bs.drop i) =
                            .error (.badEscape (off + 2)) := by
                          rw [hcons, hc2, e2, e3, e4, e5,
                            scanCharsFrom_uchar_badHex off x0 x1 x2 x3 (bs.drop (i + 6)) hHex]
                        simp only [StepSpec, hstep]; simp [refClass, href]
                      | some cv =>
                        by_cases hhi : 0xD800 ≤ cv ∧ cv ≤ 0xDBFF
                        · -- high surrogate: the pair
                          cases h6 : (bs.drop i)[6]? with
                          | none =>
                            have hr : (bs.drop (i + 6)).length < 6 :=
                              drop_len_lt_of_missing bs (i+6) 0 6 (drop_lookup_of bs i 6 0 h6) (by omega)
                            have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                              simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6]
                            have href : scanCharsFrom off (bs.drop i) =
                                .error (.unpairedSurrogate off) := by
                              rw [hcons, hc2, e2, e3, e4, e5,
                                scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                            simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                          | some z0 =>
                            cases h7 : (bs.drop i)[7]? with
                            | none =>
                              have hr : (bs.drop (i + 6)).length < 6 :=
                                drop_len_lt_of_missing bs (i+6) 1 6 (drop_lookup_of bs i 6 1 h7) (by omega)
                              have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7]
                              have href : scanCharsFrom off (bs.drop i) =
                                  .error (.unpairedSurrogate off) := by
                                rw [hcons, hc2, e2, e3, e4, e5,
                                  scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                            | some z1 =>
                              cases h8 : (bs.drop i)[8]? with
                              | none =>
                                have hr : (bs.drop (i + 6)).length < 6 :=
                                  drop_len_lt_of_missing bs (i+6) 2 6 (drop_lookup_of bs i 6 2 h8) (by omega)
                                have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                  simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8]
                                have href : scanCharsFrom off (bs.drop i) =
                                    .error (.unpairedSurrogate off) := by
                                  rw [hcons, hc2, e2, e3, e4, e5,
                                    scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                                simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                              | some l0 =>
                                cases h9 : (bs.drop i)[9]? with
                                | none =>
                                  have hr : (bs.drop (i + 6)).length < 6 :=
                                    drop_len_lt_of_missing bs (i+6) 3 6 (drop_lookup_of bs i 6 3 h9) (by omega)
                                  have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                    simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9]
                                  have href : scanCharsFrom off (bs.drop i) =
                                      .error (.unpairedSurrogate off) := by
                                    rw [hcons, hc2, e2, e3, e4, e5,
                                      scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                                  simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                | some l1 =>
                                  cases h10 : (bs.drop i)[10]? with
                                  | none =>
                                    have hr : (bs.drop (i + 6)).length < 6 :=
                                      drop_len_lt_of_missing bs (i+6) 4 6 (drop_lookup_of bs i 6 4 h10) (by omega)
                                    have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                      simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10]
                                    have href : scanCharsFrom off (bs.drop i) =
                                        .error (.unpairedSurrogate off) := by
                                      rw [hcons, hc2, e2, e3, e4, e5,
                                        scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                                    simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                  | some l2 =>
                                    cases h11 : (bs.drop i)[11]? with
                                    | none =>
                                      have hr : (bs.drop (i + 6)).length < 6 :=
                                        drop_len_lt_of_missing bs (i+6) 5 6 (drop_lookup_of bs i 6 5 h11) (by omega)
                                      have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                        simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11]
                                      have href : scanCharsFrom off (bs.drop i) =
                                          .error (.unpairedSurrogate off) := by
                                        rw [hcons, hc2, e2, e3, e4, e5,
                                          scanCharsFrom_pair_ended off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hhi hr]
                                      simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                    | some l3 =>
                                      have e6 : bs.drop (i + 6) = z0 +: bs.drop (i + 7) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 6).symm.trans h6)
                                      have e7 : bs.drop (i + 7) = z1 +: bs.drop (i + 8) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 7).symm.trans h7)
                                      have e8 : bs.drop (i + 8) = l0 +: bs.drop (i + 9) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 8).symm.trans h8)
                                      have e9 : bs.drop (i + 9) = l1 +: bs.drop (i + 10) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 9).symm.trans h9)
                                      have e10 : bs.drop (i + 10) = l2 +: bs.drop (i + 11) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 10).symm.trans h10)
                                      have e11 : bs.drop (i + 11) = l3 +: bs.drop (i + 12) :=
                                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 11).symm.trans h11)
                                      by_cases hzw : z0 = 0x5C ∧ z1 = 0x75
                                      · obtain ⟨hz0, hz1⟩ := hzw
                                        subst hz0; subst hz1
                                        cases hL : Hex4 l0 l1 l2 l3 with
                                        | none =>
                                          have hstep : policyStep bs i = ⟨none, none⟩ := by
                                            simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hL]
                                          have href : scanCharsFrom off (bs.drop i) =
                                              .error (.badEscape (off + 8)) := by
                                            rw [hcons, hc2, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
                                              scanCharsFrom_pair_badHex off x0 x1 x2 x3 l0 l1 l2 l3 (bs.drop (i + 12)) cv hHex hhi hL]
                                          simp only [StepSpec, hstep]; simp [refClass, href]
                                        | some lv =>
                                          by_cases hlv : 0xDC00 ≤ lv ∧ lv ≤ 0xDFFF
                                          · by_cases hnc : IsNoncharacter (0x10000 + (cv - 0xD800) * 0x400 + (lv - 0xDC00)) = true
                                            · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                                simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hL, hlv, hnc]
                                              have href : scanCharsFrom off (bs.drop i) =
                                                  .error (.noncharacter off) := by
                                                rw [hcons, hc2, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
                                                  scanCharsFrom_pair off x0 x1 x2 x3 l0 l1 l2 l3 (bs.drop (i + 12)) cv lv rfl hHex hL hhi hlv]
                                                simp [scanCons, okCons, hnc]
                                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                            · have hnc' : IsNoncharacter (0x10000 + (cv - 0xD800) * 0x400 + (lv - 0xDC00)) = false := by
                                                simpa using hnc
                                              have hstep : policyStep bs i = ⟨some (i + 12), none⟩ := by
                                                simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hL, hlv, hnc]
                                              have href : scanCharsFrom off (bs.drop i) =
                                                  okCons off (0x10000 + (cv - 0xD800) * 0x400 + (lv - 0xDC00))
                                                    (scanCharsFrom (off + 12) (bs.drop (i + 12))) := by
                                                rw [hcons, hc2, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
                                                  scanCharsFrom_pair off x0 x1 x2 x3 l0 l1 l2 l3 (bs.drop (i + 12)) cv lv rfl hHex hL hhi hlv]
                                                simp [scanCons, okCons, hnc']
                                              simp only [StepSpec, hstep]
                                              refine ⟨by omega, _, hnc', ?_⟩
                                              rw [href, show i + 12 - i = 12 from by omega]
                                          · have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                              simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hL, hlv]
                                            have href : scanCharsFrom off (bs.drop i) =
                                                .error (.unpairedSurrogate off) := by
                                              rw [hcons, hc2, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
                                                scanCharsFrom_pair_badLow off x0 x1 x2 x3 l0 l1 l2 l3 (bs.drop (i + 12)) cv lv hHex hhi hL hlv]
                                            simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                      · by_cases hz0 : z0 = 0x5C
                                        · have hz1' : z1 ≠ 0x75 := by
                                            intro hh; exact hzw ⟨hz0, hh⟩
                                          have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                            simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hz0, hz1']
                                          have e6' : bs.drop (i + 6) = 0x5C +: bs.drop (i + 7) := by
                                            rw [e6, hz0]
                                          have href : scanCharsFrom off (bs.drop i) =
                                              .error (.unpairedSurrogate off) := by
                                            rw [hcons, hc2, e2, e3, e4, e5, e6', e7,
                                              scanCharsFrom_pair_noU off x0 x1 x2 x3 z1 (bs.drop (i + 8)) cv hHex hhi hz1']
                                          simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                                        · have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                                            simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, h6, h7, h8, h9, h10, h11, hz0]
                                          have href : scanCharsFrom off (bs.drop i) =
                                              .error (.unpairedSurrogate off) := by
                                            rw [hcons, hc2, e2, e3, e4, e5, e6,
                                              scanCharsFrom_pair_noEscape off x0 x1 x2 x3 z0 (bs.drop (i + 7)) cv hHex hhi hz0]
                                          simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                        · by_cases hlo : 0xDC00 ≤ cv ∧ cv ≤ 0xDFFF
                          · have hstep : policyStep bs i = ⟨none, some .unpaired⟩ := by
                              simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, hlo]
                            have href : scanCharsFrom off (bs.drop i) = .error (.unpairedSurrogate off) := by
                              rw [hcons, hc2, e2, e3, e4, e5,
                                scanCharsFrom_uchar_low off x0 x1 x2 x3 (bs.drop (i + 6)) cv hHex hlo]
                            simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                          · by_cases hnc : IsNoncharacter cv = true
                            · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, hlo, hnc]
                              have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                rw [hcons, hc2, e2, e3, e4, e5,
                                  scanCharsFrom_uchar off x0 x1 x2 x3 (bs.drop (i + 6)) cv rfl hHex hhi hlo]
                                simp [scanCons, okCons, hnc]
                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                            · have hnc' : IsNoncharacter cv = false := by simpa using hnc
                              have hstep : policyStep bs i = ⟨some (i + 6), none⟩ := by
                                simp [policyStep, h0, h1, hu, h2, h3, h4, h5, hHex, hhi, hlo, hnc]
                              have href : scanCharsFrom off (bs.drop i) =
                                  okCons off cv (scanCharsFrom (off + 6) (bs.drop (i + 6))) := by
                                rw [hcons, hc2, e2, e3, e4, e5,
                                  scanCharsFrom_uchar off x0 x1 x2 x3 (bs.drop (i + 6)) cv rfl hHex hhi hlo]
                                simp [scanCons, okCons, hnc']
                              simp only [StepSpec, hstep]
                              refine ⟨by omega, cv, hnc', ?_⟩
                              rw [href, show i + 6 - i = 6 from by omega]
            · have hstep : policyStep bs i = ⟨none, none⟩ := by
                simp [policyStep, h0, h1, hEsc, he75]
              have href : scanCharsFrom off (bs.drop i) = .error (.badEscape off) := by
                rw [hcons, hc2, scanCharsFrom_escape_bad off e (bs.drop (i + 2)) hEsc he75]
              simp only [StepSpec, hstep]; simp [refClass, href]
      · by_cases h80 : c.toNat < 0x80
        · by_cases h20 : c.toNat < 0x20
          · have hstep : policyStep bs i = ⟨none, none⟩ := by
              simp [policyStep, h0, hq, hsc, h80, h20]
            have hq' : c ≠ 0x22 := hq
            have hs' : c ≠ 0x5C := hsc
            have href : scanCharsFrom off (bs.drop i) = .error (.controlCharacter off) := by
              rw [hcons, scanCharsFrom_control off c (bs.drop (i + 1)) h80 (by omega)]
            simp only [StepSpec, hstep]; simp [refClass, href]
          · have hstep : policyStep bs i = ⟨some (i + 1), none⟩ := by
              simp [policyStep, h0, hq, hsc, h80, h20]
            have hnc : IsNoncharacter c.toNat = false := noncharacter_of_lt c.toNat (by omega)
            have href : scanCharsFrom off (bs.drop i) =
                okCons off c.toNat (scanCharsFrom (off + 1) (bs.drop (i + 1))) := by
              rw [hcons, scanCharsFrom_ascii off c (bs.drop (i + 1)) hq hsc (u8lt (by show c.toNat < (128 : Nat); omega)) (by omega)]
              simp [scanCons, okCons, hnc]
            simp only [StepSpec, hstep]
            refine ⟨by omega, c.toNat, hnc, ?_⟩
            rw [href, show i + 1 - i = 1 from by omega]
        · by_cases hout : c.toNat < 0xC2 ∨ 0xF4 < c.toNat
          · have hstep : policyStep bs i = ⟨none, none⟩ := by
              simp [policyStep, h0, hq, hsc, h80, hout]
            have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
              rw [hcons, scanCharsFrom_utf8_lead off c (bs.drop (i + 1)) (by omega) (by omega)]
            simp only [StepSpec, hstep]; simp [refClass, href]
          · have hlo : 0xC2 ≤ c.toNat := by omega
            have hhi : c.toNat ≤ 0xF4 := by omega
            by_cases htwo : c.toNat ≤ 0xDF
            · cases h1 : (bs.drop i)[1]? with
              | none =>
                have hemp1 : bs.drop (i + 1) = empty := drop_empty_of_missing bs (i+1) (drop_lookup_of bs i 1 0 h1)
                have hstep : policyStep bs i = ⟨none, none⟩ := by
                  simp [policyStep, h0, hq, hsc, h80, hout, htwo, h1]
                have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                  rw [hcons, hemp1, scanCharsFrom_utf8_two_ended off c (u8le (by show (194 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (223 : Nat); omega))]
                simp only [StepSpec, hstep]; simp [refClass, href]
              | some b1 =>
                have hc2 : bs.drop (i + 1) = b1 +: bs.drop (i + 2) :=
                  cons_of_lookup bs ((ByteString.getElem?_drop bs i 1).symm.trans h1)
                by_cases hb : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                · have hstep : policyStep bs i = ⟨some (i + 2), none⟩ := by
                    simp [policyStep, h0, hq, hsc, h80, hout, htwo, h1, hb]
                  have hnc : IsNoncharacter ((c.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)) = false :=
                    noncharacter_of_lt _ (by omega)
                  have href : scanCharsFrom off (bs.drop i) =
                      okCons off ((c.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80))
                        (scanCharsFrom (off + 2) (bs.drop (i + 2))) := by
                    rw [hcons, hc2, scanCharsFrom_utf8_two off c b1 (bs.drop (i + 2))
                      (u8le (by show (194 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (223 : Nat); omega)) (u8le hb.1) (u8le hb.2)]
                    simp [scanCons, okCons, hnc]
                  simp only [StepSpec, hstep]
                  refine ⟨by omega, _, hnc, ?_⟩
                  rw [href, show i + 2 - i = 2 from by omega]
                · have hstep : policyStep bs i = ⟨none, none⟩ := by
                    simp [policyStep, h0, hq, hsc, h80, hout, htwo, h1, hb]
                  have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                    rw [hcons, hc2, scanCharsFrom_utf8_two_bad off c b1 (bs.drop (i + 2))
                    (u8le (by show (194 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (223 : Nat); omega)) hb]
                  simp only [StepSpec, hstep]; simp [refClass, href]
            · by_cases hthree : c.toNat ≤ 0xEF
              · -- three-byte lead
                cases h1 : (bs.drop i)[1]? with
                | none =>
                  have hl : (bs.drop (i + 1)).length < 2 :=
                    drop_len_lt_of_missing bs (i+1) 0 2 (drop_lookup_of bs i 1 0 h1) (by omega)
                  have hstep : policyStep bs i = ⟨none, none⟩ := by
                    simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1]
                  have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                    rw [hcons, scanCharsFrom_3b_ended off c (bs.drop (i + 1)) (by omega) (by omega) hl]
                  simp only [StepSpec, hstep]; simp [refClass, href]
                | some b1 =>
                  cases h2 : (bs.drop i)[2]? with
                  | none =>
                    have hl : (bs.drop (i + 1)).length < 2 :=
                      drop_len_lt_of_missing bs (i+1) 1 2 (drop_lookup_of bs i 1 1 h2) (by omega)
                    have hstep : policyStep bs i = ⟨none, none⟩ := by
                      simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2]
                    have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                      rw [hcons, scanCharsFrom_3b_ended off c (bs.drop (i + 1)) (by omega) (by omega) hl]
                    simp only [StepSpec, hstep]; simp [refClass, href]
                  | some b2 =>
                    have e2 : bs.drop (i + 1) = b1 +: bs.drop (i + 2) :=
                      cons_of_lookup bs ((ByteString.getElem?_drop bs i 1).symm.trans h1)
                    have e3 : bs.drop (i + 2) = b2 +: bs.drop (i + 3) :=
                      cons_of_lookup bs ((ByteString.getElem?_drop bs i 2).symm.trans h2)
                    by_cases he0 : c = 0xE0
                    · subst he0
                      by_cases hA : 0xA0 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                      · by_cases hnc : IsNoncharacter ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = true
                        · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                            simp [policyStep, h0, hq, hsc, h1, h2, hA, hnc]
                          have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                            rw [hcons, e2, e3, scanCharsFrom_utf8_e0 off b1 b2 (bs.drop (i + 3))
                              (u8le hA.1) (u8le hA.2.1) (u8le hA.2.2.1) (u8le hA.2.2.2)]
                            simp [scanCons, okCons, hnc]
                          simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                        · have hnc' : IsNoncharacter ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = false := by
                            simpa using hnc
                          have hstep : policyStep bs i = ⟨some (i + 3), none⟩ := by
                            simp [policyStep, h0, hq, hsc, h1, h2, hA, hnc]
                          have href : scanCharsFrom off (bs.drop i) =
                              okCons off ((b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                                (scanCharsFrom (off + 3) (bs.drop (i + 3))) := by
                            rw [hcons, e2, e3, scanCharsFrom_utf8_e0 off b1 b2 (bs.drop (i + 3))
                              (u8le hA.1) (u8le hA.2.1) (u8le hA.2.2.1) (u8le hA.2.2.2)]
                            simp [scanCons, okCons, hnc']
                          simp only [StepSpec, hstep]
                          refine ⟨by omega, _, hnc', ?_⟩
                          rw [href, show i + 3 - i = 3 from by omega]
                      · have hstep : policyStep bs i = ⟨none, none⟩ := by
                          simp [policyStep, h0, hq, hsc, h1, h2, hA]
                        have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                          rw [hcons, e2, e3, scanCharsFrom_utf8_e0_bad off b1 b2 (bs.drop (i + 3)) hA]
                        simp only [StepSpec, hstep]; simp [refClass, href]
                    · by_cases hed : c = 0xED
                      · subst hed
                        by_cases hB : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x9F ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                        · by_cases hnc : IsNoncharacter (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = true
                          · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                              simp [policyStep, h0, hq, hsc, h1, h2, hB, hnc]
                            have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                              rw [hcons, e2, e3, scanCharsFrom_utf8_ed off b1 b2 (bs.drop (i + 3))
                                (u8le hB.1) (u8le hB.2.1) (u8le hB.2.2.1) (u8le hB.2.2.2)]
                              simp [scanCons, okCons, hnc]
                            simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                          · have hnc' : IsNoncharacter (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = false := by
                              simpa using hnc
                            have hstep : policyStep bs i = ⟨some (i + 3), none⟩ := by
                              simp [policyStep, h0, hq, hsc, h1, h2, hB, hnc]
                            have href : scanCharsFrom off (bs.drop i) =
                                okCons off (0xD000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                                  (scanCharsFrom (off + 3) (bs.drop (i + 3))) := by
                              rw [hcons, e2, e3, scanCharsFrom_utf8_ed off b1 b2 (bs.drop (i + 3))
                                (u8le hB.1) (u8le hB.2.1) (u8le hB.2.2.1) (u8le hB.2.2.2)]
                              simp [scanCons, okCons, hnc']
                            simp only [StepSpec, hstep]
                            refine ⟨by omega, _, hnc', ?_⟩
                            rw [href, show i + 3 - i = 3 from by omega]
                        · have hstep : policyStep bs i = ⟨none, none⟩ := by
                            simp [policyStep, h0, hq, hsc, h1, h2, hB]
                          have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                            rw [hcons, e2, e3, scanCharsFrom_utf8_ed_bad off b1 b2 (bs.drop (i + 3)) hB]
                          simp only [StepSpec, hstep]; simp [refClass, href]
                      · by_cases hC : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF
                        · by_cases hle2 : c.toNat ≤ 0xEC
                          · by_cases hnc : IsNoncharacter ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = true
                            · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, he0, hed, hC, hnc]
                              have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                rw [hcons, e2, e3, scanCharsFrom_utf8_e1ec off c b1 b2 (bs.drop (i + 3))
                                  (u8le (by have h' : c.toNat ≠ 224 := toNat_ne_of_ne he0; show (225 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (236 : Nat); omega)) (u8le hC.1) (u8le hC.2.1) (u8le hC.2.2.1) (u8le hC.2.2.2)]
                                simp [scanCons, okCons, hnc]
                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                            · have hnc' : IsNoncharacter ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = false := by
                                simpa using hnc
                              have hstep : policyStep bs i = ⟨some (i + 3), none⟩ := by
                                simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, he0, hed, hC, hnc]
                              have href : scanCharsFrom off (bs.drop i) =
                                  okCons off ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                                    (scanCharsFrom (off + 3) (bs.drop (i + 3))) := by
                                rw [hcons, e2, e3, scanCharsFrom_utf8_e1ec off c b1 b2 (bs.drop (i + 3))
                                  (u8le (by have h' : c.toNat ≠ 224 := toNat_ne_of_ne he0; show (225 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (236 : Nat); omega)) (u8le hC.1) (u8le hC.2.1) (u8le hC.2.2.1) (u8le hC.2.2.2)]
                                simp [scanCons, okCons, hnc']
                              simp only [StepSpec, hstep]
                              refine ⟨by omega, _, hnc', ?_⟩
                              rw [href, show i + 3 - i = 3 from by omega]
                          · by_cases hnc : IsNoncharacter ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = true
                            · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, he0, hed, hC, hnc]
                              have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                rw [hcons, e2, e3, scanCharsFrom_utf8_eeef off c b1 b2 (bs.drop (i + 3))
                                  (u8le (by have h1' : c.toNat ≠ 224 := toNat_ne_of_ne he0; have h2' : c.toNat ≠ 237 := toNat_ne_of_ne hed; show (238 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (239 : Nat); omega)) (u8le hC.1) (u8le hC.2.1) (u8le hC.2.2.1) (u8le hC.2.2.2)]
                                simp [scanCons, okCons, hnc]
                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                            · have hnc' : IsNoncharacter ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80)) = false := by
                                simpa using hnc
                              have hstep : policyStep bs i = ⟨some (i + 3), none⟩ := by
                                simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, he0, hed, hC, hnc]
                              have href : scanCharsFrom off (bs.drop i) =
                                  okCons off ((c.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 + (b2.toNat - 0x80))
                                    (scanCharsFrom (off + 3) (bs.drop (i + 3))) := by
                                rw [hcons, e2, e3, scanCharsFrom_utf8_eeef off c b1 b2 (bs.drop (i + 3))
                                  (u8le (by have h1' : c.toNat ≠ 224 := toNat_ne_of_ne he0; have h2' : c.toNat ≠ 237 := toNat_ne_of_ne hed; show (238 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (239 : Nat); omega)) (u8le hC.1) (u8le hC.2.1) (u8le hC.2.2.1) (u8le hC.2.2.2)]
                                simp [scanCons, okCons, hnc']
                              simp only [StepSpec, hstep]
                              refine ⟨by omega, _, hnc', ?_⟩
                              rw [href, show i + 3 - i = 3 from by omega]
                        · have hstep : policyStep bs i = ⟨none, none⟩ := by
                            simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, he0, hed, hC]
                          have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                            by_cases hle2 : c.toNat ≤ 0xEC
                            · exact (by rw [hcons, e2, e3, scanCharsFrom_utf8_e1ec_bad off c b1 b2 (bs.drop (i + 3))
                                (u8le (by have h' : c.toNat ≠ 224 := toNat_ne_of_ne he0; show (225 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (236 : Nat); omega)) hC])
                            · exact (by rw [hcons, e2, e3, scanCharsFrom_utf8_eeef_bad off c b1 b2 (bs.drop (i + 3))
                                (u8le (by have h1' : c.toNat ≠ 224 := toNat_ne_of_ne he0; have h2' : c.toNat ≠ 237 := toNat_ne_of_ne hed; show (238 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (239 : Nat); omega)) hC])
                          simp only [StepSpec, hstep]; simp [refClass, href]
              · -- four-byte lead
                cases h1 : (bs.drop i)[1]? with
                | none =>
                  have hl : (bs.drop (i + 1)).length < 3 :=
                    drop_len_lt_of_missing bs (i+1) 0 3 (drop_lookup_of bs i 1 0 h1) (by omega)
                  have hstep : policyStep bs i = ⟨none, none⟩ := by
                    simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1]
                  have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                    rw [hcons, scanCharsFrom_4b_ended off c (bs.drop (i + 1)) (by omega) (by omega) hl]
                  simp only [StepSpec, hstep]; simp [refClass, href]
                | some b1 =>
                  cases h2 : (bs.drop i)[2]? with
                  | none =>
                    have hl : (bs.drop (i + 1)).length < 3 :=
                      drop_len_lt_of_missing bs (i+1) 1 3 (drop_lookup_of bs i 1 1 h2) (by omega)
                    have hstep : policyStep bs i = ⟨none, none⟩ := by
                      simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2]
                    have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                      rw [hcons, scanCharsFrom_4b_ended off c (bs.drop (i + 1)) (by omega) (by omega) hl]
                    simp only [StepSpec, hstep]; simp [refClass, href]
                  | some b2 =>
                    cases h3 : (bs.drop i)[3]? with
                    | none =>
                      have hl : (bs.drop (i + 1)).length < 3 :=
                        drop_len_lt_of_missing bs (i+1) 2 3 (drop_lookup_of bs i 1 2 h3) (by omega)
                      have hstep : policyStep bs i = ⟨none, none⟩ := by
                        simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, h3]
                      have href : scanCharsFrom off (bs.drop i) = .error .ended := by
                        rw [hcons, scanCharsFrom_4b_ended off c (bs.drop (i + 1)) (by omega) (by omega) hl]
                      simp only [StepSpec, hstep]; simp [refClass, href]
                    | some b3 =>
                      have e2 : bs.drop (i + 1) = b1 +: bs.drop (i + 2) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 1).symm.trans h1)
                      have e3 : bs.drop (i + 2) = b2 +: bs.drop (i + 3) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 2).symm.trans h2)
                      have e4 : bs.drop (i + 3) = b3 +: bs.drop (i + 4) :=
                        cons_of_lookup bs ((ByteString.getElem?_drop bs i 3).symm.trans h3)
                      by_cases hC' : 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF
                      · by_cases hF0 : c = 0xF0
                        · subst hF0
                          by_cases hD : 0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                          · by_cases hnc : IsNoncharacter ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = true
                            · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hD, hnc]
                              have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f0 off b1 b2 b3 (bs.drop (i + 4))
                                  (u8le hD.1) (u8le hD.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                simp [scanCons, okCons, hnc]
                              simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                            · have hnc' : IsNoncharacter ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = false := by
                                simpa using hnc
                              have hstep : policyStep bs i = ⟨some (i + 4), none⟩ := by
                                simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hD, hnc]
                              have href : scanCharsFrom off (bs.drop i) =
                                  okCons off ((b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                                    (scanCharsFrom (off + 4) (bs.drop (i + 4))) := by
                                rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f0 off b1 b2 b3 (bs.drop (i + 4))
                                  (u8le hD.1) (u8le hD.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                simp [scanCons, okCons, hnc']
                              simp only [StepSpec, hstep]
                              refine ⟨by omega, _, hnc', ?_⟩
                              rw [href, show i + 4 - i = 4 from by omega]
                          · have hstep : policyStep bs i = ⟨none, none⟩ := by
                              simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hD]
                            have hbad : ¬ (0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
                              b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                              rintro ⟨h1', h2', h3', h4', h5', h6'⟩; exact hD ⟨h1', h2'⟩
                            have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                              rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f0_bad off b1 b2 b3 (bs.drop (i + 4)) hbad]
                            simp only [StepSpec, hstep]; simp [refClass, href]
                        · by_cases hle3 : c.toNat ≤ 0xF3
                          · by_cases hE : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF
                            · by_cases hnc : IsNoncharacter ((c.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = true
                              · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                  simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, h3, hC', hF0, hle3, hE, hnc]
                                have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                  rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f1f3 off c b1 b2 b3 (bs.drop (i + 4))
                                    (u8le (by have h' : c.toNat ≠ 240 := toNat_ne_of_ne hF0; show (241 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (243 : Nat); omega)) (u8le hE.1) (u8le hE.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                  simp [scanCons, okCons, hnc]
                                simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                              · have hnc' : IsNoncharacter ((c.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = false := by
                                  simpa using hnc
                                have hstep : policyStep bs i = ⟨some (i + 4), none⟩ := by
                                  simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, h3, hC', hF0, hle3, hE, hnc]
                                have href : scanCharsFrom off (bs.drop i) =
                                    okCons off ((c.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                                      (scanCharsFrom (off + 4) (bs.drop (i + 4))) := by
                                  rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f1f3 off c b1 b2 b3 (bs.drop (i + 4))
                                    (u8le (by have h' : c.toNat ≠ 240 := toNat_ne_of_ne hF0; show (241 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (243 : Nat); omega)) (u8le hE.1) (u8le hE.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                  simp [scanCons, okCons, hnc']
                                simp only [StepSpec, hstep]
                                refine ⟨by omega, _, hnc', ?_⟩
                                rw [href, show i + 4 - i = 4 from by omega]
                            · have hstep : policyStep bs i = ⟨none, none⟩ := by
                                simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, h3, hC', hF0, hle3, hE]
                              have hbad : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
                                b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                                rintro ⟨h1', h2', h3', h4', h5', h6'⟩; exact hE ⟨h1', h2'⟩
                              have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                                rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f1f3_bad off c b1 b2 b3 (bs.drop (i + 4))
                                  (u8le (by have h' : c.toNat ≠ 240 := toNat_ne_of_ne hF0; show (241 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (243 : Nat); omega)) hbad]
                              simp only [StepSpec, hstep]; simp [refClass, href]
                          · have hc4 : c = 0xF4 := UInt8.toNat_inj.mp (by show c.toNat = (244 : Nat); omega)
                            subst hc4
                            by_cases hF : 0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F
                            · by_cases hnc : IsNoncharacter (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = true
                              · have hstep : policyStep bs i = ⟨none, some .noncharacter⟩ := by
                                  simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hF0, hF, hnc]
                                have href : scanCharsFrom off (bs.drop i) = .error (.noncharacter off) := by
                                  rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f4 off b1 b2 b3 (bs.drop (i + 4))
                                    (u8le hF.1) (u8le hF.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                  simp [scanCons, okCons, hnc]
                                simp only [StepSpec, hstep]; simp [refClass, href, hdi]
                              · have hnc' : IsNoncharacter (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)) = false := by
                                  simpa using hnc
                                have hstep : policyStep bs i = ⟨some (i + 4), none⟩ := by
                                  simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hF0, hF, hnc]
                                have href : scanCharsFrom off (bs.drop i) =
                                    okCons off (0x100000 + (b1.toNat - 0x80) * 0x1000 + (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80))
                                      (scanCharsFrom (off + 4) (bs.drop (i + 4))) := by
                                  rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f4 off b1 b2 b3 (bs.drop (i + 4))
                                    (u8le hF.1) (u8le hF.2) (u8le hC'.1) (u8le hC'.2.1) (u8le hC'.2.2.1) (u8le hC'.2.2.2)]
                                  simp [scanCons, okCons, hnc']
                                simp only [StepSpec, hstep]
                                refine ⟨by omega, _, hnc', ?_⟩
                                rw [href, show i + 4 - i = 4 from by omega]
                            · have hstep : policyStep bs i = ⟨none, none⟩ := by
                                simp [policyStep, h0, hq, hsc, h1, h2, h3, hC', hF0, hF]
                              have hbad : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧ 0x80 ≤ b2.toNat ∧
                                b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                                rintro ⟨h1', h2', h3', h4', h5', h6'⟩; exact hF ⟨h1', h2'⟩
                              have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                                rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f4_bad off b1 b2 b3 (bs.drop (i + 4)) hbad]
                              simp only [StepSpec, hstep]; simp [refClass, href]
                      · by_cases hF0 : c = 0xF0
                        · subst hF0
                          have hbad : ¬ (0x90 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
                            b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                            rintro ⟨_, _, h3', h4', h5', h6'⟩; exact hC' ⟨h3', h4', h5', h6'⟩
                          have hstep : policyStep bs i = ⟨none, none⟩ := by
                            simp [policyStep, h0, hq, hsc, h1, h2, h3, hC']
                          have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                            rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f0_bad off b1 b2 b3 (bs.drop (i + 4)) hbad]
                          simp only [StepSpec, hstep]; simp [refClass, href]
                        · by_cases hle3 : c.toNat ≤ 0xF3
                          · have hbad : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0xBF ∧ 0x80 ≤ b2.toNat ∧
                              b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                              rintro ⟨_, _, h3', h4', h5', h6'⟩; exact hC' ⟨h3', h4', h5', h6'⟩
                            have hstep : policyStep bs i = ⟨none, none⟩ := by
                              simp [policyStep, h0, hq, hsc, h80, hout, htwo, hthree, h1, h2, h3, hC']
                            have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                              rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f1f3_bad off c b1 b2 b3 (bs.drop (i + 4))
                                (u8le (by have h' : c.toNat ≠ 240 := toNat_ne_of_ne hF0; show (241 : Nat) ≤ c.toNat; omega)) (u8le (by show c.toNat ≤ (243 : Nat); omega)) hbad]
                            simp only [StepSpec, hstep]; simp [refClass, href]
                          · have hc4 : c = 0xF4 := UInt8.toNat_inj.mp (by show c.toNat = (244 : Nat); omega)
                            subst hc4
                            have hbad : ¬ (0x80 ≤ b1.toNat ∧ b1.toNat ≤ 0x8F ∧ 0x80 ≤ b2.toNat ∧
                              b2.toNat ≤ 0xBF ∧ 0x80 ≤ b3.toNat ∧ b3.toNat ≤ 0xBF) := by
                              rintro ⟨_, _, h3', h4', h5', h6'⟩; exact hC' ⟨h3', h4', h5', h6'⟩
                            have hstep : policyStep bs i = ⟨none, none⟩ := by
                              simp [policyStep, h0, hq, hsc, h1, h2, h3, hC']
                            have href : scanCharsFrom off (bs.drop i) = .error (.badUTF8 off) := by
                              rw [hcons, e2, e3, e4, scanCharsFrom_utf8_f4_bad off b1 b2 b3 (bs.drop (i + 4)) hbad]
                            simp only [StepSpec, hstep]; simp [refClass, href]

/-- A suffix that starts at or past the end is empty. -/
theorem drop_empty_of_le (bs : Bytes) (i : Nat) (h : bs.size ≤ i) : bs.drop i = empty := by
  apply ByteString.eq_empty_of_data_toList
  rw [ByteString.data_toList_drop, List.drop_eq_nil_of_le]
  rw [← ByteString.toList_eq_data_toList, ByteString.toList_length]
  omega

/-- The walk theorem: `policyWalk` from `i` with any fuel at least `bs.size - i`
reaches exactly the answer the reference's scan from the same position carries —
its class and the document position that raises it, or nothing.  The fuel
suffices because a continuing step's position strictly increases, which is
`policyStep_spec`'s continuing case. -/
theorem policyWalk_spec (bs : Bytes) (f : Nat) :
    ∀ (i off d : Nat), d + off = i → bs.size - i ≤ f →
      (match policyWalk bs i f with
       | some (cl, p) => refClass bs i off d = some (cl, p)
       | none => refClass bs i off d = none) := by
  induction f with
  | zero =>
    intro i off d hdi hf
    have hle : bs.size ≤ i := by omega
    have hemp : bs.drop i = empty := drop_empty_of_le bs i hle
    have href : scanCharsFrom off (bs.drop i) = .error .ended := by rw [hemp, scanCharsFrom_nil]
    simp only [policyWalk]
    simp [refClass, href]
  | succ f ih =>
    intro i off d hdi hf
    have hspec := policyStep_spec bs i off d hdi
    rw [policyWalk]
    cases hs : (policyStep bs i).self with
    | some c =>
      simp only [StepSpec, hs] at hspec
      simp only
      exact hspec
    | none =>
      cases hn : (policyStep bs i).next with
      | some j =>
        simp only [StepSpec, hs, hn] at hspec
        obtain ⟨hij, cv, hnc, hdec⟩ := hspec
        simp only
        have hdi' : d + (off + (j - i)) = j := by omega
        have hfu : bs.size - j ≤ f := by omega
        rw [refClass_cons bs i off d cv j (off + (j - i)) hnc hdec]
        exact ih j (off + (j - i)) d hdi' hfu
      | none =>
        simp only [StepSpec, hs, hn] at hspec
        simp only
        exact hspec

/-- The walk reads no more fuel than the buffer: any two budgets at least
`bs.size - i` walk the same steps.  This is why the emission's fill may give a
slot any budget it likes — the answer is the position's, not the fuel's. -/
theorem policyWalk_fuel (bs : Bytes) (i : Nat) {f g : Nat}
    (hf : bs.size - i ≤ f) (hg : bs.size - i ≤ g) :
    policyWalk bs i f = policyWalk bs i g := by
  have hf' := policyWalk_spec bs f i 0 i (by omega) hf
  have hg' := policyWalk_spec bs g i 0 i (by omega) hg
  cases hfw : policyWalk bs i f with
  | none =>
    cases hgw : policyWalk bs i g with
    | none => rfl
    | some q =>
      simp only [hfw] at hf'
      simp only [hgw] at hg'
      rw [hf'] at hg'
      exact absurd hg' (by simp)
  | some p =>
    cases hgw : policyWalk bs i g with
    | none =>
      simp only [hfw] at hf'
      simp only [hgw] at hg'
      rw [hf'] at hg'
      exact absurd hg' (by simp)
    | some q =>
      simp only [hfw] at hf'
      simp only [hgw] at hg'
      rw [hf'] at hg'
      exact hg'

/-- The answer a scan reaches is the reference's reading of the same scan: the
walk theorem read at the fuel the definition supplies. -/
theorem policyClass_refClass (bs : Bytes) (i off d : Nat) (hdi : d + off = i) :
    policyClass bs i = refClass bs i off d := by
  have h := policyWalk_spec bs (bs.size - i) i off d hdi (Nat.le_refl _)
  unfold policyClass
  cases hw : policyWalk bs i (bs.size - i) with
  | none => simp only [hw] at h; exact h.symm
  | some p =>
    obtain ⟨cl, q⟩ := p
    simp only [hw] at h
    exact h.symm

/-- The emission's backward fill: the class at `i` is the step's own class, or
the class the slot it continues at already carries, or nothing.  `next` names a
later position, so a pass that fills slots from the buffer's end never reads a
slot it has not filled, and the value it leaves at `i` is the forward walk's. -/
theorem policyClass_backward (bs : Bytes) (i : Nat) :
    policyClass bs i =
      (match (policyStep bs i).self with
       | some c => some (c, i)
       | none =>
         match (policyStep bs i).next with
         | some j => policyClass bs j
         | none => none) := by
  unfold policyClass
  cases hfi : bs.size - i with
  | zero =>
    have hle : bs.size ≤ i := by omega
    have hemp : bs.drop i = empty := drop_empty_of_le bs i hle
    have hz0 : (bs.drop i)[0]? = none := by rw [hemp]; rfl
    have hstep : policyStep bs i = ⟨none, none⟩ := by simp [policyStep, hz0]
    rw [hstep]
    rfl
  | succ f =>
    rw [policyWalk]
    cases hs : (policyStep bs i).self with
    | some c => rfl
    | none =>
      cases hn : (policyStep bs i).next with
      | none => rfl
      | some j =>
        have hspec := policyStep_spec bs i 0 i (by omega)
        simp only [StepSpec, hs, hn] at hspec
        have hij : i < j := hspec.1
        have hfu : bs.size - j ≤ f := by omega
        exact policyWalk_fuel bs j hfu (Nat.le_refl _)


/-! ### The position scan, read the way a caller reads it

`scanCharsEnd` is the scan the parser and the policy query use — it records an
index instead of copying the remainder.  `refClass_scanCharsEnd` states that its
refusal is the reference scan's, reason and position, which is the step
`policyRefusalAt`'s pattern match on it takes; the side it needs is
`scanCharsEnd_error` in `LeanLLVM/JSON/Scan.lean`. -/

/-- The policy answer read through the position scan: the refusal `scanCharsEnd`
reports is `refClass`'s, at the same reason and the same document position.  This
is the form a caller that reads the recorded index uses — `policyRefusalAt`
matches on `scanCharsEnd`'s error — and it is where `scanCharsEnd_error` is
consumed: the index scan's failure side and the reference scan's are one. -/
theorem refClass_scanCharsEnd (bs : Bytes) (i off d : Nat) :
    (match scanCharsEnd bs i off with
     | .error (.unpairedSurrogate o) => some (PClass.unpaired, d + o)
     | .error (.noncharacter o) => some (PClass.noncharacter, d + o)
     | _ => none) = refClass bs i off d := by
  cases h : scanCharsEnd bs i off with
  | error e =>
    have hs := (scanCharsEnd_error (bs := bs) (i := i) (off := off) (e := e)).mp h
    cases e with
    | unpairedSurrogate o => simp only [refClass, hs]
    | noncharacter o => simp only [refClass, hs]
    | ended => simp only [refClass, hs]
    | badEscape o => simp only [refClass, hs]
    | badUTF8 o => simp only [refClass, hs]
    | controlCharacter o => simp only [refClass, hs]
  | ok p =>
    obtain ⟨rest, hok, -⟩ := scanCharsEnd_sound h
    cases p with
    | mk cs stop => simp only [refClass, hok]

/-! ### Axiom footprints

The step's equivalence is a case analysis over the emission's branches against
the reference's own equations, and the walk and the fill read only that: no
choice, and nothing the reference's equations and the two `Scan` lemmas did not
already carry.  The control at the end shows the instrument reports a declaration
whose type mentions `Classical.choice`, so the absence below is measured rather
than assumed. -/

/-- info: 'LeanLLVM.JSON.scanCharsEnd_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scanCharsEnd_error

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policyStep_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms policyStep_spec

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policyWalk_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms policyWalk_spec

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policyWalk_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms policyWalk_fuel

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policyClass_refClass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms policyClass_refClass

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policyClass_backward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms policyClass_backward

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.refClass_scanCharsEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refClass_scanCharsEnd

/-- Control: a declaration whose type mentions `Classical.choice` is reported
with it, so the absence above is measured rather than assumed. -/
theorem policy_axiom_control :
    (Classical.choice (show Nonempty Nat from ⟨0⟩)) = 0 ∨ True := Or.inr trivial

/-- info: 'LeanLLVM.Refinement.JsonPolicyModel.policy_axiom_control' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms policy_axiom_control

end LeanLLVM.Refinement.JsonPolicyModel
