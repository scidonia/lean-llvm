/-
The kernel domain's certificates: each admission clause is proved to exclude
the reference parser outcome it is there to exclude.

* the opener count bounds the parser's nesting: a `depthExceeded` refusal
  consumes `maxDepth + 1` opener bytes, so `openersTotal ≤ maxDepth` keeps the
  clause `pipelineSpecPre` asks for;
* the quote scan is the reference's own body scanner, so a policy refusal from
  the parser is one the scan reports;
* token exhaustion is unreachable under the input bound: a table of tokens
  carries at most one token per input byte, so a document inside the input bound
  cannot exceed the token bound.  The bound is proved through the tape's own
  span discipline (`checkSpans`) rather than by re-parsing.

No clause is an axiom: each is a theorem about `parseBytes` or its parts.  The
proofs below use the parser's own mutual recursion (`parseValue.mutual_induct`)
for the two properties that mention parser outcomes, and the public tape
theorems for the token bound.
-/
import LeanLLVM.JSON.Correct
import LeanLLVM.JSON.TapeCorrect
import LeanLLVM.JsonKernelDomain

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The nesting bound -/

/-- The prefix count the induction carries: opener bytes from `i` on. -/
def openersIn (l : List UInt8) : Nat := l.countP openerB

def openersFrom (bs : Bytes) (i : Nat) : Nat := openersIn (bs.data.toList.drop i)

theorem openersIn_append (a b : List UInt8) :
    openersIn (a ++ b) = openersIn a + openersIn b := by
  simp [openersIn, List.countP_append]

theorem openersFrom_zero (bs : Bytes) : openersFrom bs 0 = openersTotal bs := by
  simp [openersFrom, openersTotal, openersIn]

theorem openersFrom_mono {bs : Bytes} {i j : Nat} (h : i ≤ j) :
    openersFrom bs j ≤ openersFrom bs i := by
  unfold openersFrom openersIn
  have h1 : List.take (j - i) (bs.data.toList.drop i) ++
      List.drop (j - i) (bs.data.toList.drop i) = bs.data.toList.drop i :=
    List.take_append_drop _ _
  rw [← h1, List.countP_append]
  have h2 : List.drop (j - i) (bs.data.toList.drop i) = bs.data.toList.drop j := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [h2]
  omega

theorem getElem?_data {bs : Bytes} {i : Nat} {b : UInt8} (h : bs[i]? = some b) :
    bs.data.toList[i]? = some b := by
  rw [← ByteString.toList_eq_data_toList]
  exact (ByteString.toList_getElem?_eq_getElem? bs i).trans h

theorem getElem_data {bs : Bytes} {i : Nat} {b : UInt8} (h : bs[i]? = some b) :
    ∃ (hl : i < bs.data.toList.length), bs.data.toList[i] = b := by
  obtain ⟨hl, hget⟩ := List.getElem?_eq_some_iff.mp (getElem?_data h)
  exact ⟨hl, hget⟩

theorem one_le_openersFrom_of_get? {bs : Bytes} {i : Nat} {b : UInt8}
    (h : bs[i]? = some b) (hb : openerB b = true) : 1 ≤ openersFrom bs i := by
  unfold openersFrom openersIn
  obtain ⟨hl, hget⟩ := getElem_data h
  rw [List.drop_eq_getElem_cons hl, hget, List.countP_cons]
  have h1 : (if openerB b = true then 1 else 0) = 1 := by rw [hb]; rfl
  rw [h1]; omega

theorem openersFrom_succ_of {bs : Bytes} {i : Nat} {b : UInt8}
    (h : bs[i]? = some b) (hb : openerB b = true) :
    openersFrom bs i = 1 + openersFrom bs (i + 1) := by
  unfold openersFrom openersIn
  obtain ⟨hl, hget⟩ := getElem_data h
  rw [List.drop_eq_getElem_cons hl, hget, List.countP_cons]
  have h1 : (if openerB b = true then 1 else 0) = 1 := by rw [hb]; rfl
  rw [h1]; omega

theorem openersFrom_ge_shift {bs : Bytes} {i j : Nat} {b : UInt8}
    (h : bs[i]? = some b) (hb : openerB b = true) (hij : i < j) :
    1 + openersFrom bs j ≤ openersFrom bs i := by
  rw [openersFrom_succ_of h hb]
  have := openersFrom_mono (bs := bs) (show i + 1 ≤ j from hij)
  omega

theorem parseKey_ne_depth (bs : Bytes) (i : Nat) :
    parseKey bs i ≠ .fail .depthExceeded := by
  intro h
  rw [parseKey.eq_def] at h
  repeat (split at h)
  all_goals simp_all

theorem parseString_ne_depth (bs : Bytes) (i : Nat) :
    parseString bs i ≠ .fail .depthExceeded := by
  intro h
  rw [parseString.eq_def] at h
  repeat (split at h)
  all_goals simp_all [parseKey_ne_depth]

theorem parseNumber_ne_depth (bs : Bytes) (i : Nat) :
    parseNumber bs i ≠ .fail .depthExceeded := by
  intro h
  rw [parseNumber.eq_def] at h
  dsimp only at h
  split at h <;> cases h

theorem parseLiteral_ne_depth (bs : Bytes) (i : Nat) (lit : Bytes) (tag : LitTag)
    (hlit : 0 < lit.length) :
    parseLiteral bs i lit tag hlit ≠ .fail .depthExceeded := by
  intro h
  rw [parseLiteral.eq_def] at h
  repeat (split at h)
  all_goals simp_all

set_option maxHeartbeats 1000000 in
theorem depth_openers_from (bs : Bytes) :
    (∀ i depth, parseValue bs i depth = .fail .depthExceeded →
      depth + 1 ≤ openersFrom bs i) ∧
    (∀ j depth, parseMembersTail bs j depth = .fail .depthExceeded →
      depth + 1 ≤ openersFrom bs j) ∧
    (∀ j depth, parseElemsTail bs j depth = .fail .depthExceeded →
      depth + 1 ≤ openersFrom bs j) := by
  refine parseValue.mutual_induct bs _ _ _
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c2 =>
    intro i hb h
    exact one_le_openersFrom_of_get? hb (by decide)
  case c3 =>
    intro i depth hb hd hi first hfirst hclose h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm h
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihm hcall
    have hge := openersFrom_ge_shift hb (by decide : openerB 0x5B = true) hfirst
    omega
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm h
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihtm htail
    have hge := openersFrom_ge_shift hb (by decide : openerB 0x5B = true) (by omega)
    omega
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c8 =>
    intro i hb h
    exact one_le_openersFrom_of_get? hb (by decide)
  case c9 =>
    intro i depth hb hd hi first hfirst hclose h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall ihm h
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihm hcall
    have hge := openersFrom_ge_shift hb (by decide : openerB 0x7B = true) hpos2
    omega
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm h
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihtm htail
    have hge := openersFrom_ge_shift hb (by decide : openerB 0x7B = true) (by omega)
    omega
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hclose ihm ihtm h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hnclose ihm ihtm h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first, parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c16 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c17 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c18 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c19 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey h
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon h
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm h
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihm hcall
    have hle : openersFrom bs (skipFrom bs (skipFrom bs k.next + 1)) ≤ openersFrom bs i :=
      openersFrom_mono (by omega)
    omega
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm h
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihtm htail
    have hle : openersFrom bs pv.next ≤ openersFrom bs i := openersFrom_mono (by omega)
    omega
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail _ ihtm h
    have hres : ∃ t', parseMembersTail bs i depth = .done t' := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall, htail]
        exact ⟨_, rfl⟩
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨t', ht'⟩ := hres
    rw [ht'] at h
    cases h
  case c27 =>
    intro i depth hnc h
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm h
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihm hcall
    have hle : openersFrom bs (skipFrom bs (skipFrom bs i + 1)) ≤ openersFrom bs i :=
      openersFrom_mono (by omega)
    omega
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm h
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]
    rw [hres] at h
    have he : e = .depthExceeded := by injection h
    subst he
    have := ihtm htail
    have hle : openersFrom bs pv.next ≤ openersFrom bs i := openersFrom_mono (by omega)
    omega
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail _ ihtm h
    have hres : ∃ t', parseElemsTail bs i depth = .done t' := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall, htail]
        exact ⟨_, rfl⟩
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨t', ht'⟩ := hres
    rw [ht'] at h
    cases h
  case c31 =>
    intro i depth hnc h
    rw [parseElemsTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [parseKey_ne_depth, parseString_ne_depth, parseNumber_ne_depth, parseLiteral_ne_depth]

/-! ### The parser's nesting refusal -/

theorem depthExceeded_openers (bs : Bytes)
    (h : parseBytes Limits.default bs = .error .depthExceeded) :
    129 ≤ openersTotal bs := by
  have h3 := depth_openers_from bs
  unfold parseBytes at h
  by_cases hin : bs.length > Limits.default.maxInput
  · rw [if_pos hin] at h; cases h
  · rw [if_neg hin] at h
    by_cases hbom : bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
    · rw [if_pos hbom] at h; cases h
    · rw [if_neg hbom] at h
      cases hpv : parseValue bs (skipFrom bs 0) Limits.default.maxDepth with
      | fail e =>
          simp only [hpv] at h
          injection h with he
          subst he
          have hb := h3.1 (skipFrom bs 0) Limits.default.maxDepth hpv
          simp only [Limits.default] at hb
          have hle : openersFrom bs (skipFrom bs 0) ≤ openersTotal bs := by
            have h0 := openersFrom_mono (bs := bs) (i := 0) (j := skipFrom bs 0)
              (Nat.zero_le _)
            simpa [openersFrom_zero] using h0
          omega
      | done p =>
          simp only [hpv] at h
          repeat (split at h) <;> simp_all

/-! ### The capacity outcome is unreachable

The recursive core reports two kinds of failure and never a limit one other than
depth: every `Step.fail` it builds is a `.depthExceeded` of its own or an
`.invalid` a scanner produced.  So `parseBytes` is the only place
`.outOfCapacity` is built, and it builds it only after a successful parse whose
token count exceeds the limit.  The span discipline bounds that count by the
input length, which is what makes the outcome unreachable inside the input
bound.

The first four lemmas are the scanners'; the mutual induction is the core's. -/

theorem parseKey_ne_outOfCapacity (bs : Bytes) (i : Nat) :
    parseKey bs i ≠ .fail .outOfCapacity := by
  intro h
  rw [parseKey.eq_def] at h
  repeat (split at h)
  all_goals simp_all

theorem parseString_ne_outOfCapacity (bs : Bytes) (i : Nat) :
    parseString bs i ≠ .fail .outOfCapacity := by
  intro h
  rw [parseString.eq_def] at h
  repeat (split at h)
  all_goals simp_all [parseKey_ne_outOfCapacity]

theorem parseNumber_ne_outOfCapacity (bs : Bytes) (i : Nat) :
    parseNumber bs i ≠ .fail .outOfCapacity := by
  intro h
  rw [parseNumber.eq_def] at h
  dsimp only at h
  split at h <;> cases h

theorem parseLiteral_ne_outOfCapacity (bs : Bytes) (i : Nat) (lit : Bytes)
    (tag : LitTag) (hlit : 0 < lit.length) :
    parseLiteral bs i lit tag hlit ≠ .fail .outOfCapacity := by
  intro h
  rw [parseLiteral.eq_def] at h
  repeat (split at h)
  all_goals simp_all

set_option maxHeartbeats 1000000 in
theorem parseValue_ne_outOfCapacity (bs : Bytes) :
    (∀ i depth, parseValue bs i depth ≠ .fail .outOfCapacity) ∧
    (∀ j depth, parseMembersTail bs j depth ≠ .fail .outOfCapacity) ∧
    (∀ j depth, parseElemsTail bs j depth ≠ .fail .outOfCapacity) := by
  refine parseValue.mutual_induct bs _ _ _
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
  case c2 =>
    intro i hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
  case c3 =>
    intro i depth hb hd hi first hfirst hclose h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm h
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first]
    rw [hres] at h
    injection h with he
    subst he
    exact ihm hcall
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm h
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first]
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm htail
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c8 =>
    intro i hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
  case c9 =>
    intro i depth hb hd hi first hfirst hclose h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey h
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first]
    rw [hres] at h
    injection h with he
    subst he
    exact (parseKey_ne_outOfCapacity bs _) hkey
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall ihm h
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first]
    rw [hres] at h
    injection h with he
    subst he
    exact ihm hcall
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm h
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all [first]
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm htail
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hclose ihm ihtm h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hnclose ihm ihtm h
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
  case c16 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseString_ne_outOfCapacity bs i) h
  case c17 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_ne_outOfCapacity bs i _ _ _) h
  case c18 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_ne_outOfCapacity bs i _ _ _) h
  case c19 =>
    intro i depth hb h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_ne_outOfCapacity bs i _ _ _) h
  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseNumber_ne_outOfCapacity bs i) h
  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd h
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey h
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact (parseKey_ne_outOfCapacity bs _) hkey
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon h
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hkey]
  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm h
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm hcall
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm h
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm htail
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail _ ihtm h
    have hres : ∃ t', parseMembersTail bs i depth = .done t' := by
      rw [parseMembersTail.eq_def]
      split
      · rename_i hc
        simp only [hkey]
        simp [hncColon]
        simp only [hcall, htail]
        exact ⟨_, rfl⟩
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨t', ht'⟩ := hres
    rw [ht'] at h
    cases h
  case c27 =>
    intro i depth hnc h
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all
  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm h
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm hcall
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm h
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm htail
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail _ ihtm h
    have hres : ∃ t', parseElemsTail bs i depth = .done t' := by
      rw [parseElemsTail.eq_def]
      split
      · rename_i hc
        simp only [hcall, htail]
        exact ⟨_, rfl⟩
      · rename_i hother
        exact absurd hcomma hother
    obtain ⟨t', ht'⟩ := hres
    rw [ht'] at h
    cases h
  case c31 =>
    intro i depth hnc h
    rw [parseElemsTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all

/-! ### The token count is bounded by the input

A successful parse's tokens satisfy `checkSpans` at the document: that is
`tape_valid` read at the tape the parse produced.  The span discipline then
bounds the count by the input length, because every token's span is non-empty
and the spans advance strictly through the input. -/

theorem checkSpans_length_le (bs : Bytes) (toks : List Token) (prev : Nat)
    (hspans : checkSpans bs toks prev = true) (hprev : prev ≤ bs.length) :
    toks.length + prev ≤ bs.length := by
  induction toks generalizing prev with
  | nil => simpa using hprev
  | cons tok rest ih =>
      simp only [checkSpans, Bool.and_eq_true, decide_eq_true_eq] at hspans
      have h1 : prev ≤ tok.span.start := hspans.1.1.1.1
      have h2 : tok.span.start < tok.span.stop := hspans.1.1.1.2
      have h3 : tok.span.stop ≤ bs.length := hspans.1.1.2
      have h4 : checkSpans bs rest tok.span.stop = true := hspans.2
      have hrec := ih tok.span.stop h4 h3
      simp only [List.length_cons]
      omega

/-- A successful parse inside the input bound carries at most one token per input
byte: the tape's span discipline is `checkSpans`, and the spans are non-empty,
ordered and inside the document.  The tape is obtained by parsing again at the
limit whose token bound is exactly the count the parse produced, so the
statement is `parseRef_sound` followed by `tape_valid`, not a second parser. -/
theorem tokens_length_le_input (bs : Bytes) {p : Parsed (skipFrom bs 0)}
    (hin : bs.length ≤ Limits.default.maxInput)
    (hbom : bs.take 3 ≠ ByteString.literal [0xEF, 0xBB, 0xBF])
    (hp : parseValue bs (skipFrom bs 0) Limits.default.maxDepth = .done p)
    (htr : ¬ skipFrom bs p.next < bs.length) :
    p.tokens.length ≤ bs.length := by
  let L : Limits := { Limits.default with maxTokens := p.tokens.length }
  have hparse : parseBytes L bs = .ok ⟨bs, p.tokens⟩ := by
    have hlen : ¬ bs.length > L.maxInput := by
      show ¬ bs.length > Limits.default.maxInput
      omega
    unfold parseBytes
    rw [if_neg hlen, if_neg hbom]
    have hpL : parseValue bs (skipFrom bs 0) L.maxDepth = .done p := hp
    rw [hpL]
    dsimp only
    rw [if_neg htr]
    rw [if_pos (by simp [L])]
  obtain ⟨-, v, -, hdec⟩ := (parseRef_sound L bs).1 ⟨bs, p.tokens⟩ hparse
  have hspans : checkSpans bs p.tokens 0 = true := by
    have := (tape_valid ⟨bs, p.tokens⟩ v hdec).1
    simpa [spansWellFormed] using this
  have := checkSpans_length_le bs p.tokens 0 hspans (Nat.zero_le _)
  simpa using this

/-- `parseBytes` builds `.outOfCapacity` only from a successful parse whose token
count exceeds the limit, and the token count cannot exceed the input length.  So
a document inside the input bound is never refused for capacity. -/
theorem parseBytes_no_outOfCapacity (bs : Bytes)
    (hin : bs.length ≤ Limits.default.maxInput) :
    parseBytes Limits.default bs ≠ .error .outOfCapacity := by
  intro h
  unfold parseBytes at h
  rw [if_neg (by omega : ¬ bs.length > Limits.default.maxInput)] at h
  by_cases hbom : bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
  · rw [if_pos hbom] at h; cases h
  · rw [if_neg hbom] at h
    cases hpv : parseValue bs (skipFrom bs 0) Limits.default.maxDepth with
    | fail e =>
        simp only [hpv] at h
        injection h with he
        subst he
        exact (parseValue_ne_outOfCapacity bs).1 (skipFrom bs 0) Limits.default.maxDepth hpv
    | done p =>
        simp only [hpv] at h
        by_cases htr : skipFrom bs p.next < bs.length
        · rw [if_pos htr] at h; cases h
        · rw [if_neg htr] at h
          by_cases hcap : p.tokens.length ≤ Limits.default.maxTokens
          · rw [if_pos hcap] at h; cases h
          · refine hcap ?_
            have hle := tokens_length_le_input bs hin hbom hpv htr
            have : p.tokens.length ≤ Limits.default.maxInput :=
              Nat.le_trans hle hin
            simpa [Limits.default] using this

/-! ### The character policy -/

def isPolicyReject : Reject → Bool
  | .unpairedSurrogate _ => true
  | .noncharacter _ => true
  | _ => false

def isPolicyError : ParseError → Bool
  | .invalid r => isPolicyReject r
  | _ => false

def isPolicyErr : ScanError → Bool
  | .unpairedSurrogate _ => true
  | .noncharacter _ => true
  | _ => false

/-- The scanner's policy refusals are the parser's policy rejections, at the
position the parser shifts them to. -/
theorem isPolicyReject_rejectOf (i : Nat) (e : ScanError) :
    isPolicyReject (rejectOf i e) = isPolicyErr e := by
  cases e <;> rfl

/-- The document carries a quote whose body scan refuses under the policy. -/
def PolicyScanHit (bs : Bytes) : Prop :=
  ∃ i err, i < bs.size ∧ bs[i]? = some 0x22 ∧
    scanCharsEnd bs (i + 1) 0 = .error err ∧ isPolicyErr err = true

/-- A quote whose body scan refuses under the policy is one `policyRefusal`
reports. -/
theorem policyRefusal_of_hit {bs : Bytes} {i : Nat} {err : ScanError}
    (hi : i < bs.size) (hq : bs[i]? = some 0x22)
    (hs : scanCharsEnd bs (i + 1) 0 = .error err)
    (hp : isPolicyErr err = true) : policyRefusal bs ≠ none := by
  intro hnone
  have hall := List.findSome?_eq_none_iff.mp hnone
  have hat := hall i (List.mem_range.mpr hi)
  unfold policyRefusalAt at hat
  rw [if_pos hq, hs] at hat
  cases err <;> simp_all [isPolicyErr]

/-- A policy refusal from `parseKey` is a policy refusal from the quote's own
body scan. -/
theorem parseKey_policyHit {bs : Bytes} {i : Nat} {e : ParseError}
    (h : parseKey bs i = .fail e) (hp : isPolicyError e = true) :
    PolicyScanHit bs := by
  rw [parseKey.eq_def] at h
  split at h
  · rename_i hb
    split at h
    · rename_i err hs
      injection h with he
      subst he
      simp only [isPolicyError] at hp
      have hpe : isPolicyErr err = true := by
        rw [← isPolicyReject_rejectOf]
        exact hp
      exact ⟨i, err, length_gt_of_get? hb, hb, hs, hpe⟩
    · cases h
  · rename_i hb
    injection h with he
    subst he
    simp [isPolicyError, isPolicyReject] at hp

theorem parseString_policyHit {bs : Bytes} {i : Nat} {e : ParseError}
    (h : parseString bs i = .fail e) (hp : isPolicyError e = true) :
    PolicyScanHit bs := by
  rw [parseString.eq_def] at h
  split at h
  · rename_i hk
    injection h with he
    subst he
    exact parseKey_policyHit hk hp
  · cases h

theorem parseLiteral_not_policy {bs : Bytes} {i : Nat} {lit : Bytes} {tag : LitTag}
    {hlit : 0 < lit.length} {e : ParseError}
    (h : parseLiteral bs i lit tag hlit = .fail e) (hp : isPolicyError e = true) :
    False := by
  rw [parseLiteral.eq_def] at h
  split at h
  · cases h
  · injection h with he
    subst he
    simp [isPolicyError, isPolicyReject] at hp

theorem parseNumber_not_policy {bs : Bytes} {i : Nat} {e : ParseError}
    (h : parseNumber bs i = .fail e) (hp : isPolicyError e = true) :
    False := by
  rw [parseNumber.eq_def] at h
  dsimp only at h
  split at h
  · cases h
  · injection h with he
    subst he
    simp [isPolicyError, isPolicyReject] at hp

set_option maxHeartbeats 1000000 in
theorem parseValue_policyHit (bs : Bytes) :
    (∀ i depth, ∀ r, parseValue bs i depth = .fail (.invalid r) →
      isPolicyReject r = true → PolicyScanHit bs) ∧
    (∀ j depth, ∀ r, parseMembersTail bs j depth = .fail (.invalid r) →
      isPolicyReject r = true → PolicyScanHit bs) ∧
    (∀ j depth, ∀ r, parseElemsTail bs j depth = .fail (.invalid r) →
      isPolicyReject r = true → PolicyScanHit bs) := by
  refine parseValue.mutual_induct bs _ _ _
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    subst r
    simp [isPolicyReject] at hp

  case c2 =>
    intro i hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all

  case c3 =>
    intro i depth hb hd hi first hfirst hclose r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]

  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm r h hp
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm r hcall hp
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm r h hp
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm r htail hp
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]

  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
    subst r
    simp [isPolicyReject] at hp

  case c8 =>
    intro i hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all

  case c9 =>
    intro i depth hb hd hi first hfirst hclose r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]

  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey r h hp
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact parseKey_policyHit hkey hp
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
    subst r
    simp [isPolicyReject] at hp

  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall ihm r h hp
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm r hcall hp
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm r h hp
    simp only [first] at *
    have hres : parseValue bs i depth = .fail e := by
      rw [parseValue.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm r htail hp
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hclose ihm ihtm r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]

  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hnclose ihm ihtm r h hp
    simp only [first] at *
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all [first]
    subst r
    simp [isPolicyReject] at hp

  case c16 =>
    intro i depth hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact parseString_policyHit h hp

  case c17 =>
    intro i depth hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_not_policy h hp).elim

  case c18 =>
    intro i depth hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_not_policy h hp).elim

  case c19 =>
    intro i depth hb r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseLiteral_not_policy h hp).elim

  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    exact (parseNumber_not_policy h hp).elim

  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd r h hp
    rw [parseValue.eq_def] at h
    repeat (split at h)
    all_goals simp_all
    subst r
    simp [isPolicyReject] at hp

  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey r h hp
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact parseKey_policyHit hkey hp
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon r h hp
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hkey]
    subst r
    simp [isPolicyReject] at hp

  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm r h hp
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm r hcall hp
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm r h hp
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm r htail hp
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail _ ihtm r h hp
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hkey, hncColon, hcall, htail]
    all_goals subst_vars
    all_goals simp_all [hcall, htail]

  case c27 =>
    intro i depth hnc r h hp
    rw [parseMembersTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hnc]

  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm r h hp
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihm r hcall hp
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm r h hp
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all
    rw [hres] at h
    injection h with he
    subst he
    exact ihtm r htail hp
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail _ ihtm r h hp
    rw [parseElemsTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hcall, htail]
    all_goals subst_vars
    all_goals simp_all

  case c31 =>
    intro i depth hnc r h hp
    rw [parseElemsTail.eq_def] at h
    repeat (split at h)
    all_goals simp_all [hnc]

theorem parseBytes_policyRefusal (bs : Bytes) (r : Reject)
    (h : parseBytes Limits.default bs = .error (.invalid r))
    (hp : isPolicyReject r = true) : policyRefusal bs ≠ none := by
  have h3 := parseValue_policyHit bs
  unfold parseBytes at h
  by_cases hin : bs.length > Limits.default.maxInput
  · rw [if_pos hin] at h; cases h
  · rw [if_neg hin] at h
    by_cases hbom : bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
    · rw [if_pos hbom] at h
      cases h
      simp [isPolicyReject] at hp
    · rw [if_neg hbom] at h
      cases hpv : parseValue bs (skipFrom bs 0) Limits.default.maxDepth with
      | fail e =>
          simp only [hpv] at h
          injection h with he
          subst he
          obtain ⟨i, err, hi, hq, hs, hpe⟩ :=
            h3.1 (skipFrom bs 0) Limits.default.maxDepth r hpv hp
          exact policyRefusal_of_hit hi hq hs hpe
      | done p =>
          simp only [hpv] at h
          by_cases htr : skipFrom bs p.next < bs.length
          · rw [if_pos htr] at h
            cases h
            simp [isPolicyReject] at hp
          · rw [if_neg htr] at h
            by_cases hcap : p.tokens.length ≤ Limits.default.maxTokens
            · rw [if_pos hcap] at h; cases h
            · rw [if_neg hcap] at h; cases h

/-! ### The domain decision, read as the record's document clauses

`admission` is the route's document decision; these three theorems turn its
`ok` into exactly the clauses `pipelineSpecPre` asks of the document, so a
caller that check accepts reaches the record's domain by proof rather than by a
second check.  The reasons are the ones the certificate's sections above
establish: the empty document and the input bound are the decision's own first
two clauses, the nesting bound is `depthExceeded_openers`, the capacity outcome
is `parseBytes_no_outOfCapacity`, and the character policy is
`parseBytes_policyRefusal` read through the quote scan. -/

theorem admission_ok {doc : ByteArray} (h : (admission doc).isOk = true) :
    0 < doc.size ∧ doc.size ≤ kernelMaxInput ∧
    openersTotal doc ≤ kernelMaxDepth ∧ policyRefusal doc = none := by
  unfold admission at h
  by_cases h0 : doc.size = 0
  · rw [if_pos h0] at h
    simp only [Except.isOk] at h
    cases h
  · rw [if_neg h0] at h
    by_cases hbig : kernelMaxInput < doc.size
    · rw [if_pos hbig] at h
      simp only [Except.isOk] at h
      cases h
    · rw [if_neg hbig] at h
      by_cases hdep : kernelMaxDepth < openersTotal doc
      · rw [if_pos hdep] at h
        simp only [Except.isOk] at h
        cases h
      · rw [if_neg hdep] at h
        cases hpol : policyRefusal doc with
        | none => exact ⟨by omega, by omega, by omega, rfl⟩
        | some r =>
            rw [hpol] at h
            simp only [Except.isOk] at h
            cases h

/-- A parser refusal that names a policy reason is one the quote scan reports. -/
theorem policyRefusal_of_isPolicyError {bs : Bytes} {e : ParseError}
    (he : parseBytes Limits.default bs = .error e) (hp : isPolicyError e = true) :
    policyRefusal bs ≠ none := by
  cases e with
  | invalid r => exact parseBytes_policyRefusal bs r he hp
  | inputTooLong => simp [isPolicyError] at hp
  | depthExceeded => simp [isPolicyError] at hp
  | outOfCapacity => simp [isPolicyError] at hp

/-- **The domain decision implies the record's document clauses.**  A document
`admission` accepts is non-empty, inside the input bound, and the reference
parser does not refuse it for depth, for capacity, or under its character
policy. -/
theorem admission_documentDomain (doc : ByteArray)
    (h : (admission doc).isOk = true) :
    0 < doc.size ∧ doc.size ≤ Limits.default.maxInput ∧
    (∀ e : ParseError,
      parseBytes Limits.default doc = .error e →
        e ≠ .depthExceeded ∧ e ≠ .outOfCapacity ∧ ¬ isPolicyError e) := by
  obtain ⟨hpos, hlen, hopen, hpol⟩ := admission_ok h
  have hlen' : doc.size ≤ Limits.default.maxInput := by
    simpa [kernelMaxInput, Limits.default] using hlen
  refine ⟨hpos, hlen', ?_⟩
  intro e he
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    have h129 : 129 ≤ openersTotal doc := by
      exact depthExceeded_openers doc (by rw [hd] at he; exact he)
    have h128 : openersTotal doc ≤ 128 := by simpa [kernelMaxDepth] using hopen
    omega
  · intro hout
    exact parseBytes_no_outOfCapacity doc hlen' (hout ▸ he)
  · intro hp
    exact policyRefusal_of_isPolicyError he hp hpol

/-! ### Axiom footprints

The capacity argument adds no assumption: the mutual induction is the parser's
own recursion, and the bound is read off `tape_valid` and the tape's span
discipline.  The control at the end shows the instrument reports a declaration
that does carry `Classical.choice`, so the pins below are measured. -/

/-- info: 'LeanLLVM.Refinement.parseValue_ne_outOfCapacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseValue_ne_outOfCapacity

/-- info: 'LeanLLVM.Refinement.checkSpans_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkSpans_length_le

/-- info: 'LeanLLVM.Refinement.tokens_length_le_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokens_length_le_input

/-- info: 'LeanLLVM.Refinement.parseBytes_no_outOfCapacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseBytes_no_outOfCapacity

/-- info: 'LeanLLVM.Refinement.admission_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms admission_ok

/-- info: 'LeanLLVM.Refinement.admission_documentDomain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms admission_documentDomain

/-- info: 'LeanLLVM.Refinement.admission' depends on axioms: [propext] -/
#guard_msgs in
#print axioms admission

/-- Control: a declaration whose type mentions `Classical.choice` is reported
with it, so the absence above is measured rather than assumed. -/
theorem admission_axiom_control :
    (Classical.choice (show Nonempty Nat from ⟨0⟩)) = 0 ∨ True := Or.inr trivial

/-- info: 'LeanLLVM.Refinement.admission_axiom_control' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms admission_axiom_control

end LeanLLVM.Refinement
