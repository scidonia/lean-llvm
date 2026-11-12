/-
The kernel domain's certificates: each admission clause is proved to exclude
the reference parser outcome it is there to exclude.

* the measured nesting depth bounds the parser's: the clause reads the maximum
  of the stage-1 depth counter's fold over the document's structural delimiter
  sequence (`docDepth`), and the bridge below proves the reference parser
  refuses for depth exactly when that maximum is past its bound — one direction
  turns a `depthExceeded` into a witness of a genuinely deeper document, the
  other turns the measured bound into the absence of that refusal;
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
open LeanLLVM.Refinement.DepthCountRefine

/-! ### The depth clause's certificate

The clause's number is `docDepth`, the maximum of the depth counter's fold over
the document's structural delimiter sequence (`LeanLLVM/JsonKernelDomain.lean`).
The bridge to the parser is stated over the parser's own recursion: a refusal
`depthExceeded` is reached only after the budget's worth of nested containers,
and every container the recursion enters is a structural opener, so the measured
maximum grows with the descent.  The two results are

* `depth_measured_no_refusal`: a document inside the bound is not refused for
  depth — the implication the clause needs, and the one
  `admission_documentDomain` consumes;
* `depth_refusal_deep`: a depth refusal witnesses a document past the bound — the
  measurement is not an over-approximation, which is what makes the clause's
  tightening (the deleted opener count) a narrowing with no case it kept out that
  the parser would have accepted.

The induction carries a second conjunct: a successful parse's span is no deeper
than the position it started at.  The container branches need it between a value
and the tail that follows it, and it is proved by the same recursion.

The document-side pieces are: the scan's stop is past its start (the fixture's
well-foundedness), a whitespace run and a number run and a literal and an object
key contribute no depth, and an opener raises the measured maximum by one while
a closer lowers it by at most one. -/

theorem one_le_depthAt_of_open {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (ho : IsOpenB c = true) : 1 ≤ depthAt bs i := by
  rw [depthAt_open_step h ho]
  have hthis : 0 ≤ depthAt bs (i + 1) := maxDepthTokens_nonneg _
  omega

theorem depthAt_close_le_succ {bs : Bytes} {n : Nat} {c : UInt8}
    (h : bs[n]? = some c) (hc : IsCloseB c = true) :
    depthAt bs (n + 1) ≤ depthAt bs n + 1 := by
  have := depthAt_close_step (bs := bs) h hc
  omega

/-- The scan sees nothing across a window whose bytes are inert. -/
theorem depthAt_window_inert {bs : Bytes} {i d : Nat} {w : Bytes}
    (hw : (bs.drop i).take d = w) (hlen : w.length = d)
    (hinert : ∀ (k : Nat) (b : UInt8), w[k]? = some b → b ≠ 0x22 ∧ delimTok b = false) :
    depthAt bs (i + d) = depthAt bs i := by
  have hr : structTokensFrom bs i = structTokensFrom bs (i + d) := by
    refine structTokensFrom_run bs i d ?_
    intro k b hk hkb hget
    have hdrop : (bs.drop i)[k - i]? = some b := by
      rw [ByteString.getElem?_drop, Nat.add_sub_of_le hk]
      simpa using hget
    have hwget : w[k - i]? = some b := by
      rw [← hw, ByteString.getElem?_take, if_pos (by omega)]
      exact hdrop
    exact hinert (k - i) b hwget
  rw [depthAt, depthAt, hr]

/-- A number run contributes no depth: its bytes are constituents, none of them a
string or a bracket. -/
theorem depthAt_numRunFrom (bs : Bytes) (i : Nat) :
    depthAt bs (i + (numRunFrom bs i).length) = depthAt bs i := by
  have hw : (bs.drop i).take (numRunFrom bs i).length = numRunFrom bs i := by
    rw [numRunFrom_eq]
    exact (numRun_spec (bs.drop i)).1
  refine depthAt_window_inert hw rfl ?_
  intro k b hb
  rw [numRunFrom_eq] at hb
  exact constituent_inert (numRun_getElem (bs.drop i) k hb)

/-- A literal's bytes are its list's, and none of them is a string or a bracket. -/
theorem literal_inert {l : List UInt8} (h : ∀ x ∈ l, x ≠ 0x22 ∧ delimTok x = false) :
    ∀ (k : Nat) (b : UInt8), (ByteString.literal l)[k]? = some b →
      b ≠ 0x22 ∧ delimTok b = false := by
  intro k b hb
  simp only [ByteString.getElem?_literal] at hb
  exact h _ (List.mem_of_getElem? hb)

theorem depthAt_literal {bs : Bytes} {i : Nat} {l : List UInt8}
    (hw : (bs.drop i).take l.length = ByteString.literal l)
    (hinert : ∀ x ∈ l, x ≠ 0x22 ∧ delimTok x = false) :
    depthAt bs (i + l.length) = depthAt bs i := by
  refine depthAt_window_inert (w := ByteString.literal l) hw (by simp) ?_
  exact literal_inert hinert

/-- An object key's span: from the opening quote, through the scan's stop, past the
whitespace and the colon, to the first byte of the member's value. -/
theorem depthAt_key_chain {bs : Bytes} {j : Nat} {knext : Nat} {cs : List Nat}
    {stop : { n : Nat // n ≤ bs.size }}
    (hq : bs[j]? = some 0x22) (hs : scanCharsEnd bs (j + 1) 0 = .ok (cs, stop))
    (hnext : knext = stop.val) (hcolon : bs[skipFrom bs knext]? = some 0x3A) :
    depthAt bs j = depthAt bs (skipFrom bs (skipFrom bs knext + 1)) := by
  subst hnext
  rw [depthAt_quote_step hq hs, depthAt_skipFrom bs stop.val,
    depthAt_inert_step hcolon (by decide) (by decide),
    depthAt_skipFrom bs (skipFrom bs stop.val + 1)]

/-- A key's scan witnesses: the byte at the key's index is a quote and the scan
stops where the key ends. -/
theorem key_scan {bs : Bytes} {j : Nat} {k : Key j} (h : parseKey bs j = .done k) :
    ∃ (cs : List Nat) (stop : { n : Nat // n ≤ bs.size }),
      bs[j]? = some 0x22 ∧ scanCharsEnd bs (j + 1) 0 = .ok (cs, stop) ∧
        k.next = stop.val := by
  rw [parseKey.eq_def] at h
  split at h
  · rename_i heq
    split at h
    · cases h
    · rename_i hs
      simp only [Step.done.injEq] at h
      exact ⟨_, _, heq, hs, by rw [← h]⟩
  · cases h


theorem depthAt_literal_done {bs : Bytes} {i : Nat} {lit : Bytes} {tag : LitTag}
    {hlit : 0 < lit.length} {pv : Parsed i}
    (h : parseLiteral bs i lit tag hlit = .done pv)
    (hinert : ∀ (k : Nat) (b : UInt8), lit[k]? = some b → b ≠ 0x22 ∧ delimTok b = false) :
    depthAt bs pv.next ≤ depthAt bs i := by
  rw [parseLiteral.eq_def] at h
  split at h
  · rename_i hl
    injection h with h'
    subst pv
    dsimp only
    have hw : (bs.drop i).take lit.length = lit := hasPrefixB_iff.mp hl
    rw [depthAt_window_inert hw rfl hinert]
    omega
  · cases h

theorem le_of_eq_aux {a b : Int} (h : a = b) : a ≤ b := by omega

theorem depthAt_number_done {bs : Bytes} {i : Nat} {pv : Parsed i}
    (h : parseNumber bs i = .done pv) : depthAt bs pv.next ≤ depthAt bs i := by
  rw [parseNumber.eq_def] at h
  dsimp only at h
  split at h
  · injection h with h'
    subst pv
    dsimp only
    exact le_of_eq_aux (depthAt_numRunFrom bs i)
  · cases h

theorem parseKey_ne_depth (bs : Bytes) (i : Nat) : parseKey bs i ≠ .fail .depthExceeded := by
  intro h
  rw [parseKey.eq_def] at h
  repeat (split at h)
  all_goals simp_all

theorem parseString_ne_depth (bs : Bytes) (i : Nat) : parseString bs i ≠ .fail .depthExceeded := by
  intro h
  rw [parseString.eq_def] at h
  repeat (split at h)
  all_goals simp_all [parseKey_ne_depth]

theorem parseNumber_ne_depth (bs : Bytes) (i : Nat) : parseNumber bs i ≠ .fail .depthExceeded := by
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

set_option maxHeartbeats 4000000 in
theorem depth_bridge_core (bs : Bytes) :
    (∀ i depth, (parseValue bs i depth = .fail .depthExceeded →
        (depth : Int) + 1 ≤ depthAt bs i) ∧
      (∀ pv : Parsed i, parseValue bs i depth = .done pv → depthAt bs pv.next ≤ depthAt bs i)) ∧
    (∀ i depth, (parseMembersTail bs i depth = .fail .depthExceeded →
        (depth : Int) + 1 ≤ depthAt bs i) ∧
      (∀ t : ObjectTail i, parseMembersTail bs i depth = .done t →
        depthAt bs t.next ≤ depthAt bs i)) ∧
    (∀ i depth, (parseElemsTail bs i depth = .fail .depthExceeded →
        (depth : Int) + 1 ≤ depthAt bs i) ∧
      (∀ t : ArrayTail i, parseElemsTail bs i depth = .done t →
        depthAt bs t.next ≤ depthAt bs i)) := by
  refine parseValue.mutual_induct bs _ _ _
    ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8 ?c9 ?c10 ?c11 ?c12 ?c13 ?c14 ?c15 ?c16 ?c17 ?c18
    ?c19 ?c20 ?c21 ?c22 ?c23 ?c24 ?c25 ?c26 ?c27 ?c28 ?c29 ?c30 ?c31
  case c1 =>
    intro i depth hnone
    exact ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;> simp_all,
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;> simp_all⟩
  case c2 =>
    intro i hb
    exact ⟨by intro h; exact one_le_depthAt_of_open hb (by decide),
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;> simp_all⟩
  case c3 =>
    intro i depth hb hd hi first hfirst hclose
    have hclose' : bs[first]? = some 0x5D := by simpa using hclose
    let p : Parsed i :=
      { tokens := [Token.punct .openBracket ⟨i, i + 1⟩,
                   Token.punct .closeBracket ⟨first, first + 1⟩],
        value := .array [], next := first + 1, consumed := by omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [p, first, hbi])
    refine ⟨?_, ?_⟩
    · intro h; rw [hres] at h; cases h
    · intro pv hp
      rw [hres] at hp
      injection hp with hpeq
      subst pv
      dsimp only [p]
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      have hstep : depthAt bs (first + 1) ≤ depthAt bs first + 1 :=
        depthAt_close_le_succ hclose' (by decide)
      omega
  case c4 =>
    intro i depth hb hd hi first hfirst hnc e hcall ihm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [first, hd, hnc, hcall])
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hchild := ihm.1 hcall
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      omega
    · intro pv hp; rw [hres] at hp; cases hp
  case c5 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext e htail ihm ihtm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [first, hd, hnc, hcall, htail])
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hval := ihm.2 pv hcall
      have htail' := ihtm.1 htail
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      omega
    · intro pv' hp; rw [hres] at hp; cases hp
  case c6 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hclose ihm ihtm
    have hclose' : bs[t.next]? = some 0x5D := by simpa using hclose
    let p : Parsed i :=
      { tokens := Token.punct .openBracket ⟨i, i + 1⟩ ::
          (pv.tokens ++ (t.tokens ++ [Token.punct .closeBracket ⟨t.next, t.next + 1⟩])),
        value := .array (pv.value :: t.values), next := t.next + 1,
        consumed := by have := t.moved; omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x5B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [p, first, hd, hnc, hcall, htail, hclose])
    refine ⟨?_, ?_⟩
    · intro h; rw [hres] at h; cases h
    · intro pv' hp
      rw [hres] at hp
      injection hp with hpeq
      subst pv'
      dsimp only [p]
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      have hval := ihm.2 pv hcall
      have htail' := ihtm.2 t htail
      have hstep : depthAt bs (t.next + 1) ≤ depthAt bs t.next + 1 :=
        depthAt_close_le_succ hclose' (by decide)
      omega
  case c7 =>
    intro i depth hb hd hi first hfirst hnc pv hcall hpnext t htail hnclose ihm ihtm
    exact ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;>
        simp_all [first, hd, hnc, hcall, htail, hnclose],
      by intro pv' hp; rw [parseValue.eq_def] at hp; split at hp <;>
        simp_all [first, hd, hnc, hcall, htail, hnclose]⟩
  case c8 =>
    intro i hb
    exact ⟨by intro h; exact one_le_depthAt_of_open hb (by decide),
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;> simp_all⟩
  case c9 =>
    intro i depth hb hd hi first hfirst hclose
    have hclose' : bs[first]? = some 0x7D := by simpa using hclose
    let p : Parsed i :=
      { tokens := [Token.punct .openBrace ⟨i, i + 1⟩,
                   Token.punct .closeBrace ⟨first, first + 1⟩],
        value := .object [], next := first + 1, consumed := by omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [p, first, hbi])
    refine ⟨?_, ?_⟩
    · intro h; rw [hres] at h; cases h
    · intro pv hp
      rw [hres] at hp
      injection hp with hpeq
      subst pv
      dsimp only [p]
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      have hstep : depthAt bs (first + 1) ≤ depthAt bs first + 1 :=
        depthAt_close_le_succ hclose' (by decide)
      omega
  case c10 =>
    intro i depth hb hd hi first hfirst hnc e hkey
    exact ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;>
        simp_all [first, hd, hnc, hkey, parseKey_ne_depth],
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;>
        simp_all [first, hd, hnc, hkey, parseKey_ne_depth]⟩
  case c11 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon
    exact ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;>
        simp_all [first, hd, hnc, hkey, hncColon, parseKey_ne_depth],
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;>
        simp_all [first, hd, hnc, hkey, hncColon, parseKey_ne_depth]⟩
  case c12 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 e hcall ihm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [first, hd, hnc, hkey, hncColon, hcall])
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hchild := ihm.1 hcall
      obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
      have hcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      have hkeychain := depthAt_key_chain hq hs hnext hcolon
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      omega
    · intro pv hp; rw [hres] at hp; cases hp
  case c13 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm
    have hres : parseValue bs i depth = .fail e := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [first, hd, hnc, hkey, hncColon, hcall, htail])
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hval := ihm.2 pv hcall
      have htail' := ihtm.1 htail
      obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
      have hcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      have hkeychain := depthAt_key_chain hq hs hnext hcolon
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      omega
    · intro pv' hp; rw [hres] at hp; cases hp
  case c14 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hclose ihm ihtm
    have hclose' : bs[t.next]? = some 0x7D := by simpa using hclose
    let p : Parsed i :=
      { tokens := Token.punct .openBrace ⟨i, i + 1⟩ :: k.token ::
          ([Token.punct .colon ⟨skipFrom bs k.next, skipFrom bs k.next + 1⟩] ++
            (pv.tokens ++ (t.tokens ++ [Token.punct .closeBrace ⟨t.next, t.next + 1⟩]))),
        value := .object ((k.name, pv.value) :: t.members), next := t.next + 1,
        consumed := by have := t.moved; omega }
    have hres : parseValue bs i depth = .done p := by
      cases hbi : bs[i]? with
      | none => simp_all
      | some b =>
          have hb_eq : b = 0x7B := by
            have h := hb; rw [hbi] at h; exact Option.some.inj h
          subst hb_eq
          rw [parseValue.eq_def]
          split
          all_goals
            first
            | (exfalso; rw [ByteString.getElem?_eq_getElem hi] at *; simp_all; done)
            | (simp_all [p, first, hd, hnc, hkey, hncColon, hcall, htail, hclose])
    refine ⟨?_, ?_⟩
    · intro h; rw [hres] at h; cases h
    · intro pv' hp
      rw [hres] at hp
      injection hp with hpeq
      subst pv'
      dsimp only [p]
      have hopen : depthAt bs i = depthAt bs first + 1 := by
        rw [depthAt_open_step hb (by decide), depthAt_skipFrom bs (i + 1)]
      obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
      have hcolon : bs[skipFrom bs k.next]? = some 0x3A := by simpa using hncColon
      have hkeychain := depthAt_key_chain hq hs hnext hcolon
      have hval := ihm.2 pv hcall
      have htail' := ihtm.2 t htail
      have hstep : depthAt bs (t.next + 1) ≤ depthAt bs t.next + 1 :=
        depthAt_close_le_succ hclose' (by decide)
      omega
  case c15 =>
    intro i depth hb hd hi first hfirst hnc k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail hnclose ihm ihtm
    exact ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;>
        simp_all [first, hd, hnc, hkey, hncColon, hcall, htail, hnclose],
      by intro pv' hp; rw [parseValue.eq_def] at hp; split at hp <;>
        simp_all [first, hd, hnc, hkey, hncColon, hcall, htail, hnclose]⟩
  case c16 =>
    intro i depth hb
    have hres : parseValue bs i depth = parseString bs i := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      simp only [parseString] at h
      split at h
      · rename_i x heq
        injection h with hx
        subst hx
        exact absurd heq (parseKey_ne_depth bs i)
      · rename_i x k hk
        cases h
    · intro pv hp
      rw [hres] at hp
      simp only [parseString] at hp
      split at hp
      · cases hp
      · rename_i x k hk
        injection hp with hp'
        subst pv
        show depthAt bs k.next ≤ depthAt bs i
        obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hk
        rw [hnext, depthAt_quote_step hq hs]
        omega
  case c17 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i (ByteString.literal [116, 114, 117, 101]) .true (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨by intro h; rw [hres] at h; exact absurd h (parseLiteral_ne_depth bs i _ _ _),
      by intro pv hp; rw [hres] at hp
         exact depthAt_literal_done hp (literal_inert (by decide))⟩
  case c18 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i (ByteString.literal [102, 97, 108, 115, 101]) .false (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨by intro h; rw [hres] at h; exact absurd h (parseLiteral_ne_depth bs i _ _ _),
      by intro pv hp; rw [hres] at hp
         exact depthAt_literal_done hp (literal_inert (by decide))⟩
  case c19 =>
    intro i depth hb
    have hres : parseValue bs i depth =
        parseLiteral bs i (ByteString.literal [110, 117, 108, 108]) .null (by decide) := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨by intro h; rw [hres] at h; exact absurd h (parseLiteral_ne_depth bs i _ _ _),
      by intro pv hp; rw [hres] at hp
         exact depthAt_literal_done hp (literal_inert (by decide))⟩
  case c20 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd
    have hres : parseValue bs i depth = parseNumber bs i := by
      rw [parseValue.eq_def]; split <;> simp_all
    refine ⟨by intro h; rw [hres] at h; exact absurd h (parseNumber_ne_depth bs i),
      by intro pv hp; rw [hres] at hp; exact depthAt_number_done hp⟩
  case c21 =>
    intro i depth b hb91 hb123 hb34 hb116 hb102 hb110 hb hd
    refine ⟨by intro h; rw [parseValue.eq_def] at h; split at h <;> simp_all [hd],
      by intro pv hp; rw [parseValue.eq_def] at hp; split at hp <;> simp_all [hd]⟩
  case c22 =>
    intro i depth hcomma hclt hilen hpos e hkey
    exact ⟨by intro h; rw [parseMembersTail.eq_def] at h; split at h <;>
        simp_all [parseKey_ne_depth],
      by intro t ht; rw [parseMembersTail.eq_def] at ht; split at ht <;>
        simp_all [parseKey_ne_depth]⟩
  case c23 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon
    exact ⟨by intro h; rw [parseMembersTail.eq_def] at h; split at h <;>
        simp_all [parseKey_ne_depth, hncColon],
      by intro t ht; rw [parseMembersTail.eq_def] at ht; split at ht <;>
        simp_all [parseKey_ne_depth, hncColon]⟩
  case c24 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 e hcall ihm
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals
        simp_all [parseKey_ne_depth, hncColon, hcall]
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hchild := ihm.1 hcall
      obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
      have hkc := depthAt_key_chain (bs := bs) hq hs hnext (by simpa using hncColon)
      have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
        rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
            ← depthAt_inert_step hcomma (by decide) (by decide),
            ← depthAt_skipFrom bs i]
        omega
      omega
    · intro t ht; rw [hres] at ht; cases ht
  case c25 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext e htail ihm ihtm
    have hres : parseMembersTail bs i depth = .fail e := by
      rw [parseMembersTail.eq_def]; repeat (split); all_goals
        simp_all [parseKey_ne_depth, hncColon, hcall, htail]
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hval := ihm.2 pv hcall
      have htail' := ihtm.1 htail
      obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
      have hkc := depthAt_key_chain (bs := bs) hq hs hnext (by simpa using hncColon)
      have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
        rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
            ← depthAt_inert_step hcomma (by decide) (by decide),
            ← depthAt_skipFrom bs i]
        omega
      omega
    · intro t ht; rw [hres] at ht; cases ht
  case c26 =>
    intro i depth hcomma hclt hilen hpos k hkey hknext hkskip hncColon hpos2 pv hcall hpnext t htail ihm ihtm
    refine ⟨?_, ?_⟩
    · intro h
      rw [parseMembersTail.eq_def] at h
      split at h <;> simp_all [parseKey_ne_depth, hncColon, hcall, htail]
    · intro t' ht
      rw [parseMembersTail.eq_def] at ht
      split at ht
      · rename_i hc
        simp only [hkey] at ht
        simp only [hncColon] at ht
        simp only [hcall, htail] at ht
        injection ht with hpeq
        subst t'
        dsimp only
        have hval := ihm.2 pv hcall
        have htail'' := ihtm.2 t htail
        obtain ⟨cs, stop, hq, hs, hnext⟩ := key_scan hkey
        have hkc := depthAt_key_chain (bs := bs) hq hs hnext (by simpa using hncColon)
        have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
          rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
              ← depthAt_inert_step hcomma (by decide) (by decide),
              ← depthAt_skipFrom bs i]
          omega
        omega
      · injection ht with hpeq
        subst t'
        dsimp only
        rw [← depthAt_skipFrom bs i]
        omega
  case c27 =>
    intro i depth hnc
    refine ⟨by intro h; rw [parseMembersTail.eq_def] at h; split at h <;> simp_all, ?_⟩
    intro t ht
    rw [parseMembersTail.eq_def] at ht
    split at ht
    · simp_all
    · injection ht with hpeq
      subst t
      dsimp only
      rw [← depthAt_skipFrom bs i]
      omega
  case c28 =>
    intro i depth hcomma hclt hilen hpos e hcall ihm
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all [hcall]
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hchild := ihm.1 hcall
      have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
        rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
            ← depthAt_inert_step hcomma (by decide) (by decide),
            ← depthAt_skipFrom bs i]
        omega
      omega
    · intro t ht; rw [hres] at ht; cases ht
  case c29 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext e htail ihm ihtm
    have hres : parseElemsTail bs i depth = .fail e := by
      rw [parseElemsTail.eq_def]; repeat (split); all_goals simp_all [hcall, htail]
    refine ⟨?_, ?_⟩
    · intro h
      rw [hres] at h
      have he : e = .depthExceeded := by injection h
      subst he
      have hval := ihm.2 pv hcall
      have htail' := ihtm.1 htail
      have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
        rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
            ← depthAt_inert_step hcomma (by decide) (by decide),
            ← depthAt_skipFrom bs i]
        omega
      omega
    · intro t ht; rw [hres] at ht; cases ht
  case c30 =>
    intro i depth hcomma hclt hilen hpos pv hcall hpnext t htail ihm ihtm
    refine ⟨?_, ?_⟩
    · intro h
      rw [parseElemsTail.eq_def] at h
      split at h <;> simp_all [hcall, htail]
    · intro t' ht
      rw [parseElemsTail.eq_def] at ht
      split at ht
      · rename_i hc
        simp only [hcall, htail] at ht
        injection ht with hpeq
        subst t'
        dsimp only
        have hval := ihm.2 pv hcall
        have htail'' := ihtm.2 t htail
        have hspan : depthAt bs (skipFrom bs (skipFrom bs i + 1)) ≤ depthAt bs i := by
          rw [← depthAt_skipFrom bs (skipFrom bs i + 1),
              ← depthAt_inert_step hcomma (by decide) (by decide),
              ← depthAt_skipFrom bs i]
          omega
        omega
      · injection ht with hpeq
        subst t'
        dsimp only
        rw [← depthAt_skipFrom bs i]
        omega
  case c31 =>
    intro i depth hnc
    refine ⟨by intro h; rw [parseElemsTail.eq_def] at h; split at h <;> simp_all, ?_⟩
    intro t ht
    rw [parseElemsTail.eq_def] at ht
    split at ht
    · simp_all
    · injection ht with hpeq
      subst t
      dsimp only
      rw [← depthAt_skipFrom bs i]
      omega

/-- **The measured bound suffices: the depth clause's certificate.**  A document
whose measured nesting is inside the reference's bound is not refused for
depth, so the clause `admission` decides with `docDepth` excludes exactly the
outcome `pipelineSpecPre` forbids. -/
theorem depth_measured_no_refusal {bs : Bytes} (hbound : docDepth bs ≤ 128) :
    parseBytes Limits.default bs ≠ .error .depthExceeded := by
  intro h
  unfold parseBytes at h
  by_cases hin : bs.length > Limits.default.maxInput
  · rw [if_pos hin] at h; cases h
  · rw [if_neg hin] at h
    by_cases hbom : bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
    · rw [if_pos hbom] at h; cases h
    · rw [if_neg hbom] at h
      cases hpv : parseValue bs (skipFrom bs 0) Limits.default.maxDepth with
      | fail e =>
          rw [hpv] at h
          injection h with he
          subst he
          have hb := (depth_bridge_core bs).1 (skipFrom bs 0) Limits.default.maxDepth |>.1 hpv
          simp only [Limits.default] at hb
          rw [docDepth] at hbound
          omega
      | done p =>
          simp only [hpv] at h
          repeat (split at h) <;> simp_all

/-- **A depth refusal witnesses the measurement.**  A document the reference
refuses for depth nests deeper than its bound, so the clause's number is not an
over-approximation of the quantity the parser refuses on. -/
theorem depth_refusal_deep {bs : Bytes}
    (h : parseBytes Limits.default bs = .error .depthExceeded) :
    128 < docDepth bs := by
  unfold parseBytes at h
  by_cases hin : bs.length > Limits.default.maxInput
  · rw [if_pos hin] at h; cases h
  · rw [if_neg hin] at h
    by_cases hbom : bs.take 3 = ByteString.literal [0xEF, 0xBB, 0xBF]
    · rw [if_pos hbom] at h; cases h
    · rw [if_neg hbom] at h
      cases hpv : parseValue bs (skipFrom bs 0) Limits.default.maxDepth with
      | fail e =>
          rw [hpv] at h
          injection h with he
          subst he
          have hb := (depth_bridge_core bs).1 (skipFrom bs 0) Limits.default.maxDepth |>.1 hpv
          simp only [Limits.default] at hb
          rw [docDepth]
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
two clauses, the nesting bound is `depth_measured_no_refusal`, the capacity
outcome is `parseBytes_no_outOfCapacity`, and the character policy is
`parseBytes_policyRefusal` read through the quote scan. -/

theorem admission_ok {doc : ByteArray} (h : (admission doc).isOk = true) :
    0 < doc.size ∧ doc.size ≤ kernelMaxInput ∧
    ¬ ((kernelMaxDepth : Int) < docDepth doc) ∧ policyRefusal doc = none := by
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
      by_cases hdep : (kernelMaxDepth : Int) < docDepth doc
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
  obtain ⟨hpos, hlen, hdep, hpol⟩ := admission_ok h
  have hlen' : doc.size ≤ Limits.default.maxInput := by
    simpa [kernelMaxInput, Limits.default] using hlen
  have hmeasure : docDepth doc ≤ 128 := by
    have h := hdep
    simp only [kernelMaxDepth] at h
    omega
  refine ⟨hpos, hlen', ?_⟩
  intro e he
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    exact depth_measured_no_refusal hmeasure (hd ▸ he)
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

/-- info: 'LeanLLVM.Refinement.depth_bridge_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms depth_bridge_core

/-- info: 'LeanLLVM.Refinement.depth_measured_no_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms depth_measured_no_refusal

/-- info: 'LeanLLVM.Refinement.depth_refusal_deep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms depth_refusal_deep

/-- info: 'LeanLLVM.Refinement.admission_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms admission_ok

/-- info: 'LeanLLVM.Refinement.admission_documentDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms admission_documentDomain

/-- info: 'LeanLLVM.Refinement.admission' depends on axioms: [propext, Quot.sound] -/
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
