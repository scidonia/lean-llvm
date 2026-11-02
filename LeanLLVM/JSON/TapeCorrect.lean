/-
Tape validity: the decoder's own correctness.

`tape_valid` quantifies over every tape, so a tape is valid because its spans
check out against the bytes, not because a parser produced it.  The proof
establishes, by induction over the decoder's recursion, that every token's span
points at the bytes its kind denotes and that the decoded value is a derivation
of the strict grammar.
-/

import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Tape

namespace LeanLLVM.JSON

/-! ### Span chains -/

/-- The span discipline `checkSpans` decides, stated as a proposition so the
proof can compose it: every span lies inside the input, the spans advance, and a
punctuation span is one byte. -/
private def SpansOK (bs : Bytes) : List Token → Nat → Prop
  | [], _ => True
  | tok :: rest, prev =>
      prev ≤ tok.span.start ∧
      tok.span.start < tok.span.stop ∧
      tok.span.stop ≤ bs.length ∧
      (match tok with | .punct _ _ => tok.span.stop = tok.span.start + 1 | _ => True) ∧
      SpansOK bs rest tok.span.stop

/-- The byte position after the last token of a list, entered at a boundary. -/
private def lastStop : List Token → Nat → Nat
  | [], prev => prev
  | tok :: rest, _ => lastStop rest tok.span.stop

/-- Whether the first token of a tape is punctuation of the given kind.  It is a
`Bool` so that the decoder's two-token branches can be decided without a
non-computable `Decidable` instance for an existential. -/
private def headPunct (k : Punct) : List Token → Bool
  | .punct k' _ :: _ => decide (k' = k)
  | _ => false

/-- `checkSpans` and `SpansOK` are the same claim. -/
private theorem spansOK_iff (bs : Bytes) : ∀ (toks : List Token) (prev : Nat),
    SpansOK bs toks prev ↔ checkSpans bs toks prev = true
  | [], _ => by simp [SpansOK, checkSpans]
  | tok :: rest, prev => by
      cases tok <;>
        simp [SpansOK, checkSpans, Bool.and_eq_true, decide_eq_true_eq,
          spansOK_iff bs rest, and_assoc]

/-- The last cursor of an append is the last cursor of its second part. -/
private theorem lastStop_append : ∀ (a : List Token) (b : List Token) (prev : Nat),
    lastStop (a ++ b) prev = lastStop b (lastStop a prev)
  | [], b, prev => by simp [lastStop]
  | tok :: a, b, prev => by
      simp only [List.cons_append, lastStop]
      exact lastStop_append a b tok.span.stop

/-- A nonempty list's last cursor does not depend on the boundary it is entered
from, because the first token's span fixes the rest. -/
private theorem lastStop_congr {pre : List Token} (hne : pre ≠ []) (a b : Nat) :
    lastStop pre a = lastStop pre b := by
  cases pre with
  | nil => exact absurd rfl hne
  | cons tok rest => simp [lastStop]

/-- Two span chains compose at the first one's last cursor. -/
private theorem spansOK_append : ∀ (a : List Token) (b : List Token) (prev : Nat),
    SpansOK bs a prev ∧ SpansOK bs b (lastStop a prev) → SpansOK bs (a ++ b) prev
  | [], b, prev, h => by simp [lastStop] at h; exact h.2
  | tok :: a, b, prev, h => by
      obtain ⟨h1, h2⟩ := h
      simp only [SpansOK] at h1 ⊢
      obtain ⟨h11, h12, h13, h14, h15⟩ := h1
      exact ⟨h11, h12, h13, h14, spansOK_append a b tok.span.stop ⟨h15, h2⟩⟩

/-! ### Element and member lists -/

/-- The element tail's two outcomes: no elements, and then no token is consumed
and the cursor is the skip from the entry point; or a nonempty list, and then the
grammar's `Elems` derivation runs from the first element's start. -/
private def ElemsSound (bs : Bytes) (j : Nat) (toks rest : List Token) (vs : List Value) (k : Nat) : Prop :=
  (vs = [] ∧ rest = toks ∧ k = skipFrom bs j) ∨
    (bs[skipFrom bs j]? = some 0x2C ∧
      Elems .strict bs (skipFrom bs (skipFrom bs j + 1)) vs k)

/-- The member tail's two outcomes, with `Members` in the nonempty case. -/
private def MembersSound (bs : Bytes) (j : Nat) (toks rest : List Token)
    (ms : List (List Nat × Value)) (k : Nat) : Prop :=
  (ms = [] ∧ rest = toks ∧ k = skipFrom bs j) ∨
    (bs[skipFrom bs j]? = some 0x2C ∧
      Members .strict bs (skipFrom bs (skipFrom bs j + 1)) ms k)

/-! ### The decoder's soundness -/

/-- Soundness of the three mutually recursive decoders: a successful decode has a
strict-grammar derivation over the bytes it consumed, and the tokens it consumed
form a span chain running from the entry bound to the returned cursor.  The
induction is on the token count, which every recursive call strictly decreases. -/
private theorem decode_sound_aux (bs : Bytes) :
    ∀ (n : Nat) (toks : List Token), toks.length = n →
      (∀ (i prev : Nat) (d : Decoded toks), prev ≤ i →
        decodeValue bs i toks = some d →
        ValueAt .strict bs i d.value d.cursor ∧
        ∃ pre, toks = pre ++ d.rest ∧ SpansOK bs pre prev ∧ lastStop pre i = d.cursor)
      ∧
      (∀ (j prev : Nat) (t : ElemsTail toks), prev ≤ j →
        decodeElemsTail bs j toks = some t →
        (∃ pre, toks = pre ++ t.rest ∧ SpansOK bs pre prev ∧
          t.cursor = skipFrom bs (lastStop pre j))
        ∧ ElemsSound bs j toks t.rest t.values t.cursor)
      ∧
      (∀ (j prev : Nat) (t : MembersTail toks), prev ≤ j →
        decodeMembersTail bs j toks = some t →
        (∃ pre, toks = pre ++ t.rest ∧ SpansOK bs pre prev ∧
          t.cursor = skipFrom bs (lastStop pre j))
        ∧ MembersSound bs j toks t.rest t.members t.cursor) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro toks hlen
    refine ⟨?_, ?_, ?_⟩
    · -- decodeValue
      intro i prev d hprev hdec
      cases toks with
      | nil => simp [decodeValue] at hdec
      | cons tok rest =>
        cases tok with
        | null s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · rename_i hcond
            obtain ⟨hs, hp⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            injection hdec with hd
            subst hd
            subst hs
            refine ⟨ValueAt.null (hasPrefixB_iff.mp hp), ?_⟩
            refine ⟨[Token.null ⟨i, i + 4⟩], by simp, ?_, ?_⟩
            · simp only [SpansOK, Token.span]
              refine ⟨hprev, by omega, ?_, trivial, trivial⟩
              have := hasPrefix_le (hasPrefixB_iff.mp hp)
                (by decide : 0 < [0x6E, 0x75, 0x6C, 0x6C].length)
              omega
            · simp [lastStop, Token.span]
          · cases hdec
        | bool b s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · -- b = true
            rename_i hbt
            subst hbt
            split at hdec
            · rename_i hcond
              obtain ⟨hs, hp⟩ := by
                simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
              injection hdec with hd
              subst hd
              subst hs
              refine ⟨ValueAt.true (hasPrefixB_iff.mp hp), ?_⟩
              refine ⟨[Token.bool true ⟨i, i + 4⟩], by simp, ?_, ?_⟩
              · simp only [SpansOK, Token.span]
                refine ⟨hprev, by omega, ?_, trivial, trivial⟩
                have := hasPrefix_le (hasPrefixB_iff.mp hp)
                  (by decide : 0 < [0x74, 0x72, 0x75, 0x65].length)
                omega
              · simp [lastStop, Token.span]
            · cases hdec
          · -- b = false
            rename_i hbf
            have hbfl : b = false := by cases b <;> simp_all
            subst hbfl
            split at hdec
            · rename_i hcond
              obtain ⟨hs, hp⟩ := by
                simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
              injection hdec with hd
              subst hd
              subst hs
              refine ⟨ValueAt.false (hasPrefixB_iff.mp hp), ?_⟩
              refine ⟨[Token.bool false ⟨i, i + 5⟩], by simp, ?_, ?_⟩
              · simp only [SpansOK, Token.span]
                refine ⟨hprev, by omega, ?_, trivial, trivial⟩
                have := hasPrefix_le (hasPrefixB_iff.mp hp)
                  (by decide : 0 < [0x66, 0x61, 0x6C, 0x73, 0x65].length)
                omega
              · simp [lastStop, Token.span]
            · cases hdec
        | number s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · rename_i hcond
            obtain ⟨hs, hlex⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            have hnum : NumberAt bs i (i + (numRun (bs.drop i)).length) := by
              refine ⟨Nat.le_add_right _ _, ?_⟩
              show RfcNumber ((bs.drop i).take (i + (numRun (bs.drop i)).length - i))
              rw [Nat.add_sub_cancel_left, (numRun_spec (bs.drop i)).1]
              exact numLexB_iff _ |>.mp hlex
            have hv : ValueAt .strict bs i (.number (numRun (bs.drop i)))
                (i + (numRun (bs.drop i)).length) := by
              have h := ValueAt.number (m := .strict) hnum
              rwa [Nat.add_sub_cancel_left, (numRun_spec (bs.drop i)).1] at h
            injection hdec with hd
            subst hd
            subst hs
            refine ⟨hv, ?_⟩
            refine ⟨[Token.number ⟨i, i + (numRun (bs.drop i)).length⟩], by simp, ?_, ?_⟩
            · simp only [SpansOK, Token.span]
              refine ⟨hprev, by have := numLexB_nonempty _ hlex; omega, ?_, trivial, trivial⟩
              have hple : (numRun (bs.drop i)).length ≤ (bs.drop i).length := by
                have h1 := (numRun_spec (bs.drop i)).1
                have h2 : ((bs.drop i).take (numRun (bs.drop i)).length).length
                    ≤ (bs.drop i).length := by
                  rw [List.length_take]
                  omega
                rwa [h1] at h2
              have hpos := numLexB_nonempty _ hlex
              rw [List.length_drop] at hple
              omega
            · simp [lastStop, Token.span]
          · cases hdec
        | string s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · cases hdec
          · rename_i cs after hs
            dsimp only at hdec
            split at hdec
            · rename_i hcond
              obtain ⟨hq, hspan⟩ := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
              have hstr : StrChars .strict (bs.drop (i + 1)) cs after :=
                (scanChars_iff (bs.drop (i + 1)) cs after).mp hs
              have hsa : StringAt .strict bs i (bs.length - after.length) cs := by
                unfold StringAt
                refine ⟨hq, after, hstr, ?_⟩
                obtain ⟨pre, hp⟩ := strChars_split hstr
                have hsuffix : ∃ pre', bs = pre' ++ after :=
                  ⟨bs.take (i + 1) ++ pre, by
                    rw [List.append_assoc, ← hp, List.take_append_drop]⟩
                obtain ⟨pre', hpre'⟩ := hsuffix
                exact drop_of_split hpre'
              injection hdec with hd
              subst hd
              subst hspan
              refine ⟨ValueAt.string hsa, ?_⟩
              refine ⟨[Token.string ⟨i, bs.length - after.length⟩], by simp, ?_, ?_⟩
              · simp only [SpansOK, Token.span]
                refine ⟨hprev, ?_, by omega, trivial, trivial⟩
                have hlt := strChars_suffix_lt hstr
                rw [List.length_drop] at hlt
                obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hq
                omega
              · simp [lastStop, Token.span]
            · cases hdec
        | punct k s =>
          cases k with
          | openBracket =>
            cases rest with
            | nil => simp [decodeValue] at hdec
            | cons tok2 rest2 =>
              by_cases h : headPunct .closeBracket (tok2 :: rest2) = true
              · cases tok2 with
                | punct k2 s2 =>
                  cases k2 with
                  | closeBracket =>
                      rw [decodeValue] at hdec <;> (first | (intro a b hh; cases hh) | skip)
                      split at hdec
                      · rename_i hcond
                        simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, beq_iff_eq] at hcond
                        obtain ⟨hs, hb, hc, hcl⟩ := hcond
                        injection hdec with hd
                        subst hd
                        subst hs
                        subst hc
                        refine ⟨ValueAt.array (vs := []) hb (ArrBody.empty hcl) hcl, ?_⟩
                        refine ⟨[Token.punct .openBracket ⟨i, i + 1⟩,
                          Token.punct .closeBracket ⟨skipFrom bs (i + 1), skipFrom bs (i + 1) + 1⟩],
                          by simp, ?_, ?_⟩
                        · simp only [SpansOK, Token.span]
                          refine ⟨hprev, by omega, ?_, trivial, skipFrom_ge _ _, by omega, ?_, trivial, trivial⟩
                          · have := (List.getElem?_eq_some_iff.mp hb).1
                            omega
                          · have := (List.getElem?_eq_some_iff.mp hcl).1
                            omega
                        · simp [lastStop, Token.span]
                      · cases hdec
                  | openBracket => simp [headPunct] at h
                  | openBrace => simp [headPunct] at h
                  | closeBrace => simp [headPunct] at h
                  | comma => simp [headPunct] at h
                  | colon => simp [headPunct] at h
                | null s2 => simp [headPunct] at h
                | bool b2 s2 => simp [headPunct] at h
                | number s2 => simp [headPunct] at h
                | string s2 => simp [headPunct] at h
              · have hnot : ∀ (c : Span) (rest' : List Token),
                    ¬ (tok2 :: rest2 = .punct .closeBracket c :: rest') := by
                  intro c rest' heq
                  have h1 : headPunct .closeBracket (tok2 :: rest2) = true := by
                    rw [heq]
                    simp [headPunct]
                  exact h h1
                rw [decodeValue] at hdec <;> (first | exact hnot | skip)
                split at hdec
                · rename_i hcond
                  dsimp only at hdec
                  cases hdv : decodeValue bs (skipFrom bs (i + 1)) (tok2 :: rest2) with
                  | none => rw [hdv] at hdec
                            cases hdec
                  | some d1 =>
                    rw [hdv] at hdec
                    dsimp only at hdec
                    cases hdt : decodeElemsTail bs d1.cursor d1.rest with
                    | none => rw [hdt] at hdec
                              cases hdec
                    | some t =>
                      rw [hdt] at hdec
                      dsimp only at hdec
                      split at hdec
                      · -- closing bracket present
                        rename_i c rest' hC
                        split at hdec
                        · rename_i hcond2
                          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond hcond2
                          obtain ⟨hs, hb⟩ := hcond
                          obtain ⟨hcspan, hcl⟩ := hcond2
                          subst hs
                          subst hcspan
                          injection hdec with hd
                          subst hd
                          -- the induction hypotheses at the two shorter lists
                          have hlen1 : (tok2 :: rest2).length < n := by
                            simp only [List.length_cons] at hlen ⊢
                            omega
                          obtain ⟨hV, hE, hM⟩ := ih (tok2 :: rest2).length hlen1 (tok2 :: rest2) rfl
                          have hlen2 : d1.rest.length < n := by
                            have hsh := d1.shrunk
                            simp only [List.length_cons] at hsh hlen1 ⊢
                            omega
                          obtain ⟨hV2, hE2, hM2⟩ := ih d1.rest.length hlen2 d1.rest rfl
                          obtain ⟨hv1, pre1, hsplit1, hspans1, hlast1⟩ :=
                            hV (skipFrom bs (i + 1)) (i + 1) d1 (skipFrom_ge _ _) hdv
                          obtain ⟨hE2', hEsound⟩ :=
                            hE2 d1.cursor d1.cursor t (Nat.le_refl _) hdt
                          obtain ⟨pre2, hsplit2, hspans2, hlast2⟩ := hE2'
                          have hpre1 : pre1 ≠ [] := by
                            intro hnil
                            have he : (tok2 :: rest2).length = d1.rest.length := by
                              have h1 : (tok2 :: rest2).length = (pre1 ++ d1.rest).length :=
                                congrArg List.length hsplit1
                              rw [hnil] at h1
                              simpa using h1
                            have := d1.shrunk
                            omega
                          have hlast1' : lastStop pre1 (i + 1) = d1.cursor := by
                            rw [lastStop_congr hpre1 (i + 1) (skipFrom bs (i + 1))]
                            exact hlast1
                          -- the grammar derivation
                          have helems : Elems .strict bs (skipFrom bs (i + 1))
                              (d1.value :: t.values) t.cursor := by
                            rcases hEsound with ⟨hvs, -, hcur⟩ | ⟨hcomma, he⟩
                            · rw [hvs, hcur]
                              exact Elems.last hv1 (skipFrom_space bs d1.cursor)
                            · exact Elems.cons hv1 (skipFrom_space bs d1.cursor) hcomma
                                (skipFrom_space bs (skipFrom bs d1.cursor + 1)) he
                          refine ⟨ValueAt.array hb (ArrBody.elems helems hcl) hcl, ?_⟩
                          -- the span chain
                          refine ⟨(([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2)
                            ++ [Token.punct .closeBracket ⟨t.cursor, t.cursor + 1⟩],
                            ?_, ?_, ?_⟩
                          · -- the tokens split as the chain followed by the rest
                            simp only [hsplit1, hsplit2, hC, List.append_assoc, List.cons_append,
                              List.nil_append]
                          · -- the chain
                            have hbr : SpansOK bs [Token.punct .openBracket ⟨i, i + 1⟩] prev := by
                              simp only [SpansOK, Token.span]
                              refine ⟨hprev, by omega, ?_, trivial, trivial⟩
                              have := (List.getElem?_eq_some_iff.mp hb).1
                              omega
                            have h12 : SpansOK bs ([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) prev := by
                              have h := spansOK_append (bs := bs)
                                [Token.punct .openBracket ⟨i, i + 1⟩] pre1 prev ⟨hbr, ?_⟩
                              · exact h
                              · simpa [lastStop, Token.span] using hspans1
                            have h123 : SpansOK bs
                                (([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2) prev := by
                              have h := spansOK_append (bs := bs)
                                ([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) pre2 prev
                                ⟨h12, ?_⟩
                              · exact h
                              · rw [lastStop_append]
                                simp only [lastStop, Token.span]
                                rw [hlast1']
                                exact hspans2
                            have hclose' : SpansOK bs [Token.punct .closeBracket ⟨t.cursor, t.cursor + 1⟩]
                                (lastStop (([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2) prev) := by
                              have hl : lastStop (([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2) prev
                                  = lastStop pre2 d1.cursor := by
                                rw [lastStop_append, lastStop_append]
                                simp only [lastStop, Token.span]
                                rw [hlast1']
                              rw [hl]
                              simp only [SpansOK, Token.span]
                              refine ⟨?_, by omega, ?_, trivial, trivial⟩
                              · rw [hlast2]
                                exact skipFrom_ge _ _
                              · have := (List.getElem?_eq_some_iff.mp hcl).1
                                omega
                            exact spansOK_append (bs := bs)
                              (([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2)
                              [Token.punct .closeBracket ⟨t.cursor, t.cursor + 1⟩] prev ⟨h123, hclose'⟩
                          · -- the final cursor
                            rw [lastStop_append]
                            have hl : lastStop (([Token.punct .openBracket ⟨i, i + 1⟩] ++ pre1) ++ pre2) i
                                = lastStop pre2 d1.cursor := by
                              rw [lastStop_append, lastStop_append]
                              simp only [lastStop, Token.span]
                              rw [hlast1']
                            rw [hl]
                            simp only [lastStop, Token.span]
                        · cases hdec
                      · cases hdec
                · cases hdec
          | closeBracket => simp [decodeValue] at hdec
          | openBrace =>
            cases rest with
            | nil => simp [decodeValue] at hdec
            | cons tok2 rest2 =>
              by_cases h : headPunct .closeBrace (tok2 :: rest2) = true
              · cases tok2 with
                | punct k2 s2 =>
                  cases k2 with
                  | closeBrace =>
                      rw [decodeValue] at hdec <;> (first | (intro a b hh; cases hh) | skip)
                      split at hdec
                      · rename_i hcond
                        simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, beq_iff_eq] at hcond
                        obtain ⟨hs, hb, hc, hcl⟩ := hcond
                        injection hdec with hd
                        subst hd
                        subst hs
                        subst hc
                        refine ⟨ValueAt.object (ms := []) hb (ObjBody.empty hcl) hcl, ?_⟩
                        refine ⟨[Token.punct .openBrace ⟨i, i + 1⟩,
                          Token.punct .closeBrace ⟨skipFrom bs (i + 1), skipFrom bs (i + 1) + 1⟩],
                          by simp, ?_, ?_⟩
                        · simp only [SpansOK, Token.span]
                          refine ⟨hprev, by omega, ?_, trivial, skipFrom_ge _ _, by omega, ?_, trivial, trivial⟩
                          · have := (List.getElem?_eq_some_iff.mp hb).1
                            omega
                          · have := (List.getElem?_eq_some_iff.mp hcl).1
                            omega
                        · simp [lastStop, Token.span]
                      · cases hdec
                  | openBracket => simp [headPunct] at h
                  | closeBracket => simp [headPunct] at h
                  | openBrace => simp [headPunct] at h
                  | comma => simp [headPunct] at h
                  | colon => simp [headPunct] at h
                | null s2 => simp [headPunct] at h
                | bool b2 s2 => simp [headPunct] at h
                | number s2 => simp [headPunct] at h
                | string s2 => simp [headPunct] at h
              · have hnot : ∀ (c : Span) (rest' : List Token),
                    ¬ (tok2 :: rest2 = .punct .closeBrace c :: rest') := by
                  intro c rest' heq
                  have h1 : headPunct .closeBrace (tok2 :: rest2) = true := by
                    rw [heq]
                    simp [headPunct]
                  exact h h1
                rw [decodeValue] at hdec <;> (first | exact hnot | skip)
                split at hdec
                · rename_i hcond
                  dsimp only at hdec
                  cases hkv : decodeValue bs (skipFrom bs (i + 1)) (tok2 :: rest2) with
                  | none => rw [hkv] at hdec
                            cases hdec
                  | some k =>
                    rw [hkv] at hdec
                    dsimp only at hdec
                    cases hkv2 : k.value with
                    | null => rw [hkv2] at hdec; cases hdec
                    | bool b => rw [hkv2] at hdec; cases hdec
                    | number l => rw [hkv2] at hdec; cases hdec
                    | array vs => rw [hkv2] at hdec; cases hdec
                    | object ms => rw [hkv2] at hdec; cases hdec
                    | string cs =>
                      rw [hkv2] at hdec
                      dsimp only at hdec
                      split at hdec
                      · rename_i sc rest1 hColon
                        split at hdec
                        · rename_i hcondC
                          cases hdv : decodeValue bs (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                          | none => rw [hdv] at hdec
                                    cases hdec
                          | some d1 =>
                            rw [hdv] at hdec
                            dsimp only at hdec
                            cases hdt : decodeMembersTail bs d1.cursor d1.rest with
                            | none => rw [hdt] at hdec
                                      cases hdec
                            | some t =>
                              rw [hdt] at hdec
                              dsimp only at hdec
                              split at hdec
                              · -- closing brace present
                                rename_i c rest' hC
                                split at hdec
                                · rename_i hcond2
                                  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
                                    at hcond hcond2 hcondC
                                  obtain ⟨hs, hb⟩ := hcond
                                  obtain ⟨hsc, hcol⟩ := hcondC
                                  obtain ⟨hcspan, hcl⟩ := hcond2
                                  subst hs
                                  subst hsc
                                  subst hcspan
                                  injection hdec with hd
                                  subst hd
                                  -- the shorter lists
                                  have hlen1 : (tok2 :: rest2).length < n := by
                                    simp only [List.length_cons] at hlen ⊢
                                    omega
                                  obtain ⟨hV, hE, hM⟩ :=
                                    ih (tok2 :: rest2).length hlen1 (tok2 :: rest2) rfl
                                  obtain ⟨hvk, preK, hsplitK, hspansK, hlastK⟩ :=
                                    hV (skipFrom bs (i + 1)) (i + 1) k (skipFrom_ge _ _) hkv
                                  have hpreK : preK ≠ [] := by
                                    intro hnil
                                    have he : (tok2 :: rest2).length = k.rest.length := by
                                      have h1 : (tok2 :: rest2).length = (preK ++ k.rest).length :=
                                        congrArg List.length hsplitK
                                      rw [hnil] at h1
                                      simpa using h1
                                    have := k.shrunk
                                    omega
                                  have hlastK' : lastStop preK (i + 1) = k.cursor := by
                                    rw [lastStop_congr hpreK (i + 1) (skipFrom bs (i + 1))]
                                    exact hlastK
                                  have hklen : k.rest.length = rest1.length + 1 := by
                                    rw [hColon]
                                    simp
                                  have hkl : (tok2 :: rest2).length = preK.length + k.rest.length := by
                                    simpa [List.length_append] using congrArg List.length hsplitK
                                  have hlenR1 : rest1.length < n := by
                                    simp only [List.length_cons] at hlen1 hklen hkl ⊢
                                    omega
                                  obtain ⟨hV1, hE1, hM1⟩ :=
                                    ih rest1.length hlenR1 rest1 rfl
                                  obtain ⟨hvd, preV, hsplitV, hspansV, hlastV⟩ :=
                                    hV1 (skipFrom bs (skipFrom bs k.cursor + 1))
                                      (skipFrom bs k.cursor + 1) d1 (skipFrom_ge _ _) hdv
                                  have hpreV : preV ≠ [] := by
                                    intro hnil
                                    have he : rest1.length = d1.rest.length := by
                                      have h1 : rest1.length = (preV ++ d1.rest).length :=
                                        congrArg List.length hsplitV
                                      rw [hnil] at h1
                                      simpa using h1
                                    have := d1.shrunk
                                    omega
                                  have hlastV' : lastStop preV (skipFrom bs k.cursor + 1) = d1.cursor := by
                                    rw [lastStop_congr hpreV (skipFrom bs k.cursor + 1)
                                      (skipFrom bs (skipFrom bs k.cursor + 1))]
                                    exact hlastV
                                  have hlenD : d1.rest.length < n := by
                                    have := d1.shrunk
                                    omega
                                  obtain ⟨hV2, hE2, hM2⟩ :=
                                    ih d1.rest.length hlenD d1.rest rfl
                                  obtain ⟨hM2', hMsound⟩ :=
                                    hM2 d1.cursor d1.cursor t (Nat.le_refl _) hdt
                                  obtain ⟨preT, hsplitT, hspansT, hlastT⟩ := hM2'
                                  -- the key's string span
                                  have hk : StringAt .strict bs (skipFrom bs (i + 1)) k.cursor cs := by
                                    have hv' := hvk
                                    rw [hkv2] at hv'
                                    cases hv' with
                                    | string h => exact h
                                  -- the first member
                                  have hmem : Member .strict bs (skipFrom bs (i + 1)) (cs, d1.value) d1.cursor :=
                                    Member.mk hk (skipFrom_space bs k.cursor) hcol
                                      (skipFrom_space bs (skipFrom bs k.cursor + 1)) hvd
                                  have hmembers : Members .strict bs (skipFrom bs (i + 1))
                                      ((cs, d1.value) :: t.members) t.cursor := by
                                    rcases hMsound with ⟨hvs, -, hcur⟩ | ⟨hcomma, he⟩
                                    · rw [hvs, hcur]
                                      exact Members.last hmem (skipFrom_space bs d1.cursor)
                                    · exact Members.cons hmem (skipFrom_space bs d1.cursor) hcomma
                                        (skipFrom_space bs (skipFrom bs d1.cursor + 1)) he
                                  refine ⟨ValueAt.object hb (ObjBody.members hmembers hcl) hcl, ?_⟩
                                  refine ⟨(([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                      ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                          skipFrom bs k.cursor + 1⟩]
                                      ++ preV) ++ preT
                                    ++ [Token.punct .closeBrace ⟨t.cursor, t.cursor + 1⟩],
                                    ?_, ?_, ?_⟩
                                  · -- the token split
                                    simp only [hsplitK, hsplitV, hsplitT, hColon, hC,
                                      List.append_assoc, List.cons_append, List.nil_append]
                                  · -- the chain
                                    have hbr : SpansOK bs [Token.punct .openBrace ⟨i, i + 1⟩] prev := by
                                      simp only [SpansOK, Token.span]
                                      refine ⟨hprev, by omega, ?_, trivial, trivial⟩
                                      have := (List.getElem?_eq_some_iff.mp hb).1
                                      omega
                                    have h1 : SpansOK bs
                                        ([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK) prev := by
                                      have h := spansOK_append (bs := bs)
                                        [Token.punct .openBrace ⟨i, i + 1⟩] preK prev ⟨hbr, ?_⟩
                                      · exact h
                                      · simpa [lastStop, Token.span] using hspansK
                                    have h2 : SpansOK bs
                                        (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩]) prev := by
                                      have h := spansOK_append (bs := bs)
                                        ([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                        [Token.punct .colon ⟨skipFrom bs k.cursor,
                                          skipFrom bs k.cursor + 1⟩] prev ⟨h1, ?_⟩
                                      · exact h
                                      · rw [lastStop_append]
                                        simp only [lastStop, Token.span]
                                        rw [hlastK']
                                        simp only [SpansOK, Token.span]
                                        refine ⟨?_, by omega, ?_, trivial, trivial⟩
                                        · exact skipFrom_ge _ _
                                        · have := (List.getElem?_eq_some_iff.mp hcol).1
                                          omega
                                    have h3 : SpansOK bs
                                        (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩] ++ preV) prev := by
                                      have h := spansOK_append (bs := bs)
                                        (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩]) preV prev ⟨h2, ?_⟩
                                      · exact h
                                      · rw [lastStop_append]
                                        simp only [lastStop, Token.span]
                                        exact hspansV
                                    have h4 : SpansOK bs
                                        (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩] ++ preV ++ preT) prev := by
                                      have h := spansOK_append (bs := bs)
                                        (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩] ++ preV) preT prev ⟨h3, ?_⟩
                                      · exact h
                                      · rw [lastStop_append, lastStop_append, lastStop_append]
                                        simp only [lastStop, Token.span]
                                        rw [hlastV']
                                        exact hspansT
                                    have hclose' : SpansOK bs
                                        [Token.punct .closeBrace ⟨t.cursor, t.cursor + 1⟩]
                                        (lastStop (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩] ++ preV ++ preT) prev) := by
                                      have hl : lastStop (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                          ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                              skipFrom bs k.cursor + 1⟩] ++ preV ++ preT) prev
                                          = lastStop preT d1.cursor := by
                                        rw [lastStop_append, lastStop_append, lastStop_append,
                                          lastStop_append]
                                        simp only [lastStop, Token.span]
                                        rw [hlastV']
                                      rw [hl]
                                      simp only [SpansOK, Token.span]
                                      refine ⟨?_, by omega, ?_, trivial, trivial⟩
                                      · rw [hlastT]
                                        exact skipFrom_ge _ _
                                      · have := (List.getElem?_eq_some_iff.mp hcl).1
                                        omega
                                    exact spansOK_append (bs := bs)
                                      (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                        ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                            skipFrom bs k.cursor + 1⟩] ++ preV ++ preT)
                                      [Token.punct .closeBrace ⟨t.cursor, t.cursor + 1⟩] prev
                                      ⟨h4, hclose'⟩
                                  · -- the final cursor
                                    rw [lastStop_append]
                                    have hl : lastStop (([Token.punct .openBrace ⟨i, i + 1⟩] ++ preK)
                                        ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                            skipFrom bs k.cursor + 1⟩] ++ preV ++ preT) i
                                        = lastStop preT d1.cursor := by
                                      rw [lastStop_append, lastStop_append, lastStop_append,
                                        lastStop_append]
                                      simp only [lastStop, Token.span]
                                      rw [hlastV']
                                    rw [hl]
                                    simp only [lastStop, Token.span]
                                · cases hdec
                              · cases hdec
                        · cases hdec
                      · cases hdec
                · cases hdec
          | closeBrace => simp [decodeValue] at hdec
          | comma => simp [decodeValue] at hdec
          | colon => simp [decodeValue] at hdec
    · -- decodeElemsTail
      intro j prev t hprev hdec
      cases toks with
      | nil =>
        rw [decodeElemsTail] at hdec <;> (first | (intro a b hh; cases hh) | skip)
        injection hdec with hd
        subst hd
        exact ⟨⟨[], by simp, trivial, by simp [lastStop]⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
      | cons tok rest =>
        by_cases hcm : headPunct .comma (tok :: rest) = true
        · cases tok with
          | punct k s =>
            cases k with
            | comma =>
              rw [decodeElemsTail] at hdec
              split at hdec
              · rename_i hcond
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
                obtain ⟨hs, hc⟩ := hcond
                subst hs
                dsimp only at hdec
                cases hdv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
                | none => rw [hdv] at hdec
                          cases hdec
                | some d =>
                  rw [hdv] at hdec
                  dsimp only at hdec
                  cases hdt : decodeElemsTail bs d.cursor d.rest with
                  | none => rw [hdt] at hdec
                            dsimp only at hdec
                            exact absurd hdec (by simp)
                  | some t =>
                    rw [hdt] at hdec
                    dsimp only at hdec
                    injection hdec with hd
                    subst hd
                    have hlen1 : rest.length < n := by
                      have h1 : rest.length + 1 = n := hlen
                      omega
                    obtain ⟨hV, hE, hM⟩ := ih rest.length hlen1 rest rfl
                    have hlen2 : d.rest.length < n := by
                      have hsh := d.shrunk
                      omega
                    obtain ⟨hV2, hE2, hM2⟩ := ih d.rest.length hlen2 d.rest rfl
                    obtain ⟨hvd, preD, hsplitD, hspansD, hlastD⟩ :=
                      hV (skipFrom bs (skipFrom bs j + 1)) (skipFrom bs j + 1) d
                        (skipFrom_ge _ _) hdv
                    obtain ⟨hE2', hEsound⟩ :=
                      hE2 d.cursor d.cursor t (Nat.le_refl _) hdt
                    obtain ⟨preT, hsplitT, hspansT, hlastT⟩ := hE2'
                    have hpreD : preD ≠ [] := by
                      intro hnil
                      have he : rest.length = d.rest.length := by
                        have h1 : rest.length = (preD ++ d.rest).length := congrArg List.length hsplitD
                        rw [hnil] at h1
                        simpa using h1
                      have := d.shrunk
                      omega
                    have hlastD' : lastStop preD (skipFrom bs j + 1) = d.cursor := by
                      rw [lastStop_congr hpreD (skipFrom bs j + 1)
                        (skipFrom bs (skipFrom bs j + 1))]
                      exact hlastD
                    have hbr : SpansOK bs [Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩]
                        prev := by
                      simp only [SpansOK, Token.span]
                      refine ⟨?_, by omega, ?_, trivial, trivial⟩
                      · exact Nat.le_trans hprev (skipFrom_ge _ _)
                      · have := (List.getElem?_eq_some_iff.mp hc).1
                        omega
                    have h12 : SpansOK bs
                        ([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preD) prev := by
                      have h := spansOK_append (bs := bs)
                        [Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] preD prev ⟨hbr, ?_⟩
                      · exact h
                      · simpa [lastStop, Token.span] using hspansD
                    have h123 : SpansOK bs
                        (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preD)
                          ++ preT) prev := by
                      have h := spansOK_append (bs := bs)
                        ([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preD) preT prev
                        ⟨h12, ?_⟩
                      · exact h
                      · rw [lastStop_append]
                        simp only [lastStop, Token.span]
                        rw [hlastD']
                        exact hspansT
                    refine ⟨⟨([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preD)
                        ++ preT, ?_, h123, ?_⟩, Or.inr ⟨hc, ?_⟩⟩
                    · simp only [hsplitD, hsplitT, List.append_assoc, List.cons_append,
                        List.nil_append]
                    · rw [lastStop_append, lastStop_append]
                      simp only [lastStop, Token.span]
                      rw [hlastD', hlastT]
                    · rcases hEsound with ⟨hvs, -, hcur⟩ | ⟨hcomma, he⟩
                      · rw [hvs, hcur]
                        exact Elems.last hvd (skipFrom_space bs d.cursor)
                      · exact Elems.cons hvd (skipFrom_space bs d.cursor) hcomma
                          (skipFrom_space bs (skipFrom bs d.cursor + 1)) he
              · cases hdec
            | openBracket => simp [headPunct] at hcm
            | closeBracket => simp [headPunct] at hcm
            | openBrace => simp [headPunct] at hcm
            | closeBrace => simp [headPunct] at hcm
            | colon => simp [headPunct] at hcm
          | null s => simp [headPunct] at hcm
          | bool b s => simp [headPunct] at hcm
          | number s => simp [headPunct] at hcm
          | string s => simp [headPunct] at hcm
        · have hnot : ∀ (c : Span) (rest' : List Token),
              ¬ (tok :: rest = .punct .comma c :: rest') := by
            intro c rest' heq
            have h1 : headPunct .comma (tok :: rest) = true := by
              rw [heq]
              simp [headPunct]
            exact hcm h1
          rw [decodeElemsTail] at hdec <;> (first | exact hnot | skip)
          injection hdec with hd
          subst hd
          exact ⟨⟨[], by simp, trivial, by simp [lastStop]⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · -- decodeMembersTail
      intro j prev t hprev hdec
      cases toks with
      | nil =>
        rw [decodeMembersTail] at hdec <;> (first | (intro a b hh; cases hh) | skip)
        injection hdec with hd
        subst hd
        exact ⟨⟨[], by simp, trivial, by simp [lastStop]⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
      | cons tok rest =>
        by_cases hcm : headPunct .comma (tok :: rest) = true
        · cases tok with
          | punct k s =>
            cases k with
            | comma =>
              rw [decodeMembersTail] at hdec
              split at hdec
              · rename_i hcond
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
                obtain ⟨hs, hc⟩ := hcond
                subst hs
                dsimp only at hdec
                cases hkv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
                | none => rw [hkv] at hdec
                          cases hdec
                | some k =>
                  rw [hkv] at hdec
                  dsimp only at hdec
                  cases hkv2 : k.value with
                  | null => rw [hkv2] at hdec; cases hdec
                  | bool b => rw [hkv2] at hdec; cases hdec
                  | number l => rw [hkv2] at hdec; cases hdec
                  | array vs => rw [hkv2] at hdec; cases hdec
                  | object ms => rw [hkv2] at hdec; cases hdec
                  | string cs =>
                    rw [hkv2] at hdec
                    dsimp only at hdec
                    split at hdec
                    · rename_i sc rest1 hColon
                      split at hdec
                      · rename_i hcondC
                        cases hdv : decodeValue bs (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                        | none => rw [hdv] at hdec
                                  cases hdec
                        | some d =>
                          rw [hdv] at hdec
                          dsimp only at hdec
                          cases hdt : decodeMembersTail bs d.cursor d.rest with
                          | none => rw [hdt] at hdec
                                    cases hdec
                          | some t =>
                            rw [hdt] at hdec
                            dsimp only at hdec
                            injection hdec with hd
                            subst hd
                            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcondC
                            obtain ⟨hsc, hcol⟩ := hcondC
                            subst hsc
                            have hlen1 : rest.length < n := by
                              simp only [List.length_cons] at hlen
                              omega
                            obtain ⟨hV, hE, hM⟩ := ih rest.length hlen1 rest rfl
                            obtain ⟨hvk, preK, hsplitK, hspansK, hlastK⟩ :=
                              hV (skipFrom bs (skipFrom bs j + 1)) (skipFrom bs j + 1) k
                                (skipFrom_ge _ _) hkv
                            have hpreK : preK ≠ [] := by
                              intro hnil
                              have he : rest.length = k.rest.length := by
                                have h1 : rest.length = (preK ++ k.rest).length :=
                                  congrArg List.length hsplitK
                                rw [hnil] at h1
                                simpa using h1
                              have := k.shrunk
                              omega
                            have hlastK' : lastStop preK (skipFrom bs j + 1) = k.cursor := by
                              rw [lastStop_congr hpreK (skipFrom bs j + 1)
                                (skipFrom bs (skipFrom bs j + 1))]
                              exact hlastK
                            have hklen : k.rest.length = rest1.length + 1 := by
                              rw [hColon]
                              simp
                            have hkl : rest.length = preK.length + k.rest.length := by
                              simpa [List.length_append] using congrArg List.length hsplitK
                            have hlenR1 : rest1.length < n := by omega
                            obtain ⟨hV1, hE1, hM1⟩ := ih rest1.length hlenR1 rest1 rfl
                            obtain ⟨hvd, preV, hsplitV, hspansV, hlastV⟩ :=
                              hV1 (skipFrom bs (skipFrom bs k.cursor + 1))
                                (skipFrom bs k.cursor + 1) d (skipFrom_ge _ _) hdv
                            have hpreV : preV ≠ [] := by
                              intro hnil
                              have he : rest1.length = d.rest.length := by
                                have h1 : rest1.length = (preV ++ d.rest).length :=
                                  congrArg List.length hsplitV
                                rw [hnil] at h1
                                simpa using h1
                              have := d.shrunk
                              omega
                            have hlastV' : lastStop preV (skipFrom bs k.cursor + 1) = d.cursor := by
                              rw [lastStop_congr hpreV (skipFrom bs k.cursor + 1)
                                (skipFrom bs (skipFrom bs k.cursor + 1))]
                              exact hlastV
                            have hlenD : d.rest.length < n := by
                              have := d.shrunk
                              omega
                            obtain ⟨hV2, hE2, hM2⟩ := ih d.rest.length hlenD d.rest rfl
                            obtain ⟨hM2', hMsound⟩ :=
                              hM2 d.cursor d.cursor t (Nat.le_refl _) hdt
                            obtain ⟨preT, hsplitT, hspansT, hlastT⟩ := hM2'
                            have hk : StringAt .strict bs (skipFrom bs (skipFrom bs j + 1))
                                k.cursor cs := by
                              have hv' := hvk
                              rw [hkv2] at hv'
                              cases hv' with
                              | string h => exact h
                            have hmem : Member .strict bs (skipFrom bs (skipFrom bs j + 1))
                                (cs, d.value) d.cursor :=
                              Member.mk hk (skipFrom_space bs k.cursor) hcol
                                (skipFrom_space bs (skipFrom bs k.cursor + 1)) hvd
                            have hbr : SpansOK bs
                                [Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] prev := by
                              simp only [SpansOK, Token.span]
                              refine ⟨?_, by omega, ?_, trivial, trivial⟩
                              · exact Nat.le_trans hprev (skipFrom_ge _ _)
                              · have := (List.getElem?_eq_some_iff.mp hc).1
                                omega
                            have h12 : SpansOK bs
                                ([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                prev := by
                              have h := spansOK_append (bs := bs)
                                [Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] preK prev
                                ⟨hbr, ?_⟩
                              · exact h
                              · simpa [lastStop, Token.span] using hspansK
                            have h2 : SpansOK bs
                                (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                  ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                      skipFrom bs k.cursor + 1⟩]) prev := by
                              have h := spansOK_append (bs := bs)
                                ([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                [Token.punct .colon ⟨skipFrom bs k.cursor,
                                  skipFrom bs k.cursor + 1⟩] prev ⟨h12, ?_⟩
                              · exact h
                              · rw [lastStop_append]
                                simp only [lastStop, Token.span]
                                rw [hlastK']
                                simp only [SpansOK, Token.span]
                                refine ⟨?_, by omega, ?_, trivial, trivial⟩
                                · exact skipFrom_ge _ _
                                · have := (List.getElem?_eq_some_iff.mp hcol).1
                                  omega
                            have h3 : SpansOK bs
                                (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                  ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                      skipFrom bs k.cursor + 1⟩] ++ preV) prev := by
                              have h := spansOK_append (bs := bs)
                                (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                  ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                      skipFrom bs k.cursor + 1⟩]) preV prev ⟨h2, ?_⟩
                              · exact h
                              · rw [lastStop_append]
                                simp only [lastStop, Token.span]
                                exact hspansV
                            have h4 : SpansOK bs
                                (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                  ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                      skipFrom bs k.cursor + 1⟩] ++ preV ++ preT) prev := by
                              have h := spansOK_append (bs := bs)
                                (([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩] ++ preK)
                                  ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                      skipFrom bs k.cursor + 1⟩] ++ preV) preT prev ⟨h3, ?_⟩
                              · exact h
                              · rw [lastStop_append, lastStop_append, lastStop_append]
                                simp only [lastStop, Token.span]
                                rw [hlastV']
                                exact hspansT
                            refine ⟨⟨(([Token.punct .comma ⟨skipFrom bs j, skipFrom bs j + 1⟩]
                                ++ preK) ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                    skipFrom bs k.cursor + 1⟩] ++ preV) ++ preT, ?_, h4, ?_⟩,
                              Or.inr ⟨hc, ?_⟩⟩
                            · simp only [hsplitK, hsplitV, hsplitT, hColon, List.append_assoc,
                                List.cons_append, List.nil_append]
                            · rw [lastStop_append, lastStop_append, lastStop_append, lastStop_append]
                              simp only [lastStop, Token.span]
                              rw [hlastV']
                              exact hlastT
                            · rcases hMsound with ⟨hvs, -, hcur⟩ | ⟨hcomma, he⟩
                              · rw [hvs, hcur]
                                exact Members.last hmem (skipFrom_space bs d.cursor)
                              · exact Members.cons hmem (skipFrom_space bs d.cursor) hcomma
                                  (skipFrom_space bs (skipFrom bs d.cursor + 1)) he
                      · cases hdec
                    · cases hdec
              · cases hdec
            | openBracket => simp [headPunct] at hcm
            | closeBracket => simp [headPunct] at hcm
            | openBrace => simp [headPunct] at hcm
            | closeBrace => simp [headPunct] at hcm
            | colon => simp [headPunct] at hcm
          | null s => simp [headPunct] at hcm
          | bool b s => simp [headPunct] at hcm
          | number s => simp [headPunct] at hcm
          | string s => simp [headPunct] at hcm
        · have hnot : ∀ (c : Span) (rest' : List Token),
              ¬ (tok :: rest = .punct .comma c :: rest') := by
            intro c rest' heq
            have h1 : headPunct .comma (tok :: rest) = true := by
              rw [heq]
              simp [headPunct]
            exact hcm h1
          rw [decodeMembersTail] at hdec <;> (first | exact hnot | skip)
          injection hdec with hd
          subst hd
          exact ⟨⟨[], by simp, trivial, by simp [lastStop]⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- Tape validity.  Any tape the decoder accepts has well-formed spans and names,
against its own input, a text of the accepted language.  The statement quantifies
over every tape, so a tape is valid because its spans check out against the
bytes, not because a parser produced it. -/
theorem tape_valid (t : Tape) (v : Value) (h : decodeTape t = some v) :
    spansWellFormed t = true ∧ ValidDocument t.input v := by
  unfold decodeTape at h
  split at h
  · rename_i d hdec
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hrest, hcursor⟩ := hok
      injection h with hv
      subst hv
      obtain ⟨hV, -, -⟩ := decode_sound_aux t.input t.tokens.length t.tokens rfl
      obtain ⟨hval, pre, hsplit, hspans, -⟩ :=
        hV (skipFrom t.input 0) 0 d (Nat.zero_le _) hdec
      rw [hrest, List.append_nil] at hsplit
      have hspansOK : SpansOK t.input t.tokens 0 := by
        rw [hsplit]
        exact hspans
      refine ⟨?_, ?_⟩
      · unfold spansWellFormed
        exact (spansOK_iff t.input t.tokens 0).mp hspansOK
      · obtain ⟨hrfc, hpol⟩ :=
          valueAt_strict_rfc t.input (skipFrom t.input 0) d.value d.cursor hval
        exact ⟨⟨skipFrom t.input 0, d.cursor, rfl, hrfc, hcursor⟩, hpol⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end LeanLLVM.JSON
