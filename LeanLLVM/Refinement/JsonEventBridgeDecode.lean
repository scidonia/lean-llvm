/-
The general agreement between the tape's decoders and the token decoders.

The tape decoder (`decodeValue`) carries a byte cursor and checks every token's
span against it; the token decoder (`parseValueTB`) reads each span on its own
and is fuelled by the number of tokens it consumes.  This module states and
proves the agreement between them on a token list whose spans already fit the
cursor: a value's decode result is the token parse's value and remainder, and
the two tail decoders agree the same way.  The statement is over the tape's
input and token list alone, so a consumer comparing two readings of a document
can use it without fixing either reading.

`parseValueTB_decodeValue_agree` is the shared fact: its first conjunct is a
`Decoded` against `parseValueTB` at a fuel covering the consumed prefix, its
second and third are the element and member tails against `parseElemsTB` and
`parseMembersTB`.  The fuel bounds are the arithmetic of those relations — a
value's fuel covers the tokens it consumes, a tail's fuel covers its source
list — and they are maintained because the decoder's `shrunk` and `moved`
fields say each recursive call's source is strictly shorter (or no longer) than
its parent's.

The single non-structural fact the number arm needs is that a run from a
position is a prefix of the bytes from that position (`numRun_spec`); the
string arm needs only that both decoders scan from the same index, which the
tape decoder's span check supplies.

There is no `sorry`, `admit` or `native_decide`; the axiom pin is recorded in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonEventDecode

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The token decoder's value shape

`parseValueTB` produces a string only from a string token, and the code points
it returns are the scan of the span it was given.  The containers' arms need
this inversion to know the token list's head, because the tape decoder checked
the head token's kind before reaching the same list. -/

private theorem parseValueTB_string_inv {bs : Bytes} {n : Nat} {L : List Token}
    {cs : List Nat} {R : List Token}
    (h : parseValueTB bs n L = some (.string cs, R)) :
    ∃ (s : Span), L = .string s :: R ∧
      ∃ stop, scanCharsEnd bs (s.start + 1) 0 = .ok (cs, stop) := by
  cases n with
  | zero => simp only [parseValueTB] at h; simp at h
  | succ n =>
    cases L with
    | nil => simp only [parseValueTB] at h; simp at h
    | cons tok rest =>
      cases tok with
      | punct k s =>
        cases k
        · simp only [parseValueTB] at h; split at h <;> simp at h
        · simp only [parseValueTB] at h; simp at h
        · simp only [parseValueTB] at h; split at h <;> simp at h
        · simp only [parseValueTB] at h; simp at h
        · simp only [parseValueTB] at h; simp at h
        · simp only [parseValueTB] at h; simp at h
      | null s => simp only [parseValueTB] at h; simp at h
      | bool b s => simp only [parseValueTB] at h; simp at h
      | number s => simp only [parseValueTB] at h; simp at h
      | string s =>
        simp only [parseValueTB] at h
        cases hscan : scanCharsEnd bs (s.start + 1) 0 with
        | error e => rw [hscan] at h; simp at h
        | ok p =>
          obtain ⟨cs', stop'⟩ := p
          rw [hscan] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcs, hrest⟩ := h
          cases hcs
          cases hrest
          exact ⟨s, rfl, stop', hscan⟩

/-- The token decoder refuses an empty token list. -/
private theorem parseValueTB_nil (bs : Bytes) (n : Nat) :
    parseValueTB bs n ([] : List Token) = none := by
  rcases n with _ | n
  · rw [parseValueTB.eq_1]
  · rw [parseValueTB.eq_2 bs (n + 1) (by omega)]

/-- The token decoder refuses a list that starts with a closing bracket: the
value grammar has no production for it. -/
private theorem parseValueTB_closeBracket (bs : Bytes) (n : Nat) (s : Span) (rest : List Token) :
    parseValueTB bs n (.punct .closeBracket s :: rest) = none := by
  rcases n with _ | n
  · rw [parseValueTB.eq_1]
  · rw [parseValueTB.eq_9] <;> (first | (intro a b hh; cases hh) | (intro a hh; cases hh) | skip)

/-! ### The decoders agree

The induction's three statements are the three decoders.  The value statement
consumes a decode result and bounds the fuel by the tokens that result leaves
behind; the two tail statements consume a tail whose terminator the enclosing
container's decode matches, so the token decoder's own consumption of that
terminator is the only difference between them. -/

private theorem parseValueTB_decodeValue_agree (bs : Bytes) : ∀ (N : Nat),
    (∀ (L : List Token) (i fuel : Nat) (d : Decoded L), L.length ≤ N →
      decodeValue bs i L = some d →
      fuel + d.rest.length ≥ L.length + 1 →
      parseValueTB bs fuel L = some (d.value, d.rest)) ∧
    (∀ (S : List Token) (j g : Nat) (t : ElemsTail S) (L : List Token) (v : JSON.Value)
        (cb : Span) (ra : List Token), S.length ≤ N →
      decodeElemsTail bs j S = some t →
      t.rest = .punct .closeBracket cb :: ra →
      parseValueTB bs (g - 1) L = some (v, S) →
      g + t.rest.length ≥ S.length + 2 →
      parseElemsTB bs g L = some (v :: t.values, ra)) ∧
    (∀ (S : List Token) (j g : Nat) (t : MembersTail S) (L : List Token)
        (cs : List Nat) (val : JSON.Value) (s sc : Span) (cb : Span) (ra : List Token),
      S.length ≤ N →
      decodeMembersTail bs j S = some t →
      t.rest = .punct .closeBrace cb :: ra →
      (∃ stop, scanCharsEnd bs (s.start + 1) 0 = .ok (cs, stop)) →
      parseValueTB bs (g - 1) L = some (val, S) →
      g + t.rest.length ≥ S.length + 2 →
      parseMembersTB bs g (.string s :: .punct .colon sc :: L) =
        some ((cs, val) :: t.members, ra)) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro L i fuel d hlen hdec hfuel
      rcases L with _ | ⟨tok, rest⟩
      · simp only [decodeValue] at hdec
        cases hdec
      · cases tok with
        | null s =>
          rw [decodeValue.eq_2] at hdec
          split at hdec
          · rename_i hcond
            injection hdec with hd
            subst hd
            simp only [List.length_cons] at hfuel
            cases fuel with
            | zero => omega
            | succ f => simp only [parseValueTB]
          · cases hdec
        | bool b s =>
          rw [decodeValue.eq_3] at hdec
          split at hdec
          · rename_i hb
            subst hb
            split at hdec
            · rename_i hcond
              injection hdec with hd
              subst hd
              simp only [List.length_cons] at hfuel
              cases fuel with
              | zero => omega
              | succ f => simp only [parseValueTB]
            · cases hdec
          · rename_i hb
            have hbf : b = false := by cases b <;> simp_all
            subst hbf
            split at hdec
            · rename_i hcond
              injection hdec with hd
              subst hd
              simp only [List.length_cons] at hfuel
              cases fuel with
              | zero => omega
              | succ f => simp only [parseValueTB]
            · cases hdec
        | number s =>
          rw [decodeValue.eq_4] at hdec
          split at hdec
          · rename_i hcond
            obtain ⟨hs, hlex⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            have htake : (bs.drop s.start).take (s.stop - s.start) = numRunFrom bs i := by
              rw [hs]
              dsimp only
              rw [Nat.add_sub_cancel_left, numRunFrom_eq]
              exact (numRun_spec (bs.drop i)).1
            injection hdec with hd
            subst hd
            simp only [List.length_cons] at hfuel
            cases fuel with
            | zero => omega
            | succ f =>
              simp only [parseValueTB]
              rw [htake]
          · cases hdec
        | string s =>
          rw [decodeValue.eq_5] at hdec
          split at hdec
          · cases hdec
          · rename_i cs' stop' hscan
            split at hdec
            · rename_i hcond
              obtain ⟨hq, hs⟩ := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
              injection hdec with hd
              subst hd
              simp only [List.length_cons] at hfuel
              cases fuel with
              | zero => omega
              | succ f =>
                rw [hs]
                simp only [parseValueTB]
                rw [hscan]
            · cases hdec
        | punct k s =>
          cases k
          · -- `[`
            have nonempty : ∀ (rr : List Token)
                (dd : Decoded (Token.punct .openBracket s :: rr)),
                (Token.punct .openBracket s :: rr).length ≤ N →
                (∀ (c : Span) (r : List Token), rr ≠ .punct .closeBracket c :: r) →
                decodeValue bs i (Token.punct .openBracket s :: rr) = some dd →
                fuel + dd.rest.length ≥ (Token.punct .openBracket s :: rr).length + 1 →
                parseValueTB bs fuel (Token.punct .openBracket s :: rr) =
                  some (dd.value, dd.rest) := by
              intro rr dd hln hnt hdc hfl
              rw [decodeValue.eq_7] at hdc <;> (first | exact hnt | skip)
              split at hdc
              · rename_i hcond
                dsimp only at hdc
                cases hdv : decodeValue bs (skipFrom bs (i + 1)) rr with
                | none => rw [hdv] at hdc; cases hdc
                | some d1 =>
                  rw [hdv] at hdc
                  dsimp only at hdc
                  cases hdt : decodeElemsTail bs d1.cursor d1.rest with
                  | none => rw [hdt] at hdc; cases hdc
                  | some t =>
                    rw [hdt] at hdc
                    dsimp only at hdc
                    split at hdc
                    · rename_i c rest' hC
                      split at hdc
                      · rename_i hcond2
                        injection hdc with hd
                        subst hd
                        simp only [List.length_cons] at hln hfl
                        have hlen1 : rr.length < N := by omega
                        have hmv : t.rest.length ≤ d1.rest.length := t.moved
                        rw [hC] at hmv
                        simp only [List.length_cons] at hmv
                        have hfuel2 : 2 ≤ fuel := by
                          have h2 : d1.rest.length < rr.length := d1.shrunk
                          omega
                        have hfuel1 : (fuel - 2) + d1.rest.length ≥ rr.length + 1 := by
                          rcases fuel with _ | _ | f3 <;> omega
                        have hparse1 := (ih rr.length hlen1).1 rr (skipFrom bs (i + 1))
                          (fuel - 2) d1 (Nat.le_refl _) hdv hfuel1
                        have hltS : d1.rest.length < N := by
                          have hsh := d1.shrunk
                          omega
                        have hfuelE : (fuel - 1) + t.rest.length ≥ d1.rest.length + 2 := by
                          have h1 : t.rest.length = rest'.length + 1 := by rw [hC]; simp
                          have h3 : d1.rest.length < rr.length := d1.shrunk
                          have h4 : 2 ≤ fuel := hfuel2
                          have h5 : fuel + rest'.length ≥ rr.length + 2 := hfl
                          have h6 : rest'.length + 1 ≤ d1.rest.length := hmv
                          clear hfuel hdec hlen hparse1 hfuel1 hltS hlen1 hmv hC hfl hfuel2
                          omega
                        have hres := (ih d1.rest.length hltS).2.1 d1.rest d1.cursor
                          (fuel - 1) t rr d1.value c rest' (Nat.le_refl _) hdt hC hparse1 hfuelE
                        rw [show fuel = (fuel - 1) + 1 from
                          (Nat.sub_add_cancel (by omega : 1 ≤ fuel)).symm]
                        simp only [parseValueTB]
                        rw [hres]
                      · cases hdc
                    · cases hdc
              · cases hdc
            rcases rest with _ | ⟨tok2, rest2⟩
            · exact nonempty [] d hlen (by intro c r hh; cases hh) hdec hfuel
            · cases tok2 with
              | punct k2 s2 =>
                cases k2
                · exact nonempty (.punct .openBracket s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · rw [decodeValue.eq_6] at hdec
                  split at hdec
                  · rename_i hcond
                    injection hdec with hd
                    subst hd
                    simp only [List.length_cons] at hfuel
                    cases fuel with
                    | zero => omega
                    | succ f =>
                      cases f with
                      | zero => omega
                      | succ f2 =>
                        simp only [parseValueTB]
                        rfl
                  · cases hdec
                · exact nonempty (.punct .openBrace s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonempty (.punct .closeBrace s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonempty (.punct .comma s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonempty (.punct .colon s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
              | null s2 =>
                exact nonempty (.null s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | bool b2 s2 =>
                exact nonempty (.bool b2 s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | number s2 =>
                exact nonempty (.number s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | string s2 =>
                exact nonempty (.string s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
          · simp [decodeValue] at hdec
          · -- `{`
            have nonemptyObj : ∀ (rr : List Token)
                (dd : Decoded (Token.punct .openBrace s :: rr)),
                (Token.punct .openBrace s :: rr).length ≤ N →
                (∀ (c : Span) (r : List Token), rr ≠ .punct .closeBrace c :: r) →
                decodeValue bs i (Token.punct .openBrace s :: rr) = some dd →
                fuel + dd.rest.length ≥ (Token.punct .openBrace s :: rr).length + 1 →
                parseValueTB bs fuel (Token.punct .openBrace s :: rr) =
                  some (dd.value, dd.rest) := by
              intro rr dd hln hnt hdc hfl
              rw [decodeValue.eq_9] at hdc <;> (first | exact hnt | skip)
              split at hdc
              · rename_i hcond
                dsimp only at hdc
                cases hdv : decodeValue bs (skipFrom bs (i + 1)) rr with
                | none => rw [hdv] at hdc; cases hdc
                | some k =>
                  rw [hdv] at hdc
                  dsimp only at hdc
                  cases hkv : k.value with
                  | null => rw [hkv] at hdc; cases hdc
                  | bool bb => rw [hkv] at hdc; cases hdc
                  | number l => rw [hkv] at hdc; cases hdc
                  | array vs => rw [hkv] at hdc; cases hdc
                  | object ms => rw [hkv] at hdc; cases hdc
                  | string cs =>
                    rw [hkv] at hdc
                    dsimp only at hdc
                    split at hdc
                    · rename_i sc rest1 hColon
                      split at hdc
                      · rename_i hcondC
                        cases hdd : decodeValue bs
                          (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                        | none => rw [hdd] at hdc; cases hdc
                        | some dv =>
                          rw [hdd] at hdc
                          dsimp only at hdc
                          cases hdt : decodeMembersTail bs dv.cursor dv.rest with
                          | none => rw [hdt] at hdc; cases hdc
                          | some t =>
                            rw [hdt] at hdc
                            dsimp only at hdc
                            split at hdc
                            · rename_i c rest' hC
                              split at hdc
                              · rename_i hcond2
                                injection hdc with hd
                                subst hd
                                simp only [List.length_cons] at hln hfl
                                have hkl : k.rest.length = rest1.length + 1 := by
                                  rw [hColon]; simp
                                have hmvK : t.rest.length ≤ dv.rest.length := t.moved
                                rw [hC] at hmvK
                                simp only [List.length_cons] at hmvK
                                have hshD : dv.rest.length < rest1.length := dv.shrunk
                                have hshK : k.rest.length < rr.length := k.shrunk
                                have hfuel2 : 2 ≤ fuel := by
                                  have h2 : dv.rest.length < rest1.length := dv.shrunk
                                  omega
                                have hfuelk : (fuel - 1) + k.rest.length ≥ rr.length + 1 := by
                                  rcases fuel with _ | f3 <;> omega
                                have hltk : rr.length < N := by omega
                                have hparsek := (ih rr.length hltk).1 rr (skipFrom bs (i + 1))
                                  (fuel - 1) k (Nat.le_refl _) hdv hfuelk
                                rw [hkv] at hparsek
                                obtain ⟨sk, hrestk, stopk, hscank⟩ :=
                                  parseValueTB_string_inv hparsek
                                have hrl : rr.length = rest1.length + 2 := by
                                  rw [hrestk]
                                  simp only [List.length_cons, hkl]
                                have hltv : rest1.length < N := by omega
                                have hfuelv : (fuel - 2) + dv.rest.length ≥ rest1.length + 1 := by
                                  rcases fuel with _ | _ | f3 <;> omega
                                have hparsev := (ih rest1.length hltv).1 rest1
                                  (skipFrom bs (skipFrom bs k.cursor + 1)) (fuel - 2) dv
                                  (Nat.le_refl _) hdd hfuelv
                                have hltS : dv.rest.length < N := by omega
                                have hfuelM : (fuel - 1) + t.rest.length ≥ dv.rest.length + 2 := by
                                  have h1 : t.rest.length = rest'.length + 1 := by rw [hC]; simp
                                  have h2 : dv.rest.length < rest1.length := dv.shrunk
                                  rcases fuel with _ | f3 <;> omega
                                have hres := (ih dv.rest.length hltS).2.2 dv.rest
                                  dv.cursor (fuel - 1) t
                                  rest1 cs dv.value sk sc c rest' (Nat.le_refl _)
                                  hdt hC ⟨stopk, hscank⟩ hparsev hfuelM
                                rw [show fuel = (fuel - 1) + 1 from
                                  (Nat.sub_add_cancel (by omega : 1 ≤ fuel)).symm]
                                simp only [parseValueTB]
                                rw [hrestk, hColon]
                                rw [hres]
                              · cases hdc
                            · cases hdc
                      · cases hdc
                    · cases hdc
              · cases hdc
            rcases rest with _ | ⟨tok2, rest2⟩
            · exact nonemptyObj [] d hlen (by intro c r hh; cases hh) hdec hfuel
            · cases tok2 with
              | punct k2 s2 =>
                cases k2
                · exact nonemptyObj (.punct .openBracket s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonemptyObj (.punct .closeBracket s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonemptyObj (.punct .openBrace s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · rw [decodeValue.eq_8] at hdec
                  split at hdec
                  · rename_i hcond
                    injection hdec with hd
                    subst hd
                    simp only [List.length_cons] at hfuel
                    cases fuel with
                    | zero => omega
                    | succ f =>
                      cases f with
                      | zero => omega
                      | succ f2 =>
                        simp only [parseValueTB]
                        rfl
                  · cases hdec
                · exact nonemptyObj (.punct .comma s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
                · exact nonemptyObj (.punct .colon s2 :: rest2) d hlen
                    (by intro c r hh; cases hh) hdec hfuel
              | null s2 =>
                exact nonemptyObj (.null s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | bool b2 s2 =>
                exact nonemptyObj (.bool b2 s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | number s2 =>
                exact nonemptyObj (.number s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
              | string s2 =>
                exact nonemptyObj (.string s2 :: rest2) d hlen
                  (by intro c r hh; cases hh) hdec hfuel
          · simp [decodeValue] at hdec
          · simp [decodeValue] at hdec
          · simp [decodeValue] at hdec

    · -- the element tail
      intro S j g t L v cb ra hlen hdec hrest hparse hfuel
      have hg1 : 1 ≤ g := by
        rcases g with _ | g'
        · simp only [Nat.zero_sub] at hparse
          simp only [parseValueTB.eq_1] at hparse
          cases hparse
        · omega
      have hgrw : g = (g - 1) + 1 := (Nat.sub_add_cancel hg1).symm
      rcases S with _ | ⟨tok, rest⟩
      · rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
        injection hdec with ht
        subst ht
        cases hrest
      · cases tok with
        | punct k s =>
          cases k
          · rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · -- the closing bracket: the parse's terminator
            rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
            rw [hgrw]
            cases L with
            | nil => rw [parseValueTB_nil] at hparse; cases hparse
            | cons tok' rest' =>
              cases tok' with
              | punct k' s' =>
                cases k'
                · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                  rw [hparse]
                · rw [parseValueTB_closeBracket] at hparse; cases hparse
                · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                  rw [hparse]
                · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                  rw [hparse]
                · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                  rw [hparse]
                · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                  rw [hparse]
              | null s' =>
                rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                simp only [hparse]
              | bool b' s' =>
                rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                simp only [hparse]
              | number s' =>
                rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                simp only [hparse]
              | string s' =>
                rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                simp only [hparse]
          · rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · -- the comma: the recursive branch
            rw [decodeElemsTail.eq_1] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            split at hdec
            · dsimp only at hdec
              cases hdv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
              | none => rw [hdv] at hdec; cases hdec
              | some d =>
                rw [hdv] at hdec
                dsimp only at hdec
                cases hdt : decodeElemsTail bs d.cursor d.rest with
                | none => rw [hdt] at hdec; cases hdec
                | some t_rec =>
                  rw [hdt] at hdec
                  dsimp only at hdec
                  injection hdec with ht
                  subst ht
                  simp only [List.length_cons] at hlen hfuel
                  have hlt1 : rest.length < N := by omega
                  have hmv : t_rec.rest.length ≤ d.rest.length := t_rec.moved
                  have hsh : d.rest.length < rest.length := d.shrunk
                  have hfuel2 : 2 ≤ g := by
                    clear hrest hparse hlen hdt
                    omega
                  have hfuelv : ((g - 1) - 1) + d.rest.length ≥ rest.length + 1 := by
                    clear hrest hparse hdt
                    omega
                  have hparsev := (ih rest.length hlt1).1 rest
                    (skipFrom bs (skipFrom bs j + 1))
                    ((g - 1) - 1) d (Nat.le_refl _) hdv hfuelv
                  have hltS : d.rest.length < N := by omega
                  have hfuelE : (g - 1) + t_rec.rest.length ≥ d.rest.length + 2 := by
                    clear hrest hparse hdt
                    omega
                  have hrec := (ih d.rest.length hltS).2.1 d.rest d.cursor (g - 1) t_rec
                    rest d.value cb ra (Nat.le_refl _) hdt hrest hparsev hfuelE
                  rw [hgrw]
                  cases L with
                  | nil => rw [parseValueTB_nil] at hparse; cases hparse
                  | cons tok' rest' =>
                    cases tok' with
                    | punct k' s' =>
                      cases k'
                      · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                        simp only [hparse, hrec]
                      · rw [parseValueTB_closeBracket] at hparse; cases hparse
                      · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                        simp only [hparse, hrec]
                      · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                        simp only [hparse, hrec]
                      · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                        simp only [hparse, hrec]
                      · rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                        simp only [hparse, hrec]
                    | null s' =>
                      rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                      simp only [hparse, hrec]
                    | bool b' s' =>
                      rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                      simp only [hparse, hrec]
                    | number s' =>
                      rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                      simp only [hparse, hrec]
                    | string s' =>
                      rw [parseElemsTB.eq_4 bs (g - 1) _ _ (by intro s0 hh; cases hh)]
                      simp only [hparse, hrec]
            · cases hdec
          · rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
        | null s =>
          rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | bool b s =>
          rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | number s =>
          rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | string s =>
          rw [decodeElemsTail.eq_2] at hdec <;> (first | (intro s0 r0 hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
    · -- the member tail
      intro S j g t L cs val s sc cb ra hlen hdec hrest hscan hparse hfuel
      obtain ⟨stop, hscan⟩ := hscan
      have hg1 : 1 ≤ g := by
        rcases g with _ | g'
        · simp only [Nat.zero_sub] at hparse
          simp only [parseValueTB.eq_1] at hparse
          cases hparse
        · omega
      have hgrw : g = (g - 1) + 1 := (Nat.sub_add_cancel hg1).symm
      rcases S with _ | ⟨tok, rest⟩
      · rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
        injection hdec with ht
        subst ht
        cases hrest
      · cases tok with
        | punct k s0 =>
          cases k
          · rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
          · -- the closing brace: the parse's terminator
            rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
            rw [hgrw]
            rw [parseMembersTB.eq_4]
            rw [hscan]
            cases L with
            | nil => rw [parseValueTB_nil] at hparse; cases hparse
            | cons v' vs =>
              dsimp only
              simp only [hparse]
          · -- the comma: the recursive branch
            rw [decodeMembersTail.eq_1] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            split at hdec
            · dsimp only at hdec
              cases hdv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
              | none => rw [hdv] at hdec; cases hdec
              | some k =>
                rw [hdv] at hdec
                dsimp only at hdec
                cases hkv : k.value with
                | null => rw [hkv] at hdec; cases hdec
                | bool bb => rw [hkv] at hdec; cases hdec
                | number l => rw [hkv] at hdec; cases hdec
                | array vs => rw [hkv] at hdec; cases hdec
                | object ms => rw [hkv] at hdec; cases hdec
                | string cs2 =>
                  rw [hkv] at hdec
                  dsimp only at hdec
                  split at hdec
                  · rename_i sc2 rest1 hColon
                    split at hdec
                    · cases hdd : decodeValue bs
                        (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                      | none => rw [hdd] at hdec; cases hdec
                      | some d =>
                        rw [hdd] at hdec
                        dsimp only at hdec
                        cases hdt : decodeMembersTail bs d.cursor d.rest with
                        | none => rw [hdt] at hdec; cases hdec
                        | some t_rec =>
                          rw [hdt] at hdec
                          dsimp only at hdec
                          injection hdec with ht
                          subst ht
                          simp only [List.length_cons] at hlen hfuel
                          have hkl : k.rest.length = rest1.length + 1 := by
                            rw [hColon]; simp
                          have hmvK : t_rec.rest.length ≤ d.rest.length := t_rec.moved
                          have hshD : d.rest.length < rest1.length := d.shrunk
                          have hshK : k.rest.length < rest.length := k.shrunk
                          have hfuel2 : 2 ≤ g := by
                            clear hrest hparse hlen hdt hdd hdv hscan
                            omega
                          have hfuelk : (g - 1) + k.rest.length ≥ rest.length + 1 := by
                            clear hrest hparse hlen hdt hdd hscan
                            omega
                          have hltk : rest.length < N := by omega
                          have hparsek := (ih rest.length hltk).1 rest
                            (skipFrom bs (skipFrom bs j + 1))
                            (g - 1) k (Nat.le_refl _) hdv hfuelk
                          rw [hkv] at hparsek
                          obtain ⟨sk, hrestk, stopk, hscank⟩ :=
                            parseValueTB_string_inv hparsek
                          have hrl : rest.length = rest1.length + 2 := by
                            rw [hrestk]; simp only [List.length_cons, hkl]
                          have hltv : rest1.length < N := by omega
                          have hfuelv : ((g - 1) - 1) + d.rest.length ≥
                              rest1.length + 1 := by
                            clear hrest hparse hlen hdt hdd hscan hparsek
                            omega
                          have hparsev := (ih rest1.length hltv).1 rest1
                            (skipFrom bs (skipFrom bs k.cursor + 1)) ((g - 1) - 1) d
                            (Nat.le_refl _) hdd hfuelv
                          have hltS : d.rest.length < N := by omega
                          have hfuelM : (g - 1) + t_rec.rest.length ≥
                              d.rest.length + 2 := by
                            clear hrest hparse hlen hdt hdd hscan hparsek
                            omega
                          have hrec := (ih d.rest.length hltS).2.2 d.rest d.cursor
                            (g - 1) t_rec rest1 cs2 d.value sk sc2 cb ra
                            (Nat.le_refl _) hdt hrest ⟨stopk, hscank⟩ hparsev hfuelM
                          rw [hgrw]
                          rw [parseMembersTB.eq_4]
                          rw [hscan]
                          cases L with
                          | nil => rw [parseValueTB_nil] at hparse; cases hparse
                          | cons v' vs =>
                            dsimp only
                            simp only [hparse]
                            rw [hrestk, hColon]
                            rw [hrec]
                    · cases hdec
                  · cases hdec
            · cases hdec
          · rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
            injection hdec with ht
            subst ht
            cases hrest
        | null s0 =>
          rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | bool b s0 =>
          rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | number s0 =>
          rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest
        | string s0 =>
          rw [decodeMembersTail.eq_2] at hdec <;> (first | (intro a r hh; cases hh) | skip)
          injection hdec with ht
          subst ht
          cases hrest

/-! ### The shared facts

Four facts, separate so that a consumer takes only the one it needs: a value's
decode fixes the token parse's value; the same decode fixes its remainder; and
the two tails relate the tape decoder's element and member tails to the token
side's.  The fuel is a premise in the value facts and in the tails' form; the
two `_at` corollaries instantiate the value facts at the token list's own length
plus one, the fuel a whole-document reading uses. -/

/-- **The token parse's value.**  A value the tape decoder accepts, at a fuel
covering the tokens that result leaves behind, is parsed by `parseValueTB` to
that value. -/
theorem parseValueTB_value {bs : Bytes} {L : List Token} {i fuel : Nat} {d : Decoded L}
    (hdec : decodeValue bs i L = some d)
    (hfuel : fuel + d.rest.length ≥ L.length + 1) :
    ∃ rest : List Token, parseValueTB bs fuel L = some (d.value, rest) :=
  ⟨d.rest, (parseValueTB_decodeValue_agree bs L.length).1 L i fuel d
    (Nat.le_refl _) hdec hfuel⟩

/-- **The token parse's remainder.**  The same decode leaves the token parse at
the same remainder. -/
theorem parseValueTB_remainder {bs : Bytes} {L : List Token} {i fuel : Nat} {d : Decoded L}
    (hdec : decodeValue bs i L = some d)
    (hfuel : fuel + d.rest.length ≥ L.length + 1) :
    ∃ value : JSON.Value, parseValueTB bs fuel L = some (value, d.rest) :=
  ⟨d.value, (parseValueTB_decodeValue_agree bs L.length).1 L i fuel d
    (Nat.le_refl _) hdec hfuel⟩

/-- **The token parse's value at the whole-document fuel.**  The token list's own
length plus one always covers the consumed prefix, so a consumer reading a whole
document need not redo the fuel arithmetic. -/
theorem parseValueTB_value_at {bs : Bytes} {L : List Token} {i : Nat} {d : Decoded L}
    (hdec : decodeValue bs i L = some d) :
    ∃ rest : List Token, parseValueTB bs (L.length + 1) L = some (d.value, rest) :=
  parseValueTB_value hdec (by omega)

/-- **The token parse's remainder at the whole-document fuel.** -/
theorem parseValueTB_remainder_at {bs : Bytes} {L : List Token} {i : Nat} {d : Decoded L}
    (hdec : decodeValue bs i L = some d) :
    ∃ value : JSON.Value, parseValueTB bs (L.length + 1) L = some (value, d.rest) :=
  parseValueTB_remainder hdec (by omega)

/-- **The element tail.**  The token side has parsed a value and the tape
decoder's element tail runs from the same source list; the token side's element
parse then returns that value followed by the tail's values. -/
theorem parseElemsTB_agree {bs : Bytes} {S : List Token} {j g : Nat} {t : ElemsTail S}
    {L : List Token} {v : JSON.Value} {cb : Span} {ra : List Token}
    (hdec : decodeElemsTail bs j S = some t)
    (hrest : t.rest = .punct .closeBracket cb :: ra)
    (hparse : parseValueTB bs (g - 1) L = some (v, S))
    (hfuel : g + t.rest.length ≥ S.length + 2) :
    parseElemsTB bs g L = some (v :: t.values, ra) :=
  (parseValueTB_decodeValue_agree bs S.length).2.1 S j g t L v cb ra
    (Nat.le_refl _) hdec hrest hparse hfuel

/-- **The object tail.**  The token side has parsed a member's value and the tape
decoder's member tail runs from the same source list; the token side's member
parse then returns that member followed by the tail's members. -/
theorem parseMembersTB_agree {bs : Bytes} {S : List Token} {j g : Nat}
    {t : MembersTail S} {L : List Token} {cs : List Nat} {val : JSON.Value}
    {s sc cb : Span} {ra : List Token}
    (hdec : decodeMembersTail bs j S = some t)
    (hrest : t.rest = .punct .closeBrace cb :: ra)
    (hscan : ∃ stop, scanCharsEnd bs (s.start + 1) 0 = .ok (cs, stop))
    (hparse : parseValueTB bs (g - 1) L = some (val, S))
    (hfuel : g + t.rest.length ≥ S.length + 2) :
    parseMembersTB bs g (.string s :: .punct .colon sc :: L) =
      some ((cs, val) :: t.members, ra) :=
  (parseValueTB_decodeValue_agree bs S.length).2.2 S j g t L cs val s sc cb ra
    (Nat.le_refl _) hdec hrest hscan hparse hfuel

/-! ### The shared facts' pins

The footprint belongs to this module: a change that breaks the shared facts
should fail here, not in a consumer's module.  Each pin is the exact message
`#print axioms` reports. -/

/-- info: 'LeanLLVM.Refinement.parseValueTB_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueTB_value

/-- info: 'LeanLLVM.Refinement.parseValueTB_remainder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueTB_remainder

/-- info: 'LeanLLVM.Refinement.parseValueTB_value_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueTB_value_at

/-- info: 'LeanLLVM.Refinement.parseValueTB_remainder_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueTB_remainder_at

/-- info: 'LeanLLVM.Refinement.parseElemsTB_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseElemsTB_agree

/-- info: 'LeanLLVM.Refinement.parseMembersTB_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseMembersTB_agree

end LeanLLVM.Refinement
