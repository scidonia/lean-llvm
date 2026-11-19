/-
# Which of the whitespace class's rows the tree produces, and what the rest need

`HcontWsRows` (`JsonStage2WalkDispatchWsRows`) states three rows at the class's own
reachable states: the run's own rows at the check state (`run`), the tail's rows at the
class's seam (`tail`), and the traversal's per-index class on the visits' window
(`trav`).  None of the three is a `∀ G` producer, and this module says exactly which part
of each the tree supports and which part is supply.

## The run's row

`run` states

```
∀ C s, WalkInv G C s → C.block = walkLoopHead → C.k + 1 < G.nep →
  evalICmp .slt (hlastByte G C) (ofNat 8 125) = 0 →
  evalICmp .eq (hlastByte G C) (ofNat 8 125) = 0 → ∀ v,
  readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some (natToBytes v.toNat 4) →
  evalICmp .ugt (ofNat 64 v.toNat) (contIx G C) = 1 →
  wsStop G (v.toNat - 1) → HcontRunBody G C (wsCheckS G C s v)
```

The guard is the class's own two clear bits, and it is load-bearing: `HcontRunBody.h8c`
binds `x1` to the seam's `%8`, which at `wsCheckS` is the loop head's (`wsSlAt_env8`,
`contLandS_env8`, `WalkInv.iter.reg8` — `hlastByte G C`), and at a head whose entry byte
is `-` the tag bit cannot clear (`hcontRunBody_dash_false`).  With the guard the two
clauses that were missing from the earlier statement are derived:

* `hbit` — `hlast_bit6_of_class` at the two bits, as in the scan-free producer;
* `hInv` — `WalkInv G (ContAC₄ C) (wsCheckS G C s v)`: the check state's memory is
  `contEndS`'s (two token-record stores past `s.mem`) and its carry is `ContAC₄ C`, and
  the head's eight links produce the invariant (`contPrefixLand`, whose arms the bits
  resolve).

What remains in the field is the document's content, and that is what it supplies:

* `hClass`'s document part — the stop `k`, the per-index class on `[contIx G C, k)`, the
  stop's byte and the budget.  These are the skip's rows, the content
  `HcontClassRows.runSkip` supplies (`HcontRunSkip`); the lane word at `v - 1` says
  nothing about the bytes before it;
* `hspan` — `v.toNat ≤ entryPos G (C.k + 1)`, the entry stream's order.

`hcontRunBody_wsCheck` below is the row's conclusion from exactly the guard, the entry
stream's span and the skip's four document rows; so the field is a supply row for the
document, not a claim stronger than its premises.

## The tail's row

`HcontWsTail` has thirteen fields; three of them are the landing's cell arithmetic and
follow from the byte the landing reads:

* `h47` — `%47` at `landRhs457OutAt` *is* the cell the landing binds, so it is the read's
  number with no hypothesis at all;
* `hbit47`/`hws47` — both comparisons are `9`/`10` on that number, i.e. the document's
  visit byte being a continuing JSON whitespace byte.

`hcontWsTail_of_landing` derives those three from `bytesToNat bs = 9 ∨ bytesToNat bs = 10`
and leaves the rest as supply: the seam's three calls with their literal, the root slot's
word, the appended record, the landing's read and the latch's block-local fact.

## The traversal's row

`trav` states `slt (wsX G (p + 1)) 13 = 1 ∧ ule (wsX G (p + 1) + 247) 1 = 1` on
`[k + 1, v)`.  That is the scan's continuing class — `wsStop`'s *first* disjunct — and
`wsVisit_class_of_byte` reduces it to the document's byte being `9` or `10`.  It is not a
consequence of the stop's own class: `wsStop` at `13` or `32` is the stop's second and
third disjuncts, and `wsVisit_13_false` shows the row's second conjunct fails there.
So the row is the document's content at the visits' window, as the group's own header
says; what the tree contributes is the reduction to the two byte values, and no producer
can supply it at a variable `G`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWsRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The run's own rows at the class's check state

The four missing premises are the class's guard (the head byte's two bits), the entry
stream's order, and the skip's document rows.  Every cell the bundle states is the check
state's own: `%35` is `contLandS_35`, `%idxprom.i` is `contLandS_idx`'s peel plus
`WalkInv.idx_reg`, `%cond350.i` is `contLandS_cond`, and `%8` is `contLandS_env8`'s. -/

/-- **The run's body, from the class's guard, the span and the skip.**  The check state's
invariant is `contPrefixLand`'s endpoint (`contPrefixLand` is the continuing head's eight
links, whose arms the class's bits resolve), and the class conjunct is `wsStop`'s at the
byte before the entry's end plus the skip's rows. -/
noncomputable def hcontRunBody_wsCheck {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) (contIx G C) = 1)
    (hws : wsStop G (v.toNat - 1))
    (k : Nat)
    (hrun : ∀ q, (contIx G C).toNat ≤ q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hik : (contIx G C).toNat < k)
    (hinner : v.toNat - (contIx G C).toNat ≤ C.inner) :
    HcontRunBody G C (wsCheckS G C s v) := by
  -- the head's cells at the succeeding arm
  have hinc : evalOperand (headAS₄ s (hlastByte G C)) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand]
    rw [headAS4_envInc s (hlastByte G C)]
    exact LeanLLVM.evalOperand_reg_of hInv.inc_reg
  have hnep : evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand]
    rw [headAS4_envNep s (hlastByte G C)]
    exact LeanLLVM.evalOperand_reg_of
      (hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs]))
  -- the lane's read, at the succeeding arm's memory
  have hread' : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    have hmem : (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem = s.mem := rfl
    rw [hmem, cont_inc_toNat G C hk]
    exact hread
  -- the stop is inside the entry's end
  have hix : (contIx G C).toNat = entryPos G C.k := contIx_toNat G C hk
  have heicd : k < v.toNat := by
    refine cont_heicd_of (G := G) (C := C) (v := v) (k := k) hk hws ?_ ?_ ?_
    · intro q hq hqk
      exact hrun q (by rw [hix]; exact hq) hqk
    · simpa only [hix] using hik
    · simpa only [contIx] using hugt
  -- the byte before the entry's end is read at `v - 1`, which is inside the document
  have hv1 : 1 ≤ v.toNat := by
    have hk0 : 0 < k := by
      have := Nat.zero_le (contIx G C).toNat
      omega
    omega
  -- the continuing head's eight links: the check state's invariant
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (wsCheckS G C s v) 8 :=
    contPrefixLand (G := G) (C := C) (s := s) hInv hblock
      (x := hlastByte G C)
      (by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        exact LeanLLVM.evalOperand_reg_of hInv.iter.reg8)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      hlt125 hne125
      (inc := hlastIncV C) (nep := hlastNepV G) (ep := G.ep) (v := v)
      hinc hnep (cont_ult_one G C hk)
      (contAS5_env5 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) hInv)
      (cont_hi63 G C hk) hread'
      (ix := contIx G C)
      (contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) (contIx G C) hInv.idx_reg)
      (contAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) (cont_static_tok hInv))
      (contAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])))
      hugt
      (b35 := contB35 G v)
      (cont_hread35 (G := G) (C := C) (s := s) hInv hk (v := v) (k := v.toNat - 1)
        hspan (by omega))
  -- the byte before the entry's end, whitespace: the class's first disjunct
  have hcls : (evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (cont35 (contB35 G v) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1) := by
    have hx : wsX G (v.toNat - 1) = cont35 (contB35 G v) := rfl
    have h := hws
    unfold wsStop at h
    rw [hx] at h
    exact h
  -- the seam's `%8` is the check state's, and the check state's is the loop head's
  have h8c : evalOperand (contWsSeamS C
      (wsSlAt G (wsCheckS G C s v) (contB35 G v) (contIx G C) v k) k (hlastByte G C))
      (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    refine LeanLLVM.evalOperand_reg_of ?_
    simp only [contWsSeamS]
    rw [seamS_env8, wsSlAt_env8, contLandS_env8]
    exact hInv.iter.reg8
  refine
    { hInv := hseg8.inv'
      b35 := contB35 G v
      h35 := by
        simp only [evalOperand]
        exact contLandS_35 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
          (contIx G C) (contB35 G v)
      ix := contIx G C
      hidx := by
        rw [contLandS_idx]
        exact contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) (contIx G C)
          hInv.idx_reg
      v := v
      hcond := contLandS_cond C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
        (contIx G C) (contB35 G v)
      hugt := hugt
      k := k
      x1 := hlastByte G C
      hClass := ⟨hcls, hrun, hstop, hik, hinner, by rw [contIx_toNat G C hk]⟩
      heicd := heicd
      h8c := h8c
      hbit := hlast_bit6_of_class hlt125 hne125
      hspan := hspan }

/-- **The `run` row's conclusion is false at a `-` head**, which is why the row carries
the class's guard: `hlastByte G C` is `WalkInv.iter.reg8`'s cell, and at `45` the seam's
tag test does not clear.  The narrowing this justifies is the field's statement, checked
at the byte rather than argued. -/
theorem hcontRunBody_dash_false :
    ¬ ((evalICmp .eq (BitVec.ofNat 8 45) (BitVec.ofNat 8 45) |||
        evalICmp .ult ((BitVec.ofNat 8 45) + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) := by
  decide

/-! ### The tail's rows, from the landing's byte

`landRhs457OutAt` binds `%47` to `ofNat 8 q` where `q` is the read's number, so the
landing's cell is a definition and its two comparisons are the byte's value.  The rest of
`HcontWsTail` — the seam's three calls, their literal, the root slot's word, the record,
the landing's read and the latch — stays supply. -/

/-- **The tail's rows, reduced to the landing's byte.**  `h47` is the landing's own cell
(`landRhs457OutAt` binds `%47`), and `hbit47`/`hws47` follow from the visited byte being
`9` or `10` — the scan's continuing class.  Everything the seam's callers supply
(`calls`, `hcA`, `hroot`, `ev`, `happ`) and the document's (`hreadS`, `hlatch`) is an
argument, at the states the class's structure names. -/
noncomputable def hcontWsTail_of_landing {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {v : BitVec 32} (b35 : UInt8) (ix : BitVec 64) (k : Nat) (x1 : BitVec 8)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
        b35 k) k x1 x1))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes
      (contWsTailStart C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix
        b35 k) k x1 x1).mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4))
    (ev : EventRecord)
    (happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes)
    {bs : List UInt8}
    (hreadS : readBytes
      (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k)
        k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA).mem
      (G.b + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs)
    (hval : bytesToNat bs = 9 ∨ bytesToNat bs = 10)
    (hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
      (contWsLatch C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k)
        k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA
        (BitVec.ofNat 64 k) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs)))) :
    HcontWsTail G C s v b35 ix k x1 := by
  -- the landing's `%47` is the cell the landing binds
  have h47 : evalOperand
      (landRhs457OutAt
        (contWsEntry C (wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k)
          k x1 x1 calls.r₁ calls.r₂ calls.r₃ k v calls.cA calls.rdv calls.xA)
        (BitVec.ofNat 64 k) G.b (bytesToNat bs)) (.reg "%47") =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [evalOperand, landRhs457OutAt, stateAt, cells]
    rw [lookupName_cons_self]
  -- the byte is `9` or `10`: the scan's continuing class
  have hbit47 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs)) (BitVec.ofNat 8 13) = 1 := by
    rcases hval with h | h <;> rw [h] <;> decide
  have hws47 : evalICmp .ule (BitVec.ofNat 8 (bytesToNat bs) + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 := by
    rcases hval with h | h <;> rw [h] <;> decide
  exact
    { calls := calls
      hcA := hcA
      hroot := hroot
      ev := ev
      happ := happ
      q := bytesToNat bs
      bs := bs
      x47 := BitVec.ofNat 8 (bytesToNat bs)
      hreadS := hreadS
      hbsS := rfl
      h47 := h47
      hbit47 := hbit47
      hws47 := hws47
      hlatch := hlatch }

/-! ### The visits' class, from the document's bytes

`trav`'s conjunction is the scan's continuing class at each index of the visits' window.
The tree contributes the reduction to the byte's value and the negative that the stop's
other two arms do not give it. -/

/-- **A visited byte that is `9` or `10` satisfies the visits' row.**  The two comparisons
are `decide` at the two values; the class's own definition (`wsX`) is the document's byte's
register value. -/
theorem wsVisit_class_of_byte {m0 : Mem} (G : WalkGeom m0) {q : Nat}
    (h : wsByte G q = 9 ∨ wsByte G q = 10) :
    evalICmp .slt (wsX G q) (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (wsX G q + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 := by
  rcases h with h | h
  · rw [wsX, h]; decide
  · rw [wsX, h]; decide

/-- **The stop's `13` arm is not the visits' row.**  At byte `13` the row's second
conjunct is `0`, so `wsStop`'s second disjunct at a visit contradicts the row: the row is
the document's continuing whitespace class, not the stop's class at that index. -/
theorem wsVisit_13_false :
    ¬ (evalICmp .ule ((BitVec.ofNat 8 13) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) := by
  decide

/-! ### The run's segment, from the body the tree produces

The landed counted run is `contWsRunBody` (`JsonStage2WalkRevolution`): from an
`HcontRunBody` it derives the run's segment, its count bound and the stop's
`%cond350.i` cell.  At the body this module produces, that is the row the group's `run`
exists to feed: the segment from the check state to `ContSeamC` is the run's, and the
group does not state it. -/

/-- **The run's segment and price, at the check state the class reaches.**  This is
`contWsRunBody` at `hcontRunBody_wsCheck`'s body: the same premises the row's conclusion
needs, and the conclusion `contWsRunF`/`contWsRunBody` states. -/
theorem contWsRunBody_at_wsCheck {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) (contIx G C) = 1)
    (hws : wsStop G (v.toNat - 1))
    (k : Nat)
    (hrun : ∀ q, (contIx G C).toNat ≤ q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hik : (contIx G C).toNat < k)
    (hinner : v.toNat - (contIx G C).toNat ≤ C.inner) :
    ∃ N, N ≤ 5 * (k - (contIx G C).toNat) + 10 ∧
      WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C) (wsCheckS G C s v) (ContSeamC C)
        (contWsSeamS C (wsSlAt G (wsCheckS G C s v) (contB35 G v) (contIx G C) v k) k
          (hlastByte G C)) N ∧
      lookupName
        (wsSlAt G (wsCheckS G C s v) (contB35 G v) (contIx G C) v k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  let b := hcontRunBody_wsCheck hInv hblock hk hlt125 hne125 hread hspan hugt hws k
    hrun hstop hik hinner
  have hbk : b.k = k := rfl
  have hbix : b.ix = contIx G C := rfl
  have hb35 : b.b35 = contB35 G v := rfl
  have hbv : b.v = v := rfl
  have hbx1 : b.x1 = hlastByte G C := rfl
  obtain ⟨N, hN, hseg, hcond⟩ :=
    contWsRunBody G C (wsCheckS G C s v) b hk
  refine ⟨N, ?_, ?_, ?_⟩
  · rw [hbk, hbix] at hN
    exact hN
  · rw [hb35, hbix, hbv, hbk, hbx1] at hseg
    exact hseg
  · rw [hb35, hbix, hbv, hbk] at hcond
    exact hcond

/-- **The traversal's row, from the document's bytes.**  `trav`'s conjunction at each index
of the visits' window is `wsVisit_class_of_byte`'s at the byte being `9` or `10`, so the
field's whole content is that document row — which no producer can supply at a variable
`G`. -/
theorem hcontWsTravRow_of_bytes {m0 : Mem} (G : WalkGeom m0)
    (h : ∀ (p : Nat) (v : BitVec 32) (k : Nat), k < p + 1 → p + 1 < v.toNat →
      wsByte G (p + 1) = 9 ∨ wsByte G (p + 1) = 10) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → ∀ (v : BitVec 32) (k : Nat) p, k < p + 1 → p + 1 < v.toNat →
      (evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) :=
  fun _ _ _ _ _ v k p hp hpv => wsVisit_class_of_byte G (h p v k hp hpv)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontRunBody_wsCheck
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunBody_dash_false
#print axioms LeanLLVM.Refinement.WalkScope.hcontWsTail_of_landing
#print axioms LeanLLVM.Refinement.WalkScope.wsVisit_class_of_byte
#print axioms LeanLLVM.Refinement.WalkScope.contWsRunBody_at_wsCheck
#print axioms LeanLLVM.Refinement.WalkScope.hcontWsTravRow_of_bytes
#print axioms LeanLLVM.Refinement.WalkScope.wsVisit_13_false

end WalkScope
end LeanLLVM.Refinement
