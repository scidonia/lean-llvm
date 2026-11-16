/-
# The standalone string, from the staging

`HcontArm.twoEntry` (`JsonStage2WalkDispatchHcontArms`) is the string opener's class: the
head's byte is `34`, and the token consumes **two** entries — the opener's own and the
closer's — so its merge index is `C.k + 2` and `WalkDispatchResult.ofStringMerge`
(`JsonStage2WalkDispatchWitnessString`) is the arm's composition.  Its bundle is
`HstringFacts`, and its residue `HstringResidue` carries nothing: the two log words the
path reads are `WalkInv`'s `log_dst` and `log_base`, and the accepting-arm selector is
the arm's own field.

This module produces the arm at every state that carries the invariant.

## What is derived, and what is taken

The bundle states the head byte's three class bits, the counts, the next entry's lane,
the two-entry advance's arithmetic, the value-position call's staging, the four cursor
words and the log words.  The first two groups are the invariant's or arithmetic on the
consumer's own guard; the producer derives them:

| row | how |
|---|---|
| `h8` | `cont_reg8_at` at the class's byte (`WalkInv.iter.reg8`) |
| `hlt91`, `hlt44` | `eq_bit_value` from `heq34`, then `decide`: `34` is below both bounds |
| `hinc`, `hnep` | `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row |
| `hcount` | `cont_ult_one` from the consumer's guard `C.k + 1 < G.nep` |
| `ep`, `h5` | `G.ep` and `WalkPtrs`'s positions pointer |
| `q`, `hbs` | `bytesToNat bs` at the lane the read fetched |
| `h4` | `%4`'s `walkStaticRegs` row |
| `hk63`, `hk64` | the entry count's width (`G.nep ≤ 2 ^ 32`) |
| `root`, `hroot` | `%root_done.i`'s `walkStaticRegs` row |
| `ix`, `hix`, `hixPos` | `WalkInv.idx_reg`, whose word is `entryPos G C.k` |
| `ext`, `hext` | the tying equation's arithmetic |
| `hCc` | the capacity read beside `WalkInv.log_acap`: two reads at `%z + 56` are one word |
| `h7` | `WalkIter.reg7` |
| `hnl`, `hnc` | `WalkInv.log_len` and `log_cap` at `%z + 8` and `%z + 16` |

The document's content is taken, each with what supplies it:

| premise | what supplies it |
|---|---|
| `heq34` | **the head byte's class**: `%8 = 34` — the document's byte at the entry's position |
| `bs`, `hreadLane`, `hq` | **the next entry's lane word**: the read at `%5 + (%inc.i)·4` and the word itself, which is the closer's position (`G.ent`) |
| `rd`, `hreadRoot` | **the root-done word's value**: the four bytes at `%root_done.i`, which the run's own store wrote |
| `hsp0` | **the depth split**: `C.sp = 0` selects `if.end245.i`, not the helper's success path |
| `hpreV`, `xv`, `hxv`, `hbranch` | **the value-position call**: its precondition, its answer and the success bit |
| `hcur` | **the cursor pin**: `C.alen ≤ G.ndst0 + ix`, which the loop head's `pending = none` does not carry |
| `A`, `hreadA` | **the log's arena word**: `WalkInv.log_alen` gives the inequality, the word's identity is the memory's |
| `Cc`, `hreadC` | **the log's capacity word's read**: the value is `log_acap`'s, which is what `hCc` derives |
| `hpreS` | **the string body's call**: its precondition at the argument list the walk stages — the staging's, which the tree does not yet produce |
| `hwin` | **the window**: `C.alen + ext ≤ G.n` |
| `y`, `hy` | **the body's answer** |
| `outn`, `houtn` | **the decoded length**: the eight bytes at `%outn.i` |
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLaneOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The standalone string's bundle, from the entry's evidence.**  Produced at the loop's
own witnesses: the head's byte is `hlastByte G C`, the counts are their header values, the
position table is `G.ep`, the entry's index is `contIx G C` and the next entry's lane is
`bytesToNat bs` at the read that fetched it. -/
def hstringFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (heq34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    {bs : List UInt8}
    (hreadLane : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some bs)
    (hq : bytesToNat bs = entryPos G (C.k + 1))
    {rd : BitVec 32}
    (hreadRoot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hsp0 : C.sp = 0)
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {xv : BitVec 32}
    (hxv : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r →
      r.ret = .int 32 xv)
    (hbranch : evalICmp .ne xv (BitVec.ofNat 32 0) = 1)
    (hcur : C.alen ≤ G.ndst0 + (contIx G C).toNat)
    {A : BitVec 64}
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    {Cc : BitVec 64}
    (hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8))
    (hpreS : s2StringBodyPre
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next)
    (hwin : C.alen + (entryPos G (C.k + 1) - (contIx G C).toNat - 1) ≤ G.n)
    {y : BitVec 32}
    (hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r →
      r.ret = .int 32 y)
    {outn : Nat}
    (houtn : readBytes s.mem (G.next0 + 20) 8 = some (wordBytes 8 outn)) :
    HstringFacts G C s := by
  -- the next entry's position, and the two counts' width
  have hq' : bytesToNat bs = entryPos G (C.k + 1) := hq
  have hk63 : C.k + 1 < 2 ^ 63 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hk64 : C.k + 2 < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  -- the capacity word's value: the bundle's read and `log_acap` are one word
  have hCc : natToBytes Cc.toNat 8 = wordBytes 8 G.dstcap := by
    have hword : (some (natToBytes Cc.toNat 8) : Option (List UInt8)) =
        some (wordBytes 8 G.dstcap) := by
      rw [← hreadC, hInv.log_acap]
    exact Option.some.inj hword
  exact
    { x := hlastByte G C
      h8 := cont_reg8_at hInv rfl
      hlt91 := by
        rw [eq_bit_value heq34]; decide
      hlt44 := by
        rw [eq_bit_value heq34]; decide
      heq34 := heq34
      hinc := hInv.inc_reg
      hnep := hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
      hcount := cont_ult_one G C hk
      ep := G.ep
      h5 := hInv.ptrs.2.1
      bs := bs
      hreadLane := hreadLane
      q := bytesToNat bs
      hbs := rfl
      hq := hq'
      h4 := hInv.regs ("%4", .int 64 (BitVec.ofNat 64 G.n)) (by simp [walkStaticRegs])
      hk63 := hk63
      hk64 := hk64
      root := G.next0 + 8
      hroot := hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
      rd := rd
      hreadRoot := hreadRoot
      hsp0 := hsp0
      hpreV := hpreV
      xv := xv
      hxv := hxv
      hbranch := hbranch
      ix := contIx G C
      hix := hInv.idx_reg
      hixPos := contIx_toNat G C hk
      ext := entryPos G (C.k + 1) - (contIx G C).toNat - 1
      hext := rfl
      hcur := hcur
      A := A
      hreadA := hreadA
      Cc := Cc
      hreadC := hreadC
      hCc := hCc
      hpreS := hpreS
      hwin := hwin
      y := y
      hy := hy
      h7 := hInv.iter.reg7
      outn := outn
      houtn := houtn
      hnl := hInv.log_len
      hnc := hInv.log_cap }

/-- **The standalone string's arm, from the staging.**  The bundle's producer, the empty
residue and the arm's own accepting-arm selector. -/
def hcontArm_twoEntry_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (heq34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    {bs : List UInt8}
    (hreadLane : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some bs)
    (hq : bytesToNat bs = entryPos G (C.k + 1))
    {rd : BitVec 32}
    (hreadRoot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hsp0 : C.sp = 0)
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {xv : BitVec 32}
    (hxv : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r →
      r.ret = .int 32 xv)
    (hbranch : evalICmp .ne xv (BitVec.ofNat 32 0) = 1)
    (hcur : C.alen ≤ G.ndst0 + (contIx G C).toNat)
    {A : BitVec 64}
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    {Cc : BitVec 64}
    (hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8))
    (hpreS : s2StringBodyPre
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next)
    (hwin : C.alen + (entryPos G (C.k + 1) - (contIx G C).toNat - 1) ≤ G.n)
    {y : BitVec 32}
    (hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r →
      r.ret = .int 32 y)
    {outn : Nat}
    (houtn : readBytes s.mem (G.next0 + 20) 8 = some (wordBytes 8 outn))
    (hR8 : evalICmp .slt y (BitVec.ofNat 32 1) = 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .twoEntry (hstringFacts_of_staging G C s hInv hk heq34 hreadLane hq hreadRoot hsp0 hpreV
    hxv hbranch hcur hreadA hreadC hpreS hwin hy houtn) {} hR8

/-- **The standalone string's dispatch, from the staging.** -/
theorem walkDispatch_at_twoEntry_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (heq34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    {bs : List UInt8}
    (hreadLane : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some bs)
    (hq : bytesToNat bs = entryPos G (C.k + 1))
    {rd : BitVec 32}
    (hreadRoot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hsp0 : C.sp = 0)
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {xv : BitVec 32}
    (hxv : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r →
      r.ret = .int 32 xv)
    (hbranch : evalICmp .ne xv (BitVec.ofNat 32 0) = 1)
    (hcur : C.alen ≤ G.ndst0 + (contIx G C).toNat)
    {A : BitVec 64}
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    {Cc : BitVec 64}
    (hreadC : readBytes s.mem (C.stage.z + 56) 8 = some (natToBytes Cc.toNat 8))
    (hpreS : s2StringBodyPre
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next)
    (hwin : C.alen + (entryPos G (C.k + 1) - (contIx G C).toNat - 1) ≤ G.n)
    {y : BitVec 32}
    (hy : ∀ r, stage2Calls stage2SubCalls "s2_string_body"
      [.ptr C.stage.c, .ptr (G.b + (contIx G C).toNat + 1),
       .int 64 (BitVec.ofNat 64 (entryPos G (C.k + 1) - (contIx G C).toNat - 1)),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next = some r →
      r.ret = .int 32 y)
    {outn : Nat}
    (houtn : readBytes s.mem (G.next0 + 20) 8 = some (wordBytes 8 outn))
    (hR8 : evalICmp .slt y (BitVec.ofNat 32 1) = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_twoEntry_of_staging G C s hInv hk heq34 hreadLane hq hreadRoot hsp0 hpreV
      hxv hbranch hcur hreadA hreadC hpreS hwin hy houtn hR8)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hstringFacts_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_twoEntry_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_twoEntry_of_staging

end WalkScope
end LeanLLVM.Refinement
