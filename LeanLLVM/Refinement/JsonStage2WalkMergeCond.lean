/-
# The merge's two exit tests, from the carry

`evb_caller_result` takes the accept route's two branches — the depth-zero test
(`%sp.i.1 = 0` at `if.then485.i`) and the root-done word (`%root_done.i ≠ 0` at
`if.end490.i`) — as hypotheses about the merge state.  This module makes them
consequences: it extends `WalkCarry` with the two numbers the tests read, states
the arm carries' computations of them, and proves at `[1]` that the merge's
depth is zero and its root-done word is one.

The two fields are `spm`, the depth the merge's `%sp.i.1` `phi` selects (a
different register per arm: `%inc33.i`, `%sp.i.0248` or `%sub.i`), and `root`,
the four-byte word at `%root_done.i`.  Neither is a function of the carry's
existing fields: the seed and the three arm constructs are what compute them, so
they are carried beside `sp` rather than re-derived at each consumer.

## What is proved

* the extended arm carries — `openC₉M`, `headPassCM`, `scMergeCM`, `closeCEndM`
  — and their projections, plus the bridge `headPassCM C k = headPassC C k C.spm`
  to the head pass the revolution's own step lemma produces;
* `mergeCond_of_chain`: the `[1]` chain's five carry identifications give
  `C₃.spm = 0 ∧ C₃.root = 1` — the two facts the exit branches on;
* `mergeDepth_test` and `mergeRoot_test`: the two `icmp`s are `1` and `0`;
* `hsp0_of_carry` and `hroot0_of_carry`: the two tests follow from the carried
  numbers together with the *readings* — the `phi` operand's value and the
  slot's word — which is the tie the caller's restatement takes in place of the
  test results.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2WalkSpansChain

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seed's two numbers

The loop head has not merged, so the depth the merge will select is the head's
own (`0`), and `entry`'s second store left the root-done slot `0`. -/

theorem walkSeed_spm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).spm = 0 := rfl

theorem walkSeed_root {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).root = 0 := rfl

theorem walkSeed_sp {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).sp = 0 := rfl

/-! ### The opener's head and merge

The head only moves the block.  The merge's depth `phi` selects `%inc33.i`, the
push's `sp + 1`, and the opener's route calls `s2_value_pos`, which does not write
the root slot, so the word is the source's. -/

theorem openHeadC_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (openHeadC C).sp = C.sp := rfl

theorem openHeadC_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (openHeadC C).spm = C.spm := rfl

theorem openHeadC_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (openHeadC C).root = C.root := rfl

/-- **The opener's merge carry**, extended: `%inc33.i` is the selected depth. -/
abbrev openC₉M {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    WalkCarry G :=
  { openC₉ C b with spm := C.sp + 1 }

theorem openC₉M_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).spm = C.sp + 1 := rfl

theorem openC₉M_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).root = C.root := rfl

theorem openC₉M_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).sp = C.sp := rfl

theorem openC₉M_block {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).block = "cleanup478.i" := rfl

theorem openC₉M_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).spans = C.spans := rfl

theorem openC₉M_events {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).events = C.events ++ [EventRecord.tag (ifEnd24St b).toNat] := rfl

theorem openC₉M_stage {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (openC₉M C b).stage = C.stage := rfl

/-! ### The revolution's head pass

The header's `phi` reads the merge's `%sp.i.1`, so the loop head's depth is the
merge's carried `spm`; every other field the two record updates leave alone. -/

/-- **The loop head, extended**: the merge's own depth becomes the head's. -/
abbrev headPassCM {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    WalkCarry G :=
  { { C with block := "while.body.i", inner := walkInnerCap G } with
      block := "NodeBlock21", k := k2, sp := C.spm }

/-- The head pass is the revolution's own at the carry's selected depth. -/
theorem headPassCM_eq_headPassC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    headPassCM C k2 = headPassC C k2 C.spm := rfl

theorem headPassCM_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    (headPassCM C k2).sp = C.spm := rfl

theorem headPassCM_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    (headPassCM C k2).spm = C.spm := rfl

theorem headPassCM_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    (headPassCM C k2).root = C.root := rfl

theorem headPassCM_block {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    (headPassCM C k2).block = "NodeBlock21" := rfl

theorem headPassCM_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (k2 : Nat) :
    (headPassCM C k2).k = k2 := rfl

/-! ### The scalar arm's merge

`%sp.i.1` selects `%sp.i.0248`, the loop head's depth, and the arm's
`s2_after_value` call is made at that same depth: at zero it writes `1` into the
root slot and above zero it writes a stack byte, leaving the slot as it was. -/

/-- **The scalar merge carry**, extended: the depth is the head's and the call
runs at it. -/
abbrev scMergeCM {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { scMergeC C ev with
    spm := C.sp,
    root := if C.sp = 0 then 1 else C.root }

theorem scMergeCM_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).spm = C.sp := rfl

theorem scMergeCM_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).root = (if C.sp = 0 then 1 else C.root) := rfl

/-- **The scalar merge's root word, at the callee's own condition.**  The
after-value call is made at `%sp.i.0248`, whose word is `BitVec.ofNat 32 C.sp`;
`C.sp` is a depth (`WalkInv.depth_cap`), so the word's `.toNat` is the number the
carry's test uses.  This is the bridge from the construction to the word the exit
branches on, and it is where that representation is justified. -/
theorem scMergeCM_root_word {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (ev : EventRecord) (h32 : C.sp < 2 ^ 32) :
    (scMergeCM C ev).root =
      (if (BitVec.ofNat 32 C.sp).toNat = 0 then 1 else C.root) := by
  rw [scMergeCM_root]
  have hto : (BitVec.ofNat 32 C.sp).toNat = C.sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
  rw [hto]

theorem scMergeCM_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).sp = C.sp := rfl

theorem scMergeCM_block {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).block = "cleanup478.i" := rfl

theorem scMergeCM_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).spans = C.spans := rfl

theorem scMergeCM_stage {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    (scMergeCM C ev).stage = C.stage := rfl

/-! ### The closer's merge

`%sp.i.1` selects `%sub.i`, the popped depth, and the arm's `s2_after_value` call
is made at that same word: a closing bracket that pops to zero writes `1`. -/

/-- **The closer's merge carry**, extended: the popped depth and the call at it. -/
abbrev closeCEndM {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : WalkCarry G :=
  { closeCEnd C spz c8 with
    spm := C.sp - 1,
    root := if C.sp - 1 = 0 then 1 else C.root }

theorem closeCEndM_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).spm = C.sp - 1 := rfl

theorem closeCEndM_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).root = (if C.sp - 1 = 0 then 1 else C.root) :=
  rfl

/-- **The closer merge's selected depth, at `%sub.i`'s own word.**  The merge's
`%sp.i.1` incoming is `%sub.i = BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295`;
on the closer's route `C.sp` is a positive depth (`WalkInv.depth_cap`, and the arm's
`C.sp ≠ 0`), so that word's `.toNat` is the constructed `C.sp - 1`.  The `hpos` is
the route's own hypothesis, carried here so the identification is a fact of the
word rather than of the representation. -/
theorem closeCEndM_spm_word {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) (hpos : 0 < C.sp) (h32 : C.sp < 2 ^ 32) :
    (closeCEndM C spz c8).spm =
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat := by
  rw [closeCEndM_spm]
  have hsub := closeSub_eq hpos h32
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- **The closer merge's root word, at the callee's own condition.**  The
after-value call's depth argument is `%sub.i`'s word, so the slot is written `1`
exactly at the word's zero — `C.sp = 1` on this route. -/
theorem closeCEndM_root_word {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) (hpos : 0 < C.sp) (h32 : C.sp < 2 ^ 32) :
    (closeCEndM C spz c8).root =
      (if (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = 0
        then 1 else C.root) := by
  rw [closeCEndM_root]
  have hsub := closeSub_eq hpos h32
  have hto : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hto]

theorem closeCEndM_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).sp = C.sp := rfl

theorem closeCEndM_block {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).block = "cleanup478.i" := rfl

theorem closeCEndM_spans {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).spans = C.spans := rfl

theorem closeCEndM_stage {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (spz : BitVec 32)
    (c8 : BitVec 8) : (closeCEndM C spz c8).stage = C.stage := rfl

/-- The closer's pre-merge carry changes the block only. -/
theorem closeC₁₀b_sp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (closeC₁₀b C).sp = C.sp := rfl

theorem closeC₁₀b_spm {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (closeC₁₀b C).spm = C.spm := rfl

theorem closeC₁₀b_root {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    (closeC₁₀b C).root = C.root := rfl

/-! ### The chain's two numbers

At `[1]` the opener pushes `0 → 1`, the number's merge selects the head's `1`, the
second head pass carries it, and the closer pops `1 → 0` while calling
`s2_after_value` at the popped zero.  So the merge's depth is `0` and its root-done
word is `1`. -/

/-- **The merge's two exit numbers, from the five carry identifications.** -/
theorem mergeCond_of_chain {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {C₁ H₁ C₂ H₂ C₃ : WalkCarry G} {b : BitVec 8} {ev : EventRecord}
    {spz : BitVec 32} {c8 : BitVec 8} {k₁ k₂ : Nat}
    (h₁ : C₁ = openC₉M (openHeadC (walkSeed G S)) b)
    (hH₁ : H₁ = headPassCM C₁ k₁)
    (h₂ : C₂ = scMergeCM H₁ ev)
    (hH₂ : H₂ = headPassCM C₂ k₂)
    (h₃ : C₃ = closeCEndM (closeC₁₀b H₂) spz c8) :
    C₃.spm = 0 ∧ C₃.root = 1 := by
  have hspm₁ : C₁.spm = 1 := by
    rw [h₁, openC₉M_spm, openHeadC_sp, walkSeed_sp]
  have hH₁sp : H₁.sp = 1 := by
    rw [hH₁, headPassCM_sp, hspm₁]
  have hC₂spm : C₂.spm = 1 := by
    rw [h₂, scMergeCM_spm, hH₁sp]
  have hH₂sp : H₂.sp = 1 := by
    rw [hH₂, headPassCM_sp, hC₂spm]
  constructor
  · rw [h₃, closeCEndM_spm, closeC₁₀b_sp, hH₂sp]
  · rw [h₃, closeCEndM_root, closeC₁₀b_sp, hH₂sp]
    simp

/-! ### The two tests

The exit's branches compute their `icmp` from the numbers, so the merge's select
is a consequence of `C₃.spm = 0` and `C₃.root = 1`. -/

/-- The depth-zero test is `1` when the carried depth is zero. -/
theorem mergeDepth_test {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} (h : C.spm = 0) :
    evalICmp .eq (BitVec.ofNat 32 C.spm) (BitVec.ofNat 32 0) = 1 := by
  rw [h]
  decide

/-- The root-done test is `0` when the carried word is `1`. -/
theorem mergeRoot_test {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} (h : C.root = 1) :
    evalICmp .eq (BitVec.ofNat 32 C.root) (BitVec.ofNat 32 0) = 0 := by
  rw [h]
  decide

/-! ### The readings the caller supplies

The two numbers are what the exit *tests*; the merge state's own reading of the
`phi` operand and of the root slot are the tie between the carry and the state.
These are the two equations the caller's restatement takes in place of the test
results. -/

/-- **The depth test at the merge, from the carried depth and the operand's
reading.**  `hspv` is the caller's register fact; `htie` says the operand reads
the carry's `spm`, which is the arm's own arithmetic. -/
theorem hsp0_of_carry {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {spOp : Operand} {spv : Nat}
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (htie : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 C.spm)))
    (hzero : C.spm = 0) :
    evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1 := by
  have hbv : BitVec.ofNat 32 spv = BitVec.ofNat 32 C.spm := by
    have h : (.int 32 (BitVec.ofNat 32 spv) : Value) = .int 32 (BitVec.ofNat 32 C.spm) :=
      Option.some.inj (hspv.symm.trans htie)
    injection h
  rw [hbv, hzero]
  decide

/-- **Equal four-byte words are equal numbers.** -/
theorem mergeCond_natToBytes4_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : natToBytes a 4 = natToBytes b 4) : a = b := by
  have h1 : a % 256 ^ 4 = b % 256 ^ 4 := by
    simpa only [natToBytes_toNat] using congrArg bytesToNat h
  have h256 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [h256, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1

/-- **The root-done test at the merge, from the carried word and the slot's
reading.**  `hread` is the caller's word read; `htie` says the slot holds the
carry's `root`. -/
theorem hroot0_of_carry {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {rv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (htie : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes C.root 4))
    (hroot : C.root = 1) :
    evalICmp .eq rv (BitVec.ofNat 32 0) = 0 := by
  have hbytes : natToBytes rv.toNat 4 = natToBytes C.root 4 :=
    Option.some.inj (hread.symm.trans htie)
  have hrvlt : rv.toNat < 2 ^ 32 := rv.isLt
  have hrootlt : C.root < 2 ^ 32 := by
    rw [hroot]
    decide
  have heq : rv.toNat = C.root := mergeCond_natToBytes4_eq hrvlt hrootlt hbytes
  have hrveq : rv = BitVec.ofNat 32 C.root := by
    apply BitVec.eq_of_toNat_eq
    rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrootlt]
  rw [hrveq, hroot]
  decide

/-! ### Axiom footprints -/

#print axioms mergeCond_of_chain
#print axioms mergeDepth_test
#print axioms mergeRoot_test
#print axioms hsp0_of_carry
#print axioms hroot0_of_carry

end WalkScope
end LeanLLVM.Refinement
