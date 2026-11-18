/-
# The container openers, from the staging

`HcontArm.containerOpen` and `LastEntryArm.containerOpen` are `[` and `{` on the head: both
bytes enter `if.then.i`, and the four head links beside the tail's five reach the merge —
nine links (`containerOpenMerge_at`).  This module produces the arm at every state that
carries the invariant, at both levels, so the `…Domain` wrappers stop building the
constructor by hand out of a document's byte read.

## The cap's arm, and the same two literals

`HcontArm.openAtCap` and `LastEntryArm.openAtCap` are the same two bytes at the stacks'
staged extent: `if.end.i`'s `ugt %sp.i.0248, 519` is taken at `520`, so the run is the
head's four links, `if.then.i`'s call, the guard's true arm and `if.then21.i`'s offset
store — seven links (`containerOpenCap_at`), priced at `7 + 2 ≤ 32`.  Its producers take
`C.sp = 520` in place of `containerOpen`'s `C.sp ≤ 519` and derive the same cells: the
byte's class test, its disjunction, `%idxprom.i`, `%e` and the two document bounds.  The
two arms together are the emitted `ugt` test's two sides, so between them the openers'
depths are covered and neither is the other's residue.

## The class, and the two literals

The census class is one of two bytes, `91` and `123`, and each is an `eq` test on the
head's byte.  So there are two producers per level, one per literal: each takes the
class's own byte test and pins the value with `eq_bit_value`, and the arm's disjunction
`hopen : b = 91 ∨ b = 123` is then *filled* from the pinned byte (`Or.inl`/`Or.inr rfl`)
rather than supplied.  Two producers rather than one at a class disjunction is the shape
the dispatcher can call: `HcontClass`'s `.openBracket`/`.openBrace` constructors each hold
one equality bit, so the eventual consumer holds one of these two premises and not the
disjunction.

## The answer `0`, and the class's totality over the states

`HcontArm.containerOpenRefuse`/`LastEntryArm.containerOpenRefuse` are the same two bytes
when `if.then.i`'s call answers `0`: the branch goes to `if.then16.i`'s offset store and the
copy, six links (`containerOpenRefuse_at`), priced at `6 + 2 ≤ 32`.  Their producers take
the same class test and the call's row at the slot's witness word plus its zero, and derive
the byte, the offset and `%e` from the invariant, exactly as the `1` producers do.  The
answer is always one of the two bits (`s2ValuePos_ret_zero_or_one`), so with these four
producers the class is total over the invariant's states as well as over its bytes.

## What the arm reads, and what it does not

| cell | mark | how the producer has it |
|---|---|---|
| `h8` | **D** | `WalkInv.iter.reg8` is `%8`'s cell and `hlastByte G C` its witness (`cont_reg8`); the class's byte test pins the value (`eq_bit_value`) |
| `hopen` | **D** | the pinned byte: the disjunction's member is the literal the class test names |
| `hsp519` (`C.sp ≤ 519`) | **F-split/boundary** | a named premise.  `WalkInv.depth_cap` gives `C.sp ≤ stage2StackExtent = 520` only, and the block's own `ugt %sp.i, 519` sends `520` to `if.then21.i` instead of this route — a depth selector the invariant does not settle, and the census marks it as the boundary it is |
| `rdv` and `hread` (the root slot's word) | **F** | the call's third argument, as a witness: `WalkInv.root_slot` is the slot's *presence* (`HasBytes`), and the read back is `walkReadBytes_rootSlot_word`'s.  The value is the memory's — `entry` writes `0` and the depth-zero `s2_after_value` writes `1` — so no clause names it and the arm carries it |
| `hpreV`, `r`, `hcall` | (ii) | the callee's staging and outcome at that word: `s2ValuePosPre` at the arm's argument list and the call's result, exactly as the constructor carries them |
| `hret` (`1` or `0`) | (ii) | the answer, and the arm's selector: `1` is `.containerOpen`/`.openAtCap`, `0` is `.containerOpenRefuse`.  `s2ValuePos_ret_zero_or_one` makes the pair total |

So a wrapper supplies the class, the depth boundary, the slot's witness word and the call's
row at it; the byte, its class bits and the disjunction are derived.  The census's row is
confirmed with no correction.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchRefusalsOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing level

Two producers, one per opener byte, and their dispatches. -/

/-- **The open bracket's arm on the continuing head, from the staging.**
`HcontArm.containerOpen` at every state that carries the invariant, the `519` boundary and
the call's own bundle: the byte is the class's value and the disjunction its first
member. -/
def hcontArm_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp519 hread hpreV r hcall hret

/-- **The open brace's arm on the continuing head, from the staging.**  The same nine
links at `NodeBlock17 → LeafBlock13`, with the disjunction's second member. -/
def hcontArm_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp519 hread hpreV r hcall hret

/-- **The open bracket's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpen91_of_staging C s hInv hclass hsp519 hread hpreV r hcall hret)

/-- **The open brace's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpen123_of_staging C s hInv hclass hsp519 hread hpreV r hcall hret)

/-! ### The last entry

The same nine links at the level whose count is exhausted: the arm is the continuing one's
term, and only the dispatch's hypothesis differs. -/

/-- **The open bracket's arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp519 hread hpreV r hcall hret

/-- **The open brace's arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp519 hread hpreV r hcall hret

/-- **The open bracket's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen91_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpen91_of_staging C s hInv hclass hsp519 hread hpreV r hcall hret)

/-- **The open brace's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen123_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpen123_of_staging C s hInv hclass hsp519 hread hpreV r hcall hret)

/-! ### The cap's arm

The same two bytes at the stacks' staged extent.  The push's guard is taken there, so the
run is `if.then.i`'s call, `if.end.i`'s true arm and `if.then21.i`'s offset store — three
blocks after the head's four — and the arm's premise is `C.sp = 520` in place of the
`.containerOpen` route's `C.sp ≤ 519`.  The five cells the refusal reads are the
invariant's: `%8` is `cont_reg8`, `%idxprom.i` is `idx_reg`, `%e` is a static name, and the
two document bounds are the geometry's (`entryPos_le`, `entryPos_lt_64`), so a wrapper
supplies the class's byte test, the depth, the root word and the call. -/

/-- **The open bracket's cap arm on the continuing head, from the staging.** -/
def hcontArm_openAtCap91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .openAtCap (b := BitVec.ofNat 8 91) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp520 hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open brace's cap arm on the continuing head, from the staging.** -/
def hcontArm_openAtCap123_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .openAtCap (b := BitVec.ofNat 8 123) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp520 hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open bracket's cap arm at the last entry, from the staging.** -/
def lastEntryArm_openAtCap91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .openAtCap (b := BitVec.ofNat 8 91) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp520 hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open brace's cap arm at the last entry, from the staging.** -/
def lastEntryArm_openAtCap123_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .openAtCap (b := BitVec.ofNat 8 123) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp520 hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open bracket's cap dispatch on the continuing head, from the staging.** -/
theorem walkDispatch_at_openAtCap91_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_openAtCap91_of_staging C s hInv hclass hsp520 hread hpreV r hcall hret)

/-- **The open brace's cap dispatch on the continuing head, from the staging.** -/
theorem walkDispatch_at_openAtCap123_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_openAtCap123_of_staging C s hInv hclass hsp520 hread hpreV r hcall hret)

/-- **The open bracket's cap dispatch at the last entry, from the staging.** -/
theorem walkDispatch_at_openAtCap91_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_openAtCap91_of_staging C s hInv hclass hsp520 hread hpreV r hcall hret)

/-- **The open brace's cap dispatch at the last entry, from the staging.** -/
theorem walkDispatch_at_openAtCap123_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp520 : C.sp = 520)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_openAtCap123_of_staging C s hInv hclass hsp520 hread hpreV r hcall hret)

/-! ### The answer-`0` arm

The class `91`/`123` also reaches the refusal: when the value-position call answers `0`,
`if.then.i` takes `if.then16.i` and its offset store reaches the copy.  The two producers
per level take the same class test, the call's row at the root slot's witness word, and
its zero; the byte, its class bit, the offset and `%e` are the invariant's, as at the other
openers.  With them and the `1` producers above, the class is total over the invariant's
states as well as over its bytes: the callee's answer is always `0` or `1`. -/

/-- **The open bracket's refusal arm on the continuing head, from the staging.** -/
def hcontArm_containerOpenRefuse91_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpenRefuse (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open brace's refusal arm on the continuing head, from the staging.** -/
def hcontArm_containerOpenRefuse123_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpenRefuse (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open bracket's refusal arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpenRefuse91_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpenRefuse (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open brace's refusal arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpenRefuse123_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpenRefuse (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hread hpreV r hcall hret
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k) (entryPos_lt_64 G C.k)

/-- **The open bracket's refusal dispatch on the continuing head.** -/
theorem walkDispatch_at_containerOpenRefuse91_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpenRefuse91_of_staging C s hInv hclass hread hpreV r hcall hret)

/-- **The open brace's refusal dispatch on the continuing head.** -/
theorem walkDispatch_at_containerOpenRefuse123_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpenRefuse123_of_staging C s hInv hclass hread hpreV r hcall hret)

/-- **The open bracket's refusal dispatch at the last entry.** -/
theorem walkDispatch_at_containerOpenRefuse91_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpenRefuse91_of_staging C s hInv hclass hread hpreV r hcall hret)

/-- **The open brace's refusal dispatch at the last entry.** -/
theorem walkDispatch_at_containerOpenRefuse123_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    {rdv : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpenRefuse123_of_staging C s hInv hclass hread hpreV r hcall hret)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_openAtCap91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_openAtCap123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_openAtCap91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_openAtCap123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_openAtCap91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_openAtCap123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_openAtCap91_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_openAtCap123_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen91_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen123_last_of_staging

end WalkScope
end LeanLLVM.Refinement
