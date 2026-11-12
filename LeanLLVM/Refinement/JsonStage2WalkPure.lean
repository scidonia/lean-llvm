/-
The stage-2 walk's remaining pure blocks: class G's `load`-and-compare runs.

`JsonStage2WalkRest` supplies a pure run's three transfers (`WalkLink.pureCore`,
`WalkLink.pureJumpCore`, `WalkLink.pureCoreCarried`), the `%k11.i`-binding variant
`WalkLink.pureJumpK11`, and six links — H1's five `LeafBlock`s and `if.then281.i`.
What it records as not supplied is the *instance work*: writing each block's
outgoing environment so its `denoteCode` equality is a term the transfer consumes.
This module is that work for ten of the census's fourteen G rows.  The other four
(`if.end59.i`, `if.end133.i`, `land.lhs.true.i`, `if.end179.i`) state the same
`denoteCode` equalities, but their declarations do not pass the kernel's
type-checker: with the run written either through `denoteCode_gep8_reg` and
`simpa`/`omega`-built rewrites or through `denoteCode_gep8_ofNat`, the kernel
reports a deep recursion while checking the declaration even though the statement
alone and the proof's individual arguments type-check (measured: `maxRecDepth
50000` does not help, so it is not a depth limit).  They are named as the class's
open rows in the census.

A G block reads a word the invariant does not bind — the two log fields `%len` and
`%cap`, a container-stack byte at the depth's index, a document byte, or the
`%root_done.i` slot — and compares it.  So each instance takes the block's register
and byte hypotheses exactly as class A takes its compared register, states the
`denoteCode` run at the cells the run leaves, and hands the run to its edge's
transfer.  The block writes no memory and binds no carried register, so the memory,
`pc` and carried clauses are the run's own.

The four jump-shaped reads (`cond.true345.i`, `cond.true.i106`,
`land.lhs.true357.i`, `if.then231.i`) leave by `br` and are `pureJumpCore`;
`if.end74.i` branches on the bit `if.end59.i` computed, so it is
`pureCoreCarried`; the rest branch on a bit they computed themselves and are
`pureCore`.

One step lemma is not in `BlockEval`: a `getelementptr i32` at a register index
(the two `%arrayidx` reads of the entry stream).  `denoteCode_gep32_reg` below is
that step at a `stateAt` environment, in the shape the chains use.
-/
import LeanLLVM.Refinement.JsonStage2WalkRest

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### The scaled `getelementptr` at a register index -/

/-- `%d = getelementptr i32, ptr %base, i64 %off`: the scaled step at a built
environment. -/
theorem evalInstr_gep32_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {o : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 o)) (h : o.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 32) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + o.toNat * 4)) :: env) s) := by
  have h2 : o.toNat < 9223372036854775808 := by
    rw [show (9223372036854775808 : Nat) = 2 ^ 63 from by decide]; exact h
  simp [stateAt, State.bind, evalInstr, evalOperand, hb, ho, h2, Ty.sizeBytes]

theorem denoteCode_gep32_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {o : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 o)) (h : o.toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 32) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + o.toNat * 4)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_gep32_reg calls env s d base off hb ho h)]

/-- A comparison against an immediate at any predicate and width: `BlockEval`'s
`denoteCode_icmp_ult_imm` is the 64-bit `ult` case of this. -/
theorem denoteCode_icmp_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    (p : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d p w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)])]
  simp only [stateAt, State.bind]

/-! ### The event reserves' two tests

`if.end.i.i` and `if.end.i.i55` read the log's length and capacity words and test
`len + 1 > cap`; their two edges are the trap and the tag byte's store.  The reads
are the invariant's own (`log_len`, `log_cap`) read at `%len`/`%cap`, which the
caller supplies as the staging's two pointers. -/

/-- `if.end.i.i`: the tag byte's reserve test. -/
def walkIf_end_i_i : Block :=
  { name := "if.end.i.i",
    instrs := [
      Instr.load "%o.val.i.i" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%o.val11.i.i" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i.i.i" BinOp.add 64 (Operand.reg "%o.val.i.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i" IPred.ugt 64 (Operand.reg "%add.i.i.i") (Operand.reg "%o.val11.i.i")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i.i.i") "if.end.i.i.i" "out_reserve.exit.i.i" }

theorem walkIf_end_i_i_find : stage2Body.findBlock "if.end.i.i" = some walkIf_end_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end_i_i]

/-- **`if.end.i.i` as a link**: the reserve's test at the invariant's two log words. -/
theorem WalkLink.if_end_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i.i")
    {al ac : Nat} {nl nc : BitVec 64}
    (hlen : lookupName s.env "%len" = some (.ptr al))
    (hcap : lookupName s.env "%cap" = some (.ptr ac))
    (hreadL : readBytes s.mem al 8 = some (natToBytes nl.toNat 8))
    (hreadC : readBytes s.mem ac 8 = some (natToBytes nc.toNat 8)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 1
          then "if.end.i.i.i" else "out_reserve.exit.i.i") } s' := by
  have hden : denoteCode calls walkIf_end_i_i.instrs s =
      some (stateAt (cells
        [("%cmp.not.i.i.i", .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
         ("%add.i.i.i", .int 64 (nl + BitVec.ofNat 64 1)),
         ("%o.val11.i.i", .int 64 nc),
         ("%o.val.i.i", .int 64 nl)] s.env) s) := by
    simp only [walkIf_end_i_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load64 (calls := calls) (env := s.env) (s := s) (d := "%o.val.i.i")
      (p := "%len") (a := al) (v := nl) hlen hreadL]
    rw [denoteCode_load64 (calls := calls)
      (env := ("%o.val.i.i", .int 64 nl) :: s.env) (s := s)
      (d := "%o.val11.i.i") (p := "%cap") (a := ac) (v := nc) hcap hreadC]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%o.val11.i.i", .int 64 nc) :: ("%o.val.i.i", .int 64 nl) :: s.env) (s := s)
      (d := "%add.i.i.i") (a := "%o.val.i.i") (w := 64) (x := nl) (c := BitVec.ofNat 64 1)
      (by simp [lookupName])]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%add.i.i.i", .int 64 (nl + BitVec.ofNat 64 1)) ::
        ("%o.val11.i.i", .int 64 nc) :: ("%o.val.i.i", .int 64 nl) :: s.env) (s := s)
      (d := "%cmp.not.i.i.i") (a := "%add.i.i.i") (b := "%o.val11.i.i") IPred.ugt 64
      (x := nl + BitVec.ofNat 64 1) (y := nc)
      (by simp [lookupName]) (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end_i_i) (by rw [hblock]; exact walkIf_end_i_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)
    (by simp [stateAt, cells]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end.i.i55`: the second tag byte's reserve test. -/
def walkIf_end_i_i55 : Block :=
  { name := "if.end.i.i55",
    instrs := [
      Instr.load "%o.val.i.i56" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%o.val11.i.i57" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i.i.i58" BinOp.add 64 (Operand.reg "%o.val.i.i56") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i59" IPred.ugt 64 (Operand.reg "%add.i.i.i58") (Operand.reg "%o.val11.i.i57")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i.i.i59") "if.end.i.i.i64" "out_reserve.exit.i.i60" }

theorem walkIf_end_i_i55_find :
    stage2Body.findBlock "if.end.i.i55" = some walkIf_end_i_i55 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end_i_i55]

/-- **`if.end.i.i55` as a link.** -/
theorem WalkLink.if_end_i_i55 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i.i55")
    {al ac : Nat} {nl nc : BitVec 64}
    (hlen : lookupName s.env "%len" = some (.ptr al))
    (hcap : lookupName s.env "%cap" = some (.ptr ac))
    (hreadL : readBytes s.mem al 8 = some (natToBytes nl.toNat 8))
    (hreadC : readBytes s.mem ac 8 = some (natToBytes nc.toNat 8)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 1
          then "if.end.i.i.i64" else "out_reserve.exit.i.i60") } s' := by
  have hden : denoteCode calls walkIf_end_i_i55.instrs s =
      some (stateAt (cells
        [("%cmp.not.i.i.i59", .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
         ("%add.i.i.i58", .int 64 (nl + BitVec.ofNat 64 1)),
         ("%o.val11.i.i57", .int 64 nc),
         ("%o.val.i.i56", .int 64 nl)] s.env) s) := by
    simp only [walkIf_end_i_i55]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load64 (calls := calls) (env := s.env) (s := s) (d := "%o.val.i.i56")
      (p := "%len") (a := al) (v := nl) hlen hreadL]
    rw [denoteCode_load64 (calls := calls)
      (env := ("%o.val.i.i56", .int 64 nl) :: s.env) (s := s)
      (d := "%o.val11.i.i57") (p := "%cap") (a := ac) (v := nc) hcap hreadC]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%o.val11.i.i57", .int 64 nc) :: ("%o.val.i.i56", .int 64 nl) :: s.env) (s := s)
      (d := "%add.i.i.i58") (a := "%o.val.i.i56") (w := 64) (x := nl) (c := BitVec.ofNat 64 1)
      (by simp [lookupName])]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%add.i.i.i58", .int 64 (nl + BitVec.ofNat 64 1)) ::
        ("%o.val11.i.i57", .int 64 nc) :: ("%o.val.i.i56", .int 64 nl) :: s.env) (s := s)
      (d := "%cmp.not.i.i.i59") (a := "%add.i.i.i58") (b := "%o.val11.i.i57") IPred.ugt 64
      (x := nl + BitVec.ofNat 64 1) (y := nc)
      (by simp [lookupName]) (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end_i_i55) (by rw [hblock]; exact walkIf_end_i_i55_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)
    (by simp [stateAt, cells]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end59.i`: the depth's index, the two container stacks' bytes at it, and the
pair's comparison.  `%sub.i` is `%sp - 1`, `%idxprom65.i` its zero-extension, and
`%conv64.i` the expected marker (1 when the document byte is `}`, 2 otherwise). -/
def walkIf_end59_i : Block :=
  { name := "if.end59.i",
    instrs := [
      Instr.binop "%sub.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.icmp "%cmp61.i" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 125))),
      Instr.select "%conv64.i" (Ty.int 32) (Operand.reg "%cmp61.i") (Operand.imm (.int 32 (BitVec.ofNat 32 1))) (Operand.imm (.int 32 (BitVec.ofNat 32 2))),
      Instr.zext "%idxprom65.i" 32 64 (Operand.reg "%sub.i"),
      Instr.gep "%arrayidx66.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom65.i"),
      Instr.load "%14" (Ty.int 8) (Operand.reg "%arrayidx66.i"),
      Instr.zext "%conv67.i" 8 32 (Operand.reg "%14"),
      Instr.icmp "%cmp69.not.i" IPred.eq 32 (Operand.reg "%conv64.i") (Operand.reg "%conv67.i")
    ],
    term := Term.condbr (Operand.reg "%cmp69.not.i") "if.end74.i" "if.then71.i" }

theorem walkIf_end59_i_find : stage2Body.findBlock "if.end59.i" = some walkIf_end59_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end59_i]

/-- A one-byte read's `BitVec 8` value is its `Nat` value below `256`. -/
theorem walkToNat_ofNat8 {j : Nat} (hj : j < 256) : (BitVec.ofNat 8 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

/-- `if.end74.i`: `%cst.i`'s byte at the depth index, then a branch on the bit
`if.end59.i` computed. -/
def walkIf_end74_i : Block :=
  { name := "if.end74.i",
    instrs := [
      Instr.gep "%arrayidx76.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom65.i"),
      Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx76.i")
    ],
    term := Term.condbr (Operand.reg "%cmp61.i") "cond.true.i" "cond.end.i" }

theorem walkIf_end74_i_find : stage2Body.findBlock "if.end74.i" = some walkIf_end74_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end74_i]

/-- **`if.end74.i` as a link**: the read is pure, and the edge is `if.end59.i`'s
own comparison, carried rather than recomputed. -/
theorem WalkLink.if_end74_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end74.i")
    {cs : Nat} {q : Nat} {b : UInt8} {bit : BitVec 1}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom65.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63)
    (hread : readBytes s.mem (cs + q) 1 = some [b])
    (hbit : lookupName s.env "%cmp61.i" = some (.int 1 bit)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if bit = 1 then "cond.true.i" else "cond.end.i") } s' := by
  have hden : denoteCode calls walkIf_end74_i.instrs s =
      some (stateAt (cells
        [("%15", .int 8 (BitVec.ofNat 8 b.toNat)),
         ("%arrayidx76.i", .ptr (cs + q))] s.env) s) := by
    simp only [walkIf_end74_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx76.i")
      (base := "%cst.i") (off := "%idxprom65.i") (a := cs)
      (idx := BitVec.ofNat 64 q) hcs hidx (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx76.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%15") (p := "%arrayidx76.i") (a := cs + q)
      (by simp [lookupName]) hread]
    rfl
  exact WalkLink.pureCoreCarried (G := G) (C := C) (s := s) hInv
    (B := walkIf_end74_i) (by rw [hblock]; exact walkIf_end74_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (bit := bit) hbit
    (by unfold walkSkips; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end133.i`: the two stacks' bytes at `%sp - 1` and the marker's test. -/
def walkIf_end133_i : Block :=
  { name := "if.end133.i",
    instrs := [
      Instr.binop "%sub135.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom136.i" 32 64 (Operand.reg "%sub135.i"),
      Instr.gep "%arrayidx137.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom136.i"),
      Instr.load "%21" (Ty.int 8) (Operand.reg "%arrayidx137.i"),
      Instr.icmp "%cmp139.i" IPred.eq 8 (Operand.reg "%21") (Operand.imm (.int 8 (BitVec.ofNat 8 1))),
      Instr.gep "%arrayidx143.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom136.i"),
      Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx143.i")
    ],
    term := Term.condbr (Operand.reg "%cmp139.i") "if.then141.i" "if.else153.i" }

theorem walkIf_end133_i_find : stage2Body.findBlock "if.end133.i" = some walkIf_end133_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end133_i]

/-- `land.lhs.true.i`: `%ctype.i`'s byte at `%sp - 1`, tested for the nest's
marker. -/
def walkLand_lhs_true_i : Block :=
  { name := "land.lhs.true.i",
    instrs := [
      Instr.binop "%sub225.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom226.i" 32 64 (Operand.reg "%sub225.i"),
      Instr.gep "%arrayidx227.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom226.i"),
      Instr.load "%27" (Ty.int 8) (Operand.reg "%arrayidx227.i"),
      Instr.icmp "%cmp229.i" IPred.eq 8 (Operand.reg "%27") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp229.i") "if.then231.i" "if.end245.i" }

theorem walkLand_lhs_true_i_find :
    stage2Body.findBlock "land.lhs.true.i" = some walkLand_lhs_true_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_lhs_true_i]

/-- `lor.lhs.false.i`: `%cst.i`'s byte at the depth index `if.end179.i` left, tested
for the block's marker. -/
def walkLor_lhs_false_i : Block :=
  { name := "lor.lhs.false.i",
    instrs := [
      Instr.gep "%arrayidx188.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom182.i"),
      Instr.load "%24" (Ty.int 8) (Operand.reg "%arrayidx188.i"),
      Instr.icmp "%cmp190.not.i" IPred.eq 8 (Operand.reg "%24") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp190.not.i") "if.end195.i" "if.then192.i" }

theorem walkLor_lhs_false_i_find :
    stage2Body.findBlock "lor.lhs.false.i" = some walkLor_lhs_false_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLor_lhs_false_i]

/-- **`lor.lhs.false.i` as a link.** -/
theorem WalkLink.lor_lhs_false_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "lor.lhs.false.i")
    {cs q : Nat} {b : UInt8}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom182.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (cs + q) 1 = some [b]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
          then "if.end195.i" else "if.then192.i") } s' := by
  have hden : denoteCode calls walkLor_lhs_false_i.instrs s =
      some (stateAt (cells
        [("%cmp190.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1))),
         ("%24", .int 8 (BitVec.ofNat 8 b.toNat)),
         ("%arrayidx188.i", .ptr (cs + q))] s.env) s) := by
    simp only [walkLor_lhs_false_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx188.i")
      (base := "%cst.i") (off := "%idxprom182.i") (a := cs) (idx := BitVec.ofNat 64 q)
      hcs hidx (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx188.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%24") (p := "%arrayidx188.i") (a := cs + q) (by simp [lookupName]) hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%24", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx188.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%cmp190.not.i") (a := "%24") 8 (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 1) (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkLor_lhs_false_i) (by rw [hblock]; exact walkLor_lhs_false_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1))
    (by simp [stateAt, cells]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end179.i`: `%ctype.i`'s byte at `%sp - 1`, tested for the nest's marker. -/
def walkIf_end179_i : Block :=
  { name := "if.end179.i",
    instrs := [
      Instr.binop "%sub181.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom182.i" 32 64 (Operand.reg "%sub181.i"),
      Instr.gep "%arrayidx183.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom182.i"),
      Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx183.i"),
      Instr.icmp "%cmp185.not.i" IPred.eq 8 (Operand.reg "%23") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp185.not.i") "lor.lhs.false.i" "if.then192.i" }

theorem walkIf_end179_i_find : stage2Body.findBlock "if.end179.i" = some walkIf_end179_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end179_i]

/-- `if.then231.i`: `%cst.i`'s byte at the depth index, masked against the two
container kinds. -/
def walkIf_then231_i : Block :=
  { name := "if.then231.i",
    instrs := [
      Instr.gep "%arrayidx235.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom226.i"),
      Instr.load "%28" (Ty.int 8) (Operand.reg "%arrayidx235.i"),
      Instr.binop "%29" BinOp.and 8 (Operand.reg "%28") (Operand.imm (.int 8 (BitVec.ofNat 8 251))),
      Instr.icmp "%or.cond.i" IPred.eq 8 (Operand.reg "%29") (Operand.imm (.int 8 (BitVec.ofNat 8 0)))
    ],
    term := Term.br "if.end245.i" }

theorem walkIf_then231_i_find : stage2Body.findBlock "if.then231.i" = some walkIf_then231_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then231_i]

/-- **`if.then231.i` as a link.** -/
theorem WalkLink.if_then231_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then231.i")
    {cs q : Nat} {b : UInt8}
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hidx : lookupName s.env "%idxprom226.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (cs + q) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "if.end245.i" } s' := by
  have hden : denoteCode calls walkIf_then231_i.instrs s =
      some (stateAt (cells
        [("%or.cond.i", .int 1 (evalICmp .eq
            (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251) (BitVec.ofNat 8 0))),
         ("%29", .int 8 (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251)),
         ("%28", .int 8 (BitVec.ofNat 8 b.toNat)),
         ("%arrayidx235.i", .ptr (cs + q))] s.env) s) := by
    simp only [walkIf_then231_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx235.i")
      (base := "%cst.i") (off := "%idxprom226.i") (a := cs) (idx := BitVec.ofNat 64 q)
      hcs hidx (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%28") (p := "%arrayidx235.i") (a := cs + q) (by simp [lookupName]) hread]
    rw [denoteCode_and_imm_w (calls := calls)
      (env := ("%28", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%29") (a := "%28") (w := 8) (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 251) (by simp [lookupName])]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%29", .int 8 (BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251)) ::
        ("%28", .int 8 (BitVec.ofNat 8 b.toNat)) ::
        ("%arrayidx235.i", .ptr (cs + q)) :: s.env) (s := s)
      (d := "%or.cond.i") (a := "%29") 8
      (x := BitVec.ofNat 8 b.toNat &&& BitVec.ofNat 8 251) (c := BitVec.ofNat 8 0)
      (by simp [lookupName])]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_then231_i) (by rw [hblock]; exact walkIf_then231_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (by simp [WalkLocal])

/-- `cond.true345.i`: the next entry's stream lane, zero-extended. -/
def walkCond_true345_i : Block :=
  { name := "cond.true345.i",
    instrs := [
      Instr.gep "%arrayidx346.i" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%inc.i"),
      Instr.load "%34" (Ty.int 32) (Operand.reg "%arrayidx346.i"),
      Instr.zext "%conv347.i" 32 64 (Operand.reg "%34")
    ],
    term := Term.br "cond.end349.i" }

theorem walkCond_true345_i_find :
    stage2Body.findBlock "cond.true345.i" = some walkCond_true345_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_true345_i]

/-- **`cond.true345.i` as a link.** -/
theorem WalkLink.cond_true345_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.true345.i")
    {ep : Nat} {i : BitVec 64} {v : BitVec 32}
    (h5 : lookupName s.env "%5" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.i" = some (.int 64 i))
    (hi63 : i.toNat < 2 ^ 63)
    (hread : readBytes s.mem (ep + i.toNat * 4) 4 = some (natToBytes v.toNat 4)) :
    ∃ s', WalkLink calls G C s { C with block := "cond.end349.i" } s' := by
  have hden : denoteCode calls walkCond_true345_i.instrs s =
      some (stateAt (cells
        [("%conv347.i", .int 64 (BitVec.ofNat 64 v.toNat)),
         ("%34", .int 32 v),
         ("%arrayidx346.i", .ptr (ep + i.toNat * 4))] s.env) s) := by
    simp only [walkCond_true345_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep32_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx346.i")
      (base := "%5") (off := "%inc.i") (a := ep) (o := i) h5 hinc hi63]
    rw [denoteCode_load_i32 (calls := calls)
      (env := ("%arrayidx346.i", .ptr (ep + i.toNat * 4)) :: s.env) (s := s)
      (d := "%34") (p := "%arrayidx346.i") (a := ep + i.toNat * 4) (v := v)
      (by simp [lookupName]) hread]
    rw [denoteCode_zext (calls := calls)
      (env := ("%34", .int 32 v) :: ("%arrayidx346.i", .ptr (ep + i.toNat * 4)) :: s.env)
      (s := s) (d := "%conv347.i") (v := "%34") 32 64 (x := v) (by simp [lookupName])]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkCond_true345_i) (by rw [hblock]; exact walkCond_true345_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (by simp [WalkLocal])

/-- `cond.true.i106`: the string scan's bound lane, zero-extended. -/
def walkCond_true_i106 : Block :=
  { name := "cond.true.i106",
    instrs := [
      Instr.gep "%arrayidx.i108" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%inc.i"),
      Instr.load "%39" (Ty.int 32) (Operand.reg "%arrayidx.i108"),
      Instr.zext "%conv.i" 32 64 (Operand.reg "%39")
    ],
    term := Term.br "cond.end.i96" }

theorem walkCond_true_i106_find :
    stage2Body.findBlock "cond.true.i106" = some walkCond_true_i106 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_true_i106]

/-- **`cond.true.i106` as a link.** -/
theorem WalkLink.cond_true_i106 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.true.i106")
    {ep : Nat} {i : BitVec 64} {v : BitVec 32}
    (h5 : lookupName s.env "%5" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.i" = some (.int 64 i))
    (hi63 : i.toNat < 2 ^ 63)
    (hread : readBytes s.mem (ep + i.toNat * 4) 4 = some (natToBytes v.toNat 4)) :
    ∃ s', WalkLink calls G C s { C with block := "cond.end.i96" } s' := by
  have hden : denoteCode calls walkCond_true_i106.instrs s =
      some (stateAt (cells
        [("%conv.i", .int 64 (BitVec.ofNat 64 v.toNat)),
         ("%39", .int 32 v),
         ("%arrayidx.i108", .ptr (ep + i.toNat * 4))] s.env) s) := by
    simp only [walkCond_true_i106]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep32_reg (calls := calls) (env := s.env) (s := s) (d := "%arrayidx.i108")
      (base := "%5") (off := "%inc.i") (a := ep) (o := i) h5 hinc hi63]
    rw [denoteCode_load_i32 (calls := calls)
      (env := ("%arrayidx.i108", .ptr (ep + i.toNat * 4)) :: s.env) (s := s)
      (d := "%39") (p := "%arrayidx.i108") (a := ep + i.toNat * 4) (v := v)
      (by simp [lookupName]) hread]
    rw [denoteCode_zext (calls := calls)
      (env := ("%39", .int 32 v) :: ("%arrayidx.i108", .ptr (ep + i.toNat * 4)) :: s.env)
      (s := s) (d := "%conv.i") (v := "%39") 32 64 (x := v) (by simp [lookupName])]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkCond_true_i106) (by rw [hblock]; exact walkCond_true_i106_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (by simp [WalkLocal])

/-- `land.lhs.true357.i`: the document byte at the scan's bound. -/
def walkLand_lhs_true357_i : Block :=
  { name := "land.lhs.true357.i",
    instrs := [
      Instr.gep "%gep" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%cond350.i"),
      Instr.load "%35" (Ty.int 8) (Operand.reg "%gep")
    ],
    term := Term.br "NodeBlock41" }

theorem walkLand_lhs_true357_i_find :
    stage2Body.findBlock "land.lhs.true357.i" = some walkLand_lhs_true357_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_lhs_true357_i]

/-- **`land.lhs.true357.i` as a link.** -/
theorem WalkLink.land_lhs_true357_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.lhs.true357.i")
    {ig q : Nat} {b : UInt8}
    (hig : lookupName s.env "%invariant.gep" = some (.ptr ig))
    (hcond : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (ig + q) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock41" } s' := by
  have hden : denoteCode calls walkLand_lhs_true357_i.instrs s =
      some (stateAt (cells
        [("%35", .int 8 (BitVec.ofNat 8 b.toNat)),
         ("%gep", .ptr (ig + q))] s.env) s) := by
    simp only [walkLand_lhs_true357_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s) (d := "%gep")
      (base := "%invariant.gep") (off := "%cond350.i") (a := ig) (idx := BitVec.ofNat 64 q)
      hig hcond (by rw [sExt_ofNat64 hq63]; exact hq63)]
    rw [sExt_ofNat64 hq63]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%gep", .ptr (ig + q)) :: s.env) (s := s)
      (d := "%35") (p := "%gep") (a := ig + q) (by simp [lookupName]) hread]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkLand_lhs_true357_i) (by rw [hblock]; exact walkLand_lhs_true357_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl (by simp [WalkLocal])

/-- `if.end.i97`: the byte after the string scan's end, tested against `-` and the
digit range. -/
def walkIf_end_i97 : Block :=
  { name := "if.end.i97",
    instrs := [
      Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx10.i"),
      Instr.icmp "%cmp11.i" IPred.eq 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%42" BinOp.add 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond.i98" IPred.ult 8 (Operand.reg "%42") (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond127.i" BinOp.or 1 (Operand.reg "%cmp11.i") (Operand.reg "%or.cond.i98")
    ],
    term := Term.condbr (Operand.reg "%or.cond127.i") "if.then19.i" "if.else.i" }

theorem walkIf_end_i97_find : stage2Body.findBlock "if.end.i97" = some walkIf_end_i97 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end_i97]

/-- **`if.end.i97` as a link.** -/
theorem WalkLink.if_end_i97 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i97")
    {a : Nat} {b : UInt8}
    (hd : lookupName s.env "%arrayidx10.i" = some (.ptr a))
    (hread : readBytes s.mem a 1 = some [b]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
          evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
          then "if.then19.i" else "if.else.i") } s' := by
  have hden : denoteCode calls walkIf_end_i97.instrs s =
      some (stateAt (cells
        [("%or.cond127.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
            evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
         ("%or.cond.i98", .int 1 (evalICmp .ult
            (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
         ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)),
         ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))),
         ("%41", .int 8 (BitVec.ofNat 8 b.toNat))] s.env) s) := by
    simp only [walkIf_end_i97]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load8_single (calls := calls) (env := s.env) (s := s)
      (d := "%41") (p := "%arrayidx10.i") (a := a) hd hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%cmp11.i") (a := "%41") 8 (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 45) (by simp [lookupName])]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%42") (a := "%41") (w := 8) (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 208)
      (by
        rw [lookupName_cons_ne _ _ (by decide)]
        simp [lookupName])]
    rw [denoteCode_icmp_imm (calls := calls)
      (env := ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)) ::
        ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%or.cond.i98") (a := "%42") IPred.ult 8
      (x := BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (c := BitVec.ofNat 8 10)
      (by simp [lookupName])]
    rw [denoteCode_or_reg_w (calls := calls)
      (env := ("%or.cond.i98", .int 1 (evalICmp .ult
          (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
        ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)) ::
        ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%or.cond127.i") (a := "%cmp11.i") (b := "%or.cond.i98") (w := 1)
      (x := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))
      (y := evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        simp [lookupName])
      (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end_i97) (by rw [hblock]; exact walkIf_end_i97_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
    (by simp [stateAt, cells]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end490.i`: the `%root_done.i` flag's last test. -/
def walkIf_end490_i : Block :=
  { name := "if.end490.i",
    instrs := [
      Instr.load "%.pr" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.icmp "%tobool491.not.i" IPred.eq 32 (Operand.reg "%.pr") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool491.not.i") "if.then492.i" "s2_walk.exit" }

theorem walkIf_end490_i_find : stage2Body.findBlock "if.end490.i" = some walkIf_end490_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end490_i]

/-- **`if.end490.i` as a link.** -/
theorem WalkLink.if_end490_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end490.i")
    {rd : Nat} {v : BitVec 32}
    (hroot : lookupName s.env "%root_done.i" = some (.ptr rd))
    (hread : readBytes s.mem rd 4 = some (natToBytes v.toNat 4)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq v (BitVec.ofNat 32 0) = 1
          then "if.then492.i" else "s2_walk.exit") } s' := by
  have hden : denoteCode calls walkIf_end490_i.instrs s =
      some (stateAt (cells
        [("%tobool491.not.i", .int 1 (evalICmp .eq v (BitVec.ofNat 32 0))),
         ("%.pr", .int 32 v)] s.env) s) := by
    simp only [walkIf_end490_i]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load_i32 (calls := calls) (env := s.env) (s := s)
      (d := "%.pr") (p := "%root_done.i") (a := rd) (v := v) hroot hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%.pr", .int 32 v) :: s.env) (s := s)
      (d := "%tobool491.not.i") (a := "%.pr") 32 (x := v) (c := BitVec.ofNat 32 0)
      (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end490_i) (by rw [hblock]; exact walkIf_end490_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq v (BitVec.ofNat 32 0))
    (by simp [stateAt, cells]) (by simp [WalkLocal]) (by simp [WalkLocal])


/-! ### The instrument

The module's declarations' axiom footprints, measured rather than asserted.  The
two ends are the step lemma the class's reads are built from and the two shapes
whose runs are the longest (`if.end59.i`'s `gep` chain and `if.end490.i`'s alloca
read). -/
/-- info: 'LeanLLVM.Refinement.WalkScope.walkToNat_ofNat8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkToNat_ofNat8

/-- info: 'LeanLLVM.Refinement.WalkScope.denoteCode_icmp_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.denoteCode_icmp_imm

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end_i_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end_i_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end_i97' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end_i97

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end490_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end490_i

end WalkScope
end LeanLLVM.Refinement
