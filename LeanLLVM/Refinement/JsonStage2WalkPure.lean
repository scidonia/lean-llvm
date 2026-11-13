/-
The stage-2 walk's remaining pure blocks: class G's `load`-and-compare runs.

`JsonStage2WalkRest` supplies a pure run's three transfers (`WalkLink.pureCore`,
`WalkLink.pureJumpCore`, `WalkLink.pureCoreCarried`), the `%k11.i`-binding variant
`WalkLink.pureJumpK11`, and six links — H1's five `LeafBlock`s and `if.then281.i`.
What it records as not supplied is the *instance work*: writing each block's
outgoing environment so its `denoteCode` equality is a term the transfer consumes.
This module is that work for all fourteen of the census's G rows.  Four of them
read a container-stack byte through `sp - 1` (`if.end179.i`, `land.lhs.true.i`,
`if.end133.i`, `if.end59.i`), and their runs are stated at the block's *variables*
with the outgoing environment named once, because writing the environment into the
statement twice (once per `WalkLocal`) does not pass the kernel's type-checker:
with the run at the block's literal instruction list the declaration reports a
deep recursion (measured: `maxRecDepth 50000` does not help, so it is not a depth
limit, and the pair's declaration alone reached 7.8 GB resident under a 6 GB cap).
The two five-instruction rows take `walkMarkerEnv` through one class lemma
(`WalkLink.stackMarkerBr`); the seven- and eight-instruction rows take a named
`env'` with an equation `env' = walkPairEnv …`/`walkSelectEnv …`
(`WalkLink.stackPairBr`, `WalkLink.stackSelectBr`), and the instances supply the
block by `rfl`, so no statement contains the environment twice.

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


/-- The five cells a marker run leaves: `%gg = add %sp, c`, the zero-extension,
the byte's address, the byte and its comparison. -/
def walkMarkerEnv (gg zx ap ld d : String) (x c : BitVec 32) (a q : Nat) (one : BitVec 8)
    (env : Env) : Env :=
  cells [(d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)),
    (ld, .int 8 (BitVec.ofNat 8 q)), (ap, .ptr (a + (x + c).toNat)),
    (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)), (gg, .int 32 (x + c))] env

/-- The seven cells a pair run leaves: the marker run, then the second stack's
address and byte above the comparison. -/
def walkPairEnv (gg zx ap1 ld1 d ap2 ld2 : String) (x c : BitVec 32) (a1 a2 : Nat)
    (one : BitVec 8) (q : Nat) (bs2 : List UInt8) (env : Env) : Env :=
  cells [(ld2, .int 8 (BitVec.ofNat 8 (bytesToNat bs2))),
    (ap2, .ptr (a2 + (x + c).toNat)),
    (d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)),
    (ld1, .int 8 (BitVec.ofNat 8 q)), (ap1, .ptr (a1 + (x + c).toNat)),
    (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)), (gg, .int 32 (x + c))] env

/-- The `select` nest's comparison of the document byte with `125`. -/
def walkSelBit (db : BitVec 8) : BitVec 1 :=
  evalICmp .eq db (BitVec.ofNat 8 125)

/-- The expected marker: `1` when the document byte is `}`, `2` otherwise. -/
def walkSelVal (db : BitVec 8) : BitVec 32 :=
  if walkSelBit db = 1 then BitVec.ofNat 32 1 else BitVec.ofNat 32 2

/-- The eight cells the `select` nest leaves, in the explicit form the run builds
(the definitional `walkSelVal`/`walkSelBit` folded out, so the statement's
environment is the run's term). -/
def walkSelectEnv (sub cmpi sel zx apx ldv cvt d : String) (db : BitVec 8)
    (x c : BitVec 32) (ct q : Nat) (env : Env) : Env :=
  cells [
    (d, .int 1 (evalICmp .eq
      (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
        else BitVec.ofNat 32 2)
      (BitVec.ofNat 32 (BitVec.ofNat 8 q).toNat))),
    (cvt, .int 32 (BitVec.ofNat 32 (BitVec.ofNat 8 q).toNat)),
    (ldv, .int 8 (BitVec.ofNat 8 q)),
    (apx, .ptr (ct + (x + c).toNat)),
    (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)),
    (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1
      then BitVec.ofNat 32 1 else BitVec.ofNat 32 2)),
    (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))),
    (sub, .int 32 (x + c))] env

/-- **The environment the select nest's first half leaves.**  The four cells the
arithmetic and the `select` bind, in the order the run binds them: the offset, the
expected marker, the byte's test, and the depth less one.  Naming it is what lets the
nest's `denoteCode` be two four-instruction theorems instead of one eight-instruction
term — the split this layer's cap needs. -/
def walkSelectEnv4 (sub cmpi sel zx : String) (db : BitVec 8) (x c : BitVec 32)
    (env : Env) : Env :=
  cells [
    (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)),
    (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
      else BitVec.ofNat 32 2)),
    (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))),
    (sub, .int 32 (x + c))] env

/-- **The select nest's first four instructions**, at an arbitrary tail: `%sub.i` is
the depth less one, `%cmp61.i` the closing byte's test, `%conv64.i` the expected marker
and `%idxprom65.i` the offset.  The successor's environment is `walkSelectEnv4`. -/
theorem walkSelectDen4 {calls : Calls} (env : Env) (s : State)
    {sub cmpi sel zx : String} {db : BitVec 8} {x c : BitVec 32}
    (hsp : lookupName env "%sp.i.0248" = some (.int 32 x))
    (h8 : lookupName env "%8" = some (.int 8 db))
    (hs8 : sub ≠ "%8") (hselSub : sel ≠ sub) (hcmpiSub : cmpi ≠ sub)
    (rest : List Instr) :
    denoteCode calls (
      Instr.binop sub BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)) ::
      Instr.icmp cmpi IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125))) ::
      Instr.select sel (.int 32) (.reg cmpi) (.imm (.int 32 (BitVec.ofNat 32 1)))
        (.imm (.int 32 (BitVec.ofNat 32 2))) ::
      Instr.zext zx 32 64 (.reg sub) :: rest) (stateAt env s) =
      denoteCode calls rest (stateAt (walkSelectEnv4 sub cmpi sel zx db x c env) s) := by
  rw [walkDenoteCode_add_imm_w (calls := calls) (env := env) (s := s) (d := sub)
    (a := "%sp.i.0248") (w := 32) (x := x) (c := c) hsp]
  rw [denoteCode_icmp_eq_imm_w (calls := calls) (env := (sub, .int 32 (x + c)) :: env)
    (s := s) (d := cmpi) (a := "%8") (w := 8) (x := db) (c := BitVec.ofNat 8 125)
    (by rw [lookupName_cons_ne (k := sub) (n := "%8") _ _ hs8]; exact h8)]
  rw [denoteCode_select_imm_imm_w (calls := calls)
    (env := (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env) (s := s)
    (d := sel) (c := cmpi) (w := 32) (bb := evalICmp .eq db (BitVec.ofNat 8 125))
    (x := BitVec.ofNat 32 1) (y := BitVec.ofNat 32 2)
    (by simp [lookupName])]
  rw [denoteCode_zext (calls := calls)
    (env := (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1
        then BitVec.ofNat 32 1 else BitVec.ofNat 32 2)) ::
      (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env) (s := s) (d := zx) (v := sub)
    (wIn := 32) (wOut := 64) (x := x + c)
    (by rw [lookupName_cons_ne (k := sel) (n := sub) _ _ hselSub,
            lookupName_cons_ne (k := cmpi) (n := sub) _ _ hcmpiSub]; simp [lookupName])]
  rfl

/-- **The select nest's second four instructions**: the stack's address, the byte, its
`zext`, and the comparison with the expected marker.  Runs from the environment
`walkSelectEnv4` names and leaves `walkSelectEnv`. -/
theorem walkSelectDen8 {calls : Calls} (env : Env) (s : State)
    {sub cmpi sel zx apx ldv cvt d base : String} {db : BitVec 8} {x c : BitVec 32}
    {ct q : Nat} {bs : List UInt8}
    (hzb : zx ≠ base) (hselBase : sel ≠ base) (hcmpiBase : cmpi ≠ base)
    (hsb : sub ≠ base)
    (hb : lookupName env base = some (.ptr ct))
    (hpos : (x + c).toNat < 2 ^ 63)
    (hread : readBytes s.mem (ct + (x + c).toNat) 1 = some bs)
    (hbsn : bytesToNat bs = q)
    (hcvtSel : cvt ≠ sel) (hldvSel : ldv ≠ sel) (hapxSel : apx ≠ sel) (hzxSel : zx ≠ sel)
    (rest : List Instr) :
    denoteCode calls (
      Instr.gep apx (.int 8) (.reg base) (.reg zx) ::
      Instr.load ldv (.int 8) (.reg apx) ::
      Instr.zext cvt 8 32 (.reg ldv) ::
      Instr.icmp d IPred.eq 32 (.reg sel) (.reg cvt) :: rest)
      (stateAt (walkSelectEnv4 sub cmpi sel zx db x c env) s) =
      denoteCode calls rest
        (stateAt (walkSelectEnv sub cmpi sel zx apx ldv cvt d db x c ct q env) s) := by
  simp only [walkSelectEnv4, cells]
  rw [denoteCode_gep8_ofNat (calls := calls)
    (env := (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) ::
      (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
        else BitVec.ofNat 32 2)) ::
      (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env) (s := s) (d := apx) (base := base) (off := zx)
    (a := ct) (j := (x + c).toNat)
    (by
      rw [lookupName_cons_ne (k := zx) (n := base) _ _ hzb,
          lookupName_cons_ne (k := sel) (n := base) _ _ hselBase,
          lookupName_cons_ne (k := cmpi) (n := base) _ _ hcmpiBase,
          lookupName_cons_ne (k := sub) (n := base) _ _ hsb]
      exact hb)
    (by simp [lookupName]) hpos]
  rw [denoteCode_load8 (calls := calls)
    (env := (apx, .ptr (ct + (x + c).toNat)) ::
      (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) ::
      (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
        else BitVec.ofNat 32 2)) ::
      (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env)
    (s := s) (d := ldv) (p := apx) (a := ct + (x + c).toNat) (q := q) (bs := bs)
    (by simp [lookupName]) hread hbsn]
  rw [denoteCode_zext (calls := calls)
    (env := (ldv, .int 8 (BitVec.ofNat 8 q)) :: (apx, .ptr (ct + (x + c).toNat)) ::
      (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) ::
      (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
        else BitVec.ofNat 32 2)) ::
      (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env) (s := s) (d := cvt) (v := ldv)
    (wIn := 8) (wOut := 32) (x := BitVec.ofNat 8 q) (by simp [lookupName])]
  rw [denoteCode_icmp_reg_w (calls := calls)
    (env := (cvt, .int 32 (BitVec.ofNat 32 (BitVec.ofNat 8 q).toNat)) ::
      (ldv, .int 8 (BitVec.ofNat 8 q)) :: (apx, .ptr (ct + (x + c).toNat)) ::
      (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) ::
      (sel, .int 32 (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
        else BitVec.ofNat 32 2)) ::
      (cmpi, .int 1 (evalICmp .eq db (BitVec.ofNat 8 125))) ::
      (sub, .int 32 (x + c)) :: env) (s := s) (d := d) (a := sel) (b := cvt)
    IPred.eq 32
    (x := if evalICmp .eq db (BitVec.ofNat 8 125) = 1
      then BitVec.ofNat 32 1 else BitVec.ofNat 32 2)
    (y := BitVec.ofNat 32 (BitVec.ofNat 8 q).toNat)
    (by
      rw [lookupName_cons_ne (k := cvt) (n := sel) _ _ hcvtSel,
          lookupName_cons_ne (k := ldv) (n := sel) _ _ hldvSel,
          lookupName_cons_ne (k := apx) (n := sel) _ _ hapxSel,
          lookupName_cons_ne (k := zx) (n := sel) _ _ hzxSel]
      simp [lookupName, walkSelVal, walkSelBit])
    (by simp [lookupName])]
  rfl

/-- **One stack byte at `%sp - 1`, tested for a marker, then a `condbr`.**  The
five-instruction shape `if.end179.i` and `land.lhs.true.i`. -/
theorem WalkLink.stackMarkerBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {gg zx ap ld d base tl fl : String} {x c : BitVec 32} {a : Nat} {one : BitVec 8}
    {bs : List UInt8} {q : Nat}
    (hinstrs : B.instrs = [
      Instr.binop gg BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)),
      Instr.zext zx 32 64 (.reg gg),
      Instr.gep ap (.int 8) (.reg base) (.reg zx),
      Instr.load ld (.int 8) (.reg ap),
      Instr.icmp d IPred.eq 8 (.reg ld) (.imm (.int 8 one))])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 x))
    (hbase : lookupName s.env base = some (.ptr a))
    (hzb : zx ≠ base) (hgb : gg ≠ base)
    (hpos : (x + c).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (x + c).toNat) 1 = some bs)
    (hbs : bytesToNat bs = q)
    (hfree : walkCarried B.instrs)
    (hl : WalkLocal { C with block := tl }
      { stateAt (walkMarkerEnv gg zx ap ld d x c a q one s.env) s with
        pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl }
      { stateAt (walkMarkerEnv gg zx ap ld d x c a q one s.env) s with
        pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 q) one = 1 then tl else fl) } s' := by
  have hden : denoteCode calls B.instrs s =
      some (stateAt (walkMarkerEnv gg zx ap ld d x c a q one s.env) s) := by
    rw [hinstrs, ← stateAt_self s]
    rw [walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := gg)
      (a := "%sp.i.0248") (w := 32) (x := x) (c := c) hsp]
    rw [denoteCode_zext (calls := calls) (env := (gg, .int 32 (x + c)) :: s.env) (s := s)
      (d := zx) (v := gg) (wIn := 32) (wOut := 64) (x := x + c) (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap) (base := base) (off := zx) (a := a) (j := (x + c).toNat)
      (by rw [lookupName_cons_ne (k := zx) (n := base) _ _ hzb,
              lookupName_cons_ne (k := gg) (n := base) _ _ hgb]; exact hbase)
      (by simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap, .ptr (a + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld) (p := ap) (a := a + (x + c).toNat) (q := q) (bs := bs)
      (by simp [lookupName]) hread hbs]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := (ld, .int 8 (BitVec.ofNat 8 q)) :: (ap, .ptr (a + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := d) (a := ld) (w := 8) (x := BitVec.ofNat 8 q) (c := one)
      (by simp [lookupName])]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv hfind hden hfree rfl rfl hterm
    (by simp only [stateAt, walkMarkerEnv, cells, lookupName_cons_self]) hl hf

/-- **`if.end179.i` as a link.** -/
theorem WalkLink.if_end179_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end179.i")
    {sp ct : Nat} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
          then "lor.lhs.false.i" else "if.then192.i") } s' :=
  WalkLink.stackMarkerBr (G := G) (C := C) (s := s) hInv
    (B := walkIf_end179_i) (by rw [hblock]; exact walkIf_end179_i_find)
    rfl rfl hsp hct (by decide) (by decide) hq63 hread (bytesToNat_singleton b)
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- **`land.lhs.true.i` as a link.** -/
theorem WalkLink.land_lhs_true_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.lhs.true.i")
    {sp ct : Nat} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
          then "if.then231.i" else "if.end245.i") } s' :=
  WalkLink.stackMarkerBr (G := G) (C := C) (s := s) hInv
    (B := walkLand_lhs_true_i) (by rw [hblock]; exact walkLand_lhs_true_i_find)
    rfl rfl hsp hct (by decide) (by decide) hq63 hread (bytesToNat_singleton b)
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- **Two stack bytes at `%sp - 1`, the first tested for a marker.**  The
seven-instruction shape `if.end133.i`.  The run's environment is named once
(`env'`), so the statement mentions the seven cells once and no proof term
duplicates them. -/
theorem WalkLink.stackPairBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {gg zx ap1 ld1 d ap2 ld2 base1 base2 tl fl : String}
    {x c : BitVec 32} {a1 a2 : Nat} {one : BitVec 8} {bs : List UInt8} {bs2 : List UInt8}
    {q : Nat} {env' : Env}
    (hinstrs : B.instrs = [
      Instr.binop gg BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)),
      Instr.zext zx 32 64 (.reg gg),
      Instr.gep ap1 (.int 8) (.reg base1) (.reg zx),
      Instr.load ld1 (.int 8) (.reg ap1),
      Instr.icmp d IPred.eq 8 (.reg ld1) (.imm (.int 8 one)),
      Instr.gep ap2 (.int 8) (.reg base2) (.reg zx),
      Instr.load ld2 (.int 8) (.reg ap2)])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (henv : env' = walkPairEnv gg zx ap1 ld1 d ap2 ld2 x c a1 a2 one q bs2 s.env)
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 x))
    (hb1 : lookupName s.env base1 = some (.ptr a1))
    (hb2 : lookupName s.env base2 = some (.ptr a2))
    (hzb1 : zx ≠ base1) (hgb1 : gg ≠ base1)
    (hzb2 : zx ≠ base2) (hgb2 : gg ≠ base2)
    (hdzx : d ≠ zx) (hlzx : ld1 ≠ zx) (hazx : ap1 ≠ zx)
    (hlb2 : ld1 ≠ base2) (hab2 : ap1 ≠ base2) (hdb2 : d ≠ base2)
    (hld2d : ld2 ≠ d) (hap2d : ap2 ≠ d)
    (hpos : (x + c).toNat < 2 ^ 63)
    (hbs : bytesToNat bs = q)
    (hread1 : readBytes s.mem (a1 + (x + c).toNat) 1 = some bs)
    (hread2 : readBytes s.mem (a2 + (x + c).toNat) 1 = some bs2)
    (hfree : walkCarried B.instrs)
    (hl : WalkLocal { C with block := tl } { stateAt env' s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { stateAt env' s with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 q) one = 1 then tl else fl) } s' := by
  have hden : denoteCode calls B.instrs s = some (stateAt env' s) := by
    rw [hinstrs, ← stateAt_self s]
    rw [walkDenoteCode_add_imm_w (calls := calls) (env := s.env) (s := s) (d := gg)
      (a := "%sp.i.0248") (w := 32) (x := x) (c := c) hsp]
    rw [denoteCode_zext (calls := calls) (env := (gg, .int 32 (x + c)) :: s.env) (s := s)
      (d := zx) (v := gg) (wIn := 32) (wOut := 64) (x := x + c) (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap1) (base := base1) (off := zx) (a := a1) (j := (x + c).toNat)
      (by rw [lookupName_cons_ne (k := zx) (n := base1) _ _ hzb1,
              lookupName_cons_ne (k := gg) (n := base1) _ _ hgb1]; exact hb1)
      (by simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld1) (p := ap1) (a := a1 + (x + c).toNat) (q := q) (bs := bs)
      (by simp [lookupName]) hread1 hbs]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := d) (a := ld1) (w := 8) (x := BitVec.ofNat 8 q) (c := one)
      (by simp [lookupName])]
    rw [denoteCode_gep8_ofNat (calls := calls)
      (env := (d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)) ::
        (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ap2) (base := base2) (off := zx) (a := a2) (j := (x + c).toNat)
      (by
        rw [lookupName_cons_ne (k := d) (n := base2) _ _ hdb2,
            lookupName_cons_ne (k := ld1) (n := base2) _ _ hlb2,
            lookupName_cons_ne (k := ap1) (n := base2) _ _ hab2,
            lookupName_cons_ne (k := zx) (n := base2) _ _ hzb2,
            lookupName_cons_ne (k := gg) (n := base2) _ _ hgb2]
        exact hb2)
      (by
        rw [lookupName_cons_ne (k := d) (n := zx) _ _ hdzx,
            lookupName_cons_ne (k := ld1) (n := zx) _ _ hlzx,
            lookupName_cons_ne (k := ap1) (n := zx) _ _ hazx]
        simp [lookupName]) hpos]
    rw [denoteCode_load8 (calls := calls)
      (env := (ap2, .ptr (a2 + (x + c).toNat)) ::
        (d, .int 1 (evalICmp .eq (BitVec.ofNat 8 q) one)) ::
        (ld1, .int 8 (BitVec.ofNat 8 q)) :: (ap1, .ptr (a1 + (x + c).toNat)) ::
        (zx, .int 64 (BitVec.ofNat 64 (x + c).toNat)) :: (gg, .int 32 (x + c)) :: s.env)
      (s := s) (d := ld2) (p := ap2) (a := a2 + (x + c).toNat) (q := bytesToNat bs2)
      (bs := bs2) (by simp [lookupName]) hread2 rfl]
    rw [henv]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv hfind hden hfree rfl rfl hterm
    (by
      rw [henv]
      simp only [stateAt, walkPairEnv, cells]
      rw [lookupName_cons_ne (k := ld2) (n := d) _ _ hld2d,
        lookupName_cons_ne (k := ap2) (n := d) _ _ hap2d, lookupName_cons_self])
    hl hf

/-- **`if.end133.i` as a link.** -/
theorem WalkLink.if_end133_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end133.i")
    {sp ct cs : Nat} {b : UInt8} {b2 : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName s.env "%cst.i" = some (.ptr cs))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread1 : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b])
    (hread2 : readBytes s.mem
      (cs + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b2]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1) = 1
          then "if.then141.i" else "if.else153.i") } s' :=
  WalkLink.stackPairBr (G := G) (C := C) (s := s) hInv
    (B := walkIf_end133_i) (by rw [hblock]; exact walkIf_end133_i_find)
    rfl rfl
    (env' := walkPairEnv "%sub135.i" "%idxprom136.i" "%arrayidx137.i" "%21" "%cmp139.i" "%arrayidx143.i" "%22"
      (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295) ct cs
      (BitVec.ofNat 8 1) (bytesToNat [b]) [b2] s.env)
    (q := bytesToNat [b]) (bs := [b]) (bs2 := [b2])
    (one := BitVec.ofNat 8 1) (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 4294967295)
    (a1 := ct) (a2 := cs)
    rfl hsp hct hcs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hq63 rfl hread1 hread2
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])


/-- **The `select` nest of `if.end59.i`**: `%sp - 1`, the marker chosen from the
document byte, the type stack's byte, and the pair's comparison. -/
theorem WalkLink.stackSelectBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {zx apx ldv cvt d sub cmpi sel base tl fl : String}
    {x c : BitVec 32} {ct : Nat} {db : BitVec 8} {q : Nat} {bs : List UInt8} {env' : Env}
    (hinstrs : B.instrs = [
      Instr.binop sub BinOp.add 32 (.reg "%sp.i.0248") (.imm (.int 32 c)),
      Instr.icmp cmpi IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125))),
      Instr.select sel (.int 32) (.reg cmpi) (.imm (.int 32 (BitVec.ofNat 32 1)))
        (.imm (.int 32 (BitVec.ofNat 32 2))),
      Instr.zext zx 32 64 (.reg sub),
      Instr.gep apx (.int 8) (.reg base) (.reg zx),
      Instr.load ldv (.int 8) (.reg apx),
      Instr.zext cvt 8 32 (.reg ldv),
      Instr.icmp d IPred.eq 32 (.reg sel) (.reg cvt)])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (henv : env' = walkSelectEnv sub cmpi sel zx apx ldv cvt d db x c ct q s.env)
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 x))
    (h8 : lookupName s.env "%8" = some (.int 8 db))
    (hb : lookupName s.env base = some (.ptr ct))
    (hzb : zx ≠ base) (hsb : sub ≠ base) (hs8 : sub ≠ "%8")
    (hselSub : sel ≠ sub) (hcmpiSub : cmpi ≠ sub)
    (hselBase : sel ≠ base) (hcmpiBase : cmpi ≠ base)
    (hcvtSel : cvt ≠ sel) (hldvSel : ldv ≠ sel)
    (hapxSel : apx ≠ sel) (hzxSel : zx ≠ sel)
    (hpos : (x + c).toNat < 2 ^ 63)
    (hread : readBytes s.mem (ct + (x + c).toNat) 1 = some bs)
    (hbsn : bytesToNat bs = q)
    (hfree : walkCarried B.instrs)
    (hl : WalkLocal { C with block := tl } { stateAt env' s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { stateAt env' s with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq
          (if evalICmp .eq db (BitVec.ofNat 8 125) = 1 then BitVec.ofNat 32 1
            else BitVec.ofNat 32 2)
          (BitVec.ofNat 32 (BitVec.ofNat 8 q).toNat) = 1 then tl else fl) } s' := by
  have hden : denoteCode calls B.instrs s = some (stateAt env' s) := by
    rw [hinstrs, ← stateAt_self s,
      walkSelectDen4 (calls := calls) (env := s.env) (s := s) hsp h8 hs8 hselSub hcmpiSub
        (rest := [Instr.gep apx (.int 8) (.reg base) (.reg zx),
          Instr.load ldv (.int 8) (.reg apx),
          Instr.zext cvt 8 32 (.reg ldv),
          Instr.icmp d IPred.eq 32 (.reg sel) (.reg cvt)]),
      walkSelectDen8 (calls := calls) (env := s.env) (s := s) hzb hselBase hcmpiBase hsb hb
        hpos hread hbsn hcvtSel hldvSel hapxSel hzxSel (rest := [])]
    rw [henv]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv hfind hden hfree rfl rfl hterm
    (by
      rw [henv]
      simp only [stateAt, walkSelectEnv, cells]
      simp [lookupName])
    hl hf

/-- **`if.end59.i` as a link.** -/
theorem WalkLink.if_end59_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end59.i")
    {sp ct : Nat} {db : BitVec 8} {b : UInt8}
    (hsp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (h8 : lookupName s.env "%8" = some (.int 8 db))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ct))
    (hq63 : (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63)
    (hread : readBytes s.mem
      (ct + (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (walkSelVal db)
          (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat) = 1
          then "if.end74.i" else "if.then71.i") } s' := by
  show (∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (walkSelVal db)
          (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b])).toNat) = 1
          then "if.end74.i" else "if.then71.i") } s')
  simp only [walkSelVal, walkSelBit]
  exact WalkLink.stackSelectBr (G := G) (C := C) (s := s) hInv
    (B := walkIf_end59_i) (by rw [hblock]; exact walkIf_end59_i_find)
    rfl rfl
    (env' := walkSelectEnv "%sub.i" "%cmp61.i" "%conv64.i" "%idxprom65.i" "%arrayidx66.i"
      "%14" "%conv67.i" "%cmp69.not.i" db (BitVec.ofNat 32 sp) (BitVec.ofNat 32 4294967295)
      ct (bytesToNat [b]) s.env)
    (bs := [b]) (q := bytesToNat [b]) (db := db)
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 4294967295)
    rfl hsp h8 hct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hq63 hread rfl
    (by unfold walkCarried; decide)
    (by simp [WalkLocal]) (by simp [WalkLocal])


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

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end133_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end133_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end59_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end59_i

end WalkScope
end LeanLLVM.Refinement
