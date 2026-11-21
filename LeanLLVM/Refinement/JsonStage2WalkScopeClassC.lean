import LeanLLVM.Refinement.JsonStage2WalkScopeClasses

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### Class C's eighteen instances

Each is the body's own text, transcribed, with its `findBlock` proof beside it.
The instance differs from the last only in the stored register, the `gep`'s name
and the exit block — fifteen exit to `if.then` and three to `cleanup474.i` — and
the proof is one `WalkLink.refusalStore` application in each. -/

/-- `if.then16.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then16_i : Block :=
  { name := "if.then16.i",
    instrs := [Instr.gep "%off1.i.i" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i")],
    term := Term.br "if.then" }

theorem walkIf_then16_i_find : stage2Body.findBlock "if.then16.i" = some walkIf_then16_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then16_i]

theorem WalkLink.if_then16_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then16.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then16_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then21.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then21_i : Block :=
  { name := "if.then21.i",
    instrs := [Instr.gep "%off1.i.i38" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i38")],
    term := Term.br "if.then" }

theorem walkIf_then21_i_find : stage2Body.findBlock "if.then21.i" = some walkIf_then21_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then21_i]

theorem WalkLink.if_then21_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then21.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then21_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then56.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then56_i : Block :=
  { name := "if.then56.i",
    instrs := [Instr.gep "%off1.i.i41" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i41")],
    term := Term.br "if.then" }

theorem walkIf_then56_i_find : stage2Body.findBlock "if.then56.i" = some walkIf_then56_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then56_i]

theorem WalkLink.if_then56_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then56.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then56_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then71.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then71_i : Block :=
  { name := "if.then71.i",
    instrs := [Instr.gep "%off1.i.i43" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i43")],
    term := Term.br "if.then" }

theorem walkIf_then71_i_find : stage2Body.findBlock "if.then71.i" = some walkIf_then71_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then71_i]

theorem WalkLink.if_then71_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then71.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then71_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `cleanup104.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkCleanup104_i : Block :=
  { name := "cleanup104.i",
    instrs := [Instr.gep "%off1.i.i45" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i45")],
    term := Term.br "if.then" }

theorem walkCleanup104_i_find : stage2Body.findBlock "cleanup104.i" = some walkCleanup104_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCleanup104_i]

theorem WalkLink.cleanup104_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cleanup104.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkCleanup104_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then130.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then130_i : Block :=
  { name := "if.then130.i",
    instrs := [Instr.gep "%off1.i.i66" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i66")],
    term := Term.br "if.then" }

theorem walkIf_then130_i_find : stage2Body.findBlock "if.then130.i" = some walkIf_then130_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then130_i]

theorem WalkLink.if_then130_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then130.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then130_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then147.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then147_i : Block :=
  { name := "if.then147.i",
    instrs := [Instr.gep "%off1.i.i68" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i68")],
    term := Term.br "if.then" }

theorem walkIf_then147_i_find : stage2Body.findBlock "if.then147.i" = some walkIf_then147_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then147_i]

theorem WalkLink.if_then147_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then147.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then147_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then159.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then159_i : Block :=
  { name := "if.then159.i",
    instrs := [Instr.gep "%off1.i.i70" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i70")],
    term := Term.br "if.then" }

theorem walkIf_then159_i_find : stage2Body.findBlock "if.then159.i" = some walkIf_then159_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then159_i]

theorem WalkLink.if_then159_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then159.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then159_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then176.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then176_i : Block :=
  { name := "if.then176.i",
    instrs := [Instr.gep "%off1.i.i72" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i72")],
    term := Term.br "if.then" }

theorem walkIf_then176_i_find : stage2Body.findBlock "if.then176.i" = some walkIf_then176_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then176_i]

theorem WalkLink.if_then176_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then176.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then176_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then192.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then192_i : Block :=
  { name := "if.then192.i",
    instrs := [Instr.gep "%off1.i.i74" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i74")],
    term := Term.br "if.then" }

theorem walkIf_then192_i_find : stage2Body.findBlock "if.then192.i" = some walkIf_then192_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then192_i]

theorem WalkLink.if_then192_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then192.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then192_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then205.i`: the refusal's offset store, of `%idxprom.i` — the entry's position,
which is where the parser reports an unterminated string. -/
def walkIf_then205_i : Block :=
  { name := "if.then205.i",
    instrs := [Instr.gep "%off1.i.i76" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i76")],
    term := Term.br "if.then" }

theorem walkIf_then205_i_find : stage2Body.findBlock "if.then205.i" = some walkIf_then205_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then205_i]

theorem WalkLink.if_then205_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then205.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then205_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then214.i`: the refusal's offset store, of `%idxprom.i` — the entry's position,
for the same reason as `if.then205.i`. -/
def walkIf_then214_i : Block :=
  { name := "if.then214.i",
    instrs := [Instr.gep "%off1.i.i78" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i78")],
    term := Term.br "if.then" }

theorem walkIf_then214_i_find : stage2Body.findBlock "if.then214.i" = some walkIf_then214_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then214_i]

theorem WalkLink.if_then214_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then214.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then214_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then249.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then249_i : Block :=
  { name := "if.then249.i",
    instrs := [Instr.gep "%off1.i.i80" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i80")],
    term := Term.br "if.then" }

theorem walkIf_then249_i_find : stage2Body.findBlock "if.then249.i" = some walkIf_then249_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then249_i]

theorem WalkLink.if_then249_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then249.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then249_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then418.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then418_i : Block :=
  { name := "if.then418.i",
    instrs := [Instr.gep "%off1.i.i91" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i91")],
    term := Term.br "cleanup474.i" }

theorem walkIf_then418_i_find : stage2Body.findBlock "if.then418.i" = some walkIf_then418_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then418_i]

theorem WalkLink.if_then418_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then418.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then418_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.else43.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_else43_i : Block :=
  { name := "if.else43.i",
    instrs := [Instr.gep "%off1.i129.i" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i129.i")],
    term := Term.br "cleanup474.i" }

theorem walkIf_else43_i_find : stage2Body.findBlock "if.else43.i" = some walkIf_else43_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else43_i]

theorem WalkLink.if_else43_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else43.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else43_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then467.i`: the refusal's offset store, of `%q.0.i246`. -/
def walkIf_then467_i : Block :=
  { name := "if.then467.i",
    instrs := [Instr.gep "%off1.i.i113" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%q.0.i246") (.reg "%off1.i.i113")],
    term := Term.br "cleanup474.i" }

theorem walkIf_then467_i_find : stage2Body.findBlock "if.then467.i" = some walkIf_then467_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then467_i]

theorem WalkLink.if_then467_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then467.i")
    {j : Nat} (hv : evalOperand s (.reg "%q.0.i246") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then467_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then488.i`: the refusal's offset store, of `%4`. -/
def walkIf_then488_i : Block :=
  { name := "if.then488.i",
    instrs := [Instr.gep "%off1.i.i115" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i115")],
    term := Term.br "if.then" }

theorem walkIf_then488_i_find : stage2Body.findBlock "if.then488.i" = some walkIf_then488_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then488_i]

theorem WalkLink.if_then488_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then488.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then488_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then492.i`: the refusal's offset store, of `%4`. -/
def walkIf_then492_i : Block :=
  { name := "if.then492.i",
    instrs := [Instr.gep "%off1.i.i117" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i117")],
    term := Term.br "if.then" }

theorem walkIf_then492_i_find : stage2Body.findBlock "if.then492.i" = some walkIf_then492_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then492_i]

theorem WalkLink.if_then492_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then492.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then492_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- **Class B′: no instructions and a branch on a carried bit.**  The block binds
nothing; the bit is one the previous block's comparison left behind, and the edge
it names is the edge taken.  Every clause of the invariant is the one it had. -/
theorem WalkLink.condBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    (hinstrs : B.instrs = []) {d tl fl : String} {bit : BitVec 1}
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hd : evalOperand s (.reg d) = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if bit = 1 then tl else fl) } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s with pc := (if bit = 1 then tl else fl), pre := some s.pc }
  have hden : denoteCode calls B.instrs s = some s := by rw [hinstrs]; rfl
  have hdl : lookupName s.env d = some (.int 1 bit) := lookupName_of_evalOperand_reg hd
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    exact walkExecTerm_condbr (bit := bit) hdl
  refine ⟨s', ⟨hInv, hstep, ?_, ?_, rfl⟩⟩
  · have hnm : B.name = C.block := findBlockList_name hfind
    have hle := walkEmitC_condbr_le (findBlockList_mem hfind) hterm
    have hph : walkEmitC C.block ≤ walkEmitC (if bit = 1 then tl else fl) := by
      rw [← hnm]
      by_cases hb : bit = 1
      · rw [if_pos hb]; exact hle.1
      · rw [if_neg hb]; exact hle.2
    refine
      { pc_eq := rfl
        blockIndex := hInv.blockIndex
        k_le := hInv.k_le
        events_le := by
          dsimp only
          have h := hInv.events_le
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := hInv.depth_reg
        ptrs := hInv.ptrs
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        regs := hInv.regs
        iter := hInv.iter
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := hInv.owned
        root_slot := hInv.root_slot
        next_ge := hInv.next_ge
        frame := hInv.frame
        inc_reg := hInv.inc_reg
        idx_reg := hInv.idx_reg
        blockLocal := ?_ }
    · dsimp only [s']
      by_cases ht : bit = 1
      · rw [ite_eq_left ht]; exact hl
      · rw [ite_eq_right ht]; exact hf
  · rfl

/-- `if.then432.i`: the block `if.then425.i`'s clear test enters, and its branch is
`%cmp343.i`'s answer — the same bit `if.end133.i` computed. -/
def walkIf_then432_i : Block :=
  { name := "if.then432.i", instrs := [],
    term := Term.condbr (.reg "%cmp343.i") "cond.true.i106" "cond.end.i96" }

theorem walkIf_then432_i_find :
    stage2Body.findBlock "if.then432.i" = some walkIf_then432_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then432_i]

theorem WalkLink.if_then432_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then432.i")
    {x : BitVec 1} (h1 : evalOperand s (.reg "%cmp343.i") = some (.int 1 x))
    : ∃ s', WalkLink calls G C s
      { C with block := (if x = 1 then "cond.true.i106" else "cond.end.i96") } s' := by
  exact WalkLink.condBr (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then432_i_find) rfl rfl h1
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- **Class B: no instructions and a jump.**  The block binds nothing, so every
clause of the invariant is the one it had and the only change is the block the run
is at.

The one edge a generic jump cannot carry is the header's pass
(`while.body.i → NodeBlock21`): it leaves the trace's stretch because it advances
`k`, so `walkEmitC` falls by one there and the link's target would need the tight
form.  That step is `whileBody_step`'s, and `hne` says this link is not it. -/
theorem WalkLink.br {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    (hinstrs : B.instrs = []) {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s with pc := t, pre := some s.pc })
    (hne : C.block ≠ "while.body.i") :
    ∃ s', WalkLink calls G C s { C with block := t } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s with pc := t, pre := some s.pc }
  have hden : denoteCode calls B.instrs s = some s := by rw [hinstrs]; rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm, s']
  have hnm : B.name = C.block := findBlockList_name hfind
  have hph : walkEmitC C.block ≤ walkEmitC t := by
    rw [← hnm]
    exact walkEmitC_br_le (findBlockList_mem hfind) (by rw [hnm]; exact hne) hterm
  refine ⟨s', ⟨hInv, hstep, ?_, ?_, rfl⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := hInv.blockIndex
        k_le := hInv.k_le
        events_le := by
          dsimp only
          have h := hInv.events_le
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := hInv.depth_reg
        ptrs := hInv.ptrs
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        regs := hInv.regs
        iter := hInv.iter
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := hInv.owned
        root_slot := hInv.root_slot
        next_ge := hInv.next_ge
        frame := hInv.frame
        inc_reg := hInv.inc_reg
        idx_reg := hInv.idx_reg
        blockLocal := hloc }
  · rfl


/-! ### The literal comparison's latch, as a link

`for.inc.i.i` increments its counter and takes the back edge while the counter is
short of the bound, so `forInc_step` gives the step, the invariant and a strictly
smaller measure.  `WalkLink.forInc` is that arm as a link, for the trace to use: the
strictness is dropped to `WalkLink`'s non-increase.  The four scan headers are not
links here; their visit is the counted round of
`JsonStage2WalkRevolutionScanRound`. -/

/-- **The literal comparison's latch as a link.**  `for.inc.i.i` is `forInc_step`
without the strictness: the measure falls by one, so it does not rise. -/
theorem WalkLink.forInc {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.inc.i.i") (hguard : ForIncGuard C s) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "for.body.i.i" := by
  obtain ⟨i, c, hinner, hlt, hcw, hi, hc⟩ := hguard
  obtain ⟨e, C', hstep, hinv, hstage, hland, hmeas, -⟩ :=
    forInc_step G C s i c hInv hblock hi hc hinner hlt hcw
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas, hstage⟩, hland⟩

end WalkScope
end LeanLLVM.Refinement
