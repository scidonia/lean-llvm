import LeanLLVM.Refinement.JsonStage2WalkScopeStores

set_option autoImplicit false

/-! ### Steps at the two blocks' widths -/

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval


theorem sExt_ofNat64 {j : Nat} (hj : j < 2 ^ 63) :
    ((BitVec.ofNat 64 j).signExtend 64).toNat = j := by
  simp [BitVec.toNat_ofNat, BitVec.signExtend]
  omega

theorem walkToNat_ofNat64 {j : Nat} (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem walkToNat_ofNat32 {j : Nat} (hj : j < 2 ^ 32) :
    (BitVec.ofNat 32 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem bytesToNat_singleton (b : UInt8) : bytesToNat [b] = b.toNat := by
  simp [bytesToNat]

theorem bytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have h' := bytesToNat_lt bs
  rw [h, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide] at h'
  exact h'

theorem bytesToNat_lt_8 {bs : List UInt8} (h : bs.length = 1) :
    bytesToNat bs < 256 := by
  have h' := bytesToNat_lt bs
  rw [h] at h'
  exact h'

/-- **A write outside a read's range leaves the read alone.** -/
theorem walkReadBytes_writeBytes_outside {m : Mem} {v : List UInt8} :
    ∀ {start addr n : Nat}, addr + n ≤ start ∨ start + v.length ≤ addr →
      readBytes (writeBytes m start v) addr n = readBytes m addr n
  | start, addr, 0, _ => by simp [readBytes]
  | start, addr, n + 1, h => by
      have hhead : addr < start ∨ start + v.length ≤ addr := by omega
      have htail : addr + 1 + n ≤ start ∨ start + v.length ≤ addr + 1 := by omega
      rw [readBytes, readBytes, readByte_writeBytes_outside m v hhead,
        walkReadBytes_writeBytes_outside (m := m) (v := v) (start := start)
          (addr := addr + 1) (n := n) htail]

/-- A one-byte read from a present byte. -/
theorem walkReadBytes_one_of_readByte {m : Mem} {a : Nat} {b : UInt8}
    (h : readByte m a = some b) : readBytes m a 1 = some [b] := by
  simp only [readBytes, h]

theorem walkReadBytes_length {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {bs : List UInt8}, readBytes m addr n = some bs → bs.length = n
  | 0, bs, h => by
      simp only [readBytes, Option.some.injEq] at h
      subst h; rfl
  | n + 1, bs, h => by
      simp only [readBytes] at h
      split at h
      · cases h
      · rename_i b hb
        split at h
        · cases h
        · rename_i bs' hbs
          cases h
          simp only [List.length_cons]
          rw [walkReadBytes_length hbs]

theorem readLanes32_nth {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧ bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := readLanes32_nth (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

-- `denoteCode` chain steps: the same shapes `BlockEval` has, at the widths and
-- the `ofNat` values the two blocks use.

theorem denoteCode_zext32_64_ofNat (calls : Calls) (env : Env) (s : State)
    (d v : String) {q : Nat}
    (hv : lookupName env v = some (.int 32 (BitVec.ofNat 32 q)))
    (hq : q < 2 ^ 32) (is : List Instr) :
    denoteCode calls (.zext d 32 64 (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (BitVec.ofNat 64 q)) :: env) s) := by
  rw [denoteCode_zext calls env s d v 32 64 (x := BitVec.ofNat 32 q) hv is,
    walkToNat_ofNat32 hq]

theorem denoteCode_gep8_ofNat (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a j : Nat}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + j)) :: env) s) := by
  have hs := sExt_ofNat64 hj
  rw [denoteCode_gep8_reg calls env s d base off hb ho (by rw [hs]; exact hj) is, hs]

theorem denoteCode_gep32_ofNat (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a j : Nat}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 32) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + j * 4)) :: env) s) := by
  have hs := sExt_ofNat64 hj
  have hsize : (Ty.int 32).sizeBytes = 4 := by decide
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [evalInstr_gep (s := stateAt env s) (elemTy := .int 32)
      (hb := evalOperand_reg_of env s base (.ptr a) hb)
      (ho := evalOperand_reg_of env s off (.int 64 (BitVec.ofNat 64 j)) ho)
      (hpos := by rw [hs]; exact hj)])]
  simp only [stateAt, State.bind, hs, hsize]

theorem denoteCode_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat} {bs : List UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some bs) (hbs : bytesToNat bs = q) (is : List Instr) :
    denoteCode calls (.load d (.int 32) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 (BitVec.ofNat 32 q)) :: env) s) := by
  have hv' : loadValue (stateAt env s).mem (.int 32) a
      = some (.int 32 (BitVec.ofNat 32 q)) := by
    show loadValue s.mem (.int 32) a = _
    simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
      ite_eq_right (by decide : ¬ (32 = 0)), hv, hbs]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hv')])]
  simp only [stateAt, State.bind]

theorem denoteCode_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat} {bs : List UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some bs) (hbs : bytesToNat bs = q) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 q)) :: env) s) := by
  have hv' : loadValue (stateAt env s).mem (.int 8) a
      = some (.int 8 (BitVec.ofNat 8 q)) := by
    show loadValue s.mem (.int 8) a = _
    simp only [loadValue, show (8 + 7) / 8 = 1 from rfl,
      ite_eq_right (by decide : ¬ (8 = 0)), hv, hbs]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hv')])]
  simp only [stateAt, State.bind]

theorem denoteCode_load8_single (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) :=
  denoteCode_load8 calls env s d p (q := b.toNat) hp hv (bytesToNat_singleton b) is

theorem denoteCode_store64_ofNat (calls : Calls) (env : Env) (s : State)
    (v p : String) {a j : Nat}
    (hv : lookupName env v = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 64) (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (wordBytes 8 j) }) := by
  rw [denoteCode_store64 calls env s v p (x := BitVec.ofNat 64 j) hv hp is,
    walkToNat_ofNat64 hj]
  rfl

theorem denoteCode_store8 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 8} {a : Nat}
    (hv : lookupName env v = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, stateAt, show (8 + 7) / 8 = 1 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 8 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
      (hv := evalOperand_reg_of env s v (.int 8 x) hv)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

theorem denoteCode_store8_imm (calls : Calls) (env : Env) (s : State) (x : BitVec 8)
    (p : String) {a : Nat} (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.imm (.int 8 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, stateAt, show (8 + 7) / 8 = 1 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 8 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
      (hv := evalOperand_lit_of (stateAt env s) 8 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

theorem denoteCode_icmp_eq_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .eq w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)])]
  simp only [stateAt, State.bind]

theorem walkDenoteCode_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (s := stateAt env s)
      (r := (x + c).toNat)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]

theorem denoteCode_add_one_ofNat (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {j : Nat}
    (ha : lookupName env a = some (.int w (BitVec.ofNat w j))) (is : List Instr) :
    denoteCode calls
        (.binop d .add w (.reg a) (.imm (.int w (BitVec.ofNat w 1))) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (BitVec.ofNat w (j + 1))) :: env) s) := by
  rw [walkDenoteCode_add_imm_w calls env s d a w (x := BitVec.ofNat w j)
    (c := BitVec.ofNat w 1) ha is, ← BitVec.ofNat_add]

theorem denoteCode_select_imm_imm_w (calls : Calls) (env : Env) (s : State)
    (d c : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb)) (is : List Instr) :
    denoteCode calls
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.imm (.int w y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide : ¬ ((0 : BitVec 1) = 1))]
    rw [denoteCode_cons_of _ _ _ _ _ (by
      rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false (s := stateAt env s)
        (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
        (ha := evalOperand_lit_of (stateAt env s) w x)
        (hb := evalOperand_lit_of (stateAt env s) w y)])]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [denoteCode_cons_of _ _ _ _ _ (by
      rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true (s := stateAt env s)
        (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
        (ha := evalOperand_lit_of (stateAt env s) w x)
        (hb := evalOperand_lit_of (stateAt env s) w y)])]
    simp only [stateAt, State.bind]

/-- One instruction of the two blocks: the chain step whose shape matches. -/
macro "walk_step" : tactic => `(tactic|
  (first
   | rw [denoteCode_zext32_64_ofNat _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep32_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load32 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load8_single _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store64_ofNat _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_eq_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_one_ofNat _ _ _ _ _ _ ?_ _]
   | rw [walkDenoteCode_add_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_select_imm_imm_w _ _ _ _ _ _ ?_ _]
   | block_step))

/-- A whole block with the two blocks' further shapes. -/
macro "walk_block_eval" : tactic => `(tactic|
  (repeat walk_step
   block_close
   all_goals (try omega)))

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-- The header's instruction list, as the pinned body writes it. -/
def whileBodyInstrs : List Instr := [
  Instr.phi "%k.0.i249" (Ty.int 64)
    [("while.body.i.lr.ph", .imm (.int 64 (BitVec.ofNat 64 0))),
     ("cleanup478.i", .reg "%k.2.i")],
  Instr.phi "%sp.i.0248" (Ty.int 32)
    [("while.body.i.lr.ph", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("cleanup478.i", .reg "%sp.i.1")],
  Instr.binop "%inc.i" BinOp.add 64 (.reg "%k.0.i249") (.imm (.int 64 (BitVec.ofNat 64 1))),
  Instr.gep "%arrayidx.i" (Ty.int 32) (.reg "%5") (.reg "%k.0.i249"),
  Instr.load "%7" (Ty.int 32) (.reg "%arrayidx.i"),
  Instr.zext "%idxprom.i" 32 64 (.reg "%7"),
  Instr.gep "%arrayidx10.i" (Ty.int 8) (.reg "%3") (.reg "%idxprom.i"),
  Instr.load "%8" (Ty.int 8) (.reg "%arrayidx10.i"),
  Instr.store (Ty.int 64) (.reg "%inc.i") (.reg "%k11.i")]

/-- The header, as a block: the pin the chain is proved about. -/
def whileBodyBlock : Block :=
  { name := "while.body.i", instrs := whileBodyInstrs, term := Term.br "NodeBlock21" }

theorem whileBody_find : stage2Body.findBlock "while.body.i" = some whileBodyBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, whileBodyBlock, whileBodyInstrs]

macro "walk_close" : tactic => `(tactic|
  (all_goals (try (simp (config := { failIfUnchanged := false })
    only [cells, denoteCode, State.bindAll]))
   all_goals (try rfl)
   all_goals (try
     (first
      | assumption
      | exact LeanLLVM.Refinement.BlockEval.evalOperand_reg_of _ _ _ _ (by assumption)
      | block_lk
      | (simp only [phiIncoming]; rfl)
      | rfl
      | (exact evalOperand_lit_of _ _ _)))
   all_goals (try rfl)))

macro "walk_eval" : tactic => `(tactic|
  (repeat walk_step
   walk_close
   all_goals (try omega)))

/-- The state seen as its own environment's builder is itself. -/
@[simp] theorem stateAt_self (s : State) : stateAt s.env s = s := rfl

/-- The header's outgoing environment: its cells newest first. -/
def whileBodyOut (env : Env) (k sp b ep c q : Nat) (bt : UInt8) : Env :=
  cells [("%8", .int 8 (BitVec.ofNat 8 bt.toNat)),
         ("%arrayidx10.i", .ptr (b + q)),
         ("%idxprom.i", .int 64 (BitVec.ofNat 64 q)),
         ("%7", .int 32 (BitVec.ofNat 32 q)),
         ("%arrayidx.i", .ptr (ep + k * 4)),
         ("%inc.i", .int 64 (BitVec.ofNat 64 (k + 1))),
         ("%sp.i.0248", .int 32 (BitVec.ofNat 32 sp)),
         ("%k.0.i249", .int 64 (BitVec.ofNat 64 k))] env

/-- **`WalkPtrs` survives a run of binds at other names.** -/
theorem WalkPtrs.cells_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) (cs : List (String × Value))
    (hne : ∀ c ∈ cs, c.1 ≠ "%3" ∧ c.1 ≠ "%5" ∧ c.1 ≠ "%k11.i" ∧ c.1 ≠ "%ctype.i"
      ∧ c.1 ≠ "%cst.i" ∧ c.1 ≠ "%hash1.i.i") :
    WalkPtrs G C (BlockEval.cells cs env) := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
      obtain ⟨h3, h5, hk, hc, hs, hh⟩ := hne c (by simp)
      exact (ih (fun c' hc' => hne c' (by simp [hc']))).bind
        (d := c.1) (v := c.2) h3 h5 hk hc hs hh

example (env : Env) (k sp b ep c q : Nat) (bt : UInt8) :
    lookupName (whileBodyOut env k sp b ep c q bt) "%k.0.i249" =
      some (.int 64 (BitVec.ofNat 64 k)) := by
  simp [whileBodyOut, cells, lookupName]

/-- **The header's chain.** -/
theorem whileBody_denote {calls : Calls} (env : Env) (s : State)
    {k sp ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (h5 : lookupName env "%5" = some (.ptr ep))
    (h3 : lookupName env "%3" = some (.ptr b))
    (hK : lookupName env "%k11.i" = some (.ptr (c + 32)))
    (hk2 : lookupName env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpre : s.pre = some "cleanup478.i")
    (hread : readBytes s.mem (ep + k * 4) 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) (hk63 : k < 2 ^ 63) (hk64 : k + 1 < 2 ^ 64) :
    denoteCode calls whileBodyInstrs (stateAt env s) =
      some (stateAt (whileBodyOut env k sp b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) := by
  simp only [whileBodyInstrs, whileBodyOut]
  walk_eval

/-- **The header's terminator**: `br NodeBlock21`, at the state its chain leaves. -/
theorem whileBody_term {calls : Calls} (s : State)
    {k sp ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (hpc : s.pc = "while.body.i")
    (h5 : lookupName s.env "%5" = some (.ptr ep))
    (h3 : lookupName s.env "%3" = some (.ptr b))
    (hK : lookupName s.env "%k11.i" = some (.ptr (c + 32)))
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpre : s.pre = some "cleanup478.i")
    (hread : readBytes s.mem (ep + k * 4) 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) (hk63 : k < 2 ^ 63) (hk64 : k + 1 < 2 ^ 64) :
    step calls stage2Body s =
      .jump { (stateAt (whileBodyOut s.env k sp b ep c q bt)
          { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) with
        pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hden := whileBody_denote (calls := calls) (env := s.env) (s := s)
    h5 h3 hK hk2 hsp1 hpre hread hbs hdoc hq hk63 hk64
  simp only [step, hpc, whileBody_find, whileBodyBlock]
  rw [show denoteCode calls whileBodyInstrs s =
      some (stateAt (whileBodyOut s.env k sp b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) from by
    rw [← stateAt_self s]; exact hden]
  simp only [execTerm, hpc]
  rfl

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### Separation, for the two steps' memory and log claims -/

theorem pairwise_of_mem_ne {l : List (Nat × Nat)}
    (h : List.Pairwise (fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1) l)
    {r s : Nat × Nat} (hr : r ∈ l) (hs : s ∈ l) (hne : r ≠ s) :
    r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 := by
  induction l with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hx, hxs⟩ := h
      rcases List.mem_cons.mp hr with rfl | hr'
      · rcases List.mem_cons.mp hs with rfl | hs'
        · exact absurd rfl hne
        · exact hx s hs'
      · rcases List.mem_cons.mp hs with rfl | hs'
        · rcases hx r hr' with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        · exact ih hxs hr' hs'

/-- Two members of the walk's staged list are separated. -/
theorem staged_pair {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
    c ctype cst tok sv z e nkSlot nxpSlot : Nat}
    (h : DisjointRegions (stage2StagedRegions b n ep nep xp nxp dst ndst0 ev evcap
      ndst nev err c ctype cst tok sv z e nkSlot nxpSlot))
    {r q : Nat × Nat}
    (hr : r ∈ stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e)
    (hq : q ∈ stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e) (hne : r ≠ q) :
    r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1 := by
  have h' : (stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e).Pairwise
      (fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1) := by
    unfold DisjointRegions at h
    rw [stage2StagedRegions] at h
    exact (List.pairwise_append.mp h).1
  exact pairwise_of_mem_ne h' hr hq hne

/-- **The cursor record and the log are separate**, read off the staging. -/
theorem cursor_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.c + stage2CursorExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.c := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2CursorExtent, stage2LogExtent])

/-- **The type stack and the log are separate.** -/
theorem ctype_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.ctype + stage2StackExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.ctype := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.ctype, stage2StackExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2StackExtent, stage2LogExtent])

/-- **The state stack and the log are separate.** -/
theorem cst_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.cst + stage2StackExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.cst := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.cst, stage2StackExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2StackExtent, stage2LogExtent])

/-- **A write into the cursor record leaves the log alone.** -/
theorem readBytes_log_of_cursor_write {m : Mem} {c z : Nat} {v : List UInt8}
    (hcz : c + stage2CursorExtent ≤ z ∨ z + stage2LogExtent ≤ c)
    (hv : v.length ≤ 8) {off len : Nat} (hoff : off + len ≤ stage2LogExtent) :
    readBytes (writeBytes m (c + 32) v) (z + off) len = readBytes m (z + off) len := by
  refine walkReadBytes_writeBytes_outside (start := c + 32) ?_
  rcases hcz with hcz | hcz
  · right
    simp only [stage2CursorExtent, stage2LogExtent] at *
    omega
  · left
    simp only [stage2CursorExtent, stage2LogExtent] at *
    omega

/-- **A write into a container stack at a depth inside it leaves the log alone.** -/
theorem readBytes_log_of_stack_write {m : Mem} {base z : Nat} {v : List UInt8} {sp : Nat}
    (hbz : base + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ base)
    (hsp : sp < stage2StackExtent) (hv : v.length ≤ 1)
    {off len : Nat} (hoff : off + len ≤ stage2LogExtent) :
    readBytes (writeBytes m (base + sp) v) (z + off) len = readBytes m (z + off) len := by
  refine walkReadBytes_writeBytes_outside (start := base + sp) ?_
  rcases hbz with hbz | hbz
  · right
    simp only [stage2StackExtent, stage2LogExtent] at *
    omega
  · left
    simp only [stage2StackExtent, stage2LogExtent] at *
    omega

/-- **A write into the cursor record leaves the log's base word alone.**  The clause's
address is `%z` itself rather than `%z + off`, so this is
`readBytes_log_of_cursor_write` at offset zero with the sum reduced. -/
theorem readBytes_log_base_of_cursor_write {m : Mem} {c z : Nat} {v : List UInt8}
    (hcz : c + stage2CursorExtent ≤ z ∨ z + stage2LogExtent ≤ c) (hv : v.length ≤ 8) :
    readBytes (writeBytes m (c + 32) v) z 8 = readBytes m z 8 := by
  simpa using readBytes_log_of_cursor_write (m := m) (c := c) (z := z) (v := v) hcz hv
    (off := 0) (len := 8) (by decide)

/-- **A write into a container stack leaves the log's base word alone.**
`readBytes_log_of_stack_write` at offset zero. -/
theorem readBytes_log_base_of_stack_write {m : Mem} {base z : Nat} {v : List UInt8} {sp : Nat}
    (hbz : base + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ base)
    (hsp : sp < stage2StackExtent) (hv : v.length ≤ 1) :
    readBytes (writeBytes m (base + sp) v) z 8 = readBytes m z 8 := by
  simpa using readBytes_log_of_stack_write (m := m) (base := base) (z := z) (v := v)
    (sp := sp) hbz hsp hv (off := 0) (len := 8) (by decide)

end LeanLLVM.Refinement
