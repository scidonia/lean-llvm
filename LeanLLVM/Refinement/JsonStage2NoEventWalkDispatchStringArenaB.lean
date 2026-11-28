/-
The no-event walk's string class: the arena byte-sum loop.

`JsonStage2NoEventWalkString` stops at `if.end239`'s entry and
`JsonStage2NoEventWalkStringB` gives the class's carry and its trace step.  This
module is the walk's own body between them: after the `s2_string_body` call and
the result's dispatch, the loop at `for.body270` sums the decoded body's bytes
into the arena word, `for.cond.cleanup269` advances the logical arena's length,
and `cleanup287` counts the token, adds the record's contribution and hands to
`after_value`.

**The sum identity.**  The loop reads eight bytes per revolution from the
scratch base (`%scratch` and the preheader's seven `%invariant.gep1650…1662`),
and the epilogue reads the remaining `len mod 8` bytes one at a time.  The
identity proved here is `%arena.5.lcssa = (%arena.0.ph1406 + byteSum body) mod
2 ^ 64` for the body the callee wrote at the scratch base, split as `len / 8`
revolutions plus `len mod 8` epilogue steps: a generic eight-byte revolution
(`arenaBBody270Tail_denote`) is instantiated at trip counts `len / 8` and
`len mod 8`, and the two partial sums are joined by `byteSum_append` over the
`take`/`drop` split.

The route changes no memory (the block's only call is `llvm.lifetime.end`, which
the selection answers without a write), so the export carries `s'.mem = s.mem`
and every frame the caller held survives unchanged.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkStringB

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### Bit-vector and byte arithmetic

The two masks the unrolled loop's preheader forms, the eight-bit word the loads
read, and the modular sum the accumulator carries. -/

/-- **The epilogue's count**: `%31 &&& 7` is the length modulo eight. -/
theorem arenaB_ofNat_and_seven (x : Nat) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (x % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show 7 % 2 ^ 64 = 7 from by decide]
  rw [show (7 : Nat) = 2 ^ 3 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [show (2 : Nat) ^ 3 = 8 from by decide]
  rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : x % 8 < 2 ^ 64)]

/-- **Clearing the low three bits is rounding down to a multiple of eight.** -/
theorem arenaB_and_clear_low_three (x : Nat) (hx : x < 2 ^ 64) :
    x &&& 18446744073709551608 = 8 * (x / 8) := by
  have hm8 : (18446744073709551608 : Nat) / 8 = 2 ^ 61 - 1 := by decide
  have hmmod : (18446744073709551608 : Nat) % 8 = 0 := by decide
  have hd : (x &&& 18446744073709551608) / 8 = x / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from by decide, Nat.and_div_two_pow, hm8,
      Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.mod_eq_of_lt
    omega
  have hmod : (x &&& 18446744073709551608) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from by decide, Nat.and_mod_two_pow, hmmod]
    simp
  have := Nat.div_add_mod (x &&& 18446744073709551608) 8
  omega

/-- **The main loop's trip count**: `%31 &&& ~7` is eight times the length's
quotient by eight. -/
theorem arenaB_ofNat_and_unroll (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 18446744073709551608 =
      BitVec.ofNat 64 (8 * (x / 8)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show 18446744073709551608 % 2 ^ 64 = 18446744073709551608 from by decide]
  rw [Nat.mod_eq_of_lt hx, arenaB_and_clear_low_three x hx]
  rw [Nat.mod_eq_of_lt (by omega : 8 * (x / 8) < 2 ^ 64)]

/-- **A word sum is the sum's residue.** -/
theorem arenaB_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.add_mod]
  simp only [Nat.mod_mod]
  exact (Nat.add_mod a b (2 ^ 64)).symm

/-- **A successor at 64 bits.** -/
theorem arenaB_ofNat_succ {k : Nat} (h : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by
  have h1 : (1 : BitVec 64) = BitVec.ofNat 64 1 := by decide
  rw [h1, arenaB_ofNat_add]

/-- **`icmp ult` is zero at or above the `Nat` order.** -/
theorem arenaB_icmp_ult_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : b ≤ a) :
    evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0 := by
  have hlt : ¬ BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) := by
    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    simp
    omega
  simp [evalICmp, hlt]

/-- **`icmp eq` is one at equal words.** -/
theorem arenaB_icmp_eq_one {w : Nat} {x y : BitVec w} (h : x = y) :
    evalICmp .eq x y = 1 := by
  simp [evalICmp, h]

/-- **`icmp eq` is zero at distinct words.** -/
theorem arenaB_icmp_eq_zero {w : Nat} {x y : BitVec w} (h : x ≠ y) :
    evalICmp .eq x y = 0 := by
  simp [evalICmp, h]

/-- A cell list appended to a cell list. -/
theorem arenaB_cells_append : ∀ (a b : List (String × Value)) (env : Env),
    cells (a ++ b) env = cells a (cells b env)
  | [], _, _ => rfl
  | _ :: cs, b, env => by
      simp only [List.cons_append, cells, arenaB_cells_append cs b env]

/-- **A leading `phi` run's bindings are the cell list, newest first.** -/
theorem arenaB_bindAll_stateAt (vs : List (String × Value)) (env : Env) (s : State) :
    (stateAt env s).bindAll vs = stateAt (cells vs.reverse env) s := by
  induction vs generalizing env with
  | nil => rfl
  | cons x rest ih =>
      obtain ⟨n, v⟩ := x
      change (stateAt ((n, v) :: env) s).bindAll rest = _
      rw [ih]
      simp only [List.reverse_cons, arenaB_cells_append, cells]


/-! ### `for.cond266.preheader`: the callee's length word

The block loads `%outn205`'s word (`%31`, the decoded length the callee wrote)
and tests it against zero. -/

/-- `for.cond266.preheader`, as instructions. -/
def arenaBPreheaderInstrs : List Instr :=
  [ Instr.load "%31" (Ty.int 64) (Operand.reg "%outn205"),
    Instr.icmp "%cmp2671048.not" IPred.eq 64 (Operand.reg "%31")
      (Operand.imm (.int 64 (BitVec.ofNat 64 0))) ]

/-- `for.cond266.preheader`, pinned. -/
def arenaBPreheaderBlock : Block :=
  { name := "for.cond266.preheader", instrs := arenaBPreheaderInstrs,
    term := Term.condbr (Operand.reg "%cmp2671048.not") "for.cond.cleanup269"
      "for.body270.preheader" }

theorem arenaBPreheaderBlock_find :
    stage2NoEventBody.findBlock "for.cond266.preheader" = some arenaBPreheaderBlock := by
  decide

/-- The cells `for.cond266.preheader` binds: the length word and the zero test. -/
def arenaBPreheaderCells (len : Nat) : List (String × Value) :=
  [("%cmp2671048.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 len) (BitVec.ofNat 64 0))),
   ("%31", .int 64 (BitVec.ofNat 64 len))]

/-- **`for.cond266.preheader`'s run.** -/
theorem arenaBPreheader_denote (calls : Calls) (env : Env) (s : State) {outn len : Nat}
    (houtn : lookupName env "%outn205" = some (.ptr outn))
    (hread : readBytes s.mem outn 8 = some (natToBytes len 8))
    (hlen : len < 2 ^ 64) :
    denoteCode calls arenaBPreheaderInstrs (stateAt env s) =
      some (stateAt (cells (arenaBPreheaderCells len) env) s) := by
  simp only [arenaBPreheaderInstrs]
  rw [denoteCode_load64 (calls := calls) (env := env) (s := s) (d := "%31")
    (p := "%outn205") (a := outn) (v := BitVec.ofNat 64 len) houtn (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]; exact hread)]
  rw [denoteCode_icmp_eq_imm (calls := calls)
    (env := ("%31", .int 64 (BitVec.ofNat 64 len)) :: env) (s := s)
    (d := "%cmp2671048.not") (a := "%31") (x := BitVec.ofNat 64 len)
    (c := BitVec.ofNat 64 0) (by simp only [lookupName_cons_self])]
  simp only [arenaBPreheaderCells, cells, denoteCode, denoteRun, State.bindAll]

/-- **`for.cond266.preheader`'s step**, at the zero arm. -/
theorem arenaBPreheader_step_zero {calls : Calls} {s : State} {outn len : Nat}
    (hpc : s.pc = "for.cond266.preheader") (hlen0 : len = 0)
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hread : readBytes s.mem outn 8 = some (natToBytes len 8))
    (hlenLt : len < 2 ^ 64) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBPreheaderCells len) s.env) s
        "for.cond.cleanup269") := by
  have hcode := arenaBPreheader_denote (calls := calls) (env := s.env) (s := s)
    (outn := outn) (len := len) houtn hread hlenLt
  have hbit : lookupName (cells (arenaBPreheaderCells len) s.env) "%cmp2671048.not" =
      some (.int 1 (1 : BitVec 1)) := by
    subst hlen0
    simp only [arenaBPreheaderCells, cells, lookupName_cons_self]
    rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl, arenaB_icmp_eq_one rfl]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBPreheaderBlock_find)
    (by simpa only [stateAt, arenaBPreheaderBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **`for.cond266.preheader`'s step**, at the non-zero arm. -/
theorem arenaBPreheader_step_nonzero {calls : Calls} {s : State} {outn len : Nat}
    (hpc : s.pc = "for.cond266.preheader") (hlen0 : len ≠ 0)
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hread : readBytes s.mem outn 8 = some (natToBytes len 8))
    (hlenLt : len < 2 ^ 64) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBPreheaderCells len) s.env) s
        "for.body270.preheader") := by
  have hcode := arenaBPreheader_denote (calls := calls) (env := s.env) (s := s)
    (outn := outn) (len := len) houtn hread hlenLt
  have hne : BitVec.ofNat 64 len ≠ (BitVec.ofNat 64 0 : BitVec 64) := by
    intro hc
    apply hlen0
    have h := congrArg BitVec.toNat hc
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt, Nat.zero_mod] using h
  have hbit : lookupName (cells (arenaBPreheaderCells len) s.env) "%cmp2671048.not" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBPreheaderCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hne]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBPreheaderBlock_find)
    (by simpa only [stateAt, arenaBPreheaderBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### `for.body270.preheader`: the epilogue count and the trip test -/

/-- `for.body270.preheader`, as instructions. -/
def arenaBBodyPreInstrs : List Instr :=
  [ Instr.binop "%xtraiter" BinOp.and 64 (Operand.reg "%31")
      (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
    Instr.icmp "%32" IPred.ult 64 (Operand.reg "%31")
      (Operand.imm (.int 64 (BitVec.ofNat 64 8))) ]

/-- `for.body270.preheader`, pinned. -/
def arenaBBodyPreBlock : Block :=
  { name := "for.body270.preheader", instrs := arenaBBodyPreInstrs,
    term := Term.condbr (Operand.reg "%32") "for.cond.cleanup269.loopexit.unr-lcssa"
      "for.body270.preheader.new" }

theorem arenaBBodyPreBlock_find :
    stage2NoEventBody.findBlock "for.body270.preheader" = some arenaBBodyPreBlock := by
  decide

/-- The cells `for.body270.preheader` binds. -/
def arenaBBodyPreCells (len : Nat) : List (String × Value) :=
  [("%32", .int 1 (evalICmp .ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 8))),
   ("%xtraiter", .int 64 (BitVec.ofNat 64 len &&& BitVec.ofNat 64 7))]

/-- **`for.body270.preheader`'s run.** -/
theorem arenaBBodyPre_denote (calls : Calls) (env : Env) (s : State) {len : Nat}
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len))) :
    denoteCode calls arenaBBodyPreInstrs (stateAt env s) =
      some (stateAt (cells (arenaBBodyPreCells len) env) s) := by
  simp only [arenaBBodyPreInstrs]
  rw [denoteCode_and_imm (calls := calls) (env := env) (s := s) (d := "%xtraiter")
    (a := "%31") (x := BitVec.ofNat 64 len) (c := BitVec.ofNat 64 7) h31]
  rw [denoteCode_icmp_ult_imm (calls := calls)
    (env := ("%xtraiter", .int 64 (BitVec.ofNat 64 len &&& BitVec.ofNat 64 7)) :: env)
    (s := s) (d := "%32") (a := "%31") (x := BitVec.ofNat 64 len)
    (c := BitVec.ofNat 64 8)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact h31)]
  simp only [arenaBBodyPreCells, cells, denoteCode, denoteRun, State.bindAll]

/-- **`for.body270.preheader`'s step**: below eight, straight to the loop exit's
`phi` merge; at or above, to the unrolled loop's preheader. -/
theorem arenaBBodyPre_step_lt {calls : Calls} {s : State} {len : Nat}
    (hpc : s.pc = "for.body270.preheader") (hlen : len < 8)
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (hlenLt : len < 2 ^ 64) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBBodyPreCells len) s.env) s
        "for.cond.cleanup269.loopexit.unr-lcssa") := by
  have hcode := arenaBBodyPre_denote (calls := calls) (env := s.env) (s := s) (len := len) h31
  have hbit : lookupName (cells (arenaBBodyPreCells len) s.env) "%32" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [arenaBBodyPreCells, cells, lookupName_cons_self]
    rw [stage2NoEventWalkStringB_ult hlenLt (by decide) hlen]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBodyPreBlock_find)
    (by simpa only [stateAt, arenaBBodyPreBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **`for.body270.preheader`'s step**: at or above eight, to the unrolled loop. -/
theorem arenaBBodyPre_step_ge {calls : Calls} {s : State} {len : Nat}
    (hpc : s.pc = "for.body270.preheader") (hlen : 8 ≤ len)
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (hlenLt : len < 2 ^ 64) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBBodyPreCells len) s.env) s
        "for.body270.preheader.new") := by
  have hcode := arenaBBodyPre_denote (calls := calls) (env := s.env) (s := s) (len := len) h31
  have hbit : lookupName (cells (arenaBBodyPreCells len) s.env) "%32" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBBodyPreCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_ult_zero hlenLt (by decide) hlen]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBodyPreBlock_find)
    (by simpa only [stateAt, arenaBBodyPreBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### `for.body270.preheader.new`: the unrolled trip count -/

/-- `for.body270.preheader.new`, as instructions. -/
def arenaBBodyPreNewInstrs : List Instr :=
  [ Instr.binop "%unroll_iter" BinOp.and 64 (Operand.reg "%31")
      (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551608))) ]

/-- `for.body270.preheader.new`, pinned. -/
def arenaBBodyPreNewBlock : Block :=
  { name := "for.body270.preheader.new", instrs := arenaBBodyPreNewInstrs,
    term := Term.br "for.body270" }

theorem arenaBBodyPreNewBlock_find :
    stage2NoEventBody.findBlock "for.body270.preheader.new" =
      some arenaBBodyPreNewBlock := by
  decide

/-- **`for.body270.preheader.new`'s run.** -/
theorem arenaBBodyPreNew_denote (calls : Calls) (env : Env) (s : State) {len : Nat}
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len))) :
    denoteCode calls arenaBBodyPreNewInstrs (stateAt env s) =
      some (stateAt
        (("%unroll_iter", .int 64 (BitVec.ofNat 64 len &&&
          BitVec.ofNat 64 18446744073709551608)) :: env) s) := by
  simp only [arenaBBodyPreNewInstrs]
  rw [denoteCode_and_imm (calls := calls) (env := env) (s := s) (d := "%unroll_iter")
    (a := "%31") (x := BitVec.ofNat 64 len) (c := BitVec.ofNat 64 18446744073709551608)
    h31]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- **`for.body270.preheader.new`'s step.** -/
theorem arenaBBodyPreNew_step {calls : Calls} {s : State} {len : Nat}
    (hpc : s.pc = "for.body270.preheader.new")
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len))) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (("%unroll_iter", .int 64 (BitVec.ofNat 64 len &&&
          BitVec.ofNat 64 18446744073709551608)) :: s.env) s "for.body270") := by
  have hcode := arenaBBodyPreNew_denote (calls := calls) (env := s.env) (s := s) (len := len) h31
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBodyPreNewBlock_find)
    (by simpa only [stateAt, arenaBBodyPreNewBlock] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep





/-! ### Axiom footprints -/

#print axioms arenaB_ofNat_and_seven
#print axioms arenaB_and_clear_low_three
#print axioms arenaB_ofNat_and_unroll
#print axioms arenaBPreheaderBlock_find
#print axioms arenaBPreheader_denote
#print axioms arenaBPreheader_step_nonzero
#print axioms arenaBBodyPreBlock_find
#print axioms arenaBBodyPre_step_ge
#print axioms arenaBBodyPreNew_step



/-! ### A poison-tolerant `phi` run -/

/-- The bindings a leading `phi` run selects, with a poison incoming admitted. -/
inductive ArenaBPhiSelects (s : State) (p : String) :
    List PhiSpec → List (String × Value) → Prop
  | nil : ArenaBPhiSelects s p [] []
  | cons {sp : PhiSpec} {specs : List PhiSpec} {vs : List (String × Value)}
      {op : Operand} {v : Value} :
      phiIncoming p sp.incoming = some op →
      phiSelect s sp.incoming = some v →
      ArenaBPhiSelects s p specs vs →
      ArenaBPhiSelects s p (sp :: specs) ((sp.dst, v) :: vs)

/-- **A poison-tolerant run is one step.** -/
theorem arenaB_denoteRun_phiRun {calls : Calls} {s : State} {p : String}
    {specs : List PhiSpec} {vs : List (String × Value)} {rest : List Instr}
    {pend : List (String × Value)}
    (hpre : s.pre = some p) (hsel : ArenaBPhiSelects s p specs vs) :
    denoteRun calls pend (specs.map PhiSpec.instr ++ rest) s =
      denoteRun calls (pend ++ vs) rest s := by
  induction hsel generalizing pend with
  | nil => simp
  | cons hinc hselv _ ih =>
      simp only [List.map_cons, List.cons_append, PhiSpec.instr, denoteRun, hselv]
      rw [ih, List.append_assoc, List.singleton_append]

/-- **A poison-tolerant run at `denoteCode`.** -/
theorem arenaB_denoteCode_phiRun {calls : Calls} {s : State} {p : String}
    {specs : List PhiSpec} {vs : List (String × Value)} {rest : List Instr}
    (hpre : s.pre = some p) (hsel : ArenaBPhiSelects s p specs vs)
    (hrest : startsWithPhi rest = false) :
    denoteCode calls (specs.map PhiSpec.instr ++ rest) s =
      denoteCode calls rest (s.bindAll vs) := by
  rw [denoteCode, arenaB_denoteRun_phiRun hpre hsel, List.nil_append,
    denoteRun_nil_pend hrest]
  rfl

/-- **A register operand's `phi` selection.** -/
theorem arenaB_phiSel_reg {s : State} {p : String} {inc : List (String × Operand)}
    {n : String} {v : Value} (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = some (.reg n))
    (hlook : lookupName s.env n = some v) (hv : v ≠ .poison := by intro hh; cases hh) :
    phiSelect s inc = some v := by
  simp only [phiSelect, hpre, hinc]
  simp only [evalOperand, hlook]
  cases v with
  | poison => exact absurd rfl hv
  | int w x => rfl
  | ptr a => rfl
  | vec n w l => rfl
  | vecPoison n w l => rfl
  | float b => rfl

/-- **An integer literal's `phi` selection.** -/
theorem arenaB_phiSel_int {s : State} {p : String} {inc : List (String × Operand)}
    {w : Nat} {x : BitVec w} (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = some (.imm (.int w x))) :
    phiSelect s inc = some (.int w x) := by
  simp only [phiSelect, hpre, hinc, evalOperand, Const.toValue]

/-- **A poison literal's `phi` selection.** -/
theorem arenaB_phiSel_poison {s : State} {p : String} {inc : List (String × Operand)}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = some (.imm .poison)) :
    phiSelect s inc = some .poison := by
  simp only [phiSelect, hpre, hinc]

/-! ### The eight-byte revolution's group and tail -/

/-- The four cells one byte group binds. -/
def arenaBGroupCells (a ip : Nat) (x : BitVec 64) (b : UInt8)
    (g ld zx d : String) : List (String × Value) :=
  [ (d, .int 64 (x + BitVec.ofNat 64 b.toNat)),
    (zx, .int 64 (BitVec.ofNat 64 b.toNat)),
    (ld, .int 8 (BitVec.ofNat 8 b.toNat)),
    (g, .ptr (a + ip)) ]


/-- A byte read at `addr` from a one-byte read. -/
theorem arenaB_load8_value {m : Mem} {a : Nat} {b : UInt8}
    (h : readBytes m a 1 = some [b]) :
    loadValue m (Ty.int 8) a = some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
  simp only [loadValue, show (8 + 7) / 8 = 1 from rfl,
    show (8 = 0) = False from by decide, ite_false, h, bytesToNat,
    Nat.mul_zero, Nat.add_zero]

/-- The `i8` load's instruction step. -/
theorem arenaB_step_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) :
    evalInstr calls (stateAt env s) (.load d (Ty.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) := by
  have hop : evalOperand (stateAt env s) (.reg p) = some (.ptr a) := by
    simp only [evalOperand, stateAt, hp]
  have hl : loadValue (stateAt env s).mem (Ty.int 8) a =
      some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
    rw [show (stateAt env s).mem = s.mem from rfl]
    exact arenaB_load8_value hv
  simp only [evalInstr, hop]
  rw [hl]
  simp only [State.bind, stateAt]

/-- The `i8` load's chain step. -/
theorem arenaB_denoteCode_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) (is : List Instr) :
    denoteCode calls (.load d (Ty.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (arenaB_step_load8 calls env s d p hp hv)]

/-- **One eight-byte group**: the address, the byte, its widening and the add
into the accumulator. -/
theorem arenaB_byteGroup (calls : Calls) (env : Env) (s : State)
    (g ld zx d acc base off : String) {a : Nat} {i x : BitVec 64} {b : UInt8}
    (hbase : lookupName env base = some (.ptr a))
    (hoff : lookupName env off = some (.int 64 i))
    (hpos : (i.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some [b])
    (hacc : lookupName env acc = some (.int 64 x))
    (hne_g : g ≠ acc) (hne_ld : ld ≠ acc) (hne_zx : zx ≠ acc)
    (is : List Instr) :
    denoteCode calls
        (Instr.gep g (Ty.int 8) (.reg base) (.reg off) ::
          Instr.load ld (Ty.int 8) (.reg g) ::
          Instr.zext zx 8 64 (.reg ld) ::
          Instr.binop d BinOp.add 64 (.reg acc) (.reg zx) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 64 (x + BitVec.ofNat 64 b.toNat)) ::
          (zx, .int 64 (BitVec.ofNat 64 b.toNat)) ::
          (ld, .int 8 (BitVec.ofNat 8 b.toNat)) ::
          (g, .ptr (a + (i.signExtend 64).toNat)) :: env) s) := by
  rw [denoteCode_gep8_reg (calls := calls) (env := env) (s := s) (d := g)
    (base := base) (off := off) (a := a) (idx := i) hbase hoff hpos]
  rw [arenaB_denoteCode_load8 (calls := calls)
    (env := (g, .ptr (a + (i.signExtend 64).toNat)) :: env) (s := s) (d := ld)
    (p := g) (a := a + (i.signExtend 64).toNat) (b := b)
    (by simp only [lookupName_cons_self]) hread]
  rw [denoteCode_zext (calls := calls)
    (env := (ld, .int 8 (BitVec.ofNat 8 b.toNat)) ::
      (g, .ptr (a + (i.signExtend 64).toNat)) :: env) (s := s) (d := zx) (v := ld)
    (wIn := 8) (wOut := 64) (x := BitVec.ofNat 8 b.toNat)
    (by simp only [lookupName_cons_self])]
  rw [show (BitVec.ofNat 8 b.toNat).toNat = b.toNat from by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := b.toNat_lt; simpa using this)]]
  rw [denoteCode_add_reg (calls := calls)
    (env := (zx, .int 64 (BitVec.ofNat 64 b.toNat)) ::
      (ld, .int 8 (BitVec.ofNat 8 b.toNat)) ::
      (g, .ptr (a + (i.signExtend 64).toNat)) :: env) (s := s) (d := d)
    (a := acc) (b := zx) (x := x) (y := BitVec.ofNat 64 b.toNat)
    (by
      rw [lookupName_cons_ne _ _ hne_zx, lookupName_cons_ne _ _ hne_ld,
        lookupName_cons_ne _ _ hne_g]
      exact hacc)
    (by simp only [lookupName_cons_self])]

/-- **One eight-byte group at the address offset `ip`.** -/
theorem arenaB_byteGroup_ip (calls : Calls) (env : Env) (s : State)
    (g ld zx d acc base off : String) {a ip : Nat} {i x : BitVec 64} {b : UInt8}
    (hbase : lookupName env base = some (.ptr a))
    (hoff : lookupName env off = some (.int 64 i))
    (hip : (i.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hread : readBytes s.mem (a + ip) 1 = some [b])
    (hacc : lookupName env acc = some (.int 64 x))
    (hne_g : g ≠ acc) (hne_ld : ld ≠ acc) (hne_zx : zx ≠ acc)
    (is : List Instr) :
    denoteCode calls
        (Instr.gep g (Ty.int 8) (.reg base) (.reg off) ::
          Instr.load ld (Ty.int 8) (.reg g) ::
          Instr.zext zx 8 64 (.reg ld) ::
          Instr.binop d BinOp.add 64 (.reg acc) (.reg zx) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt (cells (arenaBGroupCells a ip x b g ld zx d) env) s) := by
  have h := arenaB_byteGroup (calls := calls) (env := env) (s := s)
    (g := g) (ld := ld) (zx := zx) (d := d) (acc := acc) (base := base) (off := off)
    (a := a) (i := i) (x := x) (b := b) hbase hoff (by rw [hip]; exact hpos)
    (by rw [hip]; exact hread) hacc hne_g hne_ld hne_zx is
  simpa only [arenaBGroupCells, cells, hip] using h


/-- The loop body's instructions after its `phi` run. -/
def arenaBBody270TailInstrs : List Instr :=
  [
    Instr.gep "%arrayidx271" (Ty.int 8) (Operand.reg "%scratch") (Operand.reg "%i265.01050"),
    Instr.load "%35" (Ty.int 8) (Operand.reg "%arrayidx271"),
    Instr.zext "%conv272" 8 64 (Operand.reg "%35"),
    Instr.binop "%add273" BinOp.add 64 (Operand.reg "%arena.51049") (Operand.reg "%conv272"),
    Instr.gep "%gep1651" (Ty.int 8) (Operand.reg "%invariant.gep1650") (Operand.reg "%i265.01050"),
    Instr.load "%36" (Ty.int 8) (Operand.reg "%gep1651"),
    Instr.zext "%conv272.1" 8 64 (Operand.reg "%36"),
    Instr.binop "%add273.1" BinOp.add 64 (Operand.reg "%add273") (Operand.reg "%conv272.1"),
    Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
    Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
    Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
    Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
    Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
    Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
    Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
    Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
    Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
    Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
    Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
    Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
    Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
    Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
    Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
    Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
    Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
    Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
    Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
    Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
    Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
    Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
    Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
    Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
    Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
    Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
    Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter")
  ]

/-- The cells the loop body's eight groups and its three tail instructions
bind, newest first. -/
def arenaBBody270TailCells (ip sc : Nat) (i acc n u : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : List (String × Value) :=
  [("%niter.ncmp.7", .int 1 (evalICmp .eq (n + BitVec.ofNat 64 8) u)),
   ("%niter.next.7", .int 64 (n + BitVec.ofNat 64 8)),
   ("%inc275.7", .int 64 (i + BitVec.ofNat 64 8)),
   ("%add273.7", .int 64 ((((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) + BitVec.ofNat 64 b6.toNat) + BitVec.ofNat 64 b7.toNat)),
   ("%conv272.7", .int 64 (BitVec.ofNat 64 b7.toNat)),
   ("%42", .int 8 (BitVec.ofNat 8 b7.toNat)),
   ("%gep1663", .ptr ((sc + 7) + ip)),
   ("%add273.6", .int 64 (((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) + BitVec.ofNat 64 b6.toNat)),
   ("%conv272.6", .int 64 (BitVec.ofNat 64 b6.toNat)),
   ("%41", .int 8 (BitVec.ofNat 8 b6.toNat)),
   ("%gep1661", .ptr ((sc + 6) + ip)),
   ("%add273.5", .int 64 ((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat)),
   ("%conv272.5", .int 64 (BitVec.ofNat 64 b5.toNat)),
   ("%40", .int 8 (BitVec.ofNat 8 b5.toNat)),
   ("%gep1659", .ptr ((sc + 5) + ip)),
   ("%add273.4", .int 64 (((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat)),
   ("%conv272.4", .int 64 (BitVec.ofNat 64 b4.toNat)),
   ("%39", .int 8 (BitVec.ofNat 8 b4.toNat)),
   ("%gep1657", .ptr ((sc + 4) + ip)),
   ("%add273.3", .int 64 ((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat)),
   ("%conv272.3", .int 64 (BitVec.ofNat 64 b3.toNat)),
   ("%38", .int 8 (BitVec.ofNat 8 b3.toNat)),
   ("%gep1655", .ptr ((sc + 3) + ip)),
   ("%add273.2", .int 64 (((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat)),
   ("%conv272.2", .int 64 (BitVec.ofNat 64 b2.toNat)),
   ("%37", .int 8 (BitVec.ofNat 8 b2.toNat)),
   ("%gep1653", .ptr ((sc + 2) + ip)),
   ("%add273.1", .int 64 ((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat)),
   ("%conv272.1", .int 64 (BitVec.ofNat 64 b1.toNat)),
   ("%36", .int 8 (BitVec.ofNat 8 b1.toNat)),
   ("%gep1651", .ptr ((sc + 1) + ip)),
   ("%add273", .int 64 (acc + BitVec.ofNat 64 b0.toNat)),
   ("%conv272", .int 64 (BitVec.ofNat 64 b0.toNat)),
   ("%35", .int 8 (BitVec.ofNat 8 b0.toNat)),
   ("%arrayidx271", .ptr ((sc + 0) + ip))]

/-- **The loop body's tail**: eight byte groups and the count's advance. -/
theorem arenaBBody270Tail_denote (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {i acc n u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hg1 : lookupName env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hoff : lookupName env "%i265.01050" = some (.int 64 i))
    (hacc : lookupName env "%arena.51049" = some (.int 64 acc))
    (hn : lookupName env "%niter" = some (.int 64 n))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hip : (i.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7]) :
    denoteCode calls arenaBBody270TailInstrs (stateAt env s) =
      some (stateAt (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7) env) s) := by
  let E1 : Env := cells (arenaBGroupCells (sc + 0) ip acc b0 "%arrayidx271" "%35" "%conv272" "%add273") env
  let E2 : Env := cells (arenaBGroupCells (sc + 1) ip (acc + BitVec.ofNat 64 b0.toNat) b1 "%gep1651" "%36" "%conv272.1" "%add273.1") E1
  let E3 : Env := cells (arenaBGroupCells (sc + 2) ip ((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) b2 "%gep1653" "%37" "%conv272.2" "%add273.2") E2
  let E4 : Env := cells (arenaBGroupCells (sc + 3) ip (((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) b3 "%gep1655" "%38" "%conv272.3" "%add273.3") E3
  let E5 : Env := cells (arenaBGroupCells (sc + 4) ip ((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) b4 "%gep1657" "%39" "%conv272.4" "%add273.4") E4
  let E6 : Env := cells (arenaBGroupCells (sc + 5) ip (((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) b5 "%gep1659" "%40" "%conv272.5" "%add273.5") E5
  let E7 : Env := cells (arenaBGroupCells (sc + 6) ip ((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) b6 "%gep1661" "%41" "%conv272.6" "%add273.6") E6
  let E8 : Env := cells (arenaBGroupCells (sc + 7) ip (((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) + BitVec.ofNat 64 b6.toNat) b7 "%gep1663" "%42" "%conv272.7" "%add273.7") E7

  calc
    denoteCode calls arenaBBody270TailInstrs (stateAt env s) =
        denoteCode calls [ Instr.gep "%gep1651" (Ty.int 8) (Operand.reg "%invariant.gep1650") (Operand.reg "%i265.01050"),
        Instr.load "%36" (Ty.int 8) (Operand.reg "%gep1651"),
        Instr.zext "%conv272.1" 8 64 (Operand.reg "%36"),
        Instr.binop "%add273.1" BinOp.add 64 (Operand.reg "%add273") (Operand.reg "%conv272.1"),
        Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
        Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
        Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
        Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
        Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E1 s) := by
      simp only [arenaBBody270TailInstrs]
      exact arenaB_byteGroup_ip (calls := calls) (env := env) (s := s)
        (g := "%arrayidx271") (ld := "%35") (zx := "%conv272") (d := "%add273") (acc := "%arena.51049")
        (base := "%scratch") (off := "%i265.01050") (a := sc + 0) (ip := ip) (i := i) (x := acc) (b := b0)
        (by block_lk) (by block_lk) hip hpos
        hr0 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1651" (Ty.int 8) (Operand.reg "%invariant.gep1650") (Operand.reg "%i265.01050"),
        Instr.load "%36" (Ty.int 8) (Operand.reg "%gep1651"),
        Instr.zext "%conv272.1" 8 64 (Operand.reg "%36"),
        Instr.binop "%add273.1" BinOp.add 64 (Operand.reg "%add273") (Operand.reg "%conv272.1"),
        Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
        Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
        Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
        Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
        Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
        Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
        Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
        Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
        Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E2 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E1) (s := s)
        (g := "%gep1651") (ld := "%36") (zx := "%conv272.1") (d := "%add273.1") (acc := "%add273")
        (base := "%invariant.gep1650") (off := "%i265.01050") (a := sc + 1) (ip := ip) (i := i) (x := acc + BitVec.ofNat 64 b0.toNat) (b := b1)
        (by block_lk) (by block_lk) hip hpos
        hr1 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
        Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
        Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
        Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
        Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E3 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E2) (s := s)
        (g := "%gep1653") (ld := "%37") (zx := "%conv272.2") (d := "%add273.2") (acc := "%add273.1")
        (base := "%invariant.gep1652") (off := "%i265.01050") (a := sc + 2) (ip := ip) (i := i) (x := (acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) (b := b2)
        (by block_lk) (by block_lk) hip hpos
        hr2 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
        Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
        Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
        Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E4 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E3) (s := s)
        (g := "%gep1655") (ld := "%38") (zx := "%conv272.3") (d := "%add273.3") (acc := "%add273.2")
        (base := "%invariant.gep1654") (off := "%i265.01050") (a := sc + 3) (ip := ip) (i := i) (x := ((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) (b := b3)
        (by block_lk) (by block_lk) hip hpos
        hr3 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
        Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
        Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
        Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E5 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E4) (s := s)
        (g := "%gep1657") (ld := "%39") (zx := "%conv272.4") (d := "%add273.4") (acc := "%add273.3")
        (base := "%invariant.gep1656") (off := "%i265.01050") (a := sc + 4) (ip := ip) (i := i) (x := (((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) (b := b4)
        (by block_lk) (by block_lk) hip hpos
        hr4 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
        Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
        Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
        Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
        Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E6 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E5) (s := s)
        (g := "%gep1659") (ld := "%40") (zx := "%conv272.5") (d := "%add273.5") (acc := "%add273.4")
        (base := "%invariant.gep1658") (off := "%i265.01050") (a := sc + 5) (ip := ip) (i := i) (x := ((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) (b := b5)
        (by block_lk) (by block_lk) hip hpos
        hr5 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
        Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
        Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
        Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E7 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E6) (s := s)
        (g := "%gep1661") (ld := "%41") (zx := "%conv272.6") (d := "%add273.6") (acc := "%add273.5")
        (base := "%invariant.gep1660") (off := "%i265.01050") (a := sc + 6) (ip := ip) (i := i) (x := (((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) (b := b6)
        (by block_lk) (by block_lk) hip hpos
        hr6 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
        Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
        Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
        Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
        Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = denoteCode calls [ Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ] (stateAt E8 s) := by
      exact arenaB_byteGroup_ip (calls := calls) (env := E7) (s := s)
        (g := "%gep1663") (ld := "%42") (zx := "%conv272.7") (d := "%add273.7") (acc := "%add273.6")
        (base := "%invariant.gep1662") (off := "%i265.01050") (a := sc + 7) (ip := ip) (i := i) (x := ((((((acc + BitVec.ofNat 64 b0.toNat) + BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) + BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) + BitVec.ofNat 64 b5.toNat) + BitVec.ofNat 64 b6.toNat) (b := b7)
        (by block_lk) (by block_lk) hip hpos
        hr7 (by block_lk) (by decide) (by decide) (by decide)
        (is := [ Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter") ])
    _ = some (stateAt (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7) env) s) := by
      rw [denoteCode_add_imm (calls := calls) (env := E8) (s := s) (d := "%inc275.7")
        (a := "%i265.01050") (x := i) (c := BitVec.ofNat 64 8) (by block_lk)]
      rw [denoteCode_add_imm (calls := calls) (env := _) (s := s) (d := "%niter.next.7")
        (a := "%niter") (x := n) (c := BitVec.ofNat 64 8) (by block_lk)]
      rw [denoteCode_icmp_eq_reg (calls := calls) (env := _) (s := s)
        (d := "%niter.ncmp.7") (a := "%niter.next.7") (b := "%unroll_iter")
        (x := n + BitVec.ofNat 64 8) (y := u) (by block_lk) (by block_lk)]
      simp only [E1, E2, E3, E4, E5, E6, E7, E8]
      simp only [arenaBBody270TailCells, arenaBGroupCells, cells, denoteCode, denoteRun, State.bindAll]



/-- The loop body's `phi` specs. -/
def arenaBBody270PhiSpecs : List PhiSpec :=
  [ ⟨"%i265.01050", Ty.int 64,
      [("for.body270.preheader.new", .imm (.int 64 (BitVec.ofNat 64 0))),
       ("for.body270", .reg "%inc275.7")]⟩,
    ⟨"%arena.51049", Ty.int 64,
      [("for.body270.preheader.new", .reg "%arena.0.ph1406"),
       ("for.body270", .reg "%add273.7")]⟩,
    ⟨"%niter", Ty.int 64,
      [("for.body270.preheader.new", .imm (.int 64 (BitVec.ofNat 64 0))),
       ("for.body270", .reg "%niter.next.7")]⟩ ]

/-- `for.body270`, as instructions. -/
def arenaBBody270Instrs : List Instr :=
  arenaBBody270PhiSpecs.map PhiSpec.instr ++ arenaBBody270TailInstrs

/-- `for.body270`, pinned. -/
def arenaBBody270Block : Block :=
  { name := "for.body270", instrs := arenaBBody270Instrs,
    term := Term.condbr (Operand.reg "%niter.ncmp.7")
      "for.cond.cleanup269.loopexit.unr-lcssa" "for.body270" }

theorem arenaBBody270Block_find :
    stage2NoEventBody.findBlock "for.body270" = some arenaBBody270Block := by
  decide

/-- The `phi` cells of the loop body's first entry, newest first. -/
def arenaBBody270PhiCellsPre (acc : BitVec 64) : List (String × Value) :=
  [("%niter", .int 64 0), ("%arena.51049", .int 64 acc),
   ("%i265.01050", .int 64 0)]

/-- The `phi` cells of a re-entered loop body, newest first. -/
def arenaBBody270PhiCellsLoop (i acc n : BitVec 64) : List (String × Value) :=
  [("%niter", .int 64 n), ("%arena.51049", .int 64 acc),
   ("%i265.01050", .int 64 i)]

/-- The `phi` selections of the loop body's first entry. -/
theorem arenaBBody270_phiSelects_pre (env : Env) (s : State) {acc : BitVec 64}
    (hpre : s.pre = some "for.body270.preheader.new")
    (harenaphi : lookupName env "%arena.0.ph1406" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.body270.preheader.new"
      arenaBBody270PhiSpecs (arenaBBody270PhiCellsPre acc).reverse := by
  refine ArenaBPhiSelects.cons (op := .imm (.int 64 0)) (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .imm (.int 64 0)) (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_int hpre (by decide)
  · exact arenaB_phiSel_reg hpre (by decide) harenaphi
  · exact arenaB_phiSel_int hpre (by decide)

/-- The `phi` selections of a re-entered loop body. -/
theorem arenaBBody270_phiSelects_loop (env : Env) (s : State) {i acc n : BitVec 64}
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName env "%add273.7" = some (.int 64 acc))
    (hnn : lookupName env "%niter.next.7" = some (.int 64 n)) :
    ArenaBPhiSelects (stateAt env s) "for.body270"
      arenaBBody270PhiSpecs (arenaBBody270PhiCellsLoop i acc n).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%inc275.7") (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%add273.7") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%niter.next.7") (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_reg hpre (by decide) hinc
  · exact arenaB_phiSel_reg hpre (by decide) hadd
  · exact arenaB_phiSel_reg hpre (by decide) hnn

/-- **The loop body's run at its first entry.** -/
theorem arenaBBody270_denote_pre (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {acc u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpre : s.pre = some "for.body270.preheader.new")
    (harenaphi : lookupName env "%arena.0.ph1406" = some (.int 64 acc))
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hg1 : lookupName env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hip : ((0 : BitVec 64).signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7]) :
    denoteCode calls arenaBBody270Instrs (stateAt env s) =
      some (stateAt (cells (arenaBBody270TailCells ip sc 0 acc 0 u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsPre acc) env)) s) := by
  simp only [arenaBBody270Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270.preheader.new") hpre
    (arenaBBody270_phiSelects_pre env s hpre harenaphi) (by decide)]
  change denoteCode calls arenaBBody270TailInstrs
      (stateAt (cells (arenaBBody270PhiCellsPre acc) env) s) = _
  exact arenaBBody270Tail_denote (calls := calls)
    (env := cells (arenaBBody270PhiCellsPre acc) env) (s := s)
    (ip := ip) (sc := sc) (i := 0) (acc := acc) (n := 0) (u := u)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5)
    (b6 := b6) (b7 := b7)
    (by block_lk) (by block_lk) (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7

/-- **The loop body's run at a re-entry.** -/
theorem arenaBBody270_denote_loop (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {i acc n u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName env "%add273.7" = some (.int 64 acc))
    (hnn : lookupName env "%niter.next.7" = some (.int 64 n))
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hg1 : lookupName env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hip : (i.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7]) :
    denoteCode calls arenaBBody270Instrs (stateAt env s) =
      some (stateAt (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsLoop i acc n) env)) s) := by
  simp only [arenaBBody270Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270") hpre
    (arenaBBody270_phiSelects_loop env s hpre hinc hadd hnn) (by decide)]
  change denoteCode calls arenaBBody270TailInstrs
      (stateAt (cells (arenaBBody270PhiCellsLoop i acc n) env) s) = _
  exact arenaBBody270Tail_denote (calls := calls)
    (env := cells (arenaBBody270PhiCellsLoop i acc n) env) (s := s)
    (ip := ip) (sc := sc) (i := i) (acc := acc) (n := n) (u := u)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5)
    (b6 := b6) (b7 := b7)
    (by block_lk) (by block_lk) (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) (by block_lk) (by block_lk)
    (by block_lk) hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7

/-- **The loop body's step at a non-final revolution.** -/
theorem arenaBBody270_step_loop {calls : Calls} {s : State}
    {ip sc : Nat} {i acc n u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpc : s.pc = "for.body270") (hpre : s.pre = some "for.body270")
    (hinc : lookupName s.env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName s.env "%add273.7" = some (.int 64 acc))
    (hnn : lookupName s.env "%niter.next.7" = some (.int 64 n))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName s.env "%unroll_iter" = some (.int 64 u))
    (hip : (i.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7])
    (hne : n + BitVec.ofNat 64 8 ≠ u) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7)
          (cells (arenaBBody270PhiCellsLoop i acc n) s.env)) s "for.body270") := by
  have hcode := arenaBBody270_denote_loop (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hnn hsc hg1 hg2 hg3 hg4 hg5 hg6 hg7 hu hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have hbit : lookupName
      (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsLoop i acc n) s.env)) "%niter.ncmp.7" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBBody270TailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hne]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBody270Block_find)
    (by simpa only [stateAt, arenaBBody270Block] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **The loop body's step at the final revolution.** -/
theorem arenaBBody270_step_exit {calls : Calls} {s : State}
    {ip sc : Nat} {i acc n u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpc : s.pc = "for.body270") (hpre : s.pre = some "for.body270")
    (hinc : lookupName s.env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName s.env "%add273.7" = some (.int 64 acc))
    (hnn : lookupName s.env "%niter.next.7" = some (.int 64 n))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName s.env "%unroll_iter" = some (.int 64 u))
    (hip : (i.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7])
    (hexit : n + BitVec.ofNat 64 8 = u) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7)
          (cells (arenaBBody270PhiCellsLoop i acc n) s.env)) s
        "for.cond.cleanup269.loopexit.unr-lcssa") := by
  have hcode := arenaBBody270_denote_loop (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hnn hsc hg1 hg2 hg3 hg4 hg5 hg6 hg7 hu hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have hbit : lookupName
      (cells (arenaBBody270TailCells ip sc i acc n u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsLoop i acc n) s.env)) "%niter.ncmp.7" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [arenaBBody270TailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_one hexit]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBody270Block_find)
    (by simpa only [stateAt, arenaBBody270Block] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep



/-! ### `for.cond.cleanup269.loopexit.unr-lcssa`: the loop's exit merge -/

/-- The exit merge's `phi` specs. -/
def arenaBLoopexitPhiSpecs : List PhiSpec :=
  [ ⟨"%add273.lcssa.ph", Ty.int 64,
      [("for.body270.preheader", .imm .poison),
       ("for.body270", .reg "%add273.7")]⟩,
    ⟨"%i265.01050.unr", Ty.int 64,
      [("for.body270.preheader", .imm (.int 64 (BitVec.ofNat 64 0))),
       ("for.body270", .reg "%inc275.7")]⟩,
    ⟨"%arena.51049.unr", Ty.int 64,
      [("for.body270.preheader", .reg "%arena.0.ph1406"),
       ("for.body270", .reg "%add273.7")]⟩ ]

/-- The exit merge's tail. -/
def arenaBLoopexitTailInstrs : List Instr :=
  [ Instr.icmp "%lcmp.mod.not" IPred.eq 64 (Operand.reg "%xtraiter")
      (Operand.imm (.int 64 (BitVec.ofNat 64 0))) ]

/-- The exit merge, as instructions. -/
def arenaBLoopexitInstrs : List Instr :=
  arenaBLoopexitPhiSpecs.map PhiSpec.instr ++ arenaBLoopexitTailInstrs

/-- The exit merge, pinned. -/
def arenaBLoopexitBlock : Block :=
  { name := "for.cond.cleanup269.loopexit.unr-lcssa", instrs := arenaBLoopexitInstrs,
    term := Term.condbr (Operand.reg "%lcmp.mod.not") "for.cond.cleanup269"
      "for.body270.epil" }

theorem arenaBLoopexitBlock_find :
    stage2NoEventBody.findBlock "for.cond.cleanup269.loopexit.unr-lcssa" =
      some arenaBLoopexitBlock := by
  decide

/-- The exit merge's `phi` cells at the loop's edge, newest first. -/
def arenaBLoopexitPhiCellsLoop (i acc : BitVec 64) : List (String × Value) :=
  [("%arena.51049.unr", .int 64 acc), ("%i265.01050.unr", .int 64 i),
   ("%add273.lcssa.ph", .int 64 acc)]

/-- The exit merge's `phi` cells at the preheader's edge, newest first. -/
def arenaBLoopexitPhiCellsPre (acc : BitVec 64) : List (String × Value) :=
  [("%arena.51049.unr", .int 64 acc), ("%i265.01050.unr", .int 64 0),
   ("%add273.lcssa.ph", .poison)]

/-- **The exit merge's tail.** -/
theorem arenaBLoopexitTail_denote (calls : Calls) (env : Env) (s : State) {xt : BitVec 64}
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt)) :
    denoteCode calls arenaBLoopexitTailInstrs (stateAt env s) =
      some (stateAt
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) :: env) s) := by
  simp only [arenaBLoopexitTailInstrs]
  rw [denoteCode_icmp_eq_imm (calls := calls) (env := env) (s := s)
    (d := "%lcmp.mod.not") (a := "%xtraiter") (x := xt) (c := BitVec.ofNat 64 0) hxt]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- The `phi` selections at the loop's edge. -/
theorem arenaBLoopexit_phiSelects_loop (env : Env) (s : State) {i acc : BitVec 64}
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName env "%add273.7" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.body270"
      arenaBLoopexitPhiSpecs (arenaBLoopexitPhiCellsLoop i acc).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%add273.7") (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%inc275.7") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%add273.7") (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_reg hpre (by decide) hadd
  · exact arenaB_phiSel_reg hpre (by decide) hinc
  · exact arenaB_phiSel_reg hpre (by decide) hadd

/-- The `phi` selections at the preheader's edge (the poison accumulator). -/
theorem arenaBLoopexit_phiSelects_pre (env : Env) (s : State) {acc : BitVec 64}
    (hpre : s.pre = some "for.body270.preheader")
    (harenaphi : lookupName env "%arena.0.ph1406" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.body270.preheader"
      arenaBLoopexitPhiSpecs (arenaBLoopexitPhiCellsPre acc).reverse := by
  refine ArenaBPhiSelects.cons (op := .imm .poison) (by decide) ?_
    (ArenaBPhiSelects.cons (op := .imm (.int 64 0)) (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_poison hpre (by decide)
  · exact arenaB_phiSel_int hpre (by decide)
  · exact arenaB_phiSel_reg hpre (by decide) harenaphi

/-- **The exit merge's run at the loop's edge.** -/
theorem arenaBLoopexit_denote_loop (calls : Calls) (env : Env) (s : State)
    {i acc xt : BitVec 64}
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName env "%add273.7" = some (.int 64 acc))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt)) :
    denoteCode calls arenaBLoopexitInstrs (stateAt env s) =
      some (stateAt
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
          cells (arenaBLoopexitPhiCellsLoop i acc) env) s) := by
  simp only [arenaBLoopexitInstrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270") hpre
    (arenaBLoopexit_phiSelects_loop env s hpre hinc hadd) (by decide)]
  change denoteCode calls arenaBLoopexitTailInstrs
      (stateAt (cells (arenaBLoopexitPhiCellsLoop i acc) env) s) = _
  rw [arenaBLoopexitTail_denote (calls := calls)
    (env := cells (arenaBLoopexitPhiCellsLoop i acc) env) (s := s) hxt]

/-- **The exit merge's run at the preheader's edge.** -/
theorem arenaBLoopexit_denote_pre (calls : Calls) (env : Env) (s : State)
    {acc xt : BitVec 64}
    (hpre : s.pre = some "for.body270.preheader")
    (harenaphi : lookupName env "%arena.0.ph1406" = some (.int 64 acc))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt)) :
    denoteCode calls arenaBLoopexitInstrs (stateAt env s) =
      some (stateAt
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
          cells (arenaBLoopexitPhiCellsPre acc) env) s) := by
  simp only [arenaBLoopexitInstrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270.preheader") hpre
    (arenaBLoopexit_phiSelects_pre env s hpre harenaphi) (by decide)]
  change denoteCode calls arenaBLoopexitTailInstrs
      (stateAt (cells (arenaBLoopexitPhiCellsPre acc) env) s) = _
  rw [arenaBLoopexitTail_denote (calls := calls)
    (env := cells (arenaBLoopexitPhiCellsPre acc) env) (s := s) hxt]

/-- **The exit merge's step at the loop's edge**, to the cleanup entry. -/
theorem arenaBLoopexit_step_cleanup {calls : Calls} {s : State} {i acc xt : BitVec 64}
    (hpc : s.pc = "for.cond.cleanup269.loopexit.unr-lcssa")
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName s.env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName s.env "%add273.7" = some (.int 64 acc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hx0 : xt = BitVec.ofNat 64 0) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
          cells (arenaBLoopexitPhiCellsLoop i acc) s.env) s "for.cond.cleanup269") := by
  have hcode := arenaBLoopexit_denote_loop (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hxt
  have hbit : lookupName
      (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
        cells (arenaBLoopexitPhiCellsLoop i acc) s.env) "%lcmp.mod.not" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [lookupName_cons_self]
    subst hx0
    rw [arenaB_icmp_eq_one rfl]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBLoopexitBlock_find)
    (by simpa only [stateAt, arenaBLoopexitBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **The exit merge's step at the loop's edge**, to the epilogue. -/
theorem arenaBLoopexit_step_epil {calls : Calls} {s : State} {i acc xt : BitVec 64}
    (hpc : s.pc = "for.cond.cleanup269.loopexit.unr-lcssa")
    (hpre : s.pre = some "for.body270")
    (hinc : lookupName s.env "%inc275.7" = some (.int 64 i))
    (hadd : lookupName s.env "%add273.7" = some (.int 64 acc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hx0 : xt ≠ BitVec.ofNat 64 0) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
          cells (arenaBLoopexitPhiCellsLoop i acc) s.env) s "for.body270.epil") := by
  have hcode := arenaBLoopexit_denote_loop (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hxt
  have hbit : lookupName
      (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
        cells (arenaBLoopexitPhiCellsLoop i acc) s.env) "%lcmp.mod.not" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hx0]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBLoopexitBlock_find)
    (by simpa only [stateAt, arenaBLoopexitBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **The exit merge's step at the preheader's edge**, to the epilogue. -/
theorem arenaBLoopexit_step_pre {calls : Calls} {s : State} {acc xt : BitVec 64}
    (hpc : s.pc = "for.cond.cleanup269.loopexit.unr-lcssa")
    (hpre : s.pre = some "for.body270.preheader")
    (harenaphi : lookupName s.env "%arena.0.ph1406" = some (.int 64 acc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hx0 : xt ≠ BitVec.ofNat 64 0) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
          cells (arenaBLoopexitPhiCellsPre acc) s.env) s "for.body270.epil") := by
  have hcode := arenaBLoopexit_denote_pre (calls := calls) (env := s.env) (s := s)
    hpre harenaphi hxt
  have hbit : lookupName
      (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
        cells (arenaBLoopexitPhiCellsPre acc) s.env) "%lcmp.mod.not" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hx0]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBLoopexitBlock_find)
    (by simpa only [stateAt, arenaBLoopexitBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep



/-! ### `for.body270.epil`: the one-byte epilogue revolution -/

/-- The epilogue's `phi` specs. -/
def arenaBEpilPhiSpecs : List PhiSpec :=
  [ ⟨"%i265.01050.epil", Ty.int 64,
      [("for.body270.epil", .reg "%inc275.epil"),
       ("for.cond.cleanup269.loopexit.unr-lcssa", .reg "%i265.01050.unr")]⟩,
    ⟨"%arena.51049.epil", Ty.int 64,
      [("for.body270.epil", .reg "%add273.epil"),
       ("for.cond.cleanup269.loopexit.unr-lcssa", .reg "%arena.51049.unr")]⟩,
    ⟨"%epil.iter", Ty.int 64,
      [("for.body270.epil", .reg "%epil.iter.next"),
       ("for.cond.cleanup269.loopexit.unr-lcssa", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩ ]

/-- The epilogue's tail. -/
def arenaBEpilTailInstrs : List Instr :=
  [ Instr.gep "%arrayidx271.epil" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.reg "%i265.01050.epil"),
    Instr.load "%34" (Ty.int 8) (Operand.reg "%arrayidx271.epil"),
    Instr.zext "%conv272.epil" 8 64 (Operand.reg "%34"),
    Instr.binop "%add273.epil" BinOp.add 64 (Operand.reg "%arena.51049.epil")
      (Operand.reg "%conv272.epil"),
    Instr.binop "%inc275.epil" BinOp.add 64 (Operand.reg "%i265.01050.epil")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%epil.iter.next" BinOp.add 64 (Operand.reg "%epil.iter")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.icmp "%epil.iter.cmp.not" IPred.eq 64 (Operand.reg "%epil.iter.next")
      (Operand.reg "%xtraiter") ]

/-- The epilogue, as instructions. -/
def arenaBEpilInstrs : List Instr :=
  arenaBEpilPhiSpecs.map PhiSpec.instr ++ arenaBEpilTailInstrs

/-- The epilogue, pinned. -/
def arenaBEpilBlock : Block :=
  { name := "for.body270.epil", instrs := arenaBEpilInstrs,
    term := Term.condbr (Operand.reg "%epil.iter.cmp.not") "for.cond.cleanup269"
      "for.body270.epil" }

theorem arenaBEpilBlock_find :
    stage2NoEventBody.findBlock "for.body270.epil" = some arenaBEpilBlock := by
  decide

/-- The epilogue's `phi` cells at the exit merge's edge, newest first. -/
def arenaBEpilPhiCellsFirst (ie acc : BitVec 64) : List (String × Value) :=
  [("%epil.iter", .int 64 0), ("%arena.51049.epil", .int 64 acc),
   ("%i265.01050.epil", .int 64 ie)]

/-- The epilogue's `phi` cells at its own edge, newest first. -/
def arenaBEpilPhiCellsSelf (ie acc ep : BitVec 64) : List (String × Value) :=
  [("%epil.iter", .int 64 ep), ("%arena.51049.epil", .int 64 acc),
   ("%i265.01050.epil", .int 64 ie)]

/-- The epilogue's three tail cells over the group's four, newest first. -/
def arenaBEpilTailCells (ip sc : Nat) (ie acc ep xt : BitVec 64) (b : UInt8) :
    List (String × Value) :=
  [("%epil.iter.cmp.not", .int 1 (evalICmp .eq (ep + BitVec.ofNat 64 1) xt)),
   ("%epil.iter.next", .int 64 (ep + BitVec.ofNat 64 1)),
   ("%inc275.epil", .int 64 (ie + BitVec.ofNat 64 1))]

/-- **The epilogue's tail.** -/
theorem arenaBEpilTail_denote (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {ie acc ep xt : BitVec 64} {b : UInt8}
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hie : lookupName env "%i265.01050.epil" = some (.int 64 ie))
    (hacc : lookupName env "%arena.51049.epil" = some (.int 64 acc))
    (hep : lookupName env "%epil.iter" = some (.int 64 ep))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b]) :
    denoteCode calls arenaBEpilTailInstrs (stateAt env s) =
      some (stateAt (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil") env)) s) := by
  rw [show arenaBEpilTailInstrs =
      (Instr.gep "%arrayidx271.epil" (Ty.int 8) (Operand.reg "%scratch")
          (Operand.reg "%i265.01050.epil") ::
        Instr.load "%34" (Ty.int 8) (Operand.reg "%arrayidx271.epil") ::
        Instr.zext "%conv272.epil" 8 64 (Operand.reg "%34") ::
        Instr.binop "%add273.epil" BinOp.add 64 (Operand.reg "%arena.51049.epil")
          (Operand.reg "%conv272.epil") ::
        [ Instr.binop "%inc275.epil" BinOp.add 64 (Operand.reg "%i265.01050.epil")
            (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
          Instr.binop "%epil.iter.next" BinOp.add 64 (Operand.reg "%epil.iter")
            (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
          Instr.icmp "%epil.iter.cmp.not" IPred.eq 64 (Operand.reg "%epil.iter.next")
            (Operand.reg "%xtraiter") ]) from rfl]
  rw [arenaB_byteGroup_ip (calls := calls) (env := env) (s := s)
    (g := "%arrayidx271.epil") (ld := "%34") (zx := "%conv272.epil")
    (d := "%add273.epil") (acc := "%arena.51049.epil") (base := "%scratch")
    (off := "%i265.01050.epil") (a := sc) (ip := ip) (i := ie) (x := acc) (b := b)
    (by block_lk) (by block_lk) hip hpos hr (by block_lk)
    (by decide) (by decide) (by decide)
    (is := [ Instr.binop "%inc275.epil" BinOp.add 64 (Operand.reg "%i265.01050.epil")
              (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
            Instr.binop "%epil.iter.next" BinOp.add 64 (Operand.reg "%epil.iter")
              (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
            Instr.icmp "%epil.iter.cmp.not" IPred.eq 64 (Operand.reg "%epil.iter.next")
              (Operand.reg "%xtraiter") ])]
  rw [denoteCode_add_imm (calls := calls) (env := _) (s := s) (d := "%inc275.epil")
    (a := "%i265.01050.epil") (x := ie) (c := BitVec.ofNat 64 1) (by block_lk)]
  rw [denoteCode_add_imm (calls := calls) (env := _) (s := s) (d := "%epil.iter.next")
    (a := "%epil.iter") (x := ep) (c := BitVec.ofNat 64 1) (by block_lk)]
  rw [denoteCode_icmp_eq_reg (calls := calls) (env := _) (s := s)
    (d := "%epil.iter.cmp.not") (a := "%epil.iter.next") (b := "%xtraiter")
    (x := ep + BitVec.ofNat 64 1) (y := xt) (by block_lk) (by block_lk)]
  simp only [arenaBEpilTailCells, arenaBGroupCells, cells, denoteCode, denoteRun,
    State.bindAll]


/-- The `phi` selections at the exit merge's edge. -/
theorem arenaBEpil_phiSelects_first (env : Env) (s : State) {ie acc : BitVec 64}
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hiunr : lookupName env "%i265.01050.unr" = some (.int 64 ie))
    (haunr : lookupName env "%arena.51049.unr" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.cond.cleanup269.loopexit.unr-lcssa"
      arenaBEpilPhiSpecs (arenaBEpilPhiCellsFirst ie acc).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%i265.01050.unr") (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%arena.51049.unr") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .imm (.int 64 0)) (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_reg hpre (by decide) hiunr
  · exact arenaB_phiSel_reg hpre (by decide) haunr
  · exact arenaB_phiSel_int hpre (by decide)

/-- The `phi` selections at the epilogue's own edge. -/
theorem arenaBEpil_phiSelects_self (env : Env) (s : State) {ie acc ep : BitVec 64}
    (hpre : s.pre = some "for.body270.epil")
    (hinc : lookupName env "%inc275.epil" = some (.int 64 ie))
    (hadd : lookupName env "%add273.epil" = some (.int 64 acc))
    (hnext : lookupName env "%epil.iter.next" = some (.int 64 ep)) :
    ArenaBPhiSelects (stateAt env s) "for.body270.epil"
      arenaBEpilPhiSpecs (arenaBEpilPhiCellsSelf ie acc ep).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%inc275.epil") (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%add273.epil") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%epil.iter.next") (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_reg hpre (by decide) hinc
  · exact arenaB_phiSel_reg hpre (by decide) hadd
  · exact arenaB_phiSel_reg hpre (by decide) hnext

/-- **The epilogue's run at its first revolution.** -/
theorem arenaBEpil_denote_first (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {ie acc xt : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hiunr : lookupName env "%i265.01050.unr" = some (.int 64 ie))
    (haunr : lookupName env "%arena.51049.unr" = some (.int 64 acc))
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b]) :
    denoteCode calls arenaBEpilInstrs (stateAt env s) =
      some (stateAt (cells (arenaBEpilTailCells ip sc ie acc 0 xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsFirst ie acc) env))) s) := by
  simp only [arenaBEpilInstrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.cond.cleanup269.loopexit.unr-lcssa") hpre
    (arenaBEpil_phiSelects_first env s hpre hiunr haunr) (by decide)]
  change denoteCode calls arenaBEpilTailInstrs
      (stateAt (cells (arenaBEpilPhiCellsFirst ie acc) env) s) = _
  rw [arenaBEpilTail_denote (calls := calls)
    (env := cells (arenaBEpilPhiCellsFirst ie acc) env) (s := s)
    (ip := ip) (sc := sc) (ie := ie) (acc := acc) (ep := 0) (xt := xt) (b := b)
    (by block_lk) (by block_lk) (by block_lk) (by block_lk) (by block_lk)
    hip hpos hr]

/-- **The epilogue's run at a re-entry.** -/
theorem arenaBEpil_denote_self (calls : Calls) (env : Env) (s : State)
    {ip sc : Nat} {ie acc ep xt : BitVec 64} {b : UInt8}
    (hpre : s.pre = some "for.body270.epil")
    (hinc : lookupName env "%inc275.epil" = some (.int 64 ie))
    (hadd : lookupName env "%add273.epil" = some (.int 64 acc))
    (hnext : lookupName env "%epil.iter.next" = some (.int 64 ep))
    (hsc : lookupName env "%scratch" = some (.ptr sc))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b]) :
    denoteCode calls arenaBEpilInstrs (stateAt env s) =
      some (stateAt (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsSelf ie acc ep) env))) s) := by
  simp only [arenaBEpilInstrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270.epil") hpre
    (arenaBEpil_phiSelects_self env s hpre hinc hadd hnext) (by decide)]
  change denoteCode calls arenaBEpilTailInstrs
      (stateAt (cells (arenaBEpilPhiCellsSelf ie acc ep) env) s) = _
  rw [arenaBEpilTail_denote (calls := calls)
    (env := cells (arenaBEpilPhiCellsSelf ie acc ep) env) (s := s)
    (ip := ip) (sc := sc) (ie := ie) (acc := acc) (ep := ep) (xt := xt) (b := b)
    (by block_lk) (by block_lk) (by block_lk) (by block_lk) (by block_lk)
    hip hpos hr]

/-- **The epilogue's step at its last revolution**, to the cleanup entry. -/
theorem arenaBEpil_step_exit {calls : Calls} {s : State}
    {ip sc : Nat} {ie acc ep xt : BitVec 64} {b : UInt8}
    (hpc : s.pc = "for.body270.epil") (hpre : s.pre = some "for.body270.epil")
    (hinc : lookupName s.env "%inc275.epil" = some (.int 64 ie))
    (hadd : lookupName s.env "%add273.epil" = some (.int 64 acc))
    (hnext : lookupName s.env "%epil.iter.next" = some (.int 64 ep))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b])
    (hexit : ep + BitVec.ofNat 64 1 = xt) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
          (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
            "%conv272.epil" "%add273.epil")
            (cells (arenaBEpilPhiCellsSelf ie acc ep) s.env))) s
        "for.cond.cleanup269") := by
  have hcode := arenaBEpil_denote_self (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hnext hsc hxt hip hpos hr
  have hbit : lookupName
      (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsSelf ie acc ep) s.env))) "%epil.iter.cmp.not" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [arenaBEpilTailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_one hexit]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBEpilBlock_find)
    (by simpa only [stateAt, arenaBEpilBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- **The epilogue's step at a non-final revolution**, to itself. -/
theorem arenaBEpil_step_loop {calls : Calls} {s : State}
    {ip sc : Nat} {ie acc ep xt : BitVec 64} {b : UInt8}
    (hpc : s.pc = "for.body270.epil") (hpre : s.pre = some "for.body270.epil")
    (hinc : lookupName s.env "%inc275.epil" = some (.int 64 ie))
    (hadd : lookupName s.env "%add273.epil" = some (.int 64 acc))
    (hnext : lookupName s.env "%epil.iter.next" = some (.int 64 ep))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip)
    (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b])
    (hexit : ep + BitVec.ofNat 64 1 ≠ xt) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
          (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
            "%conv272.epil" "%add273.epil")
            (cells (arenaBEpilPhiCellsSelf ie acc ep) s.env))) s
        "for.body270.epil") := by
  have hcode := arenaBEpil_denote_self (calls := calls) (env := s.env) (s := s)
    hpre hinc hadd hnext hsc hxt hip hpos hr
  have hbit : lookupName
      (cells (arenaBEpilTailCells ip sc ie acc ep xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsSelf ie acc ep) s.env))) "%epil.iter.cmp.not" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBEpilTailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hexit]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBEpilBlock_find)
    (by simpa only [stateAt, arenaBEpilBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep



/-! ### `for.cond.cleanup269`: the arena's length and the record's contribution -/

/-- The cleanup entry's `phi` spec. -/
def arenaBCleanup269PhiSpecs : List PhiSpec :=
  [ ⟨"%arena.5.lcssa", Ty.int 64,
      [("for.cond266.preheader", .reg "%arena.0.ph1406"),
       ("for.cond.cleanup269.loopexit.unr-lcssa", .reg "%add273.lcssa.ph"),
       ("for.body270.epil", .reg "%add273.epil")]⟩ ]

/-- The cleanup entry's tail. -/
def arenaBCleanup269TailInstrs : List Instr :=
  [ Instr.binop "%add278" BinOp.add 64 (Operand.reg "%31")
      (Operand.reg "%alen.0.ph1405"),
    Instr.binop "%add281" BinOp.add 64 (Operand.reg "%alen.0.ph1405")
      (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
    Instr.binop "%add282" BinOp.add 64 (Operand.reg "%add281") (Operand.reg "%31") ]

/-- The cleanup entry, as instructions. -/
def arenaBCleanup269Instrs : List Instr :=
  arenaBCleanup269PhiSpecs.map PhiSpec.instr ++ arenaBCleanup269TailInstrs

/-- The cleanup entry, pinned. -/
def arenaBCleanup269Block : Block :=
  { name := "for.cond.cleanup269", instrs := arenaBCleanup269Instrs,
    term := Term.br "cleanup287" }

theorem arenaBCleanup269Block_find :
    stage2NoEventBody.findBlock "for.cond.cleanup269" = some arenaBCleanup269Block := by
  decide

/-- The cleanup entry's tail cells, newest first. -/
def arenaBCleanup269TailCells (len alen acc : Nat) : List (String × Value) :=
  [("%add282", .int 64 (BitVec.ofNat 64 ((alen + 6) + len))),
   ("%add281", .int 64 (BitVec.ofNat 64 (alen + 6))),
   ("%add278", .int 64 (BitVec.ofNat 64 (len + alen)))]

/-- The cleanup entry's `phi` cell. -/
def arenaBCleanup269PhiCell (acc : Nat) : List (String × Value) :=
  [("%arena.5.lcssa", .int 64 (BitVec.ofNat 64 acc))]

/-- **The cleanup entry's tail.** -/
theorem arenaBCleanup269Tail_denote (calls : Calls) (env : Env) (s : State)
    {len alen acc : Nat}
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (hacc : lookupName env "%arena.5.lcssa" = some (.int 64 (BitVec.ofNat 64 acc))) :
    denoteCode calls arenaBCleanup269TailInstrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup269TailCells len alen acc) env) s) := by
  simp only [arenaBCleanup269TailInstrs]
  rw [denoteCode_add_reg (calls := calls) (env := env) (s := s) (d := "%add278")
    (a := "%31") (b := "%alen.0.ph1405") (x := BitVec.ofNat 64 len)
    (y := BitVec.ofNat 64 alen) h31 halen]
  rw [denoteCode_add_imm (calls := calls) (env := _) (s := s) (d := "%add281")
    (a := "%alen.0.ph1405") (x := BitVec.ofNat 64 alen) (c := BitVec.ofNat 64 6)
    (by block_lk)]
  have h81 : BitVec.ofNat 64 alen + (6#64) = BitVec.ofNat 64 (alen + 6) := by
    rw [show (6#64 : BitVec 64) = BitVec.ofNat 64 6 from rfl, arenaB_ofNat_add]
  rw [denoteCode_add_reg (calls := calls) (env := _) (s := s) (d := "%add282")
    (a := "%add281") (b := "%31") (x := BitVec.ofNat 64 (alen + 6))
    (y := BitVec.ofNat 64 len) (by rw [← h81]; block_lk) (by block_lk)]
  simp only [arenaBCleanup269TailCells, cells, arenaB_ofNat_add, denoteCode,
    denoteRun, State.bindAll]

/-- The `phi` selections at the zero-length preheader's edge. -/
theorem arenaBCleanup269_phiSelects_pre (env : Env) (s : State) {acc : Nat}
    (hpre : s.pre = some "for.cond266.preheader")
    (harenaphi : lookupName env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 acc))) :
    ArenaBPhiSelects (stateAt env s) "for.cond266.preheader"
      arenaBCleanup269PhiSpecs (arenaBCleanup269PhiCell acc).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
    ArenaBPhiSelects.nil
  exact arenaB_phiSel_reg hpre (by decide) harenaphi

/-- The `phi` selections at the exit merge's edge. -/
theorem arenaBCleanup269_phiSelects_loop (env : Env) (s : State) {acc : BitVec 64}
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hadd : lookupName env "%add273.lcssa.ph" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.cond.cleanup269.loopexit.unr-lcssa"
      arenaBCleanup269PhiSpecs [("%arena.5.lcssa", .int 64 acc)] := by
  refine ArenaBPhiSelects.cons (op := .reg "%add273.lcssa.ph") (by decide) ?_
    ArenaBPhiSelects.nil
  exact arenaB_phiSel_reg hpre (by decide) hadd

/-- The `phi` selections at the epilogue's edge. -/
theorem arenaBCleanup269_phiSelects_epil (env : Env) (s : State) {acc : BitVec 64}
    (hpre : s.pre = some "for.body270.epil")
    (hadd : lookupName env "%add273.epil" = some (.int 64 acc)) :
    ArenaBPhiSelects (stateAt env s) "for.body270.epil"
      arenaBCleanup269PhiSpecs [("%arena.5.lcssa", .int 64 acc)] := by
  refine ArenaBPhiSelects.cons (op := .reg "%add273.epil") (by decide) ?_
    ArenaBPhiSelects.nil
  exact arenaB_phiSel_reg hpre (by decide) hadd

/-- **The cleanup entry's run at the zero-length arm.** -/
theorem arenaBCleanup269_denote_pre (calls : Calls) (env : Env) (s : State)
    {len alen acc : Nat}
    (hpre : s.pre = some "for.cond266.preheader")
    (harenaphi : lookupName env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    denoteCode calls arenaBCleanup269Instrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup269TailCells len alen acc)
        (cells (arenaBCleanup269PhiCell acc) env)) s) := by
  simp only [arenaBCleanup269Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.cond266.preheader") hpre
    (arenaBCleanup269_phiSelects_pre env s hpre harenaphi) (by decide)]
  change denoteCode calls arenaBCleanup269TailInstrs
      (stateAt (cells (arenaBCleanup269PhiCell acc) env) s) = _
  rw [arenaBCleanup269Tail_denote (calls := calls)
    (env := cells (arenaBCleanup269PhiCell acc) env) (s := s)
    (len := len) (alen := alen) (acc := acc)
    (by block_lk) (by block_lk) (by block_lk)]

/-- **The cleanup entry's run at the exit merge's edge.** -/
theorem arenaBCleanup269_denote_loop (calls : Calls) (env : Env) (s : State)
    {len alen acc : Nat}
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hadd : lookupName env "%add273.lcssa.ph" = some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    denoteCode calls arenaBCleanup269Instrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup269TailCells len alen acc)
        (cells (arenaBCleanup269PhiCell acc) env)) s) := by
  simp only [arenaBCleanup269Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.cond.cleanup269.loopexit.unr-lcssa") hpre
    (arenaBCleanup269_phiSelects_loop env s hpre hadd) (by decide)]
  change denoteCode calls arenaBCleanup269TailInstrs
      (stateAt (cells (arenaBCleanup269PhiCell acc) env) s) = _
  rw [arenaBCleanup269Tail_denote (calls := calls)
    (env := cells (arenaBCleanup269PhiCell acc) env) (s := s)
    (len := len) (alen := alen) (acc := acc)
    (by block_lk) (by block_lk) (by block_lk)]

/-- **The cleanup entry's run at the epilogue's edge.** -/
theorem arenaBCleanup269_denote_epil (calls : Calls) (env : Env) (s : State)
    {len alen acc : Nat}
    (hpre : s.pre = some "for.body270.epil")
    (hadd : lookupName env "%add273.epil" = some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    denoteCode calls arenaBCleanup269Instrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup269TailCells len alen acc)
        (cells (arenaBCleanup269PhiCell acc) env)) s) := by
  simp only [arenaBCleanup269Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.body270.epil") hpre
    (arenaBCleanup269_phiSelects_epil env s hpre hadd) (by decide)]
  change denoteCode calls arenaBCleanup269TailInstrs
      (stateAt (cells (arenaBCleanup269PhiCell acc) env) s) = _
  rw [arenaBCleanup269Tail_denote (calls := calls)
    (env := cells (arenaBCleanup269PhiCell acc) env) (s := s)
    (len := len) (alen := alen) (acc := acc)
    (by block_lk) (by block_lk) (by block_lk)]

/-! ### `cleanup287`: the class's counts and the handoff to `after_value` -/

/-- The handoff's `phi` specs. -/
def arenaBCleanup287PhiSpecs : List PhiSpec :=
  [ ⟨"%alen.4", Ty.int 64,
      [("do.body254", .reg "%alen.0.ph1405"),
       ("for.cond.cleanup269", .reg "%add278")]⟩,
    ⟨"%arena.6", Ty.int 64,
      [("do.body254", .reg "%arena.0.ph1406"),
       ("for.cond.cleanup269", .reg "%arena.5.lcssa")]⟩,
    ⟨"%add260.pn", Ty.int 64,
      [("do.body254", .reg "%add260"),
       ("for.cond.cleanup269", .reg "%add282")]⟩ ]

/-- The handoff's tail. -/
def arenaBCleanup287TailInstrs : List Instr :=
  [ Instr.binop "%tokens.4" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1075")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%terms.4" BinOp.add 64 (Operand.reg "%add260.pn")
      (Operand.reg "%terms.0.lcssa1081"),
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
       (Ty.ptr, (Operand.reg "%outn205"))] ]

/-- The handoff, as instructions. -/
def arenaBCleanup287Instrs : List Instr :=
  arenaBCleanup287PhiSpecs.map PhiSpec.instr ++ arenaBCleanup287TailInstrs

/-- The handoff, pinned. -/
def arenaBCleanup287Block : Block :=
  { name := "cleanup287", instrs := arenaBCleanup287Instrs,
    term := Term.br "after_value" }

theorem arenaBCleanup287Block_find :
    stage2NoEventBody.findBlock "cleanup287" = some arenaBCleanup287Block := by
  decide

/-- The handoff's `phi` cells, newest first. -/
def arenaBCleanup287PhiCells (alen arena pn : Nat) : List (String × Value) :=
  [("%add260.pn", .int 64 (BitVec.ofNat 64 pn)),
   ("%arena.6", .int 64 (BitVec.ofNat 64 arena)),
   ("%alen.4", .int 64 (BitVec.ofNat 64 alen))]

/-- The handoff's two tail cells, newest first. -/
def arenaBCleanup287TailCells (pn tokens terms : Nat) : List (String × Value) :=
  [("%terms.4", .int 64 (BitVec.ofNat 64 (pn + terms))),
   ("%tokens.4", .int 64 (BitVec.ofNat 64 (tokens + 1)))]

/-- The `phi` selections at the cleanup entry's edge. -/
theorem arenaBCleanup287_phiSelects (env : Env) (s : State) {alen arena pn : Nat}
    (hpre : s.pre = some "for.cond.cleanup269")
    (halen : lookupName env "%add278" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.5.lcssa" =
      some (.int 64 (BitVec.ofNat 64 arena)))
    (hpn : lookupName env "%add282" = some (.int 64 (BitVec.ofNat 64 pn))) :
    ArenaBPhiSelects (stateAt env s) "for.cond.cleanup269" arenaBCleanup287PhiSpecs
      (arenaBCleanup287PhiCells alen arena pn).reverse := by
  refine ArenaBPhiSelects.cons (op := .reg "%add278") (by decide) ?_
    (ArenaBPhiSelects.cons (op := .reg "%arena.5.lcssa") (by decide) ?_
      (ArenaBPhiSelects.cons (op := .reg "%add282") (by decide) ?_
        ArenaBPhiSelects.nil))
  · exact arenaB_phiSel_reg hpre (by decide) halen
  · exact arenaB_phiSel_reg hpre (by decide) harena
  · exact arenaB_phiSel_reg hpre (by decide) hpn

/-- **The handoff's run.** -/
theorem arenaBCleanup287_denote {gap : Calls} (env : Env) (s : State)
    {alen arena pn tokens terms outn : Nat}
    (hpre : s.pre = some "for.cond.cleanup269")
    (halen : lookupName env "%add278" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.5.lcssa" =
      some (.int 64 (BitVec.ofNat 64 arena)))
    (hpn : lookupName env "%add282" = some (.int 64 (BitVec.ofNat 64 pn)))
    (htok : lookupName env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName env "%outn205" = some (.ptr outn)) :
    denoteCode (stage2NoEventCalls gap) arenaBCleanup287Instrs (stateAt env s) =
      some (stateAt (cells (arenaBCleanup287TailCells pn tokens terms)
        (cells (arenaBCleanup287PhiCells alen arena pn) env)) s) := by
  simp only [arenaBCleanup287Instrs]
  rw [arenaB_denoteCode_phiRun (s := stateAt env s)
    (p := "for.cond.cleanup269") hpre
    (arenaBCleanup287_phiSelects env s hpre halen harena hpn) (by decide)]
  change denoteCode (stage2NoEventCalls gap) arenaBCleanup287TailInstrs
      (stateAt (cells (arenaBCleanup287PhiCells alen arena pn) env) s) = _
  simp only [arenaBCleanup287TailInstrs]
  rw [denoteCode_add_imm (calls := stage2NoEventCalls gap) (env := _) (s := s)
    (d := "%tokens.4") (a := "%tokens.0.lcssa1075")
    (x := BitVec.ofNat 64 tokens) (c := BitVec.ofNat 64 1) (by block_lk)]
  rw [denoteCode_add_reg (calls := stage2NoEventCalls gap) (env := _) (s := s)
    (d := "%terms.4") (a := "%add260.pn") (b := "%terms.0.lcssa1081")
    (x := BitVec.ofNat 64 pn) (y := BitVec.ofNat 64 terms)
    (by block_lk) (by block_lk)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap) (env := _) (s := s)
    (p := "%outn205") (sz := 8) (a := outn) (by block_lk)]
  simp only [arenaBCleanup287TailCells, cells, arenaB_ofNat_add, denoteCode,
    denoteRun, State.bindAll]

/-- **The handoff's step.** -/
theorem arenaBCleanup287_step {gap : Calls} {s : State}
    {alen arena pn tokens terms outn : Nat}
    (hpc : s.pc = "cleanup287")
    (hpre : s.pre = some "for.cond.cleanup269")
    (halen : lookupName s.env "%add278" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName s.env "%arena.5.lcssa" =
      some (.int 64 (BitVec.ofNat 64 arena)))
    (hpn : lookupName s.env "%add282" = some (.int 64 (BitVec.ofNat 64 pn)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn)) :
    step (stage2NoEventCalls gap) stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBCleanup287TailCells pn tokens terms)
          (cells (arenaBCleanup287PhiCells alen arena pn) s.env)) s "after_value") := by
  have hcode := arenaBCleanup287_denote (gap := gap) (env := s.env) (s := s)
    hpre halen harena hpn htok hterms houtn
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBCleanup287Block_find)
    (by simpa only [stateAt, arenaBCleanup287Block] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep



/-! ### The accumulator and the bytes -/

/-- The accumulator after `m` bytes of the body. -/
def arenaBAcc (a0 : Nat) (body : List UInt8) (m : Nat) : Nat :=
  (a0 + byteSum (body.take m)) % 2 ^ 64

/-- The `t`-th eight-byte chunk of the body. -/
def arenaBChunk (body : List UInt8) (t : Nat) : List UInt8 :=
  (body.drop (8 * t)).take 8

/-- **A `take` splits at any offset.** -/
theorem arenaB_take_add : ∀ (m n : Nat) (l : List UInt8),
    l.take (m + n) = l.take m ++ (l.drop m).take n
  | 0, n, l => by simp
  | m + 1, n, [] => by simp
  | m + 1, n, x :: xs => by
      rw [Nat.succ_add]
      show x :: xs.take (m + n) = (x :: xs).take (m + 1) ++ ((x :: xs).drop (m + 1)).take n
      rw [arenaB_take_add m n xs]
      rfl

/-- **A revolution advances the accumulator by the chunk's sum.** -/
theorem arenaBAcc_succ {a0 : Nat} {body : List UInt8} {m : Nat}
    (hm : m + 8 ≤ body.length) :
    arenaBAcc a0 body (m + 8) =
      (arenaBAcc a0 body m + byteSum ((body.drop m).take 8)) % 2 ^ 64 := by
  unfold arenaBAcc
  rw [arenaB_take_add, byteSum_append, ← Nat.add_assoc]
  rw [Nat.mod_add_mod]

/-- The byte at `m` is the one-byte take. -/
theorem arenaB_take_one {body : List UInt8} {m : Nat} (hm : m + 1 ≤ body.length) :
    (body.drop m).take 1 = [body.getD m 0] := by
  rw [List.drop_eq_getElem_cons (by omega)]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- **An epilogue step advances the accumulator by one byte.** -/
theorem arenaBAcc_epil {a0 : Nat} {body : List UInt8} {m : Nat}
    (hm : m + 1 ≤ body.length) :
    arenaBAcc a0 body (m + 1) =
      (arenaBAcc a0 body m + (body.getD m 0).toNat) % 2 ^ 64 := by
  unfold arenaBAcc
  rw [arenaB_take_add, byteSum_append, ← Nat.add_assoc]
  rw [Nat.mod_add_mod]
  rw [arenaB_take_one hm]
  rfl

/-- The chunk's length. -/
theorem arenaBChunk_length {body : List UInt8} {t : Nat}
    (h : 8 * t + 8 ≤ body.length) : (arenaBChunk body t).length = 8 := by
  unfold arenaBChunk
  rw [List.length_take, List.length_drop]
  omega

/-- A byte of the chunk is the body's byte at the corresponding offset. -/
theorem arenaBChunk_getD {body : List UInt8} {t j : Nat}
    (h : 8 * t + 8 ≤ body.length) (hj : j < 8) :
    (arenaBChunk body t).getD j 0 = body.getD (8 * t + j) 0 := by
  unfold arenaBChunk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj, List.getElem?_eq_getElem (by omega)]

/-- The first byte of a non-empty read. -/
theorem arenaB_readBytes_head {m : Mem} {a n : Nat} {bs : List UInt8}
    (h : readBytes m a (n + 1) = some bs) :
    ∃ b rs, readByte m a = some b ∧ readBytes m (a + 1) n = some rs ∧ bs = b :: rs := by
  simp only [readBytes] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · rename_i rs hr
      exact ⟨b, rs, hb, hr, by simpa using h.symm⟩

/-- A read's length. -/
theorem arenaB_readBytes_length {m : Mem} {a : Nat} :
    ∀ (n : Nat) {bs : List UInt8}, readBytes m a n = some bs → bs.length = n
  | 0, bs, h => by cases h; rfl
  | n + 1, bs, h => by
      obtain ⟨b, rs, hb, hr, rfl⟩ := arenaB_readBytes_head h
      simp only [List.length_cons, arenaB_readBytes_length n hr]

/-- A read's prefix at a shorter length. -/
theorem arenaB_readBytes_prefix {m : Mem} {a : Nat} :
    ∀ (n : Nat) {len : Nat} {bs : List UInt8},
      readBytes m a len = some bs → n ≤ len → readBytes m a n = some (bs.take n)
  | 0, len, bs, h, hn => rfl
  | n + 1, len, bs, h, hn => by
      cases len with
      | zero => omega
      | succ len' =>
          obtain ⟨b, rs, hb, hr, rfl⟩ := arenaB_readBytes_head h
          rw [List.take_succ_cons]
          simp only [readBytes, hb]
          rw [arenaB_readBytes_prefix n hr (by omega)]

/-- A read's slice at an interior offset. -/
theorem arenaB_readBytes_slice {m : Mem} :
    ∀ (i : Nat) {a len : Nat} {bs : List UInt8},
      readBytes m a len = some bs → ∀ n, i + n ≤ len →
        readBytes m (a + i) n = some ((bs.drop i).take n)
  | 0, a, len, bs, h, n, hn => by
      simpa using arenaB_readBytes_prefix n h (by omega)
  | i + 1, a, len, bs, h, n, hn => by
      cases len with
      | zero => omega
      | succ len' =>
          obtain ⟨b, rs, hb, hr, rfl⟩ := arenaB_readBytes_head h
          rw [show a + (i + 1) = (a + 1) + i from by omega]
          rw [arenaB_readBytes_slice i hr n (by omega)]
          rfl

/-- **The main loop's chunk read.** -/
theorem arenaB_readBytes_chunk {m : Mem} {sc len : Nat} {body : List UInt8}
    (h : readBytes m sc len = some body) {t : Nat} (ht : 8 * t + 8 ≤ len) :
    readBytes m (sc + 8 * t) 8 = some (arenaBChunk body t) := by
  have := arenaB_readBytes_slice (m := m) (i := 8 * t) h 8 (by omega)
  simpa only [arenaBChunk] using this

/-- A chunk byte's one-byte read. -/
theorem arenaB_chunk_one {chunk : List UInt8} {j : Nat} (hlen : chunk.length = 8)
    (hj : j < 8) : (chunk.drop j).take 1 = [chunk.getD j 0] := by
  rw [List.drop_eq_getElem_cons (by rw [hlen]; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
  rfl

/-- **A byte of the main loop's chunk read.** -/
theorem arenaB_readBytes_chunk_byte {m : Mem} {sc len : Nat} {body : List UInt8}
    (h : readBytes m sc len = some body) {t j : Nat}
    (ht : 8 * t + 8 ≤ len) (hj : j < 8) :
    readBytes m ((sc + 8 * t) + j) 1 = some [(arenaBChunk body t).getD j 0] := by
  have hc := arenaB_readBytes_chunk h ht
  have hbl : body.length = len := arenaB_readBytes_length len h
  have hlen : (arenaBChunk body t).length = 8 := arenaBChunk_length (by omega)
  have := arenaB_readBytes_slice (m := m) (i := j) (a := sc + 8 * t)
    (len := 8) (bs := arenaBChunk body t) hc 1 (by omega)
  rw [arenaB_chunk_one hlen hj] at this
  simpa using this



/-! ### The loop's invariant and its induction -/

/-- Dropping an offset commutes with the byte read. -/
theorem arenaB_getD_drop (l : List UInt8) (m j : Nat) :
    (l.drop m).getD j 0 = l.getD (m + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The eight-byte take's sum**, at the body's own bytes. -/
theorem arenaB_take8_byteSum (l : List UInt8) (h : 8 ≤ l.length) :
    byteSum (l.take 8) =
      (l.getD 0 0).toNat + ((l.getD 1 0).toNat + ((l.getD 2 0).toNat +
        ((l.getD 3 0).toNat + ((l.getD 4 0).toNat + ((l.getD 5 0).toNat +
          ((l.getD 6 0).toNat + (l.getD 7 0).toNat)))))) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ |
    ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first | rfl | (simp at h)

/-- The eight-byte fold, from an incoming word. -/
def arenaBNestedFrom : BitVec 64 → List UInt8 → BitVec 64
  | x, [] => x
  | x, b :: bs => arenaBNestedFrom (x + BitVec.ofNat 64 b.toNat) bs

/-- **The eight-byte revolution's sum**, at the `Nat` accumulator. -/
theorem arenaB_nested : ∀ (chunk : List UInt8) (A : Nat),
    arenaBNestedFrom (BitVec.ofNat 64 A) chunk =
      BitVec.ofNat 64 (A + byteSum chunk)
  | [], A => by simp [arenaBNestedFrom, byteSum]
  | b :: bs, A => by
      show arenaBNestedFrom (BitVec.ofNat 64 A + BitVec.ofNat 64 b.toNat) bs =
        BitVec.ofNat 64 (A + byteSum (b :: bs))
      rw [arenaB_ofNat_add, arenaB_nested bs (A + b.toNat)]
      simp only [byteSum]
      congr 1
      omega

/-- A word's `Nat` is its residue, so a residue and its summand agree. -/
theorem arenaB_ofNat_mod (x : Nat) : BitVec.ofNat 64 (x % 2 ^ 64) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- The successor of a revolution's cursor. -/
theorem arenaB_ofNat_succ8 (t : Nat) :
    BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * (t + 1)) := by
  rw [arenaB_ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Distinct `Nat`s give distinct words. -/
theorem arenaB_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro hc
  apply h
  have := congrArg BitVec.toNat hc
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-! ### The base table survives the route

Every step here prepends cells whose names lie outside
`stage2NoEventWalkBaseNames`, so the entry chain's live-ins stay bound at the
carry's values.  The test is a closed `Bool`, so each step's disjointness is a
`decide`. -/

/-- A name the route does not bind reads through its conses. -/
theorem arenaB_lookupName_cells_base (cs : List (String × Value)) (n : String)
    (env : Env) (h : n ∉ cs.map (·.1)) :
    lookupName (cells cs env) n = lookupName env n := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      obtain ⟨k, v⟩ := c
      have hk : k ≠ n := by
        intro hkn
        apply h
        subst hkn
        simp
      simp only [cells, lookupName_cons_ne _ _ hk]
      exact ih fun hc => h (List.mem_cons_of_mem _ hc)

/-- The cells' names, as a `Bool` test against the base table. -/
def arenaBCellsOutsideBase (cs : List (String × Value)) : Bool :=
  cs.all fun p => decide (p.1 ∉ stage2NoEventWalkBaseNames)

theorem arenaBCellsOutsideBase_spec {cs : List (String × Value)}
    (h : arenaBCellsOutsideBase cs = true) :
    ∀ n, n ∈ stage2NoEventWalkBaseNames → n ∉ cs.map (·.1) := by
  intro n hn hmem
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hmem
  have hp' : p.1 ∉ stage2NoEventWalkBaseNames :=
    of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  exact hp' (hpn ▸ hn)

/-- The base lookups, transported along an environment equation. -/
theorem Stage2NoEventWalkBaseLookups.congr_env {K : Stage2NoEventWalkCarry}
    {s s' : State} (h : Stage2NoEventWalkBaseLookups K s) (he : s'.env = s.env) :
    Stage2NoEventWalkBaseLookups K s' := by
  intro n v hv
  rw [he]
  exact h n v hv

/-- **The base lookups survive a step that binds only other names.** -/
theorem Stage2NoEventWalkBaseLookups.consCells {K : Stage2NoEventWalkCarry}
    {s : State} {cs : List (String × Value)}
    (h : Stage2NoEventWalkBaseLookups K s)
    (hd : arenaBCellsOutsideBase cs = true) :
    Stage2NoEventWalkBaseLookups K { s with env := cells cs s.env } := by
  intro n v hv
  show lookupName (cells cs s.env) n = some v
  rw [arenaB_lookupName_cells_base cs n s.env (arenaBCellsOutsideBase_spec hd n ?_)]
  · exact h n v hv
  · have hmem : n ∈ (stage2NoEventWalkBaseValues K).map (·.1) := List.mem_map_of_mem hv
    rwa [stage2NoEventWalkBaseValues_names] at hmem


/-- The `.7` cells' values at the head of revolution `t`.  The `phi` run reads
these; the `phi`'s own results are re-bound by the block and are not carried. -/
structure ArenaBLoopHead (K : Stage2NoEventWalkCarry) (mem : Mem) (sc len : Nat)
    (body : List UInt8) (a0 : Nat)
    (u xt inc217 : BitVec 64) (spv : Nat) (fr : BitVec 8) (t : Nat) (s : State)
    {alen tokens terms outn : Nat} : Prop where
  pc : s.pc = "for.body270"
  pre : s.pre = some "for.body270"
  memeq : s.mem = mem
  hbody : readBytes s.mem sc len = some body
  hbodyLen : body.length = len
  hinc : lookupName s.env "%inc275.7" = some (.int 64 (BitVec.ofNat 64 (8 * t)))
  hadd : lookupName s.env "%add273.7" =
    some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t))))
  hnext : lookupName s.env "%niter.next.7" = some (.int 64 (BitVec.ofNat 64 (8 * t)))
  hsc : lookupName s.env "%scratch" = some (.ptr sc)
  hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1))
  hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2))
  hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3))
  hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4))
  hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5))
  hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6))
  hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7))
  hu : lookupName s.env "%unroll_iter" = some (.int 64 u)
  hxt : lookupName s.env "%xtraiter" = some (.int 64 xt)
  hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217)
  hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv))
  hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr)
  h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len))
  halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen))
  htok : lookupName s.env "%tokens.0.lcssa1075" =
    some (.int 64 (BitVec.ofNat 64 tokens))
  hterms : lookupName s.env "%terms.0.lcssa1081" =
    some (.int 64 (BitVec.ofNat 64 terms))
  houtn : lookupName s.env "%outn205" = some (.ptr outn)
  hbase : Stage2NoEventWalkBaseLookups K s

/-- The exit facts of the main loop at its exit merge: the `.7` cells the exit
merge's `phi` run reads, at the last revolution `n`. -/
structure ArenaBLoopExit (K : Stage2NoEventWalkCarry) (mem : Mem) (body : List UInt8)
    (a0 : Nat) (n : Nat)
    (xt inc217 : BitVec 64) (spv : Nat) (fr : BitVec 8) (s : State)
    {sc len alen tokens terms outn : Nat} : Prop where
  pc : s.pc = "for.cond.cleanup269.loopexit.unr-lcssa"
  pre : s.pre = some "for.body270"
  memeq : s.mem = mem
  hinc : lookupName s.env "%inc275.7" = some (.int 64 (BitVec.ofNat 64 (8 * n)))
  hadd : lookupName s.env "%add273.7" =
    some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n))))
  hxt : lookupName s.env "%xtraiter" = some (.int 64 xt)
  hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217)
  hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv))
  hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr)
  h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len))
  halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen))
  htok : lookupName s.env "%tokens.0.lcssa1075" =
    some (.int 64 (BitVec.ofNat 64 tokens))
  hterms : lookupName s.env "%terms.0.lcssa1081" =
    some (.int 64 (BitVec.ofNat 64 terms))
  houtn : lookupName s.env "%outn205" = some (.ptr outn)
  hsc : lookupName s.env "%scratch" = some (.ptr sc)
  hbase : Stage2NoEventWalkBaseLookups K s

/-- The eight byte reads a revolution consumes, from the body's read. -/
theorem ArenaBLoopHead.byteReads {K : Stage2NoEventWalkCarry} {mem : Mem} {sc len : Nat}
    {body : List UInt8}
    {a0 : Nat} {u xt inc217 : BitVec 64} {spv : Nat} {fr : BitVec 8} {t : Nat}
    {alen tokens terms outn : Nat}
    {s : State} (h : ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hm : 8 * t + 8 ≤ len) :
    ∀ j, j < 8 → readBytes s.mem (sc + j + 8 * t) 1 =
      some [body.getD (8 * t + j) 0] := by
  intro j hj
  have hm' : 8 * t + 8 ≤ body.length := by rw [h.hbodyLen]; exact hm
  have h1 := arenaB_readBytes_chunk_byte (m := s.mem) (sc := sc) (len := len)
    (body := body) h.hbody (t := t) (j := j) hm hj
  rw [arenaBChunk_getD hm' hj] at h1
  rwa [show (sc + 8 * t) + j = sc + j + 8 * t from by omega] at h1

/-- The tail cells' accumulator is the next revolution's accumulator. -/
theorem ArenaBLoopHead.nextAcc {K : Stage2NoEventWalkCarry} {mem : Mem} {sc len : Nat}
    {body : List UInt8}
    {a0 : Nat} {u xt inc217 : BitVec 64} {spv : Nat} {fr : BitVec 8} {t : Nat}
    {alen tokens terms outn : Nat}
    {s : State} (h : ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hm : 8 * t + 8 ≤ len) :
    arenaBNestedFrom (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
        [body.getD (8 * t + 0) 0, body.getD (8 * t + 1) 0,
         body.getD (8 * t + 2) 0, body.getD (8 * t + 3) 0,
         body.getD (8 * t + 4) 0, body.getD (8 * t + 5) 0,
         body.getD (8 * t + 6) 0, body.getD (8 * t + 7) 0] =
      BitVec.ofNat 64 (arenaBAcc a0 body (8 * (t + 1))) := by
  have hm' : 8 * t + 8 ≤ body.length := by rw [h.hbodyLen]; exact hm
  have hm8 : 8 * t + 8 = 8 * (t + 1) := by omega
  have haccSucc : arenaBAcc a0 body (8 * (t + 1)) =
      (arenaBAcc a0 body (8 * t) + byteSum (arenaBChunk body t)) % 2 ^ 64 := by
    rw [← hm8]; exact arenaBAcc_succ hm'
  have hchunkLen : (arenaBChunk body t).length = 8 := arenaBChunk_length hm'
  have hsum : byteSum (arenaBChunk body t) =
      (body.getD (8 * t + 0) 0).toNat + ((body.getD (8 * t + 1) 0).toNat +
        ((body.getD (8 * t + 2) 0).toNat + ((body.getD (8 * t + 3) 0).toNat +
          ((body.getD (8 * t + 4) 0).toNat + ((body.getD (8 * t + 5) 0).toNat +
            ((body.getD (8 * t + 6) 0).toNat + (body.getD (8 * t + 7) 0).toNat)))))) := by
    unfold arenaBChunk
    rw [arenaB_take8_byteSum (body.drop (8 * t)) (by rw [List.length_drop, h.hbodyLen]; omega)]
    simp only [arenaB_getD_drop]
  rw [arenaB_nested]
  rw [show byteSum [body.getD (8 * t + 0) 0, body.getD (8 * t + 1) 0,
        body.getD (8 * t + 2) 0, body.getD (8 * t + 3) 0,
        body.getD (8 * t + 4) 0, body.getD (8 * t + 5) 0,
        body.getD (8 * t + 6) 0, body.getD (8 * t + 7) 0] =
      byteSum (arenaBChunk body t) from hsum.symm]
  rw [haccSucc]
  exact (arenaB_ofNat_mod _).symm

/-- **One main-loop revolution's step.** -/
theorem ArenaBLoopHead.step {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc len : Nat}
    {body : List UInt8} {a0 : Nat} {u xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {t : Nat} {s : State} {alen tokens terms outn : Nat}
    (h : ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hbound : 8 * (t + 1) ≤ len) (h8 : 8 * (t + 1) < 2 ^ 63)
    (hne : BitVec.ofNat 64 (8 * (t + 1)) ≠ u) :
    ∃ s', LeanLLVM.step calls stage2NoEventBody s = .jump s' ∧
      ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr (t + 1) s'
        (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) := by
  have hm : 8 * t + 8 ≤ len := by omega
  have hbyte := h.byteReads hm
  let s' : State := stage2NoEventWalkNext
      (cells (arenaBBody270TailCells (8 * t) sc (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t)) u
          (body.getD (8 * t + 0) 0) (body.getD (8 * t + 1) 0)
          (body.getD (8 * t + 2) 0) (body.getD (8 * t + 3) 0)
          (body.getD (8 * t + 4) 0) (body.getD (8 * t + 5) 0)
          (body.getD (8 * t + 6) 0) (body.getD (8 * t + 7) 0))
        (cells (arenaBBody270PhiCellsLoop (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t))) s.env))
      s "for.body270"
  have hstep : LeanLLVM.step calls stage2NoEventBody s = .jump s' := by
    have hmain := arenaBBody270_step_loop (calls := calls) (s := s)
      (ip := 8 * t) (sc := sc) (i := BitVec.ofNat 64 (8 * t))
      (acc := BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
      (n := BitVec.ofNat 64 (8 * t)) (u := u)
      (b0 := body.getD (8 * t + 0) 0) (b1 := body.getD (8 * t + 1) 0)
      (b2 := body.getD (8 * t + 2) 0) (b3 := body.getD (8 * t + 3) 0)
      (b4 := body.getD (8 * t + 4) 0) (b5 := body.getD (8 * t + 5) 0)
      (b6 := body.getD (8 * t + 6) 0) (b7 := body.getD (8 * t + 7) 0)
      h.pc h.pre h.hinc h.hadd h.hnext h.hsc h.hg1 h.hg2 h.hg3 h.hg4 h.hg5 h.hg6
      h.hg7 h.hu
      (by rw [stage2NoEventSignExtend_ofNat (x := 8 * t) (by omega)])
      (by omega)
      (hbyte 0 (by omega)) (hbyte 1 (by omega)) (hbyte 2 (by omega))
      (hbyte 3 (by omega)) (hbyte 4 (by omega)) (hbyte 5 (by omega))
      (hbyte 6 (by omega)) (hbyte 7 (by omega)) ?_
    · simpa only [s'] using hmain
    · rw [show BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 8 =
        BitVec.ofNat 64 (8 * (t + 1)) from arenaB_ofNat_succ8 t]
      exact hne
  have hnested := h.nextAcc hm
  have hpc' : s'.pc = "for.body270" := by
    simp only [s', stage2NoEventWalkNext, h.pc]
  have hpre' : s'.pre = some "for.body270" := by
    simp only [s', stage2NoEventWalkNext, h.pc]
  have hmem' : s'.mem = mem := by
    simpa only [s', stage2NoEventWalkNext] using h.memeq
  have hbody' : readBytes s'.mem sc len = some body := by
    simpa only [s', stage2NoEventWalkNext] using h.hbody
  have hinc' : lookupName s'.env "%inc275.7" =
      some (.int 64 (BitVec.ofNat 64 (8 * (t + 1)))) := by
    simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self, arenaB_ofNat_succ8]
  have hnext' : lookupName s'.env "%niter.next.7" =
      some (.int 64 (BitVec.ofNat 64 (8 * (t + 1)))) := by
    simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, arenaB_ofNat_succ8]
  have hadd' : lookupName s'.env "%add273.7" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * (t + 1))))) := by
    simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    exact congrArg some (congrArg (Value.int 64) hnested)
  refine ⟨s', hstep, ?_⟩
  exact
    { pc := hpc', pre := hpre', memeq := hmem', hbody := hbody', hbodyLen := h.hbodyLen
      hinc := hinc', hadd := hadd', hnext := hnext'
      hsc := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsc
      hg1 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg1
      hg2 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg2
      hg3 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg3
      hg4 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg4
      hg5 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg5
      hg6 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg6
      hg7 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hg7
      hu := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hu
      hxt := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hxt
      hinc217 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hinc217
      hsp := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsp
      hfr := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hfr
      h31 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.h31
      halen := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.halen
      htok := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.htok
      hterms := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hterms
      houtn := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.houtn
      hbase := by
        have hphi := h.hbase.consCells (cs := arenaBBody270PhiCellsLoop (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t))) (by rfl)
        exact (hphi.consCells (cs := arenaBBody270TailCells (8 * t) sc (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t)) u
          (body.getD (8 * t + 0) 0) (body.getD (8 * t + 1) 0)
          (body.getD (8 * t + 2) 0) (body.getD (8 * t + 3) 0)
          (body.getD (8 * t + 4) 0) (body.getD (8 * t + 5) 0)
          (body.getD (8 * t + 6) 0) (body.getD (8 * t + 7) 0)) (by rfl)).congr_env
          (by simp only [s', stage2NoEventWalkNext]) }



/-- A jump's fuel prefix. -/
theorem arenaB_runFuel_jump {calls : Calls} {f : Function} {s s' : State}
    (h : LeanLLVM.step calls f s = .jump s') (k : Nat) :
    runFuel calls (1 + k) f s = runFuel calls k f s' := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-- **The main loop's exit step.** -/
theorem ArenaBLoopHead.exit {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc len : Nat}
    {body : List UInt8} {a0 n : Nat} {u xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {t : Nat} {s : State} {alen tokens terms outn : Nat}
    (h : ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hbound : 8 * (t + 1) ≤ len) (h8 : 8 * (t + 1) < 2 ^ 63)
    (hu : u = BitVec.ofNat 64 (8 * n)) (hlast : t + 1 = n) :
    ∃ s', LeanLLVM.step calls stage2NoEventBody s = .jump s' ∧
      ArenaBLoopExit K mem body a0 n xt inc217 spv fr s'
        (sc := sc) (len := len) (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) := by
  have hm : 8 * t + 8 ≤ len := by omega
  have hbyte := h.byteReads hm
  have hm8n : 8 * (t + 1) = 8 * n := by omega
  have hnested := h.nextAcc hm
  let s' : State := stage2NoEventWalkNext
      (cells (arenaBBody270TailCells (8 * t) sc (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t)) u
          (body.getD (8 * t + 0) 0) (body.getD (8 * t + 1) 0)
          (body.getD (8 * t + 2) 0) (body.getD (8 * t + 3) 0)
          (body.getD (8 * t + 4) 0) (body.getD (8 * t + 5) 0)
          (body.getD (8 * t + 6) 0) (body.getD (8 * t + 7) 0))
        (cells (arenaBBody270PhiCellsLoop (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t))) s.env))
      s "for.cond.cleanup269.loopexit.unr-lcssa"
  have hstep : LeanLLVM.step calls stage2NoEventBody s = .jump s' := by
    have hmain := arenaBBody270_step_exit (calls := calls) (s := s)
      (ip := 8 * t) (sc := sc) (i := BitVec.ofNat 64 (8 * t))
      (acc := BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
      (n := BitVec.ofNat 64 (8 * t)) (u := u)
      (b0 := body.getD (8 * t + 0) 0) (b1 := body.getD (8 * t + 1) 0)
      (b2 := body.getD (8 * t + 2) 0) (b3 := body.getD (8 * t + 3) 0)
      (b4 := body.getD (8 * t + 4) 0) (b5 := body.getD (8 * t + 5) 0)
      (b6 := body.getD (8 * t + 6) 0) (b7 := body.getD (8 * t + 7) 0)
      h.pc h.pre h.hinc h.hadd h.hnext h.hsc h.hg1 h.hg2 h.hg3 h.hg4 h.hg5 h.hg6
      h.hg7 h.hu
      (by rw [stage2NoEventSignExtend_ofNat (x := 8 * t) (by omega)])
      (by omega)
      (hbyte 0 (by omega)) (hbyte 1 (by omega)) (hbyte 2 (by omega))
      (hbyte 3 (by omega)) (hbyte 4 (by omega)) (hbyte 5 (by omega))
      (hbyte 6 (by omega)) (hbyte 7 (by omega)) ?_
    · simpa only [s'] using hmain
    · rw [arenaB_ofNat_succ8, hu, hm8n]
  refine ⟨s', hstep, ?_⟩
  have hinc' : lookupName s'.env "%inc275.7" =
      some (.int 64 (BitVec.ofNat 64 (8 * n))) := by
    simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self, arenaB_ofNat_succ8, hm8n]
  have hadd' : lookupName s'.env "%add273.7" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) := by
    simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    change some (Value.int 64 (arenaBNestedFrom (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
        [body.getD (8 * t + 0) 0, body.getD (8 * t + 1) 0,
         body.getD (8 * t + 2) 0, body.getD (8 * t + 3) 0,
         body.getD (8 * t + 4) 0, body.getD (8 * t + 5) 0,
         body.getD (8 * t + 6) 0, body.getD (8 * t + 7) 0])) =
      some (Value.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n))))
    rw [show 8 * n = 8 * (t + 1) from hm8n.symm]
    exact congrArg some (congrArg (Value.int 64) hnested)
  exact
    { pc := by simp only [s', stage2NoEventWalkNext]
      pre := by simp only [s', stage2NoEventWalkNext, h.pc]
      memeq := by simpa only [s', stage2NoEventWalkNext] using h.memeq
      hinc := hinc'
      hadd := hadd'
      hxt := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hxt
      hinc217 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hinc217
      hsp := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsp
      hfr := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hfr
      h31 := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.h31
      halen := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.halen
      htok := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.htok
      hterms := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hterms
      houtn := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.houtn
      hsc := by
        simp only [s', stage2NoEventWalkNext, arenaBBody270TailCells,
          arenaBBody270PhiCellsLoop, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsc
      hbase := by
        have hphi := h.hbase.consCells (cs := arenaBBody270PhiCellsLoop (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t))) (by rfl)
        exact (hphi.consCells (cs := arenaBBody270TailCells (8 * t) sc (BitVec.ofNat 64 (8 * t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (8 * t)))
          (BitVec.ofNat 64 (8 * t)) u
          (body.getD (8 * t + 0) 0) (body.getD (8 * t + 1) 0)
          (body.getD (8 * t + 2) 0) (body.getD (8 * t + 3) 0)
          (body.getD (8 * t + 4) 0) (body.getD (8 * t + 5) 0)
          (body.getD (8 * t + 6) 0) (body.getD (8 * t + 7) 0)) (by rfl)).congr_env
          (by simp only [s', stage2NoEventWalkNext]) }

/-- **The main loop's induction.** -/
theorem arenaBLoop_run {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem} {sc len : Nat}
    {body : List UInt8} {a0 n : Nat} {u xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {t : Nat} {s : State} {alen tokens terms outn : Nat}
    (h : ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hu : u = BitVec.ofNat 64 (8 * n))
    (hbound : 8 * n ≤ len) (h8 : 8 * n < 2 ^ 63) (ht : t < n) :
    ∃ (s' : State) (j : Nat), j ≤ n - t ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      ArenaBLoopExit K mem body a0 n xt inc217 spv fr s'
        (sc := sc) (len := len) (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) := by
  have key : ∀ k, ∀ (t : Nat) (s : State), n - t = k →
      ArenaBLoopHead K mem sc len body a0 u xt inc217 spv fr t s
      (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) → t < n →
      ∃ (s' : State) (j : Nat), j ≤ n - t ∧
        (∀ m, runFuel calls (j + m) stage2NoEventBody s =
          runFuel calls m stage2NoEventBody s') ∧
        ArenaBLoopExit K mem body a0 n xt inc217 spv fr s'
        (sc := sc) (len := len) (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro t s hk hinv hlt
        by_cases hlast : t + 1 = n
        · obtain ⟨s', hstep, hexit⟩ := hinv.exit (calls := calls) (by omega) (by omega) hu hlast
          refine ⟨s', 1, by omega, ?_, hexit⟩
          intro m
          rw [show 1 + m = m + 1 from by omega]
          simp only [runFuel, hstep]
        · have ht' : t + 1 < n := by omega
          have hne : BitVec.ofNat 64 (8 * (t + 1)) ≠ u := by
            rw [hu]
            apply arenaB_ofNat_ne (by omega) (by omega)
            omega
          obtain ⟨s1, hstep, hinv1⟩ := hinv.step (calls := calls) (by omega) (by omega) hne
          obtain ⟨s', j, hj, hrun, hexit⟩ :=
            ih (n - (t + 1)) (by omega) (t + 1) s1 rfl hinv1 ht'
          refine ⟨s', j + 1, by omega, ?_, hexit⟩
          intro m
          rw [show j + 1 + m = 1 + (j + m) from by omega]
          rw [arenaB_runFuel_jump hstep (j + m), hrun m]
  exact key (n - t) t s rfl h ht



/-! ### The epilogue's invariant and its induction -/

/-- The `.epil` cells' values at the head of epilogue revolution `t`. -/
structure ArenaBEpilHead (K : Stage2NoEventWalkCarry) (mem : Mem) (sc base len : Nat)
    (body : List UInt8) (a0 : Nat)
    (xtN alen tokens terms outn : Nat) (xt inc217 : BitVec 64) (spv : Nat) (fr : BitVec 8)
    (t : Nat) (s : State) : Prop where
  pc : s.pc = "for.body270.epil"
  pre : s.pre = some "for.body270.epil"
  memeq : s.mem = mem
  hbody : readBytes s.mem sc len = some body
  hbodyLen : body.length = len
  hinc : lookupName s.env "%inc275.epil" = some (.int 64 (BitVec.ofNat 64 (base + t)))
  hadd : lookupName s.env "%add273.epil" =
    some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + t))))
  hnext : lookupName s.env "%epil.iter.next" = some (.int 64 (BitVec.ofNat 64 t))
  hsc : lookupName s.env "%scratch" = some (.ptr sc)
  hxt : lookupName s.env "%xtraiter" = some (.int 64 xt)
  hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217)
  hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv))
  hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr)
  h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len))
  halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen))
  htok : lookupName s.env "%tokens.0.lcssa1075" = some (.int 64 (BitVec.ofNat 64 tokens))
  hterms : lookupName s.env "%terms.0.lcssa1081" = some (.int 64 (BitVec.ofNat 64 terms))
  houtn : lookupName s.env "%outn205" = some (.ptr outn)
  hbase : Stage2NoEventWalkBaseLookups K s

/-- The epilogue's exit facts at the cleanup entry. -/
structure ArenaBEpilExit (K : Stage2NoEventWalkCarry) (mem : Mem) (body : List UInt8)
    (a0 : Nat) (base xtN : Nat)
    (len alen tokens terms outn : Nat) (xt inc217 : BitVec 64) (spv : Nat)
    (fr : BitVec 8) (s : State) : Prop where
  pc : s.pc = "for.cond.cleanup269"
  pre : s.pre = some "for.body270.epil"
  memeq : s.mem = mem
  hadd : lookupName s.env "%add273.epil" =
    some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN))))
  h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len))
  halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen))
  htok : lookupName s.env "%tokens.0.lcssa1075" = some (.int 64 (BitVec.ofNat 64 tokens))
  hterms : lookupName s.env "%terms.0.lcssa1081" = some (.int 64 (BitVec.ofNat 64 terms))
  houtn : lookupName s.env "%outn205" = some (.ptr outn)
  hxt : lookupName s.env "%xtraiter" = some (.int 64 xt)
  hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217)
  hsp : lookupName s.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 spv))
  hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr)
  hbase : Stage2NoEventWalkBaseLookups K s

/-- The epilogue's byte read. -/
theorem ArenaBEpilHead.byteRead {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc base len : Nat} {body : List UInt8}
    {a0 xtN alen tokens terms outn : Nat} {xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {t : Nat} {s : State}
    (h : ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
      spv fr t s)
    (hm : base + t + 1 ≤ len) :
    readBytes s.mem (sc + (base + t)) 1 = some [body.getD (base + t) 0] := by
  have hm' : (base + t) + 1 ≤ body.length := by rw [h.hbodyLen]; exact hm
  have h1 := arenaB_readBytes_slice (m := s.mem) (i := base + t) h.hbody 1 hm
  rw [arenaB_take_one hm'] at h1
  exact h1

/-- **One epilogue revolution's step.** -/
theorem ArenaBEpilHead.step {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc base len : Nat}
    {body : List UInt8} {a0 xtN alen tokens terms outn : Nat} {xt inc217 : BitVec 64}
    {spv : Nat} {fr : BitVec 8} {t : Nat} {s : State}
    (h : ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
      spv fr t s)
    (hbound : base + (t + 1) ≤ len) (h8 : base + t < 2 ^ 63)
    (hne : BitVec.ofNat 64 t + BitVec.ofNat 64 1 ≠ xt) :
    ∃ s', LeanLLVM.step calls stage2NoEventBody s = .jump s' ∧
      ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
        spv fr (t + 1) s' := by
  have hm : base + t + 1 ≤ len := by omega
  have hr := h.byteRead hm
  let s' : State := stage2NoEventWalkNext
      (cells (arenaBEpilTailCells (base + t) sc (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t) xt (body.getD (base + t) 0))
        (cells (arenaBGroupCells sc (base + t)
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (body.getD (base + t) 0) "%arrayidx271.epil" "%34" "%conv272.epil"
          "%add273.epil")
          (cells (arenaBEpilPhiCellsSelf (BitVec.ofNat 64 (base + t))
            (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
            (BitVec.ofNat 64 t)) s.env)))
      s "for.body270.epil"
  have hstep : LeanLLVM.step calls stage2NoEventBody s = .jump s' := by
    have hmain := arenaBEpil_step_loop (calls := calls) (s := s)
      (ip := base + t) (sc := sc) (ie := BitVec.ofNat 64 (base + t))
      (acc := BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
      (ep := BitVec.ofNat 64 t) (xt := xt) (b := body.getD (base + t) 0)
      h.pc h.pre h.hinc h.hadd h.hnext h.hsc h.hxt
      (by rw [stage2NoEventSignExtend_ofNat (x := base + t) (by omega)])
      (by omega) hr ?_
    · simpa only [s'] using hmain
    · exact hne
  refine ⟨s', hstep, ?_⟩
  have hm' : base + t + 1 ≤ body.length := by rw [h.hbodyLen]; exact hm
  have haccStep : arenaBAcc a0 body (base + (t + 1)) =
      (arenaBAcc a0 body (base + t) + (body.getD (base + t) 0).toNat) % 2 ^ 64 :=
    arenaBAcc_epil hm'
  have hnested :
      BitVec.ofNat 64 (arenaBAcc a0 body (base + t)) +
        BitVec.ofNat 64 (body.getD (base + t) 0).toNat =
      BitVec.ofNat 64 (arenaBAcc a0 body (base + (t + 1))) := by
    rw [arenaB_ofNat_add, haccStep]
    exact (arenaB_ofNat_mod _).symm
  have hinc' : lookupName s'.env "%inc275.epil" =
      some (.int 64 (BitVec.ofNat 64 (base + (t + 1)))) := by
    simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
    rw [show BitVec.ofNat 64 (base + t) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (base + (t + 1)) from by
        rw [arenaB_ofNat_add]
        exact congrArg (BitVec.ofNat 64) (by omega)]
  have hnext' : lookupName s'.env "%epil.iter.next" =
      some (.int 64 (BitVec.ofNat 64 (t + 1))) := by
    simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from
      arenaB_ofNat_add t 1]
  have hadd' : lookupName s'.env "%add273.epil" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + (t + 1))))) := by
    simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    exact congrArg some (congrArg (Value.int 64) hnested)
  exact
    { pc := by simp only [s', stage2NoEventWalkNext]
      pre := by simp only [s', stage2NoEventWalkNext, h.pc]
      memeq := by simpa only [s', stage2NoEventWalkNext] using h.memeq
      hbody := by simpa only [s', stage2NoEventWalkNext] using h.hbody
      hbodyLen := h.hbodyLen
      hinc := hinc'
      hadd := hadd'
      hnext := hnext'
      hsc := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsc
      hxt := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hxt
      hinc217 := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hinc217
      hsp := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsp
      hfr := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hfr
      h31 := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.h31
      halen := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.halen
      htok := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.htok
      hterms := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hterms
      houtn := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.houtn
      hbase := by
        have h1 := h.hbase.consCells (cs := arenaBEpilPhiCellsSelf
          (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t)) (by rfl)
        have h2 := h1.consCells (cs := arenaBGroupCells sc (base + t)
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (body.getD (base + t) 0) "%arrayidx271.epil" "%34" "%conv272.epil"
          "%add273.epil") (by rfl)
        exact (h2.consCells (cs := arenaBEpilTailCells (base + t) sc
          (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t) xt (body.getD (base + t) 0)) (by rfl)).congr_env
          (by simp only [s', stage2NoEventWalkNext]) }



/-- **The epilogue's exit step.** -/
theorem ArenaBEpilHead.exit {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc base len : Nat}
    {body : List UInt8} {a0 xtN alen tokens terms outn : Nat} {xt inc217 : BitVec 64}
    {spv : Nat} {fr : BitVec 8} {t : Nat} {s : State}
    (h : ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
      spv fr t s)
    (hbound : base + (t + 1) ≤ len) (h8 : base + t < 2 ^ 63)
    (hxtN : xt = BitVec.ofNat 64 xtN) (hlast : t + 1 = xtN) :
    ∃ s', LeanLLVM.step calls stage2NoEventBody s = .jump s' ∧
      ArenaBEpilExit K mem body a0 base xtN len alen tokens terms outn xt inc217 spv fr s' := by
  have hm : base + t + 1 ≤ len := by omega
  have hr := h.byteRead hm
  have hm' : base + t + 1 ≤ body.length := by rw [h.hbodyLen]; exact hm
  have haccStep : arenaBAcc a0 body (base + (t + 1)) =
      (arenaBAcc a0 body (base + t) + (body.getD (base + t) 0).toNat) % 2 ^ 64 :=
    arenaBAcc_epil hm'
  have hnested :
      BitVec.ofNat 64 (arenaBAcc a0 body (base + t)) +
        BitVec.ofNat 64 (body.getD (base + t) 0).toNat =
      BitVec.ofNat 64 (arenaBAcc a0 body (base + (t + 1))) := by
    rw [arenaB_ofNat_add, haccStep]
    exact (arenaB_ofNat_mod _).symm
  have hmxt : base + (t + 1) = base + xtN := by omega
  let s' : State := stage2NoEventWalkNext
      (cells (arenaBEpilTailCells (base + t) sc (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t) xt (body.getD (base + t) 0))
        (cells (arenaBGroupCells sc (base + t)
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (body.getD (base + t) 0) "%arrayidx271.epil" "%34" "%conv272.epil"
          "%add273.epil")
          (cells (arenaBEpilPhiCellsSelf (BitVec.ofNat 64 (base + t))
            (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
            (BitVec.ofNat 64 t)) s.env)))
      s "for.cond.cleanup269"
  have hstep : LeanLLVM.step calls stage2NoEventBody s = .jump s' := by
    have hmain := arenaBEpil_step_exit (calls := calls) (s := s)
      (ip := base + t) (sc := sc) (ie := BitVec.ofNat 64 (base + t))
      (acc := BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
      (ep := BitVec.ofNat 64 t) (xt := xt) (b := body.getD (base + t) 0)
      h.pc h.pre h.hinc h.hadd h.hnext h.hsc h.hxt
      (by rw [stage2NoEventSignExtend_ofNat (x := base + t) (by omega)])
      (by omega) hr ?_
    · simpa only [s'] using hmain
    · rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = xt from by
        rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from
          arenaB_ofNat_add t 1, hlast, ← hxtN]]
  have hadd' : lookupName s'.env "%add273.epil" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN)))) := by
    simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    change some (Value.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)) +
        BitVec.ofNat 64 (body.getD (base + t) 0).toNat)) =
      some (Value.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN))))
    rw [hnested, hmxt]
  refine ⟨s', hstep, ?_⟩
  exact
    { pc := by simp only [s', stage2NoEventWalkNext]
      pre := by simp only [s', stage2NoEventWalkNext, h.pc]
      memeq := by simpa only [s', stage2NoEventWalkNext] using h.memeq
      hadd := hadd'
      h31 := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.h31
      halen := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.halen
      htok := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.htok
      hterms := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hterms
      houtn := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.houtn
      hxt := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hxt
      hinc217 := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hinc217
      hsp := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hsp
      hfr := by
        simp only [s', stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
          arenaBEpilPhiCellsSelf, cells]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact h.hfr
      hbase := by
        have h1 := h.hbase.consCells (cs := arenaBEpilPhiCellsSelf
          (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t)) (by rfl)
        have h2 := h1.consCells (cs := arenaBGroupCells sc (base + t)
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (body.getD (base + t) 0) "%arrayidx271.epil" "%34" "%conv272.epil"
          "%add273.epil") (by rfl)
        exact (h2.consCells (cs := arenaBEpilTailCells (base + t) sc
          (BitVec.ofNat 64 (base + t))
          (BitVec.ofNat 64 (arenaBAcc a0 body (base + t)))
          (BitVec.ofNat 64 t) xt (body.getD (base + t) 0)) (by rfl)).congr_env
          (by simp only [s', stage2NoEventWalkNext]) }

/-- **The epilogue's induction.** -/
theorem arenaBEpil_run {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc base len : Nat}
    {body : List UInt8} {a0 xtN alen tokens terms outn : Nat} {xt inc217 : BitVec 64}
    {spv : Nat} {fr : BitVec 8} {t : Nat} {s : State}
    (h : ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
      spv fr t s)
    (hxtN : xt = BitVec.ofNat 64 xtN)
    (hbound : base + xtN ≤ len) (h8 : base + xtN < 2 ^ 63) (ht : t < xtN) :
    ∃ (s' : State) (j : Nat), j ≤ xtN - t ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      ArenaBEpilExit K mem body a0 base xtN len alen tokens terms outn xt inc217 spv fr s' := by
  have key : ∀ k, ∀ (t : Nat) (s : State), xtN - t = k →
      ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt inc217
        spv fr t s → t < xtN →
      ∃ (s' : State) (j : Nat), j ≤ xtN - t ∧
        (∀ m, runFuel calls (j + m) stage2NoEventBody s =
          runFuel calls m stage2NoEventBody s') ∧
        ArenaBEpilExit K mem body a0 base xtN len alen tokens terms outn xt inc217 spv fr s' := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro t s hk hinv hlt
        by_cases hlast : t + 1 = xtN
        · obtain ⟨s', hstep, hexit⟩ :=
            hinv.exit (calls := calls) (by omega) (by omega) hxtN hlast
          refine ⟨s', 1, by omega, ?_, hexit⟩
          intro m
          rw [show 1 + m = m + 1 from by omega]
          simp only [runFuel, hstep]
        · have ht' : t + 1 < xtN := by omega
          have hne : BitVec.ofNat 64 t + BitVec.ofNat 64 1 ≠ xt := by
            rw [hxtN, show BitVec.ofNat 64 t + BitVec.ofNat 64 1 =
              BitVec.ofNat 64 (t + 1) from arenaB_ofNat_add t 1]
            apply arenaB_ofNat_ne (by omega) (by omega)
            omega
          obtain ⟨s1, hstep, hinv1⟩ := hinv.step (calls := calls) (by omega) (by omega) hne
          obtain ⟨s', j, hj, hrun, hexit⟩ :=
            ih (xtN - (t + 1)) (by omega) (t + 1) s1 rfl hinv1 ht'
          refine ⟨s', j + 1, by omega, ?_, hexit⟩
          intro m
          rw [show j + 1 + m = 1 + (j + m) from by omega]
          rw [arenaB_runFuel_jump hstep (j + m), hrun m]
  exact key (xtN - t) t s rfl h ht



/-! ### The entry, the cleanup steps, and the route -/

/-- The loop body's first revolution, at the pre-entry `phi` run. -/
theorem arenaBBody270_step_pre_loop {calls : Calls} {s : State}
    {ip sc : Nat} {acc u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpc : s.pc = "for.body270") (hpre : s.pre = some "for.body270.preheader.new")
    (harenaphi : lookupName s.env "%arena.0.ph1406" = some (.int 64 acc))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName s.env "%unroll_iter" = some (.int 64 u))
    (hip : ((0 : BitVec 64).signExtend 64).toNat = ip) (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7])
    (hne : (0 : BitVec 64) + BitVec.ofNat 64 8 ≠ u) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBBody270TailCells ip sc 0 acc 0 u
          b0 b1 b2 b3 b4 b5 b6 b7) (cells (arenaBBody270PhiCellsPre acc) s.env))
        s "for.body270") := by
  have hcode := arenaBBody270_denote_pre (calls := calls) (env := s.env) (s := s)
    hpre harenaphi hsc hg1 hg2 hg3 hg4 hg5 hg6 hg7 hu hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have hbit : lookupName
      (cells (arenaBBody270TailCells ip sc 0 acc 0 u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsPre acc) s.env)) "%niter.ncmp.7" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBBody270TailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hne]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBody270Block_find)
    (by simpa only [stateAt, arenaBBody270Block] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The loop body's first revolution at a single-revolution length. -/
theorem arenaBBody270_step_pre_exit {calls : Calls} {s : State}
    {ip sc : Nat} {acc u : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hpc : s.pc = "for.body270") (hpre : s.pre = some "for.body270.preheader.new")
    (harenaphi : lookupName s.env "%arena.0.ph1406" = some (.int 64 acc))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (hu : lookupName s.env "%unroll_iter" = some (.int 64 u))
    (hip : ((0 : BitVec 64).signExtend 64).toNat = ip) (hpos : ip < 2 ^ 63)
    (hr0 : readBytes s.mem (sc + 0 + ip) 1 = some [b0])
    (hr1 : readBytes s.mem (sc + 1 + ip) 1 = some [b1])
    (hr2 : readBytes s.mem (sc + 2 + ip) 1 = some [b2])
    (hr3 : readBytes s.mem (sc + 3 + ip) 1 = some [b3])
    (hr4 : readBytes s.mem (sc + 4 + ip) 1 = some [b4])
    (hr5 : readBytes s.mem (sc + 5 + ip) 1 = some [b5])
    (hr6 : readBytes s.mem (sc + 6 + ip) 1 = some [b6])
    (hr7 : readBytes s.mem (sc + 7 + ip) 1 = some [b7])
    (hexit : (0 : BitVec 64) + BitVec.ofNat 64 8 = u) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext (cells (arenaBBody270TailCells ip sc 0 acc 0 u
          b0 b1 b2 b3 b4 b5 b6 b7) (cells (arenaBBody270PhiCellsPre acc) s.env))
        s "for.cond.cleanup269.loopexit.unr-lcssa") := by
  have hcode := arenaBBody270_denote_pre (calls := calls) (env := s.env) (s := s)
    hpre harenaphi hsc hg1 hg2 hg3 hg4 hg5 hg6 hg7 hu hip hpos
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have hbit : lookupName
      (cells (arenaBBody270TailCells ip sc 0 acc 0 u b0 b1 b2 b3 b4 b5 b6 b7)
        (cells (arenaBBody270PhiCellsPre acc) s.env)) "%niter.ncmp.7" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [arenaBBody270TailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_one hexit]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBBody270Block_find)
    (by simpa only [stateAt, arenaBBody270Block] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The cleanup entry's step at the exit merge's edge. -/
theorem arenaBCleanup269_step_loop {calls : Calls} {s : State} {lenV alen acc : Nat}
    (hpc : s.pc = "for.cond.cleanup269")
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hadd : lookupName s.env "%add273.lcssa.ph" = some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 lenV)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBCleanup269TailCells lenV alen acc)
          (cells (arenaBCleanup269PhiCell acc) s.env)) s "cleanup287") := by
  have hcode := arenaBCleanup269_denote_loop (calls := calls) (env := s.env) (s := s)
    hpre hadd h31 halen
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBCleanup269Block_find)
    (by simpa only [stateAt, arenaBCleanup269Block] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The cleanup entry's step at the epilogue's edge. -/
theorem arenaBCleanup269_step_epil {calls : Calls} {s : State} {lenV alen acc : Nat}
    (hpc : s.pc = "for.cond.cleanup269") (hpre : s.pre = some "for.body270.epil")
    (hadd : lookupName s.env "%add273.epil" = some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 lenV)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBCleanup269TailCells lenV alen acc)
          (cells (arenaBCleanup269PhiCell acc) s.env)) s "cleanup287") := by
  have hcode := arenaBCleanup269_denote_epil (calls := calls) (env := s.env) (s := s)
    hpre hadd h31 halen
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBCleanup269Block_find)
    (by simpa only [stateAt, arenaBCleanup269Block] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The cleanup entry's step at the zero-length preheader's edge. -/
theorem arenaBCleanup269_step_pre {calls : Calls} {s : State} {lenV alen acc : Nat}
    (hpc : s.pc = "for.cond.cleanup269") (hpre : s.pre = some "for.cond266.preheader")
    (harenaphi : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 acc)))
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 lenV)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen))) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBCleanup269TailCells lenV alen acc)
          (cells (arenaBCleanup269PhiCell acc) s.env)) s "cleanup287") := by
  have hcode := arenaBCleanup269_denote_pre (calls := calls) (env := s.env) (s := s)
    hpre harenaphi h31 halen
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBCleanup269Block_find)
    (by simpa only [stateAt, arenaBCleanup269Block] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep



/-- The epilogue's first revolution, at the exit merge's edge. -/
theorem arenaBEpil_step_first_loop {calls : Calls} {s : State}
    {ip sc base : Nat} {ie acc xt : BitVec 64} {b : UInt8}
    (hpc : s.pc = "for.body270.epil")
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hiunr : lookupName s.env "%i265.01050.unr" = some (.int 64 ie))
    (haunr : lookupName s.env "%arena.51049.unr" = some (.int 64 acc))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip) (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b])
    (hne : (0 : BitVec 64) + BitVec.ofNat 64 1 ≠ xt) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBEpilTailCells ip sc ie acc 0 xt b)
          (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
            "%conv272.epil" "%add273.epil")
            (cells (arenaBEpilPhiCellsFirst ie acc) s.env))) s
        "for.body270.epil") := by
  have hcode := arenaBEpil_denote_first (calls := calls) (env := s.env) (s := s)
    hpre hiunr haunr hsc hxt hip hpos hr
  have hbit : lookupName
      (cells (arenaBEpilTailCells ip sc ie acc 0 xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsFirst ie acc) s.env))) "%epil.iter.cmp.not" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [arenaBEpilTailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_zero hne]
  have hstep := stage2NoEventWalk_step_condbr_false (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBEpilBlock_find)
    (by simpa only [stateAt, arenaBEpilBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The epilogue's first revolution at a single-revolution count. -/
theorem arenaBEpil_step_first_exit {calls : Calls} {s : State}
    {ip sc base : Nat} {ie acc xt : BitVec 64} {b : UInt8}
    (hpc : s.pc = "for.body270.epil")
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hiunr : lookupName s.env "%i265.01050.unr" = some (.int 64 ie))
    (haunr : lookupName s.env "%arena.51049.unr" = some (.int 64 acc))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hip : (ie.signExtend 64).toNat = ip) (hpos : ip < 2 ^ 63)
    (hr : readBytes s.mem (sc + ip) 1 = some [b])
    (hexit : (0 : BitVec 64) + BitVec.ofNat 64 1 = xt) :
    LeanLLVM.step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkNext
        (cells (arenaBEpilTailCells ip sc ie acc 0 xt b)
          (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
            "%conv272.epil" "%add273.epil")
            (cells (arenaBEpilPhiCellsFirst ie acc) s.env))) s
        "for.cond.cleanup269") := by
  have hcode := arenaBEpil_denote_first (calls := calls) (env := s.env) (s := s)
    hpre hiunr haunr hsc hxt hip hpos hr
  have hbit : lookupName
      (cells (arenaBEpilTailCells ip sc ie acc 0 xt b)
        (cells (arenaBGroupCells sc ip acc b "%arrayidx271.epil" "%34"
          "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsFirst ie acc) s.env))) "%epil.iter.cmp.not" =
      some (.int 1 (1 : BitVec 1)) := by
    simp only [arenaBEpilTailCells, cells, lookupName_cons_self]
    rw [arenaB_icmp_eq_one hexit]
  have hstep := stage2NoEventWalk_step_condbr_true (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact arenaBEpilBlock_find)
    (by simpa only [stateAt, arenaBEpilBlock] using hcode) rfl hbit
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- A run's two pieces compose. -/
theorem arenaB_run_trans {calls : Calls} {f : Function} {s s' s'' : State} {j k : Nat}
    (h1 : ∀ n, runFuel calls (j + n) f s = runFuel calls n f s')
    (h2 : ∀ n, runFuel calls (k + n) f s' = runFuel calls n f s'') :
    ∀ n, runFuel calls ((j + k) + n) f s = runFuel calls n f s'' := by
  intro n
  rw [show (j + k) + n = j + (k + n) from by omega, h1, h2]

/-- A step and a run compose. -/
theorem arenaB_run_step {calls : Calls} {f : Function} {s s' e : State} {j : Nat}
    (hstep : LeanLLVM.step calls f s = .jump s')
    (hr : ∀ n, runFuel calls (j + n) f s' = runFuel calls n f e) :
    ∀ n, runFuel calls ((j + 1) + n) f s = runFuel calls n f e := by
  intro n
  rw [show (j + 1) + n = 1 + (j + n) from by omega, arenaB_runFuel_jump hstep, hr]



/-- A base lookup survives a cell extension whose names avoid it. -/
theorem arenaB_lookup_mono {env : Env} {cs : List (String × Value)} {n : String}
    {v : Value} (h : lookupName env n = some v) (hn : n ∉ cs.map (·.1)) :
    lookupName (cells cs env) n = some v := by
  rw [cells_lookup_of_notin cs env hn]
  exact h

/-- The body is its own `take len`. -/
theorem arenaB_body_take {body : List UInt8} {len : Nat} (h : body.length = len) :
    body.take len = body := by
  rw [← h]
  exact List.take_length

/-- A length-one body is its own byte. -/
theorem arenaB_len1_eq {body : List UInt8} (h : body.length = 1) :
    body = [body.getD 0 0] := by
  rcases body with _ | ⟨b, rest⟩
  · simp at h
  · have hr : rest = [] := by
      cases rest with
      | nil => rfl
      | cons c cs => simp at h
    subst hr
    rfl

/-- A length-one body's sum is its byte. -/
theorem arenaB_byteSum_len1 {body : List UInt8} (h : body.length = 1) :
    byteSum body = (body.getD 0 0).toNat := by
  rw [arenaB_len1_eq h]
  rfl

/-- A one-byte epilogue step's accumulator. -/
theorem arenaBAcc_one (a0 : Nat) {body : List UInt8} (h : 1 ≤ body.length) :
    arenaBAcc a0 body 1 = (a0 + (body.getD 0 0).toNat) % 2 ^ 64 := by
  have hstep := arenaBAcc_epil (a0 := a0) (body := body) (m := 0) h
  rw [Nat.zero_add] at hstep
  rw [hstep]
  have h0 : arenaBAcc a0 body 0 = a0 % 2 ^ 64 := by simp [arenaBAcc, byteSum]
  rw [h0]
  exact Nat.mod_add_mod a0 (2 ^ 64) (body.getD 0 0).toNat

/-- The accumulator at the body's extent. -/
theorem arenaBAcc_body (a0 : Nat) {body : List UInt8} {len : Nat}
    (h : body.length = len) :
    arenaBAcc a0 body len = (a0 + byteSum body) % 2 ^ 64 := by
  unfold arenaBAcc
  rw [arenaB_body_take h]

/-- The body's eight leading bytes. -/
theorem arenaB_first_bytes {m : Mem} {sc len : Nat} {body : List UInt8}
    (h : readBytes m sc len = some body) (hm : 8 ≤ len) :
    ∀ j, j < 8 → readBytes m (sc + j + 0) 1 = some [body.getD (0 + j) 0] := by
  intro j hj
  have hbl : body.length = len := arenaB_readBytes_length len h
  have hm' : j + 1 ≤ body.length := by rw [hbl]; omega
  have h1 := arenaB_readBytes_slice (m := m) (i := j) h 1 (by omega)
  rw [arenaB_take_one hm'] at h1
  simpa only [Nat.add_zero, Nat.zero_add] using h1

/-- The epilogue's byte read at its base. -/
theorem arenaB_epil_first_byte {m : Mem} {sc base len : Nat} {body : List UInt8}
    (h : readBytes m sc len = some body) (hb : base + 1 ≤ len) :
    readBytes m (sc + base) 1 = some [body.getD base 0] := by
  have hbl : body.length = len := arenaB_readBytes_length len h
  have h1 := arenaB_readBytes_slice (m := m) (i := base) h 1 hb
  rw [arenaB_take_one (by rw [hbl]; exact hb)] at h1
  exact h1



/-- A one-byte epilogue step's accumulator, at any base. -/
theorem arenaBAcc_epil_ofNat (a0 base : Nat) {body : List UInt8}
    (hm : base + 1 ≤ body.length) :
    BitVec.ofNat 64 (arenaBAcc a0 body base) +
      BitVec.ofNat 64 (body.getD base 0).toNat =
      BitVec.ofNat 64 (arenaBAcc a0 body (base + 1)) := by
  rw [arenaB_ofNat_add, arenaBAcc_epil hm]
  exact (arenaB_ofNat_mod _).symm

/-- A successor at the `Nat` base. -/
theorem arenaB_ofNat_succ' (base : Nat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 1 = BitVec.ofNat 64 (base + 1) := by
  rw [arenaB_ofNat_add]

/-- **The epilogue from its first revolution** (either it exits at once, or the
re-entered head at `t = 1` takes over). -/
theorem arenaBEpil_first {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc base len a0 xtN alen tokens
      terms outn : Nat} {xt inc217 : BitVec 64} {spv : Nat} {fr : BitVec 8}
    {body : List UInt8} {s : State}
    (hpc : s.pc = "for.body270.epil")
    (hpre : s.pre = some "for.cond.cleanup269.loopexit.unr-lcssa")
    (hmem : s.mem = mem)
    (hbody : readBytes s.mem sc len = some body) (hbodyLen : body.length = len)
    (hiunr : lookupName s.env "%i265.01050.unr" = some (.int 64 (BitVec.ofNat 64 base)))
    (haunr : lookupName s.env "%arena.51049.unr" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body base))))
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hxt : lookupName s.env "%xtraiter" = some (.int 64 xt))
    (hxtN : xt = BitVec.ofNat 64 xtN)
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)))
    (hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hpos1 : 1 ≤ xtN) (hbase8 : base + xtN < 2 ^ 63) (hbound : base + xtN ≤ len) :
    ∃ (s' : State) (j : Nat), j ≤ xtN ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      ArenaBEpilExit K mem body a0 base xtN len alen tokens terms outn xt inc217
        spv fr s' := by
  have hb1 : base + 1 ≤ len := by omega
  have hm1 : base + 1 ≤ body.length := by rw [hbodyLen]; exact hb1
  have hr := arenaB_epil_first_byte (base := base) hbody hb1
  by_cases hcase : xtN = 1
  · -- a single revolution
    have hxt1 : xt = BitVec.ofNat 64 1 := by rw [hxtN, hcase]
    have hexit : (0 : BitVec 64) + BitVec.ofNat 64 1 = xt := by
      rw [hxt1]
      simp
    have hstep := arenaBEpil_step_first_exit (calls := calls) (s := s) (base := base)
      hpc hpre hiunr haunr hsc hxt
      (by rw [stage2NoEventSignExtend_ofNat (x := base) (by omega)]) (by omega) hr hexit
    let s4 : State := stage2NoEventWalkNext
      (cells (arenaBEpilTailCells base sc (BitVec.ofNat 64 base)
          (BitVec.ofNat 64 (arenaBAcc a0 body base)) 0 xt (body.getD base 0))
        (cells (arenaBGroupCells sc base (BitVec.ofNat 64 (arenaBAcc a0 body base))
          (body.getD base 0) "%arrayidx271.epil" "%34" "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsFirst (BitVec.ofNat 64 base)
            (BitVec.ofNat 64 (arenaBAcc a0 body base))) s.env)))
      s "for.cond.cleanup269"
    refine ⟨s4, 1, by omega, ?_, ?_⟩
    · -- the run
      intro k
      rw [show 1 + k = k + 1 from by omega]
      simp only [runFuel, hstep]
      rfl
    · -- the exit facts
      have hadd4 : lookupName s4.env "%add273.epil" =
          some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN)))) := by
        simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells, cells]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
        rw [show base + xtN = base + 1 from by rw [hcase]]
        exact congrArg some (congrArg (Value.int 64) (arenaBAcc_epil_ofNat a0 base hm1))
      exact
        { pc := by simp only [s4, stage2NoEventWalkNext]
          pre := by simp only [s4, stage2NoEventWalkNext, hpc]
          memeq := by simp only [s4, stage2NoEventWalkNext, hmem]
          hadd := hadd4
          h31 := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact h31
          halen := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact halen
          htok := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact htok
          hterms := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hterms
          houtn := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact houtn
          hxt := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hxt
          hinc217 := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hinc217
          hsp := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hsp
          hfr := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hfr
          hbase := by
            have h1 := hbase.consCells (cs := arenaBEpilPhiCellsFirst (BitVec.ofNat 64 base)
              (BitVec.ofNat 64 (arenaBAcc a0 body base))) (by rfl)
            have h2 := h1.consCells (cs := arenaBGroupCells sc base
              (BitVec.ofNat 64 (arenaBAcc a0 body base))
              (body.getD base 0) "%arrayidx271.epil" "%34" "%conv272.epil"
              "%add273.epil") (by rfl)
            exact (h2.consCells (cs := arenaBEpilTailCells base sc (BitVec.ofNat 64 base)
              (BitVec.ofNat 64 (arenaBAcc a0 body base)) 0 xt (body.getD base 0))
              (by rfl)).congr_env (by simp only [s4, stage2NoEventWalkNext]) }
  · -- at least two revolutions
    have hne : (0 : BitVec 64) + BitVec.ofNat 64 1 ≠ xt := by
      rw [hxtN]
      rw [show (0 : BitVec 64) + BitVec.ofNat 64 1 = BitVec.ofNat 64 1 from by
        rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, arenaB_ofNat_add]]
      exact arenaB_ofNat_ne (by omega) (by omega) (by omega)
    have hstep := arenaBEpil_step_first_loop (calls := calls) (s := s) (base := base)
      hpc hpre hiunr haunr hsc hxt
      (by rw [stage2NoEventSignExtend_ofNat (x := base) (by omega)]) (by omega) hr hne
    let s4 : State := stage2NoEventWalkNext
      (cells (arenaBEpilTailCells base sc (BitVec.ofNat 64 base)
          (BitVec.ofNat 64 (arenaBAcc a0 body base)) 0 xt (body.getD base 0))
        (cells (arenaBGroupCells sc base (BitVec.ofNat 64 (arenaBAcc a0 body base))
          (body.getD base 0) "%arrayidx271.epil" "%34" "%conv272.epil" "%add273.epil")
          (cells (arenaBEpilPhiCellsFirst (BitVec.ofNat 64 base)
            (BitVec.ofNat 64 (arenaBAcc a0 body base))) s.env)))
      s "for.body270.epil"
    -- the re-entered head at `t = 1`
    have hhead : ArenaBEpilHead K mem sc base len body a0 xtN alen tokens terms outn xt
        inc217 spv fr 1 s4 := by
      have hinc4 : lookupName s4.env "%inc275.epil" =
          some (.int 64 (BitVec.ofNat 64 (base + 1))) := by
        simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, cells]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_self]
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, arenaB_ofNat_add]
      have hnext4 : lookupName s4.env "%epil.iter.next" =
          some (.int 64 (BitVec.ofNat 64 1)) := by
        simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, cells]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
        decide
      have hadd4 : lookupName s4.env "%add273.epil" =
          some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + 1)))) := by
        simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells, cells]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
        exact congrArg some (congrArg (Value.int 64) (arenaBAcc_epil_ofNat a0 base hm1))
      exact
        { pc := by simp only [s4, stage2NoEventWalkNext]
          pre := by simp only [s4, stage2NoEventWalkNext, hpc]
          memeq := by simp only [s4, stage2NoEventWalkNext, hmem]
          hbody := by simpa only [s4, stage2NoEventWalkNext, hmem] using hbody
          hbodyLen := hbodyLen
          hinc := hinc4
          hadd := hadd4
          hnext := hnext4
          hsc := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hsc
          hxt := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hxt
          hinc217 := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hinc217
          hsp := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hsp
          hfr := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hfr
          h31 := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact h31
          halen := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact halen
          htok := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact htok
          hterms := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact hterms
          houtn := by
            simp only [s4, stage2NoEventWalkNext, arenaBEpilTailCells, arenaBGroupCells,
              arenaBEpilPhiCellsFirst, cells]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            exact houtn
          hbase := by
            have h1 := hbase.consCells (cs := arenaBEpilPhiCellsFirst (BitVec.ofNat 64 base)
              (BitVec.ofNat 64 (arenaBAcc a0 body base))) (by rfl)
            have h2 := h1.consCells (cs := arenaBGroupCells sc base
              (BitVec.ofNat 64 (arenaBAcc a0 body base))
              (body.getD base 0) "%arrayidx271.epil" "%34" "%conv272.epil"
              "%add273.epil") (by rfl)
            exact (h2.consCells (cs := arenaBEpilTailCells base sc (BitVec.ofNat 64 base)
              (BitVec.ofNat 64 (arenaBAcc a0 body base)) 0 xt (body.getD base 0))
              (by rfl)).congr_env (by simp only [s4, stage2NoEventWalkNext]) }
    have ht1 : 1 < xtN := by omega
    obtain ⟨s5, j5, hj5, hrun5, hexit⟩ := arenaBEpil_run (calls := calls)
      (t := 1) hhead hxtN hbound hbase8 ht1
    refine ⟨s5, j5 + 1, by omega, ?_, hexit⟩
    intro k
    exact arenaB_run_step hstep hrun5 k



/-! ### The epilogue arm's tail: `cleanup269` → `cleanup287` → `after_value` -/

/-- **From the epilogue's exit to `after_value`.**  The two cleanup steps and the
seven endpoint words: the arena's length (`%alen.4 = %31 + %alen`), the arena
word (`%arena.6 = %arena.5.lcssa`), the token count (`%tokens.4`, one more), the
record contribution (`%terms.4 = %add282 + %terms`), the three class survivors
the handoff leaves alone (`%frame.0.lcssa1099`, `%sp.0.lcssa1093.wide`,
`%inc217`), and the base table, which the two `phi` runs and the handoff do not
touch. -/
theorem ArenaBEpilExit.finish {gap : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {body : List UInt8}
    {a0 base xtN len alen tokens terms outn : Nat} {xt inc217 : BitVec 64}
    {spv : Nat} {fr : BitVec 8} {s : State}
    (h : ArenaBEpilExit K mem body a0 base xtN len alen tokens terms outn xt inc217
      spv fr s) :
    ∃ (s' : State) (j : Nat), j ≤ 2 ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN)))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName s'.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName s'.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hstepA := arenaBCleanup269_step_epil (calls := stage2NoEventCalls gap) (s := s)
    h.pc h.pre h.hadd h.h31 h.halen
  let s1 : State := stage2NoEventWalkNext
    (cells (arenaBCleanup269TailCells len alen (arenaBAcc a0 body (base + xtN)))
      (cells (arenaBCleanup269PhiCell (arenaBAcc a0 body (base + xtN))) s.env))
    s "cleanup287"
  have hA278 : lookupName s1.env "%add278" =
      some (.int 64 (BitVec.ofNat 64 (len + alen))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
  have hAlcssa : lookupName s1.env "%arena.5.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN)))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hA282 : lookupName s1.env "%add282" =
      some (.int 64 (BitVec.ofNat 64 ((alen + 6) + len))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    rw [lookupName_cons_self]
  have hAtok : lookupName s1.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.htok
  have hAterms : lookupName s1.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hterms
  have hAoutn : lookupName s1.env "%outn205" = some (.ptr outn) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.houtn
  have hAinc217 : lookupName s1.env "%inc217" = some (.int 64 inc217) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hinc217
  have hAsp : lookupName s1.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hsp
  have hAfr : lookupName s1.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s1, stage2NoEventWalkNext, arenaBCleanup269TailCells, arenaBCleanup269PhiCell,
      cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hfr
  have hpc1 : s1.pc = "cleanup287" := by simp only [s1, stage2NoEventWalkNext]
  have hpre1 : s1.pre = some "for.cond.cleanup269" := by
    simp only [s1, stage2NoEventWalkNext, h.pc]
  have hstepB := arenaBCleanup287_step (gap := gap) (s := s1)
    (alen := len + alen) (arena := arenaBAcc a0 body (base + xtN))
    (pn := (alen + 6) + len) (tokens := tokens) (terms := terms) (outn := outn)
    hpc1 hpre1 hA278 hAlcssa hA282 hAtok hAterms hAoutn
  let s2 : State := stage2NoEventWalkNext
    (cells (arenaBCleanup287TailCells ((alen + 6) + len) tokens terms)
      (cells (arenaBCleanup287PhiCells (len + alen) (arenaBAcc a0 body (base + xtN))
        ((alen + 6) + len)) s1.env))
    s1 "after_value"
  have hFalen : lookupName s2.env "%alen.4" =
      some (.int 64 (BitVec.ofNat 64 (len + alen))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
  have hFarena : lookupName s2.env "%arena.6" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (base + xtN)))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hFtok : lookupName s2.env "%tokens.4" =
      some (.int 64 (BitVec.ofNat 64 (tokens + 1))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hFterms : lookupName s2.env "%terms.4" =
      some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_self]
  have hFfr : lookupName s2.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hAfr
  have hFsp : lookupName s2.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hAsp
  have hFinc217 : lookupName s2.env "%inc217" = some (.int 64 inc217) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hAinc217
  have hFbase : Stage2NoEventWalkBaseLookups K s2 := by
    have h0 := h.hbase.consCells (cs := arenaBCleanup269PhiCell
      (arenaBAcc a0 body (base + xtN))) (by rfl)
    have h1 := h0.consCells (cs := arenaBCleanup269TailCells len alen
      (arenaBAcc a0 body (base + xtN))) (by rfl)
    have h2 := h1.consCells (cs := arenaBCleanup287PhiCells (len + alen)
      (arenaBAcc a0 body (base + xtN)) ((alen + 6) + len)) (by rfl)
    have h3 := h2.consCells (cs := arenaBCleanup287TailCells ((alen + 6) + len) tokens
      terms) (by rfl)
    exact h3.congr_env (by simp only [s2, s1, stage2NoEventWalkNext])
  refine ⟨s2, 2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      arenaB_runFuel_jump hstepA (1 + k), arenaB_runFuel_jump hstepB k]
  · simp only [s2, stage2NoEventWalkNext]
  · simp only [s2, stage2NoEventWalkNext, hpc1]
  · simp only [s2, stage2NoEventWalkNext, s1, h.memeq]
  · exact hFalen
  · exact hFarena
  · exact hFtok
  · exact hFterms
  · exact hFfr
  · exact hFsp
  · exact hFinc217
  · exact hFbase

/-- **From the loop's exit to `after_value`**, at the zero epilogue count: the
exit merge's cleanup edge, the cleanup entry and the handoff. -/
theorem ArenaBLoopExit.finishZero {gap : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc : Nat}
    {body : List UInt8}
    {a0 n len alen tokens terms outn : Nat} {xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {s : State}
    (h : ArenaBLoopExit K mem body a0 n xt inc217 spv fr s
      (sc := sc) (len := len) (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hpre : s.pre = some "for.body270")
    (hxt0 : xt = BitVec.ofNat 64 0)
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn)) :
    ∃ (s' : State) (j : Nat), j ≤ 3 ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName s'.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName s'.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hstepA := arenaBLoopexit_step_cleanup (calls := stage2NoEventCalls gap) (s := s)
    h.pc hpre h.hinc h.hadd h.hxt hxt0
  let s1 : State := stage2NoEventWalkNext
    (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
      cells (arenaBLoopexitPhiCellsLoop (BitVec.ofNat 64 (8 * n))
        (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) s.env)
    s "for.cond.cleanup269"
  have h1pc : s1.pc = "for.cond.cleanup269" := by simp only [s1, stage2NoEventWalkNext]
  have h1pre : s1.pre = some "for.cond.cleanup269.loopexit.unr-lcssa" := by
    simp only [s1, stage2NoEventWalkNext, h.pc]
  have h1had : lookupName s1.env "%add273.lcssa.ph" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h1_31 : lookupName s1.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h31
  have h1alen : lookupName s1.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have h1fr : lookupName s1.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hfr
  have h1sp : lookupName s1.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hsp
  have h1inc217 : lookupName s1.env "%inc217" = some (.int 64 inc217) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hinc217
  have h1base : Stage2NoEventWalkBaseLookups K s1 := by
    have hp := h.hbase.consCells (cs := arenaBLoopexitPhiCellsLoop (BitVec.ofNat 64 (8 * n))
      (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) (by rfl)
    have hc := hp.consCells (cs := [("%lcmp.mod.not",
      .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0)))]) (by rfl)
    exact hc.congr_env (by simp only [s1, stage2NoEventWalkNext, cells])
  have hstepB := arenaBCleanup269_step_loop (calls := stage2NoEventCalls gap) (s := s1)
    h1pc h1pre h1had h1_31 h1alen
  let s2 : State := stage2NoEventWalkNext
    (cells (arenaBCleanup269TailCells len alen (arenaBAcc a0 body (8 * n)))
      (cells (arenaBCleanup269PhiCell (arenaBAcc a0 body (8 * n))) s1.env))
    s1 "cleanup287"
  have h2_278 : lookupName s2.env "%add278" =
      some (.int 64 (BitVec.ofNat 64 (len + alen))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h2_lcssa : lookupName s2.env "%arena.5.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h2_282 : lookupName s2.env "%add282" =
      some (.int 64 (BitVec.ofNat 64 ((alen + 6) + len))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    rw [lookupName_cons_self]
  have h2_tok : lookupName s2.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have h2_terms : lookupName s2.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have h2_outn : lookupName s2.env "%outn205" = some (.ptr outn) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have h2_fr : lookupName s2.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1fr
  have h2_sp : lookupName s2.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1sp
  have h2_inc217 : lookupName s2.env "%inc217" = some (.int 64 inc217) := by
    simp only [s2, stage2NoEventWalkNext, arenaBCleanup269TailCells,
      arenaBCleanup269PhiCell, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1inc217
  have h2base : Stage2NoEventWalkBaseLookups K s2 := by
    have hp := h1base.consCells (cs := arenaBCleanup269PhiCell
      (arenaBAcc a0 body (8 * n))) (by rfl)
    have ht := hp.consCells (cs := arenaBCleanup269TailCells len alen
      (arenaBAcc a0 body (8 * n))) (by rfl)
    exact ht.congr_env (by simp only [s2, s1, stage2NoEventWalkNext, cells])
  have h2pc : s2.pc = "cleanup287" := by simp only [s2, stage2NoEventWalkNext]
  have h2pre : s2.pre = some "for.cond.cleanup269" := by
    simp only [s2, stage2NoEventWalkNext, h1pc]
  have hstepC := arenaBCleanup287_step (gap := gap) (s := s2)
    (alen := len + alen) (arena := arenaBAcc a0 body (8 * n))
    (pn := (alen + 6) + len) (tokens := tokens) (terms := terms) (outn := outn)
    h2pc h2pre h2_278 h2_lcssa h2_282 h2_tok h2_terms h2_outn
  let s3 : State := stage2NoEventWalkNext
    (cells (arenaBCleanup287TailCells ((alen + 6) + len) tokens terms)
      (cells (arenaBCleanup287PhiCells (len + alen) (arenaBAcc a0 body (8 * n))
        ((alen + 6) + len)) s2.env))
    s2 "after_value"
  have hFalen : lookupName s3.env "%alen.4" =
      some (.int 64 (BitVec.ofNat 64 (len + alen))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hFarena : lookupName s3.env "%arena.6" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hFtok : lookupName s3.env "%tokens.4" =
      some (.int 64 (BitVec.ofNat 64 (tokens + 1))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hFterms : lookupName s3.env "%terms.4" =
      some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    rw [lookupName_cons_self]
  have hFfr : lookupName s3.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2_fr
  have hFsp : lookupName s3.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2_sp
  have hFinc217 : lookupName s3.env "%inc217" = some (.int 64 inc217) := by
    simp only [s3, stage2NoEventWalkNext, arenaBCleanup287TailCells,
      arenaBCleanup287PhiCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2_inc217
  have h3base : Stage2NoEventWalkBaseLookups K s3 := by
    have hp := h2base.consCells (cs := arenaBCleanup287PhiCells (len + alen)
      (arenaBAcc a0 body (8 * n)) ((alen + 6) + len)) (by rfl)
    have ht := hp.consCells (cs := arenaBCleanup287TailCells ((alen + 6) + len) tokens
      terms) (by rfl)
    exact ht.congr_env (by simp only [s3, s2, s1, stage2NoEventWalkNext, cells])
  refine ⟨s3, 3, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
      arenaB_runFuel_jump hstepA (1 + (1 + k)),
      arenaB_runFuel_jump hstepB (1 + k), arenaB_runFuel_jump hstepC k]
  · simp only [s3, stage2NoEventWalkNext]
  · simp only [s3, stage2NoEventWalkNext, h2pc]
  · simp only [s3, stage2NoEventWalkNext, s2, s1, h.memeq]
  · exact hFalen
  · exact hFarena
  · exact hFtok
  · exact hFterms
  · exact hFfr
  · exact hFsp
  · exact hFinc217
  · exact h3base

/-- **From the loop's exit through the epilogue's first revolution**, at a
non-zero epilogue count: the loop exit's epilogue edge, the epilogue's own run and
the two cleanup steps. -/
theorem ArenaBLoopExit.finishEpil {gap : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {sc : Nat}
    {body : List UInt8}
    {a0 n len xtN alen tokens terms outn : Nat} {xt inc217 : BitVec 64} {spv : Nat}
    {fr : BitVec 8} {s : State}
    (h : ArenaBLoopExit K mem body a0 n xt inc217 spv fr s
      (sc := sc) (len := len) (alen := alen) (tokens := tokens) (terms := terms) (outn := outn))
    (hpre : s.pre = some "for.body270")
    (hn : n = len / 8) (hxtNv : xtN = len % 8) (hxtN0 : xtN ≠ 0)
    (hxtv0 : xt = BitVec.ofNat 64 xtN)
    (hlenLt : len < 2 ^ 63)
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (h31 : lookupName s.env "%31" = some (.int 64 (BitVec.ofNat 64 len)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hbody : readBytes mem sc len = some body) (hbodyLen : body.length = len) :
    ∃ (s' : State) (j : Nat), j ≤ 1 + (xtN + 1) + 2 ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n + xtN)))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName s'.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName s'.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hn8 : 8 * n = 8 * (len / 8) := by rw [hn]
  have hbase : 8 * n + xtN = len := by
    rw [hxtNv, hn]; omega
  have hx0 : xt ≠ BitVec.ofNat 64 0 := by
    intro hc
    rw [hxtv0] at hc
    apply hxtN0
    have hxtNlt : xtN < 2 ^ 64 := by rw [hxtNv]; omega
    have h2 := congrArg BitVec.toNat hc
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxtNlt, Nat.zero_mod] using h2
  let s1 : State := stage2NoEventWalkNext
    (("%lcmp.mod.not", .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0))) ::
      cells (arenaBLoopexitPhiCellsLoop (BitVec.ofNat 64 (8 * n))
        (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) s.env)
    s "for.body270.epil"
  have hstepA : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump s1 := by
    simpa only [s1] using arenaBLoopexit_step_epil (calls := stage2NoEventCalls gap) (s := s)
      h.pc hpre h.hinc h.hadd h.hxt hx0
  have h1pc : s1.pc = "for.body270.epil" := by simp only [s1, stage2NoEventWalkNext]
  have h1pre : s1.pre = some "for.cond.cleanup269.loopexit.unr-lcssa" := by
    simp only [s1, stage2NoEventWalkNext, h.pc]
  have h1unr : lookupName s1.env "%i265.01050.unr" =
      some (.int 64 (BitVec.ofNat 64 (8 * n))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h1aunr : lookupName s1.env "%arena.51049.unr" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h1sc : lookupName s1.env "%scratch" = some (.ptr sc) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsc
  have h131 : lookupName s1.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h31
  have h1alen : lookupName s1.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have h1tok : lookupName s1.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have h1terms : lookupName s1.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have h1outn : lookupName s1.env "%outn205" = some (.ptr outn) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have h1inc217 : lookupName s1.env "%inc217" = some (.int 64 inc217) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hinc217
  have h1sp : lookupName s1.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hsp
  have h1fr : lookupName s1.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s1, stage2NoEventWalkNext, arenaBLoopexitPhiCellsLoop, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.hfr
  have h1base : Stage2NoEventWalkBaseLookups K s1 := by
    have hp := h.hbase.consCells (cs := arenaBLoopexitPhiCellsLoop (BitVec.ofNat 64 (8 * n))
      (BitVec.ofNat 64 (arenaBAcc a0 body (8 * n)))) (by rfl)
    have hc := hp.consCells (cs := [("%lcmp.mod.not",
      .int 1 (evalICmp .eq xt (BitVec.ofNat 64 0)))]) (by rfl)
    exact hc.congr_env (by simp only [s1, stage2NoEventWalkNext, cells])
  have h1mem : s1.mem = mem := by simp only [s1, stage2NoEventWalkNext, h.memeq]
  have h1body : readBytes s1.mem sc len = some body := by
    simpa only [h1mem] using hbody
  have hstepB := arenaBEpil_first (calls := stage2NoEventCalls gap)
    (mem := mem) (sc := sc) (base := 8 * n) (len := len) (a0 := a0) (xtN := xtN)
    (alen := alen) (tokens := tokens) (terms := terms) (outn := outn)
    (body := body) (xt := xt) (inc217 := inc217) (spv := spv) (fr := fr) (s := s1)
    h1pc h1pre h1mem h1body hbodyLen h1unr h1aunr h1sc h.hxt hxtv0 h131 h1alen
    h1tok h1terms h1outn h1inc217 h1sp h1fr h1base (by omega) (by omega) (by omega)
  obtain ⟨s2, j2, hj2, hrun2, hexit⟩ := hstepB
  obtain ⟨s3, j3, hj3, hrun3, hpc3, hpre3, hmem3, halen3, harena3, htok3, hterms3,
    hfr3, hsp3, hinc2173, hbase3⟩ :=
    hexit.finish
  refine ⟨s3, (1 + j2 + j3), by omega, ?_, hpc3, hpre3, ?_, halen3, ?_, htok3,
    hterms3, hfr3, hsp3, hinc2173, hbase3⟩
  · intro k
    rw [show 1 + j2 + j3 + k = 1 + (j2 + (j3 + k)) from by omega,
      arenaB_runFuel_jump hstepA (j2 + (j3 + k))]
    rw [hrun2 (j3 + k)]
    exact hrun3 k
  · exact hmem3
  · exact harena3

/-- **The first revolution's eight-byte fold**, at the body's own bytes: the
nested adds the loop block leaves equal the accumulator at eight. -/
theorem arenaB_first_fold {body : List UInt8} {a0 : Nat}
    {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8}
    (hb0 : b0 = body.getD 0 0) (hb1 : b1 = body.getD 1 0)
    (hb2 : b2 = body.getD 2 0) (hb3 : b3 = body.getD 3 0)
    (hb4 : b4 = body.getD 4 0) (hb5 : b5 = body.getD 5 0)
    (hb6 : b6 = body.getD 6 0) (hb7 : b7 = body.getD 7 0)
    (h8 : 8 ≤ body.length) :
    ((((((((BitVec.ofNat 64 a0 + BitVec.ofNat 64 b0.toNat) +
      BitVec.ofNat 64 b1.toNat) + BitVec.ofNat 64 b2.toNat) +
      BitVec.ofNat 64 b3.toNat) + BitVec.ofNat 64 b4.toNat) +
      BitVec.ofNat 64 b5.toNat) + BitVec.ofNat 64 b6.toNat) +
      BitVec.ofNat 64 b7.toNat) = BitVec.ofNat 64 (arenaBAcc a0 body 8) := by
  subst hb0; subst hb1; subst hb2; subst hb3
  subst hb4; subst hb5; subst hb6; subst hb7
  have hnest : arenaBNestedFrom (BitVec.ofNat 64 a0)
      [body.getD 0 0, body.getD 1 0, body.getD 2 0, body.getD 3 0,
       body.getD 4 0, body.getD 5 0, body.getD 6 0, body.getD 7 0] =
      BitVec.ofNat 64 (a0 + byteSum [body.getD 0 0, body.getD 1 0, body.getD 2 0,
        body.getD 3 0, body.getD 4 0, body.getD 5 0, body.getD 6 0, body.getD 7 0]) :=
    arenaB_nested _ a0
  have hsum : byteSum [body.getD 0 0, body.getD 1 0, body.getD 2 0, body.getD 3 0,
      body.getD 4 0, body.getD 5 0, body.getD 6 0, body.getD 7 0] =
      byteSum (body.take 8) := by
    simp only [byteSum, Nat.add_zero]
    rw [arenaB_take8_byteSum body h8]
  have hacc : arenaBAcc a0 body 8 = (a0 + byteSum (body.take 8)) % 2 ^ 64 := by
    unfold arenaBAcc
    rfl
  show arenaBNestedFrom (BitVec.ofNat 64 a0)
      [body.getD 0 0, body.getD 1 0, body.getD 2 0, body.getD 3 0,
       body.getD 4 0, body.getD 5 0, body.getD 6 0, body.getD 7 0] = _
  rw [hnest, hsum, hacc, arenaB_ofNat_mod]

/-! ### The export: the short body (`len < 8`) -/

/-- **The string class's arena step, at a body shorter than eight bytes**: the
preheader, the length test, the exit merge's preheader edge, the epilogue's own
first revolution and the two cleanup steps.

The general arm (`8 ≤ len`, in the next section) shares this conclusion verbatim,
so the carry and trace wrapper's hypothesis is the four handoff cells both arms
carry. -/
theorem stage2NoEventWalkStringArenaB_short {gap : Calls} {K : Stage2NoEventWalkCarry}
    {s : State} {mem : Mem} {sc arenaWord alen len tokens terms outn spv : Nat}
    {body : List UInt8} {xt inc217 : BitVec 64} {fr : BitVec 8}
    (hpc : s.pc = "for.cond266.preheader")
    (hmem : s.mem = mem)
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hread : readBytes mem outn 8 = some (natToBytes len 8))
    (hlenLt64 : len < 2 ^ 64) (hlen0 : len ≠ 0) (hlen8 : len < 8)
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)))
    (hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (harenaPhi : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (hbody : readBytes mem sc len = some body) (hbodyLen : body.length = len) :
    ∃ (s' : State) (j : Nat), j ≤ 3 + (len + 1) + 2 ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName s'.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName s'.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hstep0 := arenaBPreheader_step_nonzero (calls := stage2NoEventCalls gap) (s := s)
    hpc hlen0 houtn (by rw [hmem]; exact hread) hlenLt64
  let s0 : State := stage2NoEventWalkNext (cells (arenaBPreheaderCells len) s.env) s
    "for.body270.preheader"
  have hstep0' : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump s0 := by
    simpa only [s0] using hstep0
  have h0pc : s0.pc = "for.body270.preheader" := by simp only [s0, stage2NoEventWalkNext]
  have h0mem : s0.mem = mem := by simp only [s0, stage2NoEventWalkNext, hmem]
  have h0base : Stage2NoEventWalkBaseLookups K s0 :=
    (hbase.consCells (cs := arenaBPreheaderCells len) (by rfl)).congr_env
      (by simp only [s0, stage2NoEventWalkNext])
  have h031 : lookupName s0.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hstep1 := arenaBBodyPre_step_lt (calls := stage2NoEventCalls gap) (s := s0)
    h0pc hlen8 h031 hlenLt64
  let s1 : State := stage2NoEventWalkNext (cells (arenaBBodyPreCells len) s0.env) s0
    "for.cond.cleanup269.loopexit.unr-lcssa"
  have hstep1' : step (stage2NoEventCalls gap) stage2NoEventBody s0 = .jump s1 := by
    simpa only [s1] using hstep1
  have h1pc : s1.pc = "for.cond.cleanup269.loopexit.unr-lcssa" := by
    simp only [s1, stage2NoEventWalkNext]
  have h1pre : s1.pre = some "for.body270.preheader" := by
    simp only [s1, stage2NoEventWalkNext, h0pc]
  have h1mem : s1.mem = mem := by simp only [s1, stage2NoEventWalkNext, h0mem]
  have h1base : Stage2NoEventWalkBaseLookups K s1 :=
    (h0base.consCells (cs := arenaBBodyPreCells len) (by rfl)).congr_env
      (by simp only [s1, stage2NoEventWalkNext])
  have h1xt : lookupName s1.env "%xtraiter" =
      some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, arenaB_ofNat_and_seven]
  have hlenmod : len % 8 ≠ 0 := by
    intro h
    have hd : 8 ∣ len := Nat.dvd_of_mod_eq_zero h
    omega
  have h1arena : lookupName s1.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harenaPhi
  have hstep2 := arenaBLoopexit_step_pre (calls := stage2NoEventCalls gap) (s := s1)
    h1pc h1pre h1arena h1xt (by
      intro hc
      apply hlenmod
      have h2 := congrArg BitVec.toNat hc
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len % 8 < 2 ^ 64),
        Nat.mod_eq_of_lt (by decide : (0 : Nat) < 2 ^ 64), Nat.zero_mod] using h2)
  let s2 : State := stage2NoEventWalkNext
    (("%lcmp.mod.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (len % 8)) (BitVec.ofNat 64 0))) ::
      cells (arenaBLoopexitPhiCellsPre (BitVec.ofNat 64 arenaWord)) s1.env)
    s1 "for.body270.epil"
  have hstep2' : step (stage2NoEventCalls gap) stage2NoEventBody s1 = .jump s2 := by
    simpa only [s2, h1xt] using hstep2
  have h2pc : s2.pc = "for.body270.epil" := by simp only [s2, stage2NoEventWalkNext]
  have h2pre : s2.pre = some "for.cond.cleanup269.loopexit.unr-lcssa" := by
    simp only [s2, stage2NoEventWalkNext, h1pc]
  have h2mem : s2.mem = mem := by simp only [s2, stage2NoEventWalkNext, h1mem]
  have h2unr : lookupName s2.env "%i265.01050.unr" =
      some (.int 64 (BitVec.ofNat 64 0)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    rfl
  have h2aunr : lookupName s2.env "%arena.51049.unr" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body 0))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    congr 1
    rw [show arenaBAcc arenaWord body 0 = arenaWord % 2 ^ 64 from rfl, arenaB_ofNat_mod]
  have h2xt : lookupName s2.env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1xt
  have h2_31 : lookupName s2.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h031
  have h2alen : lookupName s2.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have h2tok : lookupName s2.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have h2terms : lookupName s2.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have h2outn : lookupName s2.env "%outn205" = some (.ptr outn) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have h2sc : lookupName s2.env "%scratch" = some (.ptr sc) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsc
  have h2inc217 : lookupName s2.env "%inc217" = some (.int 64 inc217) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc217
  have h2sp : lookupName s2.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have h2fr : lookupName s2.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s2, stage2NoEventWalkNext, arenaBLoopexitPhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfr
  have h2base : Stage2NoEventWalkBaseLookups K s2 := by
    have hp := h1base.consCells (cs := arenaBLoopexitPhiCellsPre
      (BitVec.ofNat 64 arenaWord)) (by rfl)
    have hc := hp.consCells (cs := [("%lcmp.mod.not",
      .int 1 (evalICmp .eq (BitVec.ofNat 64 (len % 8)) (BitVec.ofNat 64 0)))])
      (by rfl)
    exact hc.congr_env (by simp only [s2, s1, stage2NoEventWalkNext, cells])
  have h2body : readBytes s2.mem sc len = some body := by
    rw [h2mem]; exact hbody
  have h2pos : 1 ≤ len % 8 := by
    rcases Nat.eq_zero_or_pos (len % 8) with h | h
    · exact absurd h hlenmod
    · exact h
  have h2xtN : (BitVec.ofNat 64 (len % 8)) = BitVec.ofNat 64 (len % 8) := rfl
  have hstep3 := arenaBEpil_first (calls := stage2NoEventCalls gap) (mem := mem)
    (sc := sc) (base := 0) (len := len) (a0 := arenaWord) (xtN := len % 8)
    (alen := alen) (tokens := tokens) (terms := terms) (outn := outn)
    (body := body) (xt := BitVec.ofNat 64 (len % 8)) (inc217 := inc217)
    (spv := spv) (fr := fr) (s := s2)
    h2pc h2pre h2mem h2body hbodyLen h2unr h2aunr h2sc h2xt rfl h2_31 h2alen h2tok
    h2terms h2outn h2inc217 h2sp h2fr h2base h2pos (by omega) (by omega)
  obtain ⟨s3, j3, hj3, hrun3, hexit⟩ := hstep3
  obtain ⟨s4, j4, hj4, hrun4, hpc4, hpre4, hmem4, halen4, harena4, htok4, hterms4,
    hfr4, hsp4, hinc2174, hbase4⟩ :=
    hexit.finish
  refine ⟨s4, (1 + (1 + (1 + j3) + j4)), by omega, ?_, hpc4, hpre4, ?_, halen4, ?_, htok4,
    hterms4, hfr4, hsp4, hinc2174, hbase4⟩
  · intro k
    rw [show 1 + (1 + (1 + j3) + j4) + k = 1 + (1 + (1 + (j3 + (j4 + k)))) from by omega]
    rw [arenaB_runFuel_jump hstep0' (1 + (1 + (j3 + (j4 + k))))]
    rw [arenaB_runFuel_jump hstep1' (1 + (j3 + (j4 + k)))]
    rw [arenaB_runFuel_jump hstep2' (j3 + (j4 + k))]
    rw [hrun3 (j4 + k)]
    exact hrun4 k
  · exact hmem4
  · -- the arena word: the whole body, from the empty base
    have hA : lookupName s4.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body (0 + len % 8)))) := harena4
    have hlenmod : 0 + len % 8 = len := by omega
    rw [hlenmod] at hA
    rw [arenaBAcc_body arenaWord hbodyLen] at hA
    exact hA

/-! ### The export: the general body (`8 ≤ len`)

`stage2NoEventWalkStringArenaB_short` (the body shorter than eight) and
`stage2NoEventWalkStringArenaB_long` (this one) share their conclusion verbatim,
so the carry and trace wrapper's hypothesis is the four handoff cells both arms
carry. -/

/-- **The string class's arena step, at a body of at least eight bytes.**  The
preheader, the length test, the unrolled trip count, the first (unrolled) body
step, the loop's run, and the exit's two arms (`len % 8 = 0` gone straight to
`cleanup269`, otherwise the epilogue's own run). -/
theorem stage2NoEventWalkStringArenaB_long {gap : Calls} {K : Stage2NoEventWalkCarry}
    {s : State} {mem : Mem} {sc arenaWord alen len tokens terms outn spv : Nat}
    {body : List UInt8} {xt inc217 : BitVec 64} {fr : BitVec 8}
    (hpc : s.pc = "for.cond266.preheader")
    (hmem : s.mem = mem)
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hread : readBytes mem outn 8 = some (natToBytes len 8))
    (hlenLt : len < 2 ^ 63) (hlen8 : 8 ≤ len)
    (hsc : lookupName s.env "%scratch" = some (.ptr sc))
    (hg1 : lookupName s.env "%invariant.gep1650" = some (.ptr (sc + 1)))
    (hg2 : lookupName s.env "%invariant.gep1652" = some (.ptr (sc + 2)))
    (hg3 : lookupName s.env "%invariant.gep1654" = some (.ptr (sc + 3)))
    (hg4 : lookupName s.env "%invariant.gep1656" = some (.ptr (sc + 4)))
    (hg5 : lookupName s.env "%invariant.gep1658" = some (.ptr (sc + 5)))
    (hg6 : lookupName s.env "%invariant.gep1660" = some (.ptr (sc + 6)))
    (hg7 : lookupName s.env "%invariant.gep1662" = some (.ptr (sc + 7)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)))
    (htok : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)))
    (hterms : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)))
    (hinc217 : lookupName s.env "%inc217" = some (.int 64 inc217))
    (hsp : lookupName s.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)))
    (hfr : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 fr))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (harenaPhi : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (hbody : readBytes mem sc len = some body) (hbodyLen : body.length = len) :
    ∃ (s' : State) (j : Nat), j ≤ len / 8 + len % 8 + 8 ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))) ∧
      lookupName s'.env "%frame.0.lcssa1099" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) ∧
      lookupName s'.env "%inc217" = some (.int 64 inc217) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hlen0 : len ≠ 0 := by omega
  have hlenLt64 : len < 2 ^ 64 := by omega
  have hstep0 := arenaBPreheader_step_nonzero (calls := stage2NoEventCalls gap) (s := s)
    hpc hlen0 houtn (by rw [hmem]; exact hread) hlenLt64
  let s0 : State := stage2NoEventWalkNext (cells (arenaBPreheaderCells len) s.env) s
    "for.body270.preheader"
  have hstep0' : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump s0 := by
    simpa only [s0] using hstep0
  have h0pc : s0.pc = "for.body270.preheader" := by simp only [s0, stage2NoEventWalkNext]
  have h0mem : s0.mem = mem := by simp only [s0, stage2NoEventWalkNext, hmem]
  have h0base : Stage2NoEventWalkBaseLookups K s0 :=
    (hbase.consCells (cs := arenaBPreheaderCells len) (by rfl)).congr_env
      (by simp only [s0, stage2NoEventWalkNext])
  have h031 : lookupName s0.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hstep1 := arenaBBodyPre_step_ge (calls := stage2NoEventCalls gap) (s := s0)
    h0pc hlen8 h031 hlenLt64
  let s1 : State := stage2NoEventWalkNext (cells (arenaBBodyPreCells len) s0.env) s0
    "for.body270.preheader.new"
  have hstep1' : step (stage2NoEventCalls gap) stage2NoEventBody s0 = .jump s1 :=
    hstep1
  have h1pc : s1.pc = "for.body270.preheader.new" := by simp only [s1, stage2NoEventWalkNext]
  have h1mem : s1.mem = mem := by simp only [s1, stage2NoEventWalkNext, h0mem]
  have h1base : Stage2NoEventWalkBaseLookups K s1 :=
    (h0base.consCells (cs := arenaBBodyPreCells len) (by rfl)).congr_env
      (by simp only [s1, stage2NoEventWalkNext])
  have h131 : lookupName s1.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h031
  have h1xt : lookupName s1.env "%xtraiter" =
      some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, arenaB_ofNat_and_seven]
  have hstep2 := arenaBBodyPreNew_step (calls := stage2NoEventCalls gap) (s := s1)
    h1pc h131
  let s2 : State := stage2NoEventWalkNext
    (("%unroll_iter", .int 64 (BitVec.ofNat 64 len &&&
      BitVec.ofNat 64 18446744073709551608)) :: s1.env) s1 "for.body270"
  have hstep2' : step (stage2NoEventCalls gap) stage2NoEventBody s1 = .jump s2 :=
    hstep2
  have h2pc : s2.pc = "for.body270" := by simp only [s2, stage2NoEventWalkNext]
  have h2pre : s2.pre = some "for.body270.preheader.new" := by
    simp only [s2, stage2NoEventWalkNext, h1pc]
  have h2mem : s2.mem = mem := by simp only [s2, stage2NoEventWalkNext, h1mem]
  have h2u : lookupName s2.env "%unroll_iter" =
      some (.int 64 (BitVec.ofNat 64 (8 * (len / 8)))) := by
    simp only [s2, stage2NoEventWalkNext, lookupName_cons_self]
    congr 1
    rw [arenaB_ofNat_and_unroll len hlenLt64]
  have h2_31 : lookupName s2.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s2, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h131
  have h2xt : lookupName s2.env "%xtraiter" =
      some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
    simp only [s2, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h1xt
  have h2base : lookupName s2.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harenaPhi
  have h2sc : lookupName s2.env "%scratch" = some (.ptr sc) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsc
  have h2_g1 : lookupName s2.env "%invariant.gep1650" = some (.ptr (sc + 1)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg1
  have h2_g2 : lookupName s2.env "%invariant.gep1652" = some (.ptr (sc + 2)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg2
  have h2_g3 : lookupName s2.env "%invariant.gep1654" = some (.ptr (sc + 3)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg3
  have h2_g4 : lookupName s2.env "%invariant.gep1656" = some (.ptr (sc + 4)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg4
  have h2_g5 : lookupName s2.env "%invariant.gep1658" = some (.ptr (sc + 5)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg5
  have h2_g6 : lookupName s2.env "%invariant.gep1660" = some (.ptr (sc + 6)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg6
  have h2_g7 : lookupName s2.env "%invariant.gep1662" = some (.ptr (sc + 7)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hg7
  have h2alen : lookupName s2.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have h2tok : lookupName s2.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have h2terms : lookupName s2.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have h2outn : lookupName s2.env "%outn205" = some (.ptr outn) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have h2inc217 : lookupName s2.env "%inc217" = some (.int 64 inc217) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc217
  have h2sp : lookupName s2.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have h2fr : lookupName s2.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s2, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s1, stage2NoEventWalkNext, arenaBBodyPreCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [s0, stage2NoEventWalkNext, arenaBPreheaderCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfr
  have h2lookups : Stage2NoEventWalkBaseLookups K s2 :=
    (h1base.consCells (cs := [("%unroll_iter", .int 64 (BitVec.ofNat 64 len &&&
      BitVec.ofNat 64 18446744073709551608))]) (by rfl)).congr_env
      (by simp only [s2, stage2NoEventWalkNext, cells])
  have hr0 : readBytes mem (sc + 0 + 0) 1 = some [body.getD 0 0] :=
    arenaB_first_bytes hbody hlen8 0 (by omega)
  have hr1 : readBytes mem (sc + 1 + 0) 1 = some [body.getD 1 0] :=
    arenaB_first_bytes hbody hlen8 1 (by omega)
  have hr2 : readBytes mem (sc + 2 + 0) 1 = some [body.getD 2 0] :=
    arenaB_first_bytes hbody hlen8 2 (by omega)
  have hr3 : readBytes mem (sc + 3 + 0) 1 = some [body.getD 3 0] :=
    arenaB_first_bytes hbody hlen8 3 (by omega)
  have hr4 : readBytes mem (sc + 4 + 0) 1 = some [body.getD 4 0] :=
    arenaB_first_bytes hbody hlen8 4 (by omega)
  have hr5 : readBytes mem (sc + 5 + 0) 1 = some [body.getD 5 0] :=
    arenaB_first_bytes hbody hlen8 5 (by omega)
  have hr6 : readBytes mem (sc + 6 + 0) 1 = some [body.getD 6 0] :=
    arenaB_first_bytes hbody hlen8 6 (by omega)
  have hr7 : readBytes mem (sc + 7 + 0) 1 = some [body.getD 7 0] :=
    arenaB_first_bytes hbody hlen8 7 (by omega)
  let s3 : State := stage2NoEventWalkNext
    (cells (arenaBBody270TailCells 0 sc 0 (BitVec.ofNat 64 arenaWord) 0
        (BitVec.ofNat 64 (8 * (len / 8))) (body.getD 0 0) (body.getD 1 0)
        (body.getD 2 0) (body.getD 3 0) (body.getD 4 0) (body.getD 5 0)
        (body.getD 6 0) (body.getD 7 0))
      (cells (arenaBBody270PhiCellsPre (BitVec.ofNat 64 arenaWord)) s2.env))
    s2 "for.body270"
  have h3pc : s3.pc = "for.body270" := by simp only [s3, stage2NoEventWalkNext]
  have h3pre : s3.pre = some "for.body270" := by
    simp only [s3, stage2NoEventWalkNext, h2pc]
  have h3mem : s3.mem = mem := by simp only [s3, stage2NoEventWalkNext, h2mem]
  have h3base : Stage2NoEventWalkBaseLookups K s3 := by
    have hp := h2lookups.consCells (cs := arenaBBody270PhiCellsPre
      (BitVec.ofNat 64 arenaWord)) (by rfl)
    have ht := hp.consCells (cs := arenaBBody270TailCells 0 sc 0
      (BitVec.ofNat 64 arenaWord) 0 (BitVec.ofNat 64 (8 * (len / 8)))
      (body.getD 0 0) (body.getD 1 0) (body.getD 2 0) (body.getD 3 0)
      (body.getD 4 0) (body.getD 5 0) (body.getD 6 0) (body.getD 7 0)) (by rfl)
    exact ht.congr_env (by simp only [s3, stage2NoEventWalkNext, cells])
  have h3inc : lookupName s3.env "%inc275.7" =
      some (.int 64 (BitVec.ofNat 64 8)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    congr 1
  have h3add : lookupName s3.env "%add273.7" =
      some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body 8))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    congr 1
    congr 1
    exact arenaB_first_fold (a0 := arenaWord) rfl rfl rfl rfl rfl rfl rfl rfl
      (by rw [hbodyLen]; exact hlen8)
  have h3next : lookupName s3.env "%niter.next.7" =
      some (.int 64 (BitVec.ofNat 64 8)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    congr 1
  have h3sc : lookupName s3.env "%scratch" = some (.ptr sc) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2sc
  have h3xt : lookupName s3.env "%xtraiter" =
      some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2xt
  have h3_31 : lookupName s3.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2_31
  have h3alen : lookupName s3.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2alen
  have h3tok : lookupName s3.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 tokens)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2tok
  have h3terms : lookupName s3.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 terms)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2terms
  have h3outn : lookupName s3.env "%outn205" = some (.ptr outn) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2outn
  have h3inc217 : lookupName s3.env "%inc217" = some (.int 64 inc217) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2inc217
  have h3sp : lookupName s3.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 spv)) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2sp
  have h3fr : lookupName s3.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
    simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
      arenaBBody270PhiCellsPre, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h2fr
  have h3body : readBytes s3.mem sc len = some body := by
    rw [h3mem]; exact hbody
  by_cases hn1 : 8 * (len / 8) = 8
  · -- one revolution only: the first body step is the loop's exit
    have hstep3 := arenaBBody270_step_pre_exit (calls := stage2NoEventCalls gap) (s := s2)
      (ip := 0) (sc := sc) (acc := BitVec.ofNat 64 arenaWord)
      (u := BitVec.ofNat 64 (8 * (len / 8)))
      (b0 := body.getD 0 0) (b1 := body.getD 1 0) (b2 := body.getD 2 0)
      (b3 := body.getD 3 0) (b4 := body.getD 4 0) (b5 := body.getD 5 0)
      (b6 := body.getD 6 0) (b7 := body.getD 7 0)
      h2pc h2pre h2base h2sc h2_g1 h2_g2 h2_g3 h2_g4 h2_g5 h2_g6 h2_g7 h2u
      (by decide) (by decide)
      (by rw [h2mem]; exact hr0) (by rw [h2mem]; exact hr1) (by rw [h2mem]; exact hr2)
      (by rw [h2mem]; exact hr3) (by rw [h2mem]; exact hr4) (by rw [h2mem]; exact hr5)
      (by rw [h2mem]; exact hr6) (by rw [h2mem]; exact hr7) (by rw [hn1]; rfl)
    let s3e : State := stage2NoEventWalkNext
      (cells (arenaBBody270TailCells 0 sc 0 (BitVec.ofNat 64 arenaWord) 0
          (BitVec.ofNat 64 (8 * (len / 8))) (body.getD 0 0) (body.getD 1 0)
          (body.getD 2 0) (body.getD 3 0) (body.getD 4 0) (body.getD 5 0)
          (body.getD 6 0) (body.getD 7 0))
        (cells (arenaBBody270PhiCellsPre (BitVec.ofNat 64 arenaWord)) s2.env))
      s2 "for.cond.cleanup269.loopexit.unr-lcssa"
    have hstep3' : step (stage2NoEventCalls gap) stage2NoEventBody s2 = .jump s3e := hstep3
    have h3e_pc : s3e.pc = "for.cond.cleanup269.loopexit.unr-lcssa" := by
      simp only [s3e, stage2NoEventWalkNext]
    have h3e_pre : s3e.pre = some "for.body270" := by
      simp only [s3e, stage2NoEventWalkNext, h2pc]
    have h3e_mem : s3e.mem = mem := by simp only [s3e, stage2NoEventWalkNext, h2mem]
    have h3e_inc : lookupName s3e.env "%inc275.7" = some (.int 64 (BitVec.ofNat 64 8)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3inc
    have h3e_add : lookupName s3e.env "%add273.7" =
        some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body 8))) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3add
    have h3e_next : lookupName s3e.env "%niter.next.7" =
        some (.int 64 (BitVec.ofNat 64 8)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3next
    have h3e_sc : lookupName s3e.env "%scratch" = some (.ptr sc) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3sc
    have h3e_xt : lookupName s3e.env "%xtraiter" =
        some (.int 64 (BitVec.ofNat 64 (len % 8))) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3xt
    have h3e_inc217 : lookupName s3e.env "%inc217" = some (.int 64 inc217) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3inc217
    have h3e_sp : lookupName s3e.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 spv)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3sp
    have h3e_fr : lookupName s3e.env "%frame.0.lcssa1099" = some (.int 8 fr) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3fr
    have h3e_base : Stage2NoEventWalkBaseLookups K s3e :=
      h3base.congr_env (by simp only [s3e, s3, stage2NoEventWalkNext])
    have h3e_31 : lookupName s3e.env "%31" = some (.int 64 (BitVec.ofNat 64 len)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3_31
    have h3e_alen : lookupName s3e.env "%alen.0.ph1405" =
        some (.int 64 (BitVec.ofNat 64 alen)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3alen
    have h3e_tok : lookupName s3e.env "%tokens.0.lcssa1075" =
        some (.int 64 (BitVec.ofNat 64 tokens)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3tok
    have h3e_terms : lookupName s3e.env "%terms.0.lcssa1081" =
        some (.int 64 (BitVec.ofNat 64 terms)) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3terms
    have h3e_outn : lookupName s3e.env "%outn205" = some (.ptr outn) := by
      simpa only [s3e, s3, stage2NoEventWalkNext] using h3outn
    have h3e_body : readBytes s3e.mem sc len = some body := by
      rw [h3e_mem]; exact hbody
    have hexit1 : ArenaBLoopExit K mem body arenaWord 1 (BitVec.ofNat 64 (len % 8)) inc217
        spv fr s3e (len := len) (alen := alen) (tokens := tokens) (terms := terms)
        (outn := outn) :=
      { pc := h3e_pc
        pre := h3e_pre
        memeq := h3e_mem
        hinc := by rw [h3e_inc]
        hadd := by rw [h3e_add]
        hxt := h3e_xt
        hinc217 := h3e_inc217
        hsp := h3e_sp
        hfr := h3e_fr
        h31 := h3e_31
        halen := h3e_alen
        htok := h3e_tok
        hterms := h3e_terms
        houtn := h3e_outn
        hsc := h3e_sc
        hbase := h3e_base }
    by_cases hx0 : len % 8 = 0
    · obtain ⟨s5, j5, hj5, hrun5, hpc5, hpre5, hmem5, halen5, harena5, htok5, hterms5,
        hfr5, hsp5, hinc2175, hbase5⟩ :=
        hexit1.finishZero (gap := gap) hexit1.pre (by rw [hx0]) h3e_31 h3e_alen h3e_tok
          h3e_terms h3e_outn
      have harena8 : lookupName s5.env "%arena.6" =
          some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) := by
        rw [harena5]
        congr 1
        have hdm := Nat.div_add_mod len 8
        rw [show 8 * 1 = len from by omega, arenaBAcc_body arenaWord hbodyLen]
      refine ⟨s5, (1 + (1 + (1 + (1 + j5)))), ?_, ?_, hpc5, hpre5, hmem5, halen5,
        harena8, htok5, hterms5, hfr5, hsp5, hinc2175, hbase5⟩
      · have hlen1 : 1 ≤ len / 8 := by omega
        have hz : (0 : Nat) ≤ len % 8 := Nat.zero_le _
        omega
      intro k
      rw [show 1 + (1 + (1 + (1 + j5))) + k = 1 + (1 + (1 + (1 + (j5 + k)))) from by omega]
      rw [arenaB_runFuel_jump hstep0' (1 + (1 + (1 + (j5 + k))))]
      rw [arenaB_runFuel_jump hstep1' (1 + (1 + (j5 + k)))]
      rw [arenaB_runFuel_jump hstep2' (1 + (j5 + k))]
      rw [arenaB_runFuel_jump hstep3' (j5 + k)]
      exact hrun5 k
    · obtain ⟨s5, j5, hj5, hrun5, hpc5, hpre5, hmem5, halen5, harena5, htok5, hterms5,
        hfr5, hsp5, hinc2175, hbase5⟩ :=
        hexit1.finishEpil (gap := gap) hexit1.pre (by omega) (by omega) (by omega) rfl hlenLt
        h3e_sc h3e_31 h3e_alen h3e_tok h3e_terms h3e_outn hbody hbodyLen
      have harena8 : lookupName s5.env "%arena.6" =
          some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) := by
        rw [harena5]
        congr 1
        have hdm := Nat.div_add_mod len 8
        rw [show 8 * 1 + len % 8 = len from by omega,
          arenaBAcc_body arenaWord hbodyLen]
      refine ⟨s5, (1 + (1 + (1 + (1 + j5)))), ?_, ?_, hpc5, hpre5, hmem5, halen5,
        harena8, htok5, hterms5, hfr5, hsp5, hinc2175, hbase5⟩
      · have hlen1 : 1 ≤ len / 8 := by omega
        have hz : (0 : Nat) ≤ len % 8 := Nat.zero_le _
        omega
      intro k
      rw [show 1 + (1 + (1 + (1 + j5))) + k = 1 + (1 + (1 + (1 + (j5 + k)))) from by omega]
      rw [arenaB_runFuel_jump hstep0' (1 + (1 + (1 + (j5 + k))))]
      rw [arenaB_runFuel_jump hstep1' (1 + (1 + (j5 + k)))]
      rw [arenaB_runFuel_jump hstep2' (1 + (j5 + k))]
      rw [arenaB_runFuel_jump hstep3' (j5 + k)]
      exact hrun5 k
  · -- at least two revolutions: the loop's run from the re-entered head
    have hne : (0 : BitVec 64) + BitVec.ofNat 64 8 ≠
        BitVec.ofNat 64 (8 * (len / 8)) := by
      rw [show (0 : BitVec 64) + BitVec.ofNat 64 8 = BitVec.ofNat 64 8 from by
        rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, arenaB_ofNat_add]]
      exact arenaB_ofNat_ne (by omega) (by omega) (by omega)
    have hstep3 := arenaBBody270_step_pre_loop (calls := stage2NoEventCalls gap) (s := s2)
      (ip := 0) (sc := sc) (acc := BitVec.ofNat 64 arenaWord)
      (u := BitVec.ofNat 64 (8 * (len / 8)))
      (b0 := body.getD 0 0) (b1 := body.getD 1 0) (b2 := body.getD 2 0)
      (b3 := body.getD 3 0) (b4 := body.getD 4 0) (b5 := body.getD 5 0)
      (b6 := body.getD 6 0) (b7 := body.getD 7 0)
      h2pc h2pre h2base h2sc h2_g1 h2_g2 h2_g3 h2_g4 h2_g5 h2_g6 h2_g7 h2u
      (by decide) (by decide)
      (by rw [h2mem]; exact hr0) (by rw [h2mem]; exact hr1) (by rw [h2mem]; exact hr2)
      (by rw [h2mem]; exact hr3) (by rw [h2mem]; exact hr4) (by rw [h2mem]; exact hr5)
      (by rw [h2mem]; exact hr6) (by rw [h2mem]; exact hr7) hne
    have hstep3' : step (stage2NoEventCalls gap) stage2NoEventBody s2 = .jump s3 := hstep3
    have h3_g1 : lookupName s3.env "%invariant.gep1650" = some (.ptr (sc + 1)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g1
    have h3_g2 : lookupName s3.env "%invariant.gep1652" = some (.ptr (sc + 2)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g2
    have h3_g3 : lookupName s3.env "%invariant.gep1654" = some (.ptr (sc + 3)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g3
    have h3_g4 : lookupName s3.env "%invariant.gep1656" = some (.ptr (sc + 4)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g4
    have h3_g5 : lookupName s3.env "%invariant.gep1658" = some (.ptr (sc + 5)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g5
    have h3_g6 : lookupName s3.env "%invariant.gep1660" = some (.ptr (sc + 6)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g6
    have h3_g7 : lookupName s3.env "%invariant.gep1662" = some (.ptr (sc + 7)) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2_g7
    have h3u : lookupName s3.env "%unroll_iter" =
        some (.int 64 (BitVec.ofNat 64 (8 * (len / 8)))) := by
      simp only [s3, stage2NoEventWalkNext, arenaBBody270TailCells,
        arenaBBody270PhiCellsPre, cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact h2u
    have hhead : ArenaBLoopHead K mem sc len body arenaWord (BitVec.ofNat 64 (8 * (len / 8)))
        (BitVec.ofNat 64 (len % 8)) inc217 spv fr 1 s3
        (alen := alen) (tokens := tokens) (terms := terms) (outn := outn) :=
      { pc := h3pc
        pre := h3pre
        memeq := h3mem
        hbody := h3body
        hbodyLen := hbodyLen
        hinc := h3inc
        hadd := h3add
        hnext := h3next
        hsc := h3sc
        hg1 := h3_g1
        hg2 := h3_g2
        hg3 := h3_g3
        hg4 := h3_g4
        hg5 := h3_g5
        hg6 := h3_g6
        hg7 := h3_g7
        hu := h3u
        hxt := h3xt
        hinc217 := h3inc217
        hsp := h3sp
        hfr := h3fr
        h31 := h3_31
        halen := h3alen
        htok := h3tok
        hterms := h3terms
        houtn := h3outn
        hbase := h3base }
    have hu8 : BitVec.ofNat 64 (8 * (len / 8)) = BitVec.ofNat 64 (8 * (len / 8)) := rfl
    have hbound : 8 * (len / 8) ≤ len := by omega
    have h8lt : 8 * (len / 8) < 2 ^ 63 := by omega
    have ht1 : 1 < len / 8 := by
      have hdm := Nat.div_add_mod len 8
      omega
    obtain ⟨s4, j4, hj4, hrun4, hexit⟩ :=
      arenaBLoop_run (calls := stage2NoEventCalls gap) (t := 1) hhead hu8 hbound h8lt ht1
    by_cases hx0 : len % 8 = 0
    · obtain ⟨s5, j5, hj5, hrun5, hpc5, hpre5, hmem5, halen5, harena5, htok5, hterms5,
        hfr5, hsp5, hinc2175, hbase5⟩ :=
        hexit.finishZero (gap := gap) hexit.pre (by rw [hx0]) hexit.h31 hexit.halen
          hexit.htok hexit.hterms hexit.houtn
      refine ⟨s5, (1 + (1 + (1 + (1 + (j4 + j5))))), ?_, ?_, hpc5, hpre5, hmem5,
        halen5, ?_, htok5, hterms5, hfr5, hsp5, hinc2175, hbase5⟩
      · have hj4' : j4 ≤ len / 8 := by omega
        have hlen1 : 1 ≤ len / 8 := by omega
        have hz : (0 : Nat) ≤ len % 8 := Nat.zero_le _
        omega
      · intro k
        rw [show 1 + (1 + (1 + (1 + (j4 + j5)))) + k =
          1 + (1 + (1 + (1 + (j4 + (j5 + k))))) from by omega]
        rw [arenaB_runFuel_jump hstep0' (1 + (1 + (1 + (j4 + (j5 + k)))))]
        rw [arenaB_runFuel_jump hstep1' (1 + (1 + (j4 + (j5 + k))))]
        rw [arenaB_runFuel_jump hstep2' (1 + (j4 + (j5 + k)))]
        rw [arenaB_runFuel_jump hstep3' (j4 + (j5 + k))]
        rw [hrun4 (j5 + k)]
        exact hrun5 k
      · have hA : lookupName s5.env "%arena.6" =
            some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body (8 * (len / 8))))) :=
          harena5
        have hdm := Nat.div_add_mod len 8
        rw [show 8 * (len / 8) = len from by omega,
          arenaBAcc_body arenaWord hbodyLen] at hA
        exact hA
    · obtain ⟨s5, j5, hj5, hrun5, hpc5, hpre5, hmem5, halen5, harena5, htok5, hterms5,
        hfr5, hsp5, hinc2175, hbase5⟩ :=
        hexit.finishEpil (gap := gap) hexit.pre (by omega) (by omega) (by omega) rfl hlenLt
          hexit.hsc hexit.h31 hexit.halen hexit.htok hexit.hterms hexit.houtn
          hbody hbodyLen
      refine ⟨s5, (1 + (1 + (1 + (1 + (j4 + j5))))), ?_, ?_, hpc5, hpre5, hmem5,
        halen5, ?_, htok5, hterms5, hfr5, hsp5, hinc2175, hbase5⟩
      · have hj4' : j4 ≤ len / 8 := by omega
        have hlen1 : 1 ≤ len / 8 := by omega
        have hz : (0 : Nat) ≤ len % 8 := Nat.zero_le _
        omega
      · intro k
        rw [show 1 + (1 + (1 + (1 + (j4 + j5)))) + k =
          1 + (1 + (1 + (1 + (j4 + (j5 + k))))) from by omega]
        rw [arenaB_runFuel_jump hstep0' (1 + (1 + (1 + (j4 + (j5 + k)))))]
        rw [arenaB_runFuel_jump hstep1' (1 + (1 + (j4 + (j5 + k))))]
        rw [arenaB_runFuel_jump hstep2' (1 + (j4 + (j5 + k)))]
        rw [arenaB_runFuel_jump hstep3' (j4 + (j5 + k))]
        rw [hrun4 (j5 + k)]
        exact hrun5 k
      · have hA : lookupName s5.env "%arena.6" =
            some (.int 64 (BitVec.ofNat 64 (arenaBAcc arenaWord body
              (8 * (len / 8) + len % 8)))) := harena5
        have hdm := Nat.div_add_mod len 8
        rw [show 8 * (len / 8) + len % 8 = len from by omega,
          arenaBAcc_body arenaWord hbodyLen] at hA
        exact hA


/-! ### The carry and the trace

Both arms' conclusions feed the class's carry (`stage2NoEventWalkStringCarry`)
and the target trace (`Stage2NoEventWalkTrace.stringStep`).  The terms word the
state stores is the carry's own `terms` (the record's `tag + len + payload`), so
the two agree by definition once `alen` is the logical arena's length and
`tagStr = 6`. -/

/-- **The terms word's bridge**: the stored `%terms.4` is the carry's `terms`. -/
theorem stage2NoEventWalkStringArenaB_terms_eq (K : Stage2NoEventWalkCarry)
    (len alen terms : Nat) (halen : alen = K.arena.length)
    (hterms : terms = K.terms) :
    (((alen + 6) + len) + terms) =
      K.terms + (EventRecord.tagStr + len + K.arena.length) := by
  rw [halen, hterms, show EventRecord.tagStr = 6 from rfl]
  omega

/-- **The class's trace from the four handoff cells of either arm's
conclusion.**  `stage2NoEventWalkStringArenaB_short` and `_long` conclude the
run distance, `pc`/`pre`/`mem`, the four handoff cells, the three class
survivors and the base table.  This wrapper's hypothesis is the eight-part
prefix of that conclusion — the distance, the three state facts and the four
cells — so a caller holding an arm's conclusion projects that prefix before
applying it, and the wrapper does not re-emit the three survivors or the base
table.  Its remaining hypotheses are the source trace and the class's own record
and token: the lane pair and the decoded code points, which are exactly what
`Stage2NoEventWalkTrace.stringStep` consumes.  The acceptance's words are the
caller's: `stage2NoEventWalkStringArenaB_terms_eq` is the bridge from `%terms.4`
to the target carry's `terms` field. -/
theorem stage2NoEventWalkStringArenaB_trace {gap : Calls} {K : Stage2NoEventWalkCarry}
    {s : State} {mem : Mem} {sc arenaWord alen len tokens terms outn spv p : Nat}
    {body : List UInt8} {cs : List Nat} {lane nextLane : Nat}
    (h : ∃ (s' : State) (j : Nat), j ≤ p ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms))))
    (htr : Stage2NoEventWalkTrace K)
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbodyLen : body.length = len)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) = some cs) :
    (∃ (s' : State) (j : Nat), j ≤ p ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      s'.pc = "after_value" ∧ s'.pre = some "cleanup287" ∧ s'.mem = mem ∧
      lookupName s'.env "%alen.4" = some (.int 64 (BitVec.ofNat 64 (len + alen))) ∧
      lookupName s'.env "%arena.6" =
        some (.int 64 (BitVec.ofNat 64 ((arenaWord + byteSum body) % 2 ^ 64))) ∧
      lookupName s'.env "%tokens.4" = some (.int 64 (BitVec.ofNat 64 (tokens + 1))) ∧
      lookupName s'.env "%terms.4" =
        some (.int 64 (BitVec.ofNat 64 (((alen + 6) + len) + terms)))) ∧
      Stage2NoEventWalkTrace (stage2NoEventWalkStringCarry K len body) :=
  ⟨h, Stage2NoEventWalkTrace.stringStep htr hquote hspan hcode hbelow hbodyLen hdecode⟩

/-! ## Axiom pins -/
#print axioms arenaBEpil_first
#print axioms arenaBEpil_run
#print axioms arenaB_run_trans
#print axioms ArenaBLoopHead.step
#print axioms arenaBLoopexit_step_epil
#print axioms arenaBCleanup269_step_epil
#print axioms arenaBCleanup287_step
#print axioms ArenaBEpilExit.finish
#print axioms ArenaBLoopExit.finishZero
#print axioms ArenaBLoopExit.finishEpil
#print axioms arenaB_first_fold
#print axioms arenaB_first_bytes
#print axioms stage2NoEventWalkStringArenaB_short
#print axioms stage2NoEventWalkStringArenaB_long
#print axioms stage2NoEventWalkStringArenaB_terms_eq
#print axioms stage2NoEventWalkStringArenaB_trace

end LeanLLVM.Refinement
