/-
The no-event walk's string class: the guard's two cleanup arms and the call's
set-up.

`string_value` is modelled in `JsonStage2NoEventWalkClose` (`stringValue_denote`
with `link_stringValue_true`/`_false`); this module starts from the two exits
those links reach and stops at `if.end239`'s entry, where the class calls
`s2_string_body`.

**The cleanup arms do not carry the invariant.**  `if.then209` and `if.then223`
store zero at the caller's three output slots, which lie outside the invariant's
run regions (`stage2NoEventRunRegions`), so `walkFrame` is not preserved: the
walk is over and their rows state the control step and its memory effect rather
than a `Stage2NoEventWalkLink`.  `if.end216`'s one store lands in the walk's own
staging (`%k219`), so its links carry the invariant through
`Stage2NoEventWalkInv.stack_write` under the region hypothesis for the written
word.

**The trap.**  `if.then238` calls `@llvm.trap` and ends in `unreachable`.  The
tree's selection answers that symbol with `none` (`stage2Calls_trap`), so the
block's denotation is `none` and the control step is `.ub`; the theorem states
that outcome, not a jump.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The two cleanup arms: three zero stores at the caller's slots

Both `if.then209` and `if.then223` write `i64 0` at `%tokens_out`, `%values_out`
and `%sum_out` and branch to `cleanup287.thread`.  The stores are the caller's
output slots, so these rows are control steps with a memory effect and no
invariant claim. -/

/-- The three zero stores, as the two cleanup entries write them. -/
def ifThen209Instrs : List Instr :=
  [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%tokens_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%values_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%sum_out") ]

/-- `if.then209`, pinned. -/
def ifThen209Block : Block :=
  { name := "if.then209", instrs := ifThen209Instrs, term := Term.br "cleanup287.thread" }

theorem ifThen209Block_find :
    stage2NoEventBody.findBlock "if.then209" = some ifThen209Block := by
  decide

theorem ifThen209_denote (calls : Calls) (env : Env) (s : State)
    {tOut vOut sOut : Nat}
    (hto : lookupName env "%tokens_out" = some (.ptr tOut))
    (hvo : lookupName env "%values_out" = some (.ptr vOut))
    (hso : lookupName env "%sum_out" = some (.ptr sOut)) :
    denoteCode calls ifThen209Instrs (stateAt env s) =
      some (stateAt env ({ s with mem := stage2NoEventZeroMem s.mem tOut vOut sOut })) := by
  unfold ifThen209Instrs
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := s)
    (x := BitVec.ofNat 64 0) (p := "%tokens_out") hto]
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := _)
    (x := BitVec.ofNat 64 0) (p := "%values_out") hvo]
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := _)
    (x := BitVec.ofNat 64 0) (p := "%sum_out") hso]
  simp only [denoteCode_nil, stage2NoEventZeroMem, wordBytes, BitVec.toNat_ofNat,
    Nat.zero_mod]

/-- `if.then209`'s control step: the three zero stores and the branch to
`cleanup287.thread`. -/
theorem ifThen209_step {calls : Calls} {s : State} {tOut vOut sOut : Nat}
    (hpc : s.pc = "if.then209")
    (hto : lookupName s.env "%tokens_out" = some (.ptr tOut))
    (hvo : lookupName s.env "%values_out" = some (.ptr vOut))
    (hso : lookupName s.env "%sum_out" = some (.ptr sOut)) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkStored s.env s
        (stage2NoEventZeroMem s.mem tOut vOut sOut) "cleanup287.thread") := by
  have hcode := ifThen209_denote (calls := calls) (env := s.env) (s := s) hto hvo hso
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifThen209Block_find) (by simpa only [ifThen209Block, stateAt] using hcode) rfl
  simpa only [stage2NoEventWalkStored, stateAt] using hstep

/-- `if.then223`: the same three stores, branching to the same cleanup entry. -/
def ifThen223Instrs : List Instr := ifThen209Instrs

/-- `if.then223`, pinned. -/
def ifThen223Block : Block :=
  { name := "if.then223", instrs := ifThen223Instrs, term := Term.br "cleanup287.thread" }

theorem ifThen223Block_find :
    stage2NoEventBody.findBlock "if.then223" = some ifThen223Block := by
  decide

theorem ifThen223_denote (calls : Calls) (env : Env) (s : State)
    {tOut vOut sOut : Nat}
    (hto : lookupName env "%tokens_out" = some (.ptr tOut))
    (hvo : lookupName env "%values_out" = some (.ptr vOut))
    (hso : lookupName env "%sum_out" = some (.ptr sOut)) :
    denoteCode calls ifThen223Instrs (stateAt env s) =
      some (stateAt env ({ s with mem := stage2NoEventZeroMem s.mem tOut vOut sOut })) :=
  ifThen209_denote (calls := calls) env s hto hvo hso

/-- `if.then223`'s control step: the three zero stores and the branch to
`cleanup287.thread`. -/
theorem ifThen223_step {calls : Calls} {s : State} {tOut vOut sOut : Nat}
    (hpc : s.pc = "if.then223")
    (hto : lookupName s.env "%tokens_out" = some (.ptr tOut))
    (hvo : lookupName s.env "%values_out" = some (.ptr vOut))
    (hso : lookupName s.env "%sum_out" = some (.ptr sOut)) :
    step calls stage2NoEventBody s = .jump
      (stage2NoEventWalkStored s.env s
        (stage2NoEventZeroMem s.mem tOut vOut sOut) "cleanup287.thread") := by
  have hcode := ifThen223_denote (calls := calls) (env := s.env) (s := s) hto hvo hso
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifThen223Block_find) (by simpa only [ifThen223Block, stateAt] using hcode) rfl
  simpa only [stage2NoEventWalkStored, stateAt] using hstep

/-! ### `if.end216`: the entry's extent and the call's staging store

The block adds the entry's index to the cursor, reads the entry's lane word,
stores the advanced cursor at `%k219` (the walk's own staging), and compares the
entry's offset against the document's length. -/

/-- `if.end216`: the entry's extent and the guard. -/
def ifEnd216Instrs : List Instr :=
  [ Instr.binop "%inc217" BinOp.add 64 (Operand.reg "%k.0.lcssa1087")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.gep "%arrayidx218" (Ty.int 32) (Operand.reg "%ep")
      (Operand.reg "%inc.lcssa1130"),
    Instr.load "%29" (Ty.int 32) (Operand.reg "%arrayidx218"),
    Instr.store (Ty.int 64) (Operand.reg "%inc217") (Operand.reg "%k219"),
    Instr.zext "%conv220" 32 64 (Operand.reg "%29"),
    Instr.icmp "%cmp221.not" IPred.ugt 64 (Operand.reg "%n") (Operand.reg "%conv220") ]

/-- `if.end216`, pinned. -/
def ifEnd216Block : Block :=
  { name := "if.end216", instrs := ifEnd216Instrs,
    term := Term.condbr (Operand.reg "%cmp221.not") "if.end230" "if.then223" }

theorem ifEnd216Block_find :
    stage2NoEventBody.findBlock "if.end216" = some ifEnd216Block := by
  decide

/-- The env `if.end216` leaves: the advanced cursor, the lane's address, its word,
the extension and the guard. -/
def ifEnd216Cells (env : Env) (k : BitVec 64) (ep : Nat) (inc : BitVec 64)
    (bs4 : List UInt8) (n : BitVec 64) : Env :=
  ("%cmp221.not", .int 1 (evalICmp .ugt n (BitVec.ofNat 64 (bytesToNat bs4)))) ::
    ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
    ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
    ("%arrayidx218", .ptr (ep + (inc.signExtend 64).toNat * 4)) ::
    ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env

theorem ifEnd216_denote (calls : Calls) (env : Env) (s : State)
    {k : BitVec 64} {ep : Nat} {inc : BitVec 64} {a : Nat} {bs4 : List UInt8}
    {n : BitVec 64}
    (hk : lookupName env "%k.0.lcssa1087" = some (.int 64 k))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hinc : lookupName env "%inc.lcssa1130" = some (.int 64 inc))
    (hpos : (inc.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (inc.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hk219 : lookupName env "%k219" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls ifEnd216Instrs (stateAt env s) =
      some (stateAt (ifEnd216Cells env k ep inc bs4 n)
        ({ s with mem := writeBytes s.mem a (natToBytes (k + BitVec.ofNat 64 2).toNat 8) })) := by
  unfold ifEnd216Instrs
  rw [denoteCode_add_imm (calls := calls) (env := env) (s := s)
    (d := "%inc217") (a := "%k.0.lcssa1087") (x := k) (c := BitVec.ofNat 64 2) hk]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env) (s := s)
    (d := "%arrayidx218") (base := "%ep") (off := "%inc.lcssa1130")
    (a := ep) (o := inc)
    (lookupName_cons_other _ _ _ (by decide) hep)
    (lookupName_cons_other _ _ _ (by decide) hinc) hpos]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx218", .ptr (ep + (inc.signExtend 64).toNat * 4)) ::
      ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env) (s := s)
    (d := "%29") (p := "%arrayidx218") (a := ep + (inc.signExtend 64).toNat * 4)
    (w := 32) (bs := bs4) (hw := by decide)
    (by simp only [lookupName_cons_self]) (by simpa using hlane)]
  rw [denoteCode_store64 (calls := calls)
    (env := ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx218", .ptr (ep + (inc.signExtend 64).toNat * 4)) ::
      ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env) (s := s)
    (v := "%inc217") (p := "%k219") (x := k + BitVec.ofNat 64 2) (a := a)
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hk219])]
  rw [denoteCode_zext (calls := calls)
    (env := ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx218", .ptr (ep + (inc.signExtend 64).toNat * 4)) ::
      ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env) (s := _)
    (d := "%conv220") (v := "%29") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 (bytesToNat bs4)) (by simp only [lookupName_cons_self])]
  rw [stage2NoEventOfNat32_toNat hlanelt]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx218", .ptr (ep + (inc.signExtend 64).toNat * 4)) ::
      ("%inc217", .int 64 (k + BitVec.ofNat 64 2)) :: env) (s := _)
    (d := "%cmp221.not") (a := "%n") (b := "%conv220") (p := .ugt) (w := 64)
    (x := n) (y := BitVec.ofNat 64 (bytesToNat bs4))
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), hn])
    (by simp only [lookupName_cons_self]) (is := [])]
  simp only [denoteCode_nil, ifEnd216Cells]

/-- **`if.end216` at an offset inside the document**: the guard taken, to
`if.end230`.  The staging store is inside the walk's own regions, so the
invariant is `stage2NoEventWalkInv.stack_write`. -/
theorem link_ifEnd216_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {ep : Nat} {inc : BitVec 64} {a : Nat}
    {bs4 : List UInt8} {n : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end216")
    (hk : lookupName s.env "%k.0.lcssa1087" = some (.int 64 k))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.lcssa1130" = some (.int 64 inc))
    (hpos : (inc.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (inc.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hk219 : lookupName s.env "%k219" = some (.ptr a))
    (hn : lookupName s.env "%n" = some (.int 64 n))
    (hw : ∀ j, j < (natToBytes (k + BitVec.ofNat 64 2).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + j))
    (hy : evalICmp .ugt n (BitVec.ofNat 64 (bytesToNat bs4)) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored (ifEnd216Cells s.env k ep inc bs4 n) s
        (writeBytes s.mem a (natToBytes (k + BitVec.ofNat 64 2).toNat 8))
        "if.end230") := by
  have hcode : denoteCode calls ifEnd216Instrs (stateAt s.env s) =
      some (stateAt (ifEnd216Cells s.env k ep inc bs4 n)
        ({ s with mem := writeBytes s.mem a (natToBytes (k + BitVec.ofNat 64 2).toNat 8) })) :=
    ifEnd216_denote (calls := calls) s.env s hk hep hinc hpos hlane hlanelt hk219 hn
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr
    (Stage2NoEventWalkInv.stack_write h hw) rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by show stage2NoEventBody.findBlock s.pc = some ifEnd216Block; rw [hpc]; exact ifEnd216Block_find)
    hcode rfl
    (by show lookupName (ifEnd216Cells s.env k ep inc bs4 n) "%cmp221.not" = some (.int 1 1);
        simp only [ifEnd216Cells, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkStored, stateAt] using hstep

/-- **`if.end216` at an offset past the document**: the guard not taken, to
`if.then223`, with the staging store's invariant obligation as above. -/
theorem link_ifEnd216_false {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {ep : Nat} {inc : BitVec 64} {a : Nat}
    {bs4 : List UInt8} {n : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end216")
    (hk : lookupName s.env "%k.0.lcssa1087" = some (.int 64 k))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.lcssa1130" = some (.int 64 inc))
    (hpos : (inc.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (inc.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hk219 : lookupName s.env "%k219" = some (.ptr a))
    (hn : lookupName s.env "%n" = some (.int 64 n))
    (hw : ∀ j, j < (natToBytes (k + BitVec.ofNat 64 2).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + j))
    (hy : evalICmp .ugt n (BitVec.ofNat 64 (bytesToNat bs4)) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored (ifEnd216Cells s.env k ep inc bs4 n) s
        (writeBytes s.mem a (natToBytes (k + BitVec.ofNat 64 2).toNat 8))
        "if.then223") := by
  have hcode : denoteCode calls ifEnd216Instrs (stateAt s.env s) =
      some (stateAt (ifEnd216Cells s.env k ep inc bs4 n)
        ({ s with mem := writeBytes s.mem a (natToBytes (k + BitVec.ofNat 64 2).toNat 8) })) :=
    ifEnd216_denote (calls := calls) s.env s hk hep hinc hpos hlane hlanelt hk219 hn
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr
    (Stage2NoEventWalkInv.stack_write h hw) rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by show stage2NoEventBody.findBlock s.pc = some ifEnd216Block; rw [hpc]; exact ifEnd216Block_find)
    hcode rfl
    (by show lookupName (ifEnd216Cells s.env k ep inc bs4 n) "%cmp221.not" = some (.int 1 0);
        simp only [ifEnd216Cells, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkStored, stateAt] using hstep

/-! ### `if.end230`: the call's length and the scratch guard

The block inverts the entry's index, subtracts it from the entry's offset, adds
the class's 64-byte reserve and tests the result against the scratch capacity. -/

/-- `if.end230`: the call's length and the scratch guard. -/
def ifEnd230Instrs : List Instr :=
  [ Instr.binop "%30" BinOp.xor 64 (Operand.reg "%idxprom.lcssa1109")
      (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
    Instr.binop "%sub234" BinOp.add 64 (Operand.reg "%conv220") (Operand.reg "%30"),
    Instr.binop "%add235" BinOp.add 64 (Operand.reg "%sub234")
      (Operand.imm (.int 64 (BitVec.ofNat 64 64))),
    Instr.icmp "%cmp236" IPred.ugt 64 (Operand.reg "%add235")
      (Operand.reg "%scratchcap") ]

/-- `if.end230`, pinned. -/
def ifEnd230Block : Block :=
  { name := "if.end230", instrs := ifEnd230Instrs,
    term := Term.condbr (Operand.reg "%cmp236") "if.then238" "if.end239" }

theorem ifEnd230Block_find :
    stage2NoEventBody.findBlock "if.end230" = some ifEnd230Block := by
  decide

/-- The env `if.end230` leaves: the inverted index, the length, the guarded length
and the capacity test. -/
def ifEnd230Cells (env : Env) (idx : BitVec 64) (v : BitVec 64) (cap : BitVec 64) : Env :=
  ("%cmp236", .int 1
      (evalICmp .ugt ((v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) +
        BitVec.ofNat 64 64) cap)) ::
    ("%add235", .int 64 ((v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) +
      BitVec.ofNat 64 64)) ::
    ("%sub234", .int 64 (v + (idx ^^^ BitVec.ofNat 64 18446744073709551615))) ::
    ("%30", .int 64 (idx ^^^ BitVec.ofNat 64 18446744073709551615)) :: env

theorem ifEnd230_denote (calls : Calls) (env : Env) (s : State)
    {idx v cap : BitVec 64}
    (hidx : lookupName env "%idxprom.lcssa1109" = some (.int 64 idx))
    (hv : lookupName env "%conv220" = some (.int 64 v))
    (hcap : lookupName env "%scratchcap" = some (.int 64 cap)) :
    denoteCode calls ifEnd230Instrs (stateAt env s) =
      some (stateAt (ifEnd230Cells env idx v cap) s) := by
  unfold ifEnd230Instrs
  rw [denoteCode_xor_imm (calls := calls) (env := env) (s := s) (d := "%30")
    (a := "%idxprom.lcssa1109")
    (c := BitVec.ofNat 64 18446744073709551615) hidx]
  rw [denoteCode_add_reg (calls := calls)
    (env := ("%30", .int 64 (idx ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (d := "%sub234") (a := "%conv220") (b := "%30")
    (x := v) (y := idx ^^^ BitVec.ofNat 64 18446744073709551615)
    (lookupName_cons_other _ _ _ (by decide) hv)
    (by simp only [lookupName_cons_self])]
  rw [denoteCode_add_imm (calls := calls)
    (env := ("%sub234", .int 64 (v + (idx ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (idx ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (d := "%add235") (a := "%sub234")
    (x := v + (idx ^^^ BitVec.ofNat 64 18446744073709551615))
    (c := BitVec.ofNat 64 64) (by simp only [lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%add235", .int 64 ((v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) +
        BitVec.ofNat 64 64)) ::
      ("%sub234", .int 64 (v + (idx ^^^ BitVec.ofNat 64 18446744073709551615))) ::
      ("%30", .int 64 (idx ^^^ BitVec.ofNat 64 18446744073709551615)) :: env)
    (s := s) (d := "%cmp236") (a := "%add235") (b := "%scratchcap") (p := .ugt) (w := 64)
    (x := (v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
    (y := cap)
    (by simp only [lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hcap) (is := [])]
  simp only [denoteCode_nil, ifEnd230Cells]

/-- **`if.end230` inside the scratch capacity**: the guard taken, to `if.then238`. -/
theorem link_ifEnd230_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {idx v cap : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end230")
    (hidx : lookupName s.env "%idxprom.lcssa1109" = some (.int 64 idx))
    (hv : lookupName s.env "%conv220" = some (.int 64 v))
    (hcap : lookupName s.env "%scratchcap" = some (.int 64 cap))
    (hy : evalICmp .ugt ((v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) +
      BitVec.ofNat 64 64) cap = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (ifEnd230Cells s.env idx v cap) s "if.then238") := by
  have hcode : denoteCode calls ifEnd230Instrs (stateAt s.env s) =
      some (stateAt (ifEnd230Cells s.env idx v cap) s) :=
    ifEnd230_denote (calls := calls) s.env s hidx hv hcap
  exact stage2NoEventWalkLink_condbr_true (env' := ifEnd230Cells s.env idx v cap)
    h (by rw [hpc]; exact ifEnd230Block_find) hcode rfl
    (by simp only [ifEnd230Cells, lookupName_cons_self, hy])

/-- **`if.end230` at or past the scratch capacity**: the guard not taken, to
`if.end239`'s entry. -/
theorem link_ifEnd230_false {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {idx v cap : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end230")
    (hidx : lookupName s.env "%idxprom.lcssa1109" = some (.int 64 idx))
    (hv : lookupName s.env "%conv220" = some (.int 64 v))
    (hcap : lookupName s.env "%scratchcap" = some (.int 64 cap))
    (hy : evalICmp .ugt ((v + (idx ^^^ BitVec.ofNat 64 18446744073709551615)) +
      BitVec.ofNat 64 64) cap = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (ifEnd230Cells s.env idx v cap) s "if.end239") := by
  have hcode : denoteCode calls ifEnd230Instrs (stateAt s.env s) =
      some (stateAt (ifEnd230Cells s.env idx v cap) s) :=
    ifEnd230_denote (calls := calls) s.env s hidx hv hcap
  exact stage2NoEventWalkLink_condbr_false (env' := ifEnd230Cells s.env idx v cap)
    h (by rw [hpc]; exact ifEnd230Block_find) hcode rfl
    (by simp only [ifEnd230Cells, lookupName_cons_self, hy])

/-! ### `if.then238`: the trap

The block is one `@llvm.trap` call and an `unreachable` terminator.  The call
selection answers the symbol with `none`, so the block's denotation is `none` and
the control step is `.ub`: there is no link, and the honest statement is the
undefined outcome. -/

/-- `if.then238`: the trap. -/
def ifThen238Instrs : List Instr := [ Instr.callVoid "llvm.trap" [] ]

/-- `if.then238`, pinned. -/
def ifThen238Block : Block :=
  { name := "if.then238", instrs := ifThen238Instrs, term := Term.unreachable }

theorem ifThen238Block_find :
    stage2NoEventBody.findBlock "if.then238" = some ifThen238Block := by
  decide

/-- The trap call makes the block undefined. -/
theorem ifThen238_denote_none {calls : Calls} (s : State)
    (hc : calls "llvm.trap" [] s.mem s.next = none) :
    denoteCode calls ifThen238Instrs s = none := by
  unfold ifThen238Instrs
  refine denoteCode_cons_none (calls := calls) (i := Instr.callVoid "llvm.trap" [])
    (is := []) (s := s) ?_ (by rfl)
  simp only [evalInstr, evalOperands, hc]

/-- **The trap's control step is `ub`**, for any selection answering the symbol
with `none`. -/
theorem ifThen238_step_ub {calls : Calls} {s : State}
    (hpc : s.pc = "if.then238")
    (hc : calls "llvm.trap" [] s.mem s.next = none) :
    step calls stage2NoEventBody s = .ub := by
  have hcode : denoteCode calls ifThen238Block.instrs s = none := by
    simpa only [ifThen238Block] using ifThen238_denote_none (calls := calls) s hc
  simp only [step, hpc, ifThen238Block_find]
  rw [hcode]

/-- **The trap at the body's own selection**: `stage2Calls` answers `@llvm.trap`
with `none` for every gap, so the step is `ub`. -/
theorem ifThen238_step_ub_stage2Calls {gap : Calls} {s : State}
    (hpc : s.pc = "if.then238") :
    step (stage2NoEventCalls gap) stage2NoEventBody s = .ub := by
  refine ifThen238_step_ub hpc ?_
  simp only [stage2NoEventCalls]
  rw [ite_eq_right (by decide)]
  exact JsonStage2IR.stage2Calls_trap

/-! ### Axiom footprints -/

#print axioms ifThen209Block_find
#print axioms ifThen209_denote
#print axioms ifThen209_step
#print axioms ifThen223Block_find
#print axioms ifThen223_denote
#print axioms ifThen223_step
#print axioms ifEnd216Block_find
#print axioms ifEnd216_denote
#print axioms link_ifEnd216_true
#print axioms link_ifEnd216_false
#print axioms ifEnd230Block_find
#print axioms ifEnd230_denote
#print axioms link_ifEnd230_true
#print axioms link_ifEnd230_false
#print axioms ifThen238Block_find
#print axioms ifThen238_denote_none
#print axioms ifThen238_step_ub
#print axioms ifThen238_step_ub_stage2Calls

end LeanLLVM.Refinement
