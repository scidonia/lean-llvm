/-
The no-event walk's object class row: the empty pair's route to the
after-value endpoint, and the shared cycle's return to the next head.

A `{` at the head's lane and `}` at the next entry's is the object class's
empty pair.  Its route is the body's own thirteen blocks: the three-block
dispatch to `if.then9`, that head's seven-`phi` run and depth test at a live
depth, the push (`if.end19` → `if.then20` → `if.end23`), the next entry's
read (`if.end74` → `NodeBlock21` → `LeafBlock19`), the count store
(`if.then81`: `+2` tokens, `+3` terms), `close_obj`'s six-`phi` run and depth
test, and `if.then343`'s pop of the byte the push wrote, to `after_value`.

Three links the container family did not have:

* **`if.then9` at a carried depth.**  The first iteration's lemma pins the
  head's `%frame`, `%sp`, `%terms` and `%tokens` at zero; a continuation head
  carries them.  `link_braceIfThen9_false` is the same block at arbitrary
  carried values, with the depth guard false.
* **`close_obj`'s live arm.**  The closer's suffix lemma
  (`closeObjRest_denote`) is the decrement and its test; the six-`phi` run
  above it is `closeObjPhi_denote`, and `link_closeObj_live` composes them at
  a non-zero depth to `if.then343`.
* **`if.then343`.**  The pop is `ifThen343_denote` at an abstract address;
  `link_ifThen343` is the link to `after_value`.

The pair's counts are the blocks': `if.then81` adds two tokens and three terms
(`%inc82 = %k + 2`, `%inc84 = %tokens + 2`, `%add85 = %terms + 3`), and
`close_obj` changes no count.  The closer's own contribution is the frame it
pops, which is the frame the push stored.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerB

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The `{` pair's addresses

The push writes one stack byte below the depth; the pop reads the byte at the
depth the `if.then343` edge's decrement carries.
-/

/-- The address the object's pop reads: `%stk + ((%sp + 1) − 2)`. -/
def bracePopAddr (K : Stage2NoEventWalkCarry) (sp : Nat) : Nat :=
  closeReadAddr K.stk
    ((BitVec.ofNat 32 sp + BitVec.ofNat 32 1) + BitVec.ofNat 32 4294967294).toNat

/-! ### `if.then9` at a carried depth

`ifThen9`'s seven `phi`s select the `LeafBlock3` edge's registers.  At the
first iteration those are the preheader's zeros; at a continuation head they
are the carried readings.  The lemma below is the block at any of them, and
the link takes the depth guard's false arm to `if.end19`.
-/

/-- The `if.then9` cells on the `LeafBlock3` edge, at carried values. -/
abbrev braceIfThen9Cells (env : Env) (inc idx : BitVec 64) (fr : BitVec 8)
    (sp : BitVec 32) (k terms tok : BitVec 64) : Env :=
  ("%cmp10", .int 1 0) ::
    ("%tokens.0.lcssa1074", .int 64 tok) ::
    ("%terms.0.lcssa1080", .int 64 terms) ::
    ("%k.0.lcssa1086", .int 64 k) ::
    ("%sp.0.lcssa1092.wide", .int 32 sp) ::
    ("%frame.0.lcssa1098", .int 8 fr) ::
    ("%idxprom.lcssa1108", .int 64 idx) ::
    ("%inc.lcssa1129", .int 64 inc) :: env

/-- **`if.then9`'s seven `phi`s and depth test, at carried values**: the
`LeafBlock3` edge's registers, the run's cells, and the guard's false arm. -/
theorem braceIfThen9_denote (calls : Calls) (env : Env) (s : State)
    {inc idx : BitVec 64} {fr : BitVec 8} {sp : BitVec 32} {k terms tok : BitVec 64}
    (hpre : s.pre = some "LeafBlock3")
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 k))
    (hinc : lookupName env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName env "%idxprom.peel" = some (.int 64 idx))
    (hfr : lookupName env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 tok))
    (hguard : evalICmp .ugt sp (BitVec.ofNat 32 519) = 0) :
    denoteCode calls ifThen9Instrs (stateAt env s) =
      some (stateAt (braceIfThen9Cells env inc idx fr sp k terms tok) s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock3" ifThen9PhiSpecs
      [("%inc.lcssa1129", .int 64 inc),
       ("%idxprom.lcssa1108", .int 64 idx),
       ("%frame.0.lcssa1098", .int 8 fr),
       ("%sp.0.lcssa1092.wide", .int 32 sp),
       ("%k.0.lcssa1086", .int 64 k),
       ("%terms.0.lcssa1080", .int 64 terms),
       ("%tokens.0.lcssa1074", .int 64 tok)] := by
    refine PhiSelects.cons (op := .reg "%inc.peel") (by decide) ?_
      (PhiSelects.cons (op := .reg "%idxprom.peel") (by decide) ?_
        (PhiSelects.cons (op := .reg "%frame.0.ph1402") (by decide) ?_
          (PhiSelects.cons (op := .reg "%sp.0.ph1403") (by decide) ?_
            (PhiSelects.cons (op := .reg "%k.0.ph1404") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.0.ph1407") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.0.ph1408") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hinc, hidx, hfr, hsp, hk, htr, htok]
  rw [ifThen9Phi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "LeafBlock3")
      (specs := ifThen9PhiSpecs)
      (vs := [("%inc.lcssa1129", .int 64 inc),
        ("%idxprom.lcssa1108", .int 64 idx),
        ("%frame.0.lcssa1098", .int 8 fr),
        ("%sp.0.lcssa1092.wide", .int 32 sp),
        ("%k.0.lcssa1086", .int 64 k),
        ("%terms.0.lcssa1080", .int 64 terms),
        ("%tokens.0.lcssa1074", .int 64 tok)])
      (rest := [Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
        (Operand.imm (.int 32 (BitVec.ofNat 32 519)))])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  rw [stateAt_bindAll_runCells]
  have hSp : lookupName (runCells
      [("%inc.lcssa1129", .int 64 inc), ("%idxprom.lcssa1108", .int 64 idx),
       ("%frame.0.lcssa1098", .int 8 fr), ("%sp.0.lcssa1092.wide", .int 32 sp),
       ("%k.0.lcssa1086", .int 64 k), ("%terms.0.lcssa1080", .int 64 terms),
       ("%tokens.0.lcssa1074", .int 64 tok)] env) "%sp.0.lcssa1092.wide"
      = some (.int 32 sp) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := runCells
      [("%inc.lcssa1129", .int 64 inc), ("%idxprom.lcssa1108", .int 64 idx),
       ("%frame.0.lcssa1098", .int 8 fr), ("%sp.0.lcssa1092.wide", .int 32 sp),
       ("%k.0.lcssa1086", .int 64 k), ("%terms.0.lcssa1080", .int 64 terms),
       ("%tokens.0.lcssa1074", .int 64 tok)] env) (s := s)
    (d := "%cmp10") (a := "%sp.0.lcssa1092.wide") (p := .ugt) (w := 32)
    (c := BitVec.ofNat 32 519) hSp (is := [])]
  simp only [hguard, denoteCode_nil, braceIfThen9Cells, runCells]

/-- **The `if.then9` link at a carried depth**: the seven `phi`s, the depth
guard at the run's cells, and the false arm to `if.end19`. -/
theorem link_braceIfThen9_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc idx : BitVec 64} {fr : BitVec 8} {sp : BitVec 32}
    {k terms tok : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9")
    (hpre : s.pre = some "LeafBlock3")
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.peel" = some (.int 64 idx))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (hguard : evalICmp .ugt sp (BitVec.ofNat 32 519) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (braceIfThen9Cells s.env inc idx fr sp k terms tok)
        s "if.end19") := by
  have hblock : ifThen9Block.instrs = ifThen9Instrs := by decide
  have hcode : denoteCode calls ifThen9Block.instrs (stateAt s.env s) =
      some (stateAt (braceIfThen9Cells s.env inc idx fr sp k terms tok) s) := by
    rw [hblock]
    exact braceIfThen9_denote (calls := calls) s.env s hpre hk hinc hidx hfr hsp htr htok
      hguard
  refine stage2NoEventWalkLink_condbr_false
    (env' := braceIfThen9Cells s.env inc idx fr sp k terms tok)
    h (by rw [hpc]; exact ifThen9Block_find) hcode rfl ?_
  simp only [braceIfThen9Cells, lookupName_cons_self]

/-! ### `close_obj`'s live arm

The block's six `phi`s carry the counts and the depth the `if.then81` edge
stored; the two instructions after them decrement the depth and test it.  At a
depth above one the test is false and the block hands to `if.then343`.
-/

/-- `close_obj`'s six `phi`s, as specs. -/
def closeObjPhiSpecs : List PhiSpec :=
  [ { dst := "%sp.2", ty := Ty.int 32,
      incoming := [("if.then81", Operand.reg "%inc24"),
        ("do.body391", Operand.reg "%sp.4")] },
    { dst := "%k.4", ty := Ty.int 64,
      incoming := [("if.then81", Operand.reg "%inc82"),
        ("do.body391", Operand.reg "%inc379")] },
    { dst := "%alen.6", ty := Ty.int 64,
      incoming := [("if.then81", Operand.reg "%alen.0.ph1405"),
        ("do.body391", Operand.reg "%alen.8")] },
    { dst := "%arena.8", ty := Ty.int 64,
      incoming := [("if.then81", Operand.reg "%arena.0.ph1406"),
        ("do.body391", Operand.reg "%arena.10")] },
    { dst := "%terms.6", ty := Ty.int 64,
      incoming := [("if.then81", Operand.reg "%add85"),
        ("do.body391", Operand.reg "%add393")] },
    { dst := "%tokens.6", ty := Ty.int 64,
      incoming := [("if.then81", Operand.reg "%inc84"),
        ("do.body391", Operand.reg "%inc392")] } ]

/-- The block's `phi` list is the spec list's instructions. -/
theorem closeObjPhi_eq :
    closeObjPhiInstrs = List.map PhiSpec.instr closeObjPhiSpecs := by
  decide

/-- The six `phi` cells `close_obj` installs, newest first. -/
def braceCloseObjCells (sp2 : BitVec 32) (k4 alen arena terms6 toks : BitVec 64) :
    List (String × Value) :=
  [("%tokens.6", .int 64 toks), ("%terms.6", .int 64 terms6),
   ("%arena.8", .int 64 arena), ("%alen.6", .int 64 alen), ("%k.4", .int 64 k4),
   ("%sp.2", .int 32 sp2)]

/-- **`close_obj`'s six `phi`s at the `if.then81` edge.** -/
theorem closeObjPhi_denote (calls : Calls) (env : Env) (s : State)
    {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (hpre : s.pre = some "if.then81")
    (hsp2 : lookupName env "%inc24" = some (.int 32 sp2))
    (hk4 : lookupName env "%inc82" = some (.int 64 k4))
    (halen : lookupName env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName env "%arena.0.ph1406" = some (.int 64 arena))
    (hterms : lookupName env "%add85" = some (.int 64 terms6))
    (htoks : lookupName env "%inc84" = some (.int 64 toks)) :
    denoteCode calls closeObjPhiInstrs (stateAt env s) =
      some (stateAt (cells (braceCloseObjCells sp2 k4 alen arena terms6 toks) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then81" closeObjPhiSpecs
      [("%sp.2", .int 32 sp2), ("%k.4", .int 64 k4), ("%alen.6", .int 64 alen),
       ("%arena.8", .int 64 arena), ("%terms.6", .int 64 terms6),
       ("%tokens.6", .int 64 toks)] := by
    refine PhiSelects.cons (op := .reg "%inc24") (by decide) ?_
      (PhiSelects.cons (op := .reg "%inc82") (by decide) ?_
        (PhiSelects.cons (op := .reg "%alen.0.ph1405") (by decide) ?_
          (PhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
            (PhiSelects.cons (op := .reg "%add85") (by decide) ?_
              (PhiSelects.cons (op := .reg "%inc84") (by decide) ?_
                PhiSelects.nil)))))
    all_goals
      simp only [stateAt, evalOperand, hsp2, hk4, halen, harena, hterms, htoks]
  rw [closeObjPhi_eq, ← List.append_nil (List.map PhiSpec.instr closeObjPhiSpecs)]
  rw [denoteCode_phiRun (s := stateAt env s) (p := "if.then81")
    (specs := closeObjPhiSpecs)
    (vs := [("%sp.2", .int 32 sp2), ("%k.4", .int 64 k4), ("%alen.6", .int 64 alen),
      ("%arena.8", .int 64 arena), ("%terms.6", .int 64 terms6),
      ("%tokens.6", .int 64 toks)])
    (rest := []) (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  simp only [braceCloseObjCells, cells, runCells, denoteCode_nil]

/-- **`close_obj`'s decrement and test at the six-`phi` cells.** -/
theorem braceCloseObjRest_denote (calls : Calls) (env : Env) (s : State)
    {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64} :
    denoteCode calls closeObjRest
        (stateAt (cells (braceCloseObjCells sp2 k4 alen arena terms6 toks) env) s) =
      some (stateAt (cells (closeObjTail sp2 ++
        braceCloseObjCells sp2 k4 alen arena terms6 toks) env) s) := by
  rw [closeObjRest]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := cells (braceCloseObjCells sp2 k4 alen arena terms6 toks) env) (s := s)
    (d := "%dec") (a := "%sp.2") (w := 32) (x := sp2)
    (stage2NoEventWalkCells_some (cs := braceCloseObjCells sp2 k4 alen arena terms6 toks)
      (n := "%sp.2") (env := env)
      (by simp only [braceCloseObjCells, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [braceCloseObjCells, List.map_cons, List.map_nil]; decide))]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := _) (s := s)
    (d := "%tobool342.not") (a := "%dec") (p := .eq) (w := 32)
    (x := sp2 + BitVec.ofNat 32 4294967295) (c := BitVec.ofNat 32 0)
    (by simp only [lookupName_cons_self]) (is := [])]
  rw [closeObjTail, denoteCode_nil]
  simp only [cells, List.cons_append, List.nil_append]

/-- **`close_obj`'s live arm**: the six-`phi` run, the decrement and its test at
a depth above one, and the false arm to `if.then343`. -/
theorem link_closeObj_live {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_obj")
    (hpre : s.pre = some "if.then81")
    (hsp2 : lookupName s.env "%inc24" = some (.int 32 sp2))
    (hk4 : lookupName s.env "%inc82" = some (.int 64 k4))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hterms : lookupName s.env "%add85" = some (.int 64 terms6))
    (htoks : lookupName s.env "%inc84" = some (.int 64 toks))
    (hdec : (sp2 + BitVec.ofNat 32 4294967295).toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (closeObjTail sp2 ++
          braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env) s "if.then343") := by
  have h1 := closeObjPhi_denote (calls := calls) (env := s.env) (s := s)
    hpre hsp2 hk4 halen harena hterms htoks
  have h2 := braceCloseObjRest_denote (calls := calls) (env := s.env) (s := s)
    (sp2 := sp2) (k4 := k4) (alen := alen) (arena := arena)
    (terms6 := terms6) (toks := toks)
  have hbit : evalICmp .eq (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0)
      = (0 : BitVec 1) := stage2NoEventEq0_zero hdec
  refine stage2NoEventWalkLink_condbr_false
    (env' := cells (closeObjTail sp2 ++
      braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env)
    h (by rw [hpc]; exact closeObjBlock_find) ?_ rfl ?_
  · rw [closeObj_split,
      denoteCode_append_apply (a := closeObjPhiInstrs) (b := closeObjRest) h1 (by decide)]
    exact h2
  · simp only [closeObjTail, braceCloseObjCells, cells, List.cons_append,
      List.nil_append, lookupName_cons_self, hbit]

/-! ### `if.then343`: the pop

`ifThen343_denote` is the block at an abstract address; the link names
`after_value` as the target.
-/

/-- **The `if.then343` link**: the depth word, the `gep`, the one byte, and the
branch to `after_value`. -/
theorem link_ifThen343 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {stk : Nat} {sp2 : BitVec 32} {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then343")
    (hsp2 : lookupName s.env "%sp.2" = some (.int 32 sp2))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hbyte : readBytes s.mem a 1 = some bs)
    (ha : a = closeReadAddr stk (sp2 + BitVec.ofNat 32 4294967294).toNat) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
          closeGepCells a ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
          s.env) s "after_value") := by
  have hcode : denoteCode calls ifThen343Block.instrs (stateAt s.env s) =
      some (stateAt
        (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
          closeGepCells a ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
          s.env) s) :=
    ifThen343_denote (calls := calls) (env := s.env) (s := s)
      (stk := stk) (sp2 := sp2) (a := a) (bs := bs) ha hsp2 hstk hbyte
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen343Block_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr h rfl

/-! ### The `{}` route

The head's dispatch, the carried-depth `if.then9`, the push, the next entry's
read, the count store, the live closer, and the pop: thirteen blocks from the
head to `after_value`'s entry.
-/

/-- **The empty object pair's route**: thirteen blocks from the head to
`after_value`'s entry, with the pair's carry and the endpoint's
`Stage2NoEventWalkCycleSrc`. -/
theorem stage2NoEventWalkBracePairLeg {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    ∃ (s' : State) (Kc : Stage2NoEventWalkCarry),
      Kc = { K with tok := K.tok + 2, terms := K.terms + 3 } ∧
      Stage2NoEventWalkSegment calls mem K s Kc s' 13 ∧
      Nonempty (Stage2NoEventWalkCycleSrc calls mem Kc (k + 2) s') := by
  classical
  let Kc : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 3 }
  let spv : BitVec 32 := BitVec.ofNat 32 sp
  let frv : BitVec 8 := BitVec.ofNat 8 fr
  let k64 : BitVec 64 := BitVec.ofNat 64 k
  let termsv : BitVec 64 := BitVec.ofNat 64 K.terms
  let tokv : BitVec 64 := BitVec.ofNat 64 K.tok
  let nep64 : BitVec 64 := BitVec.ofNat 64 K.nep
  let inc : BitVec 64 := BitVec.ofNat 64 (k + 1)
  -- the head's own facts
  have h3H : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    h.braceCell hk hbs hb
  have hkH : lookupName s.env "%k.0.ph1404" = some (.int 64 k64) := h.kEq
  have htrH : lookupName s.env "%terms.0.ph1407" = some (.int 64 termsv) := h.termsPhi
  have htokH : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tokv) := h.tokensPhi
  have halenH : lookupName s.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := h.alenPhi
  have harenaH : lookupName s.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := h.arenaPhi
  have hnepH : lookupName s.env "%nep" = some (.int 64 nep64) := h.nepI
  have hepH : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbH : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  have hstkH : lookupName s.env "%stk" = some (.ptr K.stk) := h.stk
  obtain ⟨laneR, byteR, -, -, -, -, -, hidxH, hincH, -, -, -⟩ := h.laneRead
  let idx : BitVec 64 := BitVec.ofNat 64 laneR
  -- the three dispatch blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3H (by decide)
  have h3_1 : lookupName S1.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3H
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 0) :: S1.env) S1 "LeafBlock3"
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3_1 (by decide)
  have h3_2 : lookupName S2.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3_1
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 1) :: S2.env) S2 "if.then9"
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock3_true L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3_2 (by decide)
  -- the head edge's phi inputs, at the dispatch's environment
  have hk3 : lookupName S3.env "%k.0.ph1404" = some (.int 64 k64) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hkH
  have hinc3 : lookupName S3.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hidx3 : lookupName S3.env "%idxprom.peel" = some (.int 64 idx) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidxH
  have hfr3 : lookupName S3.env "%frame.0.ph1402" = some (.int 8 frv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hsp3 : lookupName S3.env "%sp.0.ph1403" = some (.int 32 spv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have htr3 : lookupName S3.env "%terms.0.ph1407" = some (.int 64 termsv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htrH
  have htok3 : lookupName S3.env "%tokens.0.ph1408" = some (.int 64 tokv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokH
  have hguard : evalICmp .ugt spv (BitVec.ofNat 32 519) = (0 : BitVec 1) :=
    stage2NoEventUgt519_zero (by
      rw [show spv.toNat = sp from by
        simp only [spv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]]
      exact hspLe)
  -- `if.then9` at the carried depth
  let S4 := stage2NoEventWalkNext
    (braceIfThen9Cells S3.env inc idx frv spv k64 termsv tokv) S3 "if.end19"
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_braceIfThen9_false L3.inv' rfl rfl hk3 hinc3 hidx3 hfr3 hsp3 htr3 htok3 hguard
  -- the push's first link
  have hsp4 : lookupName S4.env "%sp.0.lcssa1092.wide" = some (.int 32 spv) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  let S5 := stage2NoEventWalkNext
    (("%tobool.not", .int 1 (evalICmp .eq spv (BitVec.ofNat 32 0))) :: S4.env)
    S4 "if.then20"
  have hspvPos : 1 ≤ spv.toNat := by
    rw [show spv.toNat = sp from by
      simp only [spv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]]
    exact hspPos
  have hspvLe : spv.toNat ≤ 519 := by
    rw [show spv.toNat = sp from by
      simp only [spv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]]
    exact hspLe
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd19 L4.inv' rfl hsp4 (by omega)
  have hsp5 : lookupName S5.env "%sp.0.lcssa1092.wide" = some (.int 32 spv) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hfr5 : lookupName S5.env "%frame.0.lcssa1098" = some (.int 8 frv) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hstk5 : lookupName S5.env "%stk" = some (.ptr K.stk) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstkH
  let S6 := stage2NoEventWalkStored
    (("%arrayidx22", .ptr (bracePushAddr K spv)) ::
      ("%idxprom21", .int 64 (BitVec.ofNat 64
        ((spv + BitVec.ofNat 32 4294967295).toNat))) ::
      ("%sub", .int 32 (spv + BitVec.ofNat 32 4294967295)) :: S5.env)
    S5 (writeBytes S5.mem (bracePushAddr K spv) (natToBytes frv.toNat 1)) "if.end23"
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifThen20 L5.inv' rfl hsp5 hfr5 hstk5 hspvPos hspvLe
  have hsp6 : lookupName S6.env "%sp.0.lcssa1092.wide" = some (.int 32 spv) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hinc6 : lookupName S6.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hnep6 : lookupName S6.env "%nep" = some (.int 64 nep64) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnepH
  have hincNat : inc.toNat = k + 1 := by
    simp only [inc, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
  have hult : BitVec.ult inc nep64 = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [hincNat, show nep64.toNat = K.nep from by
      simp only [nep64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.inv.nepLt]]
    omega
  let S7 := stage2NoEventWalkNext
    (("%cmp66.not", .int 1 1) :: ("%inc24", .int 32 (spv + BitVec.ofNat 32 1))
      :: S6.env) S6 "if.end74"
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd23 L6.inv' rfl hsp6 hinc6 hnep6 hult
  have hterms7 : lookupName S7.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htok7 : lookupName S7.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hep7 : lookupName S7.env "%ep" = some (.ptr K.ep) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hepH
  have hb7 : lookupName S7.env "%b" = some (.ptr K.b) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbH
  have hinc7 : lookupName S7.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hincLt : inc.toNat < 2 ^ 63 := by rw [hincNat]; omega
  have hbyte1Ws : readBytes S7.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte] := hbyte1W
  let S8 := stage2NoEventWalkNext
    (ifEnd74Out S7.env K.ep K.b termsv tokv inc bs4 [nextByte]) S7 "NodeBlock21"
  have L8 : Stage2NoEventWalkLink calls K mem S7 K S8 :=
    link_ifEnd74 L7.inv' rfl hterms7 htok7 hep7 hb7 hinc7 hincLt hlaneW hval4lt hbyte1Ws
  -- the closer's dispatch
  have h11_8 : lookupName S8.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S8, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    rw [lookupName_cons_self]
  have h11slt : evalICmp .slt (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (0 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S9 := stage2NoEventWalkNext (("%Pivot22", .int 1 0) :: S8.env) S8 "LeafBlock19"
  have L9 : Stage2NoEventWalkLink calls K mem S8 K S9 :=
    link_nodeBlock21_false L8.inv' rfl h11_8 h11slt
  have h11_9 : lookupName S9.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S9, S8, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have h11eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = (1 : BitVec 1) := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]
    decide
  let S10 := stage2NoEventWalkNext (("%SwitchLeaf20", .int 1 1) :: S9.env) S9 "if.then81"
  have L10 : Stage2NoEventWalkLink calls K mem S9 K S10 :=
    link_leafBlock19_true L9.inv' rfl h11_9 h11eq
  have hk10 : lookupName S10.env "%k.0.lcssa1086" = some (.int 64 k64) := by
    simp only [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htok10 : lookupName S10.env "%tokens.0.lcssa1074" = some (.int 64 tokv) := by
    simp only [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htr10 : lookupName S10.env "%terms.0.lcssa1080" = some (.int 64 termsv) := by
    simp only [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells, braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk64nat : k64.toNat = k := by
    simp only [k64, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  have hcount10 : Stage2NoEventWalkCount K k64.toNat := by
    rw [hk64nat]; exact h.count
  have hkb : k64.toNat + 2 ≤ K.nep := by rw [hk64nat]; omega
  -- the pair's count store
  let S11 := stage2NoEventWalkNext (ifThen81Out S10.env k64 tokv termsv) S10 "close_obj"
  have L11 : Stage2NoEventWalkLink calls K mem S10 Kc S11 :=
    link_ifThen81_of_bound L10.inv' rfl rfl hk10 htok10 htr10 hcount10 hkb
  -- the live closer's operands
  let sp2 : BitVec 32 := spv + BitVec.ofNat 32 1
  have hsp11 : lookupName S11.env "%inc24" = some (.int 32 sp2) := by
    simp only [S11, S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifThen81Out, ifEnd74Out, ifEnd74Cells, cells,
      braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4c11 : lookupName S11.env "%inc82"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms11 : lookupName S11.env "%add85"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    rw [lookupName_cons_self]
  have htoks11 : lookupName S11.env "%inc84"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S11, stage2NoEventWalkNext, ifThen81Out, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen11 : lookupName S11.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S11, S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifThen81Out, ifEnd74Out, ifEnd74Cells, cells,
      braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halenH
  have harena11 : lookupName S11.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S11, S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
      stage2NoEventWalkStored, ifThen81Out, ifEnd74Out, ifEnd74Cells, cells,
      braceIfThen9Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harenaH
  have hsp2nat : sp2.toNat = sp + 1 := by
    have h1 : spv.toNat = sp := by
      simp only [spv, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hspLt]
    simp only [sp2, BitVec.toNat_add, h1]
    rw [show (BitVec.ofNat 32 1 : BitVec 32).toNat = 1 from by decide,
      Nat.mod_eq_of_lt (by omega : sp + 1 < 2 ^ 32)]
  have hdecEq : (sp2 + BitVec.ofNat 32 4294967295).toNat = sp := by
    rw [BitVec.toNat_add, hsp2nat,
      show (BitVec.ofNat 32 4294967295 : BitVec 32).toNat = 4294967295 from by decide]
    have h2 : sp + 1 + 4294967295 = sp + 1 * 2 ^ 32 := by
      show sp + 1 + 4294967295 = sp + 1 * 4294967296
      omega
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hspLt]
  have hdecne : (sp2 + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [hdecEq]; omega
  let S12 := stage2NoEventWalkNext
    (cells (closeObjTail sp2 ++ braceCloseObjCells sp2
      (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
      (tokv + BitVec.ofNat 64 2)) S11.env) S11 "if.then343"
  have L12 : Stage2NoEventWalkLink calls Kc mem S11 Kc S12 :=
    link_closeObj_live L11.inv' rfl rfl hsp11 hk4c11 halen11 harena11 hterms11 htoks11
      hdecne
  -- the pop
  let a343 : Nat := bracePopAddr K sp
  have hsp12 : lookupName S12.env "%sp.2" = some (.int 32 sp2) := by
    simp only [S12, stage2NoEventWalkNext, closeObjTail, braceCloseObjCells, cells,
      List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hstk12 : lookupName S12.env "%stk" = some (.ptr K.stk) := by
    simp only [S12, S11, S10, S9, S8, S7, S6, S5, S4, S3, S2, S1,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifThen81Out, ifEnd74Out,
      ifEnd74Cells, cells, closeObjTail, braceCloseObjCells, braceIfThen9Cells,
      List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstkH
  have ha343 : a343 = closeReadAddr K.stk
      (sp2 + BitVec.ofNat 32 4294967294).toNat := by
    simp only [a343, sp2, spv, bracePopAddr]
  let S13 := stage2NoEventWalkNext
    (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      S12.env) S12 "after_value"
  have L13 : Stage2NoEventWalkLink calls Kc mem S12 Kc S13 :=
    link_ifThen343 L12.inv' rfl hsp12 hstk12 hbytePop ha343
  -- the run, at the thirteen links' own fuel
  have hrun : ∀ n, runFuel calls (13 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S13 := by
    intro n
    rw [show 13 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
      (1 + (1 + n)))))))))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8,
      stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11, stage2NoEventWalkLink_runFuel L12,
      stage2NoEventWalkLink_runFuel L13]
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc S13 13 :=
    ⟨hrun, L13.inv'⟩
  -- the pair's trace
  have hbsOpen : K.bs[lane]? = some (0x7B : UInt8) := by
    have hy : byte = (0x7B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [hy] using hbs
  have hbsClose : K.bs[next]? = some (0x7D : UInt8) := by
    have hy : nextByte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
    simpa [hy] using hbs1
  have htrace' : Stage2NoEventWalkTrace Kc :=
    Stage2NoEventWalkTrace.emptyObject htrace hbsOpen hbsClose
  -- the endpoint's after-value selection at the `if.then343` edge
  have h49 : lookupName S13.env "%49"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [S13, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells,
      List.cons_append, List.nil_append]
    rw [lookupName_cons_self]
  have hdec13 : lookupName S13.env "%dec"
      = some (.int 32 (sp2 + BitVec.ofNat 32 4294967295)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4c13 : lookupName S13.env "%k.4"
      = some (.int 64 (k64 + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen6 : lookupName S13.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harena8 : lookupName S13.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hterms6 : lookupName S13.env "%terms.6"
      = some (.int 64 (termsv + BitVec.ofNat 64 3)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htoks6 : lookupName S13.env "%tokens.6"
      = some (.int 64 (tokv + BitVec.ofNat 64 2)) := by
    simp only [S13, S12, stage2NoEventWalkNext, cells, closeObjTail,
      braceCloseObjCells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups through the route's cell layers
  have hbase : Stage2NoEventWalkBaseLookups Kc S13 := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := h.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot", .int 1 0)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf4", .int 1 1)]) (names := ["%SwitchLeaf4"]) rfl (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%cmp10", .int 1 0), ("%tokens.0.lcssa1074", .int 64 tokv),
        ("%terms.0.lcssa1080", .int 64 termsv), ("%k.0.lcssa1086", .int 64 k64),
        ("%sp.0.lcssa1092.wide", .int 32 spv), ("%frame.0.lcssa1098", .int 8 frv),
        ("%idxprom.lcssa1108", .int 64 idx), ("%inc.lcssa1129", .int 64 inc)])
      (names := ["%cmp10", "%tokens.0.lcssa1074", "%terms.0.lcssa1080",
        "%k.0.lcssa1086", "%sp.0.lcssa1092.wide", "%frame.0.lcssa1098",
        "%idxprom.lcssa1108", "%inc.lcssa1129"])
      rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%tobool.not", .int 1 (evalICmp .eq spv (BitVec.ofNat 32 0)))])
      (names := ["%tobool.not"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%arrayidx22", .ptr (bracePushAddr K spv)),
        ("%idxprom21", .int 64 (BitVec.ofNat 64
          ((spv + BitVec.ofNat 32 4294967295).toNat))),
        ("%sub", .int 32 (spv + BitVec.ofNat 32 4294967295))])
      (names := ["%arrayidx22", "%idxprom21", "%sub"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := [("%cmp66.not", .int 1 1),
        ("%inc24", .int 32 (spv + BitVec.ofNat 32 1))])
      (names := ["%cmp66.not", "%inc24"]) rfl (by decide)
    have b8 := stage2NoEventCycleBase (K := K) b7
      (cs := ifEnd74Cells K.ep K.b termsv tokv inc bs4 [nextByte])
      (names := ["%11", "%arrayidx77", "%idxprom76", "%10", "%arrayidx75",
        "%inc26", "%add"]) rfl (by decide)
    have b9 := stage2NoEventCycleBase (K := K) b8
      (cs := [("%Pivot22", .int 1 0)]) (names := ["%Pivot22"]) rfl (by decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := [("%SwitchLeaf20", .int 1 1)]) (names := ["%SwitchLeaf20"]) rfl (by decide)
    have b11 := stage2NoEventCycleBase (K := K) b10
      (cs := [("%add85", .int 64 (termsv + BitVec.ofNat 64 3)),
        ("%inc84", .int 64 (tokv + BitVec.ofNat 64 2)),
        ("%inc82", .int 64 (k64 + BitVec.ofNat 64 2))])
      (names := ["%add85", "%inc84", "%inc82"]) rfl (by decide)
    have b12 := stage2NoEventCycleBase (K := K) b11
      (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
        (k64 + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (termsv + BitVec.ofNat 64 3)
        (tokv + BitVec.ofNat 64 2))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    have b13 := stage2NoEventCycleBase (K := K) b12
      (cs := ("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a343 ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294))
      (names := ["%49", "%arrayidx346", "%idxprom345", "%sub344"])
      rfl (by decide)
    intro n v hv
    exact b13 n v hv
  refine ⟨S13, Kc, rfl, hseg, ⟨?_⟩⟩
  have hkc : (k64 + BitVec.ofNat 64 2).toNat = k + 2 := by
    rw [BitVec.toNat_add, hk64nat,
      show (BitVec.ofNat 64 2 : BitVec 64).toNat = 2 from by decide,
      Nat.mod_eq_of_lt (by omega : k + 2 < 2 ^ 64)]
  refine ⟨L13.inv', rfl, bytesToNat bs, ?_, ?_, (sp2 + BitVec.ofNat 32 4294967295).toNat,
    ?_, ?_, ?_, ?_, ?_, ?_, hbase, h.bPos, htrace', ?_⟩
  · exact stage2NoEventWalkBytesToNat_lt hbsLen
  · rw [hbsVal]; omega
  · exact (sp2 + BitVec.ofNat 32 4294967295).isLt
  · exact hdecne
  · omega
  · omega
  · exact Stage2NoEventWalkCount.step (a := 2) (b := 2) h.count rfl rfl (by omega)
  · refine ⟨"if.then343", rfl, ?_⟩
    refine PhiSelects.cons (op := .reg "%49") (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [Kc, stateAt, evalOperand, h49, hdec13, hk4c13, halen6, harena8,
        hterms6, htoks6, k64, termsv, tokv, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro q hq
    exact hcomma q hq

/-! ### The object class's row

The leg's thirteen blocks and the shared cycle are the continuing row; the class
leg is priced against its own two-entry advance, `13 + Φ Kc (k+2) ≤ Φ K k`.
-/

/-- **The empty object pair's continuing row**: the head at `{`, the route to
`after_value`, and the cycle to the head at `k + 3`, as a
`Stage2NoEventWalkRow.cont`.

The route's staging is the pair's own: the head's depth and frame, the
post-push entry lane and document byte at the closer, and the popped stack
byte.  `hcomma` is the separator the cycle reads at the endpoint's index.  The
row advances three entries, so `k + 3` is the next head's index and must be
below the entry count. -/
noncomputable def stage2NoEventWalkRow_cont_bracePair {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane next : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  let w :=
    stage2NoEventWalkBracePairLeg (calls := calls) h htrace hk hbs hb hk1 hbs1 hb1
      hspH hfrH hspPos hspLe hspLt hfrLt hfrPos hkbound hlaneW hval4lt hbyte1W
      hbytePop hbsLen hbsVal hcomma hlt hk63
  let sE := Classical.choose w
  have hspec := Classical.choose_spec w
  let Kc := Classical.choose hspec
  have hspecK := Classical.choose_spec hspec
  have hKc : Kc = { K with tok := K.tok + 2, terms := K.terms + 3 } := hspecK.1
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc sE 13 := hspecK.2.1
  have hsrc : Stage2NoEventWalkCycleSrc calls mem Kc (k + 2) sE :=
    Classical.choice hspecK.2.2
  let cw := stage2NoEventWalkCycle_of_afterValue hsrc
  let s' := Classical.choose cw
  have hcwspec := Classical.choose_spec cw
  let p := Classical.choose hcwspec
  have hcyc : Stage2NoEventWalkCycle calls mem Kc (k + 2) sE 1 s' p :=
    Classical.choose_spec hcwspec
  refine stage2NoEventWalkRow_cont_of_afterValue (F := F) hseg hsrc hcyc ?_ ?_ ?_
    (by omega) ?_
  · rw [hKc]
  · rw [hKc]
  · rw [hKc]
  -- the class leg's price, against the route's own two-entry advance
  · have hpot : stage2NoEventWalkPotential Kc (k + 2) =
        stage2NoEventWalkPotential K (k + 2) := by
      rw [hKc]
      rfl
    rw [hpot]
    have hk2 : k + 2 ≤ K.nep := by omega
    have hlen : K.ent.length = K.nep :=
      readLanes32_length mem K.ep K.nep K.ent h.inv.entries
    have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 2) 0 :=
      stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
    have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 2) hk2 hentle
    omega

/-! ### Axiom footprints -/

#print axioms braceIfThen9_denote
#print axioms link_braceIfThen9_false
#print axioms closeObjPhi_denote
#print axioms braceCloseObjRest_denote
#print axioms link_closeObj_live
#print axioms link_ifThen343
#print axioms stage2NoEventWalkBracePairLeg
#print axioms stage2NoEventWalkRow_cont_bracePair

end LeanLLVM.Refinement
